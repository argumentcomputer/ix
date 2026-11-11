import IxCC.Src.KernelFront.Annotate
import IxCC.Recheck.Produce

/-! # The kernel front end: entry points

IxCC's front end over the certified kernel, beside the front end over IxCC's
own erased type checker (`Recheck.ingress`, `Recheck.produceSource`,
`Recheck.checkCanonicalRelevance`), with the same inputs and outputs:

* `ingress`: IxCC's framing and decoding of the envelope; the kernel's
  acceptance of the environment (`accept`; it replaces the erased checker's
  `Tc.checkEnv`, and is not optional); IxCC's reading of it into the
  table-free `Src.Program` for the chosen roots (`Src.Ingress.readConsts`,
  unchanged); the pinned identities from the kernel's admitted role table
  (`pinsOfTable`); and the program read against the kernel's reading
  (`Reading.build`: keys, addresses and declaration headers);
* `produceSource` and `produceWith`: the producer, with the relevance
  annotation from the kernel's inference (`annotate`) and the types the
  program reads checked against the kernel's reading
  (`checkReachedTypes`);
* `checkCanonicalRelevance`: the byte-level verifiers' requirement that a
  certificate's annotation be the kernel annotator's output on the
  certificate's table;
* `compile`: ingress, the producer, then `Recheck.run`, which is unchanged
  and takes the `Src.Program`.

The recheck path (`Recheck.run` and everything it reaches) does not change and
runs no typing: the kernel is on the byte-level path only, before it. -/

namespace IxCC.Src.KernelFront

open IxCC.Recheck (Err Config Input)

/-- The kernel front end's ingress: the earlier ingress's input, and what the
kernel accepted with IxCC's program keyed to it. -/
structure KInput where
  inp : Input
  acc : Accepted
  rd : Reading
  /-- The accepted environment's index, which the annotator queries. -/
  fe : Ix.Kernel.FEnv .anon

/-- **Ingress over the kernel**: decode, choose the roots, the kernel's
acceptance (refused with the kernel's reason), IxCC's reading into the
`Src.Program` with the pins of the admitted role table, and the program read
against the kernel's reading. Only role-bound environments are accepted. -/
def ingress (bytes : ByteArray) (equations : Lean.Json) (roots : List String := [])
    (limits : Ix.Kernel.Admission.Limits := defaultLimits) : Except Err KInput := do
  let env ← (Ixon.V3.decodeAnonymousEnv bytes).mapError fun m =>
    { stage := .ingress, code := "decode", message := m }
  let hints ← (Src.Hints.ofK1Json equations).mapError fun m =>
    { stage := .ingress, code := "hints", message := m }
  let chosen ← Recheck.selectRoots hints.roots roots
  if chosen.isEmpty then
    throw { stage := .ingress, code := "roots", message := "the sidecar names no root" }
  let hints := { hints with roots := chosen }
  let acc ← (accept env limits).mapError fun r =>
    { stage := .ingress, code := "kernel", message := r.render }
  let p ← (Src.Ingress.readConsts env (chosen.map (·.1))).mapError fun m =>
    { stage := .ingress, code := "ingress", message := m }
  let p := { p with known := { pins := pinsOfTable acc.table } }
  let p := { p with known := Src.Pinned.known p, resource := hints.resource }
  (Src.Resource.validate p).mapError fun m =>
    { stage := .ingress, code := "resource-binding", message := m }
  let rd ← (Reading.build acc p).mapError fun m =>
    { stage := .ingress, code := "faithful", message := m }
  let names := chosen.toList.zipIdx.map fun ((_, n), i) => n.getD s!"root{i}"
  pure { inp := { env, hints, program := p, names }, acc, rd, fe := Ix.Kernel.mkFEnv acc.env }

/-- The relevance oracle over the kernel, on a program with a table, and the
check that the types it reads are the kernel's. -/
def annotateChecked (k : KInput) (p : Src.Program) : Except String Src.Relevance.Ann := do
  let ann ← annotate k.fe k.rd p
  checkReachedTypes k.rd p ann
  pure ann

/-- The producer's front half over the kernel (`Recheck.produceSource` with
the kernel's annotation). -/
def produceSource (cfg : Config) (k : KInput) : Except Err Recheck.ProducedSource := do
  let inp := k.inp
  let P := inp.program
  let (table, tableDiags, tableStats) := Src.Table.build cfg.table P inp.hints.proposals
  let p0 := { P with table }
  (Src.Table.validate cfg.table p0).mapError fun m => { stage := .table, code := "table.entry", message := m }
  let ann ← (annotateChecked k p0).mapError fun m =>
    { stage := .relevance, code := "relevance-oracle", message := m }
  let (src, checked) ← match Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error (.install m) => throw { stage := .relevance, code := "relevance-S1", message := m }
    | .error (.relevance errs) =>
      throw { stage := .relevance, code := s!"relevance-{(errs[0]?.map (·.rule)).getD "S1"}"
              message := "; ".intercalate (errs.toList.take 8 |>.map (·.render p0)) }
    | .error (.table m) => throw { stage := .table, code := "table.entry", message := m }
  match Src.admit src (Recheck.sidecarName inp.hints) cfg.admit with
  | .ok _ => pure ()
  | .error diags =>
    let d := diags[0]?.getD (Src.Diag.of "admit" "rejected")
    throw { Recheck.Err.ofDiag .admit d with
      message := "; ".intercalate (diags.toList.map fun d => (Recheck.splitCode d.render).2) }
  pure { table, tableDiags, tableStats, ann, src, checked }

/-- The producer over the kernel (`Recheck.produceWith` with the kernel's
front half). -/
def produceWith (cfg : Config) (k : KInput) : Except Err Recheck.Produced := do
  let ⟨table, tableDiags, tableStats, ann, src, checked⟩ ← produceSource cfg k
  let (lam, _) ← (Lam.erase src checked).mapError Recheck.Err.ofErase
  let trace ← (Anf.Pipeline.produce cfg.budgets lam).mapError fun m =>
    { stage := .anf, code := "anf.produce", message := m }
  let anf := ((trace.stages.getLast?).map (·.2)).getD default
  let fir ← (Fir.lower anf).mapError Recheck.Err.ofFir
  let C := Cfg.lower (Own.immortal fir)
  Recheck.checkParams cfg C (C.exports.zipIdx.map fun (f, i) => (i, f))
  let lowered ← (Rt.lower { names := cfg.names } C).mapError Recheck.Err.ofRt
  let (xv, _) ← (Xv.Select.run lowered.program).mapError Recheck.Err.ofSelect
  let r ← (Xv.Alloc.runProducer cfg.env xv).mapError fun m =>
    { stage := .alloc, code := "alloc.fallback", message := m }
  let layouts := Xv.Stacking.produce r.program
  let stacked ← (Xv.Stacking.run r.program layouts lowered.reps cfg.env).mapError
    (Recheck.Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  pure { cert := { table := Src.Table.TableCert.ofTable table, relevance := ann, mid := trace.cert
                   alloc := r.outs, frames := layouts, order }
         tableDiags, tableStats, fires := trace.fires, stages := trace.stages, alloc := r.outcomes }

/-- The producer over the kernel: the certificate. -/
def produce (cfg : Config) (k : KInput) : Except Err Recheck.Cert :=
  (·.cert) <$> produceWith cfg k

/-- **Stage A over the kernel**: the certificate's relevance annotation is the
kernel annotator's output on the theorem-validated table its table certificate
gives (independent of the sidecar's proposals). -/
def checkCanonicalRelevance (cfg : Config) (k : KInput)
    (tableCert : Src.Table.TableCert) (rel : Src.Relevance.Ann) : Bool :=
  match Src.Table.ofCert cfg.table k.inp.program tableCert with
  | .error _ => false
  | .ok table =>
    match annotateChecked k { k.inp.program with table } with
    | .ok ann => ann.eqb rel
    | .error _ => false

theorem checkCanonicalRelevance_iff (cfg : Config) (k : KInput)
    (tableCert : Src.Table.TableCert) (rel : Src.Relevance.Ann) :
    checkCanonicalRelevance cfg k tableCert rel = true ↔
      ∃ table,
        Src.Table.ofCert cfg.table k.inp.program tableCert = .ok table ∧
        annotateChecked k { k.inp.program with table } = .ok rel := by
  unfold checkCanonicalRelevance
  cases htab : Src.Table.ofCert cfg.table k.inp.program tableCert with
  | error _ => simp
  | ok table =>
    simp only [Except.ok.injEq, exists_eq_left']
    cases hann : annotateChecked k { k.inp.program with table } with
    | error _ => simp
    | ok ann => simp only [Src.Relevance.Ann.eqb_iff, Except.ok.injEq]

/-- The compiler over the kernel: ingress, the producer, `Recheck.run` (which
is the same function on the same kind of program). -/
def compile (cfg : Config) (bytes : ByteArray) (equations : Lean.Json) (roots : List String := []) :
    Except Err (Recheck.Cert × Recheck.Artifact) := do
  let k ← ingress bytes equations roots
  let cfg := cfg.forInput k.inp
  let c ← produce cfg k
  let a ← IxCC.Recheck.run cfg k.inp.program c
  pure (c, a)

end IxCC.Src.KernelFront
