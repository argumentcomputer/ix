import IxCC.Recheck.Rc.Replay
import IxCC.Recheck.Produce

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Ixon

/-- Parameter ownership/locality mode derived from the frontend's binder
contracts (`~` borrowed -> `.borrow`, `!`/`1` unique/linear -> `.unique`,
otherwise `.shared`). Resource admission checks those contracts; it is not
certified, and the certified kernel's acceptance compares binders' input
contracts but not their result contracts. -/
inductive ParamMode where
  | shared
  | borrow
  | unique
  deriving DecidableEq, Repr, Inhabited

/-- Map a frontend `BinderContract` to its `ParamMode`. -/
def ParamMode.ofBinderContract (c : V3.BinderContract) : ParamMode :=
  if c.value.locality == .local then .borrow
  else if c.value.owned == .unique || c.uses == .linear then .unique
  else .shared

/-- Map a frontend `BinderContract` to an `Own.PSig`. -/
def PSig.ofBinderContract (c : V3.BinderContract) (rep : Fir.Rep := .tobj) : Own.PSig :=
  match ParamMode.ofBinderContract c with
  | .borrow =>
    { mode := .borrowed false
      kind := if c.value.owned == .unique then .unique true else .shared
      rep }
  | .unique => { mode := .owned, kind := .unique true, rep }
  | .shared => Own.PSig.plain rep

/-- Prefer `primary` when it carries a non-default contract annotation;
otherwise fall back to `fallback`. -/
def mergeBinderContract (primary fallback : V3.BinderContract) : V3.BinderContract :=
  if primary != {} then primary else fallback

/-- Maximum parameter arity implied by a constant's checked `Src.Resource` header bindings. -/
def resourceConstMaxArity (src : Src.Program) (c : Src.CId) : Nat :=
  match src.resource with
  | none => 0
  | some ctx =>
    match ctx.pairs.find? (·.definition == src.addr c) with
    | none => 0
    | some pair => pair.contracts.foldl (fun m h => max m (h.position + 1)) 0

/-- Binder contracts from a constant's checked `Src.Resource` header bindings, if any. -/
def resourceConstContracts (src : Src.Program) (c : Src.CId) (arity : Nat) : List V3.BinderContract :=
  match src.resource with
  | none => []
  | some ctx =>
    match ctx.pairs.find? (·.definition == src.addr c) with
    | none => []
    | some pair =>
      (List.range arity).map fun i =>
        match pair.contracts.find? (·.position == i) with
        | some h => h.contract
        | none => {}

/-- Binder contracts for source constant `c` combining its resolved equation body,
declaration value, Π-type telescope, and `Src.Resource` header annotations. -/
def srcConstContracts (src : Src.Program) (c : Src.CId) : List V3.BinderContract :=
  let piContracts : List V3.BinderContract :=
    match src.decl? c with
    | some d => d.type.pis.1.map (·.1.contract)
    | none => []
  let valContracts : List V3.BinderContract :=
    match src.decl? c with
    | some (.defn _ _ _ _ v) => v.lams.1.map (·.1.contract)
    | _ => []
  let eqContracts : List V3.BinderContract :=
    match src.table.resolveOf c with
    | some (.eqn _ body) => body.lams.1.map (·.1.contract)
    | _ => []
  let arity := max (max (max piContracts.length valContracts.length) eqContracts.length)
    (resourceConstMaxArity src c)
  let resContracts := resourceConstContracts src c arity
  (List.range arity).map fun i =>
    mergeBinderContract (eqContracts.getD i {})
      (mergeBinderContract (valContracts.getD i {})
        (mergeBinderContract (resContracts.getD i {}) (piContracts.getD i {})))

mutual
/-- Extract hole indices and inherited binder contracts from a specialisation
`Key.ArgKey` (including holes nested inside `.con` trees). -/
def argKeyHoles (c : V3.BinderContract) : Key.ArgKey → List (Nat × V3.BinderContract)
  | .hole h => [(h, c)]
  | .con _ ks => argKeyHolesList c ks
  | .glob _ | .lit _ => []

def argKeyHolesList (c : V3.BinderContract) : List Key.ArgKey → List (Nat × V3.BinderContract)
  | [] => []
  | k :: ks => argKeyHoles c k ++ argKeyHolesList c ks
end

/-- Binder contracts traced from `src` through `Key.GKey` (including P4 specialisations
and P5 workers). -/
def srcKeyContracts (src : Src.Program) : Key.GKey → List V3.BinderContract
  | .const c _ | .byName c _ | .recStar c _ => srcConstContracts src c
  | .wrapper h _ =>
    match h with
    | .ctor c | .quotMk c | .quotLift c | .recr c | .cases c => srcConstContracts src c
    | .prim _ => []
    | .word .. => []
  | .spec g args =>
    let base := srcKeyContracts src g
    let holeContracts : List (Nat × V3.BinderContract) :=
      (args.zipIdx).foldl (fun acc (arg, i) =>
        acc ++ argKeyHoles (base.getD i {}) arg) []
    let numHoles := holeContracts.foldl (fun m (h, _) => max m (h + 1)) 0
    (List.range numHoles).map fun h => (holeContracts.lookup h).getD {}
  | .worker g keep =>
    let base := srcKeyContracts src g
    ((List.range keep.length).zip keep).filterMap fun (i, k) =>
      if k then some (base.getD i {}) else none
  | .lam _ _ | .dispatch _ | .entry _ _ => []

/-- Result contract traced from `src` through `Key.GKey`. -/
def srcKeyResult (src : Src.Program) : Key.GKey → V3.ValueContract
  | .const c _ | .byName c _ =>
    ((src.decl? c).map (Lam.Erase.lastRes ·.type)).getD .shared
  | .spec g _ | .worker g _ | .lam g _ => srcKeyResult src g
  | _ => .shared

/-- Binder contracts traced from `src` and any parent function already present
in `P` through `Key.GKey` (including `.spec` and `.worker`). -/
def progKeyContracts (src : Src.Program) (P : Fir.Program) : Key.GKey → List V3.BinderContract
  | .spec g args =>
    let base := progKeyContracts src P g
    let holeContracts : List (Nat × V3.BinderContract) :=
      (args.zipIdx).foldl (fun acc (arg, i) =>
        acc ++ argKeyHoles (base.getD i {}) arg) []
    let numHoles := holeContracts.foldl (fun m (h, _) => max m (h + 1)) 0
    (List.range numHoles).map fun h => (holeContracts.lookup h).getD {}
  | .worker g keep =>
    let base := progKeyContracts src P g
    ((List.range keep.length).zip keep).filterMap fun (i, k) =>
      if k then some (base.getD i {}) else none
  | k =>
    let fromSrc := srcKeyContracts src k
    match P.funList.find? (fun (_, fd) => decide (fd.key = k)) with
    | none => fromSrc
    | some (_, fd) =>
      let n := max fd.contracts.length fromSrc.length
      (List.range n).map fun i =>
        mergeBinderContract (fd.contracts.getD i {}) (fromSrc.getD i {})

/-- Result contract traced from `src` and any parent function in `P`. -/
def progKeyResult (src : Src.Program) (P : Fir.Program) : Key.GKey → V3.ValueContract
  | .spec g _ | .worker g _ | .lam g _ => progKeyResult src P g
  | k =>
    let fromSrc := srcKeyResult src k
    if fromSrc != .shared then fromSrc
    else
      match P.funList.find? (fun (_, fd) => decide (fd.key = k)) with
      | some (_, fd) => fd.result
      | none => .shared

/-- Enrich a `Fir.Fun` with any binder and result contracts present on `src`. -/
def enrichFunContracts (src : Src.Program) (f : Fir.Fun) : Fir.Fun :=
  let fromSrc := srcKeyContracts src f.key
  let n := f.params.length
  let contracts := (List.range n).map fun i =>
    mergeBinderContract (f.contracts.getD i {}) (fromSrc.getD i {})
  let result := if f.result != .shared then f.result else srcKeyResult src f.key
  { f with contracts, result }

/-- Enrich all functions in `P` with source-level and parent-propagated binder
and result contracts from `src` and `P`. -/
def enrichFirContracts (src : Src.Program) (P : Fir.Program) : Fir.Program :=
  { P with
    funs := P.funs.map fun f =>
      let fromProg := progKeyContracts src P f.key
      let n := f.params.length
      let contracts := (List.range n).map fun i =>
        mergeBinderContract (f.contracts.getD i {}) (fromProg.getD i {})
      let result := if f.result != .shared then f.result else progKeyResult src P f.key
      { f with contracts, result } }

/-- Contract-aware canonical `Own.Plain.Program`: enriches `P` with the
`Src` / `Src.Resource` contracts from `src` (checked by resource admission, not
certified) while producing the canonical ownership bodies. -/
def Program.canonicalForSrc (src : Src.Program) (P : Fir.Program) : Program :=
  let enriched := enrichFirContracts src P
  { source := enriched
    bodies := enriched.funs.map fun fd => lowerCode (fd.params.map (·.1)) [] fd.body }

/-- Parameter modes of function `f` in `P` (`.borrow` for `~`, `.unique` for `!`/`1`,
`.shared` otherwise). -/
def Program.funParamModes (P : Program) (f : Fir.FunId) : List ParamMode :=
  match P.source.fun? f with
  | none => []
  | some fd =>
    (List.range fd.params.length).map fun i =>
      ParamMode.ofBinderContract (fd.contracts.getD i {})

/-- Parameter ownership signatures (`Own.PSig`) of function `f` in `P`. -/
def Program.funParamSigs (P : Program) (f : Fir.FunId) : List Own.PSig :=
  match P.source.fun? f with
  | none => []
  | some fd =>
    (fd.params.zipIdx).map fun ((_, rep), i) =>
      PSig.ofBinderContract (fd.contracts.getD i {}) rep

/-- Contract-aware RC policy selection incorporating `src` contracts. -/
def selectRcPolicyForSrc (src : Src.Program) (P : Fir.Program) : RcPolicy :=
  selectRcPolicy (enrichFirContracts src P)

end IxCC.Own.Plain

namespace IxCC.Recheck.RcReplay

/-- Output of the single-pass front-end + erasure + ANF + FIR producer. -/
structure ProducedFir where
  src : Src.Program
  checked : Src.Relevance.Checked
  lam : Lam.Program
  anf : Anf.Program
  fir : Fir.Program
  tableCert : Src.Table.TableCert
  relevance : Src.Relevance.Ann
  mid : Anf.Pipeline.Cert
  tableDiags : Array Src.Diag
  tableStats : Src.Table.Stats
  fires : Anf.Walk.Fires
  stages : List (String × Anf.Program)
  /-- The word hints after admission (`Src.Table.wordHints`, stage W1). -/
  wordHints : Array Src.Diag := #[]

/-- Run the front-end (`Table.build`, the kernel annotator, `Recheck.annotation`,
`Src.admit`), `Lam.erase`, `Anf.Pipeline.produce`, the closures step
(`Recheck.closuresOf`) and `Fir.lower` once. -/
def produceFir (cfg : Config) (inp : Recheck.Input) : Except Err ProducedFir := do
  let P := inp.program
  let (table, tableDiags, tableStats) := Src.Table.build cfg.table P inp.hints.proposals
  let p0 := { P with table }
  (Src.Table.validate cfg.table p0).mapError fun m => { stage := .table, code := "table.entry", message := m }
  let ann ← (inp.kernel.annotateChecked p0).mapError fun m =>
    { stage := .relevance, code := "relevance-oracle", message := m }
  let (src, checked) ← match Src.Recheck.annotation p0 ann with
    | .ok r => pure r
    | .error (.install m) => throw { stage := .relevance, code := "relevance-S1", message := m }
    | .error (.relevance errs) =>
      throw { stage := .relevance, code := s!"relevance-{(errs[0]?.map (·.rule)).getD "S1"}"
              message := "; ".intercalate (errs.toList.take 8 |>.map (·.render p0)) }
    | .error (.table m) => throw { stage := .table, code := "table.entry", message := m }
  let adm ← match Src.admit src (Recheck.sidecarName inp.hints) cfg.admit with
    | .ok adm => pure adm
    | .error diags =>
      let d := diags[0]?.getD (Src.Diag.of "admit" "rejected")
      throw { Err.ofDiag .admit d with message := "; ".intercalate (diags.toList.map fun d => (splitCode d.render).2) }
  let (lam, _) ← (Lam.erase src checked).mapError Err.ofErase
  let trace ← (Anf.Pipeline.produce cfg.budgets lam).mapError fun m =>
    { stage := .anf, code := "anf.produce", message := m }
  -- the closures step, as the replays run it (`Recheck.anfOf`)
  let (anf, stages) ← Recheck.produceClosures src trace
  let fir ← (Fir.lower anf).mapError Err.ofFir
  pure { src, checked, lam, anf, fir
         tableCert := Src.Table.TableCert.ofTable table
         relevance := ann
         mid := trace.cert
         tableDiags, tableStats, fires := trace.fires, stages
         wordHints := Src.Table.wordHints src adm.reached }

/-- Finish a zero-RC (`ixcc/cert/1`) certificate from an already-produced `ProducedFir`. -/
def finishZeroRcCert (cfg : Config) (front : ProducedFir) : Except Err Recheck.Produced := do
  let C := Cfg.lower (Own.immortal front.fir)
  Recheck.checkParams cfg C (C.exports.zipIdx.map fun (f, i) => (i, f))
  let lowered ← (Rt.lower { names := cfg.names } C).mapError Err.ofRt
  let (xv, _) ← (Xv.Select.run lowered.program).mapError Err.ofSelect
  let r ← (Xv.Alloc.runProducer cfg.env xv).mapError fun m =>
    { stage := .alloc, code := "alloc.fallback", message := m }
  let layouts := Xv.Stacking.produce r.program
  let stacked ← (Xv.Stacking.run r.program layouts lowered.reps cfg.env).mapError
    (Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  -- the certificate as the verifier reads it: its file text, read back (`Recheck.Cert.readBack`)
  let built : Recheck.Cert := { table := front.tableCert, relevance := front.relevance, mid := front.mid,
                                alloc := r.outs, frames := layouts, order }
  let ⟨text, cert, read⟩ ← Recheck.Cert.readBack built
  pure { cert, text, read, tableDiags := front.tableDiags, tableStats := front.tableStats
         fires := front.fires, stages := front.stages, alloc := r.outcomes
         wordHints := front.wordHints }

/-- What single-pass `RcReplay.produceWith` found beside the certificate. -/
structure Produced where
  cert : Cert
  /-- The certificate's file text, which `cert` was read back from (`Cert.readBack`). -/
  text : String
  read : Cert.parse text = .ok cert
  front : ProducedFir
  own : Own.Plain.Program
  alloc : List Xv.Alloc.Outcome

/-- Finish a plain-RC (`ixcc/rc-cert/2`) certificate directly from an already-produced
`ProducedFir` using `Own.Plain.Program.canonicalForSrc`. -/
def finishPlainRcCert (cfg : Config) (front : ProducedFir) : Except Err Produced := do
  let canonicalOwn := Own.Plain.Program.canonicalForSrc front.src front.fir
  let ownJson := Own.Plain.Certificate.encode canonicalOwn.bodies
  let admittedOwn ← (Own.Plain.Certificate.admit front.fir ownJson).mapError fun message =>
    { stage := .cert, code := "own.plain", message }
  let some candidate := Cfg.Rc.generate front.fir admittedOwn.bodies |
    throw { stage := .rt, code := "rc.cfg", message := "ownership candidate lowering declined" }
  unless Cfg.Rc.checkScopedProgram front.fir admittedOwn.bodies candidate do
    throw { stage := .rt, code := "rc.scope", message := "scoped dense-source RC gate refused" }
  Recheck.checkParams cfg candidate.base (candidate.base.exports.zipIdx.map fun (f, i) => (i, f))
  let lowered ← (Cfg.Rc.Public.lower { names := cfg.names } front.fir admittedOwn.bodies candidate).mapError
    fun message => { stage := .rt, code := "rc.lower", message }
  let reps : Lir.FunId → Option (List Xv.Stacking.ArgRep) :=
    (⟨lowered.runtime, lowered.drop⟩ : Cfg.Rc.Public.Lowered).reps
  let layout : Cfg.Rc.Native.Layout :=
    ⟨candidate.base.size, candidate.base.ctors.filter (fun c => c.arity > 0)⟩
  let rcEnv := layout.env cfg.env
  let (xv, _) ← (Xv.Select.run lowered.runtime.program).mapError Err.ofSelect
  let allocated ← (Xv.Alloc.runProducer rcEnv xv).mapError fun message =>
    { stage := .alloc, code := "alloc.fallback", message }
  let frames := Xv.Stacking.produce allocated.program
  let stacked ← (Xv.Stacking.run allocated.program frames reps rcEnv).mapError
    (Err.ofBackend ∘ .stacking)
  let order := X86.Layout.Order.produce (X86.Layout.tunnel stacked.program) stacked.shape
  let base : Recheck.Cert :=
    { table := front.tableCert, relevance := front.relevance, mid := front.mid
      alloc := allocated.outs, frames, order }
  -- the certificate as the verifier reads it: its file text, read back through `Cert.parse`
  -- (the ownership code was admitted above as a value; the read-back applies the text limits)
  let ⟨text, cert, read⟩ ← Cert.readBack { base, own := ownJson }
  pure { cert, text, read, front, own := canonicalOwn, alloc := allocated.outcomes }

/-- Single-pass RC certificate producer with allocation outcomes and contract-aware
`Own.Plain.Program`. -/
def produceWith (cfg : Config) (input : Recheck.Input) : Except Err Produced := do
  let cfg := cfg.forInput input
  let front ← produceFir cfg input
  finishPlainRcCert cfg front

/-- Single-pass contract-aware RC producer and recheck runner. -/
def produce (cfg : Config) (input : Recheck.Input) : Except Err (Cert × Artifact) := do
  let cfg := cfg.forInput input
  let p ← produceWith cfg input
  let artifact ← run cfg input.program p.cert
  return (p.cert, artifact)

/-- Select the RC policy (`.zeroRc` vs `.plainRc`) for `input` after running the
front-end + ANF + FIR producer once. -/
def selectPolicy (cfg : Config) (input : Recheck.Input) : Except Err Own.Plain.RcPolicy := do
  let cfg := cfg.forInput input
  let front ← produceFir cfg input
  return Own.Plain.selectRcPolicyForSrc front.src front.fir

/-- Result of automatic policy-aware compilation (`produceAuto`): the policy it
compiled under, with that policy's certificate and rechecked artifact. -/
inductive AutoCompiled where
  | zeroRc (cert : Recheck.Cert) (artifact : Recheck.Artifact) (alloc : List Xv.Alloc.Outcome)
  | plainRc (cert : Cert) (artifact : Artifact) (alloc : List Xv.Alloc.Outcome)
  /-- The immortal fallback: `selectRcPolicyForSrc` chose plain RC, but the
  plain-RC certificate could not be produced or its replay refused it
  (`reason`), so the program was compiled under the immortal policy
  (`Recheck.run`, an `ixcc/cert/1` certificate). -/
  | immortal (cert : Recheck.Cert) (artifact : Recheck.Artifact) (alloc : List Xv.Alloc.Outcome)
      (reason : Err)

/-- The immortal-backend certificate for an already-produced front end, and its
recheck (`Recheck.run`). -/
def produceImmortal (cfg : Config) (input : Recheck.Input) (front : ProducedFir) :
    Except Err (Recheck.Produced × Recheck.Artifact) := do
  let p ← finishZeroRcCert cfg front
  let artifact ← Recheck.run cfg input.program p.cert
  return (p, artifact)

/-- The plain-RC certificate for an already-produced front end, and its replay
(`RcReplay.run`). -/
def producePlain (cfg : Config) (input : Recheck.Input) (front : ProducedFir) :
    Except Err (Produced × Artifact) := do
  let p ← finishPlainRcCert cfg front
  let artifact ← run cfg input.program p.cert
  return (p, artifact)

/-- Automatically select `.zeroRc` or `.plainRc` from `Own.Plain.selectRcPolicyForSrc`
in a single front-end pass, then produce and recheck the selected certificate.
When plain RC is selected but its certificate cannot be produced or is refused
by its replay (for example a contract-annotated program outside
`Own.Plain.programDomain`), fall back to the immortal policy (`.immortal`,
carrying the plain-RC refusal). -/
def produceAuto (cfg : Config) (input : Recheck.Input) : Except Err AutoCompiled := do
  let cfg := cfg.forInput input
  let front ← produceFir cfg input
  match Own.Plain.selectRcPolicyForSrc front.src front.fir with
  | .zeroRc =>
    let (p, artifact) ← produceImmortal cfg input front
    return .zeroRc p.cert artifact p.alloc
  | .plainRc =>
    match producePlain cfg input front with
    | .ok (p, artifact) => return .plainRc p.cert artifact p.alloc
    | .error reason =>
      let (p, artifact) ← produceImmortal cfg input front
      return .immortal p.cert artifact p.alloc reason

/-- Policy-aware compiler from raw closure bytes and sidecar JSON. -/
def compileAuto (cfg : Config) (bytes : ByteArray) (equations : Lean.Json)
    (roots : List String := []) : Except Err AutoCompiled := do
  produceAuto cfg (← Recheck.ingress bytes equations roots)

/-- Project an `RcReplay.Artifact` to `Recheck.Artifact` for CLI reporting (`--dump-ir`,
`--signatures`, `--stats`). -/
def Artifact.toRecheckArtifact (c : Cert) (a : Artifact) : Except Err Recheck.Artifact := do
  let xv ← (Xv.Select.select a.front.lowered.program).mapError Err.ofSelect
  let xl ← (Xv.Alloc.applyProgram xv c.base.alloc).mapError fun message =>
    { stage := .alloc, code := "alloc.apply", message }
  return {
    src := a.front.src
    checked := a.front.checked
    lam := a.front.lam
    anf := a.front.anf
    fir := a.front.fir
    own := Own.immortal a.front.fir
    cfg := a.front.cfg.base
    lowered := a.front.lowered
    xv
    xl
    backend := a.backend
    roots := a.roots }

end IxCC.Recheck.RcReplay
