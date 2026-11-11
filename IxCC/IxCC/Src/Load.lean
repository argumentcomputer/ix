import IxCC.Src.Ingress
import IxCC.Src.Table.Build
import IxCC.Src.KernelFront.Annotate
import IxCC.Src.Recheck
import IxCC.Src.Admit
import IxCC.Src.Semantics
import IxCC.Src.Readback

/-! # Loading a Src program

The front-end pipeline: Ixon v4 decoding → the certified kernel's acceptance
of the whole role-bound environment (`KernelFront.accept`; no resource
admission) → ingress → pinned identities from the kernel's admitted role
table → the program read against the kernel's reading → unfolding table →
the table's revalidation → relevance annotation (an oracle, by default the
annotator over the kernel) → installation → the relevance check → `Lazify`
→ `Admit`. A failure names its stage and code. The revalidation,
installation, check and `Lazify` are the recheck path's steps
(`Src.Recheck`). -/

namespace IxCC.Src

open IxCC.Ixon

/-- The relevance oracle: any function may be supplied; the
checker decides its output. It is asked with what the kernel accepted. -/
abbrev RelOracle := KernelFront.Kernel → Program → Except String Relevance.Ann

/-- The default oracle: the relevance annotator over the kernel, with the
check that the types the program reads are the kernel's. -/
def kernelOracle : RelOracle := fun k p => k.annotateChecked p

structure LoadConfig where
  table : Table.Config := {}
  admit : AdmitConfig := {}
  deriving Inhabited

/-- A loaded program with the evidence of each stage. -/
structure Loaded where
  env : V3.Env
  /-- What the certified kernel accepted, and the program keyed to its
  reading. -/
  kernel : KernelFront.Kernel
  hints : Hints
  program : Program
  ann : Relevance.Ann
  checked : Relevance.Checked
  admitted : Admitted
  tableDiags : Array Diag
  tableStats : Table.Stats

namespace Loaded

/-- Readback with the checked field classes. -/
def readback (l : Loaded) (v : Value) : Option Sem.Obs :=
  Src.readback l.program l.checked.keeps v

/-- The root with this address, or the first root. -/
def root? (l : Loaded) (addr : Option Ixon.Address := none) : Option CId :=
  match addr with
  | some a => (l.program.roots.find? (·.1 == a)).map (·.2)
  | none => l.program.roots[0]?.map (·.2)

/-- Untrusted sidecar names, for diagnostics. -/
def names (h : Hints) (a : Ixon.Address) : Option String :=
  match h.roots.find? (·.1 == a) with
  | some (_, n) => n
  | none => (h.proposals.find? (·.subject == a)).bind (·.name?)

end Loaded

private def stage (code : String) : Except String α → Except Diag α
  | .ok a => .ok a
  | .error e => .error (Diag.of code e)

/-- The kernel's acceptance, ingress, the pinned identities of the kernel's
admitted role table, the program read against the kernel's reading, and the
unfolding table. -/
def prepare (cfg : LoadConfig) (env : V3.Env) (hints : Hints) :
    Except Diag (Program × KernelFront.Kernel × Array Diag × Table.Stats) := do
  let acc ← (KernelFront.accept env).mapError fun r => Diag.of "kernel" r.report
  let p ← stage "ingress" (Ingress.readConsts env (hints.roots.map (·.1)))
  let p := { p with known := { pins := KernelFront.pinsOfTable acc.table } }
  let p := { p with known := Pinned.known p, resource := hints.resource }
  let rd ← stage "faithful" (KernelFront.Reading.build acc p)
  let kernel : KernelFront.Kernel := { acc, rd, fe := Ix.Kernel.mkFEnv acc.env }
  let (table, tableDiags, tableStats) := Table.build cfg.table p hints.proposals
  let p := { p with table }
  stage "table-recheck" (Table.validate cfg.table p)
  return (p, kernel, tableDiags, tableStats)

/-- Installation, the relevance check (tiers S and C, then
`Relevance.checkCanonical`), `Lazify` and `Admit`, for one annotation of a
prepared program (`Recheck.annotation`, then `admit`). -/
def finish (cfg : LoadConfig) (hints : Hints) (p : Program) (ann : Relevance.Ann) :
    Except Diag (Program × Relevance.Checked × Admitted) := do
  let (p, checked) ← match Recheck.annotation p ann with
    | .ok r => pure r
    | .error (.install msg) => throw (Diag.of "relevance-S1" msg)
    | .error (.relevance errs) =>
      let first := errs[0]?.map (·.rule) |>.getD "S1"
      throw (Diag.of s!"relevance-{first}"
        (String.intercalate "; " (errs.toList.take 8 |>.map (·.render p))))
    | .error (.table msg) => throw (Diag.of "table-recheck" msg)
  let admitted ← match admit p (Loaded.names hints) cfg.admit with
    | .ok a => pure a
    | .error diags =>
      throw ((diags[0]?.getD (Diag.of "admit" "rejected")) |> fun d =>
        { d with message := String.intercalate "; " (diags.toList.map toString) })
  return (p, checked, admitted)

/-- The front-end pipeline from a decoded environment and parsed hints. -/
def loadEnv (cfg : LoadConfig) (env : V3.Env) (hints : Hints)
    (oracle : RelOracle := kernelOracle) : Except Diag Loaded := do
  let (p, kernel, tableDiags, tableStats) ← prepare cfg env hints
  let ann ← stage "relevance-oracle" (oracle kernel p)
  let (p, checked, admitted) ← finish cfg hints p ann
  return { env, kernel, hints, program := p, ann, checked, admitted, tableDiags, tableStats }

/-- The front-end entry point: closure bytes and an `ixcc/k1-equations/1`
sidecar. -/
def load (bytes : ByteArray) (equations : Lean.Json) (cfg : LoadConfig := {})
    (oracle : RelOracle := kernelOracle) : Except Diag Loaded := do
  let env ← stage "decode" (V3.decodeAnonymousEnv bytes)
  let hints ← stage "hints" (Hints.ofK1Json equations)
  loadEnv cfg env hints oracle

end IxCC.Src
