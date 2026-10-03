import Compilatrix.Src.Ingress
import Compilatrix.Src.Table.Build
import Compilatrix.Src.Relevance.Annotate
import Compilatrix.Src.Recheck
import Compilatrix.Src.Admit
import Compilatrix.Src.Semantics
import Compilatrix.Src.Readback

/-! # Loading a Src program

The front-end pipeline (design note 01 §4.4, 06 S24): strict v3 decoding and
erased typing (no resource admission, 06 S40) → ingress → pinned identities →
unfolding table → the table's revalidation → relevance annotation (an
oracle) → installation → the relevance check → `Lazify` → `Admit`. A failure
names its stage and code. The revalidation, installation, check and `Lazify`
are the recheck path's steps (`Src.Recheck`). -/

namespace Compilatrix.Src

open Compilatrix.Ixon

/-- The relevance oracle (note 02 §3.2): any function may be supplied; the
checker decides its output. -/
abbrev RelOracle := V3.Env → Program → Except String Relevance.Ann

structure LoadConfig where
  table : Table.Config := {}
  admit : AdmitConfig := {}
  /-- Run erased typing (`Tc.checkEnv`) over the whole closure. -/
  typecheck : Bool := true
  deriving Inhabited

/-- A loaded program with the evidence of each stage. -/
structure Loaded where
  env : V3.Env
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

/-- Typing, ingress, pinned identities and the unfolding table. -/
def prepare (cfg : LoadConfig) (env : V3.Env) (hints : Hints) :
    Except Diag (Program × Array Diag × Table.Stats) := do
  if cfg.typecheck then stage "typing" (V3.Tc.checkEnv env)
  let p ← stage "ingress" (Ingress.ofEnv env (hints.roots.map (·.1)))
  let p := { p with known := Pinned.known p }
  let (table, tableDiags, tableStats) := Table.build cfg.table p hints.proposals
  let p := { p with table }
  stage "table-recheck" (Table.validate cfg.table p)
  return (p, tableDiags, tableStats)

/-- Installation, the relevance check, `Lazify` and `Admit`, for one
annotation of a prepared program. -/
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
    (oracle : RelOracle := Relevance.annotate) : Except Diag Loaded := do
  let (p, tableDiags, tableStats) ← prepare cfg env hints
  let ann ← stage "relevance-oracle" (oracle env p)
  let (p, checked, admitted) ← finish cfg hints p ann
  return { env, hints, program := p, ann, checked, admitted, tableDiags, tableStats }

/-- The front-end entry point: closure bytes and a `compilatrix/k1-equations/1`
sidecar. -/
def load (bytes : ByteArray) (equations : Lean.Json) (cfg : LoadConfig := {})
    (oracle : RelOracle := Relevance.annotate) : Except Diag Loaded := do
  let env ← stage "decode" (V3.decodeAnonymousEnv bytes)
  let hints ← stage "hints" (Hints.ofK1Json equations)
  loadEnv cfg env hints oracle

end Compilatrix.Src
