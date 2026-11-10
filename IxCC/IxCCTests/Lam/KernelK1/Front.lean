import IxCC.Src.Recheck
import IxCC.Lam.Erase

/-! The front end as the kernel evaluates it on K1 artifacts:
`Src.Recheck.run` (the table's revalidation, the annotation's installation
and check, `Lazify`) followed by erasure to Lam, and the facts the
`KernelK1` modules assert about its result. -/

namespace IxCCTests.Lam.KernelK1

open IxCC IxCC.Src

/-- The front end's recheck path and erasure on a program and annotation. -/
def frontEnd (p : Program) (ann : Relevance.Ann) :
    Except String (Lam.Program × Lam.Erase.Stats) :=
  match Recheck.run {} p ann with
  | .error (.table m) => .error s!"table: {m}"
  | .error (.install m) => .error s!"install: {m}"
  | .error (.relevance es) => .error s!"relevance: {es.toList.map (·.rule)}"
  | .ok (p, ch) =>
    match Lam.erase p ch with
    | .ok r => .ok r
    | .error e => .error e.render

/-- The erased program has `globals` globals and one root, `const root` at
the empty profile. -/
def facts (p : Program) (ann : Relevance.Ann) (globals : Nat) (root : CId) : Bool :=
  match frontEnd p ann with
  | .ok (lp, st) =>
    st.globals == globals &&
    (match lp.roots with
     | [g] => (lp.globals.get? g).map (·.key) == some (.const root [])
     | _ => false)
  | .error _ => false

/-- Where the recheck path stops. -/
inductive Stage where
  | accepted
  | table
  | install
  | relevance
  deriving DecidableEq

/-- The recheck path's verdict on a program and annotation. -/
def stage (p : Program) (ann : Relevance.Ann) : Stage :=
  match Recheck.run {} p ann with
  | .error (.table _) => .table
  | .error (.install _) => .install
  | .error (.relevance _) => .relevance
  | .ok _ => .accepted

end IxCCTests.Lam.KernelK1
