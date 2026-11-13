import IxCC.Src.Relevance.Proof.P1.Defs
import IxCC.Recheck.Proof.Sound

/-! # P1's consumption: the definitions

`Recheck.sound`'s escape `Front.GoesWrong` narrowed to a `Live` result (`Front.GoesWrongLive`), and
P1's `RunSortAgree` for a front end's run of an input (`Front.RunSortAgree`). Definitions only: the
narrowing itself (`Front.goesWrong_live`, `sound_live`) is not proved; it rests on P1
(`IxCC.Src.Relevance.Proof.P1.Defs`). Kept apart from P1's definitions so that the proofs over
SrcEval do not import the compiler's back half. -/

set_option autoImplicit false

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Src.Relevance.Proof.P1

/-- `Front.GoesWrong` with its value disjunct restricted to a `Live` result: the view rejects a
value with no marker at a read position. -/
def Front.GoesWrongLive (f : Front) (ann : Src.Relevance.Ann) (i : Nat × List Nat) : Prop :=
  ∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k).GoesWrong ∨
    ∃ v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .ok v ∧
      Live f.src ann f.checked v.2 ∧ f.view i.1 (Lang.obs v) = none

/-- `SortAgree` for the run of input `i`, at every clock. -/
def Front.RunSortAgree (f : Front) (ann : Src.Relevance.Ann) (i : Nat × List Nat) : Prop :=
  ∀ k root, (f.src.roots[i.1]?).map (·.2) = some root →
    Src.Relevance.Proof.P1.RunSortAgree f.src ann k root (i.2.map .lit)

end IxCC.Recheck
