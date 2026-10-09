import Compilatrix.Rt.Rc.Proof.PendingBalance

/-! Termination measure for the concrete continuation schedule. This file
does not assert machine simulation: the byte/partition invariant must connect
each actual operation to these token-preserving administrative transitions. -/
namespace Compilatrix.Rt.Rc.Procs
open Compilatrix.Own Compilatrix.Own.Rc

inductive ReleaseControl where
  | current (value : RVal) (parents : List (List RVal))
  | advance (parents : List (List RVal))

def ReleaseControl.tokens : ReleaseControl → List RVal
  | .current value parents => value :: flattenPending parents
  | .advance parents => flattenPending parents

def ReleaseControl.admin : ReleaseControl → Nat
  | .current _ parents => 2*parents.length
  | .advance parents => 2*parents.length+1

abbrev ReleaseRank := Nat × (Nat × Nat)
def releaseRank (heap : Heap) (control : ReleaseControl) : ReleaseRank :=
  (mass heap, control.tokens.length, control.admin)
abbrev ReleaseLess := Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt)

/-- Any proven source release step decreases the first two components,
regardless of how many suspended parents the unique case creates. -/
theorem release_rank_decreases {heap heap' : Heap} {value : RVal}
    {parents : List (List RVal)} {next : ReleaseControl}
    (h : releaseOne heap value (flattenPending parents) = some (heap', next.tokens)) :
    ReleaseLess (releaseRank heap' next) (releaseRank heap (.current value parents)) := by
  have hd := releaseOne_decreases h
  rw [Prod.lex_def] at hd
  apply Prod.lex_def.mpr
  rcases hd with hm | ⟨hm, ht⟩
  · exact Or.inl hm
  · exact Or.inr ⟨hm, Prod.Lex.left _ _ ht⟩

theorem resume_tokens (child : RVal) (suffix : List RVal) (parents : List (List RVal)) :
    (ReleaseControl.current child (suffix :: parents)).tokens =
      (ReleaseControl.advance ((child :: suffix) :: parents)).tokens := by
  rfl

theorem resume_rank_decreases (heap : Heap) (child : RVal) (suffix : List RVal)
    (parents : List (List RVal)) :
    ReleaseLess (releaseRank heap (.current child (suffix :: parents)))
      (releaseRank heap (.advance ((child :: suffix) :: parents))) := by
  have hlt : 2*(parents.length+1) < 2*(parents.length+1)+1 := by omega
  exact Prod.Lex.right _ (Prod.Lex.right _ hlt)

theorem recycle_tokens (parents : List (List RVal)) :
    (ReleaseControl.advance parents).tokens =
      (ReleaseControl.advance ([] :: parents)).tokens := by
  rfl

theorem recycle_rank_decreases (heap : Heap) (parents : List (List RVal)) :
    ReleaseLess (releaseRank heap (.advance parents))
      (releaseRank heap (.advance ([] :: parents))) := by
  have hlt : 2*parents.length+1 < 2*(parents.length+1)+1 := by omega
  exact Prod.Lex.right _ (Prod.Lex.right _ hlt)




end Compilatrix.Rt.Rc.Procs
