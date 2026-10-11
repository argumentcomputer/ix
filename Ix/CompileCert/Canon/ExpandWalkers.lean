import Ix.CompileCert.Canon.ExpandRename
import Batteries.Tactic.OpenPrivate

open private Ix.Compile.Canon.liftLoose.go Ix.Compile.Canon.lowerLoose.go
  Ix.Compile.Canon.substLevels.go Ix.Compile.Canon.instantiatePiParams.go
  from Ix.Compile.Canon.Expr

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

theorem LRel.getElem {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : LRel R xs ys)
    (i : Nat) (hi : i < xs.length) (hi' : i < ys.length) : R xs[i] ys[i] := by
  induction h generalizing i with
  | nil => simp at hi
  | cons h rest ih =>
    cases i with
    | zero => exact h
    | succ i => exact ih i (by simpa using hi) (by simpa using hi')

theorem LRel.arrayGetElem {α β : Type} {R : α → β → Prop}
    {xs : Array α} {ys : Array β} (h : LRel R xs.toList ys.toList)
    (i : Nat) (hi : i < xs.size) (hi' : i < ys.size) : R xs[i] ys[i] := by
  cases xs
  cases ys
  exact h.getElem i hi hi'

section
variable {σ : Name → Name} {S : Name → Prop}

theorem ERen.liftLoose {e e' : Expr} (h : ERen σ S e e') (n cutoff : Nat) :
    ERen σ S (Ix.Compile.Canon.liftLoose e n cutoff)
      (Ix.Compile.Canon.liftLoose e' n cutoff) := by
  unfold Ix.Compile.Canon.liftLoose
  split
  · exact h
  · suffices ∀ c, ERen σ S (Ix.Compile.Canon.liftLoose.go n e c)
        (Ix.Compile.Canon.liftLoose.go n e' c) from this cutoff
    induction h <;> intro c <;> simp only [Ix.Compile.Canon.liftLoose.go]
    all_goals first | (split <;> constructor) | (constructor <;> solve_by_elim)

theorem ERen.lowerLoose {e e' : Expr} (h : ERen σ S e e') (n cutoff : Nat) :
    ERen σ S (Ix.Compile.Canon.lowerLoose e n cutoff)
      (Ix.Compile.Canon.lowerLoose e' n cutoff) := by
  unfold Ix.Compile.Canon.lowerLoose
  split
  · exact h
  · suffices ∀ c, ERen σ S (Ix.Compile.Canon.lowerLoose.go n e c)
        (Ix.Compile.Canon.lowerLoose.go n e' c) from this cutoff
    induction h <;> intro c <;> simp only [Ix.Compile.Canon.lowerLoose.go]
    all_goals first | (split <;> constructor) | (constructor <;> solve_by_elim)

theorem ERen.substLevels {e e' : Expr} (h : ERen σ S e e')
    (params : Array Name) (us : Array Ix.Level) :
    ERen σ S (Ix.Compile.Canon.substLevels params us e)
      (Ix.Compile.Canon.substLevels params us e') := by
  unfold Ix.Compile.Canon.substLevels
  split
  · exact h
  · induction h <;> simp only [Ix.Compile.Canon.substLevels.go]
    all_goals constructor <;> assumption

theorem ERen.instantiateRevAt {e e' : Expr} (h : ERen σ S e e')
    {args args' : Array Expr} (ha : LRel (ERen σ S) args.toList args'.toList)
    (depth : Nat) :
    ERen σ S (Ix.Compile.Canon.instantiateRevAt args e depth)
      (Ix.Compile.Canon.instantiateRevAt args' e' depth) := by
  have sizes : args.size = args'.size := by simpa using ha.length.symm
  induction h generalizing depth with
  | bvar i h h' =>
    simp only [Ix.Compile.Canon.instantiateRevAt, sizes]
    split
    · split
      · rename_i hi
        apply ERen.liftLoose
        exact ha.arrayGetElem (i - depth) (by simpa [sizes] using hi) hi
      · constructor
    · constructor
  | _ =>
    simp only [Ix.Compile.Canon.instantiateRevAt]
    constructor <;> solve_by_elim

theorem ERen.instantiateRev {e e' : Expr} (h : ERen σ S e e')
    {args args' : Array Expr} (ha : LRel (ERen σ S) args.toList args'.toList) :
    ERen σ S (Ix.Compile.Canon.instantiateRev e args)
      (Ix.Compile.Canon.instantiateRev e' args') := by
  have sizes : args.size = args'.size := by simpa using ha.length.symm
  have empty : args.isEmpty = args'.isEmpty := by simp [Array.isEmpty, sizes]
  unfold Ix.Compile.Canon.instantiateRev
  rw [empty]
  split
  · exact h
  · exact h.instantiateRevAt ha 0

/-- Telescope binders preserve domain relation, with names and binder
annotations left in source metadata as in `ERen`. -/
def BinderRen (σ : Name → Name) (S : Name → Prop) (b b' : Binder) : Prop :=
  ERen σ S b.2.1 b'.2.1

theorem ERen.mkForalls {body body' : Expr} (h : ERen σ S body body')
    {bs bs' : Array Binder} (hb : LRel (BinderRen σ S) bs.toList bs'.toList) :
    ERen σ S (Ix.Compile.Canon.mkForalls bs body)
      (Ix.Compile.Canon.mkForalls bs' body') := by
  unfold Ix.Compile.Canon.mkForalls
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  generalize bs.toList = xs at hb ⊢
  generalize bs'.toList = ys at hb ⊢
  induction hb with
  | nil => exact h
  | cons hhead htail ih =>
    obtain ⟨n,t,bi⟩ := ‹Binder›
    obtain ⟨n',t',bi'⟩ := ‹Binder›
    exact .forallE _ _ _ _ _ _ hhead ih

end
end Ix.CompileCert.Canon
