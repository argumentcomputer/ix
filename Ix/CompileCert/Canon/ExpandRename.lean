import Ix.CompileCert.Canon.Rename
import Ix.CompileCert.Canon.ExpandIndex
import Batteries.Tactic.OpenPrivate

open private Ix.Compile.Canon.looseAtLeast.go Ix.Compile.Canon.mentionsAnyName.go
  from Ix.Compile.Canon.Expr

/-!
Renaming lemmas for the expression walkers used by nested expansion. These
lemmas do not assume agreement of expression hashes or of the `seen` map;
that separate generated-key invariant is not asserted here.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name Expr)

theorem LRel.append {α β : Type} {R : α → β → Prop}
    {xs ys : List α} {xs' ys' : List β}
    (hx : LRel R xs xs') (hy : LRel R ys ys') :
    LRel R (xs ++ ys) (xs' ++ ys') := by
  induction hx with
  | nil => exact hy
  | cons h _ ih => exact .cons h ih

section
variable {σ : Name → Name} {S : Name → Prop}

/-- The head and ordered argument spine are preserved by a renaming. -/
theorem ERen.getAppFnArgs {e e' : Expr} (h : ERen σ S e e') :
    ERen σ S (Ix.Compile.Canon.getAppFnArgs e).1 (Ix.Compile.Canon.getAppFnArgs e').1 ∧
    LRel (ERen σ S) (Ix.Compile.Canon.getAppFnArgs e).2.toList (Ix.Compile.Canon.getAppFnArgs e').2.toList := by
  induction h with
  | app h h' hf ha ihf _ =>
    obtain ⟨hh, has⟩ := ihf
    refine ⟨?_, ?_⟩
    · simpa only [Ix.Compile.Canon.getAppFnArgs] using hh
    · simpa only [Ix.Compile.Canon.getAppFnArgs, Array.toList_push] using
        has.append (.cons ha .nil)
  | _ => exact ⟨by constructor <;> assumption, .nil⟩

/-- Rebuilding a related argument spine preserves the expression relation. -/
theorem ERen.mkAppN {f f' : Expr} (hf : ERen σ S f f')
    {args args' : Array Expr} (ha : LRel (ERen σ S) args.toList args'.toList) :
    ERen σ S (Ix.Compile.Canon.mkAppN f args) (Ix.Compile.Canon.mkAppN f' args') := by
  unfold Ix.Compile.Canon.mkAppN
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  generalize args.toList = as at ha ⊢
  generalize args'.toList = bs at ha ⊢
  induction ha generalizing f f' with
  | nil => exact hf
  | cons h _ ih =>
    exact ih (.app _ _ hf h)

/-- Source metadata at the head does not affect the renamed head. -/
theorem ERen.stripMdata {e e' : Expr} (h : ERen σ S e e') :
    ERen σ S (Ix.Compile.Canon.stripMdata e) (Ix.Compile.Canon.stripMdata e') := by
  induction h <;> simp only [Ix.Compile.Canon.stripMdata]
  all_goals first | assumption | (constructor <;> assumption)

/-- Name renaming does not change local de Bruijn scope checks. -/
theorem ERen.looseAtLeast {e e' : Expr} (h : ERen σ S e e') (d : Nat) :
    Ix.Compile.Canon.looseAtLeast e d = Ix.Compile.Canon.looseAtLeast e' d := by
  unfold Ix.Compile.Canon.looseAtLeast
  suffices ∀ k, Ix.Compile.Canon.looseAtLeast.go d e k = Ix.Compile.Canon.looseAtLeast.go d e' k from this 0
  induction h <;> intro k <;> simp only [Ix.Compile.Canon.looseAtLeast.go, *]

/-- Queue membership tests agree whenever the queue name sets correspond. -/
theorem ERen.mentionsAnyName {e e' : Expr} (h : ERen σ S e e')
    (names names' : Std.HashSet Name)
    (hempty : names.isEmpty = names'.isEmpty)
    (hmem : ∀ n, S n → names.contains n = names'.contains (σ n)) :
    Ix.Compile.Canon.mentionsAnyName names e = Ix.Compile.Canon.mentionsAnyName names' e' := by
  unfold Ix.Compile.Canon.mentionsAnyName
  rw [hempty]
  congr 1
  induction h <;> simp only [Ix.Compile.Canon.mentionsAnyName.go, *]

end
end Ix.CompileCert.Canon
