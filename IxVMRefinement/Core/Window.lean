import IxVMRefinement.Core.Specs.Subst
import IxVMRefinement.Core.RomBound

/-! # Index windows on bounded heap terms

`has_bvar_in_range` answers `0` with `NoIdxF` (`Specs/Subst.lean`): no index of the heap term is
in the window, as far as the window's end, shifted under the binders passed, stays below the
field's size. On a term whose binder nesting is bounded, this is the window itself (`NoIdx`).
The nesting of a heap term an argument of a call of a bounded derivation points to is below
`2^39` (`bounded_descent_lt`): every binder passed is a step of a descent through the term's
cells. So a caller with `hi + 2^39 ≤` the field's size reads `NoIdx` (`noIdx_of_noIdxF_call`). -/

namespace IxVM.Refinement.Core.Specs.Subst

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics IxVM.Refinement.Core IxVM.Refinement.RomBound
open IxVM.Consistency (Bounded)

/-- **A predicate on indices weakens below the nesting bound**: if every descent from `p` is
shorter than `B - m`, `IdxAll` of `P` gives `IdxAll` of any `Q` that `P` implies below `B`. -/
theorem IdxAll.weaken_bounded {h : Heap F} {P Q : Nat → F → Prop} {B : Nat}
    (hPQ : ∀ m i, m < B → P m i → Q m i) {m : Nat} {p : SourceValue F}
    (hp : IdxAll h P m p)
    (hd : ∀ n, HeapDescent h (.enum kexprEnum) p n → m + n < B) : IdxAll h Q m p := by
  induction hp with
  | bvar cell hP =>
    exact .bvar cell (hPQ _ _ (by have := hd 0 (.here cell rfl); omega) hP)
  | sort cell => exact .sort cell
  | const cell => exact .const cell
  | lit cell => exact .lit cell
  | app cell _ _ ihf iha =>
    refine .app cell (ihf fun n d => ?_) (iha fun n d => ?_)
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
  | lam cell _ _ iht ihb =>
    refine .lam cell (iht fun n d => ?_) (ihb fun n d => ?_)
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
  | forallE cell _ _ iht ihb =>
    refine .forallE cell (iht fun n d => ?_) (ihb fun n d => ?_)
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
  | letE cell _ _ _ iht ihv ihb =>
    refine .letE cell (iht fun n d => ?_) (ihv fun n d => ?_) (ihb fun n d => ?_)
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
    · have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega
  | proj cell _ ihe =>
    exact .proj cell (ihe fun n d => by
      have := hd (n + 1) (.down cell rfl (by simp [cellArgs]) d); omega)

/-- **`NoIdxF` is `NoIdx` below the nesting bound**: when every descent from the term is shorter
than `B` and `hi + B` is at most the field's size. -/
theorem noIdx_of_noIdxF {h : Heap F} {lo hi B : Nat} {p : SourceValue F}
    (hB : hi + B ≤ Aiur.Library.U32.Goldilocks.modulus)
    (hd : ∀ n, HeapDescent h (.enum kexprEnum) p n → n < B) (hn : NoIdxF h lo hi p) :
    NoIdx h lo hi p :=
  IdxAll.weaken_bounded (B := B) (fun _ _ hm hP => hP (by omega)) hn
    (fun n d => by have := hd n d; omega)

/-- **A caller reads `NoIdx`**: for a term an argument of a call of a bounded derivation, with
`hi + 2^39` at most the field's size. -/
theorem noIdx_of_noIdxF_call {calls : List (Call F)} (bounded : Bounded calls) {cl : Call F}
    (called : cl ∈ calls) {p : SourceValue F} (argument : p ∈ cl.args) {lo hi : Nat}
    (hB : hi + 2 ^ 39 ≤ Aiur.Library.U32.Goldilocks.modulus) (hn : NoIdxF cl.heap lo hi p) :
    NoIdx cl.heap lo hi p :=
  noIdx_of_noIdxF hB (fun _ d => bounded_descent_lt bounded called argument d) hn

end IxVM.Refinement.Core.Specs.Subst
