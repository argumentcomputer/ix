import IxVMRefinement.Obs.KernelLevels
import IxVMRefinement.Core.Obs
import IxVMRefinement.Levels.Rom
import Ix.IxVM.Refinement.LevelsObs

/-! # The level comparisons over observed, bounded derivations

`Ix.IxVM.Refinement.KernelLevels` proves `level_leq` and `level_equal` against the pure
`levelLeq`, `levelEqual` over the unbounded semantics (`EvalFn`), under the hypothesis that
the offsets the normalizer reaches stay below `OB` (`levelSucc l < OB`). This module removes
that hypothesis for observed derivations whose calls a valid ROM of at most `2^39` addresses
carries (the consistency statement's `Bounded`).

**Where the bound comes from.** Not from the comparisons alone. Every
`UInt32::less_than_fields` bounds the two values it compares by `2^32` itself
(`u32LessThanFields_bounded`), but the normalizer's running offset `k` is a field element
incremented once per successor, and some offsets are never compared: `normalize_aux` on
`zero` at an offset `k ≡ 0` returns its accumulator without any comparison, so `succ^p zero`
(with `p` the characteristic) would normalize as `zero`. What excludes it is the level
itself: the offsets reached are at most the number of successors on a path of the level
(`normArgSucc_le_argDepth`), so at most its height, and a level the derivation hands to
`level_normalize` is represented in the ROM, where its height is below `2^39`
(`arg_levelDepth_lt`).

**What this gives.** `levelLeq_obs` and `levelEqual_obs`: on represented levels, a bounded
observed derivation answers `levelLeq` and `levelEqual`, with no other hypothesis. -/

namespace IxVM.Refinement.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.KernelLevels
open IxVM.Consistency (Bounded)

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- Membership of a call in a concatenation of call lists. -/
macro "chainsub" : tactic =>
  `(tactic| first
    | (intro x hx; simp only [List.mem_cons, List.mem_append] at hx ⊢; tauto)
    | (intro x hx; simp only [List.mem_cons, List.mem_append]; tauto))

/-! ## Reading a level node -/

theorem load_klevel {h : Heap F} {addr : Nat} {c c' : String} {xs xs' : List (SourceValue F)}
    (cell : h[addr]? = some (.construct klevelEnum c xs))
    (ld : loadValue h (.ptr (.enum klevelEnum) addr) =
      .ok (.construct "KernelTypes::KLevelNode" c' xs')) :
    c = c' ∧ xs = xs' := by
  rw [loadValue_enum_cell cell] at ld
  injection ld with hv
  injection hv with _ hc hx
  exact ⟨hc, hx⟩

theorem rep_zero_of_load {h : Heap F} {l : Ix.Kernel.Level} {p : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Zero" [])) : l = .zero := by
  cases rep with
  | zero _ => rfl
  | succ cell _ | max cell _ _ | imax cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_succ_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Succ" [x])) :
    ∃ u, l = .succ u ∧ RepKLevel h u x := by
  cases rep with
  | succ cell ih =>
    obtain ⟨-, hx⟩ := load_klevel cell ld
    injection hx with hx _
    subst hx
    exact ⟨_, rfl, ih⟩
  | zero cell | max cell _ _ | imax cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_max_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x y : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Max" [x, y])) :
    ∃ u v, l = .max u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | max cell ihu ihv =>
    obtain ⟨-, hx⟩ := load_klevel cell ld
    injection hx with hx hy
    injection hy with hy _
    subst hx hy
    exact ⟨_, _, rfl, ihu, ihv⟩
  | zero cell | succ cell _ | imax cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_imax_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x y : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "IMax" [x, y])) :
    ∃ u v, l = .imax u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | imax cell ihu ihv =>
    obtain ⟨-, hx⟩ := load_klevel cell ld
    injection hx with hx hy
    injection hy with hy _
    subst hx hy
    exact ⟨_, _, rfl, ihu, ihv⟩
  | zero cell | succ cell _ | max cell _ _ | param _ cell =>
    exact absurd (load_klevel cell ld).1 (by decide)

theorem rep_param_of_load {h : Heap F} {l : Ix.Kernel.Level} {p x : SourceValue F}
    (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Param" [x])) :
    ∃ n, l = .param n := by
  cases rep with
  | param _ _ => exact ⟨_, rfl⟩
  | zero cell | succ cell _ | max cell _ _ | imax cell _ _ =>
    exact absurd (load_klevel cell ld).1 (by decide)


/-! ## The normalizer's offsets are bounded by the level's height -/

/-- The height of a `normalizeStep` argument. -/
def argDepth : Sum Ix.Kernel.Level (Ix.Kernel.Level × Ix.Kernel.Level) → Nat
  | .inl l => levelDepth l
  | .inr (a, b) => Max.max (levelDepth a) (levelDepth b)

/-- **The offsets the normalizer reaches are at most the height of its argument**: they count
the successors on a path, and a path has at most as many nodes as the height. -/
theorem normArgSucc_le_argDepth (fuel : Nat) :
    ∀ arg, normArgSucc fuel arg ≤ argDepth arg := by
  induction fuel with
  | zero =>
    intro arg
    simp only [normArgSucc]
    omega
  | succ fuel ih =>
    intro arg
    rcases arg with l | ⟨a, b⟩
    · cases l with
      | zero =>
        simp only [normArgSucc]
        omega
      | succ u =>
        have h1 := ih (.inl u)
        simp only [normArgSucc, argDepth, levelDepth] at h1 ⊢
        omega
      | max x y =>
        have h1 := ih (.inl x)
        have h2 := ih (.inl y)
        simp only [normArgSucc, argDepth, levelDepth] at h1 h2 ⊢
        omega
      | imax x y =>
        have h1 := ih (.inr (x, y))
        simp only [normArgSucc, argDepth, levelDepth] at h1 ⊢
        omega
      | param _ =>
        simp only [normArgSucc]
        omega
    · cases b with
      | zero =>
        simp only [normArgSucc]
        omega
      | succ v =>
        have h1 := ih (.inl a)
        have h2 := ih (.inl v)
        simp only [normArgSucc, argDepth, levelDepth] at h1 h2 ⊢
        omega
      | max v w =>
        have h1 := ih (.inr (a, v))
        have h2 := ih (.inr (a, w))
        simp only [normArgSucc, argDepth, levelDepth] at h1 h2 ⊢
        omega
      | imax v w =>
        have h1 := ih (.inr (v, w))
        have h2 := ih (.inr (a, w))
        simp only [normArgSucc, argDepth, levelDepth] at h1 h2 ⊢
        omega
      | param _ =>
        have h1 := ih (.inl a)
        simp only [normArgSucc, argDepth, levelDepth] at h1 ⊢
        omega

theorem levelSucc_le_levelDepth (l : Ix.Kernel.Level) : levelSucc l ≤ levelDepth l :=
  normArgSucc_le_argDepth (normFuel (.inl l)) (.inl l)

theorem two_pow_39_lt_OB : 2 ^ 39 < OB := by decide

/-- **The offsets the normalizer reaches on a level a bounded derivation hands to a call stay
below `OB`.** -/
theorem levelSucc_lt_of_arg {calls : List (Call F)} (hb : Bounded calls) {c : Call F}
    (hc : c ∈ calls) {p : SourceValue F} (hp : p ∈ c.args) {l : Ix.Kernel.Level}
    (rep : RepKLevel c.heap l p) : levelSucc l < OB :=
  lt_of_le_of_lt (levelSucc_le_levelDepth l)
    (lt_trans (arg_levelDepth_lt hb hc hp rep) two_pow_39_lt_OB)

/-! ## `level_leq` and `level_equal` over bounded derivations -/

/-- **`level_leq` answers `levelLeq`** on represented levels, in a bounded derivation. -/
theorem levelLeq_obs {x_a x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {la lb : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_leq" [x_a, x_b] h r h' cs)
    (hb : Bounded cs)
    (repA : RepKLevel h la x_a) (repB : RepKLevel h lb x_b) :
    r = .field (if levelLeq la lb then 1 else 0) ∧ Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_leq».obs ev with
  | n1 m2 cs13 ev15 he36 he37 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    subst he36 he37
    have heq : (la == lb) = true := by
      by_contra hne
      simp [hne] at hr
    exact ⟨by simp [levelLeq, heq], Heap.Extends.refl _⟩
  | n0_Zero m2 cs13 ev15 ld he63 he64 hc =>
    obtain ⟨-, rfl⟩ := levelEq_refines repA repB ev15.erase
    obtain rfl := rep_zero_of_load repA ld
    subst he63 he64
    exact ⟨by simp [levelLeq], Heap.Extends.refl _⟩
  | n0_other m2 cs13 v44 cs73 v76 v77 m79 cs87 m99 cs107 ev15 ld hne66 ev89 ev109 ev75 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    have hne : (la == lb) = false := by
      cases hbe : (la == lb)
      · rfl
      · simp [hbe] at hr
    have hnz : la ≠ .zero := by
      rintro rfl
      cases repA with
      | zero cell =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact hne66 [] rfl hv.symm
    subst hc
    obtain ⟨repNA, ext1⟩ := levelNormalize_refines repA
      (levelSucc_lt_of_arg hb (c := ⟨"KernelLevels::level_normalize", [x_a], _⟩) (by simp)
        (by simp) repA) ev89.erase
    obtain ⟨repNB, ext2⟩ := levelNormalize_refines (repB.mono ext1)
      (levelSucc_lt_of_arg hb (c := ⟨"KernelLevels::level_normalize", [x_b], _⟩) (by simp)
        (by simp) (repB.mono ext1)) ev109.erase
    obtain ⟨hr', rfl⟩ := nlLe_refines (repNA.mono ext2) repNB ev75.erase
    have hlev : levelLeq la lb = nlLe (levelNormalize la) (levelNormalize lb) := by
      cases la with
      | zero => exact absurd rfl hnz
      | _ => simp [levelLeq, hne]
    exact ⟨by rw [hr', hlev], ext1.trans ext2⟩

/-- **`level_equal` answers `levelEqual`** on represented levels, in a bounded derivation. -/
theorem levelEqual_obs {x_a x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {la lb : Ix.Kernel.Level}
    (ev : ObsFn IxVM.source.world "KernelLevels::level_equal" [x_a, x_b] h r h' cs)
    (hb : Bounded cs)
    (repA : RepKLevel h la x_a) (repB : RepKLevel h lb x_b) :
    r = .field (if levelEqual la lb then 1 else 0) ∧ Heap.Extends h h' := by
  cases Obs.«KernelLevels::level_equal».obs ev with
  | n1 m2 cs13 ev15 he36 he37 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    subst he36 he37
    have heq : (la == lb) = true := by
      by_contra hne
      simp [hne] at hr
    exact ⟨by simp [levelEqual, heq], Heap.Extends.refl _⟩
  | n0 m2 cs13 cs47 v50 v51 m53 cs61 m73 cs81 ev15 ev63 ev83 ev49 hc =>
    obtain ⟨hr, rfl⟩ := levelEq_refines repA repB ev15.erase
    have hne : (la == lb) = false := by
      cases hbe : (la == lb)
      · rfl
      · simp [hbe] at hr
    subst hc
    obtain ⟨repNA, ext1⟩ := levelNormalize_refines repA
      (levelSucc_lt_of_arg hb (c := ⟨"KernelLevels::level_normalize", [x_a], _⟩) (by simp)
        (by simp) repA) ev63.erase
    obtain ⟨repNB, ext2⟩ := levelNormalize_refines (repB.mono ext1)
      (levelSucc_lt_of_arg hb (c := ⟨"KernelLevels::level_normalize", [x_b], _⟩) (by simp)
        (by simp) (repB.mono ext1)) ev83.erase
    obtain ⟨hr', rfl⟩ := nlEq_refines (repNA.mono ext2) repNB ev49.erase
    have hlev : levelEqual la lb = nlEq (levelNormalize la) (levelNormalize lb) := by
      simp [levelEqual, hne]
    exact ⟨by rw [hr', hlev], ext1.trans ext2⟩

end IxVM.Refinement.Levels
