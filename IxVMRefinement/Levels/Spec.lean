import IxVMRefinement.Levels.Bound

/-! # The level layer: the consistency statement's `Levels`, and the level functions' specs

`levels` discharges the consistency statement's level obligation (`IxVM.Consistency.Levels`,
obligation `L2`): on bounded observed derivations and represented levels, `level_leq = 1`
gives `≤` and `level_equal = 1` gives `=` at every assignment, and `level_equal(l, Zero) = 0`
refutes that `l` is zero at every assignment. No hypothesis on the depth of the levels: the
offsets the normalizer reaches are bounded by the memo bound (`Levels.Bound`), and the
comparisons bound what they compare themselves.

The second part states, for each level function the core calls, its spec over observed
derivations in the form the core's induction consumes (`*Spec`, one per function, with its
step lemma `*_step`). The level functions call no core function, so the steps need no
induction hypothesis. -/

namespace IxVM.Refinement.Levels

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.KernelLevels
open IxVM.Consistency (Bounded)

/-! ## The consistency statement's level obligation -/

/-- **The level layer of `IxVM.consistent`** (`L2`). -/
theorem levels : IxVM.Consistency.Levels := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a b heap after cs la lb ev ⟨rom, -, bound⟩ repA repB φ
    obtain ⟨hr, -⟩ := levelLeq_obs ev bound repA repB
    have ht : levelLeq la lb = true := by
      by_contra hf
      simp [hf] at hr
    exact levelLeq_eq_true_sound ht φ
  · rintro a b heap after cs la lb ev ⟨rom, -, bound⟩ repA repB φ
    obtain ⟨hr, -⟩ := levelEqual_obs ev bound repA repB
    have ht : levelEqual la lb = true := by
      by_contra hf
      simp [hf] at hr
    exact levelEqual_eq_true_sound ht φ
  · rintro a b heap after cs la ev ⟨rom, -, bound⟩ repA repB
    obtain ⟨hr, -⟩ := levelEqual_obs ev bound repA repB
    have hf : levelEqual la .zero = false := by
      cases hb : levelEqual la .zero
      · rfl
      · simp [hb] at hr
    exact not_eval_zero_of_levelEqual_false hf

/-- **Obligation `L2` is discharged.** -/
theorem l2 : IxVM.Consistency.L2 := levels

/-! ## The level functions' specs, in registry form

Each spec is over the function's observed derivation (`args`, heap before `h`, result `r`,
heap after `h'`, calls `calls`). Levels are represented by `RepKLevel` (a pointer to the
`KernelTypes::KLevelNode` tree of the kernel level; `RepKLevel.toRepIxVMKUniv` maps it to
the slice's `RepIxVMKUniv`). The answer of a comparison is stated exactly (the pure function
of `Ix.IxVM.Refinement.KernelLevels`), with its meaning for `Level.eval` as a corollary. -/

section Specs

variable (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
  (calls : List (Call F))

/-- `level_leq(a, b)` answers `levelLeq`: `1` gives `≤` at every assignment
(`levelLeq_eq_true_sound`). -/
def LevelLeqSpec : Prop :=
  ∀ a b, args = [a, b] → Bounded calls → ∀ la lb, RepKLevel h la a → RepKLevel h lb b →
    r = .field (if levelLeq la lb then 1 else 0) ∧ Heap.Extends h h'

/-- `level_equal(a, b)` answers `levelEqual`: `1` gives `=` at every assignment
(`levelEqual_eq_true_sound`); at `b = zero`, `0` gives that `a` is nonzero at some
assignment (`not_eval_zero_of_levelEqual_false`). -/
def LevelEqualSpec : Prop :=
  ∀ a b, args = [a, b] → Bounded calls → ∀ la lb, RepKLevel h la a → RepKLevel h lb b →
    r = .field (if levelEqual la lb then 1 else 0) ∧ Heap.Extends h h'

/-- `level_is_not_zero(a)` answers the kernel's `Level.isNeverZero` (`1` gives a nonzero
level at every assignment, `isNeverZero_eval_ne_zero`), reading only. -/
def LevelIsNotZeroSpec : Prop :=
  ∀ a, args = [a] → ∀ l, RepKLevel h l a →
    r = .field (if l.isNeverZero then 1 else 0) ∧ h' = h

/-- `level_struct_eq(a, b)` answers syntactic equality, reading only. -/
def LevelStructEqSpec : Prop :=
  ∀ a b, args = [a, b] → ∀ la lb, RepKLevel h la a → RepKLevel h lb b →
    r = .field (if la == lb then 1 else 0) ∧ h' = h

/-- `level_reduce(a)` returns a level with the same value at every assignment. The height
bound is the field's characteristic (see `levelReduce_refines`). -/
def LevelReduceSpec : Prop :=
  ∀ a, args = [a] → ∀ l, RepKLevel h l a → levelDepth l < fieldSize →
    ∃ l', RepKLevel h' l' r ∧ Heap.Extends h h' ∧
      ∀ φ, Ix.Kernel.Level.eval φ l' = Ix.Kernel.Level.eval φ l

/-- `level_imax(a, b)` returns `levelIMax a b`, whose value is `imax`'s at every assignment
(`eval_levelIMax`). -/
def LevelIMaxSpec : Prop :=
  ∀ a b, args = [a, b] → ∀ la lb, RepKLevel h la a → RepKLevel h lb b →
    levelDepth la < fieldSize → levelDepth lb < fieldSize →
    RepKLevel h' (levelIMax la lb) r ∧ Heap.Extends h h'

/-- `level_inst_params(a, ps)` returns the substitution of the parameters `0, 1, …` by the
list's levels (`substLevel`; its value is the kernel's `Level.subst` at every assignment,
`eval_substLevel_eq_subst`). -/
def LevelInstParamsSpec : Prop :=
  ∀ a ps, args = [a, ps] → ∀ l params, RepKLevel h l a → RepKLevelList h params ps →
    levelDepth l + maxLevelDepth params < fieldSize →
    ParamsLt params.length l ∧ RepKLevel h' (substLevel l params) r ∧ Heap.Extends h h'

/-- `level_list_inst(ls, ps)`: `level_inst_params` on every level of the list. -/
def LevelListInstSpec : Prop :=
  ∀ ls ps, args = [ls, ps] → ∀ lvls params, RepKLevelList h lvls ls →
    RepKLevelList h params ps →
    (∀ l ∈ lvls, levelDepth l + maxLevelDepth params < fieldSize) →
    (∀ l ∈ lvls, ParamsLt params.length l) ∧ RepKLevelList h' (substLevelList lvls params) r ∧
      Heap.Extends h h'

end Specs

variable {args : List (SourceValue F)} {h : Heap F} {r : SourceValue F} {h' : Heap F}
  {calls : List (Call F)}

theorem levelLeq_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_leq" args h r h' calls) :
    LevelLeqSpec args h r h' calls := by
  rintro a b hargs ⟨rom, -, bound⟩ la lb repA repB
  subst hargs
  exact levelLeq_obs ev bound repA repB

theorem levelEqual_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_equal" args h r h' calls) :
    LevelEqualSpec args h r h' calls := by
  rintro a b hargs ⟨rom, -, bound⟩ la lb repA repB
  subst hargs
  exact levelEqual_obs ev bound repA repB

theorem levelIsNotZero_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_is_not_zero" args h r h' calls) :
    LevelIsNotZeroSpec args h r h' := by
  intro a hargs l rep
  subst hargs
  exact levelIsNotZero_refines rep ev.erase

theorem levelStructEq_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_struct_eq" args h r h' calls) :
    LevelStructEqSpec args h r h' := by
  intro a b hargs la lb repA repB
  subst hargs
  exact levelStructEq_refines repA repB ev.erase

theorem levelReduce_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_reduce" args h r h' calls) :
    LevelReduceSpec args h r h' := by
  intro a hargs l rep hd
  subst hargs
  exact levelReduce_eval_sound rep hd ev.erase

theorem levelIMax_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_imax" args h r h' calls) :
    LevelIMaxSpec args h r h' := by
  intro a b hargs la lb repA repB ha hb
  subst hargs
  exact levelIMax_refines repA repB ha hb ev.erase

theorem levelInstParams_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_inst_params" args h r h' calls) :
    LevelInstParamsSpec args h r h' := by
  intro a ps hargs l params repL repPs hd
  subst hargs
  exact levelInstParams_refines repL repPs hd ev.erase

theorem levelListInst_step
    (ev : ObsFn IxVM.source.world "KernelLevels::level_list_inst" args h r h' calls) :
    LevelListInstSpec args h r h' := by
  intro ls ps hargs lvls params repLs repPs hd
  subst hargs
  exact levelListInst_refines repLs repPs hd ev.erase

end IxVM.Refinement.Levels
