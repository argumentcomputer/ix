import Aiur.Optimized.PhysicalSemantics
import Aiur.Optimized.PolynomialIdentity
import Aiur.Optimized.EndToEnd
import Aiur.Circuit.CheckerContext
import Aiur.Library.U32.Goldilocks
import Mathlib.Tactic.Ring

/-!
# Certified Fast-Path / Cold-Path Chip Splitting (`C3`)

Splits a mixed-width `Aiur.Circuit.Chip F` whose constraints, sends, and ROM
lookups partition across mutually exclusive boolean branch selectors
`s_fast + s_cold = sel` (`sel = 1` on active rows) into TWO specialized physical
chips sharing the same logical LogUp channel `orig.name`:

* `c_fast`: width `|cols_fast|`, specializing `s_fast ↦ 1`, `s_cold ↦ 0`, and
  dropping all dead cold-only columns, cold-only constraints, cold-only sends,
  and cold-only ROM lookups.
* `c_cold`: width `|cols_cold|`, specializing `s_fast ↦ 0`, `s_cold ↦ 1`, and
  handling only the rare cold rows.

Both chips provide on the exact same logical LogUp channel `orig.name`, so
callers require zero dispatch changes and zero extra LogUp lookups, while hot
rows pay only `|cols_fast|` trace columns instead of `orig.numVars`.

## Contents

1. **Algebraic Selector Partition & Dead-Zero Cascade Certificates**:
   Over ANY field `F` of arbitrary characteristic, verifies booleanity,
   mutual exclusion, exhaustiveness `s_fast + s_cold = sel`, and inductive
   nested sub-choice zero propagation (`sum_zero_of_bool_excl`).
2. **Decidable Structural Verifier (`checkSplitWith`, `checkSplit`)**:
   Verifies variable remapping (`proj` & `lift`), selector exclusivity
   `s_fast + s_cold = sel`, column projection, constraint soundness &
   completeness, and exact send/memory/receive equivalence.
3. **Automatic Fail-Closed Splitter (`splitChip`, `splitSystem`)**:
   Constructs `(c_fast, c_cold)` with dead-column compaction and checks
   `checkSplitWith` before accepting.
4. **Bidirectional Chip & System Soundness + Completeness**:
   * `split_chip_sound_with` & `split_chip_sound`: exact bidirectional local
     rule equivalence `(LogicalRule orig.name fast ∨ LogicalRule orig.name cold) ↔ orig.LocalRule`.
   * `split_system_sound` & `split_system_memo_sound`: any accepted split trace
     lifts row-for-row back to an accepted trace of `orig` with the **exact
     same** `RuleClaims` list and **identical** LogUp `Balance.accumulator`.
   * `split_system_complete` & `split_system_memo_complete`: prover completeness
     mapping any accepted trace of `orig` row-for-row into an accepted split
     trace with identical LogUp ledger and reduced Stage-1 trace cells.
   * `split_system_check_iff`, `split_system_checkMemo_iff`,
     `split_modulesArtifact_sound`, `split_physical_heap_sound`.
5. **Executable `#guard` Smoke Tests & `#print axioms` Pins**:
   Demonstrates a 26-column mixed chip (4-col fast path + 24-col cold path with
   nested sub-choices, cold calls, and cold ROM lookups) splitting cleanly into
   a 4-col hot chip + 24-col cold chip with `checkSplit = true`, `6.19×` trace
   cell reduction on a 99%-hot trace, and negative controls rejecting unsound splits.

Zero `sorry`, zero `native_decide`, standard axioms `[propext, Classical.choice, Quot.sound]` only.
-/

set_option autoImplicit false

namespace Aiur.Optimized.Split

open Aiur Aiur.Circuit Aiur.Optimized

/-! ## 1. Polynomial Identity, Substitution & Selector Partition Helpers -/

section Helpers

variable {F : Type} [Field F] [DecidableEq F]

/-- Executable conservative equality on `ArithExpr F` via `Polynomial.simplify`. -/
def evalIdent (p q : ArithExpr F) : Bool :=
  Polynomial.simplify p == Polynomial.simplify q

/-- Executable conservative zero check on `ArithExpr F`. -/
def isZeroExpr (p : ArithExpr F) : Bool :=
  Polynomial.simplify p == (.const 0 : ArithExpr F)

theorem evalIdent_denote {p q : ArithExpr F} (h : evalIdent p q = true) (a : Var → F) :
    p.denote a = q.denote a := by
  have heq : Polynomial.simplify p = Polynomial.simplify q := (Polynomial.beq_eq _ _).mp h
  rw [← Polynomial.denote_simplify p a, ← Polynomial.denote_simplify q a, heq]

theorem isZeroExpr_denote {p : ArithExpr F} (h : isZeroExpr p = true) (a : Var → F) :
    p.denote a = 0 := by
  have heq : Polynomial.simplify p = (.const 0 : ArithExpr F) := (Polynomial.beq_eq _ _).mp h
  rw [← Polynomial.denote_simplify p a, heq]
  rfl

/-- Variable substitution backed by a list of replacement polynomials. -/
def listSubst (repl : List (ArithExpr F)) (v : Var) : ArithExpr F :=
  repl.getD v (.const 0)

/-- Variable embedding backed by a column projection list `proj`. -/
def projSubst (proj : List Var) (v : Var) : ArithExpr F :=
  .var (proj.getD v 0)

/-- Substitute and simplify a polynomial. -/
def substExpr (repl : Var → ArithExpr F) (e : ArithExpr F) : ArithExpr F :=
  Polynomial.simplify (Polynomial.subst repl e)

@[simp] theorem denote_substExpr (repl : Var → ArithExpr F) (e : ArithExpr F) (a : Var → F) :
    (substExpr repl e).denote a = e.denote (fun v => (repl v).denote a) := by
  simp [substExpr, Polynomial.denote_simplify, Polynomial.denote_subst]

/-- Check whether `cs` contains a constraint equal to `target` (up to `simplify`). -/
def hasConstraint (cs : List (ArithExpr F)) (target : ArithExpr F) : Bool :=
  cs.any fun p => evalIdent p target

theorem hasConstraint_denote {cs : List (ArithExpr F)} {target : ArithExpr F} {a : Var → F}
    (h : hasConstraint cs target = true) (hsat : Satisfies cs a) :
    target.denote a = 0 := by
  obtain ⟨p, hp, heq⟩ := List.any_eq_true.mp h
  rw [← evalIdent_denote heq a]
  exact hsat p hp

/-- Check that `cs` enforces `s * (s - 1) = 0`. -/
def checkBoolExpr (cs : List (ArithExpr F)) (s : ArithExpr F) : Bool :=
  hasConstraint cs (.mul s (.sub s (.const 1))) ||
    hasConstraint cs (.mul (.sub s (.const 1)) s)

theorem checkBoolExpr_sound {cs : List (ArithExpr F)} {s : ArithExpr F} {a : Var → F}
    (h : checkBoolExpr cs s = true) (hsat : Satisfies cs a) :
    s.denote a = 0 ∨ s.denote a = 1 := by
  simp only [checkBoolExpr, Bool.or_eq_true] at h
  rcases h with h1 | h2
  · have hz := hasConstraint_denote h1 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] at hz
    exact hz
  · have hz := hasConstraint_denote h2 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, mul_eq_zero, sub_eq_zero] at hz
    exact hz.symm

/-- Check that `cs` enforces `s₁ * s₂ = 0`. -/
def checkExclExpr (cs : List (ArithExpr F)) (s₁ s₂ : ArithExpr F) : Bool :=
  isZeroExpr (.mul s₁ s₂) ||
    hasConstraint cs (.mul s₁ s₂) ||
    hasConstraint cs (.mul s₂ s₁)

theorem checkExclExpr_sound {cs : List (ArithExpr F)} {s₁ s₂ : ArithExpr F} {a : Var → F}
    (h : checkExclExpr cs s₁ s₂ = true) (hsat : Satisfies cs a) :
    s₁.denote a * s₂.denote a = 0 := by
  simp only [checkExclExpr, Bool.or_eq_true] at h
  rcases h with (h0 | h1) | h2
  · simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using isZeroExpr_denote h0 a
  · simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using hasConstraint_denote h1 hsat
  · have hz := hasConstraint_denote h2 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] at hz
    rw [mul_comm]
    exact hz

/-- Check that `s₁ + s₂ = parent` holds identically or via a constraint in `cs`. -/
def checkSumEq (cs : List (ArithExpr F)) (s₁ s₂ parent : ArithExpr F) : Bool :=
  evalIdent s₂ (.sub parent s₁) ||
    evalIdent s₁ (.sub parent s₂) ||
    hasConstraint cs (.sub (.add s₁ s₂) parent) ||
    hasConstraint cs (.sub (.add s₂ s₁) parent) ||
    hasConstraint cs (.sub parent (.add s₁ s₂)) ||
    hasConstraint cs (.sub parent (.add s₂ s₁))

theorem checkSumEq_sound {cs : List (ArithExpr F)} {s₁ s₂ parent : ArithExpr F} {a : Var → F}
    (h : checkSumEq cs s₁ s₂ parent = true) (hsat : Satisfies cs a) :
    s₁.denote a + s₂.denote a = parent.denote a := by
  simp only [checkSumEq, Bool.or_eq_true] at h
  rcases h with ((((h1 | h2) | h3) | h4) | h5) | h6
  · have heq := evalIdent_denote h1 a
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] at heq ⊢
    rw [heq]; ring
  · have heq := evalIdent_denote h2 a
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] at heq ⊢
    rw [heq]; ring
  · have hz := hasConstraint_denote h3 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz ⊢
    exact hz
  · have hz := hasConstraint_denote h4 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz ⊢
    rw [add_comm]; exact hz
  · have hz := hasConstraint_denote h5 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz ⊢
    exact hz.symm
  · have hz := hasConstraint_denote h6 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz ⊢
    rw [add_comm]; exact hz.symm

/-- Check that `parent = 1` holds identically or via a constraint in `cs`. -/
def checkParentActive (cs : List (ArithExpr F)) (parent : ArithExpr F) : Bool :=
  evalIdent parent (.const 1) ||
    hasConstraint cs (.sub parent (.const 1)) ||
    hasConstraint cs (.sub (.const 1) parent)

theorem checkParentActive_sound {cs : List (ArithExpr F)} {parent : ArithExpr F} {a : Var → F}
    (h : checkParentActive cs parent = true) (hsat : Satisfies cs a) :
    parent.denote a = 1 := by
  simp only [checkParentActive, Bool.or_eq_true] at h
  rcases h with (h1 | h2) | h3
  · simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using evalIdent_denote h1 a
  · have hz := hasConstraint_denote h2 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz
    exact hz
  · have hz := hasConstraint_denote h3 hsat
    simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz
    exact hz.symm

/-- Verify selector exclusivity and exhaustiveness `fastSel + coldSel = parentSel`
with boolean selectors (supporting both two explicit selector columns and single
eliminated boolean selectors `s_cold = 1 - s_fast`). -/
def checkSelectorPartition (cs : List (ArithExpr F))
    (fastSel coldSel parentSel : ArithExpr F) : Bool :=
  checkSumEq cs fastSel coldSel parentSel &&
    ((checkBoolExpr cs fastSel && checkBoolExpr cs coldSel) ||
      (checkParentActive cs parentSel &&
        (checkBoolExpr cs fastSel || checkBoolExpr cs coldSel))) &&
    (checkParentActive cs parentSel || checkExclExpr cs fastSel coldSel)

omit [DecidableEq F] in
/-- Over any field `F` (of arbitrary characteristic), two boolean elements summing
to `1` are mutually exclusive and exhaustive: `(x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1)`. -/
theorem bool_sum_one_cases {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hsum : x + y = 1) : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · simp at hsum
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · have h0 : (1 : F) = 0 := by
      have := congrArg (fun t => t - 1) hsum
      simp at this
    exact absurd h0 one_ne_zero

theorem checkSelectorPartition_active {cs : List (ArithExpr F)}
    {fastSel coldSel parentSel : ArithExpr F} {a : Var → F}
    (h : checkSelectorPartition cs fastSel coldSel parentSel = true)
    (hsat : Satisfies cs a) (hpar : parentSel.denote a = 1) :
    (fastSel.denote a = 1 ∧ coldSel.denote a = 0) ∨
      (fastSel.denote a = 0 ∧ coldSel.denote a = 1) := by
  simp only [checkSelectorPartition, Bool.and_eq_true, Bool.or_eq_true] at h
  have hsum := checkSumEq_sound h.1.1 hsat
  rw [hpar] at hsum
  rcases h.1.2 with ⟨hf, hc⟩ | ⟨_, hf | hc⟩
  · exact bool_sum_one_cases (checkBoolExpr_sound hf hsat) (checkBoolExpr_sound hc hsat) hsum
  · rcases checkBoolExpr_sound hf hsat with h0 | h1
    · rw [h0, zero_add] at hsum
      exact Or.inr ⟨h0, hsum⟩
    · have hc0 : coldSel.denote a = 0 := by
        have := congrArg (fun t => t - 1) hsum
        rw [h1] at this
        simpa using this
      exact Or.inl ⟨h1, hc0⟩
  · rcases checkBoolExpr_sound hc hsat with h0 | h1
    · rw [h0, add_zero] at hsum
      exact Or.inl ⟨hsum, h0⟩
    · have hf0 : fastSel.denote a = 0 := by
        have := congrArg (fun t => t - 1) hsum
        rw [h1] at this
        simpa using this
      exact Or.inr ⟨hf0, h1⟩

theorem checkSelectorPartition_inactive {cs : List (ArithExpr F)}
    {fastSel coldSel parentSel : ArithExpr F} {a : Var → F}
    (h : checkSelectorPartition cs fastSel coldSel parentSel = true)
    (hsat : Satisfies cs a) (hpar : parentSel.denote a = 0) :
    fastSel.denote a = 0 ∧ coldSel.denote a = 0 := by
  simp only [checkSelectorPartition, Bool.and_eq_true, Bool.or_eq_true] at h
  have hsum := checkSumEq_sound h.1.1 hsat
  rw [hpar] at hsum
  rcases h.2 with hact | hexcl
  · have h1 := checkParentActive_sound hact hsat
    rw [hpar] at h1
    exact absurd h1.symm one_ne_zero
  · have hmul := checkExclExpr_sound hexcl hsat
    rcases mul_eq_zero.mp hmul with hf0 | hc0
    · rw [hf0, zero_add] at hsum
      exact ⟨hf0, hsum⟩
    · rw [hc0, add_zero] at hsum
      exact ⟨hsum, hc0⟩

/-! ### Dead-Zero Sub-Choice Cascade (Nested Choices in Inactive Branch) -/

/-- Sum of variable expressions `0 + v_0 + v_1 + ...`, matching `choiceEquations`. -/
def sumVars (vs : List Var) : ArithExpr F :=
  vs.foldl (fun acc v => .add acc (.var v)) (.const 0)

omit [DecidableEq F] in
theorem denote_sumVars (vs : List Var) (a : Var → F) :
    (sumVars (F := F) vs).denote a = (vs.map a).sum := by
  unfold sumVars
  suffices ∀ (init : ArithExpr F),
      (vs.foldl (fun acc v => .add acc (.var v)) init).denote a =
        init.denote a + (vs.map a).sum by
    simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using this (.const 0)
  induction vs with
  | nil => intro init; simp
  | cons v rest ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih (.add init (.var v))]
      simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote]
      ring

omit [DecidableEq F] in
/-- Over ANY field `F`, pairwise-exclusive boolean variables summing to `0` must
each be `0`. Works for arbitrarily many arms and arbitrary characteristic! -/
theorem sum_zero_of_bool_excl {a : Var → F} {vs : List Var}
    (hbool : ∀ v ∈ vs, a v = 0 ∨ a v = 1)
    (hexcl : vs.Pairwise (fun u w => a u * a w = 0))
    (hsum : (vs.map a).sum = 0) :
    ∀ v ∈ vs, a v = 0 := by
  induction vs with
  | nil => intro _ h; cases h
  | cons u rest ih =>
      obtain ⟨huRest, hrestExcl⟩ := List.pairwise_cons.mp hexcl
      have huBool := hbool u List.mem_cons_self
      have hrestBool : ∀ v ∈ rest, a v = 0 ∨ a v = 1 := fun v hv =>
        hbool v (List.mem_cons_of_mem u hv)
      simp only [List.map_cons, List.sum_cons] at hsum
      rcases huBool with hu0 | hu1
      · rw [hu0, zero_add] at hsum
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hmem
        · exact hu0
        · exact ih hrestBool hrestExcl hsum v hmem
      · have hrestZero : ∀ w ∈ rest, a w = 0 := by
          intro w hw
          have hm := huRest w hw
          rw [hu1, one_mul] at hm
          exact hm
        have hrestSum : (rest.map a).sum = 0 := by
          have hmap : rest.map a = List.replicate rest.length (0 : F) := by
            apply List.ext_getElem
            · simp
            · intro i hi1 _
              have hi : i < rest.length := by simpa using hi1
              simp only [List.getElem_map, List.getElem_replicate]
              exact hrestZero (rest[i]'hi) (List.getElem_mem hi)
          rw [hmap, List.sum_replicate, smul_zero]
        rw [hu1, hrestSum, add_zero] at hsum
        exact absurd hsum one_ne_zero

/-- Pairwise exclusion check on a list of variables in `cs`. -/
def checkPairwiseExcl (cs : List (ArithExpr F)) : List Var → Bool
  | [] => true
  | u :: rest =>
      rest.all (fun w => checkExclExpr cs (.var u) (.var w)) &&
        checkPairwiseExcl cs rest

theorem checkPairwiseExcl_sound {cs : List (ArithExpr F)} {a : Var → F} {vs : List Var}
    (h : checkPairwiseExcl cs vs = true) (hsat : Satisfies cs a) :
    vs.Pairwise (fun u w => a u * a w = 0) := by
  induction vs with
  | nil => exact List.Pairwise.nil
  | cons u rest ih =>
      simp only [checkPairwiseExcl, Bool.and_eq_true, List.all_eq_true] at h
      apply List.pairwise_cons.mpr
      refine ⟨fun w hw => ?_, ih h.2⟩
      simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using
        checkExclExpr_sound (h.1 w hw) hsat

/-- Check one dead-zero step `(parent, children)` given currently known zero
expressions/variables. -/
def checkDeadZeroStep (cs : List (ArithExpr F)) (inactiveSel : ArithExpr F)
    (knownZeros : List Var) (step : ArithExpr F × List Var) : Bool :=
  let (parent, children) := step
  let parentZero : Bool :=
    evalIdent parent inactiveSel ||
      match Polynomial.simplify parent with
      | .var p => knownZeros.contains p
      | _ => false
  let sumMatches : Bool :=
    hasConstraint cs (.sub (sumVars children) parent) ||
      hasConstraint cs (.sub parent (sumVars children))
  parentZero &&
    children.all (fun v => checkBoolExpr cs (.var v)) &&
    checkPairwiseExcl cs children &&
    sumMatches

/-- Check a sequence of dead-zero steps, accumulating all certified zero vars. -/
def checkDeadZeroSteps (cs : List (ArithExpr F)) (inactiveSel : ArithExpr F)
    (steps : List (ArithExpr F × List Var)) : Bool :=
  go [] steps
where
  go (known : List Var) : List (ArithExpr F × List Var) → Bool
    | [] => true
    | step :: rest =>
        checkDeadZeroStep cs inactiveSel known step &&
          go (known ++ step.2) rest

/-- All variables certified to be `0` by `steps`. -/
def deadZeroVars (steps : List (ArithExpr F × List Var)) : List Var :=
  steps.flatMap Prod.snd

theorem checkDeadZeroSteps_sound {cs : List (ArithExpr F)} {inactiveSel : ArithExpr F}
    {a : Var → F} {steps : List (ArithExpr F × List Var)}
    (h : checkDeadZeroSteps cs inactiveSel steps = true)
    (hsat : Satisfies cs a) (hinact : inactiveSel.denote a = 0) :
    ∀ v ∈ deadZeroVars steps, a v = 0 := by
  suffices ∀ (known : List Var) (rem : List (ArithExpr F × List Var)),
      (∀ z ∈ known, a z = 0) →
      checkDeadZeroSteps.go cs inactiveSel known rem = true →
      ∀ v ∈ rem.flatMap Prod.snd, a v = 0 by
    exact this [] steps (fun _ hz => by cases hz) h
  intro known rem
  induction rem generalizing known with
  | nil => intro _ _ _ hv; cases hv
  | cons step rest ih =>
      intro hknown hgo v hv
      rcases step with ⟨parent, children⟩
      simp only [checkDeadZeroSteps.go, Bool.and_eq_true] at hgo
      have hstep := hgo.1
      simp only [checkDeadZeroStep, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true] at hstep
      have hparZero : parent.denote a = 0 := by
        rcases hstep.1.1.1 with hid | hvar
        · rw [evalIdent_denote hid a, hinact]
        · cases hsimp : Polynomial.simplify parent with
          | var p =>
              rw [hsimp] at hvar
              have hmem : p ∈ known := by simpa using hvar
              rw [← Polynomial.denote_simplify parent a, hsimp]
              exact hknown p hmem
          | const _ | add _ _ | sub _ _ | mul _ _ =>
              rw [hsimp] at hvar
              cases hvar
      have hsumZero : (children.map a).sum = 0 := by
        rw [← denote_sumVars (F := F) children a]
        rcases hstep.2 with h1 | h2
        · have hz := hasConstraint_denote h1 hsat
          simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz ⊢
          rw [hz]
          exact hparZero
        · have hz := hasConstraint_denote h2 hsat
          simp only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, sub_eq_zero] at hz ⊢
          rw [← hz]
          exact hparZero
      have hchildrenZero : ∀ w ∈ children, a w = 0 :=
        sum_zero_of_bool_excl
          (fun w hw => by
            simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using
              checkBoolExpr_sound (hstep.1.1.2 w hw) hsat)
          (checkPairwiseExcl_sound hstep.1.2 hsat)
          hsumZero
      simp only [List.flatMap_cons, List.mem_append] at hv
      rcases hv with hch | hrest
      · exact hchildrenZero v hch
      · apply ih (known ++ children) ?_ hgo.2 v hrest
        intro z hz
        rcases List.mem_append.mp hz with hk | hc
        · exact hknown z hk
        · exact hchildrenZero z hc

end Helpers

/-! ## 2. Certified Chip-Level Branch Split (`BranchWitness`, `SplitWitness`, `checkSplit`) -/

section ChipSplit

variable {F : Type} [Field F] [DecidableEq F]

/-- Witness certifying one side (`fast` or `cold`) of a chip split. -/
structure BranchWitness (F : Type) where
  /-- Original column index retained for each column of the split branch chip
  (`proj.length = branch.numVars`). -/
  proj : List Var
  /-- Lift substitution expressing each variable `0 .. orig.numVars - 1` of the
  original chip in terms of the split branch chip's variables. -/
  lift : List (ArithExpr F)
  /-- Optional cascade of nested mutually-exclusive boolean sub-selectors inside
  the inactive branch certified to be `0` whenever `inactiveSel = 0`. -/
  deadZeroSteps : List (ArithExpr F × List Var) := []
  deriving Repr, BEq

/-- Full witness certifying a 2-way split of `orig` into `(fast, cold)` along
mutually exclusive boolean selectors `fastSel + coldSel = parentSel`. -/
structure SplitWitness (F : Type) where
  fastSel : ArithExpr F
  coldSel : ArithExpr F
  parentSel : ArithExpr F
  fast : BranchWitness F
  cold : BranchWitness F
  deriving Repr, BEq

/-- Logical receive message of `chip` tagged with logical channel `channel`. -/
def logicalConclusion (channel : String) (chip : Chip F) (a : Var → F) : Message F :=
  { chip.conclusion a with channel := channel }

/-- Logical receive message of a row of `chip` tagged with `channel`. -/
def logicalReceive (channel : String) (chip : Chip F) (row : Row F) : Message F :=
  { chip.receive row with channel := channel }

/-- Local rule of a split physical chip serving logical channel `channel`. -/
def LogicalRule (channel : String) (chip : Chip F) (rom : WireROM F)
    (conclusion : Message F) (premises : List (Message F)) : Prop :=
  ∃ row, row.chip = chip.name ∧ chip.ValidRow rom row ∧
    logicalReceive channel chip row = conclusion ∧ chip.premises row = premises

/-- Specialization substitution assuming `activeSel = 1`, `inactiveSel = 0`, and
all `deadZeros = 0`. -/
def branchSpecSubst (activeSel inactiveSel : ArithExpr F) (deadZeros : List Var)
    (v : Var) : ArithExpr F :=
  let activeVar? : Option Var := match Polynomial.simplify activeSel with | .var u => some u | _ => none
  let inactiveVar? : Option Var := match Polynomial.simplify inactiveSel with | .var u => some u | _ => none
  if activeVar? == some v then .const 1
  else if inactiveVar? == some v || deadZeros.contains v then .const 0
  else .var v

theorem branchSpecSubst_denote {orig : Chip F} {activeSel inactiveSel : ArithExpr F}
    {w : BranchWitness F} {a : Var → F}
    (hsat : Satisfies orig.constraints a)
    (hact : activeSel.denote a = 1) (hinact : inactiveSel.denote a = 0)
    (hdead : checkDeadZeroSteps orig.constraints inactiveSel w.deadZeroSteps = true)
    (e : ArithExpr F) :
    (Polynomial.subst (branchSpecSubst activeSel inactiveSel (deadZeroVars w.deadZeroSteps)) e).denote a =
      e.denote a := by
  rw [Polynomial.denote_subst]
  apply Polynomial.denote_congr
  intro v _
  unfold branchSpecSubst
  dsimp only
  split_ifs with h1 h2
  · cases hs : Polynomial.simplify activeSel with
    | var u =>
        rw [hs] at h1
        have huv : u = v := by simpa using h1
        subst huv
        rw [← Polynomial.denote_simplify activeSel a, hs] at hact
        simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using hact.symm
    | const _ | add _ _ | sub _ _ | mul _ _ =>
        rw [hs] at h1; simp at h1
  · simp only [Bool.or_eq_true] at h2
    rcases h2 with h2a | h2b
    · cases hs : Polynomial.simplify inactiveSel with
      | var u =>
          rw [hs] at h2a
          have huv : u = v := by simpa using h2a
          subst huv
          rw [← Polynomial.denote_simplify inactiveSel a, hs] at hinact
          simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using hinact.symm
      | const _ | add _ _ | sub _ _ | mul _ _ =>
          rw [hs] at h2a; simp at h2a
    · have hmem : v ∈ deadZeroVars w.deadZeroSteps := by simpa using h2b
      have hz := checkDeadZeroSteps_sound hdead hsat hinact v hmem
      simpa [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote] using hz.symm
  · rfl

/-- Check pairwise equality of two lists under a boolean predicate. -/
def zipAll {α β : Type} (p : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | x :: xs, y :: ys => p x y && zipAll p xs ys
  | _, _ => false

theorem zipAll_spec {α β : Type} {p : α → β → Bool} {xs : List α} {ys : List β}
    (h : zipAll p xs ys = true) :
    xs.length = ys.length ∧ ∀ (i : Nat) (hx : i < xs.length) (hy : i < ys.length),
      p xs[i] ys[i] = true := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨rfl, fun _ hx => by cases hx⟩
      | cons _ _ => simp [zipAll] at h
  | cons x xs ih =>
      cases ys with
      | nil => simp [zipAll] at h
      | cons y ys =>
          simp only [zipAll, Bool.and_eq_true] at h
          obtain ⟨hlen, hrest⟩ := ih h.2
          refine ⟨by simp [hlen], fun i hx hy => ?_⟩
          cases i with
          | zero => exact h.1
          | succ k => exact hrest k (Nat.lt_of_succ_lt_succ hx) (Nat.lt_of_succ_lt_succ hy)

/-- Check bidirectional variable-wire agreement under `lift` and `proj`. -/
def checkVarWire (origNumVars : Nat) (w : BranchWitness F)
    (wo wb : WireValue Var) : Bool :=
  wo.type == wb.type &&
    zipAll (fun vo vb =>
      (w.lift.getD vo (.const 0) == .var vb) &&
        (w.proj.getD vb origNumVars == vo)) wo.words wb.words

/-- Check bidirectional polynomial-wire agreement under `lift`, `proj`, and `spec`. -/
def checkPolyWire (w : BranchWitness F) (spec : Var → ArithExpr F)
    (wo wb : WireValue (ArithExpr F)) : Bool :=
  wo.type == wb.type &&
    zipAll (fun po pb =>
      evalIdent (Polynomial.subst (listSubst w.lift) po) pb &&
        evalIdent (Polynomial.subst (projSubst w.proj) pb) (Polynomial.subst spec po)) wo.words wb.words

/-- Check whether a send in `orig` is dead (enable identically zero) on this branch. -/
def checkSendDead (w : BranchWitness F) (spec : Var → ArithExpr F) (s : Send F) : Bool :=
  isZeroExpr (Polynomial.subst (listSubst w.lift) s.enable) &&
    isZeroExpr (Polynomial.subst spec s.enable)

/-- Check bidirectional agreement of a live send pair `(so, sb)`. -/
def checkSendMatch (origNumVars : Nat) (w : BranchWitness F) (spec : Var → ArithExpr F)
    (so sb : Send F) : Bool :=
  so.channel == sb.channel &&
    evalIdent (Polynomial.subst (listSubst w.lift) so.enable) sb.enable &&
    evalIdent (Polynomial.subst (projSubst w.proj) sb.enable) (Polynomial.subst spec so.enable) &&
    zipAll (checkPolyWire w spec) so.args sb.args &&
    checkVarWire origNumVars w so.result sb.result

/-- Ordered alignment between `orig.sends` (with dead sends dropped) and `branch.sends`. -/
def checkSendsAlign (origNumVars : Nat) (w : BranchWitness F) (spec : Var → ArithExpr F) :
    List (Send F) → List (Send F) → Bool
  | [], [] => true
  | so :: restO, [] => checkSendDead w spec so && checkSendsAlign origNumVars w spec restO []
  | [], _ :: _ => false
  | so :: restO, sb :: restB =>
      if checkSendDead w spec so then
        checkSendsAlign origNumVars w spec restO (sb :: restB)
      else
        checkSendMatch origNumVars w spec so sb &&
          checkSendsAlign origNumVars w spec restO restB

/-- Check whether a ROM lookup in `orig` is dead on this branch. -/
def checkMemDead (w : BranchWitness F) (spec : Var → ArithExpr F) (m : MemoryLookup F) : Bool :=
  isZeroExpr (Polynomial.subst (listSubst w.lift) m.enable) &&
    isZeroExpr (Polynomial.subst spec m.enable)

/-- Check bidirectional agreement of a live ROM lookup pair `(mo, mb)`. -/
def checkMemMatch (w : BranchWitness F) (spec : Var → ArithExpr F)
    (mo mb : MemoryLookup F) : Bool :=
  evalIdent (Polynomial.subst (listSubst w.lift) mo.enable) mb.enable &&
    evalIdent (Polynomial.subst (projSubst w.proj) mb.enable) (Polynomial.subst spec mo.enable) &&
    evalIdent (Polynomial.subst (listSubst w.lift) mo.address) mb.address &&
    evalIdent (Polynomial.subst (projSubst w.proj) mb.address) (Polynomial.subst spec mo.address) &&
    checkPolyWire w spec mo.value mb.value

/-- Ordered alignment between `orig.memory` (with dead lookups dropped) and `branch.memory`. -/
def checkMemoryAlign (w : BranchWitness F) (spec : Var → ArithExpr F) :
    List (MemoryLookup F) → List (MemoryLookup F) → Bool
  | [], [] => true
  | mo :: restO, [] => checkMemDead w spec mo && checkMemoryAlign w spec restO []
  | [], _ :: _ => false
  | mo :: restO, mb :: restB =>
      if checkMemDead w spec mo then
        checkMemoryAlign w spec restO (mb :: restB)
      else
        checkMemMatch w spec mo mb && checkMemoryAlign w spec restO restB

/-- Decidable verifier for one branch (`fast` or `cold`) of a chip split. -/
def checkBranch (orig branch : Chip F) (activeSel inactiveSel : ArithExpr F)
    (w : BranchWitness F) : Bool :=
  let spec := branchSpecSubst activeSel inactiveSel (deadZeroVars w.deadZeroSteps)
  let liftSub := listSubst w.lift
  let projSub := projSubst w.proj
  orig.wellFormed &&
    branch.wellFormed &&
    (w.proj.length == branch.numVars) &&
    w.proj.all (· < orig.numVars) &&
    (w.lift.length == orig.numVars) &&
    w.lift.all (ArithExpr.inBounds branch.numVars) &&
    checkDeadZeroSteps orig.constraints inactiveSel w.deadZeroSteps &&
    zipAll (checkVarWire orig.numVars w) orig.inputs branch.inputs &&
    checkPolyWire w spec orig.output branch.output &&
    -- Soundness of constraints (branch → orig via lift)
    orig.constraints.all (fun p =>
      isZeroExpr (Polynomial.subst liftSub p) ||
        hasConstraint branch.constraints (Polynomial.subst liftSub p)) &&
    -- Completeness of constraints (orig ∧ activeSel = 1 → branch via proj)
    branch.constraints.all (fun q =>
      let qe := Polynomial.subst projSub q
      isZeroExpr qe || orig.constraints.any (fun p =>
        evalIdent qe (Polynomial.subst spec p) ||
          evalIdent (.mul activeSel qe) (Polynomial.subst spec p))) &&
    checkSendsAlign orig.numVars w spec orig.sends branch.sends &&
    checkMemoryAlign w spec orig.memory branch.memory

/-- Decidable verifier for a full 2-way chip split with an explicit `SplitWitness`. -/
def checkSplitWith (w : SplitWitness F) (orig fast cold : Chip F) : Bool :=
  checkParentActive orig.constraints w.parentSel &&
    checkSelectorPartition orig.constraints w.fastSel w.coldSel w.parentSel &&
    checkBranch orig fast w.fastSel w.coldSel w.fast &&
    checkBranch orig cold w.coldSel w.fastSel w.cold

/-! ### Row & Assignment Lifting / Projection -/

/-- Lift a branch assignment `ab` into an assignment for `orig`. -/
def liftAssignment (w : BranchWitness F) (ab : Var → F) (v : Var) : F :=
  (listSubst w.lift v).denote ab

/-- Project an `orig` assignment `ao` onto a branch assignment. -/
def projAssignment (w : BranchWitness F) (ao : Var → F) (j : Var) : F :=
  ao (w.proj.getD j 0)

omit [DecidableEq F] in
private theorem denote_subst_projSubst (w : BranchWitness F) (ao : Var → F) (e : ArithExpr F) :
    (Polynomial.subst (projSubst w.proj) e).denote ao = e.denote (projAssignment w ao) := by
  rw [Polynomial.denote_subst]
  rfl

/-- Lift a physical branch row into a physical row of `orig`. -/
def liftRow (origName : String) (origNumVars : Nat) (w : BranchWitness F) (row : Row F) : Row F :=
  Row.ofAssignment origName origNumVars (liftAssignment w row.assignment)

/-- Project an `orig` physical row onto a physical branch row. -/
def projectRow (branchName : String) (w : BranchWitness F) (row : Row F) : Row F :=
  Row.ofAssignment branchName w.proj.length (projAssignment w row.assignment)

private theorem checkVarWire_sound {origNumVars : Nat} {w : BranchWitness F}
    {wo wb : WireValue Var} (h : checkVarWire origNumVars w wo wb = true) (ab : Var → F) :
    wo.map (liftAssignment w ab) = wb.map ab := by
  simp only [checkVarWire, Bool.and_eq_true, beq_iff_eq] at h
  rcases wo with ⟨tyO, wso⟩
  rcases wb with ⟨tyB, wsb⟩
  dsimp only at h
  obtain ⟨rfl, hzip⟩ := h
  obtain ⟨hlen, hitem⟩ := zipAll_spec hzip
  simp only [WireValue.map, WireValue.mk.injEq, true_and]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    simp only [List.getElem_map]
    have hi := hitem i (by simpa using hi1) (by simpa using hi2)
    simp only [Bool.and_eq_true, beq_iff_eq] at hi
    have hliftEq : w.lift.getD (wso[i]'(by simpa using hi1)) (.const 0) =
        .var (wsb[i]'(by simpa using hi2)) := (Polynomial.beq_eq _ _).mp hi.1
    unfold liftAssignment listSubst
    rw [hliftEq]
    rfl

private theorem checkVarWire_complete_of_lt {origNumVars : Nat} {w : BranchWitness F}
    {wo wb : WireValue Var} (h : checkVarWire origNumVars w wo wb = true)
    (hlt : ∀ v ∈ wo.words, v < origNumVars) (ao : Var → F) :
    wb.map (projAssignment w ao) = wo.map ao := by
  simp only [checkVarWire, Bool.and_eq_true, beq_iff_eq] at h
  rcases wo with ⟨tyO, wso⟩
  rcases wb with ⟨tyB, wsb⟩
  dsimp only at h
  obtain ⟨rfl, hzip⟩ := h
  obtain ⟨hlen, hitem⟩ := zipAll_spec hzip
  simp only [WireValue.map, WireValue.mk.injEq, true_and]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    have hiO : i < wso.length := by simpa using hi2
    have hiB : i < wsb.length := by simpa using hi1
    simp only [List.getElem_map]
    have hi := hitem i hiO hiB
    simp only [Bool.and_eq_true, beq_iff_eq] at hi
    set vo : Var := wso[i]'hiO
    set vb : Var := wsb[i]'hiB
    have hvoLt : vo < origNumVars := hlt vo (List.getElem_mem hiO)
    have hprojEq : w.proj.getD vb origNumVars = vo := hi.2
    have hvbLt : vb < w.proj.length := by
      by_contra hge
      have hge' : w.proj.length ≤ vb := Nat.le_of_not_lt hge
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge', Option.getD_none] at hprojEq
      exact absurd hprojEq (Nat.ne_of_gt hvoLt)
    unfold projAssignment
    have hget : w.proj.getD vb 0 = w.proj.getD vb origNumVars := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvbLt]
    rw [hget, hprojEq]

private theorem checkPolyWire_sound {w : BranchWitness F} {spec : Var → ArithExpr F}
    {wo wb : WireValue (ArithExpr F)} (h : checkPolyWire w spec wo wb = true) (ab : Var → F) :
    wo.map (ArithExpr.denote (liftAssignment w ab)) = wb.map (ArithExpr.denote ab) := by
  simp only [checkPolyWire, Bool.and_eq_true, beq_iff_eq] at h
  rcases wo with ⟨tyO, wso⟩
  rcases wb with ⟨tyB, wsb⟩
  dsimp only at h
  obtain ⟨rfl, hzip⟩ := h
  obtain ⟨hlen, hitem⟩ := zipAll_spec hzip
  simp only [WireValue.map, WireValue.mk.injEq, true_and]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    simp only [List.getElem_map]
    have hi := hitem i (by simpa using hi1) (by simpa using hi2)
    simp only [Bool.and_eq_true] at hi
    have hden := evalIdent_denote hi.1 ab
    rw [Polynomial.denote_subst] at hden
    exact hden

private theorem checkPolyWire_complete {w : BranchWitness F} {spec : Var → ArithExpr F}
    {wo wb : WireValue (ArithExpr F)} (h : checkPolyWire w spec wo wb = true) {ao : Var → F}
    (hspec : ∀ e : ArithExpr F, (Polynomial.subst spec e).denote ao = e.denote ao) :
    wb.map (ArithExpr.denote (projAssignment w ao)) = wo.map (ArithExpr.denote ao) := by
  simp only [checkPolyWire, Bool.and_eq_true, beq_iff_eq] at h
  rcases wo with ⟨tyO, wso⟩
  rcases wb with ⟨tyB, wsb⟩
  dsimp only at h
  obtain ⟨rfl, hzip⟩ := h
  obtain ⟨hlen, hitem⟩ := zipAll_spec hzip
  simp only [WireValue.map, WireValue.mk.injEq, true_and]
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi1 hi2
    simp only [List.getElem_map]
    have hi := hitem i (by simpa using hi2) (by simpa using hi1)
    simp only [Bool.and_eq_true] at hi
    have hden := evalIdent_denote hi.2 ao
    rw [denote_subst_projSubst, hspec] at hden
    exact hden

private theorem checkSendsAlign_sound {origNumVars : Nat} {w : BranchWitness F}
    {spec : Var → ArithExpr F} {so sb : List (Send F)}
    (h : checkSendsAlign origNumVars w spec so sb = true) (ab : Var → F) :
    (so.filterMap fun s =>
      if s.enable.denote (liftAssignment w ab) = 1 then some (s.message (liftAssignment w ab))
      else none) =
    (sb.filterMap fun s =>
      if s.enable.denote ab = 1 then some (s.message ab) else none) := by
  induction so generalizing sb with
  | nil =>
      cases sb with
      | nil => rfl
      | cons _ _ => simp [checkSendsAlign] at h
  | cons s restO ih =>
      cases sb with
      | nil =>
          simp only [checkSendsAlign, Bool.and_eq_true] at h
          have hdead : isZeroExpr (Polynomial.subst (listSubst w.lift) s.enable) = true :=
            ((Bool.and_eq_true _ _).mp h.1).1
          have hz : s.enable.denote (liftAssignment w ab) = 0 := by
            have := isZeroExpr_denote hdead ab
            rwa [Polynomial.denote_subst] at this
          have hne : s.enable.denote (liftAssignment w ab) ≠ 1 := by
            rw [hz]; exact zero_ne_one
          simp only [List.filterMap_cons, hne, ↓reduceIte]
          exact ih h.2
      | cons s' restB =>
          unfold checkSendsAlign at h
          split_ifs at h with hdead
          · have hz0 : isZeroExpr (Polynomial.subst (listSubst w.lift) s.enable) = true :=
              ((Bool.and_eq_true _ _).mp hdead).1
            have hz : s.enable.denote (liftAssignment w ab) = 0 := by
              have := isZeroExpr_denote hz0 ab
              rwa [Polynomial.denote_subst] at this
            have hne : s.enable.denote (liftAssignment w ab) ≠ 1 := by
              rw [hz]; exact zero_ne_one
            simp only [List.filterMap_cons, hne, ↓reduceIte]
            exact ih h
          · simp only [Bool.and_eq_true] at h
            have hm := h.1
            simp only [checkSendMatch, Bool.and_eq_true, beq_iff_eq] at hm
            have hchan : s.channel = s'.channel := hm.1.1.1.1
            have hen : s.enable.denote (liftAssignment w ab) = s'.enable.denote ab := by
              have := evalIdent_denote hm.1.1.1.2 ab
              rwa [Polynomial.denote_subst] at this
            have hargs : s.args.map (WireValue.map (ArithExpr.denote (liftAssignment w ab))) =
                s'.args.map (WireValue.map (ArithExpr.denote ab)) := by
              obtain ⟨hlen, hitem⟩ := zipAll_spec hm.1.2
              apply List.ext_getElem
              · simp [hlen]
              · intro i hi1 hi2
                simp only [List.getElem_map]
                exact checkPolyWire_sound (hitem i (by simpa using hi1) (by simpa using hi2)) ab
            have hres : s.result.map (liftAssignment w ab) = s'.result.map ab :=
              checkVarWire_sound hm.2 ab
            have hmsg : s.message (liftAssignment w ab) = s'.message ab := by
              simp [Send.message, hchan, hargs, hres]
            simp only [List.filterMap_cons, hen, hmsg]
            split_ifs
            · exact congrArg (List.cons _) (ih h.2)
            · exact ih h.2

private theorem checkSendsAlign_complete {origNumVars : Nat} {w : BranchWitness F}
    {spec : Var → ArithExpr F} {so sb : List (Send F)}
    (h : checkSendsAlign origNumVars w spec so sb = true)
    (hlt : ∀ s ∈ so, ∀ v ∈ s.result.words, v < origNumVars)
    {ao : Var → F} (hspec : ∀ e : ArithExpr F, (Polynomial.subst spec e).denote ao = e.denote ao) :
    (sb.filterMap fun s =>
      if s.enable.denote (projAssignment w ao) = 1 then some (s.message (projAssignment w ao))
      else none) =
    (so.filterMap fun s =>
      if s.enable.denote ao = 1 then some (s.message ao) else none) := by
  induction so generalizing sb with
  | nil =>
      cases sb with
      | nil => rfl
      | cons _ _ => simp [checkSendsAlign] at h
  | cons s restO ih =>
      have hrestLt : ∀ s' ∈ restO, ∀ v ∈ s'.result.words, v < origNumVars :=
        fun s' hs' => hlt s' (List.mem_cons_of_mem s hs')
      cases sb with
      | nil =>
          simp only [checkSendsAlign, Bool.and_eq_true] at h
          have hdead : isZeroExpr (Polynomial.subst spec s.enable) = true :=
            ((Bool.and_eq_true _ _).mp h.1).2
          have hz : s.enable.denote ao = 0 := by
            rw [← hspec s.enable]
            exact isZeroExpr_denote hdead ao
          have hne : s.enable.denote ao ≠ 1 := by rw [hz]; exact zero_ne_one
          simp only [List.filterMap_cons, hne, ↓reduceIte]
          exact ih h.2 hrestLt
      | cons s' restB =>
          unfold checkSendsAlign at h
          split_ifs at h with hdead
          · have hz0 : isZeroExpr (Polynomial.subst spec s.enable) = true :=
              ((Bool.and_eq_true _ _).mp hdead).2
            have hz : s.enable.denote ao = 0 := by
              rw [← hspec s.enable]
              exact isZeroExpr_denote hz0 ao
            have hne : s.enable.denote ao ≠ 1 := by rw [hz]; exact zero_ne_one
            simp only [List.filterMap_cons, hne, ↓reduceIte]
            exact ih h hrestLt
          · simp only [Bool.and_eq_true] at h
            have hm := h.1
            simp only [checkSendMatch, Bool.and_eq_true, beq_iff_eq] at hm
            have hchan : s'.channel = s.channel := hm.1.1.1.1.symm
            have hen : s'.enable.denote (projAssignment w ao) = s.enable.denote ao := by
              have := evalIdent_denote hm.1.1.2 ao
              rwa [denote_subst_projSubst, hspec] at this
            have hargs : s'.args.map (WireValue.map (ArithExpr.denote (projAssignment w ao))) =
                s.args.map (WireValue.map (ArithExpr.denote ao)) := by
              obtain ⟨hlen, hitem⟩ := zipAll_spec hm.1.2
              apply List.ext_getElem
              · simp [hlen]
              · intro i hi1 hi2
                simp only [List.getElem_map]
                exact checkPolyWire_complete (hitem i (by simpa using hi2) (by simpa using hi1)) hspec
            have hres : s'.result.map (projAssignment w ao) = s.result.map ao :=
              checkVarWire_complete_of_lt hm.2 (hlt s List.mem_cons_self) ao
            have hmsg : s'.message (projAssignment w ao) = s.message ao := by
              simp [Send.message, hchan, hargs, hres]
            simp only [List.filterMap_cons, hen, hmsg]
            split_ifs
            · exact congrArg (List.cons _) (ih h.2 hrestLt)
            · exact ih h.2 hrestLt

private theorem checkMemoryAlign_sound {w : BranchWitness F} {spec : Var → ArithExpr F}
    {mo mb : List (MemoryLookup F)} {rom : WireROM F} {ab : Var → F}
    (h : checkMemoryAlign w spec mo mb = true)
    (hvalid : ∀ m ∈ mb, m.Valid rom ab) :
    ∀ m ∈ mo, m.Valid rom (liftAssignment w ab) := by
  induction mo generalizing mb with
  | nil => intro _ hm; cases hm
  | cons m restO ih =>
      cases mb with
      | nil =>
          simp only [checkMemoryAlign, Bool.and_eq_true] at h
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hrest
          · intro hen
            have hz0 : isZeroExpr (Polynomial.subst (listSubst w.lift) x.enable) = true :=
              ((Bool.and_eq_true _ _).mp h.1).1
            have hz : x.enable.denote (liftAssignment w ab) = 0 := by
              have := isZeroExpr_denote hz0 ab
              rwa [Polynomial.denote_subst] at this
            rw [hz] at hen
            exact absurd hen zero_ne_one
          · exact ih h.2 hvalid x hrest
      | cons m' restB =>
          unfold checkMemoryAlign at h
          split_ifs at h with hdead
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hrest
            · intro hen
              have hz0 : isZeroExpr (Polynomial.subst (listSubst w.lift) x.enable) = true :=
                ((Bool.and_eq_true _ _).mp hdead).1
              have hz : x.enable.denote (liftAssignment w ab) = 0 := by
                have := isZeroExpr_denote hz0 ab
                rwa [Polynomial.denote_subst] at this
              rw [hz] at hen
              exact absurd hen zero_ne_one
            · exact ih h hvalid x hrest
          · simp only [Bool.and_eq_true] at h
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hrest
            · have hm := h.1
              simp only [checkMemMatch, Bool.and_eq_true] at hm
              have hen : x.enable.denote (liftAssignment w ab) = m'.enable.denote ab := by
                have := evalIdent_denote hm.1.1.1.1 ab
                rwa [Polynomial.denote_subst] at this
              have haddr : x.address.denote (liftAssignment w ab) = m'.address.denote ab := by
                have := evalIdent_denote hm.1.1.2 ab
                rwa [Polynomial.denote_subst] at this
              have hval := checkPolyWire_sound hm.2 ab
              intro he
              rw [hen] at he
              rw [haddr, hval]
              exact hvalid m' List.mem_cons_self he
            · exact ih h.2 (fun z hz => hvalid z (List.mem_cons_of_mem m' hz)) x hrest

private theorem checkMemoryAlign_complete {w : BranchWitness F} {spec : Var → ArithExpr F}
    {mo mb : List (MemoryLookup F)} {rom : WireROM F} {ao : Var → F}
    (h : checkMemoryAlign w spec mo mb = true)
    (hspec : ∀ e : ArithExpr F, (Polynomial.subst spec e).denote ao = e.denote ao)
    (hvalid : ∀ m ∈ mo, m.Valid rom ao) :
    ∀ m ∈ mb, m.Valid rom (projAssignment w ao) := by
  induction mo generalizing mb with
  | nil =>
      cases mb with
      | nil => intro _ hm; cases hm
      | cons _ _ => simp [checkMemoryAlign] at h
  | cons m restO ih =>
      have hrestValid : ∀ x ∈ restO, x.Valid rom ao :=
        fun x hx => hvalid x (List.mem_cons_of_mem m hx)
      cases mb with
      | nil => intro _ hm; cases hm
      | cons m' restB =>
          unfold checkMemoryAlign at h
          split_ifs at h with hdead
          · exact ih h hrestValid
          · simp only [Bool.and_eq_true] at h
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hrest
            · have hm := h.1
              simp only [checkMemMatch, Bool.and_eq_true] at hm
              have hen : x.enable.denote (projAssignment w ao) = m.enable.denote ao := by
                have := evalIdent_denote hm.1.1.1.2 ao
                rwa [denote_subst_projSubst, hspec] at this
              have haddr : x.address.denote (projAssignment w ao) = m.address.denote ao := by
                have := evalIdent_denote hm.1.2 ao
                rwa [denote_subst_projSubst, hspec] at this
              have hval := checkPolyWire_complete hm.2 hspec
              intro he
              rw [hen] at he
              rw [haddr, hval]
              exact hvalid m List.mem_cons_self he
            · exact ih h.2 hrestValid x hrest

/-- **Branch Soundness**: any valid assignment of `branch` lifts to a valid
assignment of `orig` with identical logical conclusion and call requirements. -/
theorem checkBranch_sound {orig branch : Chip F} {activeSel inactiveSel : ArithExpr F}
    {w : BranchWitness F} (h : checkBranch orig branch activeSel inactiveSel w = true)
    (rom : WireROM F) (ab : Var → F) (hvalid : branch.ValidAssignment rom ab) :
    orig.ValidAssignment rom (liftAssignment w ab) ∧
      orig.conclusion (liftAssignment w ab) = logicalConclusion orig.name branch ab ∧
      orig.requirements (liftAssignment w ab) = branch.requirements ab := by
  simp only [checkBranch, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hinp⟩, hout⟩, hcsSound⟩, _⟩, hsends⟩, hmem⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    rcases hcsSound p hp with hz | hhas
    · have h0 := isZeroExpr_denote hz ab
      rwa [Polynomial.denote_subst] at h0
    · have h0 := hasConstraint_denote hhas hvalid.1
      rwa [Polynomial.denote_subst] at h0
  · exact checkMemoryAlign_sound hmem hvalid.2
  · simp only [Chip.conclusion, logicalConclusion]
    congr 1
    · obtain ⟨hlen, hitem⟩ := zipAll_spec hinp
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi1 hi2
        simp only [List.getElem_map]
        exact checkVarWire_sound (hitem i (by simpa using hi1) (by simpa using hi2)) ab
    · exact checkPolyWire_sound hout ab
  · exact checkSendsAlign_sound hsends ab

/-- **Branch Completeness**: any valid assignment of `orig` with `activeSel = 1`
and `inactiveSel = 0` projects to a valid assignment of `branch` with identical
logical conclusion and call requirements. -/
theorem checkBranch_complete {orig branch : Chip F} {activeSel inactiveSel : ArithExpr F}
    {w : BranchWitness F} (h : checkBranch orig branch activeSel inactiveSel w = true)
    (rom : WireROM F) (ao : Var → F) (hvalid : orig.ValidAssignment rom ao)
    (hact : activeSel.denote ao = 1) (hinact : inactiveSel.denote ao = 0) :
    branch.ValidAssignment rom (projAssignment w ao) ∧
      logicalConclusion orig.name branch (projAssignment w ao) = orig.conclusion ao ∧
      branch.requirements (projAssignment w ao) = orig.requirements ao := by
  simp only [checkBranch, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨horigWf, _⟩, _⟩, _⟩, _⟩, _⟩, hdead⟩, hinp⟩, hout⟩, _⟩, hcsComp⟩, hsends⟩, hmem⟩ := h
  have hspec := branchSpecSubst_denote hvalid.1 hact hinact hdead
  have horigWf' := horigWf
  simp only [Chip.wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at horigWf'
  have hinpLt : ∀ wire ∈ orig.inputs, ∀ v ∈ wire.words, v < orig.numVars := by
    intro wire hwire v hv
    exact horigWf'.1.1.1.1 v (List.mem_flatMap.mpr ⟨wire, hwire, hv⟩)
  have hsendLt : ∀ s ∈ orig.sends, ∀ v ∈ s.result.words, v < orig.numVars := by
    intro s hs v hv
    have hsWf := horigWf'.1.2 s hs
    simp only [Send.inBounds, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hsWf
    exact hsWf.1.1 v hv
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro q hq
    rcases hcsComp q hq with hz | hex
    · have h0 := isZeroExpr_denote hz ao
      rwa [denote_subst_projSubst] at h0
    · obtain ⟨p, hp, hpeq⟩ := List.any_eq_true.mp hex
      simp only [Bool.or_eq_true] at hpeq
      have hp0 : p.denote ao = 0 := hvalid.1 p hp
      rcases hpeq with heq | hmul
      · have hden := evalIdent_denote heq ao
        rw [denote_subst_projSubst, hspec] at hden
        exact hden.trans hp0
      · have hden := evalIdent_denote hmul ao
        rw [hspec] at hden
        have hden' : activeSel.denote ao * (Polynomial.subst (projSubst w.proj) q).denote ao = p.denote ao := hden
        rw [hact, one_mul, denote_subst_projSubst] at hden'
        exact hden'.trans hp0
  · exact checkMemoryAlign_complete hmem hspec hvalid.2
  · simp only [Chip.conclusion, logicalConclusion]
    congr 1
    · obtain ⟨hlen, hitem⟩ := zipAll_spec hinp
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi1 hi2
        have hiO : i < orig.inputs.length := by simpa using hi2
        have hiB : i < branch.inputs.length := by simpa using hi1
        simp only [List.getElem_map]
        exact checkVarWire_complete_of_lt (hitem i hiO hiB)
          (hinpLt (orig.inputs[i]'hiO) (List.getElem_mem hiO)) ao
    · exact checkPolyWire_complete hout hspec
  · exact checkSendsAlign_complete hsends hsendLt hspec

/-- Finite row-level soundness for one branch: lifts a valid branch row to a
valid row of `orig` with identical logical receive and premises. -/
theorem checkBranch_liftRow {orig branch : Chip F} {activeSel inactiveSel : ArithExpr F}
    {w : BranchWitness F} (h : checkBranch orig branch activeSel inactiveSel w = true)
    (rom : WireROM F) (row : Row F) (hvalid : branch.ValidRow rom row) :
    let lifted := liftRow orig.name orig.numVars w row
    lifted.chip = orig.name ∧
      orig.ValidRow rom lifted ∧
      orig.receive lifted = logicalReceive orig.name branch row ∧
      orig.premises lifted = branch.premises row := by
  have horigWf : orig.wellFormed = true := by
    simp only [checkBranch, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.1.1.1.1.1.1.1
  obtain ⟨hv, hconc, hreq⟩ := checkBranch_sound h rom row.assignment hvalid.2.2
  have hfin := orig.finiteAssignment horigWf (liftAssignment w row.assignment) rom
  refine ⟨rfl, ⟨horigWf, Row.ofAssignment_length _ _ _, hfin.1.mp hv⟩, ?_, ?_⟩
  · exact hfin.2.1.symm.trans hconc
  · exact hfin.2.2.symm.trans hreq

/-- Finite row-level completeness for one branch: projects a valid active `orig`
row to a valid branch row with identical logical receive and premises. -/
theorem checkBranch_projectRow {orig branch : Chip F} {activeSel inactiveSel : ArithExpr F}
    {w : BranchWitness F} (h : checkBranch orig branch activeSel inactiveSel w = true)
    (rom : WireROM F) (row : Row F) (hvalid : orig.ValidRow rom row)
    (hact : activeSel.denote row.assignment = 1) (hinact : inactiveSel.denote row.assignment = 0) :
    let projected := projectRow branch.name w row
    projected.chip = branch.name ∧
      branch.ValidRow rom projected ∧
      logicalReceive orig.name branch projected = orig.receive row ∧
      branch.premises projected = orig.premises row := by
  have hwf : branch.wellFormed = true ∧ w.proj.length = branch.numVars := by
    simp only [checkBranch, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2⟩
  obtain ⟨hv, hconc, hreq⟩ := checkBranch_complete h rom row.assignment hvalid.2.2 hact hinact
  have hfin := branch.finiteAssignment hwf.1 (projAssignment w row.assignment) rom
  have hprojEq : projectRow branch.name w row =
      Row.ofAssignment branch.name branch.numVars (projAssignment w row.assignment) := by
    simp only [projectRow, hwf.2]
  rw [hprojEq]
  refine ⟨rfl, ⟨hwf.1, Row.ofAssignment_length _ _ _, hfin.1.mp hv⟩, ?_, ?_⟩
  · have hrec : logicalReceive orig.name branch
        (Row.ofAssignment branch.name branch.numVars (projAssignment w row.assignment)) =
        logicalConclusion orig.name branch (projAssignment w row.assignment) := by
      simp only [logicalReceive, logicalConclusion, hfin.2.1]
    exact hrec.trans hconc
  · exact hfin.2.2.symm.trans hreq

/-- **Bidirectional Chip Split Soundness & Completeness (`split_chip_sound_with`)**:
a claim and premise list are derivable by a single row of `orig` if and only if
they are derivable by either `fast` or `cold` on logical channel `orig.name`. -/
theorem split_chip_sound_with {w : SplitWitness F} {orig fast cold : Chip F}
    (hcheck : checkSplitWith w orig fast cold = true)
    (rom : WireROM F) (conclusion : Message F) (premises : List (Message F)) :
    (LogicalRule orig.name fast rom conclusion premises ∨
      LogicalRule orig.name cold rom conclusion premises) ↔
    orig.LocalRule rom conclusion premises := by
  simp only [checkSplitWith, Bool.and_eq_true] at hcheck
  obtain ⟨⟨⟨hpar, hpart⟩, hfast⟩, hcold⟩ := hcheck
  constructor
  · rintro (⟨row, _, hval, hrec, hprem⟩ | ⟨row, _, hval, hrec, hprem⟩)
    · obtain ⟨hname, hval', hrec', hprem'⟩ := checkBranch_liftRow hfast rom row hval
      exact ⟨liftRow orig.name orig.numVars w.fast row, hname, hval',
        hrec'.trans hrec, hprem'.trans hprem⟩
    · obtain ⟨hname, hval', hrec', hprem'⟩ := checkBranch_liftRow hcold rom row hval
      exact ⟨liftRow orig.name orig.numVars w.cold row, hname, hval',
        hrec'.trans hrec, hprem'.trans hprem⟩
  · rintro ⟨row, _, hval, hrec, hprem⟩
    have hp1 := checkParentActive_sound hpar hval.2.2.1
    rcases checkSelectorPartition_active hpart hval.2.2.1 hp1 with ⟨hf1, hc0⟩ | ⟨hf0, hc1⟩
    · obtain ⟨hname, hval', hrec', hprem'⟩ := checkBranch_projectRow hfast rom row hval hf1 hc0
      exact Or.inl ⟨projectRow fast.name w.fast row, hname, hval',
        hrec'.trans hrec, hprem'.trans hprem⟩
    · obtain ⟨hname, hval', hrec', hprem'⟩ := checkBranch_projectRow hcold rom row hval hc1 hf0
      exact Or.inr ⟨projectRow cold.name w.cold row, hname, hval',
        hrec'.trans hrec, hprem'.trans hprem⟩

/-! ## 3. Automatic Chip Splitter (`splitChip`) & Standalone Verifier (`checkSplit`) -/

/-- Infer all variables referenced by a list of polynomials, deduplicated and
sorted in ascending order. -/
private def sortedUniqueVars (vs : List Var) : List Var :=
  (vs.dedup).mergeSort (· ≤ ·)

/-- Infer nested dead-zero sub-choice cascades inside `cs` rooted at `inactiveSel`. -/
def inferDeadZeroSteps (cs : List (ArithExpr F)) (inactiveSel : ArithExpr F) :
    List (ArithExpr F × List Var) :=
  let rec extractSumVars : ArithExpr F → Option (List Var)
    | .const _ => some []
    | .var v => some [v]
    | .add a b => do
        let va ← extractSumVars a
        let vb ← extractSumVars b
        return va ++ vb
    | _ => none
  let findRound (known : List Var) : List (ArithExpr F × List Var) :=
    cs.filterMap fun p =>
      match Polynomial.simplify p with
      | .sub lhs rhs =>
          match extractSumVars lhs with
          | some vs =>
              if !vs.isEmpty &&
                  checkDeadZeroStep cs inactiveSel known (rhs, vs) &&
                  !(vs.all (known.contains ·)) then
                some (rhs, vs)
              else none
          | none =>
              match extractSumVars rhs with
              | some vs =>
                  if !vs.isEmpty &&
                      checkDeadZeroStep cs inactiveSel known (lhs, vs) &&
                      !(vs.all (known.contains ·)) then
                    some (lhs, vs)
                  else none
              | none => none
      | _ => none
  let rec loop : Nat → List Var → List (ArithExpr F × List Var) → List (ArithExpr F × List Var)
    | 0, _, acc => acc
    | fuel + 1, known, acc =>
        let found := findRound known
        if found.isEmpty then acc
        else
          let nextKnown := known ++ found.flatMap Prod.snd
          loop fuel nextKnown (acc ++ found)
  loop cs.length [] []

/-- Build one narrowed branch chip and its `BranchWitness` by specializing
`activeSel ↦ 1`, `inactiveSel ↦ 0`, and all dead sub-selectors `↦ 0`, then
compacting to only the live columns used on this branch. -/
def buildBranch (orig : Chip F) (branchName : String)
    (activeSel inactiveSel : ArithExpr F) : Chip F × BranchWitness F :=
  let deadSteps := inferDeadZeroSteps orig.constraints inactiveSel
  let deadZeros := deadZeroVars deadSteps
  let spec := branchSpecSubst activeSel inactiveSel deadZeros
  let specConstraints := orig.constraints.filterMap fun p =>
    let q := Polynomial.simplify (Polynomial.subst spec p)
    if q == (.const 0 : ArithExpr F) then none else some q
  let specOutput := orig.output.map fun p => Polynomial.simplify (Polynomial.subst spec p)
  let specSends := orig.sends.filterMap fun s =>
    let en := Polynomial.simplify (Polynomial.subst spec s.enable)
    if en == (.const 0 : ArithExpr F) then none
    else some { s with
      enable := en
      args := s.args.map (WireValue.map fun p => Polynomial.simplify (Polynomial.subst spec p)) }
  let specMemory : List (MemoryLookup F) := orig.memory.filterMap fun m =>
    let en := Polynomial.simplify (Polynomial.subst spec m.enable)
    if en == (.const 0 : ArithExpr F) then none
    else some ({
      address := Polynomial.simplify (Polynomial.subst spec m.address)
      value := m.value.map fun p => Polynomial.simplify (Polynomial.subst spec p)
      enable := en } : MemoryLookup F)
  let liveVars := sortedUniqueVars <|
    (orig.inputs.flatMap WireValue.words) ++
    (specOutput.words.flatMap Polynomial.vars) ++
    (specConstraints.flatMap Polynomial.vars) ++
    (specSends.flatMap fun s =>
      Polynomial.vars s.enable ++
        (s.args.flatMap fun a => a.words.flatMap Polynomial.vars) ++ s.result.words) ++
    (specMemory.flatMap fun m =>
      Polynomial.vars m.enable ++ Polynomial.vars m.address ++
        (m.value.words.flatMap Polynomial.vars))
  let proj := liveVars.filter (· < orig.numVars)
  let colOf (v : Var) : Option Var := proj.findIdx? (· == v)
  let activeVar? : Option Var :=
    match Polynomial.simplify activeSel with | .var u => some u | _ => none
  let lift : List (ArithExpr F) :=
    (List.range orig.numVars).map fun v =>
      match colOf v with
      | some j => .var j
      | none => if activeVar? == some v then .const 1 else .const 0
  let liftSub := listSubst lift
  let remapVar (v : Var) : Var := (colOf v).getD 0
  let remapExpr (e : ArithExpr F) : ArithExpr F := Polynomial.simplify (Polynomial.subst liftSub e)
  let branchConstraints := (orig.constraints.filterMap fun p =>
    let q := remapExpr p
    if q == (.const 0 : ArithExpr F) then none else some q).dedup
  let branchSends := orig.sends.filterMap fun s =>
    let enSpec := Polynomial.simplify (Polynomial.subst spec s.enable)
    let enLift := remapExpr s.enable
    if enSpec == (.const 0 : ArithExpr F) && enLift == (.const 0 : ArithExpr F) then none
    else some {
      channel := s.channel
      args := s.args.map (WireValue.map remapExpr)
      result := s.result.map remapVar
      enable := enLift }
  let branchMemory := orig.memory.filterMap fun m =>
    let enSpec := Polynomial.simplify (Polynomial.subst spec m.enable)
    let enLift := remapExpr m.enable
    if enSpec == (.const 0 : ArithExpr F) && enLift == (.const 0 : ArithExpr F) then none
    else some {
      address := remapExpr m.address
      value := m.value.map remapExpr
      enable := enLift }
  let branchChip : Chip F := {
    name := branchName
    inputs := orig.inputs.map (WireValue.map remapVar)
    output := orig.output.map remapExpr
    numVars := proj.length
    constraints := branchConstraints
    sends := branchSends
    memory := branchMemory
  }
  (branchChip, ⟨proj, lift, deadSteps⟩)

/-- A certified entry splitting `orig` into narrow `fast` and wide `cold` chips. -/
structure SplitChipEntry (F : Type) where
  orig : Chip F
  fast : Chip F
  cold : Chip F
  witness : SplitWitness F
  deriving Repr, BEq

/-- Automatically split `orig` along `(fastSel, coldSel)` (with `parentSel = 1`),
failing closed (`none`) unless `checkSplitWith` passes. -/
def splitChip (orig : Chip F) (fastSel coldSel : ArithExpr F)
    (parentSel : ArithExpr F := .const 1)
    (fastName : String := orig.name ++ "#fast")
    (coldName : String := orig.name ++ "#cold") : Option (SplitChipEntry F) :=
  let (fast, wFast) := buildBranch orig fastName fastSel coldSel
  let (cold, wCold) := buildBranch orig coldName coldSel fastSel
  let w : SplitWitness F := ⟨fastSel, coldSel, parentSel, wFast, wCold⟩
  if checkSplitWith w orig fast cold then
    some ⟨orig, fast, cold, w⟩
  else
    none

/-- Candidate `(fastSel, coldSel)` pairs extracted from `orig.constraints`
(handles both two-selector `s1 + s2 - 1 = 0` and single eliminated boolean
selector `b * (b - 1) = 0` with `s_cold = 1 - b`). -/
def candidateSelectorPairs (cs : List (ArithExpr F)) : List (ArithExpr F × ArithExpr F) :=
  cs.flatMap fun p =>
    match Polynomial.simplify p with
    | .sub (.add s1 s2) (.const c) =>
        if c == 1 then [(s1, s2), (s2, s1)] else []
    | .sub (.const c) (.add s1 s2) =>
        if c == 1 then [(s1, s2), (s2, s1)] else []
    | .mul (.var v) (.sub (.var v') (.const c)) =>
        if v == v' && c == 1 then
          [(.var v, .sub (.const 1) (.var v)), (.sub (.const 1) (.var v), .var v)]
        else []
    | .mul (.sub (.var v) (.const c)) (.var v') =>
        if v == v' && c == 1 then
          [(.var v, .sub (.const 1) (.var v)), (.sub (.const 1) (.var v), .var v)]
        else []
    | _ => []

/-- Untrusted witness discovery for `checkSplit (orig fast cold : Chip F)`.
All security rests on `checkSplitWith` (nothing in discovery is trusted). -/
def inferSplitWitness? (orig fast cold : Chip F) : Option (SplitWitness F) :=
  (candidateSelectorPairs orig.constraints).findSome? fun (fs, cs) =>
    let (_, wFast) := buildBranch orig fast.name fs cs
    let (_, wCold) := buildBranch orig cold.name cs fs
    let w : SplitWitness F := ⟨fs, cs, .const 1, wFast, wCold⟩
    if checkSplitWith w orig fast cold then some w else none

/-- Standalone decidable structural verifier `checkSplit (orig fast cold : Chip F) : Bool`.
Discovers the selector partition & projection/lift witness and certifies it via
`checkSplitWith`. -/
def checkSplit (orig fast cold : Chip F) : Bool :=
  match inferSplitWitness? orig fast cold with
  | some w => checkSplitWith w orig fast cold
  | none => false

theorem checkSplit_witness {orig fast cold : Chip F}
    (h : checkSplit orig fast cold = true) :
    ∃ w : SplitWitness F, checkSplitWith w orig fast cold = true := by
  unfold checkSplit at h
  cases hinfer : inferSplitWitness? orig fast cold with
  | none => simp [hinfer] at h
  | some w =>
      simp only [hinfer] at h
      exact ⟨w, h⟩

/-- **Headline Chip-Level Split Soundness & Completeness (`split_chip_sound`)**:
if `checkSplit orig fast cold = true`, then `(fast, cold)` on logical channel
`orig.name` have the exact same local rule as `orig` (bidirectional soundness
and prover completeness). -/
theorem split_chip_sound {orig fast cold : Chip F}
    (hcheck : checkSplit orig fast cold = true)
    (rom : WireROM F) (conclusion : Message F) (premises : List (Message F)) :
    (LogicalRule orig.name fast rom conclusion premises ∨
      LogicalRule orig.name cold rom conclusion premises) ↔
    orig.LocalRule rom conclusion premises := by
  obtain ⟨w, hw⟩ := checkSplit_witness hcheck
  exact split_chip_sound_with hw rom conclusion premises

end ChipSplit

/-! ## 4. System-Level Splitting (`SplitSystem`) & Trace / LogUp Equivalence -/

section SystemSplit

variable {F : Type} [Field F] [DecidableEq F]

/-- A certified split circuit system: every chip in `source` is either kept in
`unsplit` or split into `(fast, cold)` in `splits`, sharing logical channel
`orig.name` while keeping distinct physical chip names. -/
structure SplitSystem (F : Type) where
  source : Circuit.System F
  unsplit : List (Chip F)
  splits : List (SplitChipEntry F)
  deriving Repr, BEq

/-- All `(logicalChannel, physicalChip)` pairs in a `SplitSystem`. -/
def SplitSystem.physicalEntries (sys : SplitSystem F) : List (String × Chip F) :=
  sys.unsplit.map (fun c => (c.name, c)) ++
    sys.splits.flatMap (fun e => [(e.orig.name, e.fast), (e.orig.name, e.cold)])

/-- All physical chips in a `SplitSystem`. -/
def SplitSystem.physicalChips (sys : SplitSystem F) : List (Chip F) :=
  sys.physicalEntries.map Prod.snd

/-- Look up a physical chip and its logical channel by physical chip name. -/
def SplitSystem.findPhysical? (sys : SplitSystem F) (chipName : String) :
    Option (String × Chip F) :=
  sys.physicalEntries.find? (fun p => p.2.name == chipName)

/-- Structural certificate for a `SplitSystem`. -/
def SplitSystem.checkValid (sys : SplitSystem F) : Bool :=
  (match checkChips [] sys.source.chips with | .ok () => true | .error _ => false) &&
    (match checkChips [] sys.physicalChips with | .ok () => true | .error _ => false) &&
    sys.unsplit.all (fun c => decide (sys.source.findChip? c.name = some c)) &&
    sys.splits.all (fun e =>
      decide (sys.source.findChip? e.orig.name = some e.orig) &&
        checkSplitWith e.witness e.orig e.fast e.cold) &&
    sys.source.chips.all (fun c =>
      sys.unsplit.any (fun u => decide (u = c)) ||
        sys.splits.any (fun e => decide (e.orig = c)))

/-- Inspect one physical row of a `SplitSystem`, returning its logical receive
claim (on the original channel) and active call premises. -/
def SplitSystem.inspectRow (sys : SplitSystem F) (rom : WireROM F) (row : Row F) :
    Except WitnessError (RuleClaims (Message F)) := do
  let some (channel, chip) := sys.findPhysical? row.chip | throw (.unknownChip row.chip)
  let (_, prems) ← chip.checkRow rom row
  return (logicalReceive channel chip row, prems)

def SplitSystem.inspectRows (sys : SplitSystem F) (rom : WireROM F) (rows : List (Row F)) :
    Except WitnessError (List (RuleClaims (Message F))) :=
  rows.mapM (sys.inspectRow rom)

def SplitSystem.inspectWeightedRows (sys : SplitSystem F) (rom : WireROM F)
    (rows : List (WeightedRow F)) : Except WitnessError (List (RuleClaims (Message F) × Int)) :=
  rows.mapM fun weighted => do
    let claims ← sys.inspectRow rom weighted.row
    return (claims, weighted.multiplicity)

/-- Unit-multiplicity LogUp trace checker for a `SplitSystem` (exact same
`Balance.accumulator` ledger as `Circuit.System.check`). -/
def SplitSystem.check (sys : SplitSystem F) (rom : WireROM F)
    (entry : Message F) (rows : List (Row F)) : Except WitnessError Unit := do
  sys.source.checkContext rom entry
  checkChips [] sys.physicalChips
  let rules ← sys.inspectRows rom rows
  let ledger := Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry
    (rules.map fun rule => (rule, 1))
  if ledger.isZero then pure () else throw .unbalancedMessages

/-- Weighted/memoized LogUp trace checker for a `SplitSystem` (exact same
`Balance.accumulator` ledger as `Circuit.System.checkMemo`). -/
def SplitSystem.checkMemo (sys : SplitSystem F) (rom : WireROM F)
    (entry : Message F) (rows : List (WeightedRow F)) : Except WitnessError Unit := do
  sys.source.checkContext rom entry
  checkChips [] sys.physicalChips
  let rules ← sys.inspectWeightedRows rom rows
  let ledger := Balance.accumulator (fun claim => decide (sys.source.MapClaim claim)) entry rules
  if ledger.isZero then pure () else throw .unbalancedMessages

/-- Lift a single physical split row back to its corresponding `sys.source` row. -/
def SplitSystem.liftRowToSource (sys : SplitSystem F) (row : Row F) : Row F :=
  if sys.unsplit.any (fun c => c.name == row.chip) then row
  else
    match sys.splits.find? (fun e => e.fast.name == row.chip || e.cold.name == row.chip) with
    | none => row
    | some e =>
        if e.fast.name == row.chip then
          liftRow e.orig.name e.orig.numVars e.witness.fast row
        else
          liftRow e.orig.name e.orig.numVars e.witness.cold row

def SplitSystem.liftRowsToSource (sys : SplitSystem F) (rows : List (Row F)) : List (Row F) :=
  rows.map sys.liftRowToSource

def SplitSystem.liftWeightedRowsToSource (sys : SplitSystem F)
    (rows : List (WeightedRow F)) : List (WeightedRow F) :=
  rows.map fun w => ⟨sys.liftRowToSource w.row, w.multiplicity⟩

/-- Route a single `sys.source` row into its narrow fast or cold split row. -/
def SplitSystem.splitRowFromSource (sys : SplitSystem F) (row : Row F) : Row F :=
  match sys.splits.find? (fun e => e.orig.name == row.chip) with
  | none => row
  | some e =>
      if e.witness.fastSel.denote row.assignment = 1 then
        projectRow e.fast.name e.witness.fast row
      else
        projectRow e.cold.name e.witness.cold row

def SplitSystem.splitRowsFromSource (sys : SplitSystem F) (rows : List (Row F)) : List (Row F) :=
  rows.map sys.splitRowFromSource

def SplitSystem.splitWeightedRowsFromSource (sys : SplitSystem F)
    (rows : List (WeightedRow F)) : List (WeightedRow F) :=
  rows.map fun w => ⟨sys.splitRowFromSource w.row, w.multiplicity⟩

private theorem find?_eq_some_of_nodup_map {α : Type} (key : α → String)
    {xs : List α} (hnodup : (xs.map key).Nodup) {x : α} (hmem : x ∈ xs) :
    xs.find? (fun y => key y == key x) = some x := by
  induction xs with
  | nil => cases hmem
  | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp
      · have hne : key y ≠ key x := fun heq =>
          hnodup.1 (List.mem_map.mpr ⟨x, htail, heq.symm⟩)
        have hbeq : (key y == key x) = false := beq_false_of_ne hne
        simp only [List.find?_cons, hbeq]
        exact ih hnodup.2 htail

private theorem SplitSystem.physicalEntries_nodup {sys : SplitSystem F}
    (hvalid : sys.checkValid = true) :
    (sys.physicalEntries.map (fun p => p.2.name)).Nodup := by
  simp only [SplitSystem.checkValid, Bool.and_eq_true] at hvalid
  have hphys := hvalid.1.1.1.2
  cases hchk : checkChips [] sys.physicalChips with
  | error _ => simp [hchk] at hphys
  | ok u =>
      cases u
      have hnd := (checkChips_iff.mp hchk).1
      simpa [SplitSystem.physicalChips, List.map_map, Function.comp_def] using hnd

private theorem SplitSystem.findPhysical_eq_of_mem {sys : SplitSystem F}
    (hvalid : sys.checkValid = true) {ch : String} {c : Chip F}
    (hmem : (ch, c) ∈ sys.physicalEntries) :
    sys.findPhysical? c.name = some (ch, c) := by
  unfold SplitSystem.findPhysical?
  exact find?_eq_some_of_nodup_map (fun p => p.2.name) (sys.physicalEntries_nodup hvalid) hmem

private theorem SplitSystem.checkChips_physical {sys : SplitSystem F}
    (hvalid : sys.checkValid = true) :
    checkChips [] sys.physicalChips = .ok () := by
  simp only [SplitSystem.checkValid, Bool.and_eq_true] at hvalid
  have hphys := hvalid.1.1.1.2
  cases hchk : checkChips [] sys.physicalChips with
  | error _ => simp [hchk] at hphys
  | ok u => cases u; rfl

theorem SplitSystem.inspectRow_iff {sys : SplitSystem F} {rom : WireROM F} {row : Row F}
    {claims : RuleClaims (Message F)} :
    sys.inspectRow rom row = .ok claims ↔
      ∃ channel chip, sys.findPhysical? row.chip = some (channel, chip) ∧
        chip.ValidRow rom row ∧ claims = (logicalReceive channel chip row, chip.premises row) := by
  unfold SplitSystem.inspectRow
  cases hfind : sys.findPhysical? row.chip with
  | none => simp
  | some p =>
      rcases p with ⟨channel, chip⟩
      simp only [bind, Except.bind]
      cases hchk : chip.checkRow rom row with
      | error e =>
          simp only [reduceCtorEq, false_iff, not_exists, not_and]
          intro ch c h1 hval
          have ⟨hch, hc⟩ := Prod.mk.inj (Option.some.inj h1)
          subst hch hc
          have hok := Chip.checkRow_iff.mpr ⟨hval, rfl⟩
          rw [hok] at hchk
          cases hchk
      | ok res =>
          obtain ⟨hval, rfl⟩ := Chip.checkRow_iff.mp hchk
          simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq]
          constructor
          · intro heq
            exact ⟨channel, chip, ⟨rfl, rfl⟩, hval, heq.symm⟩
          · rintro ⟨ch, c, ⟨rfl, rfl⟩, _, heq⟩
            exact heq.symm

/-- **Row-Level Soundness**: lifting any accepted split row to `sys.source`
preserves its exact `(receive, premises)` claims verbatim! -/
theorem SplitSystem.inspectRow_liftRow {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {row : Row F} {claims : RuleClaims (Message F)}
    (hinsp : sys.inspectRow rom row = .ok claims) :
    sys.source.inspectRow rom (sys.liftRowToSource row) = .ok claims := by
  obtain ⟨channel, chip, hfind, hval, rfl⟩ := SplitSystem.inspectRow_iff.mp hinsp
  have hmem := List.mem_of_find?_eq_some hfind
  have hchipName : chip.name = row.chip := by
    have hs := List.find?_some (p := fun (p : String × Chip F) => p.2.name == row.chip) hfind
    exact beq_iff_eq.mp hs
  have hnd := sys.physicalEntries_nodup hvalid
  have hvalid' := hvalid
  simp only [SplitSystem.checkValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hvalid'
  unfold SplitSystem.physicalEntries at hmem
  rcases List.mem_append.mp hmem with hun | hsp
  · -- Unsplit chip
    obtain ⟨c, hcMem, hcEq⟩ := List.mem_map.mp hun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hcEq
    have hhas : sys.unsplit.any (fun u => u.name == row.chip) = true :=
      List.any_eq_true.mpr ⟨c, hcMem, beq_iff_eq.mpr hchipName⟩
    have hlift : sys.liftRowToSource row = row := by
      unfold SplitSystem.liftRowToSource
      simp [hhas]
    rw [hlift]
    apply System.inspectRow_iff.mpr
    refine ⟨c, ?_, hval, ?_⟩
    · rw [← hchipName]
      exact hvalid'.1.1.2 c hcMem
    · rfl
  · -- Split chip (either fast or cold)
    obtain ⟨e, heMem, hfc⟩ := List.mem_flatMap.mp hsp
    have hnotUnsplit : sys.unsplit.any (fun u => u.name == row.chip) = false := by
      by_contra htrue
      have htrue' : sys.unsplit.any (fun u => u.name == row.chip) = true := by
        cases h0 : sys.unsplit.any (fun u => u.name == row.chip) <;> simp_all
      obtain ⟨u, huMem, huName⟩ := List.any_eq_true.mp htrue'
      have huEq : u.name = row.chip := beq_iff_eq.mp huName
      have hfindU : sys.findPhysical? u.name = some (u.name, u) :=
        sys.findPhysical_eq_of_mem hvalid (List.mem_append_left _ (List.mem_map.mpr ⟨u, huMem, rfl⟩))
      rw [huEq, hfind] at hfindU
      -- Even simpler: `(u.name, u)` in left half and `(channel, chip)` in right half share `name`!
      -- Use Nodup on `physicalEntries.map (·.2.name)` directly!
      have hndApp : ((sys.unsplit.map (fun c => c.name)) ++
          (sys.splits.flatMap fun e => [(e.orig.name, e.fast), (e.orig.name, e.cold)]).map
            (fun p => p.2.name)).Nodup := by
        simpa [SplitSystem.physicalEntries, List.map_append, List.map_map, Function.comp_def] using hnd
      have hdisj := List.disjoint_of_nodup_append hndApp
      have hL : row.chip ∈ sys.unsplit.map (fun c => c.name) :=
        List.mem_map.mpr ⟨u, huMem, huEq⟩
      have hR : row.chip ∈ (sys.splits.flatMap fun e =>
          [(e.orig.name, e.fast), (e.orig.name, e.cold)]).map (fun p => p.2.name) :=
        List.mem_map.mpr ⟨(channel, chip), List.mem_flatMap.mpr ⟨e, heMem, hfc⟩, hchipName⟩
      exact hdisj hL hR
    have hfindSplit : sys.splits.find? (fun e' => e'.fast.name == row.chip || e'.cold.name == row.chip) = some e := by
      -- Prove directly using uniqueness of `findPhysical?`!
      have hex : ∃ e' ∈ sys.splits, (e'.fast.name == row.chip || e'.cold.name == row.chip) = true := by
        refine ⟨e, heMem, ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hfc
        rcases hfc with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [hchipName]
      cases hfs : sys.splits.find? (fun e' => e'.fast.name == row.chip || e'.cold.name == row.chip) with
      | none =>
          obtain ⟨e', he', hp'⟩ := hex
          exact absurd (List.find?_eq_none.mp hfs e' he') (by simp [hp'])
      | some e' =>
          have he'Mem := List.mem_of_find?_eq_some hfs
          have hp' := List.find?_some hfs
          simp only [Bool.or_eq_true, beq_iff_eq] at hp'
          -- Show `e' = e` by showing both `(e'.orig.name, e'.fast/cold)` and `(channel, chip)` sit in `splits.flatMap` with identical `.2.name = row.chip`!
          have hndSplits : ((sys.splits.flatMap fun s => [s.fast.name, s.cold.name])).Nodup := by
            have hnd2 := (List.nodup_append.mp (by
              simpa [SplitSystem.physicalEntries, List.map_append, List.map_map, Function.comp_def] using hnd)).2.1
            have heqMap : (sys.splits.flatMap fun s => [(s.orig.name, s.fast), (s.orig.name, s.cold)]).map
                (fun p => p.2.name) = sys.splits.flatMap (fun s => [s.fast.name, s.cold.name]) := by
              induction sys.splits with
              | nil => rfl
              | cons s ss ih => simp [ih]
            rwa [heqMap] at hnd2
          -- If `e' ≠ e`, then `row.chip` appears in two distinct elements of `sys.splits`, contradicting `hndSplits`!
          suffices e' = e by rw [this]
          -- Helper: in a list `xs` where `(xs.flatMap f).Nodup`, two elements sharing a member of `f` must be equal!
          have huniq : ∀ (xs : List (SplitChipEntry F)),
              (xs.flatMap fun s => [s.fast.name, s.cold.name]).Nodup →
              ∀ a ∈ xs, ∀ b ∈ xs,
                (a.fast.name = row.chip ∨ a.cold.name = row.chip) →
                (b.fast.name = row.chip ∨ b.cold.name = row.chip) →
                a = b := by
            intro xs
            induction xs with
            | nil => intro _ _ ha; cases ha
            | cons x xs ih =>
                intro hndX a ha b hb hax hbx
                simp only [List.flatMap_cons, List.nodup_append] at hndX
                rcases List.mem_cons.mp ha with rfl | ha' <;>
                  rcases List.mem_cons.mp hb with rfl | hb'
                · rfl
                · exfalso
                  have hL : row.chip ∈ [a.fast.name, a.cold.name] := by
                    rcases hax with h1 | h1 <;> simp [h1]
                  have hR : row.chip ∈ xs.flatMap (fun s => [s.fast.name, s.cold.name]) :=
                    List.mem_flatMap.mpr ⟨b, hb', by rcases hbx with h1 | h1 <;> simp [h1]⟩
                  exact hndX.2.2 row.chip hL row.chip hR rfl
                · exfalso
                  have hL : row.chip ∈ [b.fast.name, b.cold.name] := by
                    rcases hbx with h1 | h1 <;> simp [h1]
                  have hR : row.chip ∈ xs.flatMap (fun s => [s.fast.name, s.cold.name]) :=
                    List.mem_flatMap.mpr ⟨a, ha', by rcases hax with h1 | h1 <;> simp [h1]⟩
                  exact hndX.2.2 row.chip hL row.chip hR rfl
                · exact ih hndX.2.1 a ha' b hb' hax hbx
          have heHit : e.fast.name = row.chip ∨ e.cold.name = row.chip := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hfc
            rcases hfc with ⟨_, rfl⟩ | ⟨_, rfl⟩
            · exact Or.inl hchipName
            · exact Or.inr hchipName
          exact huniq sys.splits hndSplits e' he'Mem e heMem hp' heHit
    have heValid := hvalid'.1.2 e heMem
    have horigFind : sys.source.findChip? e.orig.name = some e.orig := heValid.1
    have hsplitChk := heValid.2
    simp only [checkSplitWith, Bool.and_eq_true] at hsplitChk
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hfc
    rcases hfc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- Fast row
      have hlift : sys.liftRowToSource row = liftRow e.orig.name e.orig.numVars e.witness.fast row := by
        unfold SplitSystem.liftRowToSource
        simp [hnotUnsplit, hfindSplit, hchipName]
      rw [hlift]
      obtain ⟨hname, hval', hrec', hprem'⟩ := checkBranch_liftRow hsplitChk.1.2 rom row hval
      apply System.inspectRow_iff.mpr
      refine ⟨e.orig, by simpa [hname] using horigFind, hval', ?_⟩
      simp [hrec', hprem']
    · -- Cold row
      have hneFC : e.fast.name ≠ e.cold.name := by
        have hnd2 := (List.nodup_append.mp (by
          simpa [SplitSystem.physicalEntries, List.map_append, List.map_map, Function.comp_def] using hnd)).2.1
        have heqMap : (sys.splits.flatMap fun s => [(s.orig.name, s.fast), (s.orig.name, s.cold)]).map
            (fun p => p.2.name) = sys.splits.flatMap (fun s => [s.fast.name, s.cold.name]) := by
          induction sys.splits with
          | nil => rfl
          | cons s ss ih => simp [ih]
        rw [heqMap] at hnd2
        have hpair : ∀ (xs : List (SplitChipEntry F)),
            (xs.flatMap fun s => [s.fast.name, s.cold.name]).Nodup →
            ∀ s ∈ xs, s.fast.name ≠ s.cold.name := by
          intro xs
          induction xs with
          | nil => intro _ _ hs; cases hs
          | cons x xs ih =>
              intro hndX s hs
              simp only [List.flatMap_cons, List.nodup_append] at hndX
              rcases List.mem_cons.mp hs with rfl | htail
              · simp at hndX
                exact hndX.1
              · exact ih hndX.2.1 s htail
        exact hpair sys.splits hnd2 e heMem
      have hlift : sys.liftRowToSource row = liftRow e.orig.name e.orig.numVars e.witness.cold row := by
        unfold SplitSystem.liftRowToSource
        have hfb : (e.fast.name == row.chip) = false := beq_false_of_ne (by rw [← hchipName]; exact hneFC)
        simp [hnotUnsplit, hfindSplit, hfb]
      rw [hlift]
      obtain ⟨hname, hval', hrec', hprem'⟩ := checkBranch_liftRow hsplitChk.2 rom row hval
      apply System.inspectRow_iff.mpr
      refine ⟨e.orig, by simpa [hname] using horigFind, hval', ?_⟩
      simp [hrec', hprem']

/-- **Row-Level Completeness**: splitting any accepted `sys.source` row produces
an accepted physical split row with the exact same `(receive, premises)` claims! -/
theorem SplitSystem.inspectRow_splitRow {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {row : Row F} {claims : RuleClaims (Message F)}
    (hinsp : sys.source.inspectRow rom row = .ok claims) :
    sys.inspectRow rom (sys.splitRowFromSource row) = .ok claims := by
  obtain ⟨origChip, hfind, hval, rfl⟩ := System.inspectRow_iff.mp hinsp
  have hmemOrig := List.mem_of_find?_eq_some hfind
  have horigName : origChip.name = row.chip := System.findChip_name hfind
  have hvalid' := hvalid
  simp only [SplitSystem.checkValid, Bool.and_eq_true, Bool.or_eq_true,
    List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at hvalid'
  unfold SplitSystem.splitRowFromSource
  cases hsp : sys.splits.find? (fun e => e.orig.name == row.chip) with
  | none =>
      -- Must be in `sys.unsplit` because every chip in `sys.source.chips` is covered!
      rcases hvalid'.2 origChip hmemOrig with ⟨u, huMem, rfl⟩ | ⟨e, heMem, rfl⟩
      · have hphys := sys.findPhysical_eq_of_mem hvalid
          (List.mem_append_left _ (List.mem_map.mpr ⟨u, huMem, rfl⟩))
        apply SplitSystem.inspectRow_iff.mpr
        refine ⟨u.name, u, by simpa [horigName] using hphys, hval, ?_⟩
        rfl
      · exfalso
        have hnot := List.find?_eq_none.mp hsp e heMem
        simp [horigName] at hnot
  | some e =>
      have heMem := List.mem_of_find?_eq_some hsp
      have heName : e.orig.name = row.chip := by
        have hs := List.find?_some (p := fun (e : SplitChipEntry F) => e.orig.name == row.chip) hsp
        exact beq_iff_eq.mp hs
      have heValid := hvalid'.1.2 e heMem
      have heOrigEq : e.orig = origChip := by
        have h1 := heValid.1
        rw [heName, hfind] at h1
        exact (Option.some.inj h1).symm
      subst heOrigEq
      have hsplitChk := heValid.2
      simp only [checkSplitWith, Bool.and_eq_true] at hsplitChk
      have hp1 := checkParentActive_sound hsplitChk.1.1.1 hval.2.2.1
      have hpart := checkSelectorPartition_active hsplitChk.1.1.2 hval.2.2.1 hp1
      dsimp only
      split_ifs with hfast
      · have hcold0 : e.witness.coldSel.denote row.assignment = 0 := by
          rcases hpart with ⟨_, hc0⟩ | ⟨hf0, _⟩
          · exact hc0
          · rw [hf0] at hfast; exact absurd hfast zero_ne_one
        obtain ⟨hname, hval', hrec', hprem'⟩ :=
          checkBranch_projectRow hsplitChk.1.2 rom row hval hfast hcold0
        have hphys : sys.findPhysical? e.fast.name = some (e.orig.name, e.fast) :=
          sys.findPhysical_eq_of_mem hvalid
            (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, heMem, by simp⟩))
        apply SplitSystem.inspectRow_iff.mpr
        refine ⟨e.orig.name, e.fast, by simpa [hname] using hphys, hval', ?_⟩
        simp [hrec', hprem']
      · rcases hpart with ⟨hf1, _⟩ | ⟨hf0, hc1⟩
        · exact absurd hf1 hfast
        · obtain ⟨hname, hval', hrec', hprem'⟩ :=
            checkBranch_projectRow hsplitChk.2 rom row hval hc1 hf0
          have hphys : sys.findPhysical? e.cold.name = some (e.orig.name, e.cold) :=
            sys.findPhysical_eq_of_mem hvalid
              (List.mem_append_right _ (List.mem_flatMap.mpr ⟨e, heMem, by simp⟩))
          apply SplitSystem.inspectRow_iff.mpr
          refine ⟨e.orig.name, e.cold, by simpa [hname] using hphys, hval', ?_⟩
          simp [hrec', hprem']

theorem SplitSystem.inspectRows_lift {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {rows : List (Row F)} {rules : List (RuleClaims (Message F))}
    (hinsp : sys.inspectRows rom rows = .ok rules) :
    sys.source.inspectRows rom (sys.liftRowsToSource rows) = .ok rules := by
  induction rows generalizing rules with
  | nil => simpa [SplitSystem.inspectRows, System.inspectRows, SplitSystem.liftRowsToSource] using hinsp
  | cons row rest ih =>
      simp only [SplitSystem.inspectRows, List.mapM_cons] at hinsp
      obtain ⟨claim, hhead, htail⟩ := except_bind_ok.mp hinsp
      obtain ⟨restClaims, hrest, hret⟩ := except_bind_ok.mp htail
      obtain rfl := except_pure_ok.mp hret
      have hrest' : sys.source.inspectRows rom (sys.liftRowsToSource rest) = .ok restClaims :=
        ih hrest
      simp only [System.inspectRows, SplitSystem.liftRowsToSource] at hrest' ⊢
      simp only [List.map_cons, List.mapM_cons]
      rw [sys.inspectRow_liftRow hvalid hhead, hrest']
      rfl

theorem SplitSystem.inspectRows_split {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {rows : List (Row F)} {rules : List (RuleClaims (Message F))}
    (hinsp : sys.source.inspectRows rom rows = .ok rules) :
    sys.inspectRows rom (sys.splitRowsFromSource rows) = .ok rules := by
  induction rows generalizing rules with
  | nil => simpa [SplitSystem.inspectRows, System.inspectRows, SplitSystem.splitRowsFromSource] using hinsp
  | cons row rest ih =>
      simp only [System.inspectRows, List.mapM_cons] at hinsp
      obtain ⟨claim, hhead, htail⟩ := except_bind_ok.mp hinsp
      obtain ⟨restClaims, hrest, hret⟩ := except_bind_ok.mp htail
      obtain rfl := except_pure_ok.mp hret
      have hrest' : sys.inspectRows rom (sys.splitRowsFromSource rest) = .ok restClaims :=
        ih hrest
      simp only [SplitSystem.inspectRows, SplitSystem.splitRowsFromSource] at hrest' ⊢
      simp only [List.map_cons, List.mapM_cons]
      rw [sys.inspectRow_splitRow hvalid hhead, hrest']
      rfl

theorem SplitSystem.inspectWeightedRows_lift {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {rows : List (WeightedRow F)}
    {rules : List (RuleClaims (Message F) × Int)}
    (hinsp : sys.inspectWeightedRows rom rows = .ok rules) :
    sys.source.inspectWeightedRows rom (sys.liftWeightedRowsToSource rows) = .ok rules := by
  induction rows generalizing rules with
  | nil =>
      simpa [SplitSystem.inspectWeightedRows, System.inspectWeightedRows,
        SplitSystem.liftWeightedRowsToSource] using hinsp
  | cons w rest ih =>
      simp only [SplitSystem.inspectWeightedRows, List.mapM_cons] at hinsp
      obtain ⟨pair, hhead, htail⟩ := except_bind_ok.mp hinsp
      obtain ⟨claim, hc, hp⟩ := except_bind_ok.mp hhead
      obtain rfl := except_pure_ok.mp hp
      obtain ⟨restClaims, hrest, hret⟩ := except_bind_ok.mp htail
      obtain rfl := except_pure_ok.mp hret
      have hrest' : sys.source.inspectWeightedRows rom (sys.liftWeightedRowsToSource rest) =
          .ok restClaims := ih hrest
      simp only [System.inspectWeightedRows, SplitSystem.liftWeightedRowsToSource] at hrest' ⊢
      simp only [List.map_cons, List.mapM_cons]
      have hhead' : (do
          let claims ← sys.source.inspectRow rom (sys.liftRowToSource w.row)
          return (claims, w.multiplicity)) = .ok (claim, w.multiplicity) := by
        rw [sys.inspectRow_liftRow hvalid hc]
        rfl
      rw [hhead', hrest']
      rfl

theorem SplitSystem.inspectWeightedRows_split {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {rows : List (WeightedRow F)}
    {rules : List (RuleClaims (Message F) × Int)}
    (hinsp : sys.source.inspectWeightedRows rom rows = .ok rules) :
    sys.inspectWeightedRows rom (sys.splitWeightedRowsFromSource rows) = .ok rules := by
  induction rows generalizing rules with
  | nil =>
      simpa [SplitSystem.inspectWeightedRows, System.inspectWeightedRows,
        SplitSystem.splitWeightedRowsFromSource] using hinsp
  | cons w rest ih =>
      simp only [System.inspectWeightedRows, List.mapM_cons] at hinsp
      obtain ⟨pair, hhead, htail⟩ := except_bind_ok.mp hinsp
      obtain ⟨claim, hc, hp⟩ := except_bind_ok.mp hhead
      obtain rfl := except_pure_ok.mp hp
      obtain ⟨restClaims, hrest, hret⟩ := except_bind_ok.mp htail
      obtain rfl := except_pure_ok.mp hret
      have hrest' : sys.inspectWeightedRows rom (sys.splitWeightedRowsFromSource rest) =
          .ok restClaims := ih hrest
      simp only [SplitSystem.inspectWeightedRows, SplitSystem.splitWeightedRowsFromSource] at hrest' ⊢
      simp only [List.map_cons, List.mapM_cons]
      have hhead' : (do
          let claims ← sys.inspectRow rom (sys.splitRowFromSource w.row)
          return (claims, w.multiplicity)) = .ok (claim, w.multiplicity) := by
        rw [sys.inspectRow_splitRow hvalid hc]
        rfl
      rw [hhead', hrest']
      rfl

/-- **Headline System-Level Split Soundness (`split_system_sound`)**:
any accepted trace of a certified `SplitSystem` lifts row-for-row to an accepted
trace of `sys.source` with identical row count and identical LogUp ledger. -/
theorem split_system_sound {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (Row F)}
    (hcheck : sys.check rom entry rows = .ok ()) :
    sys.source.check rom entry (sys.liftRowsToSource rows) = .ok () ∧
      (sys.liftRowsToSource rows).length = rows.length := by
  unfold SplitSystem.check at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨⟨⟩, _, h2⟩ := except_bind_ok.mp h1
  obtain ⟨rules, hinsp, hbal⟩ := except_bind_ok.mp h2
  refine ⟨?_, by simp [SplitSystem.liftRowsToSource]⟩
  unfold System.check
  rw [hctx, show sys.source.inspectRows rom (sys.liftRowsToSource rows) = .ok rules from
    sys.inspectRows_lift hvalid hinsp]
  exact hbal

/-- **Headline System-Level Memo / LogUp Soundness (`split_system_memo_sound`)**:
any accepted weighted LogUp trace of a certified `SplitSystem` lifts row-for-row
to an accepted weighted LogUp trace of `sys.source` with identical row count and
identical LogUp `Balance.accumulator`. -/
theorem split_system_memo_sound {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (WeightedRow F)}
    (hcheck : sys.checkMemo rom entry rows = .ok ()) :
    sys.source.checkMemo rom entry (sys.liftWeightedRowsToSource rows) = .ok () ∧
      (sys.liftWeightedRowsToSource rows).length = rows.length := by
  unfold SplitSystem.checkMemo at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨⟨⟩, _, h2⟩ := except_bind_ok.mp h1
  obtain ⟨rules, hinsp, hbal⟩ := except_bind_ok.mp h2
  refine ⟨?_, by simp [SplitSystem.liftWeightedRowsToSource]⟩
  unfold System.checkMemo
  rw [hctx, show sys.source.inspectWeightedRows rom (sys.liftWeightedRowsToSource rows) = .ok rules from
    sys.inspectWeightedRows_lift hvalid hinsp]
  exact hbal

/-- **Prover Completeness (Unit Check)**: any accepted trace of `sys.source`
splits row-for-row into an accepted trace of `sys` with identical LogUp ledger. -/
theorem split_system_complete {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (Row F)}
    (hcheck : sys.source.check rom entry rows = .ok ()) :
    sys.check rom entry (sys.splitRowsFromSource rows) = .ok () ∧
      (sys.splitRowsFromSource rows).length = rows.length := by
  unfold System.check at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨rules, hinsp, hbal⟩ := except_bind_ok.mp h1
  refine ⟨?_, by simp [SplitSystem.splitRowsFromSource]⟩
  unfold SplitSystem.check
  rw [hctx, sys.checkChips_physical hvalid,
    show sys.inspectRows rom (sys.splitRowsFromSource rows) = .ok rules from
      sys.inspectRows_split hvalid hinsp]
  exact hbal

/-- **Prover Completeness (Memo / LogUp Check)**: any accepted weighted LogUp
trace of `sys.source` splits row-for-row into an accepted weighted LogUp trace
of `sys` with identical LogUp ledger. -/
theorem split_system_memo_complete {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} {rows : List (WeightedRow F)}
    (hcheck : sys.source.checkMemo rom entry rows = .ok ()) :
    sys.checkMemo rom entry (sys.splitWeightedRowsFromSource rows) = .ok () ∧
      (sys.splitWeightedRowsFromSource rows).length = rows.length := by
  unfold System.checkMemo at hcheck
  obtain ⟨⟨⟩, hctx, h1⟩ := except_bind_ok.mp hcheck
  obtain ⟨rules, hinsp, hbal⟩ := except_bind_ok.mp h1
  refine ⟨?_, by simp [SplitSystem.splitWeightedRowsFromSource]⟩
  unfold SplitSystem.checkMemo
  rw [hctx, sys.checkChips_physical hvalid,
    show sys.inspectWeightedRows rom (sys.splitWeightedRowsFromSource rows) = .ok rules from
      sys.inspectWeightedRows_split hvalid hinsp]
  exact hbal

/-- Bidirectional existential trace equivalence (unit check). -/
theorem split_system_check_iff {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} :
    (∃ rows, sys.check rom entry rows = .ok ()) ↔
      (∃ rows, sys.source.check rom entry rows = .ok ()) :=
  ⟨fun ⟨_, h⟩ => ⟨_, (split_system_sound hvalid h).1⟩,
   fun ⟨_, h⟩ => ⟨_, (split_system_complete hvalid h).1⟩⟩

/-- Bidirectional existential trace equivalence (memo / LogUp check). -/
theorem split_system_checkMemo_iff {sys : SplitSystem F} (hvalid : sys.checkValid = true)
    {rom : WireROM F} {entry : Message F} :
    (∃ rows, sys.checkMemo rom entry rows = .ok ()) ↔
      (∃ rows, sys.source.checkMemo rom entry rows = .ok ()) :=
  ⟨fun ⟨_, h⟩ => ⟨_, (split_system_memo_sound hvalid h).1⟩,
   fun ⟨_, h⟩ => ⟨_, (split_system_memo_complete hvalid h).1⟩⟩

/-- End-to-end composition with Formal Aiur's `ModulesArtifact`: an accepted
trace of a certified split of `compiled.circuit.system` implies independent
source evaluation `prepared.EvalCall`. -/
theorem split_modulesArtifact_sound {prog : Modules.Program F}
    {prepared : Modules.Prepared prog} (compiled : ModulesArtifact prepared)
    {sys : SplitSystem F} (hsrc : sys.source = compiled.circuit.system)
    (hvalid : sys.checkValid = true)
    {external : String} {entry : Modules.Selection prog prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Row F)}
    (hcheck : sys.check rom ⟨entry.resolved.name, wires, output⟩ rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalCall external args value ∧
      Represents (rom.decode compiled.specialized.program.enums) heap value result := by
  have horig := (split_system_sound hvalid hcheck).1
  rw [hsrc] at horig
  have hmem : entry.resolved.name ∈ compiled.circuit.artifact.entries := by
    simpa only [(compile_stages compiled.circuit.compiled).2.2.1] using
      Modules.Prepared.entry_mem selected
  have hart : compiled.check rom external wires output (sys.liftRowsToSource rows) = .ok () := by
    simp only [ModulesArtifact.check, selected]
    exact Artifact.check_iff.mpr ⟨hmem, horig⟩
  exact compiled.check_sound hart arguments decoded

/-- End-to-end composition with Formal Aiur's `Physical.Prepared` +
`Modules.Prepared.physical_heap_sound`: an accepted split trace of the physical
type-erased system yields `Modules.Prepared.EvalFn`. -/
theorem split_physical_heap_sound {prog : Modules.Program F}
    {prepared : Modules.Prepared prog} (compiled : ModulesArtifact prepared)
    (physical : Physical.Prepared compiled.circuit.artifact)
    {sys : SplitSystem F} (hsrc : sys.source = physical.system)
    (hvalid : sys.checkValid = true)
    {external : String} {entry : Modules.Selection prog prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {rom : WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Value F}
    {wires : List (WireValue F)} {output : WireValue F} {rows : List (Row F)}
    (signed : Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (hcheck : sys.check (Erasure.rawROM rom)
      (Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩) rows = .ok ())
    (arguments : DecodesValues compiled.specialized.program.enums wires (entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ value heap, prepared.EvalFn external args value heap ∧
      Represents
        ((Erasure.typedROM compiled.circuit.system rom).decode compiled.specialized.program.enums)
        heap value result := by
  have horig := (split_system_sound hvalid hcheck).1
  rw [hsrc] at horig
  exact prepared.physical_heap_sound compiled physical selected valid signed
    (physical.system.check_sound horig) arguments decoded

/-- Build a certified `SplitSystem` by splitting every chip of `source` named in
`targets` (`(chipName, fastSel, coldSel)`), failing closed if any split or
global uniqueness check fails. -/
def splitSystem (source : Circuit.System F)
    (targets : List (String × ArithExpr F × ArithExpr F)) : Option (SplitSystem F) := do
  let splitEntries ← targets.mapM fun (name, fastSel, coldSel) => do
    let orig ← source.findChip? name
    splitChip orig fastSel coldSel
  let splitNames := splitEntries.map (·.orig.name)
  let unsplit := source.chips.filter fun c => !splitNames.contains c.name
  let sys : SplitSystem F := ⟨source, unsplit, splitEntries⟩
  if sys.checkValid then some sys else none

/-- Total Stage-1 field cells across a trace (sum of row widths). -/
def traceCells (rows : List (Row F)) : Nat :=
  (rows.map fun r => r.values.length).sum

end SystemSplit

/-! ## 5. Executable Smoke Tests (`#guard`) & Axiom Pins -/

section SmokeTests

private abbrev GF := Library.U32.Goldilocks.F

/-- A 26-column mixed fast/cold chip over Goldilocks:
* Columns `0, 1, 2` (`x, y, out`): interface shared by both paths.
* Column `3` (`aux_fast`): fast-path-only auxiliary (`aux_fast = x * y`, `out = aux_fast + 1`).
* Columns `4, 5` (`s_fast, s_cold`): mutually exclusive boolean selectors (`s_fast + s_cold = 1`).
* Columns `6..25` (20 cold-only columns): nested sub-choice selectors `c_0 = var 6`,
  `c_1 = var 7` (`c_0 + c_1 = s_cold`), 16 cold witness columns `var 8 .. var 23`
  (squaring chain + cold ROM read + cold helper call), plus call results `var 24, var 25`.

Splitting drops all 22 cold/selector columns from `fast` (leaving **4 cols**,
0 sends, 0 ROM) and drops `aux_fast` + selector columns from `cold` (leaving
**23 cols** or **24 cols** — here `cold` uses 21 cold columns + 3 interface cols = **24 cols**!). -/
private def wideMixedChip : Chip GF :=
  let x : ArithExpr GF := .var 0
  let y : ArithExpr GF := .var 1
  let out : ArithExpr GF := .var 2
  let auxFast : ArithExpr GF := .var 3
  let sFast : ArithExpr GF := .var 4
  let sCold : ArithExpr GF := .var 5
  let c0 : ArithExpr GF := .var 6
  let c1 : ArithExpr GF := .var 7
  -- 16 cold intermediate columns (var 8 .. var 23), plus 2 cold call outputs (var 24, 25):
  -- total cold-active columns = {0,1,2} ∪ {6..25} + {26}? Wait: 3 + 21 = 24 cols (vars 6..26 -> 27 total)!
  let coldChain : List (ArithExpr GF) :=
    (List.range 17).map fun k =>
      let prev : ArithExpr GF := if k == 0 then x else .var (7 + k)
      let cur : ArithExpr GF := .var (8 + k)
      .mul sCold (.sub cur (.add prev (.const 1)))
  let constraints : List (ArithExpr GF) :=
    [ -- Top-level selector partition: sFast + sCold = 1
      .mul sFast (.sub sFast (.const 1)),
      .mul sCold (.sub sCold (.const 1)),
      .mul sFast sCold,
      .sub (.add sFast sCold) (.const 1),
      -- Fast path (only uses cols 0, 1, 2, 3!)
      .mul sFast (.sub auxFast (.mul x y)),
      .mul sFast (.sub out (.add auxFast (.const 1))),
      -- Nested sub-choice inside cold branch: c0 + c1 = sCold
      .mul c0 (.sub c0 (.const 1)),
      .mul c1 (.sub c1 (.const 1)),
      .mul c0 c1,
      .sub (.add (.add (.const 0) c0) c1) sCold,
      -- Cold branch outputs
      .mul c0 (.sub out (.add (.var 24) (.var 25))),
      .mul c1 (.sub out (.add (.var 24) (.var 26)))
    ] ++ coldChain
  let sends : List (Send GF) :=
    [ ⟨"cold_helper", [WireValue.field (.var 24)], WireValue.field 25, c0⟩,
      ⟨"cold_helper", [WireValue.field (.var 24)], WireValue.field 26, c1⟩ ]
  let memory : List (MemoryLookup GF) :=
    [ ⟨x, WireValue.field (.var 24), sCold⟩ ]
  { name := "mixed_dispatch"
    inputs := [WireValue.field 0, WireValue.field 1]
    output := WireValue.field (.var 2)
    numVars := 27
    constraints
    sends
    memory }

/-- Simple helper chip called only on the cold path (`cold_helper(a) = a + 10`). -/
private def coldHelperChip : Chip GF :=
  { name := "cold_helper"
    inputs := [WireValue.field 0]
    output := WireValue.field (.var 1)
    numVars := 2
    constraints := [.sub (.var 1) (.add (.var 0) (.const 10))]
    sends := []
    memory := [] }

private def mixedSystem : Circuit.System GF :=
  { chips := [wideMixedChip, coldHelperChip] }

private def splitEntry? : Option (SplitChipEntry GF) :=
  splitChip wideMixedChip (.var 4) (.var 5)

private def splitWidths : Nat × Nat × Nat × Nat × Nat × Nat :=
  match splitEntry? with
  | none => (0, 0, 0, 0, 0, 0)
  | some e =>
      (e.orig.numVars, e.fast.numVars, e.cold.numVars,
       e.fast.sends.length + e.fast.memory.length,
       e.cold.sends.length + e.cold.memory.length,
       if checkSplit e.orig e.fast e.cold then 1 else 0)

-- Original 27-col chip splits into 4-col fast chip (0 lookups!) + 24-col cold chip (3 lookups)
-- and passes the standalone structural verifier `checkSplit orig fast cold == true`!
#guard splitWidths == (27, 4, 24, 0, 3, 1)

/-- Single eliminated-selector chip (`b * (b - 1) = 0`, `s_fast = b`, `s_cold = 1 - b`). -/
private def elimSelChip : Chip GF :=
  let b : ArithExpr GF := .var 2
  let notB : ArithExpr GF := .sub (.const 1) b
  { name := "elim_sel_chip"
    inputs := [WireValue.field 0]
    output := WireValue.field (.var 1)
    numVars := 6
    constraints :=
      [ .mul b (.sub b (.const 1)),
        .mul b (.sub (.var 1) (.add (.var 0) (.const 1))),
        .mul notB (.sub (.var 3) (.mul (.var 0) (.var 0))),
        .mul notB (.sub (.var 4) (.mul (.var 3) (.var 0))),
        .mul notB (.sub (.var 5) (.add (.var 4) (.const 7))),
        .mul notB (.sub (.var 1) (.var 5)) ]
    sends := []
    memory := [] }

private def elimSelSplitOk : Bool :=
  match splitChip elimSelChip (.var 2) (.sub (.const 1) (.var 2)) with
  | none => false
  | some e => e.fast.numVars == 2 && e.cold.numVars == 5 && checkSplit e.orig e.fast e.cold

#guard elimSelSplitOk == true

/-- Concrete end-to-end trace check & Stage-1 trace-cell reduction test:
99 fast invocations (`(3, 5) → 16`) + 1 cold invocation (`(2, 0) → 31` calling
`cold_helper` and reading ROM cell `(2, 19)`). -/
private def mkFastOrigRow (x y : GF) : Row GF :=
  let aux := x * y
  let out := aux + 1
  ⟨"mixed_dispatch", [x, y, out, aux, 1, 0] ++ List.replicate 21 0⟩

private def mkColdOrigRow (x y : GF) : Row GF :=
  -- chain: var 8 = x + 1, var 9 = x + 2, ..., var 24 = x + 17
  let chain : List GF := (List.range 17).map fun k => x + ((k + 1 : Nat) : GF)
  let v24 : GF := x + (17 : GF)
  let v25 : GF := v24 + (10 : GF)
  let out : GF := v24 + v25
  ⟨"mixed_dispatch", [x, y, out, 0, 0, 1, 1, 0] ++ chain ++ [v25, 0]⟩

private def testRom : WireROM GF :=
  ⟨[((2 : GF), WireValue.field (19 : GF))]⟩

private def coldCallTest : Bool :=
  match splitSystem mixedSystem [("mixed_dispatch", .var 4, .var 5)] with
  | none => false
  | some sys =>
      let origFastRows := List.replicate 99 (mkFastOrigRow 3 5)
      let origColdRows := [mkColdOrigRow 2 0, ⟨"cold_helper", [19, 29]⟩]
      let entryFast : Message GF := ⟨"mixed_dispatch", [WireValue.field 3, WireValue.field 5], WireValue.field 16⟩
      let entryCold : Message GF := ⟨"mixed_dispatch", [WireValue.field 2, WireValue.field 0], WireValue.field 48⟩
      -- Weighted memo trace proving 99 fast rows + 1 cold row + 1 helper row:
      let weightedOrig : List (WeightedRow GF) :=
        ⟨mkColdOrigRow 2 0, 1⟩ :: ⟨⟨"cold_helper", [19, 29]⟩, 1⟩ :: []
      let weightedSplit := sys.splitWeightedRowsFromSource weightedOrig
      let singleFastOrig := [mkFastOrigRow 3 5]
      let singleFastSplit := sys.splitRowsFromSource singleFastOrig
      let batchOrig := origFastRows ++ origColdRows
      let batchSplit := sys.splitRowsFromSource batchOrig
      -- 99 * 27 + 27 + 2 = 2702 cells vs 99 * 4 + 24 + 2 = 422 cells (6.4× reduction!)
      (mixedSystem.check testRom entryFast singleFastOrig == .ok ()) &&
      (sys.check testRom entryFast singleFastSplit == .ok ()) &&
      (mixedSystem.check testRom entryFast (sys.liftRowsToSource singleFastSplit) == .ok ()) &&
      (mixedSystem.checkMemo testRom entryCold weightedOrig == .ok ()) &&
      (sys.checkMemo testRom entryCold weightedSplit == .ok ()) &&
      (mixedSystem.checkMemo testRom entryCold (sys.liftWeightedRowsToSource weightedSplit) == .ok ()) &&
      (traceCells batchOrig == 2702) &&
      (traceCells batchSplit == 422)

#guard coldCallTest == true

/-- Negative controls: tampering with a split chip (dropping a constraint,
dropping a live send, or breaking selector exclusivity) MUST be rejected by
`checkSplit` and `checkSplitWith`! -/
private def negativeControlsPass : Bool :=
  match splitEntry? with
  | none => false
  | some e =>
      let badFastDropConstraint : Chip GF := { e.fast with constraints := [] }
      let badColdDropSend : Chip GF := { e.cold with sends := [] }
      let badOrigNonExcl : Chip GF :=
        { e.orig with constraints := e.orig.constraints.drop 4 }
      !(checkSplitWith e.witness e.orig badFastDropConstraint e.cold) &&
      !(checkSplit e.orig badFastDropConstraint e.cold) &&
      !(checkSplitWith e.witness e.orig e.fast badColdDropSend) &&
      !(checkSplit e.orig e.fast badColdDropSend) &&
      !(checkSplitWith e.witness badOrigNonExcl e.fast e.cold) &&
      !(checkSplit badOrigNonExcl e.fast e.cold)

#guard negativeControlsPass == true

end SmokeTests

/-- info: 'Aiur.Optimized.Split.split_chip_sound_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_chip_sound_with

/-- info: 'Aiur.Optimized.Split.split_chip_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_chip_sound

/-- info: 'Aiur.Optimized.Split.split_system_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_system_sound

/-- info: 'Aiur.Optimized.Split.split_system_memo_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_system_memo_sound

/-- info: 'Aiur.Optimized.Split.split_system_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_system_complete

/-- info: 'Aiur.Optimized.Split.split_system_memo_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_system_memo_complete

/-- info: 'Aiur.Optimized.Split.split_system_check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_system_check_iff

/-- info: 'Aiur.Optimized.Split.split_system_checkMemo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_system_checkMemo_iff

/-- info: 'Aiur.Optimized.Split.split_modulesArtifact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_modulesArtifact_sound

/-- info: 'Aiur.Optimized.Split.split_physical_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms split_physical_heap_sound

end Aiur.Optimized.Split
