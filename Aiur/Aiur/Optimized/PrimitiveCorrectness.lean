import Aiur.Optimized.StateSemantics
import Aiur.Optimized.PatternCorrectness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem equations_sound {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : (do for condition in conditions do equation scope condition : Build F Unit) before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment ∧
      ∀ condition ∈ conditions, (before.activation scope).denote assignment * condition.denote assignment = 0 := by
  induction conditions generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      exact ⟨same ▸ valid, by simp⟩
  | cons condition conditions ih =>
      simp [List.forIn_cons, equation, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
      obtain ⟨previous, tail⟩ := ih compiled
      obtain ⟨previousValid, head⟩ := equation_valid (scope := scope) (polynomial := condition) rfl previous
      exact ⟨previousValid, fun polynomial member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact head
        · exact tail polynomial member⟩

theorem equalValue_sound {scope : ScopeId} {left right : Symbolic F} {before after : State F}
    (compiled : equalValue scope left right before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment ∧
      ((before.activation scope).denote assignment = 1 →
        left.map (Circuit.ArithExpr.denote assignment) = right.map (Circuit.ArithExpr.denote assignment)) := by
  simp only [equalValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · rename_i shaped
    obtain ⟨types, widths⟩ := not_or.mp shaped
    have types := not_ne_iff.mp types
    have widths := not_ne_iff.mp widths
    obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
    have equations : (do
        for polynomial in (left.words.zip right.words).map (fun (a, b) => Polynomial.sub a b) do
          equation scope polynomial : Build F Unit) before = .ok ((), after) := by
      simpa only [List.forIn_map] using rest
    obtain ⟨previous, equal⟩ := equations_sound equations valid
    refine ⟨previous, fun active => ?_⟩
    have words : left.words.map (Circuit.ArithExpr.denote assignment) =
        right.words.map (Circuit.ArithExpr.denote assignment) := by
      apply List.ext_getElem
      · simp [widths]
      · intro i leftBound rightBound
        have leftIn : i < left.words.length := by simpa using leftBound
        have rightIn : i < right.words.length := by simpa using rightBound
        have member : (left.words[i], right.words[i]) ∈ left.words.zip right.words :=
          List.mem_iff_getElem.mpr ⟨i, by simp [leftIn, rightIn], List.getElem_zip⟩
        have equation := equal _ (List.mem_map.mpr ⟨_, member, rfl⟩)
        simpa only [active, Scalar.Circuit.ArithExpr.denote, one_mul, sub_eq_zero, List.getElem_map] using equation
    cases left; cases right
    simp_all [WireValue.map]

private theorem failure_terms_sound {scope : ScopeId} {conditions terms : List (Polynomial F)}
    {before after : State F}
    (compiled : (conditions.mapM fun difference => do
      return Polynomial.mul difference (.var (← fresh (.auxiliary scope))) : Build F (List (Polynomial F)))
        before = .ok (terms, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment ∧
      after.scopes = before.scopes ∧ (AllZero conditions assignment → AllZero terms assignment) := by
  induction conditions generalizing terms before with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
      exact ⟨valid, rfl, fun _ => by simp [AllZero]⟩
  | cons difference conditions ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨term, s₁, headRun, tailBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, s₂, tailRun, finished⟩ := bind_ok.mp tailBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨middleValid, tailScopes, tailZero⟩ := ih tailRun
      obtain ⟨id, s₃, freshRun, finished⟩ := bind_ok.mp headRun
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      have scopes : s₃.scopes = before.scopes := by
        simpa only using congrArg (fun state : State F => state.scopes) (fresh_eq freshRun).2
      refine ⟨fresh_valid freshRun middleValid, tailScopes.trans scopes, fun zero term member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · change difference.denote assignment * assignment id = 0
        rw [zero _ (List.mem_cons_self ..), zero_mul]
      · exact tailZero (fun p hp => zero p (List.mem_cons_of_mem _ hp)) term member

private theorem fold_add_zero {conditions : List (Polynomial F)} {assignment : Witness → F}
    (zero : AllZero conditions assignment) (start : Polynomial F) :
    (conditions.foldl Polynomial.add start).denote assignment = start.denote assignment := by
  induction conditions generalizing start with
  | nil => rfl
  | cons condition conditions ih =>
      rw [List.foldl_cons, ih (fun p hp => zero p (List.mem_cons_of_mem _ hp))]
      change start.denote assignment + condition.denote assignment = start.denote assignment
      rw [zero _ (List.mem_cons_self ..), add_zero]

/-- An active failure block cannot accept a matching earlier pattern. This
theorem refers to the actual emitted equation and allocated coefficients. -/
theorem failure_sound {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : failure scope conditions before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment ∧
      ((before.activation scope).denote assignment = 1 → ¬ AllZero conditions assignment) := by
  simp only [failure] at compiled
  obtain ⟨terms, middle, termsRun, equationRun⟩ := bind_ok.mp compiled
  obtain ⟨middleValid, equation⟩ := equation_valid equationRun valid
  obtain ⟨beforeValid, scopes, termsZero⟩ := failure_terms_sound termsRun middleValid
  refine ⟨beforeValid, fun active zero => ?_⟩
  have activation : middle.activation scope = before.activation scope := by simp only [State.activation, scopes]
  rw [activation, active] at equation
  change 1 * ((terms.foldl Polynomial.add (.const 0)).denote assignment - 1) = 0 at equation
  rw [fold_add_zero (termsZero zero)] at equation
  exact one_ne_zero (by simpa only [Scalar.Circuit.ArithExpr.denote, zero_sub, one_mul, neg_eq_zero] using equation)

end Aiur.Optimized.Compiler
