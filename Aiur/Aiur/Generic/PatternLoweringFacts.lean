import Aiur.Generic.LoweringChecks
import Aiur.Generic.PatternRetentionFacts
import Aiur.Generic.PatternTranslation
import Aiur.Generic.EngineInversion

namespace Aiur.Generic.PatternLowering

variable {calls : CallRelation F}

open SourceSemantics

variable [Field F] [DecidableEq F] {world : Engine.World F}

theorem env_cons_fresh (fresh : ∀ n ∈ names, n ≠ root) :
    Engine.EnvAgrees names ((root, value) :: locals) locals := by
  intro n hn
  simp only [List.find?_cons]
  rw [show (root == n) = false from beq_eq_false_iff_ne.mpr (fresh n hn).symm]

private theorem match_load_iff {pat : Pattern F} :
    matchPatternWith constant depth types heap (.load pat) value = .ok outcome ↔
      ∃ loaded, loadValue heap value = .ok loaded ∧
        matchPatternWith constant depth types heap pat loaded = .ok outcome := by
  cases h : loadValue heap value <;> simp [matchPatternWith, h, bind, Except.bind]

/-- The full let-pattern translation preserves the native, heap-reading match.
The finite safety check accounts for all compiler-generated local names. -/
theorem lowerLet_open_iff (types : Types) (pat : Pattern F) (value body : Aiur.Expr F)
    (safe : LetSafe types pat value body)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (locals : Environment F Nat) (before after : Heap F) (result : SourceValue F) :
    OpenCore.EvalExpr world calls locals (lowerLet types pat value body) before result after ↔
      ∃ input middle bindings, OpenCore.EvalExpr world calls locals value before input middle ∧
        matchPatternWith constant depth types middle pat input = .ok (some bindings) ∧
        OpenCore.EvalExpr world calls (bindings ++ locals) body middle result after := by
  cases pat with
  | load pat =>
      rw [lowerLet_load, lowerLet_open_iff types pat (.load value) body (by simpa only [LetSafe] using safe)
        constant depth locals before after result]
      simp only [OpenCore.load_iff, match_load_iff]
      constructor
      · rintro ⟨loaded, middle, bs, ⟨input, ev, read⟩, matched, eb⟩
        exact ⟨input, middle, bs, ev, ⟨loaded, read, matched⟩, eb⟩
      · rintro ⟨input, middle, bs, ev, ⟨loaded, read, matched⟩, eb⟩
        exact ⟨loaded, middle, bs, ⟨input, ev, read⟩, matched, eb⟩
  | _ =>
      unfold lowerLet
      split
      · rename_i core lowered
        rw [OpenCore.letValue_iff]
        apply exists_congr; intro input
        apply exists_congr; intro middle
        apply exists_congr; intro bindings
        rw [Pattern.toCore_match _ lowered]
        simp only [Except.ok.injEq]
      · rename_i lowered
        simp only [LetSafe, lowered] at safe
        obtain ⟨resolved, unique, fresh⟩ := safe
        simp only [plan, StateT.run, state_map_result]
        rw [OpenCore.bind_iff]
        apply exists_congr; intro input
        apply exists_congr; intro middle
        rw [exists_and_left]
        apply and_congr_right; intro _
        rw [PlanTree.let_iff _ _ unique constant depth middle input _ (by simp)
          body (fun n hn h => fresh n hn (List.mem_cons_of_mem _ h))]
        rw [← planTree_match _ resolved types _ 1 constant depth middle input]
        apply exists_congr; intro bindings
        apply and_congr_right; intro _
        apply OpenCore.evalExpr_env_iff
        apply Engine.EnvAgrees.prepend
        exact env_cons_fresh (fun n hn eq => fresh n hn (by simp [eq]))
termination_by sizeOf pat

/-- Ordered selection, polymorphic in the branch body. This is the same native
pattern matcher used by source evaluation. -/
def choose (constant : String → Ty → Except EvalError (Pattern F))
    (depth : Nat) (types : Types) (heap : Heap F) (input : SourceValue F) :
    List (Pattern F × B) → Except EvalError (Option (Environment F Nat × B))
  | [] => pure none
  | (pat, body) :: arms => do
      match ← matchPatternWith constant depth types heap pat input with
      | some bindings => return some (bindings, body)
      | none => choose constant depth types heap input arms

theorem choose_cons_iff {pat : Pattern F} :
    choose constant depth types heap input ((pat, body) :: arms) = .ok (some (bindings, selected)) ↔
      (matchPatternWith constant depth types heap pat input = .ok (some bindings) ∧ body = selected) ∨
      (matchPatternWith constant depth types heap pat input = .ok none ∧
        choose constant depth types heap input arms = .ok (some (bindings, selected))) := by
  cases h : matchPatternWith constant depth types heap pat input with
  | error e => simp [choose, h, bind, Except.bind]
  | ok matched => cases matched <;> simp [choose, h, bind, Except.bind, pure, Except.pure]

theorem choose_member {arms : List (Pattern F × B)}
    (selected : choose constant depth types heap input arms = .ok (some (bindings, body))) :
    ∃ pat, (pat, body) ∈ arms := by
  induction arms with
  | nil => simp [choose, pure, Except.pure] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, head⟩
      rcases choose_cons_iff.mp selected with ⟨_, rfl⟩ | ⟨_, selected⟩
      · exact ⟨pat, by simp⟩
      · obtain ⟨pat, hp⟩ := ih selected
        exact ⟨pat, by simp [hp]⟩

theorem choose_matched {arms : List (Pattern F × B)}
    (selected : choose constant depth types heap input arms = .ok (some (bindings, body))) :
    ∃ pat, (pat, body) ∈ arms ∧
      matchPatternWith constant depth types heap pat input = .ok (some bindings) := by
  induction arms with
  | nil => simp [choose, pure, Except.pure] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, head⟩
      rcases choose_cons_iff.mp selected with ⟨matched, rfl⟩ | ⟨_, selected⟩
      · exact ⟨pat, by simp, matched⟩
      · obtain ⟨pat, hp, matched⟩ := ih selected
        exact ⟨pat, by simp [hp], matched⟩

theorem choose_map (f : A → B) (arms : List (Pattern F × A)) :
    choose constant depth types heap input (arms.map fun arm => (arm.1, f arm.2)) =
      (choose constant depth types heap input arms).map (Option.map fun selected => (selected.1, f selected.2)) := by
  induction arms with
  | nil => rfl
  | cons arm arms ih =>
      rcases arm with ⟨pat, body⟩
      cases h : matchPatternWith constant depth types heap pat input with
      | error e => simp [choose, h, bind, Except.bind, Except.map]
      | ok result => cases result <;> simp [choose, h, ih, bind, Except.bind, Except.map, pure, Except.pure]

theorem choose_source (source : SourceSemantics.World F) (types heap input)
    (arms : List (Pattern F × Expr F)) :
    choose source.constant source.constDepth types heap input arms =
      SourceSemantics.selectArm source types heap input arms := by
  induction arms with
  | nil => rfl
  | cons arm arms ih =>
      rcases arm with ⟨pat, body⟩
      simp only [choose, SourceSemantics.selectArm, SourceSemantics.World.matchPattern, ih]
      rfl

theorem matchArms_iff (types : Types) (stem root : String)
    (arms : List (Pattern F × Aiur.Expr F)) (state : Nat)
    (safe : ArmsSafe types stem root arms state)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (heap : Heap F) (input : SourceValue F) (locals : Environment F Nat)
    (found : locals.find? (·.1 == root) = some (root, input)) :
    (∃ body, (matchArms types stem root arms state).1 = some body ∧
      OpenCore.EvalExpr world calls locals body heap result after) ↔
    ∃ bindings body, choose constant depth types heap input arms = .ok (some (bindings, body)) ∧
      OpenCore.EvalExpr world calls (bindings ++ locals) body heap result after := by
  induction arms generalizing state with
  | nil => simp [matchArms, choose, pure, StateT.pure, Except.pure]
  | cons arm arms ih =>
      rcases arm with ⟨pat, branch⟩
      obtain ⟨resolved, unique, bodyFresh, fallbackFresh, tailSafe⟩ := safe
      rw [matchArms]
      simp only [plan, state_bind_run, state_pure_run, Option.some.injEq]
      simp only [exists_eq_left']
      rw [Plan.retained_match_iff ((planTree types stem pat state).1.toPlan root) found
        (by rw [PlanTree.written]; exact (List.nodup_cons.mp unique).1)]
      rw [PlanTree.match_iff _ _ unique constant depth heap input locals found branch _
        (fun n hn h => bodyFresh n hn (List.mem_cons_of_mem _ h))
        (fun fallback present => fallbackFresh fallback (by simp [present]))]
      rw [← planTree_match pat resolved types stem state constant depth heap input]
      rw [ih _ tailSafe]
      simp only [choose_cons_iff]
      constructor
      · rintro (⟨bindings, matched, ev⟩ | ⟨missed, bindings, body, selected, ev⟩)
        · exact ⟨bindings, branch, Or.inl ⟨matched, rfl⟩, ev⟩
        · exact ⟨bindings, body, Or.inr ⟨missed, selected⟩, ev⟩
      · rintro ⟨bindings, body, (⟨matched, rfl⟩ | ⟨missed, selected⟩), ev⟩
        · exact Or.inl ⟨bindings, matched, ev⟩
        · exact Or.inr ⟨missed, bindings, body, selected, ev⟩

theorem armsSafe_fresh (safe : ArmsSafe types stem root arms state)
    {pat : Pattern F} {body : Aiur.Expr F} (member : (pat, body) ∈ arms) :
    ∀ n ∈ exprNames body, n ≠ root := by
  induction arms generalizing state with
  | nil => simp at member
  | cons arm arms ih =>
      rcases arm with ⟨p, b⟩
      obtain ⟨_, _, fresh, _, safe⟩ := safe
      rcases List.mem_cons.mp member with eq | member
      · cases eq
        exact fun n hn eq => fresh n hn (by simp [eq])
      · exact ih safe member

private theorem choose_core (types : Types) (arms : List (Pattern F × Aiur.Expr F))
    {core : List (Aiur.Pattern F × Aiur.Expr F)}
    (lowered : arms.mapM (fun arm => return (← arm.1.toCore? types, arm.2)) = some core) :
    choose constant depth types heap input arms = .ok (Aiur.selectArm input core) := by
  have related := option_mapM_relation lowered
  clear lowered
  induction related with
  | nil => rfl
  | @cons arm target arms core h _ ih =>
      rcases arm with ⟨pat, body⟩
      cases head : pat.toCore? types with
      | none => simp [head] at h
      | some cp =>
          have same : (cp, body) = target := by simpa [head] using h
          subst target
          rw [choose, Pattern.toCore_match pat head]
          cases matched : cp.bindings input <;>
            simp [bind, Except.bind, pure, Except.pure, Aiur.selectArm, matched, ih]

/-- Ordered source matching and its circuit-language expression have exactly
the same successful branch, bindings, result, and heap. -/
theorem lowerMatch_open_iff (types : Types) (value : Aiur.Expr F) (arms : List (Pattern F × Aiur.Expr F))
    (safe : MatchSafe types value arms)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (locals : Environment F Nat) (before after : Heap F) (result : SourceValue F) :
    OpenCore.EvalExpr world calls locals (lowerMatch types value arms) before result after ↔
      ∃ input middle bindings body, OpenCore.EvalExpr world calls locals value before input middle ∧
        choose constant depth types middle input arms = .ok (some (bindings, body)) ∧
        OpenCore.EvalExpr world calls (bindings ++ locals) body middle result after := by
  unfold lowerMatch
  split
  · rename_i core lowered
    rw [OpenCore.matchValue_iff]
    apply exists_congr; intro input
    apply exists_congr; intro middle
    apply exists_congr; intro bindings
    apply exists_congr; intro body
    rw [choose_core types arms lowered]
    simp only [Except.ok.injEq]
  · rename_i lowered
    simp only [MatchSafe, lowered] at safe
    rw [OpenCore.bind_iff]
    apply exists_congr; intro input
    apply exists_congr; intro middle
    simp only [exists_and_left]
    apply and_congr_right; intro _
    let stem := freshPrefix (exprNames value ++ arms.flatMap (fun arm => arm.1.bindingNames ++ exprNames arm.2))
    let root := stem ++ "0"
    have body_iff : OpenCore.EvalExpr world calls ((root, input) :: locals)
        ((matchArms types stem root arms 1).1.getD (.matchValue (.var root) [])) middle result after ↔
        ∃ body, (matchArms types stem root arms 1).1 = some body ∧
          OpenCore.EvalExpr world calls ((root, input) :: locals) body middle result after := by
      cases generated : (matchArms types stem root arms 1).1 with
      | some body => simp only [Option.getD_some, Option.some.injEq, exists_eq_left']
      | none =>
          simp only [Option.getD_none, reduceCtorEq, false_and, exists_const, OpenCore.matchValue_iff, Aiur.selectArm]
          simp
    simp only [StateT.run]
    rw [body_iff, matchArms_iff types stem root arms 1 safe constant depth middle input _ (by simp)]
    apply exists_congr; intro bindings
    apply exists_congr; intro body
    apply and_congr_right; intro selected
    obtain ⟨pat, member⟩ := choose_member selected
    exact OpenCore.evalExpr_env_iff ((env_cons_fresh (armsSafe_fresh safe member)).prepend bindings)

theorem lowerLet_iff (types : Types) (pat : Pattern F) (value body : Aiur.Expr F)
    (safe : LetSafe types pat value body)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (locals : Environment F Nat) (before after : Heap F) (result : SourceValue F) :
    Engine.EvalExpr world locals (lowerLet types pat value body) before result after ↔
      ∃ input middle bindings, Engine.EvalExpr world locals value before input middle ∧
        matchPatternWith constant depth types middle pat input = .ok (some bindings) ∧
        Engine.EvalExpr world (bindings ++ locals) body middle result after := by
  simpa only [OpenCore.closed_iff] using lowerLet_open_iff (world := world) (calls := Engine.EvalFn world)
    types pat value body safe constant depth locals before after result

theorem lowerMatch_iff (types : Types) (value : Aiur.Expr F) (arms : List (Pattern F × Aiur.Expr F))
    (safe : MatchSafe types value arms)
    (constant : String → Ty → Except EvalError (Pattern F)) (depth : Nat)
    (locals : Environment F Nat) (before after : Heap F) (result : SourceValue F) :
    Engine.EvalExpr world locals (lowerMatch types value arms) before result after ↔
      ∃ input middle bindings body, Engine.EvalExpr world locals value before input middle ∧
        choose constant depth types middle input arms = .ok (some (bindings, body)) ∧
        Engine.EvalExpr world (bindings ++ locals) body middle result after := by
  simpa only [OpenCore.closed_iff] using lowerMatch_open_iff (world := world) (calls := Engine.EvalFn world)
    types value arms safe constant depth locals before after result

end Aiur.Generic.PatternLowering
