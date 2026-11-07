import Aiur.Generic.ControlContinuationFacts

namespace Aiur.Generic.ControlLower
open SourceSemantics OpenSource
variable {F : Type} [Field F] [DecidableEq F]
variable {world : SourceSemantics.World F} {calls : CallRelation F}
variable {env bound : Renaming} {source target : Environment F Nat}
variable {next : Continuation F} {handlers : Handlers F}

/-- The expression-level claim used in the compiler induction. The source
body still has lexical exits; the generated body invokes their continuations. -/
def Correct (world : SourceSemantics.World F) (calls : CallRelation F) (env : Renaming)
    (expr code : Expr F) (next : Continuation F) (handlers : Handlers F) : Prop :=
  ∀ source target before result after, ScopeRel env source target →
    (OpenSource.EvalExpr world calls [] target code before result after ↔
      Exec world calls [] source expr
        (fun v h => next.run world calls target v h result after)
        (fun t v h => handlers.run world calls target t v h result after) before)

def ArgsCorrect (world : SourceSemantics.World F) (calls : CallRelation F) (env : Renaming)
    (exprs : List (Expr F)) (code : Expr F) (next : Continuation F) (handlers : Handlers F) : Prop :=
  ∀ source target before result after, ScopeRel env source target →
    (OpenSource.EvalExpr world calls [] target code before result after ↔
      ExecArgs world calls [] source exprs
        (fun vs h => next.run world calls target (.tuple vs) h result after)
        (fun t v h => handlers.run world calls target t v h result after) before)

theorem renamed_some (plain : Consts.dependencies pat = []) :
    world.matchPattern [] heap (renamePattern bound pat) value = .ok (some output) ↔
      ∃ bs, world.matchPattern [] heap pat value = .ok (some bs) ∧ output = renameBindings bound bs := by
  simp only [World.matchPattern, matchPattern_rename pat plain]
  cases matched : matchPatternWith world.constant world.constDepth [] heap pat value with
  | error e => simp [Except.map]
  | ok bs => cases bs <;> simp [Except.map, eq_comm]

theorem renamed_none (plain : Consts.dependencies pat = []) :
    world.matchPattern [] heap (renamePattern bound pat) value = .ok none ↔
      world.matchPattern [] heap pat value = .ok none := by
  simp only [World.matchPattern, matchPattern_rename pat plain]
  cases matchPatternWith world.constant world.constDepth [] heap pat value with
  | error e => simp [Except.map]
  | ok bs => cases bs <;> simp [Except.map]

/-- Entering a matched branch introduces renamed pattern bindings. The
continuations retain their surrounding scope, even if the source shadows it. -/
theorem branch_iff
    (built : bindings pat (reserved env next handlers) = .ok bound)
    (compiled : Correct world calls (bound ++ env) body code next handlers)
    (fresh : Fresh input env next handlers) (scope : ScopeRel env source target) :
    (∃ bs, world.matchPattern [] heap (renamePattern bound pat) value = .ok (some bs) ∧
      OpenSource.EvalExpr world calls [] (bs ++ (input, value) :: target) code heap result after) ↔
    ∃ bs, world.matchPattern [] heap pat value = .ok (some bs) ∧
      Exec world calls [] (bs ++ source) body
        (fun v h => next.run world calls target v h result after)
        (fun t v h => handlers.run world calls target t v h result after) heap := by
  obtain ⟨plain, unique, keys, unused⟩ := bindings_ok built
  have branch (bs : Environment F Nat)
      (matched : world.matchPattern [] heap pat value = .ok (some bs)) :
      OpenSource.EvalExpr world calls [] (renameBindings bound bs ++ (input, value) :: target)
        code heap result after ↔
      Exec world calls [] (bs ++ source) body
        (fun v h => next.run world calls target v h result after)
        (fun t v h => handlers.run world calls target t v h result after) heap := by
    have names := matchPattern_names pat plain matched
    have covered : ∀ n ∈ bs.map Prod.fst, n ∈ bound.map Prod.fst := by
      intro n hn; exact (keys n).mpr (names ▸ hn)
    have boundFresh : ∀ n ∈ bound.map Prod.snd, n ∉ env.map Prod.snd := by
      intro n hn he; exact unused n hn (by simp [reserved, he])
    have relation := (scope.add fresh.scope value).extend unique (fun n => (keys n).trans (by rw [names])) boundFresh
    rw [compiled _ _ _ _ _ relation]
    have untouched (k : Continuation F) (hk : ∀ n ∈ k.names, n ∈ reserved env next handlers) :
        ∀ n ∈ k.names, n ∉ (renameBindings bound bs).map Prod.fst := by
      intro n hn bad
      exact unused n (renameBindings_names covered n bad) (hk n hn)
    apply Exec.congr
    · intro v h
      exact (next.run_prepend _ (untouched next (by intros; simp [reserved, *]))).trans
        (next.run_add fresh.next)
    · intro t v h
      apply Iff.trans (Handlers.run_prepend _ ?_) (Handlers.run_add fresh.handlers)
      intro t k found
      apply untouched k
      intro n hn
      have member : (t, k) ∈ handlers := by
        obtain ⟨left, right, rfl, _⟩ := List.lookup_eq_some_iff.mp found
        simp
      simp only [reserved, List.mem_append, List.mem_flatMap]
      exact .inr ⟨_, member, hn⟩
  constructor
  · rintro ⟨bs, matched, ev⟩
    obtain ⟨original, originalMatch, rfl⟩ := (renamed_some plain).mp matched
    exact ⟨_, originalMatch, (branch _ originalMatch).mp ev⟩
  · rintro ⟨bs, matched, ev⟩
    exact ⟨_, (renamed_some plain).mpr ⟨bs, matched, rfl⟩, (branch _ matched).mpr ev⟩

def Selected (world : SourceSemantics.World F) (heap : Heap F) (value : SourceValue F)
    (arms : List (Pattern F × Expr F)) (post : Environment F Nat → Expr F → Prop) : Prop :=
  ∃ bindings body, SourceSemantics.selectArm world [] heap value arms = .ok (some (bindings, body)) ∧ post bindings body

theorem selected_nil : ¬ Selected world heap value [] post := by
  simp [Selected, SourceSemantics.selectArm]

theorem selected_cons : Selected world heap value ((pat, body) :: arms) post ↔
    (∃ bs, world.matchPattern [] heap pat value = .ok (some bs) ∧ post bs body) ∨
      (world.matchPattern [] heap pat value = .ok none ∧ Selected world heap value arms post) := by
  cases matched : world.matchPattern [] heap pat value with
  | error e => simp [Selected, SourceSemantics.selectArm, matched, bind, Except.bind]
  | ok bs => cases bs <;> simp [Selected, SourceSemantics.selectArm, matched, bind, Except.bind, pure, Except.pure]

theorem selected_congr {arms others : List (Pattern F × Expr F)}
    {left right : Environment F Nat → Expr F → Prop}
    (related : List.Forall₂ (fun a b =>
      ((∃ bs, world.matchPattern [] heap a.1 value = .ok (some bs) ∧ left bs a.2) ↔
        ∃ bs, world.matchPattern [] heap b.1 value = .ok (some bs) ∧ right bs b.2) ∧
      (world.matchPattern [] heap a.1 value = .ok none ↔ world.matchPattern [] heap b.1 value = .ok none)) arms others) :
    Selected world heap value arms left ↔ Selected world heap value others right := by
  induction related with
  | nil => simp only [Selected, SourceSemantics.selectArm, except_pure_ok, reduceCtorEq, false_and, exists_false]
  | @cons a b arms others first _ ih =>
      rcases a with ⟨pa, ea⟩; rcases b with ⟨pb, eb⟩
      rw [selected_cons, selected_cons, first.1, first.2, ih]

theorem eval_let_var :
    OpenSource.EvalExpr world calls [] ((input, value) :: target)
      (.letValue pat (.var input) code) before result after ↔
    ∃ bs, world.matchPattern [] before pat value = .ok (some bs) ∧
      OpenSource.EvalExpr world calls [] (bs ++ (input, value) :: target) code before result after := by
  constructor
  · intro h; cases h with
    | letValue ev matched body =>
        cases ev with
        | var found =>
            have same := by simpa using found
            obtain rfl := same
            exact ⟨_, matched, body⟩
  · rintro ⟨bs, matched, ev⟩
    exact .letValue (.var (by simp)) matched ev

theorem eval_match_var :
    OpenSource.EvalExpr world calls [] ((input, value) :: target)
      (.matchValue (.var input) arms) before result after ↔
    Selected world before value arms (fun bs body =>
      OpenSource.EvalExpr world calls [] (bs ++ (input, value) :: target) body before result after) := by
  constructor
  · intro h; cases h with
    | matchValue ev selected body =>
        cases ev with
        | var found =>
            have same := by simpa using found
            obtain rfl := same
            exact ⟨_, _, selected, body⟩
  · rintro ⟨bs, body, selected, ev⟩
    exact .matchValue (.var (by simp)) selected ev

end Aiur.Generic.ControlLower
