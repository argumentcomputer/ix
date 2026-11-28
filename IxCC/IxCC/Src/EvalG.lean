import IxCC.Src.Semantics
import IxCC.Src.Table.Guess

/-! # Thin Relational `SrcG` Operational Semantics (`IxCC.Src.EvalG`)

Extends standard deterministic `SrcEval` (`IxCC.Src.Semantics`) with a single nondeterministic
**Phase 2.2 Tier-2 `guess`** rule, leaving `Src.Value`, `Src.Head`, and `Src.eval` untouched:

* **`RunG p ls f xs y`** (call-level relational judgment):
  - `RunG.src`: any standard `SrcEval` derivation `runAt p k ls f xs = .ok y`.
  - `RunG.guess`: when `f` carries a `guess` table entry `g = { checker := c, arity := k, thm,
    comp? }`, `xs.length = g.arity`, and `p.known.boolTrue = some boolTrueC`, `f xs`
    nondeterministically yields any witness `y` for which `c xs y` evaluates to `Bool.true`
    (`.con boolTrueC [] [] []`) in `RunG`.

* **`EvalG p ls ρ t v`** (thin term-level relational judgment):
  - `EvalG.src`: any standard `Src.eval p k ls ρ t = .ok v`.
  - `EvalG.guess`: at a saturated strict call `Term.mkApps (.const f us) args` where `f` has a
    `guess` entry of arity `args.length`, evaluating each argument in `EvalG` to `xs` and
    verifying `g.checker (xs ++ [y])` evaluates to `Bool.true` in `RunG` yields `y`.

* **Conservativity**:
  - Every standard `Src` derivation is a `SrcG` derivation (`runG_of_runAt`, `runG_of_run`,
    `evalG_of_eval`).
  - Whenever `p.table.guess` is empty (`∀ f, p.table.guessOf f = none`, in particular
    `p.table.guess = .leaf`), `RunG` and `EvalG` collapse identically to standard `SrcEval`
    (`runG_iff_src_of_empty`, `runG_root_iff_src_of_leaf`, `evalG_iff_eval_of_empty`,
    `evalG_iff_eval_of_leaf`).

Model-level soundness (`S2`: every `SrcG` derivation over a validated table agrees with standard
denotational equality `y = f xs`) is proved in `IxCCGrounding.Guess`, keeping `IxCC` free of
`IxCK.Kernel.Denotes`. -/

namespace IxCC.Src

open IxCC.Sem (Result)

/-- Run constant `f` at concrete universe levels `ls` on argument values `xs` under standard
clocked `SrcEval` (`evalConst` followed by `applyAll`). At `ls = []`, this is definitionally
`IxCC.Src.run`. -/
def runAt (p : Program) (k : Nat) (ls : Levels) (f : CId) (xs : List Value) : Result Value :=
  match evalConst p k ls f with
  | .ok fv => applyAll p k fv (xs.map .val)
  | r => r

theorem runAt_nil (p : Program) (k : Nat) (root : CId) (xs : List Value) :
    runAt p k [] root xs = run p k root xs := rfl

/-! ## Call-level relational `SrcG` judgment (`RunG`) -/

/-- Thin relational `SrcG` call judgment: standard `SrcEval` (`runAt`) plus the single
nondeterministic `guess` rule. Recursive in the checker premise so nested/chained `guess`
entries compose cleanly (acyclicity is enforced by `Table.Guess.checkDoesNotReach`). -/
inductive RunG (p : Program) : Levels → CId → List Value → Value → Prop where
  /-- Standard `SrcEval` derivation. -/
  | src {ls : Levels} {f : CId} {xs : List Value} {y : Value} {k : Nat} :
      runAt p k ls f xs = .ok y →
      RunG p ls f xs y
  /-- Nondeterministic `guess` rule: when `p.table.guessOf f = some g`, `xs.length = g.arity`,
  and `p.known.boolTrue = some boolTrueC`, `f xs` yields any witness `y` accepted by `g.checker`
  (evaluating to `Bool.true` in `RunG`). -/
  | guess {ls : Levels} {f : CId} {g : GuessEntry} {xs : List Value} {y : Value}
      {boolTrueC : CId} :
      p.table.guessOf f = some g →
      xs.length = g.arity →
      p.known.boolTrue = some boolTrueC →
      RunG p ls g.checker (xs ++ [y]) (.con boolTrueC [] [] []) →
      RunG p ls f xs y

/-- Top-level (level-monomorphic) `RunG` at a root constant (`ls = []`). -/
abbrev RunGRoot (p : Program) (root : CId) (xs : List Value) (y : Value) : Prop :=
  RunG p [] root xs y

/-- Convenience constructor when the checker runs via standard `SrcEval`. -/
theorem runG_of_guess_src {p : Program} {ls : Levels} {f : CId} {g : GuessEntry}
    {xs : List Value} {y : Value} {boolTrueC : CId} {k : Nat}
    (hg : p.table.guessOf f = some g)
    (hlen : xs.length = g.arity)
    (hbt : p.known.boolTrue = some boolTrueC)
    (hchk : runAt p k ls g.checker (xs ++ [y]) = .ok (.con boolTrueC [] [] [])) :
    RunG p ls f xs y :=
  .guess hg hlen hbt (.src hchk)

/-! ## Conservativity of `RunG` -/

/-- **Conservativity (inclusion)**: every standard `SrcEval` call derivation is a `RunG`
derivation. -/
theorem runG_of_runAt {p : Program} {k : Nat} {ls : Levels} {f : CId} {xs : List Value}
    {y : Value} (h : runAt p k ls f xs = .ok y) :
    RunG p ls f xs y :=
  .src h

/-- **Conservativity (root inclusion)**: every standard `Src.run` derivation is a `RunGRoot`
derivation. -/
theorem runG_of_run {p : Program} {k : Nat} {root : CId} {xs : List Value} {y : Value}
    (h : run p k root xs = .ok y) :
    RunGRoot p root xs y :=
  .src h

/-- **Local collapse**: at any constant `f` without a `guess` entry, `RunG` coincides with
standard `SrcEval` (`runAt`). -/
theorem runG_iff_src_of_no_entry {p : Program} {ls : Levels} {f : CId} {xs : List Value}
    {y : Value} (hnone : p.table.guessOf f = none) :
    RunG p ls f xs y ↔ ∃ k, runAt p k ls f xs = .ok y := by
  constructor
  · intro h
    cases h with
    | src hk => exact ⟨_, hk⟩
    | guess hg _ _ _ => rw [hnone] at hg; cases hg
  · rintro ⟨k, hk⟩
    exact .src hk

/-- **Global collapse**: when `p.table.guess` has no entries, `RunG` collapses identically to
standard `SrcEval` (`runAt`). -/
theorem runG_iff_src_of_empty {p : Program} (hempty : ∀ f, p.table.guessOf f = none)
    {ls : Levels} {f : CId} {xs : List Value} {y : Value} :
    RunG p ls f xs y ↔ ∃ k, runAt p k ls f xs = .ok y :=
  runG_iff_src_of_no_entry (hempty f)

/-- **Root collapse when `p.table.guess = .leaf`**: `RunGRoot` collapses identically to
`Src.run`. -/
theorem runG_root_iff_src_of_leaf {p : Program} (hleaf : p.table.guess = .leaf)
    {root : CId} {xs : List Value} {y : Value} :
    RunGRoot p root xs y ↔ ∃ k, run p k root xs = .ok y :=
  runG_iff_src_of_no_entry (by simp [Table.guessOf, hleaf, NatMap.get?])

/-! ## Term-level relational `SrcG` judgment (`EvalG`) -/

mutual

/-- Thin term-level relational `SrcG` judgment: extends standard `Src.eval` with one
nondeterministic `guess` call rule at saturated strict relevant applications
`Term.mkApps (.const f us) args`. -/
inductive EvalG (p : Program) : Levels → Env → Term → Value → Prop where
  /-- Standard `Src.eval` derivation. -/
  | src {ls : Levels} {ρ : Env} {t : Term} {v : Value} {k : Nat} :
      eval p k ls ρ t = .ok v →
      EvalG p ls ρ t v
  /-- Nondeterministic `guess` call at a saturated strict relevant spine `f.{us} a₀ … a_{k-1}`. -/
  | guess {ls : Levels} {ρ : Env} {f : CId} {us : List Ixon.Univ}
      {args : List Term.Arg} {xs : List Value} {y : Value}
      {g : GuessEntry} {boolTrueC : CId} :
      p.table.guessOf f = some g →
      args.length = g.arity →
      (∀ a ∈ args, a.2.1 = .strict ∧ a.2.2.irrAt ls = false) →
      EvalGArgs p ls ρ args xs →
      p.known.boolTrue = some boolTrueC →
      RunG p (us.map (evalUniv ls)) g.checker (xs ++ [y]) (.con boolTrueC [] [] []) →
      EvalG p ls ρ (Term.mkApps (.const f us) args) y

/-- Pointwise `EvalG` over an application argument list. -/
inductive EvalGArgs (p : Program) : Levels → Env → List Term.Arg → List Value → Prop where
  | nil {ls : Levels} {ρ : Env} : EvalGArgs p ls ρ [] []
  | cons {ls : Levels} {ρ : Env} {a : Term.Arg} {args : List Term.Arg} {x : Value}
      {xs : List Value} :
      EvalG p ls ρ a.1 x →
      EvalGArgs p ls ρ args xs →
      EvalGArgs p ls ρ (a :: args) (x :: xs)

end

theorem evalGArgs_length {p : Program} {ls : Levels} {ρ : Env} :
    ∀ {args : List Term.Arg} {xs : List Value},
      EvalGArgs p ls ρ args xs → xs.length = args.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [evalGArgs_length h]

/-! ## Conservativity of `EvalG` -/

/-- **Conservativity (term inclusion)**: every standard `Src.eval` derivation is an `EvalG`
derivation. -/
theorem evalG_of_eval {p : Program} {k : Nat} {ls : Levels} {ρ : Env} {t : Term} {v : Value}
    (h : eval p k ls ρ t = .ok v) :
    EvalG p ls ρ t v :=
  .src h

/-- **Conservativity (term collapse)**: when `p.table.guess` has no entries, `EvalG` collapses
identically to standard `Src.eval`. -/
theorem evalG_iff_eval_of_empty {p : Program} (hempty : ∀ f, p.table.guessOf f = none)
    {ls : Levels} {ρ : Env} {t : Term} {v : Value} :
    EvalG p ls ρ t v ↔ ∃ k, eval p k ls ρ t = .ok v := by
  constructor
  · intro h
    cases h with
    | src hk => exact ⟨_, hk⟩
    | guess hg _ _ _ _ _ => rw [hempty _] at hg; cases hg
  · rintro ⟨k, hk⟩
    exact .src hk

/-- **Conservativity (term collapse when `p.table.guess = .leaf`)**. -/
theorem evalG_iff_eval_of_leaf {p : Program} (hleaf : p.table.guess = .leaf)
    {ls : Levels} {ρ : Env} {t : Term} {v : Value} :
    EvalG p ls ρ t v ↔ ∃ k, eval p k ls ρ t = .ok v :=
  evalG_iff_eval_of_empty (fun _ => by simp [Table.guessOf, hleaf, NatMap.get?])

end IxCC.Src
