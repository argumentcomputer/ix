import IxSharingVerify.IngestionTable
import IxC.Kernel.Audit.Axioms

/-! Raising resource limits never changes a successful sharing run.

`LimitsLe a b` says that `b` grants at least every resource `a` grants; the
two switches (`prune`, `uniformSubsetSearch`) are free, since the family route
reads neither. Every limit check of the construction compares a count that
does not depend on the limits against its limit, so a run that succeeds
under `a` succeeds under `b` with the same result, statistics included. This
module proves it for ingestion and expansion. -/

namespace Ix.Sharing.Verify.Budget

open Ix.Sharing.Exact
open Ix.Sharing.Verify.Ingestion
open Ix.Sharing.Verify.SharingExact (bind_eq_ok)

/-- `b` grants at least every resource of `a`. -/
structure LimitsLe (a b : Limits) : Prop where
  exprVisits : a.maxExprVisits ≤ b.maxExprVisits
  depth : a.maxDepth ≤ b.maxDepth
  nodes : a.maxNodes ≤ b.maxNodes
  states : a.maxStates ≤ b.maxStates
  knapsackCells : a.maxKnapsackCells ≤ b.maxKnapsackCells
  transitions : a.maxTransitions ≤ b.maxTransitions
  costEvals : a.maxCostEvals ≤ b.maxCostEvals
  outputBytes : a.maxOutputBytes ≤ b.maxOutputBytes
  materialize : a.maxMaterialize ≤ b.maxMaterialize
  materializeWork : a.maxMaterializeWork ≤ b.maxMaterializeWork
  oracleTables : a.maxOracleTables ≤ b.maxOracleTables
  oracleVariants : a.maxOracleVariants ≤ b.maxOracleVariants

theorem LimitsLe.refl (a : Limits) : LimitsLe a a :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem LimitsLe.trans {a b c : Limits} (first : LimitsLe a b) (second : LimitsLe b c) : LimitsLe a c :=
  ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2 second.2, Nat.le_trans first.3 second.3,
    Nat.le_trans first.4 second.4, Nat.le_trans first.5 second.5, Nat.le_trans first.6 second.6,
    Nat.le_trans first.7 second.7, Nat.le_trans first.8 second.8, Nat.le_trans first.9 second.9,
    Nat.le_trans first.10 second.10, Nat.le_trans first.11 second.11,
    Nat.le_trans first.12 second.12⟩

/-- The fieldwise maximum of two limits, with the switches of the first. -/
def Limits.join (a b : Limits) : Limits :=
  { a with
    maxExprVisits := max a.maxExprVisits b.maxExprVisits
    maxDepth := max a.maxDepth b.maxDepth
    maxNodes := max a.maxNodes b.maxNodes
    maxStates := max a.maxStates b.maxStates
    maxKnapsackCells := max a.maxKnapsackCells b.maxKnapsackCells
    maxTransitions := max a.maxTransitions b.maxTransitions
    maxCostEvals := max a.maxCostEvals b.maxCostEvals
    maxOutputBytes := max a.maxOutputBytes b.maxOutputBytes
    maxMaterialize := max a.maxMaterialize b.maxMaterialize
    maxMaterializeWork := max a.maxMaterializeWork b.maxMaterializeWork
    maxOracleTables := max a.maxOracleTables b.maxOracleTables
    maxOracleVariants := max a.maxOracleVariants b.maxOracleVariants }

theorem LimitsLe.join_left (a b : Limits) : LimitsLe a (Limits.join a b) :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _,
    Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _,
    Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem LimitsLe.join_right (a b : Limits) : LimitsLe b (Limits.join a b) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _,
    Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _,
    Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem bump_mono {count n a b : Nat} {r : Resource} {x : Nat} (le : a ≤ b)
    (ran : bump count n a r = .ok x) : bump count n b r = .ok x := by
  unfold bump at ran ⊢
  dsimp only at ran ⊢
  by_cases over : count + n > a
  · simp only [over, ↓reduceIte] at ran
    cases ran
  · simp only [over, ↓reduceIte] at ran
    simp only [show ¬ count + n > b by omega, ↓reduceIte]
    exact ran

theorem bind_ok_eq {ε α β : Type} {x : Except ε α} {a : α} {f : α → Except ε β}
    (h : x = .ok a) : (x >>= f) = f a := by
  rw [h]
  rfl

theorem any_gt_mono {xs : Array Nat} {a b : Nat} (le : a ≤ b)
    (below : ¬ (xs.any fun x => decide (x > a)) = true) : ¬ (xs.any fun x => decide (x > b)) = true := by
  intro above
  apply below
  obtain ⟨i, hi, hp⟩ := Array.any_eq_true.mp above
  exact Array.any_eq_true.mpr ⟨i, hi, by simp only [decide_eq_true_eq] at hp ⊢; omega⟩

/-! ## Ingestion -/

/-- Every successful run of `a` is a run of `b` with the same value and state. -/
def Refines {α : Type} (a b : IngestM α) : Prop :=
  ∀ before out, a.run before = .ok out → b.run before = .ok out

theorem Refines.refl {α : Type} (a : IngestM α) : Refines a a := fun _ _ ran => ran

theorem Refines.bind {α β : Type} {a b : IngestM α} {f g : α → IngestM β} (first : Refines a b)
    (rest : ∀ x, Refines (f x) (g x)) : Refines (a >>= f) (b >>= g) := by
  intro before out ran
  obtain ⟨value, middle, aRan, fRan⟩ := bind_run ran
  rw [StateT.run_bind, bind_ok_eq (first before (value, middle) aRan)]
  exact rest value middle out fRan

theorem internNode_refines {a b : Limits} (le : a.maxNodes ≤ b.maxNodes) (node : Node) :
    Refines (internNode a node) (internNode b node) := by
  intro before out ran
  unfold internNode at ran ⊢
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at ran ⊢
  cases step : before.interner.intern node with
  | mk interner actual =>
    rw [step] at ran
    by_cases large : interner.nodes.size > a.maxNodes
    · simp only [large, ↓reduceIte] at ran
      change Except.error _ = Except.ok out at ran
      cases ran
    · simp only [large, ↓reduceIte] at ran
      simp only [show ¬ interner.nodes.size > b.maxNodes by omega, ↓reduceIte]
      exact ran

theorem cached_refines {a b : Limits} (le : LimitsLe a b) (depth : Nat) (source : Ixon.Expr)
    {first second : IngestM Nat} (body : Refines first second) :
    Refines (cached a depth source first) (cached b depth source second) := by
  intro before out ran
  unfold cached at ran ⊢
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at ran ⊢
  cases found : before.ptrCache.get? (exprKey source) with
  | some actual =>
    rw [found] at ran
    exact ran
  | none =>
    rw [found] at ran
    by_cases deep : depth > a.maxDepth
    · simp only [deep, ↓reduceIte] at ran
      change Except.error _ = Except.ok out at ran
      cases ran
    · simp only [deep, ↓reduceIte, StateT.run_bind, StateT.run_get, pure_bind] at ran
      simp only [show ¬ depth > b.maxDepth by have := le.depth; omega, ↓reduceIte,
        StateT.run_bind, StateT.run_get, pure_bind]
      cases bumped : bump before.visits 1 a.maxExprVisits .exprVisits with
      | error error =>
        rw [bumped] at ran
        change Except.error _ = Except.ok out at ran
        cases ran
      | ok visits =>
        rw [bumped] at ran
        rw [bump_mono le.exprVisits bumped]
        change ((first.run { before with visits }) >>= fun (value, state) =>
          Except.ok (value, { state with ptrCache := state.ptrCache.insert (exprKey source) value })) =
            .ok out at ran
        obtain ⟨⟨value, middle⟩, bodyRan, finished⟩ := bind_eq_ok ran
        change ((second.run { before with visits }) >>= fun (value, state) =>
          Except.ok (value, { state with ptrCache := state.ptrCache.insert (exprKey source) value })) =
            .ok out
        rw [bind_ok_eq (body _ _ bodyRan)]
        exact finished

theorem ingestExpr_refines {a b : Limits} (le : LimitsLe a b) (context : ShareCtx) :
    ∀ (source : Ixon.Expr) (depth : Nat),
      Refines (ingestExpr a context depth source) (ingestExpr b context depth source) := by
  intro source
  induction source with
  | sort index =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ (internNode_refines le.nodes _)
  | var index =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ (internNode_refines le.nodes _)
  | ref index levels =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ (internNode_refines le.nodes _)
  | recur index levels =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ (internNode_refines le.nodes _)
  | prj index field value ih =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ ((ih (depth + 1)).bind fun _ => internNode_refines le.nodes _)
  | str index =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ (internNode_refines le.nodes _)
  | nat index =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ (internNode_refines le.nodes _)
  | app fn arg fnIh argIh =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ ((fnIh (depth + 1)).bind fun _ =>
      (argIh (depth + 1)).bind fun _ => internNode_refines le.nodes _)
  | lam contract type body typeIh bodyIh =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ ((typeIh (depth + 1)).bind fun _ =>
      (bodyIh (depth + 1)).bind fun _ => internNode_refines le.nodes _)
  | all contract result type body typeIh bodyIh =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ ((typeIh (depth + 1)).bind fun _ =>
      (bodyIh (depth + 1)).bind fun _ => internNode_refines le.nodes _)
  | letE contract type value body typeIh valueIh bodyIh =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ ((typeIh (depth + 1)).bind fun _ =>
      (valueIh (depth + 1)).bind fun _ => (bodyIh (depth + 1)).bind fun _ =>
        internNode_refines le.nodes _)
  | share index =>
    intro depth
    rw [ingestExpr_eq, ingestExpr_eq]
    exact cached_refines le depth _ (Refines.refl _)

theorem walk_refines {a b : Limits} (le : LimitsLe a b) (sources : Array Ixon.Expr)
    (ctxOf : Nat → Array Nat → ShareCtx) :
    ∀ count index acc, Refines (walk a sources ctxOf count index acc) (walk b sources ctxOf count index acc)
  | 0, _, _ => Refines.refl _
  | count + 1, index, acc =>
    (ingestExpr_refines le (ctxOf index acc) sources[index]! 0).bind fun id =>
      walk_refines le sources ctxOf count (index + 1) (acc.push id)

theorem ingestTable_refines {a b : Limits} (le : LimitsLe a b) (sharing roots : Array Ixon.Expr)
    (allowShare : Bool) :
    Refines (ingestTable a sharing roots allowShare) (ingestTable b sharing roots allowShare) := by
  rw [ingestTable_eq, ingestTable_eq]
  by_cases full : sharing.size ≥ wordBound
  · simp only [full, ↓reduceIte]
    exact Refines.refl _
  · simp only [full, ↓reduceIte]
    unfold tableBody
    simp only [arrayLoop_eq_walk]
    exact (walk_refines le _ _ _ _ _).bind fun _ =>
      (walk_refines le _ _ _ _ _).bind fun _ => Refines.refl _

/-- Expansion under larger limits returns the same expanded input. -/
theorem expand_mono {a b : Limits} (le : LimitsLe a b) {sharing roots : Array Ixon.Expr}
    {allowShare : Bool} {out : Expanded} (ran : expand a sharing roots allowShare = .ok out) :
    expand b sharing roots allowShare = .ok out := by
  unfold expand at ran ⊢
  obtain ⟨⟨⟨resolved, rootTemps⟩, st⟩, ingested, tail⟩ := bind_eq_ok ran
  rw [bind_ok_eq (ingestTable_refines le sharing roots allowShare {} _ ingested)]
  obtain ⟨⟨dag, ids⟩, numbered, finished⟩ := bind_eq_ok tail
  dsimp only
  rw [bind_ok_eq numbered]
  dsimp only at finished ⊢
  split at finished
  · change Except.error _ = Except.ok out at finished
    cases finished
  · rename_i shallow
    rw [ite_eq_right (any_gt_mono le.depth shallow)]
    exact finished

end Ix.Sharing.Verify.Budget

#guard_kernel_axioms Ix.Sharing.Verify.Budget.ingestExpr_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Sharing.Verify.Budget.expand_mono [propext, Classical.choice, Quot.sound]
