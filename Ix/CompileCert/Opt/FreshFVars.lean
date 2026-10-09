import Ix.AuxGen.ExprUtils
import Ix.Environment
import Ix.Compile.Canon.OccurrenceKey
import Std.Data.HashSet.Lemmas

/-!
Structural collection and deterministic freshness for the actual F-1 supply.
This proof leaf is uncompiled. It imports no proof aggregator and adds no
closed-input, caller-freshness, cached-name or hash-injectivity premise.
-/

namespace Ix.CompileCert.Opt.FreshFVarsProof

open Ix (Name Expr)
open Ix.AuxGen (FreshFVars freshFVar)
open Ix.Compile.Canon (keyName)

/-- Structural occurrence in precisely the term positions abstraction visits. -/
def Occurs (key : Lean.Name) : Expr → Prop
  | .fvar name _ => keyName name = key
  | .app f a _ => Occurs key f ∨ Occurs key a
  | .lam _ ty body _ _ | .forallE _ ty body _ _ => Occurs key ty ∨ Occurs key body
  | .letE _ ty value body _ _ => (Occurs key ty ∨ Occurs key value) ∨ Occurs key body
  | .proj _ _ body _ | .mdata _ body _ => Occurs key body
  | _ => False

/-- The actual reserve operation uses complete structural name keys. -/
theorem reserve_mem (s : FreshFVars) (name : Name) (key : Lean.Name) :
    key ∈ (s.reserve name).used ↔ keyName name = key ∨ key ∈ s.used := by
  simp [FreshFVars.reserve]

/-- Exact collection, including old protection; no closed-expression premise. -/
theorem protectExpr_mem (e : Expr) (s : FreshFVars) (key : Lean.Name) :
    key ∈ (s.protectExpr e).used ↔ key ∈ s.used ∨ Occurs key e := by
  induction e generalizing s with
  | app f a hash ihf iha =>
      simp only [FreshFVars.protectExpr, iha, ihf, Occurs, or_assoc]
  | lam name ty body info hash iht ihb =>
      simp only [FreshFVars.protectExpr, ihb, iht, Occurs, or_assoc]
  | forallE name ty body info hash iht ihb =>
      simp only [FreshFVars.protectExpr, ihb, iht, Occurs, or_assoc]
  | letE name ty value body nd hash iht ihv ihb =>
      simp only [FreshFVars.protectExpr, ihb, ihv, iht, Occurs, or_assoc]
  | proj name index body hash ih =>
      exact ih s
  | mdata data body hash ih =>
      exact ih s
  | fvar name hash =>
      simpa only [FreshFVars.protectExpr, reserve_mem, Occurs, or_comm]
  | _ => simp only [FreshFVars.protectExpr, Occurs, or_false]

private theorem protectList_mem (es : List Expr) (s : FreshFVars) (key : Lean.Name) :
    key ∈ (es.foldl FreshFVars.protectExpr s).used ↔
      key ∈ s.used ∨ ∃ e ∈ es, Occurs key e := by
  induction es generalizing s with
  | nil => simp
  | cons e es ih =>
      simp only [List.foldl_cons, ih, protectExpr_mem, List.mem_cons]
      constructor
      · rintro ((old | here) | ⟨x, hx, occurs⟩)
        · exact .inl old
        · exact .inr ⟨e, .inl rfl, here⟩
        · exact .inr ⟨x, .inr hx, occurs⟩
      · rintro (old | ⟨x, hx, occurs⟩)
        · exact .inl (.inl old)
        · rcases hx with rfl | hx
          · exact .inl (.inr occurs)
          · exact .inr ⟨x, hx, occurs⟩

theorem protectExprs_mem (es : Array Expr) (s : FreshFVars) (key : Lean.Name) :
    key ∈ (s.protectExprs es).used ↔
      key ∈ s.used ∨ ∃ e ∈ es.toList, Occurs key e := by
  unfold FreshFVars.protectExprs
  rw [← Array.foldl_toList]
  exact protectList_mem es.toList s key

theorem protectExpr_grows (s : FreshFVars) (e : Expr) (key : Lean.Name)
    (member : key ∈ s.used) : key ∈ (s.protectExpr e).used :=
  (protectExpr_mem e s key).2 (.inl member)

theorem protectExpr_covers (s : FreshFVars) (e : Expr) (key : Lean.Name)
    (occurs : Occurs key e) : key ∈ (s.protectExpr e).used :=
  (protectExpr_mem e s key).2 (.inr occurs)

/-- The numeric fold in the actual allocator, exposed only for its proof. -/
def suffixStep (key : Lean.Name) (next : Nat) (name : Lean.Name) : Nat :=
  match name with
  | .num parent n => if parent == key then max next (n + 1) else next
  | _ => next

def nextSuffix (s : FreshFVars) (key : Lean.Name) : Nat :=
  s.used.fold (suffixStep key) 0

private theorem suffixStep_ge (key name : Lean.Name) (next : Nat) :
    next ≤ suffixStep key next name := by
  cases name with
  | anonymous => exact Nat.le_refl _
  | str parent text => exact Nat.le_refl _
  | num parent n =>
      unfold suffixStep
      split
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _

private theorem suffixFold_ge (names : List Lean.Name) (key : Lean.Name) (init : Nat) :
    init ≤ names.foldl (suffixStep key) init := by
  induction names generalizing init with
  | nil => exact Nat.le_refl _
  | cons name names ih =>
      exact Nat.le_trans (suffixStep_ge key name init) (ih _)

private theorem suffixFold_member (names : List Lean.Name) (key : Lean.Name)
    (init n : Nat) (member : Lean.Name.num key n ∈ names) :
    n < names.foldl (suffixStep key) init := by
  induction names generalizing init with
  | nil => cases member
  | cons name names ih =>
      rcases List.mem_cons.1 member with equal | member
      · subst name
        have lower : n + 1 ≤ suffixStep key init (.num key n) := by
          simp only [suffixStep, beq_self_eq_true, ↓reduceIte]
          exact Nat.le_max_right _ _
        exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) lower)
          (suffixFold_ge names key _)
      · exact ih _ member

/-- A protected numeric child is strictly below the chosen suffix. -/
theorem nextSuffix_above (s : FreshFVars) (key : Lean.Name) (n : Nat)
    (member : Lean.Name.num key n ∈ s.used) : n < nextSuffix s key := by
  unfold nextSuffix
  rw [Std.HashSet.fold_eq_foldl_toList]
  exact suffixFold_member s.used.toList key 0 n (Std.HashSet.mem_toList.2 member)

theorem nextSuffix_fresh (s : FreshFVars) (key : Lean.Name) :
    Lean.Name.num key (nextSuffix s key) ∉ s.used := by
  intro member
  exact Nat.lt_irrefl _ (nextSuffix_above s key _ member)

private theorem suffixFold_le (names : List Lean.Name) (key : Lean.Name)
    (init bound : Nat) (initial : init ≤ bound)
    (upper : ∀ n, Lean.Name.num key n ∈ names → n < bound) :
    names.foldl (suffixStep key) init ≤ bound := by
  induction names generalizing init with
  | nil => exact initial
  | cons name names ih =>
      apply ih
      · cases name with
        | anonymous => exact initial
        | str parent text => exact initial
        | num parent n =>
            by_cases equal : parent = key
            · subst parent
              simp only [suffixStep, beq_self_eq_true, ↓reduceIte]
              exact Nat.max_le.mpr ⟨initial, upper n (by simp)⟩
            · simpa [suffixStep, equal] using initial
      · intro n member
        exact upper n (List.mem_cons_of_mem _ member)

theorem nextSuffix_le (s : FreshFVars) (key : Lean.Name) (bound : Nat)
    (upper : ∀ n, Lean.Name.num key n ∈ s.used → n < bound) :
    nextSuffix s key ≤ bound := by
  unfold nextSuffix
  rw [Std.HashSet.fold_eq_foldl_toList]
  exact suffixFold_le s.used.toList key 0 bound (Nat.zero_le _) fun n member =>
    upper n (Std.HashSet.mem_toList.1 member)

/-- The allocator's result is independent of hash-set iteration order. -/
theorem nextSuffix_eq_of_membership (s t : FreshFVars) (key : Lean.Name)
    (same : ∀ name, name ∈ s.used ↔ name ∈ t.used) :
    nextSuffix s key = nextSuffix t key := by
  apply Nat.le_antisymm
  · exact nextSuffix_le s key _ fun n member =>
      nextSuffix_above t key n ((same _).1 member)
  · exact nextSuffix_le t key _ fun n member =>
      nextSuffix_above s key n ((same _).2 member)

/-- The smart constructor's semantic key ignores all cached fields. -/
theorem keyName_mkNat (parent : Name) (n : Nat) :
    keyName (Name.mkNat parent n) = Lean.Name.num (keyName parent) n := by
  rfl

/-- Keep the preferred spelling and complete output/state when unused. -/
theorem fresh_of_unused (s : FreshFVars) (pfx : String) (idx : Nat)
    (unused : keyName (freshFVar pfx idx).1 ∉ s.used) :
    s.fresh pfx idx = (freshFVar pfx idx, s.reserve (freshFVar pfx idx).1) := by
  have absent := Std.HashSet.contains_eq_false_iff_not_mem.2 unused
  simpa only [FreshFVars.fresh, absent, Bool.false_eq_true, ↓reduceIte, freshFVar]

/-- Collision branch, including the exact resulting supply. -/
theorem fresh_of_used (s : FreshFVars) (pfx : String) (idx : Nat)
    (used : keyName (freshFVar pfx idx).1 ∈ s.used) :
    s.fresh pfx idx =
      let name := Name.mkNat (freshFVar pfx idx).1
        (nextSuffix s (keyName (freshFVar pfx idx).1))
      ((name, Expr.mkFVar name), s.reserve name) := by
  have present := Std.HashSet.mem_iff_contains.1 used
  simpa only [FreshFVars.fresh, present, ↓reduceIte, nextSuffix, suffixStep]

/-- No input invariant is required: every allocator output is fresh. -/
theorem fresh_not_mem (s : FreshFVars) (pfx : String) (idx : Nat) :
    keyName (s.fresh pfx idx).1.1 ∉ s.used := by
  by_cases used : keyName (freshFVar pfx idx).1 ∈ s.used
  · rw [fresh_of_used s pfx idx used]
    simpa only [keyName_mkNat] using nextSuffix_fresh s (keyName (freshFVar pfx idx).1)
  · simpa only [fresh_of_unused s pfx idx used] using used

theorem fresh_reserved (s : FreshFVars) (pfx : String) (idx : Nat) :
    keyName (s.fresh pfx idx).1.1 ∈ (s.fresh pfx idx).2.used := by
  unfold FreshFVars.fresh
  simp only [FreshFVars.reserve, Std.HashSet.mem_insert_self]

theorem fresh_grows (s : FreshFVars) (pfx : String) (idx : Nat) (key : Lean.Name)
    (member : key ∈ s.used) : key ∈ (s.fresh pfx idx).2.used := by
  unfold FreshFVars.fresh
  exact (reserve_mem s _ key).2 (.inr member)

theorem fresh_distinct (s : FreshFVars) (pfx qfx : String) (idx jdx : Nat) :
    keyName ((s.fresh pfx idx).2.fresh qfx jdx).1.1 ≠ keyName (s.fresh pfx idx).1.1 := by
  intro equal
  exact fresh_not_mem (s.fresh pfx idx).2 qfx jdx (equal.symm ▸ fresh_reserved s pfx idx)

/-- The producer derives freshness from the actual input expression. -/
theorem fresh_avoids_expr (s : FreshFVars) (e : Expr) (pfx : String) (idx : Nat) :
    ¬ Occurs (keyName ((s.protectExpr e).fresh pfx idx).1.1) e := by
  intro occurs
  exact fresh_not_mem (s.protectExpr e) pfx idx
    (protectExpr_covers s e _ occurs)

theorem fresh_avoids_exprs (s : FreshFVars) (es : Array Expr) (e : Expr)
    (member : e ∈ es.toList) (pfx : String) (idx : Nat) :
    ¬ Occurs (keyName ((s.protectExprs es).fresh pfx idx).1.1) e := by
  intro occurs
  exact fresh_not_mem (s.protectExprs es) pfx idx
    ((protectExprs_mem es s _).2 (.inr ⟨e, member, occurs⟩))

/-- Extensional protection yields the same raw chosen name and FVar. -/
theorem fresh_result_eq_of_membership (s t : FreshFVars) (pfx : String) (idx : Nat)
    (same : ∀ name, name ∈ s.used ↔ name ∈ t.used) :
    (s.fresh pfx idx).1 = (t.fresh pfx idx).1 := by
  by_cases used : keyName (freshFVar pfx idx).1 ∈ s.used
  · rw [fresh_of_used s pfx idx used, fresh_of_used t pfx idx ((same _).1 used)]
    rw [nextSuffix_eq_of_membership s t _ same]
  · have other : keyName (freshFVar pfx idx).1 ∉ t.used := fun member => used ((same _).2 member)
    rw [fresh_of_unused s pfx idx used, fresh_of_unused t pfx idx other]

/-- The actual state operation is the proved allocator, with its whole state. -/
theorem freshFVarM_run_eq (s : FreshFVars) (pfx : String) (idx : Nat) :
    Ix.AuxGen.freshFVarM pfx idx s = s.fresh pfx idx := rfl

/-- Protection followed by the actual state operation derives its own
freshness and preserves all earlier protection, for every raw input. -/
theorem freshFVarM_protected_spec (s : FreshFVars) (e : Expr)
    (pfx : String) (idx : Nat) :
    let run := Ix.AuxGen.freshFVarM pfx idx (s.protectExpr e)
    (¬ Occurs (keyName run.1.1) e) ∧
      keyName run.1.1 ∈ run.2.used ∧
      ∀ key, key ∈ s.used → key ∈ run.2.used := by
  dsimp only [Ix.AuxGen.freshFVarM]
  exact ⟨fresh_avoids_expr s e pfx idx,
    fresh_reserved (s.protectExpr e) pfx idx,
    fun key member => fresh_grows (s.protectExpr e) pfx idx key
      (protectExpr_grows s e key member)⟩

end Ix.CompileCert.Opt.FreshFVarsProof
