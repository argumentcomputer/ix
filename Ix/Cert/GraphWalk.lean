module
public import Ix.GraphM
import all Ix.GraphM
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas
import IxC.Kernel.Ingress.Records

/-! # The reference graph's walk is exact

`Ix.graphExpr` walks a term with a memo of each expression's references, keyed exactly
(`Ix.Compile.ExactKey.ExprKey`). So the references it returns for a term are exactly the names
the term mentions (`Refs`: a constant it applies, or a projection's structure), up to the names'
hash (`graphExpr_refs`), and `Ix.graphConst` returns a constant's terms' mentions with the names
its kind adds. The memo holds only correct entries (`MemoOK`): an entry is inserted once its
expression's references are computed, and a hit returns the entry of an expression equal to the
one asked. -/

public section

namespace Ix.Cert.GraphWalk

open Ix.Compile.ExactKey (ExprKey)

private theorem name_beq_iff {a b : Ix.Name} : (a == b) = true ↔ a.getHash = b.getHash :=
  Address.beq_iff_eq

/-- `Ix.Name`'s `==` compares the stored hashes: an equivalence, which `hash` respects. -/
local instance : EquivBEq Ix.Name where
  rfl := name_beq_iff.mpr rfl
  symm h := name_beq_iff.mpr (name_beq_iff.mp h).symm
  trans h₁ h₂ := name_beq_iff.mpr ((name_beq_iff.mp h₁).trans (name_beq_iff.mp h₂))

local instance : LawfulHashable Ix.Name where
  hash_eq a b h := by
    show hash a.getHash = hash b.getHash
    rw [name_beq_iff.mp h]

/-- **`n` is mentioned by the term**: a constant it applies, or a projection's structure, up to
the names' hash. -/
inductive Refs (n : Ix.Name) : Ix.Expr → Prop
  | const {m : Ix.Name} {us : Array Ix.Level} {h : Address} : (m == n) = true → Refs n (.const m us h)
  | projName {t : Ix.Name} {i : Nat} {s : Ix.Expr} {h : Address} : (t == n) = true → Refs n (.proj t i s h)
  | projStruct {t : Ix.Name} {i : Nat} {s : Ix.Expr} {h : Address} : Refs n s → Refs n (.proj t i s h)
  | appF {f a : Ix.Expr} {h : Address} : Refs n f → Refs n (.app f a h)
  | appA {f a : Ix.Expr} {h : Address} : Refs n a → Refs n (.app f a h)
  | lamT {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} : Refs n t → Refs n (.lam x t b bi h)
  | lamB {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} : Refs n b → Refs n (.lam x t b bi h)
  | allT {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      Refs n t → Refs n (.forallE x t b bi h)
  | allB {x : Ix.Name} {t b : Ix.Expr} {bi : Lean.BinderInfo} {h : Address} :
      Refs n b → Refs n (.forallE x t b bi h)
  | letT {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : Refs n t → Refs n (.letE x t v b nd h)
  | letV {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : Refs n v → Refs n (.letE x t v b nd h)
  | letB {x : Ix.Name} {t v b : Ix.Expr} {nd : Bool} {h : Address} : Refs n b → Refs n (.letE x t v b nd h)
  | mdata {d : Array (Ix.Name × Ix.DataValue)} {e : Ix.Expr} {h : Address} : Refs n e → Refs n (.mdata d e h)

/-- **The walk's memo is correct**: every entry holds exactly its expression's mentions. -/
def MemoOK (s : GraphState) : Prop :=
  ∀ (k : ExprKey) (v : Ix.Set Ix.Name), s.exprCache.get? k = some v → ∀ n, v.contains n = true ↔ Refs n k.expr

theorem memoOK_init : MemoOK GraphState.init := fun k v h => by
  change (∅ : Std.HashMap ExprKey (Ix.Set Ix.Name)).get? k = some v at h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h
  cases h

theorem memoOK_insert {s : GraphState} (hs : MemoOK s) {e : Ix.Expr} {v : Ix.Set Ix.Name}
    (hv : ∀ n, v.contains n = true ↔ Refs n e) :
    MemoOK { s with exprCache := s.exprCache.insert ⟨e⟩ v } := by
  intro k w h n
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i same
    cases h
    have e' : (⟨e⟩ : ExprKey) = k := beq_iff_eq.mp same
    subst e'
    exact hv n
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    exact hs k w h n

theorem bind_run {α β : Type} (x : GraphM α) (k : α → GraphM β) (env : Ix.Environment) (s : GraphState) :
    (x >>= k) env s = k (x env s).1 env (x env s).2 := rfl

/-- One step of the walk, from the memo. -/
private theorem graphExpr_run (e : Ix.Expr) (env : Ix.Environment) (s : GraphState) :
    graphExpr e env s = match s.exprCache.get? ⟨e⟩ with
      | some x => (x, s)
      | none => ((graphExpr.go e env s).1,
          { (graphExpr.go e env s).2 with
            exprCache := (graphExpr.go e env s).2.exprCache.insert ⟨e⟩ (graphExpr.go e env s).1 }) := by
  rw [graphExpr, bind_run]
  have hg : (get : GraphM GraphState) env s = (s, s) := rfl
  rw [hg]
  cases s.exprCache.get? ⟨e⟩ <;> rfl

theorem map_run (g : GraphM (Ix.Set Ix.Name)) (t : Ix.Name) (env : Ix.Environment) (s : GraphState) :
    ((fun r => Std.HashSet.insert r t) <$> g) env s = ((g env s).1.insert t, (g env s).2) := rfl

theorem union_run (g h : GraphM (Ix.Set Ix.Name)) (env : Ix.Environment) (s : GraphState) :
    (Std.HashSet.union <$> g <*> h) env s =
      ((g env s).1.union (h env (g env s).2).1, (h env (g env s).2).2) := rfl

theorem contains_union_iff {a b : Ix.Set Ix.Name} {n : Ix.Name} :
    (a.union b).contains n = true ↔ a.contains n = true ∨ b.contains n = true := by
  change (a ∪ b).contains n = true ↔ _
  rw [Std.HashSet.contains_union, Bool.or_eq_true]

theorem contains_insert_iff {a : Ix.Set Ix.Name} {t n : Ix.Name} :
    (a.insert t).contains n = true ↔ (t == n) = true ∨ a.contains n = true := by
  rw [Std.HashSet.contains_insert, Bool.or_eq_true]

theorem contains_singleton_iff {t n : Ix.Name} : ({t} : Ix.Set Ix.Name).contains n = true ↔ (t == n) = true := by
  change ((∅ : Ix.Set Ix.Name).insert t).contains n = true ↔ _
  rw [contains_insert_iff, Std.HashSet.contains_empty]
  simp

theorem not_contains_empty {n : Ix.Name} : ¬ (∅ : Ix.Set Ix.Name).contains n = true := by
  rw [Std.HashSet.contains_empty]
  simp

/-- **The walk returns a term's mentions**, from a correct memo, and keeps the memo correct. -/
theorem graphExpr_refs : ∀ (e : Ix.Expr) (env : Ix.Environment) (s : GraphState), MemoOK s →
    MemoOK (graphExpr e env s).2 ∧ ∀ n, (graphExpr e env s).1.contains n = true ↔ Refs n e := by
  -- a node whose own step is correct, given its memo's correctness after the step
  have node : ∀ (e : Ix.Expr) (env : Ix.Environment) (s : GraphState), MemoOK s →
      (MemoOK (graphExpr.go e env s).2 ∧ ∀ n, (graphExpr.go e env s).1.contains n = true ↔ Refs n e) →
      MemoOK (graphExpr e env s).2 ∧ ∀ n, (graphExpr e env s).1.contains n = true ↔ Refs n e := by
    intro e env s hs ⟨hgs, hgr⟩
    rw [graphExpr_run]
    split
    · rename_i x hx
      exact ⟨hs, hs ⟨e⟩ x hx⟩
    · exact ⟨memoOK_insert hgs hgr, hgr⟩
  intro e
  induction e with
  | bvar _ _ | fvar _ _ | mvar _ _ | sort _ _ | lit _ _ =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go]
    exact ⟨hs, fun n => ⟨fun h => absurd h not_contains_empty, fun h => by cases h⟩⟩
  | const m us h =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go]
    refine ⟨hs, fun n => ?_⟩
    show ({m} : Ix.Set Ix.Name).contains n = true ↔ _
    rw [contains_singleton_iff]
    exact ⟨fun h => .const h, fun h => by cases h; assumption⟩
  | app f a h ihf iha =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go, union_run]
    obtain ⟨s1, r1⟩ := ihf env s hs
    obtain ⟨s2, r2⟩ := iha env _ s1
    refine ⟨s2, fun n => ?_⟩
    rw [contains_union_iff, r1, r2]
    exact ⟨fun h => h.elim .appF .appA, fun h => by cases h <;> simp_all⟩
  | lam x t b bi h iht ihb =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go, union_run]
    obtain ⟨s1, r1⟩ := iht env s hs
    obtain ⟨s2, r2⟩ := ihb env _ s1
    refine ⟨s2, fun n => ?_⟩
    rw [contains_union_iff, r1, r2]
    exact ⟨fun h => h.elim .lamT .lamB, fun h => by cases h <;> simp_all⟩
  | forallE x t b bi h iht ihb =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go, union_run]
    obtain ⟨s1, r1⟩ := iht env s hs
    obtain ⟨s2, r2⟩ := ihb env _ s1
    refine ⟨s2, fun n => ?_⟩
    rw [contains_union_iff, r1, r2]
    exact ⟨fun h => h.elim .allT .allB, fun h => by cases h <;> simp_all⟩
  | letE x t v b nd h iht ihv ihb =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go, union_run]
    obtain ⟨s1, r1⟩ := iht env s hs
    obtain ⟨s2, r2⟩ := ihv env _ s1
    obtain ⟨s3, r3⟩ := ihb env _ s2
    refine ⟨s3, fun n => ?_⟩
    rw [contains_union_iff, r1, contains_union_iff, r2, r3]
    exact ⟨fun h => h.elim .letT (fun h => h.elim .letV .letB), fun h => by cases h <;> simp_all⟩
  | mdata d e h ih =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go]
    obtain ⟨s1, r1⟩ := ih env s hs
    exact ⟨s1, fun n => (r1 n).trans ⟨.mdata, fun h => by cases h; assumption⟩⟩
  | proj t i s' h ih =>
    intro env s hs
    refine node _ env s hs ?_
    simp only [graphExpr.go, map_run]
    obtain ⟨s1, r1⟩ := ih env s hs
    refine ⟨s1, fun n => ?_⟩
    rw [contains_insert_iff, r1]
    exact ⟨fun h => h.elim .projName .projStruct, fun h => by cases h <;> simp_all⟩

/-- Two terms walked in turn, from the empty memo: the union of their mentions. -/
theorem union_init (a b : Ix.Expr) (env : Ix.Environment) (n : Ix.Name) :
    ((Std.HashSet.union <$> graphExpr a <*> graphExpr b) env GraphState.init).1.contains n = true ↔
      Refs n a ∨ Refs n b := by
  rw [union_run, contains_union_iff]
  obtain ⟨s1, r1⟩ := graphExpr_refs a env GraphState.init memoOK_init
  rw [r1, (graphExpr_refs b _ _ s1).2]

/-! ## A constant's references -/

theorem graphConst_axiom (v : Ix.AxiomVal) (env : Ix.Environment) (n : Ix.Name) :
    (graphConst (.axiomInfo v) env GraphState.init).1.contains n = true ↔ Refs n v.cnst.type :=
  (graphExpr_refs v.cnst.type env GraphState.init memoOK_init).2 n

theorem graphConst_quot (v : Ix.QuotVal) (env : Ix.Environment) (n : Ix.Name) :
    (graphConst (.quotInfo v) env GraphState.init).1.contains n = true ↔ Refs n v.cnst.type :=
  (graphExpr_refs v.cnst.type env GraphState.init memoOK_init).2 n

theorem graphConst_defn (v : Ix.DefinitionVal) (env : Ix.Environment) (n : Ix.Name) :
    (graphConst (.defnInfo v) env GraphState.init).1.contains n = true ↔
      Refs n v.cnst.type ∨ Refs n v.value :=
  union_init v.cnst.type v.value env n

theorem graphConst_thm (v : Ix.TheoremVal) (env : Ix.Environment) (n : Ix.Name) :
    (graphConst (.thmInfo v) env GraphState.init).1.contains n = true ↔
      Refs n v.cnst.type ∨ Refs n v.value :=
  union_init v.cnst.type v.value env n

theorem graphConst_opaque (v : Ix.OpaqueVal) (env : Ix.Environment) (n : Ix.Name) :
    (graphConst (.opaqueInfo v) env GraphState.init).1.contains n = true ↔
      Refs n v.cnst.type ∨ Refs n v.value :=
  union_init v.cnst.type v.value env n

theorem graphConst_induct (v : Ix.InductiveVal) (env : Ix.Environment) {n : Ix.Name}
    (hn : Refs n v.cnst.type) : (graphConst (.inductInfo v) env GraphState.init).1.contains n = true := by
  have ht := ((graphExpr_refs v.cnst.type env GraphState.init memoOK_init).2 n).mpr hn
  exact contains_union_iff.mpr (.inl ht)

theorem graphConst_ctor (v : Ix.ConstructorVal) (env : Ix.Environment) {n : Ix.Name}
    (hn : Refs n v.cnst.type) : (graphConst (.ctorInfo v) env GraphState.init).1.contains n = true := by
  have ht := ((graphExpr_refs v.cnst.type env GraphState.init memoOK_init).2 n).mpr hn
  exact contains_insert_iff.mpr (.inr ht)

/-- The recursor loop: from a correct memo, the references it starts from stay and each rule's
right-hand side's mentions join them, for a body that adds a rule's constructor and walks its
right-hand side. -/
theorem forIn_rules (f : Ix.RecursorRule → Ix.Set Ix.Name → GraphM (ForInStep (Ix.Set Ix.Name)))
    (hf : ∀ rule r env s, f rule r env s =
      (.yield ((r.insert rule.ctor).union (graphExpr rule.rhs env s).1), (graphExpr rule.rhs env s).2))
    (env : Ix.Environment) :
    ∀ (rules : List Ix.RecursorRule) (r0 : Ix.Set Ix.Name) (s : GraphState), MemoOK s →
      (∀ n, r0.contains n = true → (forIn rules r0 f env s).1.contains n = true) ∧
        ∀ rule ∈ rules, ∀ n, Refs n rule.rhs → (forIn rules r0 f env s).1.contains n = true
  | [], r0, s, _ => ⟨fun _ h => h, fun _ h => nomatch h⟩
  | rule :: rules, r0, s, hs => by
    obtain ⟨s1, r1⟩ := graphExpr_refs rule.rhs env s hs
    have step : forIn (rule :: rules) r0 f env s =
        forIn rules ((r0.insert rule.ctor).union (graphExpr rule.rhs env s).1) f env
          (graphExpr rule.rhs env s).2 := by
      rw [List.forIn_cons, bind_run, hf]
    rw [step]
    obtain ⟨keep, rest⟩ := forIn_rules f hf env rules _ _ s1
    refine ⟨fun n h => keep n (contains_union_iff.mpr (.inl (contains_insert_iff.mpr (.inr h)))),
      fun rule' hr n hn => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · exact keep n (contains_union_iff.mpr (.inr ((r1 n).mpr hn)))
    · exact rest rule' hr n hn

/-- Inserting names keeps the names held. -/
theorem foldl_insert_keeps (rs : Ix.Set Ix.Name) (p : Ix.Name → Bool) (l : Array Ix.Name) {n : Ix.Name}
    (h : rs.contains n = true) :
    (l.foldl (fun s r => if p r then s.insert r else s) rs).contains n = true := by
  rw [← Array.foldl_toList]
  induction l.toList generalizing rs with
  | nil => exact h
  | cons x xs ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    split
    · exact contains_insert_iff.mpr (.inr h)
    · exact h

theorem graphConst_rec (v : Ix.RecursorVal) (env : Ix.Environment) {n : Ix.Name}
    (hn : Refs n v.cnst.type ∨ ∃ rule ∈ v.rules.toList, Refs n rule.rhs) :
    (graphConst (.recInfo v) env GraphState.init).1.contains n = true := by
  obtain ⟨st, rt⟩ := graphExpr_refs v.cnst.type env GraphState.init memoOK_init
  rw [graphConst, bind_run, bind_run, ← Array.forIn_toList]
  refine foldl_insert_keeps _ _ _ ?_
  obtain ⟨keep, rules⟩ := forIn_rules _ (fun _ _ _ _ => rfl) env v.rules.toList _ _ st
  rcases hn with hn | ⟨rule, hr, hn⟩
  · exact keep n ((rt n).mpr hn)
  · exact rules rule hr n hn

end Ix.Cert.GraphWalk

end
