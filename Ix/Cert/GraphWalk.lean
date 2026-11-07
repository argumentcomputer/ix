module
public import Ix.GraphM
import all Ix.GraphM
import Std.Data.HashSet.Lemmas
import Std.Data.HashMap.Lemmas
import IxCK.Kernel.Ingress.Records

/-! # The reference graph's walk is exact

`Ix.graphExpr` walks a term into an accumulator `acc : Set Ix.Name` with a visited set of
already-walked expressions (`GraphState.visited : Std.HashSet ExprKey`), keyed by structural
equality (`Ix.Compile.ExactKey.ExprKey`). Under the invariant that every expression in `visited`
already has all of its references recorded in `acc` (`VisitedOK`), the references `Ix.graphExpr`
returns for a term from `GraphState.init` are exactly the names the term mentions (`Refs`: a
constant it applies, or a projection's structure), up to the names' hash (`graphExpr_refs`), and
`Ix.graphConst` returns a constant's terms' mentions with the names its kind adds. -/

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

/-- **The walk's visited set is sound for `acc`**: every visited expression has all of its
mentions already present in `acc`. -/
def MemoOK (s : GraphState) (acc : Ix.Set Ix.Name) : Prop :=
  ∀ (k : ExprKey), s.exprSeen.contains k = true → ∀ n, Refs n k.expr → acc.contains n = true

theorem memoOK_init (acc : Ix.Set Ix.Name) : MemoOK GraphState.init acc := fun k h => by
  change (∅ : Std.HashSet ExprKey).contains k = true at h
  rw [Std.HashSet.contains_empty] at h
  cases h

theorem memoOK_mono {s : GraphState} {acc acc' : Ix.Set Ix.Name} (hs : MemoOK s acc)
    (hsub : ∀ n, acc.contains n = true → acc'.contains n = true) : MemoOK s acc' :=
  fun k hk n hr => hsub n (hs k hk n hr)

theorem memoOK_insert {s : GraphState} {acc : Ix.Set Ix.Name} (hs : MemoOK s acc) {e : Ix.Expr}
    (he : ∀ n, Refs n e → acc.contains n = true) :
    MemoOK { s with exprSeen := s.exprSeen.insert ⟨e⟩ } acc := by
  intro k h n hr
  rw [Std.HashSet.contains_insert] at h
  rcases Bool.or_eq_true_iff.mp h with same | h
  · have e' : (⟨e⟩ : ExprKey) = k := beq_iff_eq.mp same
    subst e'
    exact he n hr
  · exact hs k h n hr

theorem bind_run {α β : Type} (x : GraphM α) (k : α → GraphM β) (env : Ix.Environment) (s : GraphState) :
    (x >>= k) env s = k (x env s).1 env (x env s).2 := rfl

theorem pure_run {α : Type} (x : α) (env : Ix.Environment) (s : GraphState) :
    (pure x : GraphM α) env s = (x, s) := rfl

/-- One step of the accumulator walk, from the visited set. -/
private theorem graphExprAcc_run (e : Ix.Expr) (acc : Ix.Set Ix.Name) (env : Ix.Environment) (s : GraphState) :
    graphExprAcc e acc env s = if s.exprSeen.contains ⟨e⟩ then (acc, s)
      else ((graphExprAcc.go e acc env s).1,
        { (graphExprAcc.go e acc env s).2 with
          exprSeen := (graphExprAcc.go e acc env s).2.exprSeen.insert ⟨e⟩ }) := by
  rw [graphExprAcc, bind_run]
  have hg : (get : GraphM GraphState) env s = (s, s) := rfl
  rw [hg]
  cases s.exprSeen.contains ⟨e⟩ <;> rfl

theorem contains_union_iff {a b : Ix.Set Ix.Name} {n : Ix.Name} :
    (a.union b).contains n = true ↔ a.contains n = true ∨ b.contains n = true := by
  change (a ∪ b).contains n = true ↔ _
  rw [Std.HashSet.contains_union, Bool.or_eq_true]

theorem contains_insert_iff {a : Ix.Set Ix.Name} {t n : Ix.Name} :
    (a.insert t).contains n = true ↔ (t == n) = true ∨ a.contains n = true := by
  rw [Std.HashSet.contains_insert, Bool.or_eq_true]

theorem not_contains_empty {n : Ix.Name} : ¬ (∅ : Ix.Set Ix.Name).contains n = true := by
  rw [Std.HashSet.contains_empty]
  simp

/-- **The accumulator walk adds a term's mentions**, from a sound visited set, and keeps it sound. -/
theorem graphExprAcc_refs : ∀ (e : Ix.Expr) (acc : Ix.Set Ix.Name) (env : Ix.Environment) (s : GraphState),
    MemoOK s acc →
    MemoOK (graphExprAcc e acc env s).2 (graphExprAcc e acc env s).1 ∧
      ∀ n, (graphExprAcc e acc env s).1.contains n = true ↔ acc.contains n = true ∨ Refs n e := by
  have node : ∀ (e : Ix.Expr) (acc : Ix.Set Ix.Name) (env : Ix.Environment) (s : GraphState), MemoOK s acc →
      (MemoOK (graphExprAcc.go e acc env s).2 (graphExprAcc.go e acc env s).1 ∧
        ∀ n, (graphExprAcc.go e acc env s).1.contains n = true ↔ acc.contains n = true ∨ Refs n e) →
      MemoOK (graphExprAcc e acc env s).2 (graphExprAcc e acc env s).1 ∧
        ∀ n, (graphExprAcc e acc env s).1.contains n = true ↔ acc.contains n = true ∨ Refs n e := by
    intro e acc env s hs ⟨hgs, hgr⟩
    rw [graphExprAcc_run]
    split
    · rename_i hseen
      refine ⟨hs, fun n => ⟨fun h => .inl h, fun h => ?_⟩⟩
      rcases h with h | hr
      · exact h
      · exact hs ⟨e⟩ hseen n hr
    · exact ⟨memoOK_insert hgs (fun n hr => (hgr n).mpr (.inr hr)), hgr⟩
  intro e
  induction e with
  | bvar _ _ | fvar _ _ | mvar _ _ | sort _ _ | lit _ _ =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go, pure_run]
    exact ⟨hs, fun n => ⟨fun h => .inl h, fun h => h.elim id fun hr => by cases hr⟩⟩
  | const m us h =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go, pure_run]
    refine ⟨memoOK_mono hs (fun n hn => contains_insert_iff.mpr (.inr hn)), fun n => ?_⟩
    show (acc.insert m).contains n = true ↔ _
    rw [contains_insert_iff]
    exact ⟨fun h => h.elim (.inr ∘ .const) .inl, fun h => h.elim .inr fun hr => by cases hr; exact .inl ‹_›⟩
  | app f a h ihf iha =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go, bind_run]
    obtain ⟨s1, r1⟩ := ihf acc env s hs
    obtain ⟨s2, r2⟩ := iha _ env _ s1
    refine ⟨s2, fun n => ?_⟩
    rw [r2, r1]
    exact ⟨fun h => h.elim (fun h => h.elim .inl (.inr ∘ .appF)) (.inr ∘ .appA),
      fun h => h.elim (.inl ∘ .inl) fun hr => by cases hr with
        | appF hf => exact .inl (.inr hf)
        | appA ha => exact .inr ha⟩
  | lam x t b bi h iht ihb =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go, bind_run]
    obtain ⟨s1, r1⟩ := iht acc env s hs
    obtain ⟨s2, r2⟩ := ihb _ env _ s1
    refine ⟨s2, fun n => ?_⟩
    rw [r2, r1]
    exact ⟨fun h => h.elim (fun h => h.elim .inl (.inr ∘ .lamT)) (.inr ∘ .lamB),
      fun h => h.elim (.inl ∘ .inl) fun hr => by cases hr with
        | lamT ht => exact .inl (.inr ht)
        | lamB hb => exact .inr hb⟩
  | forallE x t b bi h iht ihb =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go, bind_run]
    obtain ⟨s1, r1⟩ := iht acc env s hs
    obtain ⟨s2, r2⟩ := ihb _ env _ s1
    refine ⟨s2, fun n => ?_⟩
    rw [r2, r1]
    exact ⟨fun h => h.elim (fun h => h.elim .inl (.inr ∘ .allT)) (.inr ∘ .allB),
      fun h => h.elim (.inl ∘ .inl) fun hr => by cases hr with
        | allT ht => exact .inl (.inr ht)
        | allB hb => exact .inr hb⟩
  | letE x t v b nd h iht ihv ihb =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go, bind_run]
    obtain ⟨s1, r1⟩ := iht acc env s hs
    obtain ⟨s2, r2⟩ := ihv _ env _ s1
    obtain ⟨s3, r3⟩ := ihb _ env _ s2
    refine ⟨s3, fun n => ?_⟩
    rw [r3, r2, r1]
    exact ⟨fun h => h.elim (fun h => h.elim (fun h => h.elim .inl (.inr ∘ .letT)) (.inr ∘ .letV)) (.inr ∘ .letB),
      fun h => h.elim (.inl ∘ .inl ∘ .inl) fun hr => by cases hr with
        | letT ht => exact .inl (.inl (.inr ht))
        | letV hv => exact .inl (.inr hv)
        | letB hb => exact .inr hb⟩
  | mdata d e h ih =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go]
    obtain ⟨s1, r1⟩ := ih acc env s hs
    refine ⟨s1, fun n => (r1 n).trans ⟨fun h => h.elim .inl (.inr ∘ .mdata), fun h => ?_⟩⟩
    rcases h with h | hr
    · exact .inl h
    · cases hr; exact .inr ‹_›
  | proj t i s' h ih =>
    intro acc env s hs
    refine node _ acc env s hs ?_
    simp only [graphExprAcc.go, bind_run, pure_run]
    obtain ⟨s1, r1⟩ := ih acc env s hs
    have hins : MemoOK (graphExprAcc s' acc env s).2 ((graphExprAcc s' acc env s).1.insert t) :=
      memoOK_mono s1 (fun n hn => contains_insert_iff.mpr (.inr hn))
    refine ⟨hins, fun n => ?_⟩
    show ((graphExprAcc s' acc env s).1.insert t).contains n = true ↔ _
    rw [contains_insert_iff, r1]
    exact ⟨fun h => h.elim (.inr ∘ .projName) (fun h => h.elim .inl (.inr ∘ .projStruct)),
      fun h => h.elim (.inr ∘ .inl) fun hr => by cases hr with
        | projName ht => exact .inl ht
        | projStruct hs => exact .inr (.inr hs)⟩

/-- **The walk returns a term's mentions**, from the empty accumulator. -/
theorem graphExpr_refs (e : Ix.Expr) (env : Ix.Environment) (s : GraphState) (hs : MemoOK s ∅) :
    MemoOK (graphExpr e env s).2 (graphExpr e env s).1 ∧
      ∀ n, (graphExpr e env s).1.contains n = true ↔ Refs n e := by
  unfold graphExpr
  obtain ⟨s1, r1⟩ := graphExprAcc_refs e ∅ env s hs
  refine ⟨s1, fun n => (r1 n).trans ⟨fun h => h.elim (fun h => absurd h not_contains_empty) id, .inr⟩⟩

/-- Two terms walked in turn into one accumulator, from the empty visited set: the union of their mentions. -/
theorem union_init (a b : Ix.Expr) (env : Ix.Environment) (n : Ix.Name) :
    ((do let acc ← graphExprAcc a ∅; graphExprAcc b acc) env GraphState.init).1.contains n = true ↔
      Refs n a ∨ Refs n b := by
  rw [bind_run]
  obtain ⟨s1, r1⟩ := graphExprAcc_refs a ∅ env GraphState.init (memoOK_init ∅)
  obtain ⟨_, r2⟩ := graphExprAcc_refs b _ env _ s1
  rw [r2, r1]
  exact ⟨fun h => h.elim (fun h => h.elim (fun h => absurd h not_contains_empty) .inl) .inr,
    fun h => h.elim (.inl ∘ .inr) .inr⟩

/-! ## A constant's references -/

theorem graphConst_axiom (v : Ix.AxiomVal) (env : Ix.Environment) (n : Ix.Name) :
    (graphConst (.axiomInfo v) env GraphState.init).1.contains n = true ↔ Refs n v.cnst.type :=
  (graphExpr_refs v.cnst.type env GraphState.init (memoOK_init ∅)).2 n

theorem graphConst_quot (v : Ix.QuotVal) (env : Ix.Environment) (n : Ix.Name) :
    (graphConst (.quotInfo v) env GraphState.init).1.contains n = true ↔ Refs n v.cnst.type :=
  (graphExpr_refs v.cnst.type env GraphState.init (memoOK_init ∅)).2 n

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
  have ht := ((graphExpr_refs v.cnst.type env GraphState.init (memoOK_init ∅)).2 n).mpr hn
  exact contains_union_iff.mpr (.inl ht)

theorem graphConst_ctor (v : Ix.ConstructorVal) (env : Ix.Environment) {n : Ix.Name}
    (hn : Refs n v.cnst.type) : (graphConst (.ctorInfo v) env GraphState.init).1.contains n = true := by
  have ht := ((graphExpr_refs v.cnst.type env GraphState.init (memoOK_init ∅)).2 n).mpr hn
  exact contains_insert_iff.mpr (.inr ht)

/-- The recursor loop: from a sound visited set, the references it starts from stay, each rule's
constructor is added, and each rule's right-hand side's mentions join them, for a body that adds a
rule's constructor and walks its right-hand side into the accumulator. -/
theorem forIn_rules (f : Ix.RecursorRule → Ix.Set Ix.Name → GraphM (ForInStep (Ix.Set Ix.Name)))
    (hf : ∀ rule r env s, f rule r env s =
      (.yield (graphExprAcc rule.rhs (r.insert rule.ctor) env s).1,
        (graphExprAcc rule.rhs (r.insert rule.ctor) env s).2))
    (env : Ix.Environment) :
    ∀ (rules : List Ix.RecursorRule) (r0 : Ix.Set Ix.Name) (s : GraphState), MemoOK s r0 →
      (∀ n, r0.contains n = true → (forIn rules r0 f env s).1.contains n = true) ∧
        (∀ rule ∈ rules, (forIn rules r0 f env s).1.contains rule.ctor = true) ∧
        ∀ rule ∈ rules, ∀ n, Refs n rule.rhs → (forIn rules r0 f env s).1.contains n = true
  | [], r0, s, _ => ⟨fun _ h => h, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  | rule :: rules, r0, s, hs => by
    have hs' : MemoOK s (r0.insert rule.ctor) :=
      memoOK_mono hs (fun n hn => contains_insert_iff.mpr (.inr hn))
    obtain ⟨s1, r1⟩ := graphExprAcc_refs rule.rhs (r0.insert rule.ctor) env s hs'
    have step : forIn (rule :: rules) r0 f env s =
        forIn rules (graphExprAcc rule.rhs (r0.insert rule.ctor) env s).1 f env
          (graphExprAcc rule.rhs (r0.insert rule.ctor) env s).2 := by
      rw [List.forIn_cons, bind_run, hf]
    rw [step]
    obtain ⟨keep, ctors, rest⟩ := forIn_rules f hf env rules _ _ s1
    refine ⟨fun n h => keep n ((r1 n).mpr (.inl (contains_insert_iff.mpr (.inr h)))),
      fun rule' hr => ?_, fun rule' hr n hn => ?_⟩
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact keep _ ((r1 _).mpr (.inl (contains_insert_iff.mpr (.inl BEq.rfl))))
      · exact ctors rule' hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact keep n ((r1 n).mpr (.inr hn))
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
  obtain ⟨st, rt⟩ := graphExpr_refs v.cnst.type env GraphState.init (memoOK_init ∅)
  rw [graphConst, bind_run, bind_run, ← Array.forIn_toList]
  refine foldl_insert_keeps _ _ _ ?_
  obtain ⟨keep, -, rules⟩ := forIn_rules _ (fun _ _ _ _ => rfl) env v.rules.toList _ _ st
  rcases hn with hn | ⟨rule, hr, hn⟩
  · exact keep n ((rt n).mpr hn)
  · exact rules rule hr n hn

end Ix.Cert.GraphWalk

end
