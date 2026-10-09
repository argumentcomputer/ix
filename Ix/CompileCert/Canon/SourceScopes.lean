import Ix.CompileCert.Canon.Source
import Ix.CompileCert.Canon.ExpandWalkers
import Batteries.Tactic.OpenPrivate

open private Ix.Compile.Canon.liftLoose.go Ix.Compile.Canon.lowerLoose.go
  Ix.Compile.Canon.substLevels.go Ix.Compile.Canon.instantiatePiParams.go
  Ix.Compile.Canon.canonicalizeConstNames.go from Ix.Compile.Canon.Expr

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr ConstantInfo)

/-- Declaration lookup scope, separate from binder/universe/metadata spellings. -/
def RefScope (P : Name → Prop) (e : Expr) : Prop := ∀ n ∈ sourceExprRefs e, P n

@[simp] theorem refs_mkBVar (i : Nat) : sourceExprRefs (Expr.mkBVar i) = [] := rfl
@[simp] theorem refs_mkSort (u : Ix.Level) : sourceExprRefs (Expr.mkSort u) = [] := rfl
@[simp] theorem refs_mkConst (n : Name) (us : Array Ix.Level) :
    sourceExprRefs (Expr.mkConst n us) = [n] := rfl
@[simp] theorem refs_mkApp (f a : Expr) :
    sourceExprRefs (Expr.mkApp f a) = sourceExprRefs f ++ sourceExprRefs a := rfl
@[simp] theorem refs_mkLam (n : Name) (t b : Expr) (bi : Lean.BinderInfo) :
    sourceExprRefs (Expr.mkLam n t b bi) = sourceExprRefs t ++ sourceExprRefs b := rfl
@[simp] theorem refs_mkForallE (n : Name) (t b : Expr) (bi : Lean.BinderInfo) :
    sourceExprRefs (Expr.mkForallE n t b bi) = sourceExprRefs t ++ sourceExprRefs b := rfl
@[simp] theorem refs_mkLetE (n : Name) (t v b : Expr) (nd : Bool) :
    sourceExprRefs (Expr.mkLetE n t v b nd) = sourceExprRefs t ++ sourceExprRefs v ++ sourceExprRefs b := rfl
@[simp] theorem refs_mkProj (n : Name) (i : Nat) (e : Expr) :
    sourceExprRefs (Expr.mkProj n i e) = n :: sourceExprRefs e := rfl
@[simp] theorem refs_mkMData (md : Array (Name × Ix.DataValue)) (e : Expr) :
    sourceExprRefs (Expr.mkMData md e) = sourceExprRefs e := rfl

theorem RefScope.mono {P Q : Name → Prop} {e : Expr}
    (h : RefScope P e) (hp : ∀ n, P n → Q n) : RefScope Q e :=
  fun n hn => hp n (h n hn)

theorem ERen.sourceExprRefs {σ : Name → Name} {S : Name → Prop} {e e' : Expr}
    (h : ERen σ S e e') : sourceExprRefs e' = (sourceExprRefs e).map σ := by
  induction h <;> simp only [Ix.Compile.Canon.sourceExprRefs, List.map_append, List.map_cons, List.map_nil, *]

theorem refs_liftLoose (e : Expr) (n cutoff : Nat) :
    sourceExprRefs (Ix.Compile.Canon.liftLoose e n cutoff) = sourceExprRefs e := by
  unfold Ix.Compile.Canon.liftLoose
  split
  · rfl
  · induction e generalizing cutoff <;>
      simp only [Ix.Compile.Canon.liftLoose.go, sourceExprRefs,
        refs_mkApp, refs_mkLam, refs_mkForallE, refs_mkLetE, refs_mkProj, refs_mkMData, *]
    split <;> rfl

theorem RefScope.liftLoose {P : Name → Prop} {e : Expr} (h : RefScope P e)
    (n cutoff : Nat) : RefScope P (Ix.Compile.Canon.liftLoose e n cutoff) := by
  simpa only [RefScope, refs_liftLoose] using h

theorem refs_lowerLoose (e : Expr) (n cutoff : Nat) :
    sourceExprRefs (Ix.Compile.Canon.lowerLoose e n cutoff) = sourceExprRefs e := by
  unfold Ix.Compile.Canon.lowerLoose
  split
  · rfl
  · induction e generalizing cutoff <;>
      simp only [Ix.Compile.Canon.lowerLoose.go, sourceExprRefs,
        refs_mkApp, refs_mkLam, refs_mkForallE, refs_mkLetE, refs_mkProj, refs_mkMData, *]
    split <;> rfl

theorem RefScope.lowerLoose {P : Name → Prop} {e : Expr} (h : RefScope P e)
    (n cutoff : Nat) : RefScope P (Ix.Compile.Canon.lowerLoose e n cutoff) := by
  simpa only [RefScope, refs_lowerLoose] using h

theorem refs_substLevels (e : Expr) (params : Array Name) (us : Array Ix.Level) :
    sourceExprRefs (Ix.Compile.Canon.substLevels params us e) = sourceExprRefs e := by
  unfold Ix.Compile.Canon.substLevels
  split
  · rfl
  · induction e <;> simp only [Ix.Compile.Canon.substLevels.go, sourceExprRefs,
      refs_mkSort, refs_mkConst, refs_mkApp, refs_mkLam, refs_mkForallE,
      refs_mkLetE, refs_mkProj, refs_mkMData, *]

theorem RefScope.substLevels {P : Name → Prop} {e : Expr} (h : RefScope P e)
    (params : Array Name) (us : Array Ix.Level) :
    RefScope P (Ix.Compile.Canon.substLevels params us e) := by
  simpa only [RefScope, refs_substLevels] using h

theorem RefScope.instantiateRevAt {P : Name → Prop} {e : Expr} (h : RefScope P e)
    {args : Array Expr} (ha : ∀ a ∈ args, RefScope P a) (depth : Nat) :
    RefScope P (Ix.Compile.Canon.instantiateRevAt args e depth) := by
  induction e generalizing depth with
  | bvar i hash =>
    simp only [Ix.Compile.Canon.instantiateRevAt]
    split
    · split
      · exact (ha _ (Array.getElem_mem _)).liftLoose depth 0
      · simp [RefScope]
    · simp [RefScope]
  | _ =>
    simp_all [RefScope, sourceExprRefs, Ix.Compile.Canon.instantiateRevAt, or_imp, forall_and]
    all_goals solve_by_elim [And.intro]

theorem RefScope.instantiateRev {P : Name → Prop} {e : Expr} (h : RefScope P e)
    {args : Array Expr} (ha : ∀ a ∈ args, RefScope P a) :
    RefScope P (Ix.Compile.Canon.instantiateRev e args) := by
  unfold Ix.Compile.Canon.instantiateRev
  split
  · exact h
  · exact h.instantiateRevAt ha 0

theorem RefScope.instantiatePiParams {P : Name → Prop} {e : Expr} (h : RefScope P e)
    {args : Array Expr} (ha : ∀ a ∈ args, RefScope P a) (n : Nat) :
    RefScope P (Ix.Compile.Canon.instantiatePiParams e n args) := by
  unfold Ix.Compile.Canon.instantiatePiParams
  suffices main : ∀ as : List Expr, (∀ a ∈ as, RefScope P a) →
      ∀ e, RefScope P e → RefScope P (Ix.Compile.Canon.instantiatePiParams.go e as) by
    apply main _ _ _ h
    intro a hm
    exact ha a (by simpa using List.mem_of_mem_take hm)
  intro as
  induction as with
  | nil => intro _ e h; simpa [Ix.Compile.Canon.instantiatePiParams.go] using h
  | cons a as ih =>
    intro ha e he
    cases e <;> try simpa [Ix.Compile.Canon.instantiatePiParams.go] using he
    rename_i nm ty body bi hash
    apply ih
    · intro x hx; exact ha x (List.mem_cons_of_mem _ hx)
    · have hparts : RefScope P ty ∧ RefScope P body := by
        simpa [RefScope, sourceExprRefs, or_imp, forall_and] using he
      apply hparts.2.instantiateRev
      intro x hx
      have : x = a := by simpa using hx
      subst x
      exact ha a List.mem_cons_self

theorem RefScope.stripMdata {P : Name → Prop} {e : Expr} (h : RefScope P e) :
    RefScope P (Ix.Compile.Canon.stripMdata e) := by
  induction e <;> simp_all [Ix.Compile.Canon.stripMdata, RefScope, sourceExprRefs]

theorem RefScope.canonicalizeConstNames {P : Name → Prop} {e : Expr} (h : RefScope P e)
    (map : Std.HashMap Name Name)
    (hrange : ∀ n value, map.get? n = some value → P value) :
    RefScope P (Ix.Compile.Canon.canonicalizeConstNames map e) := by
  unfold Ix.Compile.Canon.canonicalizeConstNames
  split
  · exact h
  · induction e <;>
      simp_all [Ix.Compile.Canon.canonicalizeConstNames.go, RefScope, sourceExprRefs, or_imp, forall_and]
    split
    · simp only [refs_mkConst, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
      apply hrange; assumption
    · simpa only [sourceExprRefs, List.mem_cons, List.not_mem_nil, or_false, forall_eq] using h

theorem SourceReach.type_scope {source : Ix.Environment}
    {groups : Std.HashMap Name (Array (Array Name))} {seeds : List Name}
    {n : Name} {ci : ConstantInfo} (hr : SourceReach source groups seeds n)
    (hget : source.get? n = some ci) :
    RefScope (SourceReach source groups seeds) ci.getCnst.type := by
  intro name member
  apply SourceReach.edge hr hget
  unfold sourceEdges
  apply List.mem_append_left
  unfold sourceConstRefs
  exact List.mem_append_left _ member

end Ix.CompileCert.Canon
