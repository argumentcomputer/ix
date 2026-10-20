module

public import IxC.Kernel.Verify.Rename.Basic

@[expose] public section

/-!
# Renaming commutes with the expression operations

Every syntactic operation of `IxC/Kernel/ExprOps.lean` and
`IxC/Kernel/Level.lean` treats a key as an opaque leaf, so renaming the keys
commutes with it unconditionally: a transformation of the renamed term is
the renamed transformation (`mapKeys_instantiate1`, …), a query of the
renamed term is the query (`looseBVarsBounded_mapKeys`, …), and a
transformation of good terms is good (`Good.instantiate1`, …).

Orientation: the transformations' equations push `mapKeys` inwards (the
normal form has the renaming at the leaves of the original run's values);
the queries' equations drop it.
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel.Expr

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

/-! ## Shape -/

@[simp] theorem mapKeys_eq_bvar_iff {e : Expr md} {i : Nat} :
    e.mapKeys f = .bvar i ↔ e = .bvar i := by
  cases e <;> simp

@[simp] theorem mapKeys_eq_sort_iff {e : Expr md} {u : Level} :
    e.mapKeys f = .sort u ↔ e = .sort u := by
  cases e <;> simp

@[simp] theorem mapKeys_eq_lit_iff {e : Expr md} {l : Literal} :
    e.mapKeys f = .lit l ↔ e = .lit l := by
  cases e <;> simp

/-! ## Transformations -/

@[simp] theorem mapKeys_instantiate1 (e v : Expr md) (d : Nat) :
    (e.instantiate1 v d).mapKeys f = (e.mapKeys f).instantiate1 (v.mapKeys f) d := by
  induction e generalizing d with
  | bvar i =>
    by_cases h₁ : i = d
    · simp [instantiate1, h₁]
    · by_cases h₂ : i > d <;> simp [instantiate1, h₁, h₂]
  | _ => simp_all [instantiate1]

private theorem mapKeys_instantiateList_step (vs : List (Expr md))
    (ih : ∀ (ws : List (Expr md)), ws.length < vs.length → ∀ (e : Expr md) (d : Nat),
      (e.instantiateList ws d).mapKeys f = (e.mapKeys f).instantiateList (ws.map (mapKeys f)) d)
    (e : Expr md) (d : Nat) :
    (e.instantiateList vs d).mapKeys f = (e.mapKeys f).instantiateList (vs.map (mapKeys f)) d := by
  induction e generalizing d with
  | bvar j =>
    simp only [instantiateList, mapKeys]
    by_cases h₁ : j < d
    · simp [h₁]
    · by_cases h₂ : j - d < vs.length
      · have h₂' : j - d < (vs.map (mapKeys f)).length := by simpa using h₂
        simp only [h₁, if_false, h₂, h₂', dif_pos, List.getElem_map, ← List.map_take]
        exact ih _ (by simp [List.length_take]; omega) _ _
      · have h₂' : ¬ j - d < (vs.map (mapKeys f)).length := by simpa using h₂
        simp [h₁, h₂, h₂']
  | _ => simp_all [instantiateList]

/-- Instantiation of a renamed term at renamed replacements. -/
@[simp] theorem mapKeys_instantiateList (e : Expr md) (vs : List (Expr md)) (d : Nat) :
    (e.instantiateList vs d).mapKeys f =
      (e.mapKeys f).instantiateList (vs.map (mapKeys f)) d :=
  mapKeys_instantiateList_step vs (fun ws _ e d => mapKeys_instantiateList e ws d) e d
termination_by vs.length

@[simp] theorem mapKeys_liftLooseBVars (n c : Nat) (e : Expr md) :
    (liftLooseBVars n c e).mapKeys f = liftLooseBVars n c (e.mapKeys f) := by
  induction e generalizing c with
  | bvar i => simp only [liftLooseBVars, mapKeys]; split <;> simp_all
  | _ => simp_all [liftLooseBVars]

@[simp] theorem mapKeys_lowerBVars (n c : Nat) (e : Expr md) :
    (lowerBVars n c e).mapKeys f = lowerBVars n c (e.mapKeys f) := by
  induction e generalizing c with
  | bvar i => simp only [lowerBVars, mapKeys]; split <;> simp_all
  | _ => simp_all [lowerBVars]

@[simp] theorem mapKeys_instantiate1Lift (e v : Expr md) (d : Nat) :
    (e.instantiate1Lift v d).mapKeys f = (e.mapKeys f).instantiate1Lift (v.mapKeys f) d := by
  induction e generalizing d with
  | bvar i =>
    by_cases h₁ : i = d
    · simp [instantiate1Lift, h₁]
    · by_cases h₂ : i > d <;> simp [instantiate1Lift, h₁, h₂]
  | _ => simp_all [instantiate1Lift]

@[simp] theorem mapKeys_abstract1 (e : Expr md) (d k : Nat) :
    (e.abstract1 d k).mapKeys f = (e.mapKeys f).abstract1 d k := by
  induction e generalizing k with
  | fvar i t => simp only [abstract1, mapKeys]; split <;> simp_all
  | _ => simp_all [abstract1]

@[simp] theorem mapKeys_abstractRange (e : Expr md) (d k c : Nat) :
    (e.abstractRange d k c).mapKeys f = (e.mapKeys f).abstractRange d k c := by
  induction e generalizing c with
  | fvar i t => simp only [abstractRange, mapKeys]; split <;> simp_all
  | _ => simp_all [abstractRange]

@[simp] theorem mapKeys_resetMeta (e : Expr md) :
    (resetMeta e).mapKeys f = resetMeta (e.mapKeys f) := by
  induction e <;> simp_all [resetMeta]

@[simp] theorem mapKeys_getAppFn (e : Expr md) :
    (getAppFn e).mapKeys f = getAppFn (e.mapKeys f) := by
  induction e <;> simp_all [getAppFn]

@[simp] theorem getAppArgs_mapKeys (e : Expr md) :
    getAppArgs (e.mapKeys f) = (getAppArgs e).map (mapKeys f) := by
  induction e <;> simp_all [getAppArgs]

@[simp] theorem mapKeys_mkAppN (g : Expr md) (as : List (Expr md)) :
    (mkAppN g as).mapKeys f = mkAppN (g.mapKeys f) (as.map (mapKeys f)) := by
  induction as generalizing g with
  | nil => rfl
  | cons a as ih => simp [mkAppN, ih]

@[simp] theorem mapKeys_fvarTypeD (e : Expr md) :
    (fvarTypeD e).mapKeys f = fvarTypeD (e.mapKeys f) := by
  cases e <;> rfl

@[simp] theorem mapKeys_piResult (e : Expr md) :
    (piResult e).mapKeys f = piResult (e.mapKeys f) := by
  induction e <;> simp_all [piResult]

@[simp] theorem mapKeys_instSpine (as : List (Expr md)) (t : Nat) (e : Expr md) :
    (instSpine as t e).mapKeys f = instSpine (as.map (mapKeys f)) t (e.mapKeys f) := by
  induction as generalizing t e with
  | nil => rfl
  | cons a as ih => simp [instSpine, ih]

@[simp] theorem mapKeys_instantiateLevelParams (ks : List LevelParam) (us : List Level)
    (e : Expr md) :
    (e.instantiateLevelParams ks us).mapKeys f = (e.mapKeys f).instantiateLevelParams ks us := by
  induction e <;> simp_all [Expr.instantiateLevelParams]

/-- `renameConsts` with a renaming `g` that commutes with `f` on the term's
keys. -/
theorem mapKeys_renameConsts {g : Key md → Key md} {g' : Key md' → Key md'} (e : Expr md)
    (hg : ∀ k, (g k).map f = g' (k.map f)) :
    (renameConsts g e).mapKeys f = renameConsts g' (e.mapKeys f) := by
  induction e <;> simp_all [renameConsts]

/-! ## Telescope views -/

/-- Rename a binder list. -/
def mapBinders (f : md.Id → md'.Id) (bs : List (Expr md × BinderMeta)) :
    List (Expr md' × BinderMeta) :=
  bs.map fun (t, m) => (t.mapKeys f, m)

@[simp] theorem mapBinders_nil : mapBinders f ([] : List (Expr md × BinderMeta)) = [] := rfl
@[simp] theorem mapBinders_cons (t : Expr md) (m : BinderMeta) (bs : List (Expr md × BinderMeta)) :
    mapBinders f ((t, m) :: bs) = (t.mapKeys f, m) :: mapBinders f bs := rfl

/-- Rename a binder list and a body. -/
def mapTele (f : md.Id → md'.Id) (p : List (Expr md × BinderMeta) × Expr md) :
    List (Expr md' × BinderMeta) × Expr md' :=
  (mapBinders f p.1, p.2.mapKeys f)

@[simp] theorem stripLams_mapKeys (k : Nat) (e : Expr md) :
    stripLams k (e.mapKeys f) = (stripLams k e).map (mapTele f) := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    cases e with
    | lam t b m =>
      simp only [mapKeys, stripLams, ih, Option.map_map]
      cases stripLams k b <;> rfl
    | _ => rfl

@[simp] theorem stripPis_mapKeys (k : Nat) (e : Expr md) :
    stripPis k (e.mapKeys f) = (stripPis k e).map (mapTele f) := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    cases e with
    | forallE t b m =>
      simp only [mapKeys, stripPis, ih, Option.map_map]
      cases stripPis k b <;> rfl
    | _ => rfl

@[simp] theorem instPis_mapKeys (e : Expr md) (as : List (Expr md)) :
    instPis (e.mapKeys f) (as.map (mapKeys f)) = (instPis e as).map (mapKeys f) := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
    cases e with
    | forallE t b m =>
      simp only [mapKeys, List.map_cons, instPis]
      rw [← mapKeys_instantiate1, ih]
    | _ => rfl

/-- Rename a list of domains and a residual. -/
def mapDoms (f : md.Id → md'.Id) (p : List (Expr md) × Expr md) : List (Expr md') × Expr md' :=
  (p.1.map (mapKeys f), p.2.mapKeys f)

@[simp] theorem instPisAt_mapKeys (as : List (Expr md)) (e : Expr md) :
    instPisAt (as.map (mapKeys f)) (e.mapKeys f) = (instPisAt as e).map (mapDoms f) := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
    cases e with
    | forallE t b m =>
      simp only [mapKeys, List.map_cons, instPisAt]
      rw [← mapKeys_instantiate1, ih, Option.map_map, Option.map_map]
      cases instPisAt as (b.instantiate1 a) <;> rfl
    | _ => rfl

@[simp] theorem instLamsAt_mapKeys (as : List (Expr md)) (e : Expr md) :
    instLamsAt (as.map (mapKeys f)) (e.mapKeys f) = (instLamsAt as e).map (mapDoms f) := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
    cases e with
    | lam t b m =>
      simp only [mapKeys, List.map_cons, instLamsAt]
      rw [← mapKeys_instantiate1, ih, Option.map_map, Option.map_map]
      cases instLamsAt as (b.instantiate1 a) <;> rfl
    | _ => rfl

theorem instPisAtFGo_mapKeys (acc as : List (Expr md)) (e : Expr md) :
    instPisAtFGo (acc.map (mapKeys f)) (as.map (mapKeys f)) (e.mapKeys f) =
      (instPisAtFGo acc as e).map (mapDoms f) := by
  induction as generalizing acc e with
  | nil => simp [instPisAtFGo, mapDoms, mapKeys_instantiateList]
  | cons a as ih =>
    cases e with
    | forallE t b m =>
      simp only [mapKeys, List.map_cons, instPisAtFGo]
      rw [← List.map_cons, ih, Option.map_map, Option.map_map]
      cases instPisAtFGo (a :: acc) as b with
      | none => rfl
      | some p => simp [mapDoms, mapKeys_instantiateList]
    | _ => rfl

@[simp] theorem instPisAtF_mapKeys (as : List (Expr md)) (e : Expr md) :
    instPisAtF (as.map (mapKeys f)) (e.mapKeys f) = (instPisAtF as e).map (mapDoms f) := by
  unfold instPisAtF
  have h := instPisAtFGo_mapKeys (f := f) [] as e
  simp only [List.map_nil] at h
  rw [h]
  cases instPisAtFGo [] as e <;> simp

theorem instLamsAtFGo_mapKeys (acc as : List (Expr md)) (e : Expr md) :
    instLamsAtFGo (acc.map (mapKeys f)) (as.map (mapKeys f)) (e.mapKeys f) =
      (instLamsAtFGo acc as e).map (mapDoms f) := by
  induction as generalizing acc e with
  | nil => simp [instLamsAtFGo, mapDoms, mapKeys_instantiateList]
  | cons a as ih =>
    cases e with
    | lam t b m =>
      simp only [mapKeys, List.map_cons, instLamsAtFGo]
      rw [← List.map_cons, ih, Option.map_map, Option.map_map]
      cases instLamsAtFGo (a :: acc) as b with
      | none => rfl
      | some p => simp [mapDoms, mapKeys_instantiateList]
    | _ => rfl

@[simp] theorem instLamsAtF_mapKeys (as : List (Expr md)) (e : Expr md) :
    instLamsAtF (as.map (mapKeys f)) (e.mapKeys f) = (instLamsAtF as e).map (mapDoms f) := by
  unfold instLamsAtF
  have h := instLamsAtFGo_mapKeys (f := f) [] as e
  simp only [List.map_nil] at h
  rw [h]
  cases instLamsAtFGo [] as e <;> simp

@[simp] theorem pisToLams_mapKeys (k : Nat) (e b : Expr md) :
    pisToLams k (e.mapKeys f) (b.mapKeys f) = (pisToLams k e b).map (mapKeys f) := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    cases e with
    | forallE t r m =>
      simp only [mapKeys, pisToLams, ih, Option.map_map]
      cases pisToLams k r b <;> rfl
    | _ => rfl

@[simp] theorem replacePiBody_mapKeys (k : Nat) (e b : Expr md) :
    replacePiBody k (e.mapKeys f) (b.mapKeys f) = (replacePiBody k e b).map (mapKeys f) := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    cases e with
    | forallE t r m =>
      simp only [mapKeys, replacePiBody, ih, Option.map_map]
      cases replacePiBody k r b <;> rfl
    | _ => rfl

@[simp] theorem instPisAtLift_mapKeys (as : List (Expr md)) (e : Expr md) :
    instPisAtLift (as.map (mapKeys f)) (e.mapKeys f) = (instPisAtLift as e).map (mapKeys f) := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
    cases e with
    | forallE t b m =>
      simp only [mapKeys, List.map_cons, instPisAtLift]
      rw [← mapKeys_instantiate1Lift, ih]
    | _ => rfl

/-! ## Queries -/

@[simp] theorem looseBVarsBounded_mapKeys (k : Nat) (e : Expr md) :
    looseBVarsBounded k (e.mapKeys f) = looseBVarsBounded k e := by
  induction e generalizing k <;> simp_all [looseBVarsBounded]

@[simp] theorem hasFvar_mapKeys (e : Expr md) : hasFvar (e.mapKeys f) = hasFvar e := by
  induction e <;> simp_all [hasFvar]

@[simp] theorem isLam_mapKeys (e : Expr md) : isLam (e.mapKeys f) = isLam e := by
  cases e <;> rfl

@[simp] theorem lamPw_mapKeys (e : Expr md) : lamPw (e.mapKeys f) = lamPw e := by
  cases e <;> rfl

@[simp] theorem forallPw_mapKeys (e : Expr md) : forallPw (e.mapKeys f) = forallPw e := by
  cases e <;> rfl

@[simp] theorem piArity_mapKeys (e : Expr md) : piArity (e.mapKeys f) = piArity e := by
  induction e <;> simp_all [piArity]

@[simp] theorem resultSort_mapKeys (e : Expr md) : resultSort (e.mapKeys f) = resultSort e := by
  induction e <;> simp_all [resultSort]

@[simp] theorem sizeB_mapKeys (e : Expr md) : sizeB (e.mapKeys f) = sizeB e := by
  induction e <;> simp_all [sizeB]

@[simp] theorem sizeF_mapKeys (e : Expr md) : sizeF (e.mapKeys f) = sizeF e := by
  induction e <;> simp_all [sizeF]

@[simp] theorem bvarBound_mapKeys (e : Expr md) : bvarBound (e.mapKeys f) = bvarBound e := by
  induction e <;> simp_all [bvarBound]

@[simp] theorem fvarRange_mapKeys (e : Expr md) : fvarRange (e.mapKeys f) = fvarRange e := by
  induction e <;> simp_all [fvarRange]

@[simp] theorem hasLevelParam_mapKeys (e : Expr md) :
    hasLevelParam (e.mapKeys f) = hasLevelParam e := by
  induction e <;> simp_all [hasLevelParam]

@[simp] theorem allLevelParamsDefined_mapKeys (ps : List LevelParam) (e : Expr md) :
    (e.mapKeys f).allLevelParamsDefined ps = e.allLevelParamsDefined ps := by
  induction e <;> simp_all [Expr.allLevelParamsDefined]

@[simp] theorem wscopedB_mapKeys (d : Nat) (e : Expr md) :
    wscopedB d (e.mapKeys f) = wscopedB d e := by
  induction e generalizing d <;> simp_all [wscopedB]

theorem fvarLeaves_mapKeys (e : Expr md) :
    fvarLeaves (e.mapKeys f) = (fvarLeaves e).map fun (i, t) => (i, t.mapKeys f) := by
  induction e <;> simp_all [fvarLeaves]

/-- A renamed spine compares with a bound-variable spine as the spine does. -/
theorem map_mapKeys_beq_bvars {α : Type} (g : α → Nat) :
    ∀ (as : List (Expr md)) (ls : List α),
      (as.map (mapKeys f) == ls.map (fun x => (Expr.bvar (g x) : Expr md'))) =
        (as == ls.map (fun x => (Expr.bvar (g x) : Expr md)))
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, x :: ls => by
    simp only [List.map_cons, List.cons_beq_cons, map_mapKeys_beq_bvars g as ls]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, mapKeys_eq_bvar_iff]

@[simp] theorem recRulePlain_mapKeys (recTy : Expr md) (mI rP cnP : Nat) :
    recRulePlain (recTy.mapKeys f) mI rP cnP = recRulePlain recTy mI rP cnP := by
  unfold recRulePlain
  rw [stripPis_mapKeys]
  cases stripPis mI recTy with
  | none => rfl
  | some p =>
    obtain ⟨bs, body⟩ := p
    cases body with
    | forallE dom b m =>
      simp only [Option.map_some, mapTele, mapKeys, getAppArgs_mapKeys, ← List.map_take,
        map_mapKeys_beq_bvars]
    | _ => rfl

/-! ## Good results -/

theorem Good.instantiate1 {e v : Expr md} (he : e.Good P) (hv : v.Good P) (d : Nat) :
    (e.instantiate1 v d).Good P := by
  induction e generalizing d with
  | bvar i =>
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | _ => simp_all [Expr.instantiate1]

private theorem Good.instantiateList_step {vs : List (Expr md)} (hvs : GoodList P vs)
    (ih : ∀ (ws : List (Expr md)), ws.length < vs.length → GoodList P ws →
      ∀ (e : Expr md), e.Good P → ∀ (d : Nat), (e.instantiateList ws d).Good P)
    {e : Expr md} (he : e.Good P) (d : Nat) : (e.instantiateList vs d).Good P := by
  induction e generalizing d with
  | bvar j =>
    simp only [Expr.instantiateList]
    by_cases h₁ : j < d
    · simp [h₁]
    · by_cases h₂ : j - d < vs.length
      · simp only [h₁, if_false, h₂, dif_pos]
        exact ih _ (by simp [List.length_take]; omega)
          (fun x hx => hvs x (List.mem_of_mem_take hx)) _ (hvs _ (List.getElem_mem h₂)) d
      · simp [h₁, h₂]
  | _ => simp_all [Expr.instantiateList]

theorem Good.instantiateList {e : Expr md} {vs : List (Expr md)} (he : e.Good P)
    (hvs : GoodList P vs) (d : Nat) : (e.instantiateList vs d).Good P :=
  Good.instantiateList_step hvs (fun _ _ hws _ he d => Good.instantiateList he hws d) he d
termination_by vs.length

theorem Good.liftLooseBVars {e : Expr md} (he : e.Good P) (n c : Nat) :
    (liftLooseBVars n c e).Good P := by
  induction e generalizing c with
  | bvar i => simp only [Expr.liftLooseBVars]; split <;> trivial
  | _ => simp_all [Expr.liftLooseBVars]

theorem Good.lowerBVars {e : Expr md} (he : e.Good P) (n c : Nat) :
    (lowerBVars n c e).Good P := by
  induction e generalizing c with
  | bvar i => simp only [Expr.lowerBVars]; split <;> trivial
  | _ => simp_all [Expr.lowerBVars]

theorem Good.instantiate1Lift {e v : Expr md} (he : e.Good P) (hv : v.Good P) (d : Nat) :
    (e.instantiate1Lift v d).Good P := by
  induction e generalizing d with
  | bvar i =>
    simp only [Expr.instantiate1Lift]
    split
    · exact Good.liftLooseBVars hv d 0
    · split <;> trivial
  | _ => simp_all [Expr.instantiate1Lift]

theorem Good.abstract1 {e : Expr md} (he : e.Good P) (d k : Nat) : (e.abstract1 d k).Good P := by
  induction e generalizing k with
  | fvar i t ih => simp only [Expr.abstract1]; split <;> simp_all
  | _ => simp_all [Expr.abstract1]

theorem Good.abstractRange {e : Expr md} (he : e.Good P) (d k c : Nat) :
    (e.abstractRange d k c).Good P := by
  induction e generalizing c with
  | fvar i t ih => simp only [Expr.abstractRange]; split <;> simp_all
  | _ => simp_all [Expr.abstractRange]

theorem Good.resetMeta {e : Expr md} (he : e.Good P) : (resetMeta e).Good P := by
  induction e <;> simp_all [Expr.resetMeta]

theorem Good.getAppFn {e : Expr md} (he : e.Good P) : (getAppFn e).Good P := by
  induction e <;> simp_all [Expr.getAppFn]

theorem Good.getAppArgs {e : Expr md} (he : e.Good P) : GoodList P (getAppArgs e) := by
  induction e with
  | app a b iha _ =>
    simp only [Expr.getAppArgs, goodList_append, goodList_cons, goodList_nil, and_true]
    exact ⟨iha he.1, he.2⟩
  | _ => simp [Expr.getAppArgs]

theorem Good.mkAppN {g : Expr md} {as : List (Expr md)} (hg : g.Good P) (has : GoodList P as) :
    (mkAppN g as).Good P := by
  induction as generalizing g with
  | nil => exact hg
  | cons a as ih =>
    simp only [goodList_cons] at has
    exact ih ⟨hg, has.1⟩ has.2

theorem Good.fvarTypeD {e : Expr md} (he : e.Good P) : (fvarTypeD e).Good P := by
  cases e <;> simp_all [Expr.fvarTypeD]

theorem Good.piResult {e : Expr md} (he : e.Good P) : (piResult e).Good P := by
  induction e <;> simp_all [Expr.piResult]

theorem Good.instantiateLevelParams {e : Expr md} (he : e.Good P) (ks : List LevelParam)
    (us : List Level) : (e.instantiateLevelParams ks us).Good P := by
  induction e <;> simp_all [Expr.instantiateLevelParams]

end Ix.Kernel.Expr
