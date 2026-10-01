module

import ConLeche.Kernel.Level
import ConLeche.Kernel.ExprOps
import ConLeche.Verify.Level
public import ConLeche.Verify.PropWhen
public import ConLeche.Verify.Subst

public section

/-!
# Syntactic lemmas about level-parameter instantiation

* substitution composition (`Level.subst_subst`, `Expr.instLevels_instLevels`),
* commutation with binder opening (`Expr.instLevels_instantiate1`),
* preservation of closedness and of level-parameter bounds.

Composition and bound-preservation need the original term to mention only
parameters from the substituted list *and* the lists to be aligned
(`us.length = ks.length`) — both checked by the checker before any
instantiation happens.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ConLeche

namespace Level

private theorem subst_go_subst {ks : List Name} {us : List Level} :
    ∀ {ps : List Name} {vs : List Level} {n : Name},
      n ∈ ps → vs.length = ps.length →
      subst ks us (subst.go ps vs n) = subst.go ps (vs.map (subst ks us)) n := by
  intro ps
  induction ps with
  | nil => intro vs n hn _; simp at hn
  | cons p ps ih =>
    intro vs n hn hl
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.map, subst.go]
      split
      · rfl
      · next hne =>
        refine ih ?_ (by simpa using hl)
        rcases List.mem_cons.mp hn with rfl | h
        · exact absurd rfl hne
        · exact h

/-- Substituting into an already-substituted level composes, provided the
original level only mentions parameters from `ps` and the lists align. -/
theorem subst_subst {ks : List Name} {us : List Level} {ps : List Name} {vs : List Level}
    (hl : vs.length = ps.length) :
    ∀ {u : Level}, u.allParamsDefined ps = true →
      subst ks us (subst ps vs u) = subst ps (vs.map (subst ks us)) u := by
  intro u
  induction u <;> intro h <;> simp_all [subst, allParamsDefined]
  case param n => exact subst_go_subst (by simpa using h) hl

private theorem allParamsDefined_subst_go {ps' : List Name} :
    ∀ {ks : List Name} {us : List Level} {n : Name},
      n ∈ ks → us.length = ks.length → (∀ u ∈ us, u.allParamsDefined ps' = true) →
      (subst.go ks us n).allParamsDefined ps' = true := by
  intro ks
  induction ks with
  | nil => intro us n hn _ _; simp at hn
  | cons k ks ih =>
    intro us n hn hl hus
    cases us with
    | nil => simp at hl
    | cons u us =>
      simp only [subst.go]
      split
      · exact hus u (by simp)
      · next hne =>
        refine ih ?_ (by simpa using hl) (fun v hv => hus v (by simp [hv]))
        rcases List.mem_cons.mp hn with rfl | h
        · exact absurd rfl hne
        · exact h

/-- Substitution keeps parameters within the bound of the substituted
levels. -/
theorem allParamsDefined_subst {ks : List Name} {us : List Level} {ps' : List Name}
    (hl : us.length = ks.length)
    (hus : ∀ u ∈ us, u.allParamsDefined ps' = true) :
    ∀ {u : Level}, u.allParamsDefined ks = true →
      (subst ks us u).allParamsDefined ps' = true := by
  intro u
  induction u <;> intro h <;> simp_all [subst, allParamsDefined]
  case param n => exact allParamsDefined_subst_go (by simpa using h) hl hus

end Level

namespace Expr

/-- Level instantiation does not change the free-variable structure. -/
theorem hasFvar_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, (e.instantiateLevelParams ks us).hasFvar = e.hasFvar := by
  intro e
  induction e <;> simp_all [instantiateLevelParams, hasFvar]

/-- Level instantiation does not change loose-bvar bounds. -/
theorem looseBVarsBounded_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiateLevelParams ks us).looseBVarsBounded k = e.looseBVarsBounded k := by
  intro e
  induction e <;> intro k <;> simp_all [instantiateLevelParams, looseBVarsBounded]

/-- Level instantiation distributes over a `∀`-telescope's
decomposition. -/
theorem stripPis_instantiateLevelParams_eq (ks : List Name)
    (us : List Level) :
    ∀ (k : Nat) {e : Expr} {bs bs' : List (Expr × BinderMeta)}
      {body body' : Expr},
      e.stripPis k = some (bs, body) →
      (e.instantiateLevelParams ks us).stripPis k = some (bs', body') →
      body' = body.instantiateLevelParams ks us ∧
      ∀ (i : Nat) (b b' : Expr × BinderMeta),
        bs[i]? = some b → bs'[i]? = some b' →
        b'.1 = b.1.instantiateLevelParams ks us := by
  intro k
  induction k with
  | zero =>
    intro e bs bs' body body' h1 h2
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    exact ⟨rfl, fun i b b' hb _ => by simp at hb⟩
  | succ k ih =>
    intro e bs bs' body body' h1 h2
    match e, h1 with
    | .forallE d b m, h1 =>
      simp only [Expr.instantiateLevelParams, Expr.stripPis] at h1 h2
      cases hs1 : b.stripPis k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : (b.instantiateLevelParams ks us).stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, hbody1⟩ : (d, m) :: p1.1 = bs ∧ p1.2 = body := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, hbody2⟩ :
          (d.instantiateLevelParams ks us,
            (⟨Level.substPW ks us m.pw⟩ : BinderMeta)) :: p2.1
              = bs' ∧
            p2.2 = body' := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hbody1 hb2 hbody2
      obtain ⟨hbody, hdoms⟩ := ih hs1 hs2
      refine ⟨hbody, ?_⟩
      intro i bb bb' hbb hbb'
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hbb hbb'
        subst hbb hbb'
        simp
      | succ i =>
        simp only [List.getElem?_cons_succ] at hbb hbb'
        exact hdoms i bb bb' hbb hbb'

/-- Level instantiation preserves a `∀`-telescope's arity. -/
theorem stripPis_instantiateLevelParams_isSome (ks : List Name)
    (us : List Level) :
    ∀ (k : Nat) {e : Expr}, (e.stripPis k).isSome →
      ((e.instantiateLevelParams ks us).stripPis k).isSome := by
  intro k
  induction k with
  | zero => intro e _; simp [Expr.stripPis]
  | succ k ih =>
    intro e h
    match e, h with
    | .forallE ty body m, h =>
      simp only [Expr.instantiateLevelParams, Expr.stripPis,
        Option.isSome_map] at h ⊢
      exact ih h

/-- Level instantiation distributes over an application spine's
arguments. -/
theorem getAppArgs_instantiateLevelParams (ks : List Name)
    (us : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).getAppArgs =
      e.getAppArgs.map (·.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | app f a ihf iha =>
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs, ihf,
      List.map_append, List.map_cons, List.map_nil]
  | _ => simp [Expr.instantiateLevelParams, Expr.getAppArgs]

/-- Level instantiation preserves the head shape. -/
theorem getAppFn_instantiateLevelParams (ks : List Name)
    (us : List Level) :
    ∀ (e : Expr), (e.instantiateLevelParams ks us).getAppFn =
      e.getAppFn.instantiateLevelParams ks us := by
  intro e
  induction e with
  | app f a ihf iha => simpa [Expr.instantiateLevelParams, Expr.getAppFn]
      using ihf
  | _ => simp [Expr.instantiateLevelParams, Expr.getAppFn]

/-- A stripped telescope's body keeps its level parameters defined. -/
theorem allLevelParamsDefined_stripPis_body {ps : List Name} :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr},
      e.stripPis k = some (bs, body) →
      e.allLevelParamsDefined ps = true →
      body.allLevelParamsDefined ps = true := by
  intro k
  induction k with
  | zero =>
    intro e bs body h hp
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact hp
  | succ k ih =>
    intro e bs body h hp
    match e, h with
    | .forallE ty b m, h =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hb, heq⟩ := h
      obtain ⟨-, rfl⟩ : (ty, m) :: bs' = bs ∧ body' = body := by
        simpa using heq
      simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hp
      exact ih hb hp.1.2

/-- Renaming constants commutes with instantiation (general argument). -/
theorem renameConsts_instantiate1_gen (f : Name → Name) {v : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 v k).renameConsts f =
        (e.renameConsts f).instantiate1 (v.renameConsts f) k := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Expr.instantiate1, Expr.renameConsts]
    split
    · rfl
    · split <;> simp [Expr.renameConsts]
  | _ =>
    intro k
    simp_all [Expr.instantiate1, Expr.renameConsts]

/-- Level instantiation commutes with binder opening. -/
theorem instantiateLevelParams_instantiate1 (ks : List Name) (us : List Level)
    {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d ty) k).instantiateLevelParams ks us =
        (e.instantiateLevelParams ks us).instantiate1
          (.fvar d (ty.instantiateLevelParams ks us)) k := by
  intro e
  induction e <;> intro k <;> simp_all [instantiate1, instantiateLevelParams]
  case bvar i =>
    split
    · rfl
    · split <;> simp [instantiateLevelParams]

theorem renameConsts_instantiate1 (f : Name → Name)
    {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 (.fvar d ty) k).renameConsts f =
        (e.renameConsts f).instantiate1
          (.fvar d (ty.renameConsts f)) k := by
  intro e
  induction e <;> intro k <;> simp_all [Expr.instantiate1, Expr.renameConsts]
  case bvar i =>
    split
    · rfl
    · split <;> simp [Expr.renameConsts]

/-- Binder opening keeps level parameters bounded. -/
theorem allLevelParamsDefined_instantiate1 {ps : List Name} {d : Nat} {ty : Expr}
    (hty : ty.allLevelParamsDefined ps = true) :
    ∀ {e : Expr} (k : Nat), e.allLevelParamsDefined ps = true →
      (e.instantiate1 (.fvar d ty) k).allLevelParamsDefined ps = true := by
  intro e
  induction e <;> intro k h <;> simp_all [instantiate1, allLevelParamsDefined]
  case bvar i =>
    split
    · simpa [allLevelParamsDefined] using hty
    · split <;> simp [allLevelParamsDefined]

/-- Renaming an instantiation sequence: pushing the renaming inside is
exact on the telescope and erased on the (fvar) arguments. -/
theorem instSeq_renameConsts {f : Name → Name} :
    ∀ (args : List Expr) (t : Nat) {X : Expr},
      (∀ a ∈ args, ErasedEq (a.renameConsts f) a) →
      ErasedEq ((instSeq args t X).renameConsts f)
        (instSeq args t (X.renameConsts f)) := by
  intro args
  induction args with
  | nil => intro t X _; exact ErasedEq.rfl _
  | cons a as ih =>
    intro t X ha
    show ErasedEq
      ((instSeq as (t - 1) (X.instantiate1 a t)).renameConsts f) _
    refine ErasedEq.trans
      (ih (t - 1) (fun x hx => ha x (List.mem_cons_of_mem _ hx))) ?_
    rw [renameConsts_instantiate1_gen]
    exact instSeq_erasedEq as (t - 1)
      (ErasedEq.instantiate1 (ErasedEq.rfl _)
        (ha a List.mem_cons_self))


end Expr


/-- Level instantiation distributes over an application spine. -/
theorem instantiateLevelParams_mkAppN (ks : List Name) (us : List Level) :
    ∀ (xs : List Expr) (h : Expr),
      (Expr.mkAppN h xs).instantiateLevelParams ks us =
        Expr.mkAppN (h.instantiateLevelParams ks us)
          (xs.map (fun x => x.instantiateLevelParams ks us))
  | [], _ => rfl
  | x :: xs, h => by
    show (Expr.mkAppN (.app h x) xs).instantiateLevelParams ks us = _
    rw [instantiateLevelParams_mkAppN ks us xs]
    rfl

/-- Substituting each level parameter by itself is the identity. -/
theorem Level.subst_param_self (ks : List Name) :
    ∀ l : Level, Level.subst ks (ks.map Level.param) l = l := by
  have hgo : ∀ (ks : List Name) (n : Name),
      Level.subst.go ks (ks.map Level.param) n = .param n := by
    intro ks
    induction ks with
    | nil => intro n; rfl
    | cons k ks ih =>
      intro n
      by_cases h : k = n
      · subst h; simp [Level.subst.go]
      · simp only [List.map_cons, Level.subst.go, if_neg h]
        exact ih n
  intro l
  induction l with
  | zero => rfl
  | succ l ih => simp [Level.subst, ih]
  | max l r ihl ihr => simp [Level.subst, ihl, ihr]
  | imax l r ihl ihr => simp [Level.subst, ihl, ihr]
  | param n => exact hgo ks n

/-- …and so is instantiating a declaration at its own parameters. -/
theorem Expr.instantiateLevelParams_self (ks : List Name) :
    ∀ e : Expr, e.instantiateLevelParams ks (ks.map Level.param) = e := by
  intro e
  have hmap : ∀ us : List Level,
      us.map (Level.subst ks (ks.map Level.param)) = us := by
    intro us
    induction us with
    | nil => rfl
    | cons x xs ih => simp [Level.subst_param_self, ih]
  induction e <;>
    simp_all [Expr.instantiateLevelParams, Level.subst_param_self, hmap,
      Level.substPW_self]

end ConLeche
