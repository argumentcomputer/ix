module

public import IxC.Kernel.Model.Open.ProjType
import IxC.Kernel.Model.Open.Levels
import IxC.Kernel.Verify.Inductives.StructBody
import IxC.Kernel.Verify.InstSpine
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.InferLemmas
import IxC.Kernel.Verify.InferLeaves
import IxC.Kernel.Verify.Subst

@[expose] public section

/-!
# The rules' soundness over the public `Model`: ι

`Red.iota` fires a stored recursor rule at a constructor application. Its soundness reads the
ι law (`Model.iota_rule`, `IotaRule`) at the values of the redex:

* the recursor's licensed walk is a fit of its type (`StoredArities`), split at the major
  premise (`FitsO.split_snoc`); the major premise's domain is the stored type's, headed by
  the family at the rule's comparand levels (`StoredRules`);
* the constructor's licensed walk is a fit of its type (`StoredRules`: its binders), moved to
  the domain's levels (`Fits.congr_instLP`);
* the parameters, at a rule that compares them: the comparison makes the constructor's
  parameters the domain's, which are the recursor's prefix variables, or a nested rule's
  stored instantiations lifted past the indices (`DenotesO.unlift`, `GradedBy.unliftO`);
* the indices, at a recursor that has some: the residual the rule compares is the
  constructor fit's residual with the major premise's arguments substituted
  (`piResidual_of_stripPis`), read as the fit reads it (`DenotesO.instSpine`), argument by
  argument because the residual is headed by a constant (`Expr.ctorTeleOk`);
* the reduct: the law's right-hand side denotes, is graded, and applies along the prefix and
  the fields on its domains (`Gr.mkAppN_of_spineOk`).
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules
open Ix.Kernel.Model.Rules (Frame LeavesSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env md}

/-! ## Lists -/

theorem evalEqList_length {ψ : LevelParam → Nat} : ∀ {us vs : List Level},
    Level.EvalEqList ψ us vs → us.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [Level.EvalEqList] at h
    simp only [List.length_cons, evalEqList_length h.2]
  | [], _ :: _, h => by simp [Level.EvalEqList] at h
  | _ :: _, [], h => by simp [Level.EvalEqList] at h

theorem eq_take_append_getD {α : Type _} (d : α) : ∀ {l : List α} {n : Nat}, l.length = n + 1 →
    l = l.take n ++ [l.getD n d]
  | [], _, h => by simp at h
  | [_], 0, _ => by simp
  | _ :: _ :: _, 0, h => by simp at h
  | x :: xs, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.take_succ_cons, List.getD_cons_succ, List.cons_append, ← eq_take_append_getD d h]

/-! ## Substituting a spine into a residual -/

/-- **A telescope's residual, instantiated at a spine**, is the stripped body with the spine
substituted for its outer variables. -/
theorem piResidual_of_stripPis : ∀ (args : List (Expr md)) {T R0 : Expr md}
    {bs : List (Expr md × BinderMeta)}, T.stripPis args.length = some (bs, R0) →
    piResidual T args = some (Expr.instSpine args (args.length - 1) R0)
  | [], T, R0, bs, h => by
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | a :: as, T, R0, bs, h => by
    rw [List.length_cons] at h
    match T, h with
    | .forallE A B m, h =>
      simp only [Expr.stripPis] at h
      cases hs : B.stripPis as.length with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        obtain ⟨bsB, RB⟩ := p
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨bs', h1, -⟩ := Ix.Kernel.stripPis_instantiate1_full (v := a) as.length 0 hs
        rw [Nat.zero_add] at h1
        show piResidual (B.instantiate1 a) as = _
        rw [piResidual_of_stripPis as h1]
        simp only [List.length_cons, Nat.add_sub_cancel, Expr.instSpine]

theorem instSeq_const' : ∀ (args : List (Expr md)) (t : Nat) (n : Key md) (ls : List Level),
    Expr.instSeq args t (.const n ls) = .const n ls
  | [], _, _, _ => rfl
  | _ :: as, t, n, ls => instSeq_const' as (t - 1) n ls

/-- A spine substituted into a constant-headed application substitutes into its arguments. -/
theorem instSpine_mkAppN_const (args : List (Expr md)) (t : Nat) (n : Key md) (ls : List Level)
    (as : List (Expr md)) :
    Expr.instSpine args t (Expr.mkAppN (.const n ls) as) =
      Expr.mkAppN (.const n ls) (as.map (Expr.instSpine args t)) := by
  rw [Ix.Kernel.Expr.instSpine_eq_instSeq, Ix.Kernel.Expr.instSeq_mkAppN, instSeq_const']
  congr 1
  exact List.map_congr_left fun a _ => (Ix.Kernel.Expr.instSpine_eq_instSeq args t a).symm

/-! ## Fits -/

section
variable {cval : Key md → (LevelParam → Nat) → V} {φ : LevelParam → Nat}

theorem Fits.nil_inv' {ρ ρ' : BVarIdx → V} {T R : Expr md}
    (h : Fits cval env φ ρ T [] ρ' R) : ρ' = ρ ∧ R = T := by
  generalize hxs : ([] : List V) = xs at h
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ => exact nomatch hxs

/-- **A fit's residual at another level instantiation**: a fit of a level-instantiated
telescope is the telescope's fit at the assignment the instantiation induces. -/
theorem Fits.of_instLP (hcp : CvalParams cval env) (ks : List LevelParam) (us : List Level) :
    ∀ (xs : List V) (T : Expr md) (ρ ρ' : BVarIdx → V) (R' : Expr md), T.hasFvar = false →
      Fits cval env φ ρ (T.instantiateLevelParams ks us) xs ρ' R' →
      ∃ R, R' = R.instantiateLevelParams ks us ∧
        Fits cval env (Level.substFn φ ks us) ρ T xs ρ' R
  | [], T, ρ, ρ', R', _, h => by
    obtain ⟨rfl, rfl⟩ := Fits.nil_inv' h
    exact ⟨T, rfl, .nil⟩
  | x :: xs, T, ρ, ρ', R', hT, h => by
    cases T with
    | forallE A B m =>
      simp only [Expr.instantiateLevelParams] at h
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hT
      cases h with
      | cons hA hx hrest =>
        obtain ⟨R, rfl, hfit⟩ := Fits.of_instLP hcp ks us xs B _ ρ' R' hT.2 hrest
        refine ⟨R, rfl, .cons ?_ hx hfit⟩
        exact ((DenotesO.instantiateLevelParams (σ := fun _ => empty) hcp ks us A ρ _).1
          (DenotesO.of_denotes hA)).to_denotes hT.1
    | _ => first | cases h | (simp only [Expr.instantiateLevelParams] at h; cases h)

theorem Fits.to_instLP (hcp : CvalParams cval env) (ks : List LevelParam) (us : List Level) :
    ∀ {ρ ρ' : BVarIdx → V} {T R : Expr md} {xs : List V},
      Fits cval env (Level.substFn φ ks us) ρ T xs ρ' R → T.hasFvar = false →
      Fits cval env φ ρ (T.instantiateLevelParams ks us) xs ρ' (R.instantiateLevelParams ks us) := by
  intro ρ ρ' T R xs h
  induction h with
  | nil => exact fun _ => .nil
  | @cons ρ ρ' A B R m X x xs hA hx _ ih =>
    intro hT
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hT
    simp only [Expr.instantiateLevelParams]
    refine .cons ?_ hx (ih hT.2)
    have hAf : (A.instantiateLevelParams ks us).hasFvar = false := by
      rw [Expr.hasFvar_instantiateLevelParams]; exact hT.1
    exact ((DenotesO.instantiateLevelParams (σ := fun _ => empty) hcp ks us A ρ _).2
      (DenotesO.of_denotes hA)).to_denotes hAf

/-- **A fit at levels that evaluate alike**: the residual moves with the instantiation. -/
theorem Fits.congr_instLP (hcp : CvalParams cval env) {ks : List LevelParam}
    {us us' : List Level} (heq : Level.substFn φ ks us = Level.substFn φ ks us')
    {xs : List V} {T : Expr md} {ρ ρ' : BVarIdx → V} {R' : Expr md} (hT : T.hasFvar = false)
    (h : Fits cval env φ ρ (T.instantiateLevelParams ks us) xs ρ' R') :
    ∃ R, R' = R.instantiateLevelParams ks us ∧
      Fits cval env φ ρ (T.instantiateLevelParams ks us') xs ρ' (R.instantiateLevelParams ks us') := by
  obtain ⟨R, rfl, hfit⟩ := Fits.of_instLP hcp ks us xs T ρ ρ' R' hT h
  rw [heq] at hfit
  exact ⟨R, rfl, Fits.to_instLP hcp ks us' hfit hT⟩

end

/-! ## Open fits and readings at any variable environment -/

variable {M : Model V env} {φ : LevelParam → Nat}

theorem FitsO.env_eq {σ : Nat → V} {ρ ρ' : BVarIdx → V} {T R : Expr md} {xs : List V}
    (h : FitsO M φ σ ρ T xs ρ' R) : ρ' = pushVals ρ xs := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => exact ih

theorem FitsO.hasFvar {σ : Nat → V} {ρ ρ' : BVarIdx → V} {T R : Expr md} {xs : List V}
    (h : FitsO M φ σ ρ T xs ρ' R) : T.hasFvar = false → R.hasFvar = false := by
  induction h with
  | nil => exact id
  | cons _ _ _ ih =>
    intro hT
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hT
    exact ih hT.2

theorem FitsO.split_snoc {σ : Nat → V} : ∀ (xs : List V) {x : V} {ρ ρ' : BVarIdx → V}
    {T R : Expr md}, FitsO M φ σ ρ T (xs ++ [x]) ρ' R →
    ∃ (σR : BVarIdx → V) (dom body : Expr md) (m : BinderMeta) (X : V),
      FitsO M φ σ ρ T xs σR (.forallE dom body m) ∧ DenotesO M.cval env φ σ σR dom X ∧ x ∈ˢ X
  | [], x, ρ, ρ', T, R, h => by
    rw [List.nil_append] at h
    cases h with
    | cons hA hx _ => exact ⟨ρ, _, _, _, _, .nil, hA, hx⟩
  | y :: ys, x, ρ, ρ', T, R, h => by
    rw [List.cons_append] at h
    cases h with
    | cons hA hy hrest =>
      obtain ⟨σR, dom, body, m, X, hfit, hd, hx⟩ := FitsO.split_snoc ys hrest
      exact ⟨σR, dom, body, m, X, .cons hA hy hfit, hd, hx⟩

theorem FitsO.residual {σ : Nat → V} {ρ ρ' : BVarIdx → V} {T R : Expr md} {xs : List V}
    (h : FitsO M φ σ ρ T xs ρ' R) :
    ∀ {W : V}, DenotesO M.cval env φ σ ρ T W → ∃ W', DenotesO M.cval env φ σ ρ' R W' := by
  induction h with
  | nil => exact fun hW => ⟨_, hW⟩
  | cons hA hx _ ih =>
    intro W hW
    cases hW with
    | pi hA' hB _ =>
      obtain rfl := DenotesO.functional hA hA'
      exact ih (hB _ hx)

theorem FitsO.graded {σ : Nat → V} {ρ ρ' : BVarIdx → V} {T R : Expr md} {xs : List V}
    (h : FitsO M φ σ ρ T xs ρ' R) :
    GradedBy (DenotesO M.cval env φ σ) ρ T → GradedBy (DenotesO M.cval env φ σ) ρ' R := by
  induction h with
  | nil => exact id
  | cons hA hx _ ih =>
    intro hg
    simp only [GradedBy] at hg
    exact ih (hg.2 _ hA _ hx)

/-- A spine's open reading, at any variable environment. -/
theorem DenotesO.mkAppN_inv' {σ : Nat → V} {ρ : BVarIdx → V} :
    ∀ {as : List (Expr md)} {f : Expr md} {W : V},
      DenotesO M.cval env φ σ ρ (Expr.mkAppN f as) W →
      ∃ F vs, DenotesO M.cval env φ σ ρ f F ∧
        (∀ k, k < as.length → DenotesO M.cval env φ σ ρ (as.getD k (.bvar 0)) (vs.getD k empty)) ∧
        vs.length = as.length ∧ W = vs.foldl app F
  | [], _, _, h => ⟨_, [], h, fun k hk => absurd hk (Nat.not_lt_zero _), rfl, rfl⟩
  | a :: as, f, _, h => by
    obtain ⟨F', vs, hF', hvs, hlen, rfl⟩ := DenotesO.mkAppN_inv' (as := as) (f := .app f a) h
    cases hF' with
    | app hF hX =>
      refine ⟨_, _ :: vs, hF, fun k hk => ?_, by simp [hlen], rfl⟩
      cases k with
      | zero => rw [List.getD_cons_zero, List.getD_cons_zero]; exact hX
      | succ k =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact hvs k (by simpa using hk)

/-- A spine's open grading grades its head, at any variable environment. -/
theorem GradedBy.mkAppN_head' {σ : Nat → V} {ρ : BVarIdx → V} :
    ∀ {as : List (Expr md)} {g : Expr md},
      GradedBy (DenotesO M.cval env φ σ) ρ (Expr.mkAppN g as) →
      GradedBy (DenotesO M.cval env φ σ) ρ g
  | [], _, h => h
  | b :: bs, g, h => by
    have h' := GradedBy.mkAppN_head' (as := bs) (g := .app g b) h
    simp only [GradedBy] at h'
    exact h'.1

/-- A spine's open grading grades its arguments, at any variable environment. -/
theorem GradedBy.mkAppN_args' {σ : Nat → V} {ρ : BVarIdx → V} :
    ∀ {as : List (Expr md)} {g : Expr md},
      GradedBy (DenotesO M.cval env φ σ) ρ (Expr.mkAppN g as) →
      ∀ x ∈ as, GradedBy (DenotesO M.cval env φ σ) ρ x
  | [], _, _ => fun _ hx => nomatch hx
  | b :: bs, g, h => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have hg := GradedBy.mkAppN_head' (as := bs) (g := .app g x) h
      simp only [GradedBy] at hg
      exact hg.2.1
    · exact GradedBy.mkAppN_args' (as := bs) (g := .app g b) h x hx

/-! ## Lifting past bound variables, at open readings -/

theorem push_agree_lift {c k : Nat} {ρ0 ρ1 : BVarIdx → V} (x : V)
    (h1 : ∀ i, i < c → ρ1 i = ρ0 i) (h2 : ∀ i, c ≤ i → ρ1 (i + k) = ρ0 i) :
    (∀ i, i < c + 1 → push x ρ1 i = push x ρ0 i) ∧
      (∀ i, c + 1 ≤ i → push x ρ1 (i + k) = push x ρ0 i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · cases i with
    | zero => rfl
    | succ i => exact h1 i (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [show j + 1 + k = (j + k) + 1 by omega]
    exact h2 j (by omega)

/-- **Lifting a term's loose variables is reading it where the lifted indices are
skipped** (open readings). -/
theorem DenotesO.lift {σ : Nat → V} {ρ0 : BVarIdx → V} {e : Expr md} {v : V}
    (h : DenotesO M.cval env φ σ ρ0 e v) :
    ∀ {k c : Nat} {ρ1 : BVarIdx → V}, (∀ i, i < c → ρ1 i = ρ0 i) →
      (∀ i, c ≤ i → ρ1 (i + k) = ρ0 i) →
      DenotesO M.cval env φ σ ρ1 (e.liftLooseBVars k c) v := by
  induction h with
  | @bvar ρ i =>
    intro k c ρ1 hlo hhi
    by_cases hic : i ≥ c
    · simp only [Expr.liftLooseBVars, if_pos hic]
      rw [← hhi i hic]
      exact .bvar
    · simp only [Expr.liftLooseBVars, if_neg hic]
      rw [← hlo i (Nat.not_le.mp hic)]
      exact .bvar
  | fvar => intros; exact .fvar
  | sort => intros; exact .sort
  | const hf hlen => intros; exact .const hf hlen
  | app _ _ ihf iha => intro k c ρ1 hlo hhi; exact .app (ihf hlo hhi) (iha hlo hhi)
  | lam _ _ hP ihA ihF =>
    intro k c ρ1 hlo hhi
    exact .lam (ihA hlo hhi)
      (fun x hx => ihF x hx (push_agree_lift x hlo hhi).1 (push_agree_lift x hlo hhi).2) hP
  | pi _ _ hP ihA ihB =>
    intro k c ρ1 hlo hhi
    exact .pi (ihA hlo hhi)
      (fun x hx => ihB x hx (push_agree_lift x hlo hhi).1 (push_agree_lift x hlo hhi).2) hP
  | proj_table ht _ ih => intro k c ρ1 hlo hhi; exact .proj_table ht (ih hlo hhi)
  | proj_fst ht _ ih => intro k c ρ1 hlo hhi; exact .proj_fst ht (ih hlo hhi)
  | proj_snd ht _ ih => intro k c ρ1 hlo hhi; exact .proj_snd ht (ih hlo hhi)
  | natLit hd _ =>
    intro k c ρ1 _ _
    exact .natLit (hd.congr_env (k := 0) (fun i hi => absurd hi (Nat.not_lt_zero _))
      (natLitToConstructor_looseBVarsBounded _ 0))
  | strLit hd _ =>
    intro k c ρ1 _ _
    exact .strLit (hd.congr_env (k := 0) (fun i hi => absurd hi (Nat.not_lt_zero _))
      (Ix.Kernel.strLitToConstructor_looseBVars _ 0))

/-- **Reading a lifted term**: what the lifted term denotes where the lifted indices are
skipped, the term denotes. -/
theorem DenotesO.unlift {σ : Nat → V} :
    ∀ (e : Expr md) {k c : Nat} {ρ0 ρ1 : BVarIdx → V} {v : V},
      (∀ i, i < c → ρ1 i = ρ0 i) → (∀ i, c ≤ i → ρ1 (i + k) = ρ0 i) →
      DenotesO M.cval env φ σ ρ1 (e.liftLooseBVars k c) v → DenotesO M.cval env φ σ ρ0 e v := by
  intro e
  induction e with
  | bvar i =>
    intro k c ρ0 ρ1 v hlo hhi h
    by_cases hic : i ≥ c
    · simp only [Expr.liftLooseBVars, if_pos hic] at h
      cases h
      rw [hhi i hic]
      exact .bvar
    · simp only [Expr.liftLooseBVars, if_neg hic] at h
      cases h
      rw [hlo i (Nat.not_le.mp hic)]
      exact .bvar
  | fvar i ty _ =>
    intro k c ρ0 ρ1 v _ _ h
    simp only [Expr.liftLooseBVars] at h
    cases h
    exact .fvar
  | sort u =>
    intro k c ρ0 ρ1 v _ _ h
    simp only [Expr.liftLooseBVars] at h
    cases h
    exact .sort
  | const n us =>
    intro k c ρ0 ρ1 v _ _ h
    simp only [Expr.liftLooseBVars] at h
    cases h with
    | const hf hlen => exact .const hf hlen
  | app f a ihf iha =>
    intro k c ρ0 ρ1 v hlo hhi h
    simp only [Expr.liftLooseBVars] at h
    cases h with
    | app hf ha => exact .app (ihf hlo hhi hf) (iha hlo hhi ha)
  | lam ty b _ ihty ihb =>
    intro k c ρ0 ρ1 v hlo hhi h
    simp only [Expr.liftLooseBVars] at h
    cases h with
    | lam hA hF hP =>
      exact .lam (ihty hlo hhi hA)
        (fun x hx => ihb (push_agree_lift x hlo hhi).1 (push_agree_lift x hlo hhi).2 (hF x hx)) hP
  | forallE ty b _ ihty ihb =>
    intro k c ρ0 ρ1 v hlo hhi h
    simp only [Expr.liftLooseBVars] at h
    cases h with
    | pi hA hB hP =>
      exact .pi (ihty hlo hhi hA)
        (fun x hx => ihb (push_agree_lift x hlo hhi).1 (push_agree_lift x hlo hhi).2 (hB x hx)) hP
  | letE _ _ _ _ _ _ _ =>
    intro k c ρ0 ρ1 v _ _ h
    simp only [Expr.liftLooseBVars] at h
    cases h
  | lit l =>
    intro k c ρ0 ρ1 v _ _ h
    simp only [Expr.liftLooseBVars] at h
    cases h with
    | natLit hd =>
      exact .natLit (hd.congr_env (k := 0) (fun i hi => absurd hi (Nat.not_lt_zero _))
        (natLitToConstructor_looseBVarsBounded _ 0))
    | strLit hd =>
      exact .strLit (hd.congr_env (k := 0) (fun i hi => absurd hi (Nat.not_lt_zero _))
        (Ix.Kernel.strLitToConstructor_looseBVars _ 0))
  | proj s i e ih =>
    intro k c ρ0 ρ1 v hlo hhi h
    simp only [Expr.liftLooseBVars] at h
    cases h with
    | proj_table ht he => exact .proj_table ht (ih hlo hhi he)
    | proj_fst ht he => exact .proj_fst ht (ih hlo hhi he)
    | proj_snd ht he => exact .proj_snd ht (ih hlo hhi he)

/-- **Grading a lifted term**: a lifted term graded where the lifted indices are skipped is
graded. -/
theorem GradedBy.unliftO {σ : Nat → V} :
    ∀ (e : Expr md) {k c : Nat} {ρ0 ρ1 : BVarIdx → V},
      (∀ i, i < c → ρ1 i = ρ0 i) → (∀ i, c ≤ i → ρ1 (i + k) = ρ0 i) →
      GradedBy (DenotesO M.cval env φ σ) ρ1 (e.liftLooseBVars k c) →
      GradedBy (DenotesO M.cval env φ σ) ρ0 e := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro k c ρ0 ρ1 hlo hhi h
    simp only [Expr.liftLooseBVars, GradedBy] at h ⊢
    obtain ⟨hf, ha, r, A, F, X, B, hF, hX, hmem, hx, h0⟩ := h
    exact ⟨ihf hlo hhi hf, iha hlo hhi ha, r, A, F, X, B, DenotesO.unlift f hlo hhi hF,
      DenotesO.unlift a hlo hhi hX, hmem, hx, h0⟩
  | lam ty b _ ihty ihb =>
    intro k c ρ0 ρ1 hlo hhi h
    simp only [Expr.liftLooseBVars, GradedBy] at h ⊢
    exact ⟨ihty hlo hhi h.1, fun A hA x hx =>
      ihb (push_agree_lift x hlo hhi).1 (push_agree_lift x hlo hhi).2
        (h.2 A (hA.lift hlo hhi) x hx)⟩
  | forallE ty b _ ihty ihb =>
    intro k c ρ0 ρ1 hlo hhi h
    simp only [Expr.liftLooseBVars, GradedBy] at h ⊢
    exact ⟨ihty hlo hhi h.1, fun A hA x hx =>
      ihb (push_agree_lift x hlo hhi).1 (push_agree_lift x hlo hhi).2
        (h.2 A (hA.lift hlo hhi) x hx)⟩
  | proj s i e ih =>
    intro k c ρ0 ρ1 hlo hhi h
    simp only [Expr.liftLooseBVars, GradedBy] at h ⊢
    exact ih hlo hhi h
  | _ => intros; first | exact True.intro | simp only [GradedBy]

/-! ## Spines -/

theorem LeavesSub.mkAppN' {e : Expr md} : ∀ {as : List (Expr md)} {f : Expr md},
    LeavesSub f e → (∀ x ∈ as, LeavesSub x e) → LeavesSub (Expr.mkAppN f as) e
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha =>
    LeavesSub.mkAppN' (as := as) (f := .app f a)
      (fun l hl => by
        simp only [Expr.fvarLeaves, List.mem_append] at hl
        exact hl.elim (hf l) (ha a List.mem_cons_self l))
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))

/-- **A spine applied on its domains is graded**: a graded head applied along graded
arguments, whose values the head's value applies along on their domains. A proposition's
product is read with a truth value as each fibre. -/
theorem Gr.mkAppN_of_spineOk {σ : Nat → V} :
    ∀ {as : List (Expr md)} {f : Expr md} {F : V} {vs : List V},
      Gr M φ σ f → Den M φ σ f F → (∀ x ∈ as, Gr M φ σ x) → DenList M φ σ as vs →
      SpineOk F vs → Gr M φ σ (Expr.mkAppN f as)
  | [], _, _, _, hg, _, _, _, _ => hg
  | a :: as, f, F, _, hg, hF, hgs, .cons hx hxs, hok => by
    obtain ⟨⟨r, A, B, hFm, hxA⟩, hrest⟩ := SpineOk.cons_iff.1 hok
    have hga : Gr M φ σ (.app f a) := by
      refine Gr.app_iff.2 ⟨hg, hgs a List.mem_cons_self, ?_⟩
      by_cases hr : r = 0
      · subst hr
        refine ⟨0, A, F, _, fun _ => truthVal True, hF, hx, ?_, hxA, fun _ _ _ => ?_⟩
        · rw [eq_pt_of_mem_piR_zero hFm]
          exact pt_mem_piR_zero_of fun _ _ => pt_mem_truthVal trivial
        · rw [univ_zero]; exact truthVal_mem_univZero True
      · exact ⟨r, A, F, _, B, hF, hx, hFm, hxA, fun h => absurd h hr⟩
    exact Gr.mkAppN_of_spineOk hga (.app hF hx) (fun y hy => hgs y (List.mem_cons_of_mem _ hy))
      hxs hrest

/-- A list read pointwise is read. -/
theorem DenotesList.of_getD' {cval : Key md → (LevelParam → Nat) → V} {ρ : BVarIdx → V} :
    ∀ {es : List (Expr md)} {vs : List V}, es.length = vs.length →
      (∀ i, i < es.length → Denotes cval env φ ρ (es.getD i (.bvar 0)) (vs.getD i empty)) →
      DenotesList cval env φ ρ es vs
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => .cons (by simpa using h 0 (by simp))
      (DenotesList.of_getD' (by simpa using hl) fun i hi => by
        simpa using h (i + 1) (by simp only [List.length_cons]; omega))
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

theorem DenList.of_getD' {σ : Nat → V} :
    ∀ {es : List (Expr md)} {vs : List V}, es.length = vs.length →
      (∀ i, i < es.length → Den M φ σ (es.getD i (.bvar 0)) (vs.getD i empty)) →
      DenList M φ σ es vs
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => .cons (by simpa using h 0 (by simp))
      (DenList.of_getD' (by simpa using hl) fun i hi => by
        simpa using h (i + 1) (by simp only [List.length_cons]; omega))
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

end Ix.Kernel.Open
