module

public import IxC.Kernel.Model.Open.StructEta
import IxC.Kernel.Model.Open.Levels
import IxC.Kernel.Model.Iota
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

theorem eq_take_append_getD {α : Type _} (d : α) : ∀ {l : List α} {n : Nat}, l.length = n + 1 →
    l = l.take n ++ [l.getD n d]
  | [], _, h => by simp at h
  | [_], 0, _ => by simp
  | _ :: _ :: _, 0, h => by simp at h
  | x :: xs, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.take_succ_cons, List.getD_cons_succ, List.cons_append, ← eq_take_append_getD (l := xs) (n := n) d h]

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
      ∃ R : Expr md, R' = R.instantiateLevelParams ks us ∧
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
    ∃ R : Expr md, R' = R.instantiateLevelParams ks us ∧
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
      ∃ (F : V) (vs : List V), DenotesO M.cval env φ σ ρ f F ∧
        (∀ k, k < as.length → DenotesO M.cval env φ σ ρ (as.getD k (.bvar 0)) (vs.getD k empty)) ∧
        vs.length = as.length ∧ W = vs.foldl app F
  | [], _, _, h => ⟨_, [], h, fun k hk => absurd hk (Nat.not_lt_zero _), rfl, rfl⟩
  | a :: as, f, _, h => by
    obtain ⟨F', vs, hF', hvs, hlen, rfl⟩ := DenotesO.mkAppN_inv' (as := as) (f := .app f a) h
    cases hF' with
    | app hF hX =>
      refine ⟨_, _ :: vs, hF, fun k hk => ?_, by simp only [List.length_cons, hlen], rfl⟩
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
        (h.2 A (DenotesO.lift hA hlo hhi) x hx)⟩
  | forallE ty b _ ihty ihb =>
    intro k c ρ0 ρ1 hlo hhi h
    simp only [Expr.liftLooseBVars, GradedBy] at h ⊢
    exact ⟨ihty hlo hhi h.1, fun A hA x hx =>
      ihb (push_agree_lift x hlo hhi).1 (push_agree_lift x hlo hhi).2
        (h.2 A (DenotesO.lift hA hlo hhi) x hx)⟩
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
    exact Gr.mkAppN_of_spineOk (as := as) (f := .app f a) hga (.app hF hx) (fun y hy => hgs y (List.mem_cons_of_mem _ hy))
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


theorem hasFvar_mkAppN_false : ∀ {as : List (Expr md)} {f : Expr md},
    (Expr.mkAppN f as).hasFvar = false → f.hasFvar = false ∧ ∀ x ∈ as, x.hasFvar = false
  | [], _, h => ⟨h, fun _ hx => nomatch hx⟩
  | b :: bs, f, h => by
    obtain ⟨h1, h2⟩ := hasFvar_mkAppN_false (as := bs) (f := .app f b) h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h1
    refine ⟨h1.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1.2
    · exact h2 x hx

theorem getD_take_lt {α : Type _} {l : List α} {n i : Nat} (d : α) (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp only [List.getD, List.getElem?_take_of_lt h]

/-! ## ι -/

set_option maxHeartbeats 3200000 in
/-- **ι** (`Red.iota`): a stored recursor applied to its telescope and a constructor
application, the major premise, reduces to the rule's right-hand side at the prefix and the
constructor's fields. -/
theorem Red.iota_sound (hse : StoredEnv env) {d : Nat} {e : Expr md} {c : Key md}
    {us : List Level} {cv : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    {major : Expr md} {cj : Key md} {usj : List Level} {cvj : ConstantVal md}
    {cnP cnF : Nat} {rl : RecRule md} {residual : Expr md}
    (hhead : e.getAppFn = .const c us)
    (hrec : env.find? c = some (.recInfo cv mI rP rules))
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = cv.levelParams.length)
    (hmajor : RedS M φ d (e.getAppArgs.getD mI (.bvar 0)) major)
    (hmhead : major.getAppFn = .const cj usj)
    (hctor : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmlen : major.getAppArgs.length = rl.ctorParams + rl.nfields)
    (hfire : rl.fire ≠ .inert)
    (hlv : ∀ φ, Level.EvalEqList φ usj
      (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).1)
    (hparams : rl.compareParams = true →
      DefEqListS M φ d (major.getAppArgs.take rl.ctorParams)
        (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).2)
    (hcertR : CertsS M φ d true (cv.type.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take mI ++ [major]))
    (hcertC : CertsS M φ d true (cvj.type.instantiateLevelParams cvj.levelParams usj)
      major.getAppArgs)
    (hres : mI ≠ rP → piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
      major.getAppArgs = some residual)
    (hidx : mI ≠ rP → DefEqListS M φ d (residual.getAppArgs.drop rl.ctorParams)
      ((e.getAppArgs.take mI).drop rP)) :
    RedS M φ d e (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)) := by
  have hrmem : rl ∈ rules := List.mem_of_find?_eq_some hrule
  have hrctor : rl.ctor = cj := by
    have := List.find?_some hrule
    simpa using this
  subst hrctor
  obtain ⟨hrPmI, hctorF, hnestF⟩ := hse.rules c cv mI rP rules hrec rl hrmem hfire
  obtain ⟨rfl, rfl, hteleC, hplainF⟩ := hctorF cvj cnP cnF hctor
  have harity := hse.arities.2 c cv mI rP rules hrec rl hrmem hfire
  have hmemR := List.mem_of_find?_eq_some hrec
  have hmemC := List.mem_of_find?_eq_some hctor
  have hrhsC := (hse.closed _ hmemR).2.2 cv mI rP rules rfl rl hrmem
  have hrhsF : (rl.rhs.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hrhsC.1
  have hrhsB : (rl.rhs.instantiateLevelParams cv.levelParams us).looseBVarsBounded 0 = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hrhsC.2
  intro hf
  have hfargs := Frame.getAppArgs hf
  have hmIlt : mI < e.getAppArgs.length := by omega
  have hmaMem := getD_mem_of_lt (.bvar 0) hmIlt
  obtain ⟨hfmaj, hsubmaj, kmaj⟩ := hmajor (hfargs _ hmaMem)
  have hfmargs := Frame.getAppArgs hfmaj
  have hargsMem : ∀ x ∈ e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams,
      x ∈ e.getAppArgs ∨ x ∈ major.getAppArgs := fun x hx =>
    (List.mem_append.mp hx).imp List.mem_of_mem_take List.mem_of_mem_drop
  refine ⟨Frame.mkAppN (Frame.of_closed hrhsF hrhsB)
      (fun x hx => (hargsMem x hx).elim (hfargs x) (hfmargs x)),
    LeavesSub.mkAppN' (LeavesSub.of_closed hrhsF) (fun x hx => (hargsMem x hx).elim
      (fun h l hl => fvarLeaves_getAppArgs h l hl)
      (fun h l hl => fvarLeaves_getAppArgs hmaMem l (hsubmaj l (fvarLeaves_getAppArgs h l hl)))),
    fun σ hC v hv hg => ?_⟩
  -- the redex's spine
  have hsp := eq_mkAppN_of_getAppFn hhead
  have hv' : Den M φ σ (Expr.mkAppN (.const c us) e.getAppArgs) v := by rw [← hsp]; exact hv
  have hg' : Gr M φ σ (Expr.mkAppN (.const c us) e.getAppArgs) := by rw [← hsp]; exact hg
  obtain ⟨R, vs, hR, hvs, rfl⟩ := Den.mkAppN_inv hv'
  have hgargs := Gr.mkAppN_args hg'
  have hCargs := hC.getAppArgs
  have hvslen : vs.length = mI + 1 := by rw [← hvs.length_eq, hlen]
  have hvsplit := eq_take_append_getD (empty : V) hvslen
  have hxs : DenList M φ σ (e.getAppArgs.take mI) (vs.take mI) := hvs.take mI
  have hm0 := DenList.getD hvs hmIlt
  -- the prepared major premise
  have hCma : Ctx M φ σ (e.getAppArgs.getD mI (.bvar 0)) := hCargs _ hmaMem
  obtain ⟨hdmaj, hgmaj⟩ := kmaj σ hCma _ hm0 (hgargs _ hmaMem)
  have hCmaj : Ctx M φ σ major := hCma.of_subset hsubmaj
  have hspm := eq_mkAppN_of_getAppFn hmhead
  have hdmaj' : Den M φ σ (Expr.mkAppN (.const rl.ctor usj) major.getAppArgs)
      (vs.getD mI empty) := by rw [← hspm]; exact hdmaj
  have hgmaj' : Gr M φ σ (Expr.mkAppN (.const rl.ctor usj) major.getAppArgs) := by
    rw [← hspm]; exact hgmaj
  obtain ⟨K, ys, hK, hys, hm0eq⟩ := Den.mkAppN_inv hdmaj'
  -- the two constants
  obtain ⟨TR, hcR, hTR, hgTR, hRmem⟩ := const_typed (M := M) (φ := φ) hse.closed hrec hus σ
  obtain rfl := DenotesO.functional hR hcR
  have hlenusj : usj.length = cvj.levelParams.length := by
    cases hK with
    | const hf hl => rw [hctor] at hf; cases hf; exact hl
  obtain ⟨TC, hcC, hTC, hgTC, hKmem⟩ := const_typed (M := M) (φ := φ) hse.closed hctor hlenusj σ
  obtain rfl := DenotesO.functional hK hcC
  -- the recursor's walk, a fit split at the major premise
  have hTRf : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact (hse.closed _ hmemR).1.1
  have hfTR := (const_type_frame (d := d) (us := us) hse.closed hrec).1
  have hargsR : ∀ x ∈ e.getAppArgs.take mI ++ [major],
      Frame d x ∧ Ctx M φ σ x ∧ Gr M φ σ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx' := List.mem_of_mem_take hx
      exact ⟨hfargs x hx', hCargs x hx', hgargs x hx'⟩
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hfmaj, hCmaj, hgmaj⟩
  have hdR : DenList M φ σ (e.getAppArgs.take mI ++ [major]) (vs.take mI ++ [vs.getD mI empty]) :=
    DenList.append hxs (.cons hdmaj .nil)
  have hspR : SpineOk (M.cval c (Level.substFn φ cv.levelParams us))
      (vs.take mI ++ [vs.getD mI empty]) := by
    rw [← hvsplit]; exact spineOk_of_graded hg' hcR hvs
  have hwalkR := hcertR hfTR (fun x hx => (hargsR x hx).1) σ (Ctx.of_closed hTRf)
    (fun x hx => (hargsR x hx).2.1) TR hTR hgTR _ hdR (fun x hx => (hargsR x hx).2.2)
    (fun _ => ⟨_, hRmem, hspR⟩)
  have hlenR : (e.getAppArgs.take mI ++ [major]).length = mI + 1 := by
    simp only [List.length_append, List.length_take, List.length_singleton, hlen]; omega
  obtain ⟨σR1, RR1, hfitO1⟩ := hwalkR.fitsO hdR (fun x hx => (hargsR x hx).1.2.1)
    (by rw [hlenR]; exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ harity)
  obtain ⟨σR, dom, body, mdom, X, hfitRO, hXO, hm0X⟩ := FitsO.split_snoc (vs.take mI) hfitO1
  have hxslen : (vs.take mI).length = mI := by rw [List.length_take]; omega
  have hfitR := hfitRO.to_fits hTRf
  obtain ⟨bsR, hsR⟩ := Fits.stripPis_eq hfitR
  rw [hxslen] at hsR
  have hσR : σR = pushVals ρ₀ (vs.take mI) := hfitRO.env_eq
  -- the major premise's domain: the stored type's, at the rule's comparand levels
  obtain ⟨pre0, dom0, body0, bm0, D0, L0, hs0, hfn0, hL0⟩ : ∃ (pre0 : List (Expr md × BinderMeta))
      (dom0 body0 : Expr md) (bm0 : BinderMeta) (D0 : Key md) (L0 : List Level),
      cv.type.stripPis mI = some (pre0, .forallE dom0 body0 bm0) ∧
      dom0.getAppFn = .const D0 L0 ∧
      L0.map (Level.subst cv.levelParams us) =
        (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).1 := by
    cases hfr : rl.fire with
    | inert => exact absurd hfr hfire
    | plain =>
      obtain ⟨pre0, dom0, body0, bm0, D0, hs0, hfn0, -⟩ := recRulePlain_shapeT (hplainF hfr)
      refine ⟨pre0, dom0, body0, bm0, D0, _, hs0, hfn0, ?_⟩
      rw [recFireComparands_plain hfr, List.map_map]
      rfl
    | nested lvls pins =>
      obtain ⟨-, -, pre0, dom0, body0, bm0, D0, hs0, hfn0, -⟩ := hnestF lvls pins hfr
      exact ⟨pre0, dom0, body0, bm0, D0, _, hs0, hfn0, (recFireComparands_nested hfr).symm⟩
  obtain ⟨hdomEq, -⟩ := Expr.stripPis_instantiateLevelParams_eq cv.levelParams us mI hs0 hsR
  simp only [Expr.instantiateLevelParams] at hdomEq
  obtain ⟨rfl, -, -⟩ := Expr.forallE.inj hdomEq
  have hdomFn : (dom0.instantiateLevelParams cv.levelParams us).getAppFn =
      .const D0 (L0.map (Level.subst cv.levelParams us)) := by
    rw [Expr.getAppFn_instantiateLevelParams, hfn0]; rfl
  have hlvφ := hlv φ
  rw [← hL0] at hlvφ
  have hsubst : Level.substFn φ cvj.levelParams usj =
      Level.substFn φ cvj.levelParams (L0.map (Level.subst cv.levelParams us)) :=
    Ix.Kernel.Level.substFn_congr hlvφ
  have hlsLen : (L0.map (Level.subst cv.levelParams us)).length = cvj.levelParams.length := by
    rw [← Ix.Kernel.Level.EvalEqList.length_eq hlvφ]; exact hlenusj
  -- the domain's arguments, read and graded at the fit's environment
  have hdomF : (dom0.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    have := hfitRO.hasFvar hTRf
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at this
    exact this.1
  have hgdom : GradedBy (DenotesO M.cval env φ σ) σR (dom0.instantiateLevelParams cv.levelParams us) := by
    have := hfitRO.graded hgTR
    simp only [GradedBy] at this
    exact this.1
  have hdomSp := eq_mkAppN_of_getAppFn hdomFn
  have hXO' : DenotesO M.cval env φ σ σR (Expr.mkAppN (.const D0 (L0.map (Level.subst cv.levelParams us)))
      (dom0.instantiateLevelParams cv.levelParams us).getAppArgs) X := by rw [← hdomSp]; exact hXO
  have hgdom' : GradedBy (DenotesO M.cval env φ σ) σR
      (Expr.mkAppN (.const D0 (L0.map (Level.subst cv.levelParams us)))
        (dom0.instantiateLevelParams cv.levelParams us).getAppArgs) := by rw [← hdomSp]; exact hgdom
  obtain ⟨FD, wsD, -, hwsD, hwsDlen, -⟩ := DenotesO.mkAppN_inv' hXO'
  have hgwsD := GradedBy.mkAppN_args' hgdom'
  have hdomArgsF := (hasFvar_mkAppN_false (by rw [← hdomSp]; exact hdomF)).2
  -- the constructor's walk, a fit, at the domain's levels
  have hCtyF : cvj.type.hasFvar = false := (hse.closed _ hmemC).1.1
  have hTCf : (cvj.type.instantiateLevelParams cvj.levelParams usj).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hCtyF
  have hfTC := (const_type_frame (d := d) (us := usj) hse.closed hctor).1
  have hwalkC := hcertC hfTC hfmargs σ (Ctx.of_closed hTCf) hCmaj.getAppArgs TC hTC hgTC ys hys
    (Gr.mkAppN_args hgmaj') (fun _ => ⟨_, hKmem, spineOk_of_graded hgmaj' hK hys⟩)
  have hyslen : ys.length = rl.ctorParams + rl.nfields := by rw [← hys.length_eq, hmlen]
  obtain ⟨bsT, R0, cH, uH, hsT, hhead0⟩ := Expr.ctorTeleOk_head hteleC
  obtain ⟨as0, rfl⟩ : ∃ as0, R0 = Expr.mkAppN (.const cH uH) as0 :=
    ⟨_, eq_mkAppN_of_getAppFn hhead0⟩
  obtain ⟨σC, RC1, hfitCO⟩ := hwalkC.fitsO hys (fun x hx => (hfmargs x hx).2.1)
    (by rw [hmlen]; exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ (by rw [hsT]; rfl))
  have hσC : σC = pushVals ρ₀ ys := hfitCO.env_eq
  have hRC1 : RC1 = (Expr.mkAppN (.const cH uH) as0).instantiateLevelParams cvj.levelParams usj := by
    obtain ⟨bs1, hs1⟩ := Fits.stripPis_eq (hfitCO.to_fits hTCf)
    rw [hyslen] at hs1
    exact (Expr.stripPis_instantiateLevelParams_eq cvj.levelParams usj _ hsT hs1).1
  subst hRC1
  obtain ⟨RC0, -, hfitC⟩ := Fits.congr_instLP M.cval_params hsubst hCtyF (hfitCO.to_fits hTCf)
  have hRCls : RC0.instantiateLevelParams cvj.levelParams (L0.map (Level.subst cv.levelParams us)) =
      (Expr.mkAppN (.const cH uH) as0).instantiateLevelParams cvj.levelParams
        (L0.map (Level.subst cv.levelParams us)) := by
    obtain ⟨bs2, hs2⟩ := Fits.stripPis_eq hfitC
    rw [hyslen] at hs2
    exact (Expr.stripPis_instantiateLevelParams_eq cvj.levelParams _ _ hsT hs2).1
  rw [hRCls] at hfitC
  -- the residual's arguments, read and graded at the constructor fit's environment
  obtain ⟨WC, hWC⟩ := hfitCO.residual hTC
  have hgRC := hfitCO.graded hgTC
  rw [instantiateLevelParams_mkAppN] at hWC hgRC
  simp only [Expr.instantiateLevelParams] at hWC hgRC
  obtain ⟨FC, wsC, -, hwsC, hwsClen, -⟩ := DenotesO.mkAppN_inv' hWC
  have hgwsC := GradedBy.mkAppN_args' hgRC
  have hRCF : ((Expr.mkAppN (.const cH uH) as0).instantiateLevelParams cvj.levelParams usj).hasFvar
      = false := hfitCO.hasFvar hTCf
  rw [instantiateLevelParams_mkAppN] at hRCF
  have has0F := (hasFvar_mkAppN_false hRCF).2
  -- the law's premises
  have hKls : Denotes M.cval env φ ρ₀ (.const rl.ctor (L0.map (Level.subst cv.levelParams us)))
      (M.cval rl.ctor (Level.substFn φ cvj.levelParams usj)) := by
    rw [hsubst]; exact .const hctor hlsLen
  have hmaj : ys.foldl app (M.cval rl.ctor (Level.substFn φ cvj.levelParams usj)) ∈ˢ X := by
    have hm0eq' : vs.getD mI empty =
        ys.foldl app (M.cval rl.ctor (Level.substFn φ cvj.levelParams usj)) := hm0eq
    rw [← hm0eq']; exact hm0X
  have hparD : rl.compareParams = true →
      DenotesList M.cval env φ σR
        ((dom0.instantiateLevelParams cv.levelParams us).getAppArgs.take rl.ctorParams)
        (ys.take rl.ctorParams) := by
    intro hcmp
    obtain ⟨hlenP, kP⟩ := hparams hcmp
    have hlenYs : (major.getAppArgs.take rl.ctorParams).length = rl.ctorParams := by
      rw [List.length_take, hmlen]; omega
    cases hfr : rl.fire with
    | inert => exact absurd hfr hfire
    | plain =>
      have hpl := hplainF hfr
      have hcpR := recRulePlain_leT hpl
      obtain ⟨pre0', dom0', body0', bm0', D0', hs0', -, hargs0⟩ := recRulePlain_shapeT hpl
      rw [hs0] at hs0'
      have hs0'' := Option.some.inj hs0'
      simp only [Prod.mk.injEq, Expr.forallE.injEq] at hs0''
      obtain ⟨-, rfl, -, -⟩ := hs0''
      have hcmpEq : (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).2 =
          e.getAppArgs.take rl.ctorParams := by
        unfold recFireComparands; rw [hfr]
      rw [hcmpEq] at kP hlenP
      have hval := kP (fun x hx => hfmargs x (List.mem_of_mem_take hx))
        (fun x hx => hfargs x (List.mem_of_mem_take hx)) σ
        (fun x hx => hCmaj.getAppArgs x (List.mem_of_mem_take hx))
        (fun x hx => hCargs x (List.mem_of_mem_take hx)) _ _ (hys.take _) (hvs.take _)
        (fun x hx => Gr.mkAppN_args hgmaj' x (List.mem_of_mem_take hx))
        (fun x hx => hgargs x (List.mem_of_mem_take hx))
      have hargsI : (dom0.instantiateLevelParams cv.levelParams us).getAppArgs.take rl.ctorParams =
          (List.range rl.ctorParams).map (fun k => Expr.bvar (mI - 1 - k)) := by
        rw [Expr.getAppArgs_instantiateLevelParams, ← List.map_take, hargs0]
        simp [Function.comp_def, Expr.instantiateLevelParams]
      rw [hargsI]
      refine DenotesList.of_getD' (by
          simp only [List.length_map, List.length_range, List.length_take, hyslen]; omega)
        fun i hi => ?_
      have hi' : i < rl.ctorParams := by simpa using hi
      have hget : ((List.range rl.ctorParams).map (fun k => Expr.bvar (mI - 1 - k))).getD i
          (.bvar 0) = (Expr.bvar (mI - 1 - i) : Expr md) := by
        simp [List.getD, List.getElem?_range hi']
      have hyv : (ys.take rl.ctorParams).getD i empty = pushVals ρ₀ (vs.take mI) (mI - 1 - i) := by
        rw [getD_take_lt _ hi', Ix.Kernel.pushVals_lt _ _ _ empty (by rw [hxslen]; omega), hxslen,
          show mI - 1 - (mI - 1 - i) = i by omega, getD_take_lt _ (by omega)]
        have := congrArg (fun l => l.getD i (empty : V)) hval
        simpa only [getD_take_lt _ hi'] using this
      rw [hget, hyv, ← hσR]
      exact .bvar
    | nested lvls pins =>
      obtain ⟨hpinsLen, hpinsWF, pre0', dom0', body0', bm0', D0', hs0', -, hargs0⟩ :=
        hnestF lvls pins hfr
      rw [hs0] at hs0'
      have hs0'' := Option.some.inj hs0'
      simp only [Prod.mk.injEq, Expr.forallE.injEq] at hs0''
      obtain ⟨-, rfl, -, -⟩ := hs0''
      have hcmpEq : (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).2 =
          pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            (p.instantiateLevelParams cv.levelParams us)) := by
        unfold recFireComparands; rw [hfr]
      rw [hcmpEq] at kP hlenP
      have hprelen : (e.getAppArgs.take rP).length = rP := by rw [List.length_take]; omega
      have hpreB : ∀ a ∈ e.getAppArgs.take rP, a.looseBVarsBounded 0 = true :=
        fun a ha => (hfargs a (List.mem_of_mem_take ha)).2.1
      have hpreG : ∀ a ∈ e.getAppArgs.take rP, Gr M φ σ a :=
        fun a ha => hgargs a (List.mem_of_mem_take ha)
      have hpreD : DenList M φ σ (e.getAppArgs.take rP) (vs.take rP) := hvs.take rP
      -- the environment of the prefix, and the fit's as it lifted past the indices
      have hτ : σR = pushVals (pushVals ρ₀ (vs.take rP)) ((vs.take mI).drop rP) := by
        have htt : (vs.take mI).take rP = vs.take rP := by
          rw [List.take_take, Nat.min_eq_left hrPmI]
        rw [hσR, ← htt, ← Ix.Kernel.pushVals_append, List.take_append_drop]
      have hzlen : ((vs.take mI).drop rP).length = mI - rP := by
        rw [List.length_drop, hxslen]
      have hagree : ∀ i, 0 ≤ i → σR (i + (mI - rP)) = pushVals ρ₀ (vs.take rP) i := by
        intro i _
        rw [hτ, Ix.Kernel.pushVals_ge _ _ _ (by rw [hzlen]; omega), hzlen, Nat.add_sub_cancel]
      have hdomArg : ∀ i, i < rl.ctorParams →
          (dom0.instantiateLevelParams cv.levelParams us).getAppArgs.getD i (.bvar 0) =
            ((pins.getD i (.bvar 0)).instantiateLevelParams cv.levelParams us).liftLooseBVars
              (mI - rP) 0 := by
        intro i hi
        have hi2 : i < pins.length := by omega
        rw [Expr.getAppArgs_instantiateLevelParams, hargs0]
        simp [List.getD, List.getElem?_append_left, List.getElem?_map, List.getElem?_eq_getElem hi2,
          hi2, Ix.Kernel.Model.instantiateLevelParams_liftLooseBVars]
      -- each comparand reads, gradedly, what the domain's argument reads
      have hcmpRead : ∀ i, i < rl.ctorParams →
          Den M φ σ ((pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us))).getD i (.bvar 0)) (wsD.getD i empty) ∧
            Gr M φ σ ((pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us))).getD i (.bvar 0)) := by
        intro i hi
        have hiD : i < (dom0.instantiateLevelParams cv.levelParams us).getAppArgs.length := by
          rw [Expr.getAppArgs_instantiateLevelParams, hargs0]
          simp only [List.length_map, List.length_append, List.length_range, hpinsLen]; omega
        have hd := hwsD i hiD
        have hgd := hgwsD _ (getD_mem_of_lt (.bvar 0) hiD)
        rw [hdomArg i hi] at hd hgd
        have hd' := DenotesO.unlift _ (k := mI - rP) (c := 0)
          (fun j hj => absurd hj (Nat.not_lt_zero _)) hagree hd
        have hgd' := GradedBy.unliftO _ (k := mI - rP) (c := 0)
          (fun j hj => absurd hj (Nat.not_lt_zero _)) hagree hgd
        have hgetC : (pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            (p.instantiateLevelParams cv.levelParams us))).getD i (.bvar 0) =
            Expr.instSpine (e.getAppArgs.take rP) ((e.getAppArgs.take rP).length - 1)
              ((pins.getD i (.bvar 0)).instantiateLevelParams cv.levelParams us) := by
          rw [hprelen]
          simp [List.getD, List.getElem?_map, List.getElem?_eq_getElem (show i < pins.length by omega)]
        rw [hgetC]
        exact ⟨(DenotesO.instSpine hpreD hpreB _ ρ₀ _).2 hd',
          (GradedBy.instSpineO hpreD hpreB hpreG _ ρ₀).2 hgd'⟩
      have hcmpLen : (pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us))).length = rl.ctorParams := by
        rw [List.length_map, hpinsLen]
      have hcmpMem : ∀ x ∈ pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)), ∃ p ∈ pins,
            x = Expr.instSpine (e.getAppArgs.take rP) ((e.getAppArgs.take rP).length - 1)
              (p.instantiateLevelParams cv.levelParams us) := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact ⟨p, hp, by rw [hprelen]⟩
      have hpinB : ∀ p ∈ pins, (p.instantiateLevelParams cv.levelParams us).looseBVarsBounded
          (e.getAppArgs.take rP).length = true := fun p hp => by
        rw [Expr.looseBVarsBounded_instantiateLevelParams, hprelen]; exact (hpinsWF p hp).2
      have hpinF : ∀ p ∈ pins, (p.instantiateLevelParams cv.levelParams us).hasFvar = false :=
        fun p hp => by rw [Expr.hasFvar_instantiateLevelParams]; exact (hpinsWF p hp).1
      have hval := kP (fun x hx => hfmargs x (List.mem_of_mem_take hx))
        (fun x hx => by
          obtain ⟨p, hp, rfl⟩ := hcmpMem x hx
          exact ⟨Ix.Kernel.instSpine_WScoped _ (Expr.WScoped.of_not_hasFvar (hpinF p hp))
              (fun y hy => (hfargs y (List.mem_of_mem_take hy)).1),
            Ix.Kernel.instSpine_closed hpreB (hpinB p hp),
            fun l hl => by
              rcases Ix.Kernel.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
              · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinF p hp)] at hl'; exact nomatch hl'
              · exact (hfargs y (List.mem_of_mem_take hy)).2.2 l hly⟩)
        σ (fun x hx => hCmaj.getAppArgs x (List.mem_of_mem_take hx))
        (fun x hx => by
          obtain ⟨p, hp, rfl⟩ := hcmpMem x hx
          intro l hl
          rcases Ix.Kernel.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
          · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinF p hp)] at hl'; exact nomatch hl'
          · exact hCargs y (List.mem_of_mem_take hy) l hly)
        _ (wsD.take rl.ctorParams) (hys.take _)
        (DenList.of_getD' (by
            rw [hcmpLen, List.length_take, hwsDlen, Expr.getAppArgs_instantiateLevelParams, hargs0]
            simp only [List.length_map, List.length_append, List.length_range, hpinsLen]; omega)
          fun i hi => by
            rw [hcmpLen] at hi
            rw [getD_take_lt _ hi]; exact (hcmpRead i hi).1)
        (fun x hx => Gr.mkAppN_args hgmaj' x (List.mem_of_mem_take hx))
        (fun x hx => by
          obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
          have hi' : i < rl.ctorParams := by rw [hcmpLen] at hi; exact hi
          have h := (hcmpRead i hi').2
          simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some, hxi] at h
          exact h)
      refine DenotesList.of_getD' (by
          rw [List.length_take, List.length_take, hyslen, Expr.getAppArgs_instantiateLevelParams,
            hargs0]
          simp only [List.length_map, List.length_append, List.length_range, hpinsLen]; omega) fun i hi => ?_
      have hi' : i < rl.ctorParams := by
        simp only [List.length_take] at hi; omega
      rw [getD_take_lt _ hi', getD_take_lt _ hi']
      have hyv : ys.getD i empty = wsD.getD i empty := by
        have := congrArg (fun l => l.getD i (empty : V)) hval
        simpa only [getD_take_lt _ hi'] using this
      rw [hyv]
      have hiD : i < (dom0.instantiateLevelParams cv.levelParams us).getAppArgs.length := by
        rw [Expr.getAppArgs_instantiateLevelParams, hargs0]
        simp only [List.length_map, List.length_append, List.length_range, hpinsLen]; omega
      exact (hwsD i hiD).to_denotes (hdomArgsF _ (getD_mem_of_lt (.bvar 0) hiD))
  have hidxD : mI ≠ rP → DenotesList M.cval env φ σC
      (((Expr.mkAppN (.const cH uH) as0).instantiateLevelParams cvj.levelParams
        (L0.map (Level.subst cv.levelParams us))).getAppArgs.drop rl.ctorParams)
      ((vs.take mI).drop rP) := by
    intro hmr
    obtain ⟨hlenI, kI⟩ := hidx hmr
    obtain ⟨bs1, hs1⟩ := Fits.stripPis_eq (hfitCO.to_fits hTCf)
    rw [hyslen, ← hmlen] at hs1
    have hresEq := piResidual_of_stripPis major.getAppArgs hs1
    rw [hres hmr] at hresEq
    have hresV := Option.some.inj hresEq
    rw [instantiateLevelParams_mkAppN] at hresV
    simp only [Expr.instantiateLevelParams] at hresV
    rw [instSpine_mkAppN_const] at hresV
    have hresArgs : residual.getAppArgs = (as0.map (·.instantiateLevelParams cvj.levelParams usj)).map
        (Expr.instSpine major.getAppArgs (major.getAppArgs.length - 1)) := by
      rw [hresV, Expr.getAppArgs_mkAppN]; simp [Expr.getAppArgs]
    have hmB : ∀ a ∈ major.getAppArgs, a.looseBVarsBounded 0 = true := fun a ha => (hfmargs a ha).2.1
    have hmG : ∀ a ∈ major.getAppArgs, Gr M φ σ a := Gr.mkAppN_args hgmaj'
    -- the residual: framed and inside the major premise's free variables
    have hres' := hres hmr
    have hfres : Frame d residual :=
      ⟨Ix.Kernel.piResidual_WScoped hres' hfTC.1 (fun x hx => (hfmargs x hx).1),
        Ix.Kernel.piResidual_looseBVars hres' hfTC.2.1 hmB,
        fun l hl => (Ix.Kernel.piResidual_fvarLeaves hres' l hl).elim
          (fun h => by rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hTCf] at h; exact nomatch h)
          (fun ⟨x, hx, hlx⟩ => (hfmargs x hx).2.2 l hlx)⟩
    have hCres : Ctx M φ σ residual := fun l hl =>
      (Ix.Kernel.piResidual_fvarLeaves hres' l hl).elim
        (fun h => by rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hTCf] at h; exact nomatch h)
        (fun ⟨x, hx, hlx⟩ => hCmaj.getAppArgs x hx l hlx)
    have hresRead : ∀ i, i < as0.length →
        Den M φ σ (residual.getAppArgs.getD i (.bvar 0)) (wsC.getD i empty) ∧
          Gr M φ σ (residual.getAppArgs.getD i (.bvar 0)) := by
      intro i hi
      have hiC : i < (as0.map (·.instantiateLevelParams cvj.levelParams usj)).length := by
        simpa using hi
      have hget : residual.getAppArgs.getD i (.bvar 0) = Expr.instSpine major.getAppArgs
          (major.getAppArgs.length - 1)
          ((as0.map (·.instantiateLevelParams cvj.levelParams usj)).getD i (.bvar 0)) := by
        rw [hresArgs, List.getD, List.getElem?_map, List.getD, List.getElem?_eq_getElem hiC]
        rfl
      rw [hget]
      have hd := hwsC i hiC
      have hgd := hgwsC _ (getD_mem_of_lt (.bvar 0) hiC)
      rw [hσC] at hd hgd
      exact ⟨(DenotesO.instSpine hys hmB _ ρ₀ _).2 hd, (GradedBy.instSpineO hys hmB hmG _ ρ₀).2 hgd⟩
    have hresLen : residual.getAppArgs.length = as0.length := by rw [hresArgs]; simp
    have hval := kI (fun x hx => Frame.getAppArgs hfres x (List.mem_of_mem_drop hx))
      (fun x hx => hfargs x (List.mem_of_mem_take (List.mem_of_mem_drop hx))) σ
      (fun x hx => hCres.getAppArgs x (List.mem_of_mem_drop hx))
      (fun x hx => hCargs x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
      (wsC.drop rl.ctorParams) _
      ((DenList.of_getD' (by rw [hresLen, hwsClen]; simp) fun i hi => by
          rw [hresLen] at hi; exact (hresRead i hi).1).drop _)
      (hxs.drop rP)
      (fun x hx => by
        obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem (List.mem_of_mem_drop hx)
        rw [← hxi]
        have := (hresRead i (by rw [← hresLen]; exact hi)).2
        simp only [List.getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
        exact this)
      (fun x hx => hgargs x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
    rw [← hval]
    rw [instantiateLevelParams_mkAppN, Expr.getAppArgs_mkAppN]
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs, List.nil_append]
    refine DenotesList.of_getD' (by simp [hwsClen]) fun i hi => ?_
    simp only [List.length_drop, List.length_map] at hi
    have hiC : rl.ctorParams + i < (as0.map (·.instantiateLevelParams cvj.levelParams usj)).length := by
      simp; omega
    have hd := hwsC _ hiC
    rw [show ((as0.map (·.instantiateLevelParams cvj.levelParams
        (L0.map (Level.subst cv.levelParams us)))).drop rl.ctorParams).getD i (.bvar 0) =
        (as0.getD (rl.ctorParams + i) (.bvar 0)).instantiateLevelParams cvj.levelParams
          (L0.map (Level.subst cv.levelParams us)) by
      simp [List.getD, List.getElem?_drop, List.getElem?_map,
        List.getElem?_eq_getElem (show rl.ctorParams + i < as0.length by simpa using hiC)]]
    rw [show (wsC.drop rl.ctorParams).getD i empty = wsC.getD (rl.ctorParams + i) empty by
      simp [List.getD, List.getElem?_drop]]
    have hgetU : (as0.map (·.instantiateLevelParams cvj.levelParams usj)).getD (rl.ctorParams + i)
        (.bvar 0) = (as0.getD (rl.ctorParams + i) (.bvar 0)).instantiateLevelParams
          cvj.levelParams usj := by
      simp [List.getD, List.getElem?_map,
        List.getElem?_eq_getElem (show rl.ctorParams + i < as0.length by simpa using hiC)]
    rw [hgetU] at hd
    have haF : (as0.getD (rl.ctorParams + i) (.bvar 0)).hasFvar = false := by
      have := has0F _ (getD_mem_of_lt (.bvar 0) hiC)
      rw [hgetU, Expr.hasFvar_instantiateLevelParams] at this
      exact this
    have hd' := (DenotesO.instantiateLevelParams M.cval_params _ _ _ _ _).1 hd
    rw [hsubst] at hd'
    have hd'' := (DenotesO.instantiateLevelParams M.cval_params _ _ _ _ _).2 hd'
    exact hd''.to_denotes (by rw [Expr.hasFvar_instantiateLevelParams]; exact haF)
  -- the law
  obtain ⟨H, hH, hgH, hspH, heq⟩ := M.iota_rule c cv mI rP rules rl hrec hrmem cvj rl.ctorParams
    rl.nfields hctor us φ ρ₀ σR σC (vs.take mI) ys (dom0.instantiateLevelParams cv.levelParams us)
    body _ mdom D0 (L0.map (Level.subst cv.levelParams us))
    (M.cval c (Level.substFn φ cv.levelParams us))
    (M.cval rl.ctor (Level.substFn φ cvj.levelParams usj)) X hus hxslen hyslen
    (hcR.to_denotes rfl) hfitR hdomFn (hXO.to_denotes hdomF) hKls hfitC hmaj hparD hidxD
  -- the reduct
  have hred : DenList M φ σ (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)
      ((vs.take mI).take rP ++ ys.drop rl.ctorParams) := by
    rw [List.take_take, Nat.min_eq_left hrPmI]
    exact DenList.append (hvs.take rP) (hys.drop _)
  have hHO : Den M φ σ (rl.rhs.instantiateLevelParams cv.levelParams us) H :=
    DenotesO.of_denotes hH
  have hleft : vs.foldl app (M.cval c (Level.substFn φ cv.levelParams us)) =
      (vs.take mI ++ [ys.foldl app (M.cval rl.ctor (Level.substFn φ cvj.levelParams usj))]).foldl
        app (M.cval c (Level.substFn φ cv.levelParams us)) := by
    have hm0eq' : vs.getD mI empty =
        ys.foldl app (M.cval rl.ctor (Level.substFn φ cvj.levelParams usj)) := hm0eq
    rw [← hm0eq', ← hvsplit]
  refine ⟨?_, Gr.mkAppN_of_spineOk (GradedBy.toOpen hgH hrhsF) hHO
    (fun x hx => (hargsMem x hx).elim (hgargs x) (Gr.mkAppN_args hgmaj' x)) hred hspH⟩
  show Den M φ σ _ (vs.foldl app (M.cval c (Level.substFn φ cv.levelParams us)))
  rw [hleft, heq]
  exact Den.mkAppN hHO hred

end Ix.Kernel.Open
