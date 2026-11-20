import IxVMRefinement.Decl.FamilyRules
import IxVMRefinement.Decl.FamilyAdvice
import IxVMRefinement.FamilyAlias.CallTele
import IxVMRefinement.FamilyAlias.CallMembers
import IxVMRefinement.FamilyAlias.RuleRecord
import IxVMRefinement.FamilyAlias.Facts

/-! # Refinement of `KernelModeled::check_iota_rule` at a single stored prefix

Ports the rule-checking proof onto the post-rename inversion `Decl.CheckIotaRuleInvR`
(`Decl/FamilyIotaRuleInv.lean`), the four scoped telescope walks (`Decl/FamilyTele.lean`,
`FamilyAlias/CallTele.lean`), and the single prefix context `sc := Core.Ctx.stored ⟨E, env, t, lim⟩`.

* **Keying `famKey`**: resolves every key stored in `env` and every family address in `srcAs`
  (plus their projection markers). `SubstAux.gall (famKey ...)` instantiates levels of `cty`
  uniformly for both stored external constructors and block constructors, and `rename_tm_stored`
  carries `Tm (famKey ...)` through `KernelModeled::rename` directly into `Tm sc.κ`.
* **Constructor level arity from `ev_tl`**: `KernelInfer::k_infer` on `lhs` types the major
  premise's constructor head `.const (g ctorKey) lvls` in `env`, giving
  `lvls.length = cvj.levelParams.length` directly for both external and block constructors.
* **Main theorem `check_iota_rule_facts`**: discharges `RuleFacts` and `StatementFacts` for one
  observed `KernelModeled::check_iota_rule` call. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (SubCalls posRulesJ)
open IxVM.Refinement.KernelLevels (RepKLevelList)
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Decl.FamilyAlias
  (aliasMap StatementFacts RuleFacts RuleCtor majorShape LeavesFixed)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam openPisAtFvars eqName
  isEqHead)
open Ix.Kernel.Semantics (NativeFam DefEqListJ TypedListJ IotaRunsJ)

set_option linter.unusedVariables false

universe u

/-- Default empty-context ghost map. -/
abbrev zeroGhost : Nat → KExpr := fun _ => .sort .zero

/-! ## Pure `KExpr`, `KeyIn`, `NoProjIn`, and `Infer` helpers -/

/-- Whether a key appears at a `const` or `proj` head inside an expression. -/
def KeyIn (k : KKey) : KExpr → Prop
  | .bvar _ | .sort _ | .lit _ => False
  | .fvar _ ty => KeyIn k ty
  | .const n _ => k = n
  | .app f a => KeyIn k f ∨ KeyIn k a
  | .lam ty b _ | .forallE ty b _ => KeyIn k ty ∨ KeyIn k b
  | .letE ty v b _ => KeyIn k ty ∨ KeyIn k v ∨ KeyIn k b
  | .proj s _ e => k = s ∨ KeyIn k e

theorem keyIn_instantiateLevelParams (ks : List LevelParam) (us : List KLevel) (k : KKey) :
    ∀ e : KExpr, KeyIn k (e.instantiateLevelParams ks us) ↔ KeyIn k e
  | .bvar _ | .sort _ | .lit _ => Iff.rfl
  | .const _ _ => Iff.rfl
  | .fvar _ ty => keyIn_instantiateLevelParams ks us k ty
  | .app f a => by
    simp [Expr.instantiateLevelParams, KeyIn,
      keyIn_instantiateLevelParams ks us k f, keyIn_instantiateLevelParams ks us k a]
  | .lam ty b _ | .forallE ty b _ => by
    simp [Expr.instantiateLevelParams, KeyIn,
      keyIn_instantiateLevelParams ks us k ty, keyIn_instantiateLevelParams ks us k b]
  | .letE ty v b _ => by
    simp [Expr.instantiateLevelParams, KeyIn,
      keyIn_instantiateLevelParams ks us k ty, keyIn_instantiateLevelParams ks us k v,
      keyIn_instantiateLevelParams ks us k b]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, KeyIn, keyIn_instantiateLevelParams ks us k e]

theorem keyIn_lowerBVars (n : Nat) (k : KKey) :
    ∀ (e : KExpr) (c : Nat), KeyIn k (e.lowerBVars n c) ↔ KeyIn k e
  | .bvar i, c => by unfold Expr.lowerBVars; split <;> exact Iff.rfl
  | .sort _, _ | .lit _, _ | .const _ _, _ => Iff.rfl
  | .fvar _ ty, _ => by simp [Expr.lowerBVars, KeyIn]
  | .app f a, c => by
    simp [Expr.lowerBVars, KeyIn, keyIn_lowerBVars n k f c, keyIn_lowerBVars n k a c]
  | .lam ty b _, c | .forallE ty b _, c => by
    simp [Expr.lowerBVars, KeyIn, keyIn_lowerBVars n k ty c, keyIn_lowerBVars n k b (c + 1)]
  | .letE ty v b _, c => by
    simp [Expr.lowerBVars, KeyIn, keyIn_lowerBVars n k ty c, keyIn_lowerBVars n k v c,
      keyIn_lowerBVars n k b (c + 1)]
  | .proj _ _ e, c => by
    simp [Expr.lowerBVars, KeyIn, keyIn_lowerBVars n k e c]

theorem keyIn_stripPis (k : KKey) :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.stripPis m = some (bs, rem) → KeyIn k rem → KeyIn k e
  | 0, _, _, _, h, hk => by
    injection h with hp; injection hp with _ hr; subst hr; exact hk
  | m + 1, .forallE ty b _, _, _, h, hk => by
    simp only [Expr.stripPis] at h
    cases hs : b.stripPis m with
    | none => simp [hs] at h
    | some p =>
      rw [hs] at h; injection h with hp; injection hp with _ hr; subst hr
      exact Or.inr (keyIn_stripPis k m hs hk)
  | _ + 1, .bvar _, _, _, h, _ | _ + 1, .fvar _ _, _, _, h, _ | _ + 1, .sort _, _, _, h, _
  | _ + 1, .const _ _, _, _, h, _ | _ + 1, .app _ _, _, _, h, _ | _ + 1, .lam _ _ _, _, _, h, _
  | _ + 1, .letE _ _ _ _, _, _, h, _ | _ + 1, .lit _, _, _, h, _ | _ + 1, .proj _ _ _, _, _, h, _ =>
    nomatch h

theorem keyIn_getAppArgs (k : KKey) :
    ∀ {e x : KExpr}, x ∈ e.getAppArgs → KeyIn k x → KeyIn k e
  | .app f a, x, hx, hkx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hf | rfl
    · exact Or.inl (keyIn_getAppArgs k hf hkx)
    · exact Or.inr hkx
  | .bvar _, _, hx, _ | .fvar _ _, _, hx, _ | .sort _, _, hx, _ | .const _ _, _, hx, _
  | .lam _ _ _, _, hx, _ | .forallE _ _ _, _, hx, _ | .letE _ _ _ _, _, hx, _
  | .lit _, _, hx, _ | .proj _ _ _, _, hx, _ => nomatch hx

private theorem keyIn_liftLooseBVars (k : KKey) (d : Nat) :
    ∀ (e : KExpr) (c : Nat), KeyIn k (e.liftLooseBVars d c) ↔ KeyIn k e
  | .bvar _, _ => by unfold Expr.liftLooseBVars; split <;> exact Iff.rfl
  | .sort _, _ | .lit _, _ | .const _ _, _ | .fvar _ _, _ => Iff.rfl
  | .app f a, c => by
    simp [Expr.liftLooseBVars, KeyIn, keyIn_liftLooseBVars k d f c, keyIn_liftLooseBVars k d a c]
  | .lam ty b _, c | .forallE ty b _, c => by
    simp [Expr.liftLooseBVars, KeyIn, keyIn_liftLooseBVars k d ty c,
      keyIn_liftLooseBVars k d b (c + 1)]
  | .letE ty v b _, c => by
    simp [Expr.liftLooseBVars, KeyIn, keyIn_liftLooseBVars k d ty c,
      keyIn_liftLooseBVars k d v c, keyIn_liftLooseBVars k d b (c + 1)]
  | .proj _ _ e, c => by
    simp [Expr.liftLooseBVars, KeyIn, keyIn_liftLooseBVars k d e c]

private theorem keyIn_instShift (k : KKey) (V : KExpr) :
    ∀ (B : KExpr) (j : Nat), KeyIn k (instShift V j B) → KeyIn k V ∨ KeyIn k B
  | .bvar i, j, hk => by
    simp only [instShift, Expr.instantiate1Lift] at hk
    split at hk
    · exact Or.inl ((keyIn_liftLooseBVars k j V 0).mp hk)
    · split at hk <;> exact nomatch hk
  | .fvar _ _, _, hk => Or.inr hk
  | .sort _, _, hk | .lit _, _, hk => nomatch hk
  | .const _ _, _, hk => Or.inr hk
  | .app f a, j, hk => by
    simp only [instShift, Expr.instantiate1Lift, KeyIn] at hk
    rcases hk with hf | ha
    · exact (keyIn_instShift k V f j hf).imp id Or.inl
    · exact (keyIn_instShift k V a j ha).imp id Or.inr
  | .lam ty b _, j, hk | .forallE ty b _, j, hk => by
    simp only [instShift, Expr.instantiate1Lift, KeyIn] at hk
    rcases hk with ht | hb
    · exact (keyIn_instShift k V ty j ht).imp id Or.inl
    · exact (keyIn_instShift k V b (j + 1) hb).imp id Or.inr
  | .letE ty v b _, j, hk => by
    simp only [instShift, Expr.instantiate1Lift, KeyIn] at hk
    rcases hk with ht | hv | hb
    · exact (keyIn_instShift k V ty j ht).imp id Or.inl
    · exact (keyIn_instShift k V v j hv).imp id (Or.inr ∘ Or.inl)
    · exact (keyIn_instShift k V b (j + 1) hb).imp id (Or.inr ∘ Or.inr)
  | .proj _ _ e, j, hk => by
    simp only [instShift, Expr.instantiate1Lift, KeyIn] at hk
    rcases hk with rfl | he
    · exact Or.inr (Or.inl rfl)
    · exact (keyIn_instShift k V e j he).imp id Or.inr

theorem keyIn_of_majorShape {tyA : KExpr} {mI rP cnP : Nat} {lvls : List Level} {pins : List KExpr}
    (hmaj : majorShape tyA mI rP cnP = some (lvls, pins))
    {p : KExpr} (hp : p ∈ pins) {k : KKey} (hk : KeyIn k p) : KeyIn k tyA := by
  unfold majorShape at hmaj
  split at hmaj
  · cases hs : tyA.stripPis mI with
    | none => simp [hs] at hmaj
    | some pair =>
      rw [hs] at hmaj
      rcases pair with ⟨bs, rem⟩
      cases rem with
      | forallE dom body bm =>
        dsimp only at hmaj
        cases hfn : dom.getAppFn with
        | const cn clvls =>
          rw [hfn] at hmaj
          dsimp only at hmaj
          split at hmaj
          · injection hmaj with hpair; injection hpair with _ hpins_eq
            rw [← hpins_eq] at hp
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            have hkq : KeyIn k q := (keyIn_lowerBVars (mI - rP) k q 0).mp hk
            have hkdom : KeyIn k dom := keyIn_getAppArgs k (List.mem_of_mem_take hq) hkq
            exact keyIn_stripPis k mI hs (Or.inl hkdom)
          · cases hmaj
        | _ => rw [hfn] at hmaj; cases hmaj
      | _ => cases hmaj
  · cases hmaj

private theorem noProjIn_stripPis {bad : List KKey} :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      Decl.NoProjIn bad e = true → e.stripPis m = some (bs, rem) → Decl.NoProjIn bad rem = true
  | 0, _, _, _, hnp, hs => by
    injection hs with hp; injection hp with _ hr; subst hr; exact hnp
  | m + 1, .forallE ty b _, _, _, hnp, hs => by
    simp only [Decl.NoProjIn, Bool.and_eq_true] at hnp
    simp only [Expr.stripPis] at hs
    cases hsb : b.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ hr; subst hr
      exact noProjIn_stripPis m hnp.2 hsb
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs
  | _ + 1, .proj _ _ _, _, _, _, hs => nomatch hs

private theorem noProjIn_getAppArgs {bad : List KKey} :
    ∀ {e : KExpr}, Decl.NoProjIn bad e = true →
      ∀ x ∈ e.getAppArgs, Decl.NoProjIn bad x = true
  | .app f a, hnp, x, hx => by
    simp only [Decl.NoProjIn, Bool.and_eq_true] at hnp
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hf | rfl
    · exact noProjIn_getAppArgs hnp.1 x hf
    · exact hnp.2
  | .bvar _, _, _, hx | .fvar _ _, _, _, hx | .sort _, _, _, hx | .const _ _, _, _, hx
  | .lam _ _ _, _, _, hx | .forallE _ _ _, _, _, hx | .letE _ _ _ _, _, _, hx
  | .lit _, _, _, hx | .proj _ _ _, _, _, hx => nomatch hx

private theorem noProjIn_lowerBVars (bad : List KKey) (n : Nat) :
    ∀ (e : KExpr) (c : Nat), Decl.NoProjIn bad (e.lowerBVars n c) = Decl.NoProjIn bad e
  | .bvar i, c => by unfold Expr.lowerBVars; split <;> rfl
  | .sort _, _ | .lit _, _ | .const _ _, _ | .fvar _ _, _ => rfl
  | .app f a, c => by
    simp [Expr.lowerBVars, Decl.NoProjIn, noProjIn_lowerBVars bad n f c,
      noProjIn_lowerBVars bad n a c]
  | .lam ty b _, c | .forallE ty b _, c => by
    simp [Expr.lowerBVars, Decl.NoProjIn, noProjIn_lowerBVars bad n ty c,
      noProjIn_lowerBVars bad n b (c + 1)]
  | .letE ty v b _, c => by
    simp [Expr.lowerBVars, Decl.NoProjIn, noProjIn_lowerBVars bad n ty c,
      noProjIn_lowerBVars bad n v c, noProjIn_lowerBVars bad n b (c + 1)]
  | .proj _ _ e, c => by
    simp [Expr.lowerBVars, Decl.NoProjIn, noProjIn_lowerBVars bad n e c]

theorem noProjIn_of_majorShape {bad : List KKey} {tyA : KExpr} {mI rP cnP : Nat}
    {lvls : List Level} {pins : List KExpr}
    (hnp : Decl.NoProjIn bad tyA = true)
    (hmaj : majorShape tyA mI rP cnP = some (lvls, pins)) :
    ∀ p ∈ pins, Decl.NoProjIn bad p = true := by
  intro p hp
  unfold majorShape at hmaj
  split at hmaj
  · cases hs : tyA.stripPis mI with
    | none => simp [hs] at hmaj
    | some pair =>
      rw [hs] at hmaj
      rcases pair with ⟨bs, rem⟩
      cases rem with
      | forallE dom body bm =>
        dsimp only at hmaj
        cases hfn : dom.getAppFn with
        | const cn clvls =>
          rw [hfn] at hmaj
          dsimp only at hmaj
          split at hmaj
          · injection hmaj with hpair; injection hpair with _ hpins_eq
            rw [← hpins_eq] at hp
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            have hnp_fa := noProjIn_stripPis mI hnp hs
            simp only [Decl.NoProjIn, Bool.and_eq_true] at hnp_fa
            rw [noProjIn_lowerBVars]
            exact noProjIn_getAppArgs hnp_fa.1 q (List.mem_of_mem_take hq)
          · cases hmaj
        | _ => rw [hfn] at hmaj; cases hmaj
      | _ => cases hmaj
  · cases hmaj

theorem noProjIn_of_constsResolve_fresh {env : Ix.Kernel.Env .anon} {bad : List KKey}
    (hfresh : ∀ k ∈ bad, env.find? k = none) :
    ∀ e : KExpr, e.constsResolve env = true → Decl.NoProjIn bad e = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ ty, h => noProjIn_of_constsResolve_fresh hfresh ty h
  | .app f a, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Decl.NoProjIn, noProjIn_of_constsResolve_fresh hfresh f h.1,
      noProjIn_of_constsResolve_fresh hfresh a h.2]
  | .lam ty b _, h | .forallE ty b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Decl.NoProjIn, noProjIn_of_constsResolve_fresh hfresh ty h.1,
      noProjIn_of_constsResolve_fresh hfresh b h.2]
  | .letE ty v b _, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    simp [Decl.NoProjIn, noProjIn_of_constsResolve_fresh hfresh ty h.1.1,
      noProjIn_of_constsResolve_fresh hfresh v h.1.2,
      noProjIn_of_constsResolve_fresh hfresh b h.2]
  | .proj s _ e, h => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at h
    have hnotmem : s ∉ bad := by
      intro hm
      rw [hfresh s hm] at h
      simp at h
    have hcont : bad.contains s = false := by
      rw [List.contains_eq_mem, decide_eq_false_iff_not]; exact hnotmem
    simp only [Decl.NoProjIn, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨hcont, noProjIn_of_constsResolve_fresh hfresh e h.2⟩

theorem addrIn_of_keyIn_tmExact {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Decl.TmExact κ 0 Γ h k E p) :
    ∀ key, KeyIn key E → ∃ a, AddrIn h p a ∧ κ (ixAddr a) = key := by
  induction rep with
  | bvarLocal _ _ _ => intro _ hk; exact nomatch hk
  | bvarFree _ _ _ hd => exact nomatch hd
  | sort _ _ => intro _ hk; exact nomatch hk
  | const cell ra _ =>
    intro key hk; exact ⟨_, .const cell ra, hk.symm⟩
  | app cell _ _ ihf iha =>
    intro key hk
    rcases hk with hf | ha
    · obtain ⟨a, hin, heq⟩ := ihf key hf; exact ⟨a, .appFn cell hin, heq⟩
    · obtain ⟨a, hin, heq⟩ := iha key ha; exact ⟨a, .appArg cell hin, heq⟩
  | lam cell _ _ _ iht ihb =>
    intro key hk
    rcases hk with ht | hb
    · obtain ⟨a, hin, heq⟩ := iht key ht; exact ⟨a, .lamTy cell hin, heq⟩
    · obtain ⟨a, hin, heq⟩ := ihb key hb; exact ⟨a, .lamBody cell hin, heq⟩
  | forallE cell _ _ _ iht ihb =>
    intro key hk
    rcases hk with ht | hb
    · obtain ⟨a, hin, heq⟩ := iht key ht; exact ⟨a, .forallTy cell hin, heq⟩
    · obtain ⟨a, hin, heq⟩ := ihb key hb; exact ⟨a, .forallBody cell hin, heq⟩
  | letE cell _ _ _ _ ihv ihb =>
    intro key hk
    rcases keyIn_instShift key _ _ 0 hk with hv | hb
    · obtain ⟨a, hin, heq⟩ := ihv key hv; exact ⟨a, .letVal cell hin, heq⟩
    · obtain ⟨a, hin, heq⟩ := ihb key hb; exact ⟨a, .letBody cell hin, heq⟩
  | litNat _ _ _ | litStr _ _ _ => intro _ hk; exact nomatch hk
  | proj cell ra _ ihe =>
    intro key hk
    rcases hk with rfl | he
    · exact ⟨_, .projHead cell ra, rfl⟩
    · obtain ⟨a, hin, heq⟩ := ihe key he; exact ⟨a, .projArg cell hin, heq⟩

private theorem infer_mkAppN_fn {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {args : List KExpr} {f T : KExpr},
      Ix.Kernel.Rules.Infer env .full d (Expr.mkAppN f args) T →
      ∃ Tf, Ix.Kernel.Rules.Infer env .full d f Tf
  | [], _, _, h => ⟨_, h⟩
  | a :: args, f, _, h => by
    simp only [Expr.mkAppN] at h
    obtain ⟨Tf, hfa⟩ := infer_mkAppN_fn h
    cases hfa with
    | app hf _ _ _ => exact ⟨_, hf⟩

private theorem infer_mkAppN_mem {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ {args : List KExpr} {f T x : KExpr},
      Ix.Kernel.Rules.Infer env .full d (Expr.mkAppN f args) T → x ∈ args →
      ∃ Tx, Ix.Kernel.Rules.Infer env .full d x Tx
  | [], _, _, _, _, hx => nomatch hx
  | a :: args, f, _, x, h, hx => by
    simp only [Expr.mkAppN] at h
    rcases List.mem_cons.mp hx with rfl | hx'
    · obtain ⟨Tf, hfa⟩ := infer_mkAppN_fn h
      cases hfa with
      | app _ _ ha _ => exact ⟨_, ha⟩
    · exact infer_mkAppN_mem h hx'

private theorem stripPis_constHead_of_instantiateLevelParams (ks : List LevelParam)
    (us : List KLevel) :
    ∀ (m : Nat) (e : KExpr) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr}
      {Dc : KKey} {usc : List KLevel},
      (e.instantiateLevelParams ks us).stripPis m = some (bs, rem) →
      rem.getAppFn = .const Dc usc →
      ∃ bs₀ rem₀ usc₀, e.stripPis m = some (bs₀, rem₀) ∧ rem₀.getAppFn = .const Dc usc₀ ∧
        Expr.ctorTeleOk e m = true
  | 0, e, _, rem, Dc, usc, hs, hfn => by
    injection hs with hp; injection hp with _ hrem; subst hrem
    rw [Decl.getAppFn_instantiateLevelParams] at hfn
    cases hgf : e.getAppFn with
    | const Dc₀ usc₀ =>
      rw [hgf] at hfn
      simp only [Expr.instantiateLevelParams, Expr.const.injEq] at hfn
      obtain ⟨rfl, _⟩ := hfn
      exact ⟨[], e, usc₀, rfl, hgf, by simp [Expr.ctorTeleOk, Expr.stripPis, hgf]⟩
    | _ =>
      rw [hgf] at hfn; simp [Expr.instantiateLevelParams] at hfn
  | m + 1, .forallE dom body bm, _, _, Dc, usc, hs, hfn => by
    simp only [Expr.instantiateLevelParams, Expr.stripPis] at hs
    cases hsb : (body.instantiateLevelParams ks us).stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with _ hrem; subst hrem
      obtain ⟨bs₀, rem₀, usc₀, hbs₀, hfn₀, _⟩ :=
        stripPis_constHead_of_instantiateLevelParams ks us m body hsb hfn
      refine ⟨(dom, bm) :: bs₀, rem₀, usc₀, by simp [Expr.stripPis, hbs₀], hfn₀, ?_⟩
      simp [Expr.ctorTeleOk, Expr.stripPis, hbs₀, hfn₀]
  | _ + 1, .bvar _, _, _, _, _, hs, _ | _ + 1, .fvar _ _, _, _, _, _, hs, _
  | _ + 1, .sort _, _, _, _, _, hs, _ | _ + 1, .const _ _, _, _, _, _, hs, _
  | _ + 1, .app _ _, _, _, _, _, hs, _ | _ + 1, .lam _ _ _, _, _, _, _, hs, _
  | _ + 1, .letE _ _ _ _, _, _, _, _, hs, _ | _ + 1, .lit _, _, _, _, _, hs, _
  | _ + 1, .proj _ _ _, _, _, _, _, hs, _ => by
    simp [Expr.instantiateLevelParams, Expr.stripPis] at hs

private theorem stripPis_renameConsts_ir (π : KKey → KKey) :
    ∀ (m : Nat) (e : KExpr) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {rem : KExpr},
      e.stripPis m = some (bs, rem) →
      (e.renameConsts π).stripPis m =
        some (bs.map (fun p => (p.1.renameConsts π, p.2)), rem.renameConsts π)
  | 0, _, _, _, hs => by
    injection hs with hp; injection hp with h1 h2; subst h1 h2; rfl
  | m + 1, .forallE dom body bm, _, _, hs => by
    simp only [Expr.stripPis] at hs
    cases hsb : body.stripPis m with
    | none => simp [hsb] at hs
    | some p =>
      rw [hsb] at hs; injection hs with hp; injection hp with h1 h2; subst h1 h2
      simp [Expr.renameConsts, Expr.stripPis, stripPis_renameConsts_ir π m body hsb]
  | _ + 1, .bvar _, _, _, hs | _ + 1, .fvar _ _, _, _, hs | _ + 1, .sort _, _, _, hs
  | _ + 1, .const _ _, _, _, hs | _ + 1, .app _ _, _, _, hs | _ + 1, .lam _ _ _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, hs | _ + 1, .lit _, _, _, hs | _ + 1, .proj _ _ _, _, _, hs =>
    nomatch hs

private theorem getLastD_eq_of_getElem? {α : Type} :
    ∀ (l : List α) (n : Nat) (x d : α), l.length = n + 1 → l[n]? = some x → l.getLastD d = x
  | [], _, _, _, hlen, _ => by simp at hlen
  | [a], 0, x, d, _, hget => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget; rfl
  | [_], _ + 1, _, _, hlen, _ => by simp at hlen
  | _ :: b :: t, 0, _, _, hlen, _ => by simp at hlen
  | _ :: b :: t, n + 1, x, d, hlen, hget => by
    simp only [List.length_cons] at hlen
    simp only [List.getElem?_cons_succ] at hget
    exact getLastD_eq_of_getElem? (b :: t) n x d (Nat.succ.inj hlen) hget

private theorem openPisAtFvars_pullback {g : KKey → KKey} {m i : Nat} {e rem' : KExpr}
    {fvs' : List KExpr} (hop : openPisAtFvars m (e.renameConsts g) i = some (fvs', rem')) :
    ∃ fvs rem, openPisAtFvars m e i = some (fvs, rem) ∧
      fvs.map (·.renameConsts g) = fvs' ∧ rem.renameConsts g = rem' := by
  have h1 := Decl.openPisAtFvars_renameConsts g m e i
  rw [hop] at h1
  cases hx : openPisAtFvars m e i with
  | none => rw [hx] at h1; simp at h1
  | some p =>
    rw [hx] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact ⟨p.1, p.2, rfl, h1.1.symm, h1.2.symm⟩

private theorem instLamsAt_append :
    ∀ (xs ys : List KExpr) (e : KExpr),
      Expr.instLamsAt (xs ++ ys) e =
        (Expr.instLamsAt xs e).bind (fun p =>
          (Expr.instLamsAt ys p.2).map (fun q => (p.1 ++ q.1, q.2)))
  | [], ys, e => by simp [Expr.instLamsAt]
  | x :: xs, ys, .lam ty b _ => by
    simp only [List.cons_append, Expr.instLamsAt, instLamsAt_append xs ys (b.instantiate1 x)]
    cases Expr.instLamsAt xs (b.instantiate1 x) with
    | none => rfl
    | some p =>
      cases hys : Expr.instLamsAt ys p.2 <;> simp [hys]
  | _ :: _, _, .bvar _ | _ :: _, _, .fvar _ _ | _ :: _, _, .sort _ | _ :: _, _, .const _ _
  | _ :: _, _, .app _ _ | _ :: _, _, .forallE _ _ _ | _ :: _, _, .letE _ _ _ _
  | _ :: _, _, .lit _ | _ :: _, _, .proj _ _ _ => rfl

private theorem instLamsAt_of_posOf {ps : List LevelParam} {xs : List KExpr} {e : KExpr}
    {doms' : List KExpr} {rem' : KExpr}
    (h : Expr.instLamsAt (xs.map (Core.posOf ps)) (Core.posOf ps e) = some (doms', rem')) :
    ∃ doms rem, Expr.instLamsAt xs e = some (doms, rem) ∧
      doms' = doms.map (Core.posOf ps) ∧ rem' = Core.posOf ps rem := by
  have h1 := Decl.instLamsAt_instantiateLevelParams ps (Core.posLevels ps) xs e
  change Expr.instLamsAt (xs.map (Core.posOf ps)) (Core.posOf ps e) =
    (Expr.instLamsAt xs e).map (fun p => (p.1.map (Core.posOf ps), Core.posOf ps p.2)) at h1
  rw [h] at h1
  cases hx : Expr.instLamsAt xs e with
  | none => rw [hx] at h1; simp at h1
  | some p =>
    rw [hx] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact ⟨p.1, p.2, rfl, h1.1, h1.2⟩

private theorem instLamsAt_pullback {g : KKey → KKey} {xs ys doms' : List KExpr} {e rem' : KExpr}
    (hxs : xs.map (·.renameConsts g) = ys)
    (hi : Expr.instLamsAt ys (e.renameConsts g) = some (doms', rem')) :
    ∃ doms rem, Expr.instLamsAt xs e = some (doms, rem) ∧
      doms.map (·.renameConsts g) = doms' ∧ rem.renameConsts g = rem' := by
  have h1 := Decl.FamilyAlias.instLamsAt_renameConsts g xs e
  rw [hxs, hi] at h1
  cases hx : Expr.instLamsAt xs e with
  | none => rw [hx] at h1; simp at h1
  | some p =>
    rw [hx] at h1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    exact ⟨p.1, p.2, rfl, h1.1.symm, h1.2.symm⟩

private theorem repList_imp {α : Type} {R S : Heap F → α → SourceValue F → Prop} {h : Heap F}
    (hf : ∀ x p, R h x p → S h x p) :
    ∀ {xs : List α} {v : SourceValue F},
      RepList kexprListEnum R h xs v → RepList kexprListEnum S h xs v
  | _, _, .nil cell => .nil cell
  | _, _, .cons cell hh htl => .cons cell (hf _ _ hh) (repList_imp hf htl)

private theorem repList_map_rel {α β : Type} {R : Heap F → α → SourceValue F → Prop}
    {S : Heap F → β → SourceValue F → Prop} {f : α → β} {h : Heap F}
    (hf : ∀ x p, R h x p → S h (f x) p) :
    ∀ {xs : List α} {v : SourceValue F},
      RepList kexprListEnum R h xs v → RepList kexprListEnum S h (xs.map f) v
  | _, _, .nil cell => .nil cell
  | _, _, .cons cell hh htl => .cons cell (hf _ _ hh) (repList_map_rel hf htl)

private theorem nat_eq_of_field_eq_u32' {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (h : (a : F) = (b : F)) : a = b := by
  have h1 := congrArg ZMod.val h
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  rwa [SubstAux.val_natCast (by omega), SubstAux.val_natCast (by omega)] at h1

/-! ## `famKey`, `rename_tm_stored`, `rename_list_stored_of_src`, and `eq_addr_key_scoped` -/

/-- **Keying of the prefix plus the family's source addresses**: resolves every constant stored in
`env`, every address in `srcAs`, and their projection markers. -/
def famRes (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (srcAs : List Bytes.Address)
    (a : _root_.Address) : Prop :=
  (∃ ci, env.find? (Core.keyOf t a) = some ci) ∨ a ∈ srcAs.map ixAddr ∨
    ∃ y, a = Core.projMarker y ∧
      ((∃ ci, env.find? (Core.keyOf t y) = some ci) ∨ y ∈ srcAs.map ixAddr)

noncomputable def famKey (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (srcAs : List Bytes.Address) : _root_.Address → KKey :=
  Core.resKey t (famRes t env srcAs)

theorem famKey_of_find {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {srcAs : List Bytes.Address} {a : _root_.Address} {ci : ConstantInfo .anon}
    (h : env.find? (Core.keyOf t a) = some ci) :
    famKey t env srcAs a = Core.keyOf t a :=
  Core.resKey_of_res (Or.inl ⟨ci, h⟩)

theorem famKey_of_src {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {srcAs : List Bytes.Address} {a : _root_.Address} (h : a ∈ srcAs.map ixAddr) :
    famKey t env srcAs a = Core.keyOf t a :=
  Core.resKey_of_res (Or.inr (Or.inl h))

theorem famKey_projPermitted_of_find {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {srcAs : List Bytes.Address} {a : _root_.Address} {ci : ConstantInfo .anon}
    (h : env.find? (Core.keyOf t a) = some ci) :
    ProjPermitted (famKey t env srcAs) a := by
  have he : famKey t env srcAs (Core.projMarker a) = Core.keyOf t (Core.projMarker a) :=
    Core.resKey_of_res (Or.inr (Or.inr ⟨a, rfl, Or.inl ⟨ci, h⟩⟩))
  exact ⟨by rw [he]; exact Resolved.ne⟩

theorem famKey_projPermitted_of_src {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {srcAs : List Bytes.Address} {a : _root_.Address} (h : a ∈ srcAs.map ixAddr) :
    ProjPermitted (famKey t env srcAs) a := by
  have he : famKey t env srcAs (Core.projMarker a) = Core.keyOf t (Core.projMarker a) :=
    Core.resKey_of_res (Or.inr (Or.inr ⟨a, rfl, Or.inr h⟩))
  exact ⟨by rw [he]; exact Resolved.ne⟩

theorem famKey_ne_cases {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {srcAs : List Bytes.Address} {a : Bytes.Address}
    (h : famKey t env srcAs (ixAddr a) ≠ unresolvedKey) :
    famKey t env srcAs (ixAddr a) = Core.keyOf t (ixAddr a) ∧
      ((∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr) := by
  have hres := Core.res_of_resKey_ne h
  refine ⟨Core.resKey_of_res hres, ?_⟩
  rcases hres with h1 | h2 | ⟨y, hy, -⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exact (Core.not_isProjMarker_of_size (Core.ixAddr_size a) ⟨y, hy⟩).elim

/-- Any term exact at `Core.Ctx.stored` is exact at `Core.keyOf t` (same expression). -/
theorem tmExact_rekey_stored_to_table {E₀ : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Decl.TmExact (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ d Γ h k E p) :
    Decl.TmExact (Core.keyOf t) d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl => exact .sort cell rl
  | @const k addr ap lsp a ls res cell ra rls =>
    have he : (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (ixAddr a) = Core.keyOf t (ixAddr a) :=
      (Core.Ctx.stored ⟨E₀, env, t, lim⟩).key_eq res.ne
    rw [he]; exact .const cell ra rls
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | @proj k addr ap ep a i E res _ cell ra _ ih =>
    have he : (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (ixAddr a) = Core.keyOf t (ixAddr a) :=
      (Core.Ctx.stored ⟨E₀, env, t, lim⟩).key_eq res.ne
    rw [he]; exact .proj cell ra ih

/-- Any term represented at `Core.Ctx.stored` is represented at `famKey` (same expression). -/
theorem tm_famKey_of_stored {E₀ : Ixon.Env} {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} {srcAs : List Bytes.Address} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Tm (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ d Γ h k E p) :
    Tm (famKey t env srcAs) d Γ h k E p := by
  have hkeep : ∀ x, (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ x ≠ unresolvedKey →
      famKey t env srcAs x = (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ x := by
    intro x hx
    rw [Core.Ctx.stored_κ] at hx ⊢
    have hres := Core.res_of_resKey_ne hx
    rw [Core.resKey_of_res hres]
    rcases hres with h1 | ⟨y, hy, hci⟩
    · exact Core.resKey_of_res (Or.inl h1)
    · exact Core.resKey_of_res (Or.inr (Or.inr ⟨y, hy, Or.inl hci⟩))
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl hu => exact .sort cell rl hu
  | @const k addr ap lsp a ls us res cell ra rls hus =>
    have he := hkeep (ixAddr a) res.ne
    have : Resolved (famKey t env srcAs (ixAddr a)) := ⟨by rw [he]; exact res.ne⟩
    rw [← he]; exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | @proj k addr ap ep a i E res pm cell ra _ ih =>
    have he := hkeep (ixAddr a) res.ne
    have : Resolved (famKey t env srcAs (ixAddr a)) := ⟨by rw [he]; exact res.ne⟩
    have : ProjPermitted (famKey t env srcAs) (ixAddr a) := by
      have hm := hkeep (Core.projMarker (ixAddr a)) pm.ne
      exact ⟨by rw [hm]; exact pm.ne⟩
    rw [← he]; exact .proj cell ra ih

/-- Any term represented at `Core.keyOf t` whose cells are stored or in `srcAs` is represented at
`famKey`. -/
theorem tm_famKey_of_cells {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}
    {srcAs : List Bytes.Address} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Tm (Core.keyOf t) d Γ h k E p)
    (hcells : ∀ a, AddrIn h p a →
      (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr) :
    Tm (famKey t env srcAs) d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl hu => exact .sort cell rl hu
  | @const k addr ap lsp a ls us res cell ra rls hus =>
    rcases hcells a (.const cell ra) with ⟨ci, hci⟩ | hm
    · have he := famKey_of_find (srcAs := srcAs) hci
      have : Resolved (famKey t env srcAs (ixAddr a)) := ⟨by rw [he]; exact res.ne⟩
      rw [← he]; exact .const cell ra rls hus
    · have he := famKey_of_src (t := t) (env := env) hm
      have : Resolved (famKey t env srcAs (ixAddr a)) := ⟨by rw [he]; exact res.ne⟩
      rw [← he]; exact .const cell ra rls hus
  | app cell _ _ ihf iha =>
    exact .app cell (ihf fun a m => hcells a (.appFn cell m))
      (iha fun a m => hcells a (.appArg cell m))
  | lam cell _ _ rl iht ihb =>
    exact .lam cell (iht fun a m => hcells a (.lamTy cell m))
      (ihb fun a m => hcells a (.lamBody cell m)) rl
  | forallE cell _ _ rl iht ihb =>
    exact .forallE cell (iht fun a m => hcells a (.forallTy cell m))
      (ihb fun a m => hcells a (.forallBody cell m)) rl
  | letE cell _ _ _ iht ihv ihb =>
    exact .letE cell (iht fun a m => hcells a (.letTy cell m))
      (ihv fun a m => hcells a (.letVal cell m))
      (ihb fun a m => hcells a (.letBody cell m))
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | @proj k addr ap ep a i E res pm cell ra _ ih =>
    rcases hcells a (.projHead cell ra) with ⟨ci, hci⟩ | hm
    · have he := famKey_of_find (srcAs := srcAs) hci
      have : Resolved (famKey t env srcAs (ixAddr a)) := ⟨by rw [he]; exact res.ne⟩
      have : ProjPermitted (famKey t env srcAs) (ixAddr a) := famKey_projPermitted_of_find hci
      rw [← he]; exact .proj cell ra (ih fun a m => hcells a (.projArg cell m))
    · have he := famKey_of_src (t := t) (env := env) hm
      have : Resolved (famKey t env srcAs (ixAddr a)) := ⟨by rw [he]; exact res.ne⟩
      have : ProjPermitted (famKey t env srcAs) (ixAddr a) := famKey_projPermitted_of_src hm
      rw [← he]; exact .proj cell ra (ih fun a m => hcells a (.projArg cell m))

private theorem tm_const_resolved {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p x y : SourceValue F} {a : Bytes.Address}
    (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Const" [x, y]))
    (ra : Bytes.RepAddressRef addrTy h a x) :
    κ (ixAddr a) ≠ unresolvedKey := by
  cases rep with
  | @const _ _ _ _ a' _ _ res cell ra' _ _ =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx _
    subst hx
    have he := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra' ra
    subst he; exact res.ne
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | app cell _ _ | lam cell _ _ _
  | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

private theorem tm_proj_resolved {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p x y z : SourceValue F} {a : Bytes.Address}
    (rep : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [x, y, z]))
    (ra : Bytes.RepAddressRef addrTy h a x) :
    κ (ixAddr a) ≠ unresolvedKey := by
  cases rep with
  | @proj _ _ _ _ a' _ _ res _ cell ra' _ =>
    obtain ⟨-, hxs⟩ := load_cell cell hl
    injection hxs with hx _
    subst hx
    have he := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra' ra
    subst he; exact res.ne
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ =>
    exact (load_cell_ne cell hl (by decide)).elim

private theorem tmExact_const_resolved {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p x y : SourceValue F} {a : Bytes.Address}
    (rep : Decl.TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Const" [x, y]))
    (ra : Bytes.RepAddressRef addrTy h a x) :
    κ (ixAddr a) ≠ unresolvedKey :=
  tm_const_resolved rep.toTm hl ra

local macro "iota_lt_calls" : term =>
  `(by simp only [List.length_cons, List.length_append]; omega)

/-- **Renaming a `Tm (famKey ...)` term directly into `Tm (Core.Ctx.stored ...).κ`**: every
resolved cell of `famKey` is stored in `env` or in `srcAs`, so its image under `aliasMap` is
stored in `env` (where all models `dstAs` are stored). -/
theorem rename_tm_stored {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr}
    (hlen : srcAs.length = dstAs.length)
    (hmodels : ∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci) :
    ∀ {e src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr},
      ObsFn W "KernelModeled::rename" [e, src, dst] h r h' cs →
      Tm (famKey t env srcAs) 0 Γ₁ h k E e →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst →
      Tm (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ 0 Γ₂ h' k
        (Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
          (dstAs.map fun b => Core.keyOf t (ixAddr b)))) E) r := by
  let srcKeys := srcAs.map fun b => Core.keyOf t (ixAddr b)
  let dstKeys := dstAs.map fun b => Core.keyOf t (ixAddr b)
  let g := aliasMap (srcKeys.zip dstKeys)
  let sc := Core.Ctx.stored ⟨E₀, env, t, lim⟩
  have hdst_stored : ∀ d ∈ dstKeys, ∃ ci, env.find? d = some ci := by
    intro d hd
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
    exact hmodels b hb
  have hlenK : srcKeys.length = dstKeys.length := by simp [srcKeys, dstKeys, hlen]
  have hmain : ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → fname = "KernelModeled::rename" →
      ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
        args = [e, src, dst] →
        Tm (famKey t env srcAs) 0 Γ₁ h k E e →
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src →
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst →
        Tm sc.κ 0 Γ₂ h' k (Decl.renameAll g E) r :=
    ObsFn.strong_induction (world := W)
      (fun fname args h r h' cs => fname = "KernelModeled::rename" →
        ∀ (e src dst : SourceValue F) (k : Nat) (E : KExpr),
          args = [e, src, dst] →
          Tm (famKey t env srcAs) 0 Γ₁ h k E e →
          RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src →
          RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst →
          Tm sc.κ 0 Γ₂ h' k (Decl.renameAll g E) r)
      (fun fname args h r h' cs ev ih hfn e src dst k E hargs hE hsrc hdst => by
        subst hfn hargs
        have rm := renameMap_aliasMap hwf hlen hsrc hdst
        match Obs.«KernelModeled::rename».obs ev with
        | .Const (ld12 := ld) (he34 := hr) (hm33 := hm) (ev51 := e1) .. =>
          subst hr hm
          obtain ⟨a, us, rfl, ra, ls, rls, hus⟩ := hE.const_of_load ld
          have hne := tm_const_resolved hE ld ra
          obtain ⟨hfk_eq, hcase⟩ := famKey_ne_cases hne
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := Decl.rename_addr_spec e1 ra rm
          have hcaseK : (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨
              Core.keyOf t (ixAddr a) ∈ srcKeys := by
            rcases hcase with hst | hm
            · exact Or.inl hst
            · obtain ⟨b, hb, hab⟩ := List.mem_map.mp hm
              exact Or.inr (List.mem_map.mpr ⟨b, hb, by rw [hab]⟩)
          obtain ⟨ci, hci⟩ := aliasMap_zip_stored hlenK hdst_stored hcaseK
          rw [← hka] at hci
          have hsc_a' : sc.κ (ixAddr a') = Core.keyOf t (ixAddr a') :=
            Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
          have : Resolved (sc.κ (ixAddr a')) := ⟨by rw [hsc_a']; exact Resolved.ne⟩
          have hkey_eq : g (famKey t env srcAs (ixAddr a)) = sc.κ (ixAddr a') := by
            rw [hfk_eq]
            exact hka.symm.trans hsc_a'.symm
          simp only [Decl.renameAll, hkey_eq]
          exact .const (by simp)
            (Bytes.repAddressRef_heapMono₂ addrTy (Heap.Extends.snoc _ _) ra')
            (rls.mono (Heap.Extends.snoc _ _)) hus
        | .App (ld12 := ld) (he105 := hr) (hm104 := hm) (ev122 := e1) (ev158 := e2)
            (hc183 := hc) .. =>
          subst hc hr hm
          obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
          have sf := ih _ _ _ _ _ _ iota_lt_calls e1 rfl _ src dst k Ef rfl hf hsrc hdst
          have sa := ih _ _ _ _ _ _ iota_lt_calls e2 rfl _ src dst k Ea rfl
            (ha.mono e1.heap_extends)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hsrc)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hdst)
          exact Tm.store_app (sf.mono e2.heap_extends) sa
        | .Lam (ld12 := ld) (he210 := hr) (hm209 := hm) (ev228 := e1) (ev264 := e2)
            (hc296 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.lam_of_load ld
          have st := ih _ _ _ _ _ _ iota_lt_calls e1 rfl _ src dst k T rfl ht hsrc hdst
          have sb := ih _ _ _ _ _ _ iota_lt_calls e2 rfl _ src dst (k + 1) B rfl
            (hb.mono e1.heap_extends)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hsrc)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hdst)
          exact SubstAux.tm_store_lam (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Forall (ld12 := ld) (he323 := hr) (hm322 := hm) (ev341 := e1) (ev377 := e2)
            (hc409 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := hE.forallE_of_load ld
          have st := ih _ _ _ _ _ _ iota_lt_calls e1 rfl _ src dst k T rfl ht hsrc hdst
          have sb := ih _ _ _ _ _ _ iota_lt_calls e2 rfl _ src dst (k + 1) B rfl
            (hb.mono e1.heap_extends)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hsrc)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hdst)
          exact SubstAux.tm_store_forallE (st.mono e2.heap_extends) sb
            (hl.mono (e1.heap_extends.trans e2.heap_extends))
        | .Let (ld12 := ld) (he436 := hr) (hm435 := hm) (ev454 := e1) (ev490 := e2)
            (ev526 := e3) (hc551 := hc) .. =>
          subst hc hr hm
          obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := hE.letE_of_load ld
          rw [Decl.renameAll_instShift]
          have st := ih _ _ _ _ _ _ iota_lt_calls e1 rfl _ src dst k T rfl ht hsrc hdst
          have sv := ih _ _ _ _ _ _ iota_lt_calls e2 rfl _ src dst k V rfl
            (hv.mono e1.heap_extends)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hsrc)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1.heap_extends hdst)
          have e12 := e1.heap_extends.trans e2.heap_extends
          have sb := ih _ _ _ _ _ _ iota_lt_calls e3 rfl _ src dst (k + 1) B rfl
            (hb.mono e12)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e12 hsrc)
            (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e12 hdst)
          exact SubstAux.tm_store_letE ((st.mono e2.heap_extends).mono e3.heap_extends)
            (sv.mono e3.heap_extends) sb
        | .Proj (ld12 := ld) (he578 := hr) (hm577 := hm) (ev596 := e1) (ev639 := e2)
            (hc664 := hc) .. =>
          subst hc hr hm
          obtain ⟨a, i, Es, rfl, rfl, ra, hes⟩ := hE.proj_of_load ld
          have hne := tm_proj_resolved hE ld ra
          obtain ⟨hfk_eq, hcase⟩ := famKey_ne_cases hne
          obtain ⟨⟨a', ra', hka⟩, rfl⟩ := Decl.rename_addr_spec e1 ra rm
          have hcaseK : (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨
              Core.keyOf t (ixAddr a) ∈ srcKeys := by
            rcases hcase with hst | hm
            · exact Or.inl hst
            · obtain ⟨b, hb, hab⟩ := List.mem_map.mp hm
              exact Or.inr (List.mem_map.mpr ⟨b, hb, by rw [hab]⟩)
          obtain ⟨ci, hci⟩ := aliasMap_zip_stored hlenK hdst_stored hcaseK
          rw [← hka] at hci
          have hsc_a' : sc.κ (ixAddr a') = Core.keyOf t (ixAddr a') :=
            Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
          have : Resolved (sc.κ (ixAddr a')) := ⟨by rw [hsc_a']; exact Resolved.ne⟩
          have : ProjPermitted sc.κ (ixAddr a') :=
            Core.Ctx.stored_projPermitted_of_find (c := ⟨E₀, env, t, lim⟩) hci
          have ses := ih _ _ _ _ _ _ iota_lt_calls e2 rfl _ src dst k Es rfl hes hsrc hdst
          have hkey_eq : g (famKey t env srcAs (ixAddr a)) = sc.κ (ixAddr a') := by
            rw [hfk_eq]
            exact hka.symm.trans hsc_a'.symm
          simp only [Decl.renameAll, hkey_eq]
          exact SubstAux.tm_store_proj
            (Bytes.repAddressRef_heapMono₂ addrTy e2.heap_extends ra') ses
        | .other (ld12 := ld) (hne84 := n1) (hne184 := n2) (hne297 := n3) (hne410 := n4)
            (hne552 := n5) (hne665 := n6) (he670 := hr) (he671 := hh) .. =>
          subst hr hh
          cases hE with
          | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
          | bvarFree _ _ _ hd => exact nomatch hd
          | sort cell rl hu => exact .sort cell rl hu
          | const cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n1 _ rfl)
          | app cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n2 _ rfl)
          | lam cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n3 _ rfl)
          | forallE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n4 _ rfl)
          | letE cell _ _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n5 _ rfl)
          | litNat cell rl hc => exact .litNat cell rl hc
          | litStr cell rb hs => exact .litStr cell rb hs
          | proj cell _ _ =>
            rw [loadValue_enum_cell cell] at ld
            injection ld with ld; exact absurd ld.symm (n6 _ rfl))
  intro e src dst r h h' cs k E ev hE hsrc hdst
  exact hmain _ _ _ _ _ _ ev rfl e src dst k E rfl hE hsrc hdst

/-- **`KernelModeled::rename_list` into `Core.Ctx.stored`**: lifts `rename_stored_of_src` across a
list of expressions whose heap cells are all stored in `env` or in `srcAs`. -/
theorem rename_list_stored_of_cells {t : Ix.Kernel.RoleTable} (hwf : t.wf = true) {E₀ : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    {srcAs dstAs : List Bytes.Address} {Γ₁ Γ₂ : Nat → KExpr} {k : Nat}
    (hlen : srcAs.length = dstAs.length)
    (hmodels : ∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci) :
    ∀ {Es : List KExpr} {es src dst r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn W "KernelModeled::rename_list" [es, src, dst] h r h' cs →
      RepList kexprListEnum
        (fun h E p => Decl.TmExact (Core.keyOf t) 0 Γ₁ h k E p ∧
          ∀ a, AddrIn h p a →
            (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr)
        h Es es →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst →
      RepList kexprListEnum
        (fun h E p => Decl.TmExact (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ 0 Γ₂ h k E p) h'
        (Es.map (Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
          (dstAs.map fun b => Core.keyOf t (ixAddr b)))))) r
  | [], es, src, dst, r, h, h', cs, ev, hes, _, _ => by
    rcases Obs.«KernelModeled::rename_list».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨_, _, _, _, _, _, _, _, ld, _, _, _, _, _⟩
    · exact .nil (by simp)
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hes ld; cases he
  | E :: Es, es, src, dst, r, h, h', cs, ev, hes, hsrc, hdst => by
    rcases Obs.«KernelModeled::rename_list».obs ev with ⟨ld, _, _, _⟩ |
      ⟨x_e, _, _, _, _, _, _, _, ld, rfl, rfl, ev1, ev2, _⟩
    · cases Lib.rep_nil_of_load hes ld
    · obtain ⟨E', Es', he, ⟨hE, hcellsE⟩, hEs⟩ := Lib.rep_cons_of_load hes ld
      injection he with h1 h2; subst h1 h2
      have sE := rename_stored_of_src (E₀ := E₀) (lim := lim) (Γ₂ := Γ₂) hwf ev1 hlen hsrc hdst
        hE hmodels hcellsE
      have ext1 := ev1.heap_extends
      have hEs_ext := RepLinkedList.mono
        (fun _ _ _ _ ext ⟨hx, hc⟩ =>
          ⟨hx.mono ext, fun a ha => hc a (Binding.TmExact.addrIn_back hx ext a ha)⟩)
        ext1 hEs
      have sEs := rename_list_stored_of_cells (E₀ := E₀) (lim := lim) (Γ₁ := Γ₁) (Γ₂ := Γ₂)
        hwf hlen hmodels ev2 hEs_ext
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hsrc)
        (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext1 hdst)
      exact .cons (by simp) (sE.mono (ev2.heap_extends.trans (Heap.Extends.snoc _ _)))
        (RepLinkedList.mono (fun _ _ _ _ ext x => x.mono ext) (Heap.Extends.snoc _ _) sEs)

/-- Scoped version of `Decl.eq_addr_key_spec`: resolving
`Bytes::address_eq(eqa, KernelRoles::role_addr(rc, KernelRoleSpec::role_eq())) = 1`
identifies `Core.keyOf c.t (ixAddr a_eq) = Ix.Kernel.eqName` via `RoleVal.roles_fn_spec`. -/
theorem eq_addr_key_scoped {c : ScopedCtx} {rc eqa v_role v_raddr : SourceValue F}
    {a_eq : Bytes.Address} {h₀ h₁ h₂ h₃ : Heap F} {cs_role cs_raddr cs_eq : List (Call F)}
    (hwf : c.t.wf = true)
    (hg_raddr : CoreGood c cs_raddr)
    (hrc : RCRep c.t c.lim h₁ rc)
    (ha_eq : Bytes.RepAddressRef addrTy h₂ a_eq eqa)
    (ev_role : ObsFn W "KernelRoleSpec::role_eq" [] h₀ v_role h₁ cs_role)
    (ev_raddr : ObsFn W "KernelRoles::role_addr" [rc, v_role] h₁ v_raddr h₂ cs_raddr)
    (ev_eq : ObsFn W "Bytes::address_eq" [eqa, v_raddr] h₂ (.field 1) h₃ cs_eq) :
    Core.keyOf c.t (ixAddr a_eq) = eqName ∧ h₃ = h₂ := by
  obtain ⟨hv_role, _, _⟩ := Obs.«KernelRoleSpec::role_eq».obs ev_role
  rw [hv_role] at ev_raddr
  have hnum : (8 : F) = roleNum .eq := rfl
  rw [hnum] at ev_raddr
  have hra_fn : Specs.Roles.role_addr c [rc, .field (roleNum .eq)] h₁ v_raddr h₂ cs_raddr :=
    RoleVal.roles_fn_spec c hwf .role_addr _ _ _ _ _ ev_raddr
  obtain ⟨a_tbl, ha_tbl, haddr_of, _⟩ := hra_fn rc .eq rfl hg_raddr hrc
  obtain ⟨heq_f, hh₃⟩ := Lib.address_eq_spec ev_eq ha_eq ha_tbl
  have ha_same : a_eq = a_tbl := by
    by_cases h : a_eq = a_tbl
    · exact h
    · rw [ite_eq_right h] at heq_f
      injection heq_f with hf
      exact absurd hf one_ne_zero
  subst ha_same
  exact ⟨Core.keyOf_of_addressOf hwf haddr_of, hh₃⟩

/-! ## Refinement of `KernelModeled::check_iota_rule` -/

set_option maxHeartbeats 4000000 in
/-- **Refinement of `KernelModeled::check_iota_rule` at one stored prefix `FamilyStepEnv`**:
discharges `RuleFacts` (including `StatementFacts`) from `Decl.CheckIotaRuleInvR`. -/
theorem check_iota_rule_facts
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hSE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env)
    {advAs srcAs dstAs : List Bytes.Address}
    (hlenSD : srcAs.length = dstAs.length)
    (hadvHyp : (∀ a, AdviceIn csFam a → adv a) ∨
      ∀ a, AdviceListedIn advAs a →
        adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x)
    (hdefSrc : ∀ k ∈ srcAs.map fun b => Core.keyOf t (ixAddr b),
      ∃ cvm mval hint, env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) k) = some (.defnInfo cvm mval hint))
    (hmodels : ∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci)
    {blk : List (ConstantInfo .anon)} {tys : List KExpr}
    {recKey : KKey} {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    {r : RecRule .anon} {rhsA : KExpr}
    {cnP cnF : Nat}
    {lvls : List Level} {pins : List KExpr}
    (hlps_lt : lps.length < 4294967296)
    (hlps_perm : lps.Perm (List.range lps.length))
    (hrp_le : rP ≤ mI) (hmi_lt : mI < 288230376151711744)
    (hcnp_lt : cnP < 72057594037927936) (hcnf_lt : cnF < 72057594037927936)
    (hnfields : r.nfields = cnF)
    (hrhs_lbb : r.rhs.looseBVarsBounded 0 = true)
    (hrhs_nofvar : r.rhs.hasFvar = false)
    (hrhs_ann : Annotates rhsA r.rhs)
    (hmaj : majorShape tyA mI rP cnP = some (lvls, pins))
    (hlvls_def : lvls.all (Level.allParamsDefined lps) = true)
    (hpins_ok : pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
      p.allLevelParamsDefined lps) = true)
    (hnp_ty : Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) tyA = true)
    (hleaves : ∀ fvsP crest2, openPisAtFvars rP tyA 0 = some (fvsP, crest2) →
      ∀ p ∈ pins, LeavesFixed (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))))
        (Expr.instSpine (fvsP.take rP) (rP - 1) p))
    {a_rm a_cprj a_t : Bytes.Address}
    {rc rm ty_r rhs cprj cty ilvls pins_ptr t_addr src dst aset : SourceValue F}
    {h : Heap F} {cs_iota : List (Call F)}
    (hsub_iota : SubCalls calls cs_iota)
    (hrc : RCRep t lim h rc)
    (hrm : Bytes.RepAddressRef addrTy h a_rm rm)
    (hrm_key : Core.keyOf t (ixAddr a_rm) =
      aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) recKey)
    (hrm_stored : ∃ ci, env.find? (Core.keyOf t (ixAddr a_rm)) = some ci)
    (hcprj : Bytes.RepAddressRef addrTy h a_cprj cprj)
    (hcprj_key : Core.keyOf t (ixAddr a_cprj) = r.ctor)
    (ha_t : Bytes.RepAddressRef addrTy h a_t t_addr)
    (hsrc : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs src)
    (hdst : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs dst)
    (haset : AddrMapAll addrMapEnum
      (fun _ k _ => AdvChecked calls bAddr t lim csFam advAs k) h aset)
    (hty_rep : Decl.TmCExact (Core.keyOf t) h (Core.posOf lps tyA) ty_r)
    (hty_cells : ∀ a, AddrIn h ty_r a →
      (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr)
    (hrhs_rep : Decl.TmCExact (Core.keyOf t) h (Core.posOf lps rhsA) rhs)
    (hrhs_cells : ∀ a, AddrIn h rhs a →
      (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr)
    (hcty_of_find : ∀ ci_gc,
      env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))) r.ctor) = some ci_gc →
      ∃ cvj : ConstantVal .anon,
        RuleCtor env blk tys r.ctor cvj cnP cnF ∧
        ci_gc.toConstantVal.levelParams.length = cvj.levelParams.length ∧
        cvj.type.allLevelParamsDefined cvj.levelParams = true ∧
        Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) cvj.type = true ∧
        Tm (famKey t env srcAs) 0 zeroGhost h 0 (Core.posOf cvj.levelParams cvj.type) cty)
    (hilvls_rep : RepKLevelList h (lvls.map (Level.subst lps (Core.posLevels lps))) ilvls)
    (hpins_rep : RepList kexprListEnum
      (fun h P p => Decl.TmExact (Core.keyOf t) 0 zeroGhost h rP P p ∧
        ∀ a, AddrIn h p a →
          (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr) h
      (pins.map (Core.posOf lps)) pins_ptr)
    (inv : Decl.CheckIotaRuleInvR rc rm (.field (lps.length : F)) ty_r (.field (rP : F))
      (.field ((mI - rP : Nat) : F)) rhs cprj cty (.field (cnP : F)) (.field (cnF : F))
      ilvls pins_ptr t_addr src dst aset h cs_iota) :
    RuleFacts env (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
      (dstAs.map fun b => Core.keyOf t (ixAddr b))))
      blk tys recKey lps tyA mI rP r rhsA (Core.keyOf t (ixAddr a_t)) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  let srcKeys := srcAs.map fun b => Core.keyOf t (ixAddr b)
  let dstKeys := dstAs.map fun b => Core.keyOf t (ixAddr b)
  let g := aliasMap (srcKeys.zip dstKeys)
  let sc : ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hscf := hSE.prefixInv.scopedCoreFacts
  have hef : CoreEnvFacts sc.toCtx := hscf.1
  have hlf : ScopedLoadFacts sc := hscf.2
  have hgood_all : Good sc.toCtx calls := hSE.store.good env lim
  have hgoodOf : ∀ {cs' : List (Call F)}, SubCalls cs_iota cs' → CoreGood sc cs' := fun hs =>
    CoreGood.ofRaw (hgood_all.sub (hsub_iota.trans hs)) (fun _ _ => trivial)
  have hout : ∀ k, srcKeys.contains k = false → g k = k := fun k hk => aliasMap_out_of_zip hk
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have hval0 : ZMod.val (0 : F) = 0 := ZMod.val_zero
  have hval1 : ZMod.val (1 : F) = 1 := rfl
  have hval2 : ZMod.val (2 : F) = 2 := rfl
  have hval3 : ZMod.val (3 : F) = 3 := rfl
  have hnd_lps : lps.Nodup := hlps_perm.nodup_iff.mpr List.nodup_range
  let nI : Nat := mI - rP
  let depth : Nat := rP + cnF
  have hrp_val : ZMod.val (rP : F) = rP := SubstAux.val_natCast (by omega)
  have hni_val : ZMod.val (nI : F) = nI := SubstAux.val_natCast (by omega)
  have hcnp_val : ZMod.val (cnP : F) = cnP := SubstAux.val_natCast (by omega)
  have hcnf_val : ZMod.val (cnF : F) = cnF := SubstAux.val_natCast (by omega)
  have hnl_val : ZMod.val (lps.length : F) = lps.length := SubstAux.val_natCast (by omega)
  have hmi_val : ZMod.val (mI : F) = mI := SubstAux.val_natCast (by omega)
  have hd_val : ZMod.val (depth : F) = depth := SubstAux.val_natCast (by omega)
  have hmi_eq : inv.mi = .field (mI : F) := by
    rw [SubstAux.add_ok inv.op_mi]; congr 1
    exact ZMod.val_injective _ (by
      rw [SubstAux.val_add (by rw [hrp_val, hni_val]; omega), hrp_val, hni_val, hmi_val]
      omega)
  have hd_eq : inv.d = .field (depth : F) := by
    rw [SubstAux.add_ok inv.op_d]; congr 1
    exact ZMod.val_injective _ (by
      rw [SubstAux.val_add (by rw [hrp_val, hcnf_val]; omega), hrp_val, hcnf_val, hd_val])
  -- 1. `pins.length = cnP`
  have hpins_lt : (pins.map (Core.posOf lps)).length < 2 ^ 39 :=
    IxVM.Refinement.RomBound.bounded_length_lt hbd (hsub_iota _ inv.call_plen) (by simp) hpins_rep
  obtain ⟨hplen_f, h_plen_eq⟩ := Decl.tele_klength inv.ev_plen hpins_rep
  have ev_sc_h := inv.ev_sc
  rw [h_plen_eq] at ev_sc_h
  have hpins_len : pins.length = cnP := by
    injection hplen_f with hf
    have hv := congrArg ZMod.val hf
    rw [hcnp_val, SubstAux.val_natCast (by omega), List.length_map] at hv
    exact hv.symm
  -- 2. Stored `rhsA` front-end (`validate_expr_well_scoped`, `peel_n_lams_collect`, `rename`, `k_infer`)
  have hrhs_pos_tm0 : Decl.TmExact (Core.keyOf t) 0 zeroGhost h 0 (Core.posOf lps rhsA) rhs :=
    hrhs_rep 0 zeroGhost
  have hrhsA_nofvar : rhsA.hasFvar = false := by
    have hf := tmExact_hasFvar_false hrhs_pos_tm0
    unfold Core.posOf at hf
    rwa [Decl.hasFvar_instantiateLevelParams] at hf
  have hrhsA_lvls : rhsA.allLevelParamsDefined lps = true :=
    Decl.allLevelParamsDefined_of_posOf_perm hlps_perm
      (Decl.validate_expr_well_scoped_spec hlps_lt hrhs_pos_tm0 ev_sc_h)
  have ext_sc := ev_sc_h.heap_extends
  have ext_peel_in := ext_sc.trans (Heap.Extends.snoc inv.h_sc (.construct kexprListEnum "Nil" []))
  have ev_peel' := inv.ev_peel
  rw [hd_eq] at ev_peel'
  have hrhsA_lams_pos : ((Core.posOf lps rhsA).stripLams depth).isSome = true := by
    have hs := (Decl.peel_n_lams_collect_spec_wide (by rw [hd_val]; omega) ev_peel'
      (hrhs_pos_tm0.mono ext_peel_in)).1
    rwa [hd_val] at hs
  have hrhsA_lams : (rhsA.stripLams depth).isSome = true := by
    have hcomm : ∀ (m : Nat) (e : KExpr),
        ((Core.posOf lps e).stripLams m).isSome = (e.stripLams m).isSome := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro e; cases e <;> simp [Core.posOf, Expr.instantiateLevelParams, Expr.stripLams]
        case lam _ b _ => exact ih b
    rwa [hcomm] at hrhsA_lams_pos
  have ext_peel := ext_peel_in.trans inv.ev_peel.heap_extends
  have hrhs_cells_peel : ∀ a, AddrIn inv.h_peel rhs a →
      (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr :=
    fun a ha => hrhs_cells a (Binding.TmExact.addrIn_back hrhs_pos_tm0 ext_peel a ha)
  have hrhs_m_raw : Decl.TmExact sc.κ 0 zeroGhost inv.h_rhs_m 0
      (Decl.renameAll g (Core.posOf lps rhsA)) inv.rhs_m :=
    rename_stored_of_src (E₀ := E) (lim := lim) (Γ₂ := zeroGhost) htwf inv.ev_rhs_m hlenSD
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_peel hsrc)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_peel hdst)
      (hrhs_pos_tm0.mono ext_peel) hmodels hrhs_cells_peel
  have ext_rhs_m := ext_peel.trans inv.ev_rhs_m.heap_extends
  have ext_rhs_in := Heap.Extends.snoc inv.h_rhs_m (.construct kexprListEnum "Nil" [])
  obtain ⟨rhs_ty_pos, -, hrhs_inf_raw⟩ :=
    Decl.scoped_core_infer (c := sc)
      (hrc.mono (ext_rhs_m.trans ext_rhs_in))
      (Decl.typesRep_alloc_nil sc.κ zeroGhost inv.h_rhs_m)
      (Decl.ghostScoped_zero zeroGhost) hef hlf (hgoodOf inv.sub_rhs_inf)
      inv.ev_rhs_inf (hrhs_m_raw.mono ext_rhs_in).toTm
  have hrhs_pos_fv : (Core.posOf lps rhsA).hasFvar = false := by
    unfold Core.posOf; rw [Decl.hasFvar_instantiateLevelParams]; exact hrhsA_nofvar
  have hnp_rhs_pos : Decl.NoProjIn srcKeys (Core.posOf lps rhsA) = true :=
    noProjIn_of_renameAll_infer hSE.prefixInv.store.store hdefSrc hrhs_pos_fv hrhs_inf_raw
  have hrhs_ren_eq : Decl.renameAll g (Core.posOf lps rhsA) = Core.posOf lps (rhsA.renameConsts g) := by
    rw [Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp_rhs_pos]
    unfold Core.posOf
    exact (Decl.instantiateLevelParams_renameConsts lps (Core.posLevels lps) g rhsA).symm
  rw [hrhs_ren_eq] at hrhs_m_raw hrhs_inf_raw
  have hrhs_typed : ∃ t', posRulesJ.infer env 0 (rhsA.renameConsts g) t' :=
    ⟨Decl.invPosOf lps rhs_ty_pos, Decl.posRulesJ_infer_of_pos hlps_perm hrhs_inf_raw⟩
  have ext_rhs_inf := ext_rhs_m.trans (ext_rhs_in.trans inv.ev_rhs_inf.heap_extends)
  -- 3. Advice membership & theorem lookup `Ingress::get_ci(t_addr)`
  have hAdv : AdvChecked calls bAddr t lim csFam advAs a_t :=
    Decl.addr_set_member_one_scoped (c := sc) htwf
      (Bytes.repAddressRef_heapMono₂ addrTy ext_rhs_inf ha_t)
      (AddrMapAll.mono (fun _ _ _ _ _ hx => hx) ext_rhs_inf haset)
      inv.ev_aset
  have ext_aset := ext_rhs_inf.trans inv.ev_aset.heap_extends
  have ha_t_aset : Bytes.RepAddressRef addrTy inv.h_aset a_t t_addr :=
    Bytes.repAddressRef_heapMono₂ addrTy ext_aset ha_t
  obtain ⟨ct, dt, hrecT, hinfoT, -, hkindT, hlogT, hcaT, hchkT⟩ :=
    advice_defn_record hbd hS hH hAdv ha_t_aset inv.ev_tci (hsub_iota.trans inv.sub_tci)
      (Or.inr rfl) inv.ld_tci
  obtain ⟨tty₀, ⟨Wt⟩⟩ :=
    advice_checked_type ht hbd hS hrecT hinfoT (Or.inr (hkindT rfl)) hlogT hchkT
      ha_t_aset inv.ev_tci (hsub_iota.trans inv.sub_tci) (Or.inr ⟨inv.w_tval, inv.ld_tci⟩)
  have hadvT : adv (ixAddr a_t) := adv_of_advChecked hAdv hrecT hcaT hadvHyp
  obtain ⟨cvt, vt, hfindT, hpermT_dt, hlvEqT_dt, htty_ex0⟩ :=
    advice_stored_thm_facts hSE hadvT hrecT hcaT ha_t_aset inv.ev_tci
      (hsub_iota.trans inv.sub_tci) inv.ld_tci Wt
  have hdt_lvls : dt.lvls.toNat = lps.length :=
    (nat_eq_of_field_eq_u32' hlps_lt Wt.nlvls_lt (Value.field.inj Wt.nl_eq)).symm
  have hpermT : cvt.levelParams.Perm (List.range lps.length) := hdt_lvls ▸ hpermT_dt
  have htty0_def : tty₀.allLevelParamsDefined (List.range lps.length) = true :=
    hdt_lvls ▸ Wt.ty_levels
  let stmt : KExpr := Decl.invPosOf lps tty₀
  have hstmt_pos : Core.posOf lps stmt = tty₀ := Decl.posOf_invPosOf hlps_perm tty₀
  have htty_rep : Decl.TmCExact sc.κ inv.h_tci (Core.posOf lps stmt) inv.tty := by
    rw [hstmt_pos]; exact htty_ex0
  have ext_tci := ext_aset.trans inv.ev_tci.heap_extends
  -- 4. Opening `tty` at `depth = rP + cnF` (`peel_collect`)
  have ext_open_in := Heap.Extends.snoc inv.h_tci (.construct kexprListEnum "Nil" [])
  have ev_open' := inv.ev_open
  rw [hd_eq] at ev_open'
  obtain ⟨r_tbody, r_ctx, Γ_t, fvs_pos, tbody_pos, htup_open, hopen_pos, -, hΓt_hi,
      htbody_ex, hctx_rep, hsc_t⟩ :=
    Decl.peel_collect_open_exact depth hd_val ev_open'
      ((htty_rep 0 zeroGhost).mono ext_open_in)
      (Decl.typesRep_alloc_nil sc.κ zeroGhost inv.h_tci)
      (Decl.ghostScoped_zero zeroGhost)
  injection htup_open with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
  simp only [Nat.zero_add] at hΓt_hi htbody_ex hctx_rep hsc_t
  obtain ⟨fvs, tbody, hopen_t, hfvs_pos, htbody_pos⟩ := Decl.openPisAtFvars_of_posOf hopen_pos
  subst hfvs_pos
  obtain ⟨hfvs_len, -, hfvs_shape⟩ := Decl.openPisAtFvars_spec depth stmt 0 hopen_t
  have hfvs_pos_len : (fvs.map (Core.posOf lps)).length = depth := by
    rw [List.length_map, hfvs_len]
  have ext_open := ext_tci.trans (ext_open_in.trans inv.ev_open.heap_extends)
  -- 5. Equation spine (`collect_spine(tbody)`, `eqName`, `[ell]`, `targs.length = 3`)
  obtain ⟨r_eqh, r_targs, eqH_pos, targs_pos, htup_tsp, heqH_ex, htargs_rep, htbody_app⟩ :=
    Decl.collect_spine_exact inv.ev_tsp htbody_ex
  injection htup_tsp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
  obtain ⟨a_eq, eqls_pos, rfl, ra_eq, reqls⟩ := heqH_ex.const_of_load inv.ld_eqh
  have hsc_eq_ne := tmExact_const_resolved heqH_ex inv.ld_eqh ra_eq
  have ext_tsp := ext_open.trans inv.ev_tsp.heap_extends
  have ext_req := ext_tsp.trans inv.ev_req.heap_extends
  have ext_raddr := ext_req.trans inv.ev_raddr.heap_extends
  obtain ⟨heq_key_tbl, -⟩ :=
    eq_addr_key_scoped (c := sc) htwf (hgoodOf inv.sub_raddr) (hrc.mono ext_req)
      (Bytes.repAddressRef_heapMono₂ addrTy
        (inv.ev_req.heap_extends.trans inv.ev_raddr.heap_extends) ra_eq)
      inv.ev_req inv.ev_raddr inv.ev_eqa
  have heq_key : sc.κ (ixAddr a_eq) = eqName :=
    (sc.key_eq hsc_eq_ne).trans heq_key_tbl
  have ext_tsp_eqa := inv.ev_req.heap_extends.trans
    (inv.ev_raddr.heap_extends.trans inv.ev_eqa.heap_extends)
  have reqls_eqa := reqls.mono ext_tsp_eqa
  have hld_eqls1' := inv.ld_eqls1
  have hld_eqls2' := inv.ld_eqls2
  rw [klevelListEnum_eq] at hld_eqls1' hld_eqls2'
  obtain ⟨ell_pos, eqls_tail, heqls_cons, rell_pos, reqls_tail⟩ :=
    Lib.rep_cons_of_load reqls_eqa hld_eqls1'
  obtain rfl := Lib.rep_nil_of_load reqls_tail hld_eqls2'
  subst heqls_cons
  let ell_lps : KLevel := Decl.invPosLevel lps ell_pos
  have hell_subst : Level.subst lps (Core.posLevels lps) ell_lps = ell_pos :=
    Decl.subst_invPosLevel hlps_perm ell_pos
  have heq_head : tbody.getAppFn = .const eqName [ell_lps] := by
    have hfn_pos : tbody_pos.getAppFn = .const eqName [ell_pos] := by
      rw [htbody_app, Decl.getAppFn_mkAppN, heq_key]; rfl
    rw [htbody_pos, ← hell_subst] at hfn_pos
    exact Decl.posOf_inj hlps_perm (by
      show Core.posOf lps tbody.getAppFn = Core.posOf lps (.const eqName [ell_lps])
      unfold Core.posOf
      rw [← Decl.getAppFn_instantiateLevelParams]
      exact hfn_pos)
  have hisEq : isEqHead tbody.getAppFn = true := by rw [heq_head]; simp [isEqHead]
  have htargs_pos_eq : targs_pos = tbody.getAppArgs.map (Core.posOf lps) := by
    have h1 : tbody_pos.getAppArgs = targs_pos := by
      rw [htbody_app, Decl.getAppArgs_mkAppN]; rfl
    rw [htbody_pos] at h1
    unfold Core.posOf at h1
    rw [Decl.getAppArgs_instantiateLevelParams] at h1
    exact h1.symm
  have htargs_eqa := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_tsp_eqa htargs_rep
  have htargs_lt : targs_pos.length < 2 ^ 39 :=
    IxVM.Refinement.RomBound.bounded_length_lt hbd (hsub_iota _ inv.call_tlen) (by simp) htargs_eqa
  obtain ⟨htlen_f, -⟩ := Decl.tele_klength inv.ev_tlen htargs_eqa
  have htargs_len : tbody.getAppArgs.length = 3 := by
    injection htlen_f with hf
    have hv := congrArg ZMod.val hf
    rw [hval3, SubstAux.val_natCast (by omega), htargs_pos_eq, List.length_map] at hv
    exact hv.symm
  let alphaS := tbody.getAppArgs.getD 0 (.bvar 0)
  let lhsS := tbody.getAppArgs.getD 1 (.bvar 0)
  let rhsS := tbody.getAppArgs.getD 2 (.bvar 0)
  have htargs_tlen := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    inv.ev_tlen.heap_extends htargs_eqa
  obtain ⟨⟨alpha_pos, ha0_get, halpha_tlen⟩, -⟩ := Decl.tele_klookup inv.ev_a0 htargs_tlen
  have htargs_a0 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    inv.ev_a0.heap_extends htargs_tlen
  obtain ⟨⟨lhs_pos, ha1_get, hlhs_a0⟩, -⟩ := Decl.tele_klookup inv.ev_a1 htargs_a0
  have htargs_a1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    inv.ev_a1.heap_extends htargs_a0
  obtain ⟨⟨rhsS_pos, ha2_get, hrhsS_a1⟩, -⟩ := Decl.tele_klookup inv.ev_a2 htargs_a1
  have halpha_ex := halpha_tlen.mono
    (inv.ev_a0.heap_extends.trans (inv.ev_a1.heap_extends.trans inv.ev_a2.heap_extends))
  have hlhs_ex := hlhs_a0.mono (inv.ev_a1.heap_extends.trans inv.ev_a2.heap_extends)
  have hrhsS_ex := hrhsS_a1.mono inv.ev_a2.heap_extends
  have ext_eqa_a2 := inv.ev_tlen.heap_extends.trans
    (inv.ev_a0.heap_extends.trans (inv.ev_a1.heap_extends.trans inv.ev_a2.heap_extends))
  have ext_raddr_a2 := inv.ev_eqa.heap_extends.trans ext_eqa_a2
  have ext_a2 := ext_raddr.trans ext_raddr_a2
  rw [hval0, htargs_pos_eq, List.getElem?_map] at ha0_get
  rw [hval1, htargs_pos_eq, List.getElem?_map] at ha1_get
  rw [hval2, htargs_pos_eq, List.getElem?_map] at ha2_get
  have halpha_pos : alpha_pos = Core.posOf lps alphaS := by
    have h0 : tbody.getAppArgs[0]? = some alphaS := by
      cases hts : tbody.getAppArgs with
      | nil => simp [hts] at htargs_len
      | cons x0 xs => simp [alphaS, hts]
    rw [h0] at ha0_get; injection ha0_get with h0'; exact h0'.symm
  have hlhs_pos : lhs_pos = Core.posOf lps lhsS := by
    have h1 : tbody.getAppArgs[1]? = some lhsS := by
      rcases hts : tbody.getAppArgs with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
      · simp [hts] at htargs_len
      · simp [hts] at htargs_len
      · simp [lhsS, hts]
    rw [h1] at ha1_get; injection ha1_get with h1'; exact h1'.symm
  have hrhsS_pos : rhsS_pos = Core.posOf lps rhsS := by
    have h2 : tbody.getAppArgs[2]? = some rhsS := by
      rcases hts : tbody.getAppArgs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, xs⟩⟩⟩
      · simp [hts] at htargs_len
      · simp [hts] at htargs_len
      · simp [hts] at htargs_len
      · simp [rhsS, hts]
    rw [h2] at ha2_get; injection ha2_get with h2'; exact h2'.symm
  subst halpha_pos hlhs_pos hrhsS_pos
  -- 6. Left-hand side spine, head, prefix variables, and major premise
  obtain ⟨r_lh, r_largs, lh_pos, largs_pos, htup_lsp, hlh_ex, hlargs_rep, hlhs_app⟩ :=
    Decl.collect_spine_exact inv.ev_lsp hlhs_ex
  injection htup_lsp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
  have hplvls_rep := Decl.build_param_lvls_range_spec (by rw [hnl_val]; exact hlps_lt) inv.ev_plvls
  rw [hnl_val] at hplvls_rep
  have ext_lsp := inv.ev_lsp.heap_extends
  have ext_plvls := ext_lsp.trans inv.ev_plvls.heap_extends
  have ext_rhead := Heap.Extends.snoc inv.h_plvls (.construct kexprEnum "Const" [rm, inv.v_plvls])
  have ext_h_to_rhead := ext_a2.trans (ext_plvls.trans ext_rhead)
  obtain ⟨ci_rm, hci_rm⟩ := hrm_stored
  have hsc_rm_tbl : sc.κ (ixAddr a_rm) = Core.keyOf t (ixAddr a_rm) :=
    Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hci_rm
  have hsc_rm : sc.κ (ixAddr a_rm) = g recKey := hsc_rm_tbl.trans hrm_key
  have : Resolved (sc.κ (ixAddr a_rm)) := ⟨by rw [hsc_rm_tbl]; exact Resolved.ne⟩
  have hrhead_ex : Decl.TmExact sc.κ depth Γ_t
      (inv.h_plvls ++ [.construct kexprEnum "Const" [rm, inv.v_plvls]]) 0
      (Core.posOf lps (.const (g recKey) (lps.map .param)))
      (.ptr (.enum kexprEnum) inv.h_plvls.length) := by
    rw [Decl.posOf_const_self_levels lps (g recKey) hnd_lps, ← hsc_rm]
    exact .const (by simp)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_to_rhead hrm)
      (hplvls_rep.mono ext_rhead)
  have hlh_eq_pos : lh_pos = Core.posOf lps (.const (g recKey) (lps.map .param)) :=
    Decl.kexpr_struct_eq_one (hlh_ex.mono (inv.ev_plvls.heap_extends.trans ext_rhead))
      hrhead_ex inv.ev_lheq
  have hlhs_fn : lhsS.getAppFn = .const (g recKey) (lps.map .param) := by
    have hfn_pos : (Core.posOf lps lhsS).getAppFn =
        Core.posOf lps (.const (g recKey) (lps.map .param)) := by
      rw [hlhs_app, Decl.getAppFn_mkAppN, hlh_eq_pos,
        Decl.posOf_const_self_levels lps (g recKey) hnd_lps]; rfl
    exact Decl.posOf_inj hlps_perm (by
      unfold Core.posOf at hfn_pos ⊢
      rwa [← Decl.getAppFn_instantiateLevelParams])
  have hlargs_pos_eq : largs_pos = lhsS.getAppArgs.map (Core.posOf lps) := by
    have h1 : (Core.posOf lps lhsS).getAppArgs = largs_pos := by
      rw [hlhs_app, Decl.getAppArgs_mkAppN, hlh_eq_pos,
        Decl.posOf_const_self_levels lps (g recKey) hnd_lps]; rfl
    unfold Core.posOf at h1
    rw [Decl.getAppArgs_instantiateLevelParams] at h1
    exact h1.symm
  have ext_lsp_lheq := inv.ev_plvls.heap_extends.trans
    (ext_rhead.trans inv.ev_lheq.heap_extends)
  have hlargs_lheq := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_lsp_lheq hlargs_rep
  have hlargs_lt : largs_pos.length < 2 ^ 39 :=
    IxVM.Refinement.RomBound.bounded_length_lt hbd (hsub_iota _ inv.call_llen) (by simp) hlargs_lheq
  obtain ⟨hllen_f, -⟩ := Decl.tele_klength inv.ev_llen hlargs_lheq
  have hlargs_len : lhsS.getAppArgs.length = mI + 1 := by
    have hmi1_eq := inv.op_mi1
    rw [hmi_eq] at hmi1_eq
    rw [SubstAux.add_ok hmi1_eq] at hllen_f
    injection hllen_f with hf
    have hv := congrArg ZMod.val hf
    rw [SubstAux.val_natCast (by omega), SubstAux.val_add (by omega), hmi_val, hval1,
      hlargs_pos_eq, List.length_map] at hv
    exact hv.symm
  -- Prefix check: `largs.take rP = fvs.take rP`
  have hlargs_llen := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    inv.ev_llen.heap_extends hlargs_lheq
  obtain ⟨-, hltake_rep⟩ := Decl.tele_ktake (fun _ _ _ _ e x => x.mono e) inv.ev_ltake hlargs_llen
  rw [hrp_val] at hltake_rep
  have ev_bvd1' := inv.ev_bvd1
  rw [hd_eq] at ev_bvd1'
  have hbvd1_rep := Decl.bvars_desc_exact_wide (κ := sc.κ) (d := depth) (Γ := Γ_t)
    (by rw [hrp_val, hd_val]; omega) (by rw [hd_val]) (by omega) ev_bvd1'
  rw [hrp_val, hd_val, Nat.sub_self] at hbvd1_rep
  have hbvd1_fvs :
      ((List.range rP).map fun m => Expr.fvar (0 + m) (Γ_t (0 + m))) =
        (fvs.take rP).map (Core.posOf lps) := by
    apply List.ext_getElem (by simp [hfvs_len]; omega)
    intro m hm1 hm2
    simp only [List.length_map, List.length_range] at hm1
    have hm_lt : m < (fvs.map (Core.posOf lps)).length := by rw [hfvs_pos_len]; omega
    have hΓm := hΓt_hi m hm_lt
    have hm_fvs : m < fvs.length := by rw [hfvs_len]; omega
    have hsh := hfvs_shape m hm_fvs
    rw [Nat.zero_add] at hsh
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, Nat.zero_add, hΓm]
    rw [hsh]
    simp [Core.posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
  rw [hbvd1_fvs] at hbvd1_rep
  have hltake_eq_pos :
      largs_pos.take rP = (fvs.take rP).map (Core.posOf lps) :=
    Decl.spec_params_ptr_eq_one (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
      inv.ev_bvd1.heap_extends hltake_rep) hbvd1_rep inv.ev_pref
  have hlargs_pre : lhsS.getAppArgs.take rP = fvs.take rP := by
    rw [hlargs_pos_eq, ← List.map_take] at hltake_eq_pos
    exact (List.map_injective_iff.mpr fun _ _ h' => Decl.posOf_inj hlps_perm h') hltake_eq_pos
  -- Major premise check
  have ext_lheq_pref := inv.ev_llen.heap_extends.trans (inv.ev_ltake.heap_extends.trans
    (inv.ev_bvd1.heap_extends.trans inv.ev_pref.heap_extends))
  have hlargs_pref := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_lheq_pref hlargs_lheq
  have ev_maj' := inv.ev_maj
  rw [hmi_eq] at ev_maj'
  obtain ⟨⟨major_pos, hmaj_get, hmaj_ex⟩, -⟩ := Decl.tele_klookup ev_maj' hlargs_pref
  rw [hmi_val, hlargs_pos_eq, List.getElem?_map] at hmaj_get
  have hmaj_last : major_pos = Core.posOf lps (lhsS.getAppArgs.getLastD (.bvar 0)) := by
    cases hget_m : lhsS.getAppArgs[mI]? with
    | none => simp [hget_m] at hmaj_get
    | some mj =>
      rw [hget_m] at hmaj_get; injection hmaj_get with hmj; subst hmj
      rw [getLastD_eq_of_getElem? lhsS.getAppArgs mI mj (.bvar 0) hlargs_len hget_m]
  have ext_h_pref := ext_a2.trans (inv.ev_lsp.heap_extends.trans
    (ext_lsp_lheq.trans ext_lheq_pref))
  have ext_h_maj := ext_h_pref.trans inv.ev_maj.heap_extends
  have hrm_tbl := renameMap_aliasMap htwf hlenSD
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_maj hsrc)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_maj hdst)
  obtain ⟨⟨a_cren, ra_cren_maj, hcren_key⟩, -⟩ :=
    Decl.rename_addr_spec inv.ev_cren
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_maj hcprj) hrm_tbl
  have ra_cren := Bytes.repAddressRef_heapMono₂ addrTy inv.ev_cren.heap_extends ra_cren_maj
  rw [hcprj_key] at hcren_key
  have ext_h_cren := ext_h_maj.trans inv.ev_cren.heap_extends
  have hpins_ren_rep := rename_list_stored_of_cells (E₀ := E) (lim := lim)
    (Γ₁ := zeroGhost) (Γ₂ := zeroGhost) htwf hlenSD hmodels inv.ev_pren
    (RepLinkedList.mono
      (fun _ _ _ _ e ⟨hx, hc⟩ => ⟨hx.mono e, fun a ha => hc a (Binding.TmExact.addrIn_back hx e a ha)⟩)
      ext_h_cren hpins_rep)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_cren hsrc)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_cren hdst)
  have hnp_pins : ∀ p ∈ pins, Decl.NoProjIn srcKeys p = true :=
    noProjIn_of_majorShape hnp_ty hmaj
  have hpins_ren_eq :
      (pins.map (Core.posOf lps)).map (Decl.renameAll g) =
        (pins.map (·.renameConsts g)).map (Core.posOf lps) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    have hnp_p : Decl.NoProjIn srcKeys (Core.posOf lps p) = true := by
      unfold Core.posOf; rw [Decl.noProjIn_instantiateLevelParams]; exact hnp_pins p hp
    rw [Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp_p]
    unfold Core.posOf
    exact (Decl.instantiateLevelParams_renameConsts lps (Core.posLevels lps) g p).symm
  rw [hpins_ren_eq] at hpins_ren_rep
  -- Open `pins_ren` at `fvs.take rP`, then `lift_list` by `cnF` to `depth`
  let pinsF_lps : List KExpr :=
    pins.map fun p => Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts g)
  have hpins_ren_open :
      RepList kexprListEnum (fun h P p => Decl.TmExact sc.κ rP Γ_t h 0 P p) inv.h_pren
        (pinsF_lps.map (Core.posOf lps)) inv.pins_ren := by
    have hlist_eq :
        ((pins.map (·.renameConsts g)).map (Core.posOf lps)).map
          (fun P => Expr.instSpine ((List.range rP).map fun j => .fvar j (Γ_t j)) (rP - 1) P) =
          pinsF_lps.map (Core.posOf lps) := by
      have hpre_eq : ((List.range rP).map fun j => Expr.fvar j (Γ_t j)) =
          (fvs.take rP).map (Core.posOf lps) := by
        simpa [Nat.zero_add] using hbvd1_fvs
      rw [hpre_eq, List.map_map, List.map_map]
      dsimp only [pinsF_lps]
      rw [List.map_map]
      apply List.map_congr_left
      intro p _; simp only [Function.comp_apply]
      unfold Core.posOf
      exact (Decl.instantiateLevelParams_instSpine lps (Core.posLevels lps)
        (fvs.take rP) (rP - 1) (p.renameConsts g)).symm
    rw [← hlist_eq]
    exact repList_map_rel (fun _ _ hh => hh.open_prefix_eq (Γ := Γ_t)) hpins_ren_rep
  have hpd_rep := Decl.lift_list_exact (bounded_sub (hsub_iota.trans inv.sub_pd) hbd)
    (by rw [hcnf_val]; omega) inv.ev_pd hpins_ren_open
  rw [hcnf_val] at hpd_rep
  have ext_pd_c := Heap.Extends.snoc inv.h_pd (.construct kexprEnum "Const" [inv.cren, ilvls])
  have ext_pref_pren := inv.ev_maj.heap_extends.trans
    (inv.ev_cren.heap_extends.trans inv.ev_pren.heap_extends)
  have ext_h_pd := ext_h_pref.trans (ext_pref_pren.trans inv.ev_pd.heap_extends)
  have hchead_exp_ex : Decl.TmExact (Core.keyOf t) depth Γ_t
      (inv.h_pd ++ [.construct kexprEnum "Const" [inv.cren, ilvls]]) 0
      (Core.posOf lps (.const (g r.ctor) lvls))
      (.ptr (.enum kexprEnum) inv.h_pd.length) := by
    unfold Core.posOf
    simp only [Expr.instantiateLevelParams]
    have hcren_g : g r.ctor = Core.keyOf t (ixAddr a_cren) := hcren_key.symm
    rw [hcren_g]
    exact .const (by simp)
      (Bytes.repAddressRef_heapMono₂ addrTy
        (inv.ev_pren.heap_extends.trans (inv.ev_pd.heap_extends.trans ext_pd_c)) ra_cren)
      (hilvls_rep.mono (ext_h_pd.trans ext_pd_c))
  have hbvd2_rep := Decl.bvars_desc_exact_wide (κ := Core.keyOf t) (d := depth) (Γ := Γ_t)
    (by rw [hcnf_val]) (by rw [hcnf_val]; omega) (by omega) inv.ev_bvd2
  rw [hcnf_val, show depth - cnF = rP by omega] at hbvd2_rep
  have hbvd2_fvs :
      ((List.range cnF).map fun m => Expr.fvar (rP + m) (Γ_t (rP + m))) =
        (fvs.drop rP).map (Core.posOf lps) := by
    apply List.ext_getElem (by simp [hfvs_len]; omega)
    intro m hm1 hm2
    simp only [List.length_map, List.length_range] at hm1
    have hm_lt : rP + m < (fvs.map (Core.posOf lps)).length := by rw [hfvs_pos_len]; omega
    have hΓm := hΓt_hi (rP + m) hm_lt
    have hm_fvs : rP + m < fvs.length := by rw [hfvs_len]; omega
    have hsh := hfvs_shape (rP + m) hm_fvs
    rw [Nat.zero_add] at hsh
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop, hΓm]
    rw [hsh]
    simp [Core.posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
  rw [hbvd2_fvs] at hbvd2_rep
  have hcat_rep := Decl.tele_kconcat (fun _ _ _ _ e x => x.mono e) inv.ev_cat
    (repList_imp (fun _ _ x => tmExact_rekey_stored_to_table x)
      (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
        (ext_pd_c.trans inv.ev_bvd2.heap_extends) hpd_rep))
    hbvd2_rep
  have hexp_ex := Decl.apply_spine_exact inv.ev_exp
    (hchead_exp_ex.mono (inv.ev_bvd2.heap_extends.trans inv.ev_cat.heap_extends)) hcat_rep
  have hexp_pos_eq :
      Expr.mkAppN (Core.posOf lps (.const (g r.ctor) lvls))
        (pinsF_lps.map (Core.posOf lps) ++ (fvs.drop rP).map (Core.posOf lps)) =
        Core.posOf lps (Expr.mkAppN (.const (g r.ctor) lvls) (pinsF_lps ++ fvs.drop rP)) := by
    rw [← List.map_append]
    unfold Core.posOf
    exact (Decl.mkAppN_instantiateLevelParams lps (Core.posLevels lps)
      (pinsF_lps ++ fvs.drop rP) (.const (g r.ctor) lvls)).symm
  rw [hexp_pos_eq] at hexp_ex
  have ext_pref_exp := ext_pref_pren.trans (inv.ev_pd.heap_extends.trans
    (ext_pd_c.trans (inv.ev_bvd2.heap_extends.trans
      (inv.ev_cat.heap_extends.trans inv.ev_exp.heap_extends))))
  have hmajor_pos_eq := Decl.kexpr_struct_eq_one
    (tmExact_rekey_stored_to_table (hmaj_ex.mono ext_pref_exp)) hexp_ex inv.ev_majeq
  rw [hmaj_last] at hmajor_pos_eq
  have hmajor_eq :
      lhsS.getAppArgs.getLastD (.bvar 0) =
        Expr.mkAppN (.const (g r.ctor) lvls) (pinsF_lps ++ fvs.drop rP) :=
    Decl.posOf_inj hlps_perm hmajor_pos_eq
  -- Heap extensions down to `ev_derhs` (needed early so `ev_tl` gives `hlvls_len`!)
  have ext_majeq_deidx := inv.ev_ctyl.heap_extends.trans (inv.ev_peel0.heap_extends.trans
    (inv.ev_csp0.heap_extends.trans (inv.ev_cty_ren.heap_extends.trans
      (inv.ev_crest.heap_extends.trans
        ((Heap.Extends.snoc inv.h_crest (.construct kexprListEnum "Nil" [])).trans
          (inv.ev_cres.heap_extends.trans (inv.ev_csp.heap_extends.trans
            (inv.ev_clen.heap_extends.trans (inv.ev_ldrop.heap_extends.trans
              (inv.ev_idxl.heap_extends.trans (inv.ev_idxr.heap_extends.trans
                inv.ev_deidx.heap_extends)))))))))))
  have ext_deidx_dt1 := inv.ev_ty_m.heap_extends.trans
    ((Heap.Extends.snoc inv.h_ty_m (.construct kexprListEnum "Nil" [])).trans inv.ev_dt1.heap_extends)
  have ext_dt1_dt2 := inv.ev_tty_rp.heap_extends.trans
    (inv.ev_ctx_rp.heap_extends.trans inv.ev_dt2.heap_extends)
  have ext_dt2_lt1 := (Heap.Extends.snoc inv.h_dt2 (.construct kexprListEnum "Nil" [])).trans
    (inv.ev_ctxp.heap_extends.trans (inv.ev_cty_ren2.heap_extends.trans
      (inv.ev_crestp.heap_extends.trans
        ((Heap.Extends.snoc inv.h_crestp (.construct kexprListEnum "Nil" [])).trans
          inv.ev_lt1.heap_extends))))
  have ext_lt1_derhs := inv.ev_lt2.heap_extends.trans (inv.ev_bvd3.heap_extends.trans
    (inv.ev_rhsapp.heap_extends.trans inv.ev_derhs.heap_extends))
  have ext_majeq_derhs := ext_majeq_deidx.trans (ext_deidx_dt1.trans
    (ext_dt1_dt2.trans (ext_dt2_lt1.trans ext_lt1_derhs)))
  have ext_a2_majeq := inv.ev_lsp.heap_extends.trans (ext_lsp_lheq.trans
    (ext_lheq_pref.trans (ext_pref_exp.trans inv.ev_majeq.heap_extends)))
  have ext_a2_derhs := ext_a2_majeq.trans ext_majeq_derhs
  have ext_open_derhs := inv.ev_tsp.heap_extends.trans (inv.ev_req.heap_extends.trans
    (inv.ev_raddr.heap_extends.trans (ext_raddr_a2.trans ext_a2_derhs)))
  have ext_h_derhs := ext_open.trans ext_open_derhs
  -- 6b. `lhsS : alphaS`, `rhsS : alphaS`, and `hlvls_len : lvls.length = cvj.levelParams.length`
  obtain ⟨tl_pos, htl_tm, htl_inf⟩ :=
    Decl.scoped_core_infer (c := sc) (hrc.mono ext_h_derhs)
      (hctx_rep.mono ext_open_derhs) hsc_t hef hlf (hgoodOf inv.sub_tl) inv.ev_tl
      (hlhs_ex.toTm.mono ext_a2_derhs)
  have e_tl := inv.ev_tl.heap_extends
  have htl_de :=
    Decl.scoped_core_defeq (c := sc) (hrc.mono (ext_h_derhs.trans e_tl))
      (hctx_rep.mono (ext_open_derhs.trans e_tl)) hsc_t hef hlf (hgoodOf inv.sub_detl) inv.ev_detl
      htl_tm (halpha_ex.toTm.mono (ext_a2_derhs.trans e_tl))
  have e_detl := e_tl.trans inv.ev_detl.heap_extends
  obtain ⟨tr_pos, htr_tm, htr_inf⟩ :=
    Decl.scoped_core_infer (c := sc) (hrc.mono (ext_h_derhs.trans e_detl))
      (hctx_rep.mono (ext_open_derhs.trans e_detl)) hsc_t hef hlf (hgoodOf inv.sub_tr) inv.ev_tr
      (hrhsS_ex.toTm.mono (ext_a2_derhs.trans e_detl))
  have e_tr := e_detl.trans inv.ev_tr.heap_extends
  have htr_de :=
    Decl.scoped_core_defeq (c := sc) (hrc.mono (ext_h_derhs.trans e_tr))
      (hctx_rep.mono (ext_open_derhs.trans e_tr)) hsc_t hef hlf (hgoodOf inv.sub_detr) inv.ev_detr
      htr_tm (halpha_ex.toTm.mono (ext_a2_derhs.trans e_tr))
  have hgc_info : ∃ ci_gc, env.find? (g r.ctor) = some ci_gc ∧
      lvls.length = ci_gc.toConstantVal.levelParams.length := by
    have hmem_maj : Core.posOf lps (lhsS.getAppArgs.getLastD (.bvar 0)) ∈ largs_pos := by
      rw [← hmaj_last]
      have hmi_lt_largs : mI < lhsS.getAppArgs.length := by omega
      have hget : lhsS.getAppArgs[mI]? = some (lhsS.getAppArgs[mI]) := List.getElem?_eq_getElem hmi_lt_largs
      rw [hmaj_last, getLastD_eq_of_getElem? lhsS.getAppArgs mI _ (.bvar 0) hlargs_len hget,
        hlargs_pos_eq]
      exact List.mem_map_of_mem (List.getElem_mem hmi_lt_largs)
    have htl_inf' := htl_inf
    rw [hlhs_app] at htl_inf'
    obtain ⟨Tmaj, hmaj_inf⟩ := infer_mkAppN_mem htl_inf' hmem_maj
    rw [hmajor_eq, ← hexp_pos_eq] at hmaj_inf
    obtain ⟨Tc, hc_inf⟩ := infer_mkAppN_fn hmaj_inf
    unfold Core.posOf at hc_inf
    simp only [Expr.instantiateLevelParams] at hc_inf
    cases hc_inf with
    | const hfc _ hlen_us =>
      rw [List.length_map] at hlen_us
      exact ⟨_, hfc, hlen_us⟩
  obtain ⟨ci_gc, hci_gc, hlvls_gc⟩ := hgc_info
  obtain ⟨cvj, hruleCtor, hci_gc_lvls, hcvj_def, hnp_cty, hcty_rep⟩ := hcty_of_find ci_gc hci_gc
  have hlvls_len : lvls.length = cvj.levelParams.length := hlvls_gc.trans hci_gc_lvls
  -- 7. Constructor telescope (`cty_l`, `ctorTeleOk`, `crest`, `cres`, index `defeq_list_ok`)
  have ext_h_majeq := ext_h_pref.trans (ext_pref_exp.trans inv.ev_majeq.heap_extends)
  let cty_inst : KExpr := cvj.type.instantiateLevelParams cvj.levelParams lvls
  have hctyl_tm0 : Tm (famKey t env srcAs) 0 zeroGhost inv.h_ctyl 0
      (Core.posOf lps cty_inst) inv.cty_l := by
    have hinst := SubstAux.gall (famKey t env srcAs) .expr_inst_levels [cty, ilvls] inv.h_majeq
      inv.cty_l inv.h_ctyl inv.cs_ctyl inv.ev_ctyl cty ilvls rfl
      (bounded_sub (hsub_iota.trans inv.sub_ctyl) hbd) zeroGhost 0
      (Core.posOf cvj.levelParams cvj.type) (lvls.map (Level.subst lps (Core.posLevels lps)))
      (hcty_rep.mono ext_h_majeq)
      ⟨_, hilvls_rep.mono ext_h_majeq, LvEqList.refl _⟩
    rwa [Decl.posOf_instantiateLevelParams_eq hlvls_len hcvj_def] at hinst
  have hcnp_cnf_eq : inv.cnp_cnf = .field ((cnP + cnF : Nat) : F) := by
    rw [SubstAux.add_ok inv.op_cnp_cnf]; congr 1
    exact ZMod.val_injective _ (by
      rw [SubstAux.val_add (by rw [hcnp_val, hcnf_val]; omega), hcnp_val, hcnf_val,
        SubstAux.val_natCast (by omega)])
  have ev_peel0' := inv.ev_peel0
  rw [hcnp_cnf_eq] at ev_peel0'
  obtain ⟨bs0_pos, rem0_pos, hstrip0_pos, hrem0_ctyl, -⟩ :=
    Decl.peel_n_foralls_tm (cnP + cnF) (SubstAux.val_natCast (by omega)) ev_peel0' hctyl_tm0
  have hrem0_tm := hrem0_ctyl.mono inv.ev_peel0.heap_extends
  rw [Nat.zero_add] at hrem0_tm
  obtain ⟨r_ch0, r_ca0, ch0_pos, ca0_pos, htup_csp0, hch0_tm, -, hrem0_app⟩ :=
    SubstAux.gall (famKey t env srcAs) .collect_spine [inv.v_peel0] inv.h_peel0
      (.tuple [inv.chead0, inv.cargs0]) inv.h_csp0 inv.cs_csp0 inv.ev_csp0 inv.v_peel0 rfl
      (bounded_sub (hsub_iota.trans inv.sub_csp0) hbd) 0 zeroGhost (cnP + cnF) rem0_pos hrem0_tm
  injection htup_csp0 with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
  obtain ⟨a_ch0, us_ch0, rfl, -, -, -, -⟩ := hch0_tm.const_of_load inv.ld_chead0
  have hrem0_fn : rem0_pos.getAppFn = .const (famKey t env srcAs (ixAddr a_ch0)) us_ch0 := by
    rw [hrem0_app, Decl.getAppFn_mkAppN]; rfl
  obtain ⟨bs_inst, cbody_inst, usc_inst, hstrip_inst, hfn_inst, -⟩ :=
    stripPis_constHead_of_instantiateLevelParams lps (Core.posLevels lps) (cnP + cnF) cty_inst
      hstrip0_pos hrem0_fn
  obtain ⟨cbinders, cbody0, usc0, hstrip_cvj, hfn_cvj, hctor_tele⟩ :=
    stripPis_constHead_of_instantiateLevelParams cvj.levelParams lvls (cnP + cnF) cvj.type
      hstrip_inst hfn_inst
  have ext_ctyl_csp0 := inv.ev_peel0.heap_extends.trans inv.ev_csp0.heap_extends
  have ext_h_csp0 := ext_h_majeq.trans (inv.ev_ctyl.heap_extends.trans ext_ctyl_csp0)
  have hcty_ren_tm0 : Tm sc.κ 0 zeroGhost inv.h_cty_ren 0
      (Core.posOf lps (cty_inst.renameConsts g)) inv.v_cty_ren := by
    have hr := rename_tm_stored (E₀ := E) (lim := lim) (Γ₁ := zeroGhost) (Γ₂ := zeroGhost)
      htwf hlenSD hmodels inv.ev_cty_ren (hctyl_tm0.mono ext_ctyl_csp0)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_csp0 hsrc)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_csp0 hdst)
    have hnp_inst : Decl.NoProjIn srcKeys (Core.posOf lps cty_inst) = true := by
      unfold Core.posOf cty_inst
      rw [Decl.noProjIn_instantiateLevelParams, Decl.noProjIn_instantiateLevelParams]
      exact hnp_cty
    rw [Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp_inst] at hr
    have hcomm : (Core.posOf lps cty_inst).renameConsts g =
        Core.posOf lps (cty_inst.renameConsts g) := by
      unfold Core.posOf
      exact (Decl.instantiateLevelParams_renameConsts lps (Core.posLevels lps) g cty_inst).symm
    rwa [hcomm] at hr
  have ext_pren_ctyren := inv.ev_pd.heap_extends.trans (ext_pd_c.trans
    (inv.ev_bvd2.heap_extends.trans (inv.ev_cat.heap_extends.trans
      (inv.ev_exp.heap_extends.trans (inv.ev_majeq.heap_extends.trans
        (inv.ev_ctyl.heap_extends.trans (ext_ctyl_csp0.trans inv.ev_cty_ren.heap_extends)))))))
  have hpins_ren_tm_rp :
      RepList kexprListEnum (fun h P p => Tm sc.κ rP Γ_t h 0 P p) inv.h_cty_ren
        (pinsF_lps.map (Core.posOf lps)) inv.pins_ren :=
    repList_imp (fun _ _ hh => hh.toTm)
      (RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_pren_ctyren hpins_ren_open)
  obtain ⟨cdoms1_pos, crest_pos, hinst_c1_pos, hcrest_tm⟩ :=
    Decl.inst_params_tm (bounded_sub (hsub_iota.trans inv.sub_crest) hbd) inv.ev_crest
      (hcty_ren_tm0.of_depth_zero rP) hpins_ren_tm_rp
  obtain ⟨cdoms1, crest_lps, hinst_c1, hcdoms1_pos, hcrest_pos⟩ :=
    Decl.instPisAt_of_posOf hinst_c1_pos
  subst hcdoms1_pos hcrest_pos
  have ext_crest_in := Heap.Extends.snoc inv.h_crest (.construct kexprListEnum "Nil" [])
  have hdrop_fvs_len : ZMod.val (cnF : F) = ((fvs.drop rP).map (Core.posOf lps)).length := by
    rw [hcnf_val, List.length_map, List.length_drop, hfvs_len]; omega
  have hdrop_fvs_Γ : ∀ m (hm : m < ((fvs.drop rP).map (Core.posOf lps)).length),
      Expr.fvar (rP + m) (Γ_t (rP + m)) = ((fvs.drop rP).map (Core.posOf lps))[m] := by
    intro m hm
    have hm_cnF : m < cnF := by rw [← hdrop_fvs_len, hcnf_val] at hm; exact hm
    have h1 := congrArg (·[m]?) hbvd2_fvs
    rw [List.getElem?_map, List.getElem?_range hm_cnF, Option.map_some,
      List.getElem?_eq_getElem hm] at h1
    exact Option.some.inj h1
  obtain ⟨r_cres, _, cdoms2_pos, cres_pos, htup_cres, hinst_c2_pos, hcres_tm⟩ :=
    Decl.peel_collect_inst_tm hdrop_fvs_len hdrop_fvs_Γ inv.ev_cres (hcrest_tm.mono ext_crest_in)
  injection htup_cres with hl; injection hl with h1 _; subst h1
  rw [show rP + ((fvs.drop rP).map (Core.posOf lps)).length = depth by
    rw [← hdrop_fvs_len, hcnf_val]] at hcres_tm
  obtain ⟨cdoms2, cres, hinst_c2, hcdoms2_pos, hcres_pos⟩ := Decl.instPisAt_of_posOf hinst_c2_pos
  subst hcdoms2_pos hcres_pos
  let cdoms := cdoms1 ++ cdoms2
  have hinst_c : Expr.instPisAt (pinsF_lps ++ fvs.drop rP) (cty_inst.renameConsts g) =
      some (cdoms, cres) := by
    rw [Decl.instPisAt_append, hinst_c1, Option.map_eq_some_iff]
    exact ⟨(cdoms2, cres), hinst_c2, rfl⟩
  have hcdoms_drop : cdoms.drop cnP = cdoms2 := by
    have hlen1 : cdoms1.length = cnP := by
      rw [Decl.instPisAt_length hinst_c1]; simp [pinsF_lps, hpins_len]
    simp [cdoms, hlen1]
  obtain ⟨r_ch, r_ca, ch_pos, cargs_pos, htup_csp, hch_tm, hcargs_rep, hcres_app⟩ :=
    SubstAux.gall sc.κ .collect_spine [inv.cres] inv.h_cres
      (.tuple [inv.chead, inv.cargs]) inv.h_csp inv.cs_csp inv.ev_csp inv.cres rfl
      (bounded_sub (hsub_iota.trans inv.sub_csp) hbd) depth Γ_t 0 (Core.posOf lps cres) hcres_tm
  injection htup_csp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
  obtain ⟨a_ch, us_ch, rfl, -, -, -, -⟩ := hch_tm.const_of_load inv.ld_chead
  have hcargs_pos_eq : cargs_pos = cres.getAppArgs.map (Core.posOf lps) := by
    have h1 : (Core.posOf lps cres).getAppArgs = cargs_pos := by
      rw [hcres_app, Decl.getAppArgs_mkAppN]; rfl
    unfold Core.posOf at h1
    rw [Decl.getAppArgs_instantiateLevelParams] at h1
    exact h1.symm
  have hcargs_lt : cargs_pos.length < 2 ^ 39 :=
    IxVM.Refinement.RomBound.bounded_length_lt hbd (hsub_iota _ inv.call_clen) (by simp) hcargs_rep
  obtain ⟨hclen_f, -⟩ := Decl.tele_klength inv.ev_clen hcargs_rep
  have hcres_len : cres.getAppArgs.length = cnP + nI := by
    rw [SubstAux.add_ok inv.op_cnp_ni] at hclen_f
    injection hclen_f with hf
    have hv := congrArg ZMod.val hf
    rw [SubstAux.val_natCast (by omega),
      SubstAux.val_add (by rw [hcnp_val, hni_val]; omega), hcnp_val, hni_val,
      hcargs_pos_eq, List.length_map] at hv
    exact hv.symm
  have hcbody_inst_len : cbody_inst.getAppArgs.length = cnP + nI := by
    have hstrip_ren := stripPis_renameConsts_ir g (cnP + cnF) cty_inst hstrip_inst
    have hfn_ren : (cbody_inst.renameConsts g).getAppFn =
        .const (g (famKey t env srcAs (ixAddr a_ch0))) usc_inst := by
      rw [Decl.getAppFn_renameConsts, hfn_inst]; rfl
    have hlen_ren : (cbody_inst.renameConsts g).getAppArgs.length =
        cbody_inst.getAppArgs.length := by
      rw [Decl.getAppArgs_renameConsts, List.length_map]
    have hpfx_len : (pinsF_lps ++ fvs.drop rP).length + 0 = cnP + cnF := by
      simp [pinsF_lps, hpins_len, hfvs_len]; omega
    rw [← hpfx_len] at hstrip_ren
    obtain ⟨_, cres', _, cbody_r, hinst_r', hs0, _, hlen_r⟩ :=
      Decl.instPisAt_constHead _ _ cbody_inst.getAppArgs.length (pinsF_lps ++ fvs.drop rP) 0
        (cty_inst.renameConsts g) hstrip_ren hfn_ren hlen_ren
    rw [hinst_c] at hinst_r'; injection hinst_r' with hp; injection hp with _ hcr; subst hcr
    injection hs0 with hp; injection hp with _ hcb; subst hcb
    exact hlen_r.symm.trans hcres_len
  -- Index `defeq_list_ok`
  have ext_pref_csp := ext_pref_exp.trans (inv.ev_majeq.heap_extends.trans
    (inv.ev_ctyl.heap_extends.trans (ext_ctyl_csp0.trans (inv.ev_cty_ren.heap_extends.trans
      (inv.ev_crest.heap_extends.trans (ext_crest_in.trans
        (inv.ev_cres.heap_extends.trans inv.ev_csp.heap_extends)))))))
  have hlargs_clen := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    (ext_pref_csp.trans inv.ev_clen.heap_extends) hlargs_pref
  obtain ⟨-, hldrop_clen, -⟩ := Decl.tele_kdrop inv.ev_ldrop hlargs_clen
  have hldrop_rep := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    inv.ev_ldrop.heap_extends hldrop_clen
  rw [hrp_val] at hldrop_rep
  obtain ⟨-, hidxl_rep⟩ := Decl.tele_ktake (fun _ _ _ _ e x => x.mono e) inv.ev_idxl hldrop_rep
  rw [hni_val] at hidxl_rep
  have ext_csp_idxl := inv.ev_clen.heap_extends.trans
    (inv.ev_ldrop.heap_extends.trans inv.ev_idxl.heap_extends)
  have hcargs_idxl := RepLinkedList.mono tmE_heapMono₂ ext_csp_idxl hcargs_rep
  obtain ⟨-, hidxr_idxl, -⟩ := Decl.tele_kdrop inv.ev_idxr hcargs_idxl
  have hidxr_rep := RepLinkedList.mono tmE_heapMono₂ inv.ev_idxr.heap_extends hidxr_idxl
  rw [hcnp_val] at hidxr_rep
  have hidxl_idxr := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e)
    inv.ev_idxr.heap_extends hidxl_rep
  have hidxl_tm : RepList kexprListEnum (fun h X p => Tm sc.κ depth Γ_t h 0 X p) inv.h_idxr
      (((lhsS.getAppArgs.drop rP).take nI).map (Core.posOf lps)) inv.v_idxl := by
    rw [hlargs_pos_eq, ← List.map_drop, ← List.map_take] at hidxl_idxr
    exact repList_imp (fun _ _ hh => hh.toTm) hidxl_idxr
  have hidxr_tm : RepList kexprListEnum (fun h Y p => Tm sc.κ depth Γ_t h 0 Y p) inv.h_idxr
      ((cres.getAppArgs.drop cnP).map (Core.posOf lps)) inv.v_idxr := by
    rwa [hcargs_pos_eq, ← List.map_drop] at hidxr_rep
  have ext_csp_idxr := ext_csp_idxl.trans inv.ev_idxr.heap_extends
  have ext_open_idxl := inv.ev_tsp.heap_extends.trans (inv.ev_req.heap_extends.trans
    (inv.ev_raddr.heap_extends.trans (ext_raddr_a2.trans (inv.ev_lsp.heap_extends.trans
      (ext_lsp_lheq.trans (ext_lheq_pref.trans
        (ext_pref_csp.trans ext_csp_idxr)))))))
  have ext_h_idxl := ext_open.trans ext_open_idxl
  have hde_idx : DefEqListJ posRulesJ env depth
      ((lhsS.getAppArgs.drop rP).take nI) (cres.getAppArgs.drop cnP) :=
    Decl.rawDefEqList_to_posRulesJ hlps_perm
      (Decl.defeq_list_ok_scoped_spec (c := sc) (hrc.mono ext_h_idxl)
        (hctx_rep.mono ext_open_idxl) hsc_t hef hlf (hgoodOf inv.sub_deidx)
        inv.ev_deidx hidxl_tm hidxr_tm)
  -- 8. Statement domain telescopes (`ty_m`, `defeq_tele` #1 and #2)
  have ext_idxl_deidx := inv.ev_deidx.heap_extends
  have ext_h_deidx := ext_h_idxl.trans ext_idxl_deidx
  have hty_cells_deidx : ∀ a, AddrIn inv.h_deidx ty_r a →
      (∃ ci, env.find? (Core.keyOf t (ixAddr a)) = some ci) ∨ ixAddr a ∈ srcAs.map ixAddr :=
    fun a ha => hty_cells a (Binding.TmExact.addrIn_back (hty_rep 0 zeroGhost) ext_h_deidx a ha)
  have hty_m_ex : Decl.TmExact sc.κ 0 zeroGhost inv.h_ty_m 0
      (Core.posOf lps (tyA.renameConsts g)) inv.ty_m := by
    have hr := rename_stored_of_src (E₀ := E) (lim := lim) (Γ₂ := zeroGhost) htwf inv.ev_ty_m
      hlenSD (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_deidx hsrc)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_deidx hdst)
      ((hty_rep 0 zeroGhost).mono ext_h_deidx) hmodels hty_cells_deidx
    have hnp_ty_pos : Decl.NoProjIn srcKeys (Core.posOf lps tyA) = true := by
      unfold Core.posOf; rw [Decl.noProjIn_instantiateLevelParams]; exact hnp_ty
    rw [Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp_ty_pos] at hr
    have hcomm : (Core.posOf lps tyA).renameConsts g = Core.posOf lps (tyA.renameConsts g) := by
      unfold Core.posOf
      exact (Decl.instantiateLevelParams_renameConsts lps (Core.posLevels lps) g tyA).symm
    rwa [hcomm] at hr
  have ext_ty_m_nil := Heap.Extends.snoc inv.h_ty_m (.construct kexprListEnum "Nil" [])
  have ext_tci_dt1_in := ext_open_in.trans (inv.ev_open.heap_extends.trans
    (ext_open_idxl.trans (ext_idxl_deidx.trans (inv.ev_ty_m.heap_extends.trans ext_ty_m_nil))))
  have ext_h_dt1_in := ext_tci.trans ext_tci_dt1_in
  obtain ⟨fvs1_pos, remA1_pos, rdoms_pos, lrest_pos, hop_dt1_pos, hinst_r_pos, hraw_pre⟩ :=
    Decl.defeq_tele_scoped_spec (c := sc) rP (d := 0) (depth := depth)
      hrp_val (by omega) (hrc.mono ext_h_dt1_in)
      (Decl.typesRep_alloc_nil sc.κ zeroGhost inv.h_ty_m)
      (Decl.ghostScoped_zero zeroGhost) hef hlf (hgoodOf inv.sub_dt1) inv.ev_dt1
      ((htty_rep 0 zeroGhost).mono ext_tci_dt1_in)
      (hty_m_ex.toTm.mono ext_ty_m_nil)
  obtain ⟨fvs1, remA1, hop_dt1, hfvs1_pos, hremA1_pos⟩ := Decl.openPisAtFvars_of_posOf hop_dt1_pos
  subst hfvs1_pos hremA1_pos
  have hfvs_split := (Decl.openPisAtFvars_split rP cnF stmt 0).symm
  rw [show rP + cnF = depth from rfl, hopen_t, hop_dt1, Nat.zero_add] at hfvs_split
  dsimp only at hfvs_split
  rw [Option.map_eq_some_iff] at hfvs_split
  obtain ⟨⟨fvs2, _⟩, hop_dt2_expected, hfvs_pair⟩ := hfvs_split
  dsimp only at hfvs_pair
  obtain ⟨hfvs_app, -⟩ := Prod.mk.inj hfvs_pair
  have hfvs1_len : fvs1.length = rP := (Decl.openPisAtFvars_spec rP stmt 0 hop_dt1).1
  have hfvs_take_eq : fvs.take rP = fvs1 := by rw [← hfvs_app, List.take_left' hfvs1_len]
  have hfvs_drop_eq : fvs.drop rP = fvs2 := by rw [← hfvs_app, List.drop_left' hfvs1_len]
  rw [← hfvs_take_eq] at hinst_r_pos hraw_pre
  obtain ⟨rdoms, lrest, hinst_r, hrdoms_pos, -⟩ := Decl.instPisAt_of_posOf hinst_r_pos
  subst hrdoms_pos
  have hde_pre : DefEqListJ posRulesJ env depth ((fvs.take rP).map Expr.fvarTypeD) rdoms := by
    have hmap_ty : ((fvs.take rP).map (Core.posOf lps)).map Expr.fvarTypeD =
        ((fvs.take rP).map Expr.fvarTypeD).map (Core.posOf lps) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro x hx
      have hx_mem : x ∈ fvs := List.mem_of_mem_take hx
      obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx_mem
      conv_lhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
      conv_rhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
      rfl
    rw [hmap_ty] at hraw_pre
    exact Decl.rawDefEqList_to_posRulesJ hlps_perm hraw_pre
  -- `defeq_tele` #2
  have ext_tci_dt1 := ext_tci_dt1_in.trans inv.ev_dt1.heap_extends
  have htake_fvs_len : ZMod.val (rP : F) = ((fvs.take rP).map (Core.posOf lps)).length := by
    rw [hrp_val, List.length_map, List.length_take, hfvs_len]; omega
  have htake_fvs_Γ : ∀ m (hm : m < ((fvs.take rP).map (Core.posOf lps)).length),
      Expr.fvar (0 + m) (Γ_t (0 + m)) = ((fvs.take rP).map (Core.posOf lps))[m] := by
    intro m hm
    have hm_rP : m < rP := by rw [← htake_fvs_len, hrp_val] at hm; exact hm
    have h1 := congrArg (·[m]?) hbvd1_fvs
    rw [List.getElem?_map, List.getElem?_range hm_rP, Option.map_some,
      List.getElem?_eq_getElem hm] at h1
    exact Option.some.inj h1
  obtain ⟨_, remA1_inst, hinst_tty_rp, htty_rp_dt1, _⟩ :=
    Decl.peel_n_foralls_inst_exact htake_fvs_len htake_fvs_Γ inv.ev_tty_rp
      ((htty_rep 0 Γ_t).mono ext_tci_dt1)
  rw [← htake_fvs_len, hrp_val, Nat.zero_add] at htty_rp_dt1
  have hremA1_eq : remA1_inst = Core.posOf lps remA1 := by
    rw [hfvs_take_eq] at hinst_tty_rp
    have hop_spec := (Decl.openPisAtFvars_spec rP (Core.posOf lps stmt) 0 hop_dt1_pos).2.1
    rw [hop_spec] at hinst_tty_rp
    injection hinst_tty_rp with hp; exact (Prod.mk.inj hp).2.symm
  subst hremA1_eq
  have ext_open_dt1 := ext_open_idxl.trans (ext_idxl_deidx.trans
    (inv.ev_ty_m.heap_extends.trans (ext_ty_m_nil.trans inv.ev_dt1.heap_extends)))
  obtain ⟨-, hctx_rp_ttyrp, -⟩ :=
    Decl.typesRep_drop cnF hcnf_val inv.ev_ctx_rp
      (hctx_rep.mono (ext_open_dt1.trans inv.ev_tty_rp.heap_extends))
  have hctx_rp_rep := hctx_rp_ttyrp.mono inv.ev_ctx_rp.heap_extends
  rw [show depth - ZMod.val (cnF : F) = rP by rw [hcnf_val]; omega] at hctx_rp_rep
  have hsc_t_rp : GhostScoped Γ_t rP := fun i hi => hsc_t i (by omega)
  have ext_crest_dt1 := ext_crest_in.trans (inv.ev_cres.heap_extends.trans
    (inv.ev_csp.heap_extends.trans (ext_csp_idxr.trans
      (ext_idxl_deidx.trans (inv.ev_ty_m.heap_extends.trans
        (ext_ty_m_nil.trans inv.ev_dt1.heap_extends))))))
  have ext_h_dt1 := ext_tci.trans ext_tci_dt1
  have ext_dt1_ctxrp := inv.ev_tty_rp.heap_extends.trans inv.ev_ctx_rp.heap_extends
  have htty_rp_ex := htty_rp_dt1.mono ext_dt1_ctxrp
  obtain ⟨fvs2_pos, _, doms2_pos, _, hop_dt2_pos, hinst_dt2_pos, hraw_dom⟩ :=
    Decl.defeq_tele_scoped_spec (c := sc) cnF (d := rP) (depth := depth)
      hcnf_val (by omega) (hrc.mono (ext_h_dt1.trans ext_dt1_ctxrp))
      hctx_rp_rep hsc_t_rp hef hlf (hgoodOf inv.sub_dt2) inv.ev_dt2
      htty_rp_ex (hcrest_tm.mono (ext_crest_dt1.trans ext_dt1_ctxrp))
  obtain ⟨fvs2', _, hop_dt2', hfvs2_pos, _⟩ := Decl.openPisAtFvars_of_posOf hop_dt2_pos
  subst hfvs2_pos
  rw [hop_dt2_expected] at hop_dt2'; injection hop_dt2' with hp
  obtain ⟨hfvs2_eq, -⟩ := Prod.mk.inj hp; subst hfvs2_eq
  rw [← hfvs_drop_eq] at hinst_dt2_pos hraw_dom
  rw [hinst_c2_pos] at hinst_dt2_pos
  injection hinst_dt2_pos with hp; obtain ⟨hdoms2_eq, -⟩ := Prod.mk.inj hp; subst hdoms2_eq
  have hde_dom : DefEqListJ posRulesJ env depth
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP) := by
    rw [hcdoms_drop]
    have hmap_ty : ((fvs.drop rP).map (Core.posOf lps)).map Expr.fvarTypeD =
        ((fvs.drop rP).map Expr.fvarTypeD).map (Core.posOf lps) := by
      rw [List.map_map, List.map_map]
      apply List.map_congr_left
      intro x hx
      have hx_mem : x ∈ fvs := List.mem_of_mem_drop hx
      obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx_mem
      conv_lhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
      conv_rhs => rw [Function.comp_apply, hfvs_shape idx hidx_lt]
      rfl
    rw [hmap_ty] at hraw_dom
    exact Decl.rawDefEqList_to_posRulesJ hlps_perm hraw_dom
  -- 9. Renamed parameter typing & `defeq_lam_tele` (#1 and #2 at `sc`)
  have ext_h_dt2 := ext_h_dt1.trans ext_dt1_dt2
  have ext_dt2_nil := Heap.Extends.snoc inv.h_dt2 (.construct kexprListEnum "Nil" [])
  have ext_ty_m_dt2 := ext_ty_m_nil.trans (inv.ev_dt1.heap_extends.trans ext_dt1_dt2)
  obtain ⟨r_pbody, r_ctxp, Γ_p, fvsPm_pos, crest2m_pos, htup_ctxp, hopen_pm_pos, -, hΓp_hi,
      -, hctxp_rep, hsc_p⟩ :=
    Decl.peel_collect_open_exact rP hrp_val inv.ev_ctxp
      (hty_m_ex.mono (ext_ty_m_dt2.trans ext_dt2_nil))
      (Decl.typesRep_alloc_nil sc.κ zeroGhost inv.h_dt2)
      (Decl.ghostScoped_zero zeroGhost)
  injection htup_ctxp with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
  simp only [Nat.zero_add] at hΓp_hi hctxp_rep hsc_p
  obtain ⟨fvsP_m, crest2_m, hopen_pm, hfvsPm_pos, hcrest2m_pos⟩ :=
    Decl.openPisAtFvars_of_posOf hopen_pm_pos
  subst hfvsPm_pos hcrest2m_pos
  obtain ⟨fvsP, crest2, hopen_p, hfvsP_ren, hcrest2_ren⟩ := openPisAtFvars_pullback hopen_pm
  obtain ⟨hfvsP_len, -, hfvsP_shape⟩ := Decl.openPisAtFvars_spec rP tyA 0 hopen_p
  obtain ⟨hfvsPm_len, -, hfvsPm_shape⟩ :=
    Decl.openPisAtFvars_spec rP (tyA.renameConsts g) 0 hopen_pm
  have hfvsP_take : fvsP.take rP = fvsP := List.take_of_length_le (by omega)
  -- `ev_cty_ren2` on `cty_l`
  have ext_h_ctxp := ext_h_dt2.trans (ext_dt2_nil.trans inv.ev_ctxp.heap_extends)
  have ext_ctyl_ctxp := ext_ctyl_csp0.trans (inv.ev_cty_ren.heap_extends.trans
    (inv.ev_crest.heap_extends.trans (ext_crest_dt1.trans
      (ext_dt1_dt2.trans (ext_dt2_nil.trans inv.ev_ctxp.heap_extends)))))
  have hcty_ren2_tm0 : Tm sc.κ 0 zeroGhost inv.h_cty_ren2 0
      (Core.posOf lps (cty_inst.renameConsts g)) inv.v_cty_ren2 := by
    have hr := rename_tm_stored (E₀ := E) (lim := lim) (Γ₁ := zeroGhost) (Γ₂ := zeroGhost)
      htwf hlenSD hmodels inv.ev_cty_ren2 (hctyl_tm0.mono ext_ctyl_ctxp)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_ctxp hsrc)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_h_ctxp hdst)
    have hnp_inst : Decl.NoProjIn srcKeys (Core.posOf lps cty_inst) = true := by
      unfold Core.posOf cty_inst
      rw [Decl.noProjIn_instantiateLevelParams, Decl.noProjIn_instantiateLevelParams]
      exact hnp_cty
    rw [Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp_inst] at hr
    have hcomm : (Core.posOf lps cty_inst).renameConsts g =
        Core.posOf lps (cty_inst.renameConsts g) := by
      unfold Core.posOf
      exact (Decl.instantiateLevelParams_renameConsts lps (Core.posLevels lps) g cty_inst).symm
    rwa [hcomm] at hr
  -- Apply `defeq_lam_tele` #1 FIRST so we have `Γ_l` ready for `inst_params_typed_scoped_spec`!
  have ext_h_ctyren2 := ext_h_ctxp.trans inv.ev_cty_ren2.heap_extends
  have ext_h_crestp := ext_h_ctyren2.trans inv.ev_crestp.heap_extends
  have ext_crestp_nil := Heap.Extends.snoc inv.h_crestp (.construct kexprListEnum "Nil" [])
  have ext_h_lt1_in := ext_h_crestp.trans ext_crestp_nil
  have ext_rhsm_lt1_in := ext_rhs_in.trans (inv.ev_rhs_inf.heap_extends.trans
    (inv.ev_aset.heap_extends.trans (inv.ev_tci.heap_extends.trans
      (ext_open_in.trans (inv.ev_open.heap_extends.trans
        (ext_open_dt1.trans (ext_dt1_dt2.trans (ext_dt2_nil.trans
          (inv.ev_ctxp.heap_extends.trans (inv.ev_cty_ren2.heap_extends.trans
            (inv.ev_crestp.heap_extends.trans ext_crestp_nil)))))))))))
  have ext_tym_lt1_in := ext_ty_m_dt2.trans (ext_dt2_nil.trans
    (inv.ev_ctxp.heap_extends.trans (inv.ev_cty_ren2.heap_extends.trans
      (inv.ev_crestp.heap_extends.trans ext_crestp_nil))))
  obtain ⟨r_rhs_rp, r_lctx, Γ_l, pfvs1_pos, remP1_pos, ldoms1_pos, remL1_pos,
      htup_lt1, hop_lt1_pos, hinst_lt1_pos, -, hΓl_hi, hremL1_tm, hlctx_rep, hsc_l, hraw_lt1⟩ :=
    Decl.defeq_lam_tele_scoped_spec (c := sc) rP (d := 0) (depth := depth)
      hrp_val (by omega) (hrc.mono ext_h_lt1_in)
      (Decl.typesRep_alloc_nil sc.κ zeroGhost inv.h_crestp)
      (Decl.ghostScoped_zero zeroGhost) hef hlf (hgoodOf inv.sub_lt1) inv.ev_lt1
      (hrhs_m_raw.toTm.mono ext_rhsm_lt1_in)
      (hty_m_ex.toTm.mono ext_tym_lt1_in)
  injection htup_lt1 with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
  simp only [Nat.zero_add] at hΓl_hi hremL1_tm hlctx_rep hsc_l
  rw [hopen_pm_pos] at hop_lt1_pos
  injection hop_lt1_pos with hpair1
  obtain ⟨hpfvs1_eq, hremP1_eq⟩ := Prod.mk.inj hpair1
  subst hpfvs1_eq hremP1_eq
  obtain ⟨ldoms1_m, remL1_m, hinst_lt1_m, hldoms1_pos, hremL1_pos⟩ :=
    instLamsAt_of_posOf hinst_lt1_pos
  subst hldoms1_pos hremL1_pos
  -- Both `Γ_p` and `Γ_l` open `fvsP_m = fvsP.map (·.renameConsts g)`
  have hΓp_list : ((List.range rP).map fun m => Expr.fvar m (Γ_p m)) =
      fvsP_m.map (Core.posOf lps) := by
    apply List.ext_getElem (by simp [hfvsPm_len])
    intro m hm1 hm2
    simp only [List.length_range, List.length_map] at hm1
    have hm_pos : m < (fvsP_m.map (Core.posOf lps)).length := by simp [hfvsPm_len, hm1]
    have hΓm := hΓp_hi m hm_pos
    have hm_fvsP : m < fvsP_m.length := by rw [hfvsPm_len]; exact hm1
    have hsh := hfvsPm_shape m hm_fvsP
    rw [Nat.zero_add] at hsh
    obtain ⟨T, hT⟩ : ∃ T, fvsP_m[m] = .fvar m T := ⟨_, hsh⟩
    rw [List.getElem_map, List.getElem_range, hΓm, List.getElem_map, hT]
    simp [Core.posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
  have hΓl_list : ((List.range rP).map fun m => Expr.fvar m (Γ_l m)) =
      fvsP_m.map (Core.posOf lps) := by
    apply List.ext_getElem (by simp [hfvsPm_len])
    intro m hm1 hm2
    simp only [List.length_range, List.length_map] at hm1
    have hm_pos : m < (fvsP_m.map (Core.posOf lps)).length := by simp [hfvsPm_len, hm1]
    have hΓm := hΓl_hi m hm_pos
    have hm_fvsP : m < fvsP_m.length := by rw [hfvsPm_len]; exact hm1
    have hsh := hfvsPm_shape m hm_fvsP
    rw [Nat.zero_add] at hsh
    obtain ⟨T, hT⟩ : ∃ T, fvsP_m[m] = .fvar m T := ⟨_, hsh⟩
    rw [List.getElem_map, List.getElem_range, hΓm, List.getElem_map, hT]
    simp [Core.posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
  let pinsP := pins.map fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p
  have hpinsP_ren : pinsP.map (·.renameConsts g) =
      pins.map fun p => Expr.instSpine fvsP_m (rP - 1) (p.renameConsts g) := by
    dsimp only [pinsP]
    rw [hfvsP_take, List.map_map]
    apply List.map_congr_left
    intro p _; simp only [Function.comp_apply]
    rw [← hfvsP_ren]
    exact (Decl.instSpine_renameConsts g fvsP (rP - 1) p).symm
  have ext_pren_ctyren2 := ext_pren_ctyren.trans (inv.ev_crest.heap_extends.trans
    (ext_crest_dt1.trans (ext_dt1_dt2.trans (ext_dt2_nil.trans
      (inv.ev_ctxp.heap_extends.trans inv.ev_cty_ren2.heap_extends)))))
  have hpins_open_Γ : ∀ (Γ : Nat → KExpr),
      ((List.range rP).map fun m => Expr.fvar m (Γ m)) = fvsP_m.map (Core.posOf lps) →
      RepList kexprListEnum (fun h P p => Tm sc.κ rP Γ h 0 P p) inv.h_cty_ren2
        ((pinsP.map (·.renameConsts g)).map (Core.posOf lps)) inv.pins_ren := by
    intro Γ hΓ_eq
    have h1 := RepLinkedList.mono (fun _ _ _ _ e x => x.mono e) ext_pren_ctyren2 hpins_ren_rep
    have hlist_eq :
        ((pins.map (·.renameConsts g)).map (Core.posOf lps)).map
          (fun P => Expr.instSpine ((List.range rP).map fun m => .fvar m (Γ m)) (rP - 1) P) =
          (pinsP.map (·.renameConsts g)).map (Core.posOf lps) := by
      rw [hΓ_eq, hpinsP_ren, List.map_map, List.map_map, List.map_map]
      apply List.map_congr_left
      intro p _; simp only [Function.comp_apply]
      unfold Core.posOf
      exact (Decl.instantiateLevelParams_instSpine lps (Core.posLevels lps)
        fvsP_m (rP - 1) (p.renameConsts g)).symm
    rw [← hlist_eq]
    exact repList_map_rel (fun _ _ hh => (hh.open_prefix_eq (Γ := Γ)).toTm) h1
  -- Apply `inst_params_typed_scoped_spec` with `Γ₁ := Γ_p` and `Γ₂ := Γ_l`
  obtain ⟨cdomsPm_pos, crestPm_pos, cdomsPm2_pos, crestPm2_pos,
      hinst_pm_pos, hinst_pm2_pos, -, hcrestPm_tm, hraw_pins_typed⟩ :=
    Decl.inst_params_typed_scoped_spec (c := sc) (d₁ := rP) (d₂ := rP) (depth := depth)
      (by omega) (hrc.mono ext_h_ctyren2)
      (hctxp_rep.mono inv.ev_cty_ren2.heap_extends) hsc_p hef hlf
      (hgoodOf inv.sub_crestp) inv.ev_crestp
      (hcty_ren2_tm0.of_depth_zero rP) (hcty_ren2_tm0.of_depth_zero rP)
      (hpins_open_Γ Γ_p hΓp_list) (hpins_open_Γ Γ_l hΓl_list)
  rw [hinst_pm_pos] at hinst_pm2_pos
  injection hinst_pm2_pos with hpm_eq
  obtain ⟨-, hcr_eq⟩ := Prod.mk.inj hpm_eq
  subst hcr_eq
  obtain ⟨cdomsP_m, crestP_m, hinst_pm, hcdomsPm_pos, hcrestPm_pos⟩ :=
    Decl.instPisAt_of_posOf hinst_pm_pos
  subst hcdomsPm_pos hcrestPm_pos
  obtain ⟨cdomsP, crestP, hinst_p, hcdomsP_ren, hcrestP_ren⟩ :=
    Decl.FamilyAlias.instPisAt_pullback rfl rfl hinst_pm
  have hpins_typed : TypedListJ posRulesJ env depth
      (pinsP.map (·.renameConsts g)) (cdomsP.map (·.renameConsts g)) := by
    rw [hcdomsP_ren]
    exact Decl.rawTypedList_to_posRulesJ hlps_perm hraw_pins_typed
  -- Construct `xFvsP, ldoms` (`openPisAtFvars cnF crestP rP`) and `ldoms.getAppArgs.length = cnP + nI`
  have hpP_len : pinsP.length + cnF = cnP + cnF := by simp [pinsP, hpins_len]
  rw [← hpP_len] at hstrip_inst
  obtain ⟨_, crestP', bs_cp, cbody_cp, hinst_p', hstrip_cp, hfn_cp, hlen_cp⟩ :=
    Decl.instPisAt_constHead _ _ (cnP + nI) pinsP cnF cty_inst
      hstrip_inst hfn_inst hcbody_inst_len
  rw [hinst_p] at hinst_p'; injection hinst_p' with hp; injection hp with _ hcp; subst hcp
  obtain ⟨xFvsP, ldoms, hopen_cf, _, hldoms_len⟩ :=
    Decl.openPisAtFvars_constHead _ _ (cnP + nI) cnF crestP rP hstrip_cp hfn_cp hlen_cp
  -- `defeq_lam_tele` #2 (`ev_lt2`)
  have ext_crestp_lt1 := ext_crestp_nil.trans inv.ev_lt1.heap_extends
  have ext_h_lt1 := ext_h_lt1_in.trans inv.ev_lt1.heap_extends
  obtain ⟨_, _, _, pfvs2_pos, remP2_pos, ldoms2_pos, remL2_pos,
      _, hop_lt2_pos, hinst_lt2_pos, _, _, _, _, _, hraw_lt2⟩ :=
    Decl.defeq_lam_tele_scoped_spec (c := sc) cnF (d := rP) (depth := depth)
      hcnf_val (by omega) (hrc.mono ext_h_lt1) hlctx_rep hsc_l hef hlf
      (hgoodOf inv.sub_lt2) inv.ev_lt2 hremL1_tm (hcrestPm_tm.mono ext_crestp_lt1)
  obtain ⟨xFvsP_m, ldoms_m, hop_lt2_m, hxFvsPm_pos, _⟩ := Decl.openPisAtFvars_of_posOf hop_lt2_pos
  subst hxFvsPm_pos
  have hopen_cfm : openPisAtFvars cnF crestP_m rP =
      some (xFvsP.map (·.renameConsts g), ldoms.renameConsts g) := by
    rw [← hcrestP_ren, Decl.openPisAtFvars_renameConsts, hopen_cf]; rfl
  rw [hopen_cfm] at hop_lt2_m
  injection hop_lt2_m with hpair2
  obtain ⟨hxFvsPm_eq, -⟩ := Prod.mk.inj hpair2
  subst hxFvsPm_eq
  obtain ⟨ldoms2_m, remL2_m, hinst_lt2_m, hldoms2_pos, -⟩ := instLamsAt_of_posOf hinst_lt2_pos
  subst hldoms2_pos
  -- Combine `ev_lt1` + `ev_lt2` into `instLamsAt (fvsP ++ xFvsP) rhsA` and `lam` `DefEqListJ`
  have hinst_lam_m : Expr.instLamsAt ((fvsP ++ xFvsP).map (·.renameConsts g)) (rhsA.renameConsts g) =
      some (ldoms1_m ++ ldoms2_m, remL2_m) := by
    rw [List.map_append, instLamsAt_append, hfvsP_ren, hinst_lt1_m]
    simp [hinst_lt2_m]
  obtain ⟨ldomsL, lrest2, hinst_lam, hldomsL_ren, -⟩ := instLamsAt_pullback rfl hinst_lam_m
  have hde_lam : DefEqListJ posRulesJ env depth
      (((fvsP ++ xFvsP).map Expr.fvarTypeD).map (·.renameConsts g))
      (ldomsL.map (·.renameConsts g)) := by
    have hxFvsP_shape := (Decl.openPisAtFvars_spec cnF crestP rP hopen_cf).2.2
    have hmap_ty1 : (fvsP_m.map (Core.posOf lps)).map Expr.fvarTypeD =
        ((fvsP.map Expr.fvarTypeD).map (·.renameConsts g)).map (Core.posOf lps) := by
      rw [← hfvsP_ren, List.map_map, List.map_map, List.map_map, List.map_map]
      apply List.map_congr_left
      intro x hx
      obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx
      have hsh := hfvsP_shape idx hidx_lt
      conv_lhs => rw [Function.comp_apply, Function.comp_apply, hsh]
      rfl
    have hmap_ty2 : ((xFvsP.map (·.renameConsts g)).map (Core.posOf lps)).map Expr.fvarTypeD =
        ((xFvsP.map Expr.fvarTypeD).map (·.renameConsts g)).map (Core.posOf lps) := by
      rw [List.map_map, List.map_map, List.map_map, List.map_map]
      apply List.map_congr_left
      intro x hx
      obtain ⟨idx, hidx_lt, rfl⟩ := List.getElem_of_mem hx
      have hsh := hxFvsP_shape idx hidx_lt
      conv_lhs => rw [Function.comp_apply, Function.comp_apply, hsh]
      rfl
    rw [hmap_ty1] at hraw_lt1
    rw [hmap_ty2] at hraw_lt2
    have hraw_both := Decl.rawDefEqList_append hraw_lt1 hraw_lt2
    rw [← List.map_append, ← List.map_append, ← List.map_append, ← List.map_append,
      ← hldomsL_ren] at hraw_both
    exact Decl.rawDefEqList_to_posRulesJ hlps_perm (Decl.FamilyAlias.RawDefEqList.symm hraw_both)
  -- 10. Right-hand side application (`rhsS ≡ mkAppN (rhsA.renameConsts g) fvs`)
  have ev_bvd3' := inv.ev_bvd3
  rw [hd_eq] at ev_bvd3'
  have hbvd3_rep := Decl.bvars_desc_exact_wide (κ := sc.κ) (d := depth) (Γ := Γ_t)
    (by rw [hd_val]) (by rw [hd_val]) (by omega) ev_bvd3'
  rw [hd_val, Nat.sub_self] at hbvd3_rep
  have hbvd3_fvs :
      ((List.range depth).map fun m => Expr.fvar (0 + m) (Γ_t (0 + m))) =
        fvs.map (Core.posOf lps) := by
    apply List.ext_getElem (by simp [hfvs_pos_len])
    intro m hm1 hm2
    simp only [List.length_map, List.length_range] at hm1
    have hΓm := hΓt_hi m hm2
    have hm_fvs : m < fvs.length := by rw [hfvs_len]; exact hm1
    have hsh := hfvs_shape m hm_fvs
    rw [Nat.zero_add] at hsh
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add, hΓm]
    rw [hsh]
    simp [Core.posOf, Expr.instantiateLevelParams, Expr.fvarTypeD]
  rw [hbvd3_fvs] at hbvd3_rep
  have ext_rhsm_bvd3 := ext_rhsm_lt1_in.trans (inv.ev_lt1.heap_extends.trans
    (inv.ev_lt2.heap_extends.trans inv.ev_bvd3.heap_extends))
  have hrhs_app_ex := Decl.apply_spine_exact inv.ev_rhsapp
    ((hrhs_m_raw.of_depth_zero depth).mono ext_rhsm_bvd3) hbvd3_rep
  have hrhs_app_pos_eq :
      Expr.mkAppN (Core.posOf lps (rhsA.renameConsts g)) (fvs.map (Core.posOf lps)) =
        Core.posOf lps (Expr.mkAppN (rhsA.renameConsts g) fvs) := by
    unfold Core.posOf
    exact (Decl.mkAppN_instantiateLevelParams lps (Core.posLevels lps) fvs
      (rhsA.renameConsts g)).symm
  rw [hrhs_app_pos_eq] at hrhs_app_ex
  have ext_lt1_rhsapp := inv.ev_lt2.heap_extends.trans
    (inv.ev_bvd3.heap_extends.trans inv.ev_rhsapp.heap_extends)
  have ext_a2_rhsapp := ext_a2_majeq.trans (ext_majeq_deidx.trans (ext_deidx_dt1.trans
    (ext_dt1_dt2.trans (ext_dt2_lt1.trans ext_lt1_rhsapp))))
  have ext_open_rhsapp := inv.ev_tsp.heap_extends.trans (inv.ev_req.heap_extends.trans
    (inv.ev_raddr.heap_extends.trans (ext_raddr_a2.trans ext_a2_rhsapp)))
  have ext_h_rhsapp := ext_open.trans ext_open_rhsapp
  have hde_rhs : posRulesJ.defeq env depth rhsS (Expr.mkAppN (rhsA.renameConsts g) fvs) :=
    Decl.posRulesJ_defeq_of_pos hlps_perm
      (Decl.scoped_core_defeq (c := sc) (hrc.mono ext_h_rhsapp)
        (hctx_rep.mono ext_open_rhsapp) hsc_t hef hlf (hgoodOf inv.sub_derhs) inv.ev_derhs
        (hrhsS_ex.toTm.mono ext_a2_rhsapp) hrhs_app_ex.toTm)
  -- Assemble `RuleFacts` and `StatementFacts`
  refine ⟨cvj, cnP, cnF, lvls, pins, hruleCtor, hnfields, hrhs_lbb, hrhs_nofvar, hrhs_ann,
    hrhsA_lvls, hrhsA_lams, hrhs_typed, hmaj, hlvls_def, hpins_ok, hctor_tele,
    cvt, vt, tty₀, hfindT, hpermT, htty0_def, hlvEqT_dt, ?_⟩
  refine ⟨fvs, tbody, hopen_t, hisEq, htargs_len, hlhs_fn, hlargs_len, hlargs_pre, hmajor_eq,
    cdoms, cres, rdoms, lrest, fvsP, crest2, cdomsP, crestP, xFvsP, ldoms,
    hinst_c, hcres_len, hinst_r, hopen_p, hinst_p, hopen_cf, hldoms_len,
    (fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact hleaves fvsP crest2 hopen_p q hq),
    ldomsL, lrest2, hinst_lam, hpins_typed, ?_⟩
  exact ⟨hde_idx, hde_dom, hde_pre, hde_lam, hde_rhs,
    ⟨Decl.invPosOf lps tl_pos, Decl.posRulesJ_infer_of_pos hlps_perm htl_inf,
      Decl.posRulesJ_defeq_of_pos hlps_perm (by rw [Decl.posOf_invPosOf hlps_perm]; exact htl_de)⟩,
    ⟨Decl.invPosOf lps tr_pos, Decl.posRulesJ_infer_of_pos hlps_perm htr_inf,
      Decl.posRulesJ_defeq_of_pos hlps_perm (by rw [Decl.posOf_invPosOf hlps_perm]; exact htr_de)⟩⟩

end IxVM.Refinement.Typing.FamilyAlias
