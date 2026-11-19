import IxVMRefinement.Binding.FamilyReconCons
import IxVMRefinement.Decl.LateWrapRel
import IxVMRefinement.Decl.PrefixInv
import IxVMRefinement.TwinFamily.Target

/-! # `WrapRel`, full consumption, and rule-body renaming across twin recursors

Algebra bridging the family reconstruction (`Binding.FamilyRecon`) to IxC's wrapper relation
(`Ix.Kernel.Semantics.WrapRel`) and the twin recursor route (`TwinFamily.Facts`):

* **Deterministic full consumption**: `Consumes.unique` and `FullCons.toWrapRel_of_both` show
  that two full consumptions of one reconstructed term are related by `WrapRel find?` at any
  lookup `find?`, with no wrapper-arity bridge needed.
* **Observed wrapper consumption**: `WrapperObserved` records the `Ingress::get_ci` and
  `KernelCheck::lam_first_arity` observations of `KernelCheck::consume_wrapper` in a call trace;
  `wrapperArity_of_observed` converts it to `Ix.Kernel.Semantics.wrapperArity env.find?` under
  `Decl.PrefixInv`, `WrapConsObs.toWrapRel` lifts a wrapper consumption whose consumed wrappers
  were observed (and resolve in `env`) to `WrapRel env.find?`, and `WrapConsObs.toSymWrapT` lifts
  two observed wrapper consumptions of one reconstructed term to `SymWrapT env.find?`.
* **Transport of `WrapRel` and `WrapDom`**: congruence under `ExprLvEq` on either side,
  commutation with `Expr.instantiateLevelParams` (moving between positional and recursor level
  parameters via `posOf` / `posOf_perm_inv`), commutation with `Expr.liftLooseBVars`, peeling of
  `∀` telescopes (`peelForalls`), and `WrapDom.toWrapRel_of_forallE`.
* **Rules from `RuleFollows`**: `wrapRel_rule_of_ruleFollows` builds
  `WrapRel find? (rC.rhs.renameConsts f) rW'.rhs` from `WrapRel find? tyC tyW`, `RuleFollows` on
  both sides, absence of renamed keys in `tyC`, and `cbC.renameConsts f = cbW`.
* **Reconstructed rule bodies under peer renaming**: `ruleBodiesAt_renameConsts_of_recTypeAt`
  derives `cbC.renameConsts f = cbW` from absence of moved keys in `recTypeAt`, and
  `ruleBodiesAt_renameConsts_of_closed` derives it from `ReconView.ClosedOn S V` and `REntryAt`.
* **Major-premise syntactic equality**: `majorDom_eq_of_recordFlat` extracts exact equality of
  `getAppFn` and `getAppArgs` on the major-premise domains of two records over the same flattened
  family, for both plain and auxiliary (`nested`) recursors. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core (KExpr KLevel KKey ExprLvEq LvEq LvEqList)
open IxVM.Refinement.Binding (KeyIn)
open IxVM.Refinement.Binding.FamilyFlat (FlatEntry RecordFlat peelForalls binderDomAfter)
open IxVM.Refinement.Binding.FamilyRecon (ReconView IndData CtorData wrapAt appHead consumeOf
  consumeAt Consumes FullCons LamsAlong RuleFollows recTypeAt ruleBodiesAt ruleBodies ruleBody
  applyIhs minorAt minorDoms allMinors ihDoms wrapForalls wrapLams appSpine appBVarsDec
  appBVarsDown fieldBVars liftIndices peelAll peelCtorParams fieldsClassify ctorsBefore
  flatOwnParams elimLevel RKeysAt REntryAt binderOf whnfTele hnf)
open Ix.Kernel (ConstantInfo ConstantVal RecRule Level LevelParam Expr)
open Ix.Kernel.Semantics (WrapRel WrapDom WrapT SymWrapT ConsumeStar LamDomAlong TwinRuleMatch
  stripLams consumeWrapper wrapperArity lamFirstArity letFree)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Small expression helpers -/

private theorem mkAppN_instantiateLevelParams_wb (ps : List LevelParam) (us : List KLevel) :
    ∀ (args : List KExpr) (f : KExpr),
      (Expr.mkAppN f args).instantiateLevelParams ps us =
        Expr.mkAppN (f.instantiateLevelParams ps us)
          (args.map (Expr.instantiateLevelParams ps us))
  | [], _ => rfl
  | a :: as, f => by
    simp only [Expr.mkAppN, List.map_cons]
    exact mkAppN_instantiateLevelParams_wb ps us as (.app f a)

private theorem mkAppN_liftLooseBVars_wb (n c : Nat) :
    ∀ (args : List KExpr) (f : KExpr),
      (Expr.mkAppN f args).liftLooseBVars n c =
        Expr.mkAppN (f.liftLooseBVars n c) (args.map (Expr.liftLooseBVars n c))
  | [], _ => rfl
  | a :: as, f => by
    simp only [Expr.mkAppN, List.map_cons]
    exact mkAppN_liftLooseBVars_wb n c as (.app f a)

private theorem renameConsts_liftLooseBVars_wb (f : KKey → KKey) (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      (e.liftLooseBVars n c).renameConsts f = (e.renameConsts f).liftLooseBVars n c
  | .bvar i, c => by simp only [Expr.liftLooseBVars, Expr.renameConsts]; split <;> rfl
  | .fvar _ t, c => by
    simp [Expr.liftLooseBVars, Expr.renameConsts, renameConsts_liftLooseBVars_wb f n t c]
  | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app g a, c => by
    simp [Expr.liftLooseBVars, Expr.renameConsts,
      renameConsts_liftLooseBVars_wb f n g c, renameConsts_liftLooseBVars_wb f n a c]
  | .lam t b _, c => by
    simp [Expr.liftLooseBVars, Expr.renameConsts,
      renameConsts_liftLooseBVars_wb f n t c, renameConsts_liftLooseBVars_wb f n b (c + 1)]
  | .forallE t b _, c => by
    simp [Expr.liftLooseBVars, Expr.renameConsts,
      renameConsts_liftLooseBVars_wb f n t c, renameConsts_liftLooseBVars_wb f n b (c + 1)]
  | .letE t v b _, c => by
    simp [Expr.liftLooseBVars, Expr.renameConsts,
      renameConsts_liftLooseBVars_wb f n t c, renameConsts_liftLooseBVars_wb f n v c,
      renameConsts_liftLooseBVars_wb f n b (c + 1)]
  | .proj _ _ e, c => by
    simp [Expr.liftLooseBVars, Expr.renameConsts, renameConsts_liftLooseBVars_wb f n e c]

/-- `Expr.renameConsts` commutes with `Expr.instantiateLevelParams`. -/
theorem renameConsts_instantiateLevelParams (f : KKey → KKey) (ps : List LevelParam)
    (us : List KLevel) :
    ∀ (e : KExpr), (e.instantiateLevelParams ps us).renameConsts f =
      (e.renameConsts f).instantiateLevelParams ps us
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ t => by
    simp [Expr.instantiateLevelParams, Expr.renameConsts,
      renameConsts_instantiateLevelParams f ps us t]
  | .app g a => by
    simp [Expr.instantiateLevelParams, Expr.renameConsts,
      renameConsts_instantiateLevelParams f ps us g,
      renameConsts_instantiateLevelParams f ps us a]
  | .lam t b _ => by
    simp [Expr.instantiateLevelParams, Expr.renameConsts,
      renameConsts_instantiateLevelParams f ps us t,
      renameConsts_instantiateLevelParams f ps us b]
  | .forallE t b _ => by
    simp [Expr.instantiateLevelParams, Expr.renameConsts,
      renameConsts_instantiateLevelParams f ps us t,
      renameConsts_instantiateLevelParams f ps us b]
  | .letE t v b _ => by
    simp [Expr.instantiateLevelParams, Expr.renameConsts,
      renameConsts_instantiateLevelParams f ps us t,
      renameConsts_instantiateLevelParams f ps us v,
      renameConsts_instantiateLevelParams f ps us b]
  | .proj _ _ e => by
    simp [Expr.instantiateLevelParams, Expr.renameConsts,
      renameConsts_instantiateLevelParams f ps us e]

/-! ## Deterministic full consumption -/

/-- `Consumes` followed by a stopping `consumeAt = some none` is deterministic. -/
theorem Consumes.unique {W : KKey → Option (Option Nat)} {t c₁ c₂ : KExpr}
    (h₁ : Consumes W t c₁) (hs₁ : consumeAt W c₁ = some none)
    (h₂ : Consumes W t c₂) (hs₂ : consumeAt W c₂ = some none) : c₁ = c₂ := by
  induction h₁ with
  | refl t =>
    cases h₂ with
    | refl => rfl
    | step hc _ =>
      rw [hs₁] at hc
      cases hc
  | @step _ a₁ _ hc₁ _ ih =>
    cases h₂ with
    | refl =>
      rw [hs₂] at hc₁
      cases hc₁
    | @step _ a₂ _ hc₂ h₂' =>
      have ha : a₁ = a₂ := Option.some.inj (Option.some.inj (hc₁.symm.trans hc₂))
      subst ha
      exact ih hs₁ h₂'

/-- Two full consumptions of one generated term are related by `WrapRel find?` at any lookup
`find?`, with no wrapper consumptions needed. -/
theorem FullCons.toWrapRel_of_both {W : KKey → Option (Option Nat)}
    {find? : KKey → Option (ConstantInfo .anon)} {g d₁ d₂ : KExpr}
    (h₁ : FullCons W g d₁) (h₂ : FullCons W g d₂) : WrapRel find? d₁ d₂ := by
  induction h₁ generalizing d₂ with
  | bvar i =>
    cases h₂
    exact .bvar i
  | fvar ht₁ =>
    cases h₂ with
    | fvar ht₂ =>
      exact .fvar (Binding.FamilyRecon.exprLvEq_wrapRel find? (ht₁.symm.trans ht₂))
  | sort hu₁ =>
    cases h₂ with
    | sort hu₂ => exact .sort (fun φ => (hu₁ φ).symm.trans (hu₂ φ))
  | const hus₁ =>
    cases h₂ with
    | const hus₂ =>
      exact .const (Binding.FamilyRecon.wrapLevels_of_lvEqList (hus₁.symm.trans hus₂))
  | lit l =>
    cases h₂
    exact .lit l
  | app _ _ ihf iha =>
    cases h₂ with
    | app hf₂ ha₂ => exact .app (ihf hf₂) (iha ha₂)
  | lam hpw₁ hcs₁ hstop₁ _ _ ihdom ihb =>
    cases h₂ with
    | lam hpw₂ hcs₂ hstop₂ hdom₂ hb₂ =>
      have hc := Consumes.unique hcs₁ hstop₁ hcs₂ hstop₂
      subst hc
      exact .lam (hpw₁.symm.trans hpw₂) (.keep (ihdom hdom₂)) (ihb hb₂)
  | forallE hpw₁ hcs₁ hstop₁ _ _ ihdom ihb =>
    cases h₂ with
    | forallE hpw₂ hcs₂ hstop₂ hdom₂ hb₂ =>
      have hc := Consumes.unique hcs₁ hstop₁ hcs₂ hstop₂
      subst hc
      exact .forallE (hpw₁.symm.trans hpw₂) (.keep (ihdom hdom₂)) (ihb hb₂)
  | letE _ _ _ iht ihv ihb =>
    cases h₂ with
    | letE ht₂ hv₂ hb₂ => exact .letE (iht ht₂) (ihv hv₂) (ihb hb₂)
  | proj _ ih =>
    cases h₂ with
    | proj he₂ => exact .proj (ih he₂)

/-! ## Observed wrapper consumptions and `wrapperArity` -/

/-- A wrapper key `w` was observed at arity `n` by `Ingress::get_ci` (returning a `Defn` value)
and `KernelCheck::lam_first_arity` (returning `(1, n)`) in `calls`. -/
def WrapperObserved (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (w : KKey) (n : Nat) : Prop :=
  ∃ (a : Bytes.Address) (addr ptr nl ty val saf hint : SourceValue F)
    (h h_ci h_la : Heap F) (cs_ci cs_la : List (Call F)),
    Core.keyOf t (Core.ixAddr a) = w ∧
    Bytes.RepAddressRef Core.addrTy h a addr ∧
    ObsFn Core.W "Ingress::get_ci" [addr] h ptr h_ci cs_ci ∧
    (∀ cl ∈ cs_ci, cl ∈ calls) ∧
    loadValue h_ci ptr = .ok (.construct Core.kciEnum "Defn" [nl, ty, val, saf, hint]) ∧
    (⟨"KernelCheck::lam_first_arity", [val, .field 0], h_ci⟩ : Call F) ∈ calls ∧
    ObsFn Core.W "KernelCheck::lam_first_arity" [val, .field 0] h_ci
      (.tuple [.field 1, .field (n : F)]) h_la cs_la ∧
    (∀ cl ∈ cs_la, cl ∈ calls) ∧
    n < 549755813888

/-- `WrapperObserved` is monotone in the call list. -/
theorem WrapperObserved.mono {calls calls' : List (Call F)} {t : Ix.Kernel.RoleTable}
    {w : KKey} {n : Nat} (hsub : ∀ cl ∈ calls, cl ∈ calls')
    (h : WrapperObserved calls t w n) : WrapperObserved calls' t w n := by
  obtain ⟨a, addr, ptr, nl, ty, val, saf, hint, h0, h_ci, h_la, cs_ci, cs_la,
    hk, ha, ev_ci, hs_ci, hld, hcl_la, ev_la, hs_la, hn⟩ := h
  exact ⟨a, addr, ptr, nl, ty, val, saf, hint, h0, h_ci, h_la, cs_ci, cs_la,
    hk, ha, ev_ci, fun cl hcl => hsub cl (hs_ci cl hcl), hld, hsub _ hcl_la,
    ev_la, fun cl hcl => hsub cl (hs_la cl hcl), hn⟩

private theorem tm_lam_descent_wb {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p w20 xb xm : SourceValue F} {steps : Nat}
    (hE : Core.Tm κ d Γ h k E p)
    (ld : loadValue h p = .ok (.construct Core.kexprEnum "Lam" [w20, xb, xm]))
    (hdesc : IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xb steps) :
    IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) p (steps + 1) := by
  cases hE with
  | @lam _ addr tp bp lp _ _ _ cell _ _ _ =>
    obtain ⟨_, hxs⟩ := Core.load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 _
    subst h1 h2
    exact .down cell (by simp [Value.type]) (by simp [IxVM.Refinement.RomBound.cellArgs]) hdesc
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact False.elim (Core.load_cell_ne cell ld (by decide))

private theorem tm_ptr_descent_zero_wb {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {E : KExpr} {p : SourceValue F}
    (hE : Core.Tm κ d Γ h k E p) :
    IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) p 0 := by
  cases hE with
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ _ | const cell _ _ _
  | app cell _ _ | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _
  | litNat cell _ _ | litStr cell _ _ | proj cell _ _ =>
    exact .here cell (by simp [Value.type])

private theorem lam_first_arity_go_wb {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn Core.W fname args h r h' cs → fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps →
          n + steps < 549755813888) →
        Core.Tm κ 0 Γ h n E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h :=
  ObsFn.strong_induction (world := Core.W)
    (fun fname args h r h' cs => fname = "KernelCheck::lam_first_arity" →
      ∀ (n : Nat) (E : KExpr) (xv xk : SourceValue F),
        args = [xv, .field (n : F)] → r = .tuple [.field 1, xk] →
        (∀ steps, IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps →
          n + steps < 549755813888) →
        Core.Tm κ 0 Γ h n E xv →
        ∃ k_out steps : Nat,
          xk = .field (k_out : F) ∧
          k_out = n + steps ∧
          IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xv steps ∧
          lamFirstArity E n = some k_out ∧
          h' = h)
    (fun fname args h r h' cs ev ih hfn n E xv xk hargs hr hbnd_desc hE => by
      subst hfn hargs hr
      match Obs.«KernelCheck::lam_first_arity».obs ev with
      | .Lam_Succ_other (he118 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_other (he141 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_n0 (he186 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .BVar_other_other (he264 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .other (he287 := he) .. =>
        injection he with hxs; injection hxs with h01 _
        exact absurd (Value.field.inj h01) one_ne_zero
      | .Lam_Succ_Zero (w20 := w20) (x_b := xb) (x_m := xm) (x_z := xz)
          (cs82 := cs82) (v86 := v86)
          (ld12 := ld12) (ld47 := ld47) (ld71 := ld71)
          (op107 := op107) (ev84 := ev84) (hc109 := hc109) =>
        subst hc109
        obtain ⟨T, B, ℓ, rfl, _, hB, hℓ⟩ := hE.lam_of_load ld12
        obtain ⟨u, rfl, hu⟩ := IxVM.Refinement.Levels.rep_succ_of_load hℓ ld47
        obtain rfl := IxVM.Refinement.Levels.rep_zero_of_load hu ld71
        have hv86 : v86 = .field ((n + 1 : Nat) : F) := Decl.evalBinOp_add_one n op107
        rw [hv86] at ev84
        have hbnd_b : ∀ steps, IxVM.Refinement.RomBound.HeapDescent h (.enum Core.kexprEnum) xb steps →
            (n + 1) + steps < 549755813888 := by
          intro steps hdb
          have hdp := tm_lam_descent_wb hE ld12 hdb
          have hlt := hbnd_desc (steps + 1) hdp
          omega
        obtain ⟨k_out, steps, hxk, hk_eq, hdb, hlam, hh⟩ :=
          ih _ _ _ _ _ _ (by simp only [List.length_cons, List.length_append]; omega)
            ev84 rfl (n + 1) B xb xk rfl rfl hbnd_b hB
        refine ⟨k_out, steps + 1, hxk, by omega, tm_lam_descent_wb hE ld12 hdb, ?_, hh⟩
        simpa [lamFirstArity, Core.bmeta, Level.zeronessOf] using hlam
      | .BVar_other_n0 (x_i := xi) (y215 := y215)
          (ld12 := ld12) (hne201 := hne201) (op230 := op230) (op221 := op221)
          (he240 := he240) (he254 := he254) .. =>
        injection he240 with hxs; injection hxs with _ hxs; injection hxs with hxk _
        have hxk' : xk = .field (n : F) := hxk
        cases n with
        | zero => exact absurd rfl hne201
        | succ m =>
          have hy215 : y215 = .field (m : F) := Decl.evalBinOp_sub_succ m op230
          obtain ⟨i_f, rfl, _, hbvar⟩ := hE.bvar_of_load ld12
          rcases hbvar with ⟨hi_lt, rfl⟩ | ⟨_, hbad, _⟩
          · rw [hy215] at op221
            simp only [evalBinOp, bind, Except.bind, pure, Except.pure, Option.some.injEq,
              Except.ok.injEq, Value.field.injEq] at op221
            have hif : i_f = (m : F) := sub_eq_zero.mp op221
            have hn_lt : m + 1 < 549755813888 := by
              have := hbnd_desc 0 (tm_ptr_descent_zero_wb hE)
              omega
            have hval_i : ZMod.val i_f = m := by
              rw [hif]
              exact ZMod.val_natCast_of_lt (Nat.lt_trans (by omega : m < 549755813888) (by decide))
            refine ⟨m + 1, 0, hxk', by omega, tm_ptr_descent_zero_wb hE, ?_, he254⟩
            simp [lamFirstArity, hval_i]
          · omega)

/-- **Observed wrapper arity gives IxC's `wrapperArity env.find?`** whenever `w` resolves in `env`
and `calls` is good for `(E, env, t, lim)` under `Decl.PrefixInv`. -/
theorem wrapperArity_of_observed {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat} {w : KKey} {n : Nat}
    (hSS : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hres : (env.find? w).isSome = true) (hobs : WrapperObserved calls t w n) :
    wrapperArity env.find? w = some n := by
  obtain ⟨a, addr, ptr, nl, ty, val, saf, hint, h0, h_ci, h_la, cs_ci, cs_la,
    hk, ha, ev_ci, hs_ci, hld, hcl_la, ev_la, hs_la, hn_lt⟩ := hobs
  let c : Core.Ctx := ⟨E, env, t, lim⟩
  obtain ⟨ci₀, hci₀⟩ := Option.isSome_iff_exists.mp hres
  have hκa : c.stored.κ (Core.ixAddr a) = w := by
    have hf : env.find? (Core.keyOf t (Core.ixAddr a)) = some ci₀ := by rw [hk]; exact hci₀
    exact (Core.Ctx.stored_key_of_find (c := c) hf).trans hk
  have hne : c.stored.κ (Core.ixAddr a) ≠ Core.unresolvedKey := by
    rw [hκa, ← hk]
    exact Core.Resolved.ne
  have hg_all : Core.Good c calls := hSS.good env lim
  have hg_ci : Core.CoreGood c.stored cs_ci :=
    Core.CoreGood.ofRaw (hg_all.sub hs_ci) (fun _ _ => trivial)
  obtain ⟨ci, hfind_ci, p_v, hp_ld, hci_rep⟩ :=
    hinv.loads.getCI addr ptr h0 h_ci cs_ci a ev_ci trivial hne hg_ci ha
  rw [hκa] at hfind_ci
  rw [hp_ld] at hld
  injection hld with hv_eq
  subst hv_eq
  obtain ⟨cv, V, hn_hint, rfl, _, hV⟩ := Core.CIRep.defn_inv hci_rep
  have hbnd_la : ∀ steps, IxVM.Refinement.RomBound.HeapDescent h_ci (.enum Core.kexprEnum) val steps →
      0 + steps < 549755813888 := by
    intro steps hdesc
    have hlt := IxVM.Refinement.RomBound.bounded_descent_lt hg_all.2 hcl_la List.mem_cons_self hdesc
    simpa using hlt
  obtain ⟨k_out, steps, hxk, hk_steps, hdesc_v, hlam_pos, -⟩ :=
    lam_first_arity_go_wb _ _ _ _ _ _ ev_la rfl 0 (Core.posOf cv.levelParams V) val (.field (n : F))
      rfl rfl hbnd_la (hV 0 (fun _ => default))
  rw [Decl.lamFirstArity_posOf] at hlam_pos
  have hk_lt : k_out < 549755813888 := by
    have := hbnd_la steps hdesc_v; omega
  have hkeq : k_out = n := by
    have hf : (n : F) = (k_out : F) := Value.field.inj hxk
    have h1 : (n : F).val = n := ZMod.val_natCast_of_lt (Nat.lt_trans hn_lt (by decide))
    have h2 : (k_out : F).val = k_out := ZMod.val_natCast_of_lt (Nat.lt_trans hk_lt (by decide))
    have hv := congrArg ZMod.val hf
    omega
  subst hkeq
  have hfind_env : env.find? w = some (.defnInfo cv V hn_hint) := hfind_ci
  simp [wrapperArity, hfind_env, hlam_pos]

/-- Wrapper consumption carrying an observation predicate `ObsW` on every consumed wrapper. -/
inductive ConsumesObs (W : KKey → Option (Option Nat)) (ObsW : KKey → Nat → Prop) :
    KExpr → KExpr → Prop
  | refl (t : KExpr) : ConsumesObs W ObsW t t
  | step {t a c : KExpr} {w : KKey} {n : Nat} :
      consumeAt W t = some (some a) →
      appHead t = some w → W w = some (some n) → ObsW w n →
      ConsumesObs W ObsW a c → ConsumesObs W ObsW t c

/-- Wrapper consumption at binder domains carrying an observation predicate `ObsW` on every
consumed wrapper (no stopping condition required). -/
inductive WrapConsObs (W : KKey → Option (Option Nat)) (ObsW : KKey → Nat → Prop) :
    KExpr → KExpr → Prop
  | bvar (i : Nat) : WrapConsObs W ObsW (.bvar i) (.bvar i)
  | fvar {i : Nat} {t t' : KExpr} : ExprLvEq t t' → WrapConsObs W ObsW (.fvar i t) (.fvar i t')
  | sort {u v : KLevel} : LvEq u v → WrapConsObs W ObsW (.sort u) (.sort v)
  | const {n : KKey} {us vs : List KLevel} :
      LvEqList us vs → WrapConsObs W ObsW (.const n us) (.const n vs)
  | lit (l : Ix.Kernel.Literal) : WrapConsObs W ObsW (.lit l) (.lit l)
  | app {f a f' a' : KExpr} :
      WrapConsObs W ObsW f f' → WrapConsObs W ObsW a a' →
      WrapConsObs W ObsW (.app f a) (.app f' a')
  | lam {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumesObs W ObsW t c →
      WrapConsObs W ObsW c t' → WrapConsObs W ObsW b b' →
      WrapConsObs W ObsW (.lam t b m) (.lam t' b' m')
  | forallE {t c b t' b' : KExpr} {m m' : Ix.Kernel.BinderMeta} :
      m.pw = m'.pw → ConsumesObs W ObsW t c →
      WrapConsObs W ObsW c t' → WrapConsObs W ObsW b b' →
      WrapConsObs W ObsW (.forallE t b m) (.forallE t' b' m')
  | letE {t v b t' v' b' : KExpr} {l l' : Ix.Kernel.LetMeta} :
      WrapConsObs W ObsW t t' → WrapConsObs W ObsW v v' → WrapConsObs W ObsW b b' →
      WrapConsObs W ObsW (.letE t v b l) (.letE t' v' b' l')
  | proj {s : KKey} {i : Nat} {e e' : KExpr} :
      WrapConsObs W ObsW e e' → WrapConsObs W ObsW (.proj s i e) (.proj s i e')

theorem ConsumesObs.toConsumes {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {t c : KExpr} (h : ConsumesObs W ObsW t c) : Consumes W t c := by
  induction h with
  | refl t => exact .refl t
  | step hc _ _ _ _ ih => exact .step hc ih

theorem ConsumesObs.mono {W W' : KKey → Option (Option Nat)} {ObsW ObsW' : KKey → Nat → Prop}
    (hW : ∀ w x, W w = some x → W' w = some x)
    (hO : ∀ w n, ObsW w n → ObsW' w n) {t c : KExpr} (h : ConsumesObs W ObsW t c) :
    ConsumesObs W' ObsW' t c := by
  induction h with
  | refl t => exact .refl t
  | step hc hd hw ho _ ih =>
    exact .step (Binding.FamilyRecon.consumeAt_mono hW hc) hd (hW _ _ hw) (hO _ _ ho) ih

theorem WrapConsObs.mono {W W' : KKey → Option (Option Nat)} {ObsW ObsW' : KKey → Nat → Prop}
    (hW : ∀ w x, W w = some x → W' w = some x)
    (hO : ∀ w n, ObsW w n → ObsW' w n) {g d : KExpr} (h : WrapConsObs W ObsW g d) :
    WrapConsObs W' ObsW' g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar ht => exact .fvar ht
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hcs _ _ ihdom ihb => exact .lam hpw (hcs.mono hW hO) ihdom ihb
  | forallE hpw hcs _ _ ihdom ihb => exact .forallE hpw (hcs.mono hW hO) ihdom ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | proj _ ih => exact .proj ih

private theorem constsResolve_appHead_and_arg {env : Ix.Kernel.Env .anon} {t a : KExpr}
    {W : KKey → Option (Option Nat)} {w : KKey} {n : Nat}
    (hcr : t.constsResolve env = true)
    (hc : consumeAt W t = some (some a)) (hd : appHead t = some w) (hw : W w = some (some n)) :
    (env.find? w).isSome = true ∧ a.constsResolve env = true ∧
      Ix.Kernel.Expr.getAppArgs t = a :: (Ix.Kernel.Expr.getAppArgs t).tail ∧
      (Ix.Kernel.Expr.getAppArgs t).length = n := by
  obtain ⟨us, hfn⟩ := Binding.FamilyRecon.appHead_some hd
  have hcr_fn : ∀ e : KExpr, e.constsResolve env = true →
      e.getAppFn.constsResolve env = true ∧ ∀ x ∈ e.getAppArgs, x.constsResolve env = true := by
    intro e
    induction e with
    | app f x ihf ihx =>
      intro h
      simp only [Expr.constsResolve, Bool.and_eq_true] at h
      have ⟨hf1, hf2⟩ := ihf h.1
      refine ⟨hf1, fun y hy => ?_⟩
      simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact hf2 y hy
      · exact h.2
    | _ => intro h; exact ⟨h, fun _ hy => nomatch hy⟩
  obtain ⟨hfn_cr, hargs_cr⟩ := hcr_fn t hcr
  rw [hfn] at hfn_cr
  simp only [Expr.constsResolve] at hfn_cr
  have hca : consumeOf W (appHead t) t.getAppArgs = some (some a) := hc
  rw [hd] at hca
  cases hargs : t.getAppArgs with
  | nil => rw [hargs] at hca; simp [consumeOf] at hca
  | cons a' rest =>
    rw [hargs] at hca
    simp only [consumeOf, hw, Option.map_some, Option.some.injEq] at hca
    split at hca
    · next hlen =>
      injection hca with ha_eq
      subst ha_eq
      refine ⟨hfn_cr, hargs_cr a' (by rw [hargs]; exact List.mem_cons_self), by simp, ?_⟩
      simpa using hlen.symm
    · cases hca

private theorem ConsumesObs.toWrapDom_of_obs {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {env : Ix.Kernel.Env .anon}
    (hObs : ∀ w n, (env.find? w).isSome = true → ObsW w n → wrapperArity env.find? w = some n)
    {t c : KExpr} (h : ConsumesObs W ObsW t c) :
    t.constsResolve env = true →
      c.constsResolve env = true ∧
      ∀ {t' : KExpr}, WrapRel env.find? c t' → WrapDom env.find? t t' := by
  induction h with
  | refl t => intro hcr; exact ⟨hcr, fun hr => .keep hr⟩
  | @step t a c w n hc hd hw ho _ ih =>
    intro hcr
    obtain ⟨hfind, ha_cr, hargs_cons, hargs_len⟩ := constsResolve_appHead_and_arg hcr hc hd hw
    obtain ⟨us, hfn⟩ := Binding.FamilyRecon.appHead_some hd
    have hwa : wrapperArity env.find? w = some n := hObs w n hfind ho
    have hcw : consumeWrapper env.find? t = some a := by
      unfold consumeWrapper
      rw [hfn, hargs_cons]
      rw [hargs_cons, List.length_cons] at hargs_len
      dsimp only
      rw [hwa, hargs_len]
      simp
    obtain ⟨hc_cr, hdom⟩ := ih ha_cr
    exact ⟨hc_cr, fun hr => .consume hcw (hdom hr)⟩

/-- **Observed wrapper consumption implies `WrapRel env.find?`** whenever every constant in `g`
resolves in `env` and observed wrappers match `wrapperArity env.find?`. -/
theorem WrapConsObs.toWrapRel {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {env : Ix.Kernel.Env .anon}
    (hObs : ∀ w n, (env.find? w).isSome = true → ObsW w n → wrapperArity env.find? w = some n)
    {g d : KExpr} (h : WrapConsObs W ObsW g d) (hcr : g.constsResolve env = true) :
    WrapRel env.find? g d := by
  induction h with
  | bvar i => exact .bvar i
  | fvar ht => exact .fvar (Binding.FamilyRecon.exprLvEq_wrapRel env.find? ht)
  | sort hu => exact .sort hu
  | const hus => exact .const (Binding.FamilyRecon.wrapLevels_of_lvEqList hus)
  | lit l => exact .lit l
  | app _ _ ihf iha =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    exact .app (ihf hcr.1) (iha hcr.2)
  | lam hpw hcs _ _ ihdom ihb =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    obtain ⟨hc_cr, hdom⟩ := hcs.toWrapDom_of_obs hObs hcr.1
    exact .lam hpw (hdom (ihdom hc_cr)) (ihb hcr.2)
  | forallE hpw hcs _ _ ihdom ihb =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    obtain ⟨hc_cr, hdom⟩ := hcs.toWrapDom_of_obs hObs hcr.1
    exact .forallE hpw (hdom (ihdom hc_cr)) (ihb hcr.2)
  | letE _ _ _ iht ihv ihb =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    exact .letE (iht hcr.1.1) (ihv hcr.1.2) (ihb hcr.2)
  | proj _ ih =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    exact .proj (ih hcr.2)

/-- Two observed wrapper consumptions from the same starting term are linearly ordered. -/
theorem ConsumesObs.linear {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {t c₁ c₂ : KExpr} (h₁ : ConsumesObs W ObsW t c₁) (h₂ : ConsumesObs W ObsW t c₂) :
    ConsumesObs W ObsW c₁ c₂ ∨ ConsumesObs W ObsW c₂ c₁ := by
  induction h₁ with
  | refl => exact Or.inl h₂
  | @step t a₁ c₁ w₁ n₁ hc₁ hd₁ hw₁ ho₁ h₁' ih =>
    cases h₂ with
    | refl => exact Or.inr (.step hc₁ hd₁ hw₁ ho₁ h₁')
    | @step _ a₂ _ _ _ hc₂ _ _ _ h₂' =>
      have ha : a₁ = a₂ := Option.some.inj (Option.some.inj (hc₁.symm.trans hc₂))
      subst ha
      exact ih h₂'

private theorem consumeAt_inv_wb {W : KKey → Option (Option Nat)} {t a : KExpr} {w : KKey} {n : Nat}
    (hc : consumeAt W t = some (some a)) (hd : appHead t = some w) (hw : W w = some (some n)) :
    ∃ us rest, t = Expr.mkAppN (.const w us) (a :: rest) ∧ rest.length + 1 = n := by
  obtain ⟨us, hfn⟩ := Binding.FamilyRecon.appHead_some hd
  have ht := Ix.Kernel.Expr.mkAppN_getApp t
  have hca : consumeOf W (appHead t) t.getAppArgs = some (some a) := hc
  rw [hd] at hca
  cases hargs : t.getAppArgs with
  | nil => rw [hargs] at hca; simp [consumeOf] at hca
  | cons a' rest =>
    rw [hargs] at hca
    simp only [consumeOf, hw, Option.map_some, Option.some.injEq] at hca
    split at hca
    · next hlen =>
      injection hca with ha_eq
      subst ha_eq
      exact ⟨us, rest, by rw [← ht, hfn, hargs], by simpa [List.length_cons] using hlen.symm⟩
    · cases hca

private theorem ConsumesObs.sizeB_le {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {t c : KExpr} (h : ConsumesObs W ObsW t c) : c.sizeB ≤ t.sizeB := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step _ a _ w _ hc hd hw _ _ ih =>
    obtain ⟨us, rest, rfl, -⟩ := consumeAt_inv_wb hc hd hw
    have hlt : a.sizeB < (Expr.mkAppN (.const w us) (a :: rest)).sizeB :=
      Nat.lt_of_lt_of_le (by simp only [Ix.Kernel.Expr.sizeB]; omega)
        (Ix.Kernel.Semantics.sizeB_le_mkAppN rest (.app (.const w us) a))
    exact Nat.le_trans ih (Nat.le_of_lt hlt)

private theorem WrapConsObs.mkAppN_inv {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop} :
    ∀ (args : List KExpr) {f t : KExpr},
      WrapConsObs W ObsW (Expr.mkAppN f args) t →
      ∃ f' args', t = Expr.mkAppN f' args' ∧ args'.length = args.length ∧
        WrapConsObs W ObsW f f' ∧ List.Forall₂ (WrapConsObs W ObsW) args args'
  | [], _, t, h => ⟨t, [], rfl, rfl, h, .nil⟩
  | a :: as, f, t, h => by
    obtain ⟨fa', as', rfl, hlen, hfa, has'⟩ := WrapConsObs.mkAppN_inv as (f := .app f a) h
    cases hfa with
    | app hf ha => exact ⟨_, _ :: as', rfl, by simp [hlen], hf, .cons ha has'⟩

private theorem mkAppN_constsResolve_wb {env : Ix.Kernel.Env .anon} :
    ∀ (args : List KExpr) (f : KExpr),
      (Expr.mkAppN f args).constsResolve env = true ↔
        f.constsResolve env = true ∧ ∀ a ∈ args, a.constsResolve env = true
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    simp only [Expr.mkAppN, mkAppN_constsResolve_wb as (.app f a), Expr.constsResolve,
      Bool.and_eq_true, List.mem_cons]
    constructor
    · rintro ⟨⟨hf, ha⟩, has⟩
      exact ⟨hf, fun x hx => hx.elim (fun h => h ▸ ha) (has x)⟩
    · rintro ⟨hf, hall⟩
      exact ⟨⟨hf, hall a (Or.inl rfl)⟩, fun x hx => hall x (Or.inr hx)⟩

private theorem mkAppN_letFree_wb :
    ∀ (args : List KExpr) (f : KExpr),
      letFree (Expr.mkAppN f args) = true ↔
        letFree f = true ∧ ∀ a ∈ args, letFree a = true
  | [], f => by simp [Expr.mkAppN]
  | a :: as, f => by
    simp only [Expr.mkAppN, mkAppN_letFree_wb as (.app f a), letFree, Bool.and_eq_true,
      List.mem_cons]
    constructor
    · rintro ⟨⟨hf, ha⟩, has⟩
      exact ⟨hf, fun x hx => hx.elim (fun h => h ▸ ha) (has x)⟩
    · rintro ⟨hf, hall⟩
      exact ⟨⟨hf, hall a (Or.inl rfl)⟩, fun x hx => hall x (Or.inr hx)⟩

private theorem WrapConsObs.consumeObs {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {env : Ix.Kernel.Env .anon}
    (hObs : ∀ w n, (env.find? w).isSome = true → ObsW w n → wrapperArity env.find? w = some n)
    {t a d : KExpr} {w : KKey} {n : Nat}
    (hd : WrapConsObs W ObsW t d)
    (hc : consumeAt W t = some (some a)) (hhd : appHead t = some w)
    (hw : W w = some (some n)) (ho : ObsW w n)
    (hcr : d.constsResolve env = true) (hlf : letFree d = true) :
    ∃ a', consumeWrapper env.find? d = some a' ∧ WrapConsObs W ObsW a a' ∧
      a'.constsResolve env = true ∧ letFree a' = true := by
  obtain ⟨us, rest, rfl, hlen⟩ := consumeAt_inv_wb hc hhd hw
  obtain ⟨f', args', rfl, hargs_len, hf', hargs'⟩ := WrapConsObs.mkAppN_inv (a :: rest) hd
  cases hf' with
  | const _ =>
    cases hargs' with
    | cons ha' hrest' =>
      rename_i a' rest'
      have hcr' := (mkAppN_constsResolve_wb (a' :: rest') (.const w _)).mp hcr
      have hlf' := (mkAppN_letFree_wb (a' :: rest') (.const w _)).mp hlf
      have hfind : (env.find? w).isSome = true := hcr'.1
      have hwa : wrapperArity env.find? w = some n := hObs w n hfind ho
      have hrest_len : rest'.length + 1 = n := by
        simp only [List.length_cons] at hargs_len
        omega
      refine ⟨a', Ix.Kernel.Semantics.consumeWrapper_mkAppN (by rw [hrest_len]; exact hwa),
        ha', hcr'.2 a' List.mem_cons_self, hlf'.2 a' List.mem_cons_self⟩

private theorem WrapConsObs.consumeStarObs {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {env : Ix.Kernel.Env .anon}
    (hObs : ∀ w n, (env.find? w).isSome = true → ObsW w n → wrapperArity env.find? w = some n)
    {t c d : KExpr} (hd : WrapConsObs W ObsW t d) (hcs : ConsumesObs W ObsW t c) :
    d.constsResolve env = true → letFree d = true →
      ∃ d', ConsumeStar env.find? d d' ∧ WrapConsObs W ObsW c d' ∧
        d'.constsResolve env = true ∧ letFree d' = true := by
  induction hcs generalizing d with
  | refl => intro hcr hlf; exact ⟨d, .refl d, hd, hcr, hlf⟩
  | step hc hhd hw ho _ ih =>
    intro hcr hlf
    obtain ⟨a', hcw, ha', hcr_a, hlf_a⟩ := hd.consumeObs hObs hc hhd hw ho hcr hlf
    obtain ⟨d', hstar, hc', hcr_d', hlf_d'⟩ := ih ha' hcr_a hlf_a
    exact ⟨d', .step hcw hstar, hc', hcr_d', hlf_d'⟩

private theorem WrapConsObs.toSymWrapT_aux {W : KKey → Option (Option Nat)}
    {ObsW : KKey → Nat → Prop} {env : Ix.Kernel.Env .anon}
    (hObs : ∀ w n, (env.find? w).isSome = true → ObsW w n → wrapperArity env.find? w = some n) :
    ∀ (n : Nat) (g d₁ d₂ : KExpr), g.sizeB < n →
      WrapConsObs W ObsW g d₁ → WrapConsObs W ObsW g d₂ →
      d₁.constsResolve env = true → d₂.constsResolve env = true →
      letFree d₁ = true → letFree d₂ = true →
      SymWrapT env.find? d₁ d₂
  | 0, _, _, _, hlt, _, _, _, _, _, _ => absurd hlt (Nat.not_lt_zero _)
  | n + 1, _, _, _, hlt, h₁, h₂, hcr₁, hcr₂, hlf₁, hlf₂ => by
    cases h₁ with
    | bvar i => cases h₂; exact .bvar i
    | fvar _ => cases h₂; exact .fvar _ _ _
    | sort hu₁ =>
      cases h₂ with
      | sort hu₂ => exact .sort (fun φ => (hu₁ φ).symm.trans (hu₂ φ))
    | const hus₁ =>
      cases h₂ with
      | const hus₂ =>
        exact .const (Binding.FamilyRecon.wrapLevels_of_lvEqList (hus₁.symm.trans hus₂))
    | lit l => cases h₂; exact .lit l
    | app hf₁ ha₁ =>
      cases h₂ with
      | app hf₂ ha₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        simp only [Expr.constsResolve, Bool.and_eq_true] at hcr₁ hcr₂
        simp only [letFree, Bool.and_eq_true] at hlf₁ hlf₂
        exact .app
          (WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) hf₁ hf₂ hcr₁.1 hcr₂.1 hlf₁.1 hlf₂.1)
          (WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) ha₁ ha₂ hcr₁.2 hcr₂.2 hlf₁.2 hlf₂.2)
    | lam hpw₁ hcs₁ hd₁ hb₁ =>
      cases h₂ with
      | lam hpw₂ hcs₂ hd₂ hb₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        simp only [Expr.constsResolve, Bool.and_eq_true] at hcr₁ hcr₂
        simp only [letFree, Bool.and_eq_true] at hlf₁ hlf₂
        have hb := WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) hb₁ hb₂ hcr₁.2 hcr₂.2 hlf₁.2 hlf₂.2
        rcases hcs₁.linear hcs₂ with h12 | h21
        · obtain ⟨d₁', hstar, hd₁', hcr₁', hlf₁'⟩ := hd₁.consumeStarObs hObs h12 hcr₁.1 hlf₁.1
          have hsz := hcs₂.sizeB_le
          exact .lamL (hpw₁.symm.trans hpw₂) hstar
            (WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) hd₁' hd₂ hcr₁' hcr₂.1 hlf₁' hlf₂.1) hb
        · obtain ⟨d₂', hstar, hd₂', hcr₂', hlf₂'⟩ := hd₂.consumeStarObs hObs h21 hcr₂.1 hlf₂.1
          have hsz := hcs₁.sizeB_le
          exact .lamR (hpw₁.symm.trans hpw₂) hstar
            (WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) hd₁ hd₂' hcr₁.1 hcr₂' hlf₁.1 hlf₂') hb
    | forallE hpw₁ hcs₁ hd₁ hb₁ =>
      cases h₂ with
      | forallE hpw₂ hcs₂ hd₂ hb₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        simp only [Expr.constsResolve, Bool.and_eq_true] at hcr₁ hcr₂
        simp only [letFree, Bool.and_eq_true] at hlf₁ hlf₂
        have hb := WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) hb₁ hb₂ hcr₁.2 hcr₂.2 hlf₁.2 hlf₂.2
        rcases hcs₁.linear hcs₂ with h12 | h21
        · obtain ⟨d₁', hstar, hd₁', hcr₁', hlf₁'⟩ := hd₁.consumeStarObs hObs h12 hcr₁.1 hlf₁.1
          have hsz := hcs₂.sizeB_le
          exact .forallEL (hpw₁.symm.trans hpw₂) hstar
            (WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) hd₁' hd₂ hcr₁' hcr₂.1 hlf₁' hlf₂.1) hb
        · obtain ⟨d₂', hstar, hd₂', hcr₂', hlf₂'⟩ := hd₂.consumeStarObs hObs h21 hcr₂.1 hlf₂.1
          have hsz := hcs₁.sizeB_le
          exact .forallER (hpw₁.symm.trans hpw₂) hstar
            (WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) hd₁ hd₂' hcr₁.1 hcr₂' hlf₁.1 hlf₂') hb
    | letE _ _ _ => simp [letFree] at hlf₁
    | proj he₁ =>
      cases h₂ with
      | proj he₂ =>
        simp only [Ix.Kernel.Expr.sizeB] at hlt
        simp only [Expr.constsResolve, Bool.and_eq_true] at hcr₁ hcr₂
        exact .proj (WrapConsObs.toSymWrapT_aux hObs n _ _ _ (by omega) he₁ he₂ hcr₁.2 hcr₂.2 hlf₁ hlf₂)

/-- **Two observed wrapper consumptions of one reconstructed term are related by `SymWrapT`**,
requiring constant resolution only on `d₁` and `d₂` (never on `g`) and no stopping condition. -/
theorem WrapConsObs.toSymWrapT {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {env : Ix.Kernel.Env .anon}
    (hObs : ∀ w n, (env.find? w).isSome = true → ObsW w n → wrapperArity env.find? w = some n)
    {g d₁ d₂ : KExpr}
    (h₁ : WrapConsObs W ObsW g d₁) (h₂ : WrapConsObs W ObsW g d₂)
    (hcr₁ : d₁.constsResolve env = true) (hcr₂ : d₂.constsResolve env = true)
    (hlf₁ : letFree d₁ = true) (hlf₂ : letFree d₂ = true) :
    SymWrapT env.find? d₁ d₂ :=
  WrapConsObs.toSymWrapT_aux hObs (g.sizeB + 1) g d₁ d₂ (Nat.lt_succ_self _) h₁ h₂ hcr₁ hcr₂ hlf₁ hlf₂

theorem WrapConsObs.peelForalls {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop} :
    ∀ (n : Nat) {e₁ e₂ r₁ : KExpr}, WrapConsObs W ObsW e₁ e₂ →
      Binding.FamilyFlat.peelForalls n e₁ = some r₁ →
      ∃ r₂, Binding.FamilyFlat.peelForalls n e₂ = some r₂ ∧ WrapConsObs W ObsW r₁ r₂
  | 0, _, _, _, h, h1 => by
    simp only [Binding.FamilyFlat.peelForalls, Option.some.injEq] at h1; subst h1; exact ⟨_, rfl, h⟩
  | n + 1, _, _, _, h, h1 => by
    cases h with
    | forallE _ _ _ hb => exact WrapConsObs.peelForalls n hb h1
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [Binding.FamilyFlat.peelForalls] at h1

theorem WrapConsObs.peelForalls_max_eq {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop} :
    ∀ {n₁ n₂ : Nat} {e₁ e₂ c₁ c₂ : KExpr},
      WrapConsObs W ObsW e₁ e₂ →
      Binding.FamilyFlat.peelForalls n₁ e₁ = some c₁ → (∀ d b m, c₁ ≠ .forallE d b m) →
      Binding.FamilyFlat.peelForalls n₂ e₂ = some c₂ → (∀ d b m, c₂ ≠ .forallE d b m) →
      n₁ = n₂
  | 0, 0, _, _, _, _, _, _, _, _, _ => rfl
  | 0, _ + 1, _, _, _, _, h, h1, hnc1, h2, _ => by
    simp only [Binding.FamilyFlat.peelForalls, Option.some.injEq] at h1; subst h1
    cases h with
    | forallE _ _ _ _ => exact absurd rfl (hnc1 _ _ _)
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [Binding.FamilyFlat.peelForalls] at h2
  | _ + 1, 0, _, _, _, _, h, h1, _, h2, hnc2 => by
    simp only [Binding.FamilyFlat.peelForalls, Option.some.injEq] at h2; subst h2
    cases h with
    | forallE _ _ _ _ => exact absurd rfl (hnc2 _ _ _)
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [Binding.FamilyFlat.peelForalls] at h1
  | _ + 1, _ + 1, _, _, _, _, h, h1, hnc1, h2, hnc2 => by
    cases h with
    | forallE _ _ _ hb =>
      exact congrArg Nat.succ (WrapConsObs.peelForalls_max_eq hb h1 hnc1 h2 hnc2)
    | bvar | fvar | sort | const | app | lam | letE | lit | proj =>
      simp [Binding.FamilyFlat.peelForalls] at h1

private theorem forall₂_append_wb {α β : Type} {R : α → β → Prop}
    {a₁ a₂ : List α} {b₁ b₂ : List β}
    (h₁ : List.Forall₂ R a₁ b₁) (h₂ : List.Forall₂ R a₂ b₂) :
    List.Forall₂ R (a₁ ++ a₂) (b₁ ++ b₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons hr _ ih => exact .cons hr ih

theorem WrapConsObs.getAppArgs {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {e₁ e₂ : KExpr} (h : WrapConsObs W ObsW e₁ e₂) :
    List.Forall₂ (WrapConsObs W ObsW) e₁.getAppArgs e₂.getAppArgs := by
  induction h with
  | app _ ha ihf _ =>
    simp only [Expr.getAppArgs]
    exact forall₂_append_wb ihf (.cons ha .nil)
  | bvar | fvar | sort | const | lam | forallE | letE | lit | proj => exact .nil

theorem WrapConsObs.bvar_eq {W : KKey → Option (Option Nat)} {ObsW : KKey → Nat → Prop}
    {i : Nat} {e : KExpr} (h : WrapConsObs W ObsW (.bvar i) e) : e = .bvar i := by
  cases h; rfl

/-! ## Congruence and transport of `WrapRel` and `WrapDom` -/

theorem constsResolve_of_exprLvEq {env : Ix.Kernel.Env .anon} {e₁ e₂ : KExpr}
    (h : ExprLvEq e₁ e₂) : e₁.constsResolve env = e₂.constsResolve env := by
  induction h with
  | bvar | sort _ | const _ | lit => rfl
  | fvar _ ih => simp [Expr.constsResolve, ih]
  | app _ _ ihf iha => simp [Expr.constsResolve, ihf, iha]
  | lam _ _ iht ihb => simp [Expr.constsResolve, iht, ihb]
  | forallE _ _ iht ihb => simp [Expr.constsResolve, iht, ihb]
  | letE _ _ _ iht ihv ihb => simp [Expr.constsResolve, iht, ihv, ihb]
  | proj _ ih => simp [Expr.constsResolve, ih]

theorem mentionsConst_of_exprLvEq {k : KKey} {e₁ e₂ : KExpr}
    (h : ExprLvEq e₁ e₂) : e₁.mentionsConst k = e₂.mentionsConst k := by
  induction h with
  | bvar | sort _ | const _ | lit => rfl
  | fvar _ ih => simp [Expr.mentionsConst, ih]
  | app _ _ ihf iha => simp [Expr.mentionsConst, ihf, iha]
  | lam _ _ iht ihb => simp [Expr.mentionsConst, iht, ihb]
  | forallE _ _ iht ihb => simp [Expr.mentionsConst, iht, ihb]
  | letE _ _ _ iht ihv ihb => simp [Expr.mentionsConst, iht, ihv, ihb]
  | proj _ ih => simp [Expr.mentionsConst, ih]

private theorem consumeWrapper_congr {find? : KKey → Option (ConstantInfo .anon)}
    {t₁ t₂ a : KExpr} (h : ExprLvEq t₁ t₂) (hc : consumeWrapper find? t₂ = some a) :
    ∃ a₁, consumeWrapper find? t₁ = some a₁ ∧ ExprLvEq a₁ a := by
  obtain ⟨w, us, rest, ht2, hw⟩ := Ix.Kernel.Semantics.consumeWrapper_inv hc
  have hhd := Binding.FamilyRecon.appHead_congr h
  have hhd2 : appHead t₂ = some w := by
    simp [appHead, ht2, Expr.getAppFn_mkAppN, Expr.getAppFn]
  rw [hhd2] at hhd
  obtain ⟨us₁, hfn₁⟩ := Binding.FamilyRecon.appHead_some hhd
  have hargs := Binding.FamilyRecon.getAppArgs_congr h
  have hargs2 : t₂.getAppArgs = a :: rest := by
    rw [ht2, Expr.getAppArgs_mkAppN]
    simp [Expr.getAppArgs]
  rw [hargs2] at hargs
  generalize hga : t₁.getAppArgs = l₁ at hargs
  cases hargs with
  | @cons a₁ _ rest₁ _ ha hrest =>
    have hlen : rest₁.length = rest.length := Binding.FamilyRecon.forall2_length hrest
    refine ⟨a₁, ?_, ha⟩
    unfold consumeWrapper
    rw [hfn₁, hga]
    dsimp only
    rw [hw, hlen]
    simp

private theorem forall2_eval_trans_left {us₁ us₂ vs : List KLevel}
    (h1 : LvEqList us₁ us₂)
    (h2 : Ix.Kernel.Semantics.Forall₂ (fun u v => ∀ φ, u.eval φ = v.eval φ) us₂ vs) :
    Ix.Kernel.Semantics.Forall₂ (fun u v => ∀ φ, u.eval φ = v.eval φ) us₁ vs := by
  induction h2 generalizing us₁ with
  | nil =>
    cases us₁ with
    | nil => exact .nil
    | cons _ _ => exact False.elim (h1 fun _ => 0)
  | cons hr _ ih =>
    cases us₁ with
    | nil => exact False.elim (h1 fun _ => 0)
    | cons u₁ us₁' =>
      exact .cons (fun φ => (h1 φ).1.trans (hr φ)) (ih fun φ => (h1 φ).2)

private theorem forall2_eval_trans_right {us vs₁ vs₂ : List KLevel}
    (h1 : Ix.Kernel.Semantics.Forall₂ (fun u v => ∀ φ, u.eval φ = v.eval φ) us vs₁)
    (h2 : LvEqList vs₁ vs₂) :
    Ix.Kernel.Semantics.Forall₂ (fun u v => ∀ φ, u.eval φ = v.eval φ) us vs₂ := by
  induction h1 generalizing vs₂ with
  | nil =>
    cases vs₂ with
    | nil => exact .nil
    | cons _ _ => exact False.elim (h2 fun _ => 0)
  | cons hr _ ih =>
    cases vs₂ with
    | nil => exact False.elim (h2 fun _ => 0)
    | cons v₂ vs₂' =>
      exact .cons (fun φ => (hr φ).trans (h2 φ).1) (ih fun φ => (h2 φ).2)

/-- `WrapRel` respects `ExprLvEq` on the left. -/
theorem wrapRel_congr_exprLvEq_left {find? : KKey → Option (ConstantInfo .anon)} {g g₁ d : KExpr}
    (h : ExprLvEq g₁ g) (hw : WrapRel find? g d) : WrapRel find? g₁ d := by
  refine WrapRel.rec
    (motive_1 := fun g d _ => ∀ {g₁ : KExpr}, ExprLvEq g₁ g → WrapRel find? g₁ d)
    (motive_2 := fun t d _ => ∀ {t₁ : KExpr}, ExprLvEq t₁ t → WrapDom find? t₁ d)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hw h
  · intro i g₁ hg; cases hg; exact .bvar i
  · intro i t t' _ ih g₁ hg; cases hg with | fvar ht => exact .fvar (ih ht)
  · intro u v huv g₁ hg; cases hg with | sort hu => exact .sort (fun φ => (hu φ).trans (huv φ))
  · intro n us vs hlv g₁ hg; cases hg with | const hu => exact .const (forall2_eval_trans_left hu hlv)
  · intro l g₁ hg; cases hg; exact .lit l
  · intro f a f' a' _ _ ihf iha g₁ hg; cases hg with | app hf ha => exact .app (ihf hf) (iha ha)
  · intro t b t' b' m m' hpw _ _ iht ihb g₁ hg
    cases hg with | lam ht hb => exact .lam hpw (iht ht) (ihb hb)
  · intro t b t' b' m m' hpw _ _ iht ihb g₁ hg
    cases hg with | forallE ht hb => exact .forallE hpw (iht ht) (ihb hb)
  · intro t v b t' v' b' l l' _ _ _ iht ihv ihb g₁ hg
    cases hg with | letE ht hv hb => exact .letE (iht ht) (ihv hv) (ihb hb)
  · intro s i e e' _ ihe g₁ hg; cases hg with | proj he => exact .proj (ihe he)
  · intro g t v b l _ ih g₁ hg; exact .zeta (ih hg)
  · intro t t' _ ih t₁ ht; exact .keep (ih ht)
  · intro t a t' hc _ ih t₁ ht
    obtain ⟨a₁, hc₁, ha⟩ := consumeWrapper_congr ht hc
    exact .consume hc₁ (ih ha)

private theorem exprLvEq_liftLooseBVars_wb {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    ∀ (n c : Nat), ExprLvEq (e₁.liftLooseBVars n c) (e₂.liftLooseBVars n c) := by
  induction h with
  | bvar => intro n c; simp only [Expr.liftLooseBVars]; split <;> exact .bvar
  | fvar ht _ => intro _ _; exact .fvar ht
  | sort hu => intro _ _; exact .sort hu
  | const hus => intro _ _; exact .const hus
  | lit => intro _ _; exact .lit
  | app _ _ ihf iha => intro n c; exact .app (ihf n c) (iha n c)
  | lam _ _ iht ihb => intro n c; exact .lam (iht n c) (ihb n (c + 1))
  | forallE _ _ iht ihb => intro n c; exact .forallE (iht n c) (ihb n (c + 1))
  | letE _ _ _ iht ihv ihb => intro n c; exact .letE (iht n c) (ihv n c) (ihb n (c + 1))
  | proj _ ihe => intro n c; exact .proj (ihe n c)

private theorem exprLvEq_instantiate1Lift_wb {b₁ b₂ v₁ v₂ : KExpr}
    (hb : ExprLvEq b₁ b₂) (hv : ExprLvEq v₁ v₂) :
    ∀ (d : Nat), ExprLvEq (b₁.instantiate1Lift v₁ d) (b₂.instantiate1Lift v₂ d) := by
  induction hb with
  | @bvar i =>
    intro d
    simp only [Expr.instantiate1Lift]
    split
    · exact exprLvEq_liftLooseBVars_wb hv d 0
    · split <;> exact .bvar
  | fvar ht _ => intro _; exact .fvar ht
  | sort hu => intro _; exact .sort hu
  | const hus => intro _; exact .const hus
  | lit => intro _; exact .lit
  | app _ _ ihf iha => intro d; exact .app (ihf d) (iha d)
  | lam _ _ iht ihb => intro d; exact .lam (iht d) (ihb (d + 1))
  | forallE _ _ iht ihb => intro d; exact .forallE (iht d) (ihb (d + 1))
  | letE _ _ _ iht ihv ihb => intro d; exact .letE (iht d) (ihv d) (ihb (d + 1))
  | proj _ ihe => intro d; exact .proj (ihe d)

/-- `WrapDom` respects `ExprLvEq` on the left. -/
theorem wrapDom_congr_exprLvEq_left {find? : KKey → Option (ConstantInfo .anon)} {t t₁ d : KExpr}
    (h : ExprLvEq t₁ t) (hw : WrapDom find? t d) : WrapDom find? t₁ d :=
  WrapDom.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun t d _ => ∀ {t₁ : KExpr}, ExprLvEq t₁ t → WrapDom find? t₁ d)
    (bvar := fun _ => trivial) (fvar := fun _ _ => trivial) (sort := fun _ => trivial)
    (const := fun _ => trivial) (lit := fun _ => trivial) (app := fun _ _ _ _ => trivial)
    (lam := fun _ _ _ _ _ => trivial) (forallE := fun _ _ _ _ _ => trivial)
    (letE := fun _ _ _ _ _ _ => trivial) (proj := fun _ _ => trivial) (zeta := fun _ _ => trivial)
    (keep := fun hr _ _ ht => .keep (wrapRel_congr_exprLvEq_left ht hr))
    (consume := fun hc _ ih _ ht => by
      obtain ⟨a₁, hc₁, ha⟩ := consumeWrapper_congr ht hc
      exact .consume hc₁ (ih ha))
    hw h

/-- `WrapRel` respects `ExprLvEq` on the right. -/
theorem wrapRel_congr_exprLvEq_right {find? : KKey → Option (ConstantInfo .anon)} {g d d₁ : KExpr}
    (hw : WrapRel find? g d) (h : ExprLvEq d d₁) : WrapRel find? g d₁ := by
  refine WrapRel.rec
    (motive_1 := fun g d _ => ∀ {d₁ : KExpr}, ExprLvEq d d₁ → WrapRel find? g d₁)
    (motive_2 := fun t d _ => ∀ {d₁ : KExpr}, ExprLvEq d d₁ → WrapDom find? t d₁)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hw h
  · intro i d₁ hd; cases hd; exact .bvar i
  · intro i t t' _ ih d₁ hd; cases hd with | fvar ht => exact .fvar (ih ht)
  · intro u v huv d₁ hd; cases hd with | sort hv => exact .sort (fun φ => (huv φ).trans (hv φ))
  · intro n us vs hlv d₁ hd; cases hd with | const hv => exact .const (forall2_eval_trans_right hlv hv)
  · intro l d₁ hd; cases hd; exact .lit l
  · intro f a f' a' _ _ ihf iha d₁ hd; cases hd with | app hf ha => exact .app (ihf hf) (iha ha)
  · intro t b t' b' m m' hpw _ _ iht ihb d₁ hd
    cases hd with | lam ht hb => exact .lam hpw (iht ht) (ihb hb)
  · intro t b t' b' m m' hpw _ _ iht ihb d₁ hd
    cases hd with | forallE ht hb => exact .forallE hpw (iht ht) (ihb hb)
  · intro t v b t' v' b' l l' _ _ _ iht ihv ihb d₁ hd
    cases hd with | letE ht hv hb => exact .letE (iht ht) (ihv hv) (ihb hb)
  · intro s i e e' _ ihe d₁ hd; cases hd with | proj he => exact .proj (ihe he)
  · intro g t v b l _ ih d₁ hd
    cases hd with
    | letE _ hv hb => exact .zeta (ih (exprLvEq_instantiate1Lift_wb hb hv 0))
  · intro t t' _ ih d₁ hd; exact .keep (ih hd)
  · intro t a t' hc _ ih d₁ hd; exact .consume hc (ih hd)

/-- `WrapDom` respects `ExprLvEq` on the right. -/
theorem wrapDom_congr_exprLvEq_right {find? : KKey → Option (ConstantInfo .anon)} {t d d₁ : KExpr}
    (hw : WrapDom find? t d) (h : ExprLvEq d d₁) : WrapDom find? t d₁ :=
  WrapDom.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun t d _ => ∀ {d₁ : KExpr}, ExprLvEq d d₁ → WrapDom find? t d₁)
    (bvar := fun _ => trivial) (fvar := fun _ _ => trivial) (sort := fun _ => trivial)
    (const := fun _ => trivial) (lit := fun _ => trivial) (app := fun _ _ _ _ => trivial)
    (lam := fun _ _ _ _ _ => trivial) (forallE := fun _ _ _ _ _ => trivial)
    (letE := fun _ _ _ _ _ _ => trivial) (proj := fun _ _ => trivial) (zeta := fun _ _ => trivial)
    (keep := fun hr _ _ hd => .keep (wrapRel_congr_exprLvEq_right hr hd))
    (consume := fun hc _ ih _ hd => .consume hc (ih hd))
    hw h

/-! ### Level-parameter instantiation and lifting -/

private theorem level_eval_subst_congr (ps : List LevelParam) (us : List KLevel) {u v : KLevel}
    (h : ∀ φ, u.eval φ = v.eval φ) :
    ∀ φ, (Level.subst ps us u).eval φ = (Level.subst ps us v).eval φ := by
  intro φ
  rw [Ix.Kernel.Level.eval_subst, Ix.Kernel.Level.eval_subst]
  exact h _

private theorem forall2_eval_subst (ps : List LevelParam) (ls : List KLevel) :
    ∀ {us vs : List KLevel},
      Ix.Kernel.Semantics.Forall₂ (fun u v => ∀ φ, u.eval φ = v.eval φ) us vs →
      Ix.Kernel.Semantics.Forall₂ (fun u v => ∀ φ, u.eval φ = v.eval φ)
        (us.map (Level.subst ps ls)) (vs.map (Level.subst ps ls))
  | _, _, .nil => .nil
  | _, _, .cons h hr => .cons (level_eval_subst_congr ps ls h) (forall2_eval_subst ps ls hr)

private theorem consumeWrapper_instantiateLevelParams {find? : KKey → Option (ConstantInfo .anon)}
    (ps : List LevelParam) (us : List KLevel) {t a : KExpr}
    (hc : consumeWrapper find? t = some a) :
    consumeWrapper find? (t.instantiateLevelParams ps us) =
      some (a.instantiateLevelParams ps us) := by
  obtain ⟨w, ls, rest, rfl, hw⟩ := Ix.Kernel.Semantics.consumeWrapper_inv hc
  rw [mkAppN_instantiateLevelParams_wb]
  simp only [Expr.instantiateLevelParams, List.map_cons]
  exact Ix.Kernel.Semantics.consumeWrapper_mkAppN (by rw [List.length_map]; exact hw)

/-- `WrapRel` commutes with `Expr.instantiateLevelParams`. -/
theorem wrapRel_instantiateLevelParams {find? : KKey → Option (ConstantInfo .anon)}
    (ps : List LevelParam) (us : List KLevel) {g d : KExpr}
    (hw : WrapRel find? g d) :
    WrapRel find? (g.instantiateLevelParams ps us) (d.instantiateLevelParams ps us) :=
  WrapRel.rec
    (motive_1 := fun g d _ =>
      WrapRel find? (g.instantiateLevelParams ps us) (d.instantiateLevelParams ps us))
    (motive_2 := fun t d _ =>
      WrapDom find? (t.instantiateLevelParams ps us) (d.instantiateLevelParams ps us))
    (bvar := fun i => .bvar i)
    (fvar := fun _ iht => .fvar iht)
    (sort := fun huv => .sort (level_eval_subst_congr ps us huv))
    (const := fun hlv => .const (forall2_eval_subst ps us hlv))
    (lit := fun l => .lit l)
    (app := fun _ _ ihf iha => .app ihf iha)
    (lam := fun hpw _ _ iht ihb =>
      .lam (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw]) iht ihb)
    (forallE := fun hpw _ _ iht ihb =>
      .forallE (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw]) iht ihb)
    (letE := fun _ _ _ iht ihv ihb => .letE iht ihv ihb)
    (proj := fun _ ihe => .proj ihe)
    (zeta := fun _ ihz => by
      rw [Core.ProjBody.instantiate1Lift_instantiateLevelParams] at ihz
      exact .zeta ihz)
    (keep := fun _ ih => .keep ih)
    (consume := fun hc _ ih => .consume (consumeWrapper_instantiateLevelParams ps us hc) ih)
    hw

/-- Move `WrapRel` from positional level parameters (`posOf ps`) back to `ps`. -/
theorem wrapRel_of_posOf_perm {find? : KKey → Option (ConstantInfo .anon)}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) {g d : KExpr}
    (h : WrapRel find? (Core.posOf ps g) (Core.posOf ps d)) :
    WrapRel find? g d := by
  have h' := wrapRel_instantiateLevelParams (List.range ps.length) (ps.map .param) h
  rwa [Decl.posOf_perm_inv hperm g, Decl.posOf_perm_inv hperm d] at h'

private theorem consumeWrapper_liftLooseBVars {find? : KKey → Option (ConstantInfo .anon)}
    (n c : Nat) {t a : KExpr} (hc : consumeWrapper find? t = some a) :
    consumeWrapper find? (t.liftLooseBVars n c) = some (a.liftLooseBVars n c) := by
  obtain ⟨w, ls, rest, rfl, hw⟩ := Ix.Kernel.Semantics.consumeWrapper_inv hc
  rw [mkAppN_liftLooseBVars_wb]
  simp only [Expr.liftLooseBVars, List.map_cons]
  exact Ix.Kernel.Semantics.consumeWrapper_mkAppN (by rw [List.length_map]; exact hw)

/-- `WrapRel` commutes with `Expr.liftLooseBVars` on `letFree` right sides. -/
theorem wrapRel_liftLooseBVars {find? : KKey → Option (ConstantInfo .anon)}
    {g d : KExpr} (hw : WrapRel find? g d) (hd : letFree d = true) (n c : Nat) :
    WrapRel find? (g.liftLooseBVars n c) (d.liftLooseBVars n c) := by
  refine WrapRel.rec
    (motive_1 := fun g d _ => letFree d = true →
      ∀ n c, WrapRel find? (g.liftLooseBVars n c) (d.liftLooseBVars n c))
    (motive_2 := fun t d _ => letFree d = true →
      ∀ n c, WrapDom find? (t.liftLooseBVars n c) (d.liftLooseBVars n c))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hw hd n c
  · intro i _ n c; simp only [Expr.liftLooseBVars]; split <;> exact .bvar _
  · intro i t t' ht _ _ _ _; exact .fvar ht
  · intro u v huv _ _ _; exact .sort huv
  · intro k ls₁ ls₂ hlv _ _ _; exact .const hlv
  · intro l _ _ _; exact .lit l
  · intro f a f' a' _ _ ihf iha hlf n c
    simp only [letFree, Bool.and_eq_true] at hlf
    exact .app (ihf hlf.1 n c) (iha hlf.2 n c)
  · intro t b t' b' m m' hpw _ _ iht ihb hlf n c
    simp only [letFree, Bool.and_eq_true] at hlf
    exact .lam hpw (iht hlf.1 n c) (ihb hlf.2 n (c + 1))
  · intro t b t' b' m m' hpw _ _ iht ihb hlf n c
    simp only [letFree, Bool.and_eq_true] at hlf
    exact .forallE hpw (iht hlf.1 n c) (ihb hlf.2 n (c + 1))
  · intro t v b t' v' b' l l' _ _ _ _ _ _ hlf _ _; simp [letFree] at hlf
  · intro s i e e' _ ihe hlf n c; simp only [letFree] at hlf; exact .proj (ihe hlf n c)
  · intro g t v b l _ _ hlf _ _; simp [letFree] at hlf
  · intro t t' _ ih hlf n c; exact .keep (ih hlf n c)
  · intro t a t' hc _ ih hlf n c
    exact .consume (consumeWrapper_liftLooseBVars n c hc) (ih hlf n c)

/-- `WrapDom` commutes with `Expr.liftLooseBVars` on `letFree` right sides. -/
theorem wrapDom_liftLooseBVars {find? : KKey → Option (ConstantInfo .anon)}
    {t d : KExpr} (hw : WrapDom find? t d) (hd : letFree d = true) (n c : Nat) :
    WrapDom find? (t.liftLooseBVars n c) (d.liftLooseBVars n c) :=
  WrapDom.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun t d _ => letFree d = true →
      ∀ n c, WrapDom find? (t.liftLooseBVars n c) (d.liftLooseBVars n c))
    (bvar := fun _ => trivial) (fvar := fun _ _ => trivial) (sort := fun _ => trivial)
    (const := fun _ => trivial) (lit := fun _ => trivial) (app := fun _ _ _ _ => trivial)
    (lam := fun _ _ _ _ _ => trivial) (forallE := fun _ _ _ _ _ => trivial)
    (letE := fun _ _ _ _ _ _ => trivial) (proj := fun _ _ => trivial) (zeta := fun _ _ => trivial)
    (keep := fun hr _ hlf n c => .keep (wrapRel_liftLooseBVars hr hlf n c))
    (consume := fun hc _ ih hlf n c => .consume (consumeWrapper_liftLooseBVars n c hc) (ih hlf n c))
    hw hd n c

/-- A `∀`-headed term cannot be consumed as a wrapper, so `WrapDom` on it is `WrapRel`. -/
theorem wrapDom_toWrapRel_of_forallE {find? : KKey → Option (ConstantInfo .anon)}
    {d b t' : KExpr} {m : Ix.Kernel.BinderMeta}
    (h : WrapDom find? (.forallE d b m) t') : WrapRel find? (.forallE d b m) t' := by
  cases h with
  | keep hr => exact hr
  | consume hc _ =>
    simp [consumeWrapper, Expr.getAppFn] at hc

/-- Peeling `n` leading `∀` binders preserves `WrapRel` on `letFree` right sides. -/
theorem wrapRel_peelForalls {find? : KKey → Option (ConstantInfo .anon)} :
    ∀ (n : Nat) {g d g' d' : KExpr}, WrapRel find? g d → letFree d = true →
      peelForalls n g = some g' → peelForalls n d = some d' →
      WrapRel find? g' d' ∧ letFree d' = true
  | 0, _, _, _, _, hw, hlf, hg, hd => by
    simp only [peelForalls, Option.some.injEq] at hg hd
    subst hg hd
    exact ⟨hw, hlf⟩
  | n + 1, g, d, g', d', hw, hlf, hg, hd => by
    cases g <;> simp [peelForalls] at hg
    cases d <;> simp [peelForalls] at hd
    cases hw with
    | forallE _ _ hb =>
      simp only [letFree, Bool.and_eq_true] at hlf
      exact wrapRel_peelForalls n hb hlf.2 hg hd

/-! ## `RuleFollows` and `LamsAlong` into `WrapRel` -/

/-- Renaming constants that a term does not mention leaves it unchanged. -/
theorem renameConsts_eq_self_of_not_mentions {f : KKey → KKey} :
    ∀ (e : KExpr), (∀ k, f k ≠ k → e.mentionsConst k = false) → e.renameConsts f = e
  | .bvar _, _ | .sort _, _ | .lit _, _ => rfl
  | .fvar i t, h => by
    simp only [Expr.renameConsts]
    congr 1
    exact renameConsts_eq_self_of_not_mentions t fun k hk => by
      simpa [Expr.mentionsConst] using h k hk
  | .const n us, h => by
    simp only [Expr.renameConsts]
    by_cases hn : f n = n
    · rw [hn]
    · have := h n hn
      simp [Expr.mentionsConst] at this
  | .app g a, h => by
    simp only [Expr.renameConsts]
    congr 1
    · exact renameConsts_eq_self_of_not_mentions g fun k hk =>
        (Bool.or_eq_false_iff.mp (h k hk)).1
    · exact renameConsts_eq_self_of_not_mentions a fun k hk =>
        (Bool.or_eq_false_iff.mp (h k hk)).2
  | .lam t b m, h => by
    simp only [Expr.renameConsts]
    congr 1
    · exact renameConsts_eq_self_of_not_mentions t fun k hk =>
        (Bool.or_eq_false_iff.mp (h k hk)).1
    · exact renameConsts_eq_self_of_not_mentions b fun k hk =>
        (Bool.or_eq_false_iff.mp (h k hk)).2
  | .forallE t b m, h => by
    simp only [Expr.renameConsts]
    congr 1
    · exact renameConsts_eq_self_of_not_mentions t fun k hk =>
        (Bool.or_eq_false_iff.mp (h k hk)).1
    · exact renameConsts_eq_self_of_not_mentions b fun k hk =>
        (Bool.or_eq_false_iff.mp (h k hk)).2
  | .letE t v b l, h => by
    simp only [Expr.renameConsts]
    congr 1
    · exact renameConsts_eq_self_of_not_mentions t fun k hk =>
        (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp (h k hk)).1).1
    · exact renameConsts_eq_self_of_not_mentions v fun k hk =>
        (Bool.or_eq_false_iff.mp (Bool.or_eq_false_iff.mp (h k hk)).1).2
    · exact renameConsts_eq_self_of_not_mentions b fun k hk =>
        (Bool.or_eq_false_iff.mp (h k hk)).2
  | .proj s i e, h => by
    simp only [Expr.renameConsts]
    congr 1
    exact renameConsts_eq_self_of_not_mentions e fun k hk =>
      (Bool.or_eq_false_iff.mp (h k hk)).2

theorem exprLvEq_renameConsts (f : KKey → KKey) {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    ExprLvEq (e₁.renameConsts f) (e₂.renameConsts f) := by
  induction h with
  | bvar => exact .bvar
  | fvar _ ih => exact .fvar ih
  | sort hu => exact .sort hu
  | const hus => exact .const hus
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iht ihb => exact .lam iht ihb
  | forallE _ _ iht ihb => exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb => exact .letE iht ihv ihb
  | lit => exact .lit
  | proj _ ih => exact .proj ih

theorem lamsAlong_renameConsts (f : KKey → KKey) {elim : KLevel} {n : Nat} {l p r : KExpr}
    (h : LamsAlong elim n l p r) :
    LamsAlong elim n (l.renameConsts f) (p.renameConsts f) (r.renameConsts f) := by
  induction h with
  | zero => exact .zero
  | succ hpw hdom _ ih => exact .succ hpw (exprLvEq_renameConsts f hdom) ih

/-- Two λ-prefixes along `WrapRel`-related `∀`-telescopes whose bodies are `WrapRel`-related are
themselves `WrapRel`-related. -/
theorem wrapRel_of_lamsAlong {find? : KKey → Option (ConstantInfo .anon)} {elim : KLevel} :
    ∀ {n : Nat} {lC lW pC pW rC rW : KExpr},
      WrapRel find? pC pW → letFree pW = true →
      LamsAlong elim n lC pC rC → LamsAlong elim n lW pW rW →
      WrapRel find? rC rW → WrapRel find? lC lW
  | 0, _, _, _, _, _, _, _, _, hC, hW, hr => by
    cases hC; cases hW; exact hr
  | n + 1, _, _, _, _, _, _, hw, hlf, hC, hW, hr => by
    cases hC with
    | succ hpwC hdomC hC' =>
      cases hW with
      | succ hpwW hdomW hW' =>
        cases hw with
        | forallE _ hdomP hbP =>
          simp only [letFree, Bool.and_eq_true] at hlf
          have hdom : WrapDom find? _ _ :=
            wrapDom_congr_exprLvEq_right (wrapDom_congr_exprLvEq_left hdomC hdomP) hdomW.symm
          exact .lam (hpwC.trans hpwW.symm) hdom
            (wrapRel_of_lamsAlong hbP hlf.2 hC' hW' hr)

private theorem peelForalls_renameConsts (f : KKey → KKey) :
    ∀ (n : Nat) {e r : KExpr}, peelForalls n e = some r →
      peelForalls n (e.renameConsts f) = some (r.renameConsts f)
  | 0, _, _, h => by simp only [peelForalls, Option.some.injEq] at h ⊢; rw [h]
  | n + 1, .forallE _ _ _, _, h => peelForalls_renameConsts f n h
  | n + 1, .bvar _, _, h => by simp [peelForalls] at h
  | n + 1, .fvar _ _, _, h => by simp [peelForalls] at h
  | n + 1, .sort _, _, h => by simp [peelForalls] at h
  | n + 1, .const _ _, _, h => by simp [peelForalls] at h
  | n + 1, .app _ _, _, h => by simp [peelForalls] at h
  | n + 1, .lam _ _ _, _, h => by simp [peelForalls] at h
  | n + 1, .letE _ _ _ _, _, h => by simp [peelForalls] at h
  | n + 1, .lit _, _, h => by simp [peelForalls] at h
  | n + 1, .proj _ _ _, _, h => by simp [peelForalls] at h

/-- **Rule comparison from `RuleFollows`**: if `tyC` is above `tyW` by `WrapRel`, `tyC` is fixed by
`f`, `rhsC` and `rhsW` follow `cbC` and `cbW` along `tyC` and `tyW`, and `cbC.renameConsts f` is
`ExprLvEq` to `cbW`, then `rhsC.renameConsts f` is above `rhsW` by `WrapRel`. -/
theorem wrapRel_rule_of_ruleFollows {find? : KKey → Option (ConstantInfo .anon)}
    {f : KKey → KKey} {tyC tyW rhsC rhsW cbC cbW : KExpr}
    {nP nMot nMin minor nf : Nat} {elim : KLevel}
    (hty : WrapRel find? tyC tyW) (hlfW : letFree tyW = true)
    (hty_fix : tyC.renameConsts f = tyC)
    (hC : RuleFollows tyC nP nMot nMin minor nf elim rhsC cbC)
    (hW : RuleFollows tyW nP nMot nMin minor nf elim rhsW cbW)
    (hcb : ExprLvEq (cbC.renameConsts f) cbW) :
    WrapRel find? (rhsC.renameConsts f) rhsW := by
  obtain ⟨afterC, mdomC, restC, sbC, mmC, hlam1C, hpeelC, hlam2C, hsbC⟩ := hC
  obtain ⟨afterW, mdomW, restW, sbW, mmW, hlam1W, hpeelW, hlam2W, hsbW⟩ := hW
  have hlam1C' : LamsAlong elim (nP + nMot + nMin) (rhsC.renameConsts f) tyC
      (afterC.renameConsts f) := by
    have h := lamsAlong_renameConsts f hlam1C
    rwa [hty_fix] at h
  have hpeelC' : peelForalls (nP + nMot + minor) tyC =
      some (.forallE (mdomC.renameConsts f) (restC.renameConsts f) mmC) := by
    have h := peelForalls_renameConsts f (nP + nMot + minor) hpeelC
    rwa [hty_fix] at h
  have hmdom_fix : mdomC.renameConsts f = mdomC := by
    have h := Option.some.inj (hpeelC'.symm.trans hpeelC)
    injection h
  have hlam2C' : LamsAlong elim nf (afterC.renameConsts f)
      (mdomC.liftLooseBVars (nMin - minor) 0) (sbC.renameConsts f) := by
    have h := lamsAlong_renameConsts f hlam2C
    rw [renameConsts_liftLooseBVars_wb, hmdom_fix] at h
    exact h
  have hsb : WrapRel find? (sbC.renameConsts f) sbW :=
    Binding.FamilyRecon.exprLvEq_wrapRel find?
      (((exprLvEq_renameConsts f hsbC).trans hcb).trans hsbW.symm)
  have hafter : WrapRel find? (afterC.renameConsts f) afterW := by
    cases nf with
    | zero =>
      cases hlam2C; cases hlam2W; exact hsb
    | succ nf' =>
      obtain ⟨hpeel_w, hlf_peel⟩ := wrapRel_peelForalls (nP + nMot + minor) hty hlfW hpeelC hpeelW
      cases hpeel_w with
      | forallE _ hdomM _ =>
        simp only [letFree, Bool.and_eq_true] at hlf_peel
        have hdomM_lift : WrapDom find? (mdomC.liftLooseBVars (nMin - minor) 0)
            (mdomW.liftLooseBVars (nMin - minor) 0) :=
          wrapDom_liftLooseBVars hdomM hlf_peel.1 (nMin - minor) 0
        have hdomM_fa : ∃ d b m, mdomC.liftLooseBVars (nMin - minor) 0 = .forallE d b m := by
          generalize hm : mdomC.liftLooseBVars (nMin - minor) 0 = mL at hlam2C
          cases hlam2C
          exact ⟨_, _, _, rfl⟩
        obtain ⟨d, b, m, hm⟩ := hdomM_fa
        rw [hm] at hdomM_lift hlam2C'
        have hrelM := wrapDom_toWrapRel_of_forallE hdomM_lift
        have hlf_lift : letFree (mdomW.liftLooseBVars (nMin - minor) 0) = true :=
          Decl.letFree_liftLooseBVars (nMin - minor) 0 hlf_peel.1
        exact wrapRel_of_lamsAlong hrelM hlf_lift hlam2C' hlam2W hsb
  exact wrapRel_of_lamsAlong hty hlfW hlam1C' hlam1W hafter

/-! ## Reconstructed rule bodies under peer renaming -/

private theorem appSpine_renameConsts (f : KKey → KKey) (args : List KExpr) (hd : KExpr) :
    (appSpine hd args).renameConsts f =
      appSpine (hd.renameConsts f) (args.map (Expr.renameConsts f)) := by
  induction args generalizing hd with
  | nil => rfl
  | cons a as ih =>
    simp only [appSpine, List.foldl_cons, List.map_cons]
    exact ih (.app hd a)

private theorem appBVarsDec_renameConsts (f : KKey → KKey) (hd : KExpr) (n start : Nat) :
    (appBVarsDec hd n start).renameConsts f = appBVarsDec (hd.renameConsts f) n start := by
  unfold appBVarsDec
  rw [appSpine_renameConsts, List.map_map]
  rfl

private theorem appBVarsDown_renameConsts (f : KKey → KKey) (hd : KExpr) (n : Nat) :
    (appBVarsDown hd n).renameConsts f = appBVarsDown (hd.renameConsts f) n := by
  unfold appBVarsDown
  rw [appSpine_renameConsts, List.map_map]
  rfl

private theorem fieldBVars_renameConsts (f : KKey → KKey) (hd : KExpr) (nf nb : Nat) :
    (fieldBVars hd nf nb).renameConsts f = fieldBVars (hd.renameConsts f) nf nb := by
  unfold fieldBVars
  rw [appSpine_renameConsts, List.map_map]
  rfl

private theorem map_id_of_mem_wb {α : Type} {f : α → α} :
    ∀ {l : List α}, (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.map_cons, h a List.mem_cons_self,
      map_id_of_mem_wb fun x hx => h x (List.mem_cons_of_mem _ hx)]

private theorem mem_of_mem_zipIdx_wb {α : Type} {x : α} {i : Nat} :
    ∀ {l : List α} {s : Nat}, (x, i) ∈ l.zipIdx s → x ∈ l
  | [], _, h => nomatch h
  | a :: l, s, h => by
    rcases List.mem_cons.mp h with he | h'
    · injection he with hx _
      subst hx
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_zipIdx_wb h')

private theorem wrapLams_renameConsts (f : KKey → KKey) (body : KExpr) (doms : List KExpr)
    (elim : KLevel) :
    (wrapLams body doms elim).renameConsts f =
      wrapLams (body.renameConsts f) (doms.map (Expr.renameConsts f)) elim := by
  induction doms with
  | nil => rfl
  | cons d ds ih =>
    show Expr.lam (d.renameConsts f) ((wrapLams body ds elim).renameConsts f) (Core.bmeta elim) =
      Expr.lam (d.renameConsts f) (wrapLams (body.renameConsts f) (ds.map (Expr.renameConsts f)) elim)
        (Core.bmeta elim)
    rw [ih]

private theorem applyIhs_renameConsts {V : ReconView} {f : KKey → KKey}
    {rm : List Nat} {norm : List KExpr} {peersC peersW : List _root_.Address}
    {fop : List Nat} {nP nMot nMin nFields : Nat} {recLvls : List KLevel} {elim : KLevel}
    (hpeers : ∀ (j : Nat) aC, peersC[j]? = some aC →
      ∃ aW, peersW[j]? = some aW ∧ f (V.key aC) = V.key aW) :
    ∀ (k : Nat) (ri : List Nat) (headC headW resC : KExpr),
      headC.renameConsts f = headW →
      (∀ (j : Nat) (fieldIdx : Nat) (dom : KExpr),
        ri[j]? = some fieldIdx → norm[fieldIdx]? = some dom →
        let memIdx := (rm[k + j]?).getD 0
        let tnp := (fop[memIdx]?).getD 0
        let domL := (dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields
        (∀ d ∈ (peelAll domL).1, d.renameConsts f = d) ∧
        (∀ a ∈ ((peelAll domL).2.getAppArgs).drop tnp, a.renameConsts f = a)) →
      applyIhs V rm norm peersC fop nP nMot nMin nFields recLvls elim headC k ri = some resC →
      applyIhs V rm norm peersW fop nP nMot nMin nFields recLvls elim headW k ri =
        some (resC.renameConsts f) := by
  intro k ri
  induction ri generalizing k with
  | nil =>
    intro headC headW resC hhd _ h
    simp only [applyIhs, Option.some.injEq] at h ⊢
    subst h
    exact hhd.symm
  | cons fieldIdx rest ih =>
    intro headC headW resC hhd hfix h
    simp only [applyIhs] at h ⊢
    cases hpC : peersC[(rm[k]?).getD 0]? with
    | none => simp [hpC] at h
    | some targetC =>
      cases hdom : norm[fieldIdx]? with
      | none => simp [hpC, hdom] at h
      | some dom =>
        simp only [hpC, hdom] at h
        obtain ⟨targetW, hpW, hkey⟩ := hpeers _ targetC hpC
        simp only [hpW, hdom]
        obtain ⟨hfds_fix, hidx_fix⟩ := hfix 0 fieldIdx dom rfl hdom
        have hstep_hd :
            (Expr.app headC (wrapLams
              (.app (appSpine (appBVarsDec (appBVarsDec (appBVarsDec
                (.const (V.key targetC) recLvls) nP
                (nP + nMot + nMin + nFields + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length - 1))
                nMot (nP + nMot + nMin + nFields + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length - 1 - nP))
                nMin (nP + nMot + nMin + nFields + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length - 1 - nP - nMot))
                (((peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).2.getAppArgs).drop ((fop[(rm[k]?).getD 0]?).getD 0)))
                (appBVarsDown (.bvar (nFields - 1 - fieldIdx + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length))
                  (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length))
              (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1 elim)).renameConsts f =
            Expr.app headW (wrapLams
              (.app (appSpine (appBVarsDec (appBVarsDec (appBVarsDec
                (.const (V.key targetW) recLvls) nP
                (nP + nMot + nMin + nFields + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length - 1))
                nMot (nP + nMot + nMin + nFields + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length - 1 - nP))
                nMin (nP + nMot + nMin + nFields + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length - 1 - nP - nMot))
                (((peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).2.getAppArgs).drop ((fop[(rm[k]?).getD 0]?).getD 0)))
                (appBVarsDown (.bvar (nFields - 1 - fieldIdx + (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length))
                  (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1.length))
              (peelAll ((dom.liftLooseBVars (nFields - fieldIdx) 0).liftLooseBVars (nMot + nMin) nFields)).1 elim) := by
          simp only [Expr.renameConsts, hhd, wrapLams_renameConsts, appSpine_renameConsts,
            appBVarsDec_renameConsts, appBVarsDown_renameConsts, hkey]
          congr 2
          · congr 1
            congr 1
            exact map_id_of_mem_wb (by simpa only [Nat.add_zero] using hidx_fix)
          · exact map_id_of_mem_wb hfds_fix
        exact ih (k + 1) _ _ resC hstep_hd (fun j fi d hj hd' => by
          have := hfix (j + 1) fi d hj hd'
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this) h

private theorem mentionsConst_wrapForalls_false {k : KKey} {body : KExpr} {doms : List KExpr}
    {elim : KLevel} (h : (wrapForalls body doms elim).mentionsConst k = false) :
    body.mentionsConst k = false ∧ ∀ d ∈ doms, d.mentionsConst k = false := by
  induction doms with
  | nil => exact ⟨h, fun _ hm => nomatch hm⟩
  | cons d ds ih =>
    simp only [wrapForalls, List.foldr_cons, Expr.mentionsConst, Bool.or_eq_false_iff] at h
    obtain ⟨hb, hds⟩ := ih h.2
    exact ⟨hb, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact hds x hx'⟩

private theorem mentionsConst_appSpine_false {k : KKey} {hd : KExpr} {args : List KExpr}
    (h : (appSpine hd args).mentionsConst k = false) :
    hd.mentionsConst k = false ∧ ∀ a ∈ args, a.mentionsConst k = false := by
  induction args generalizing hd with
  | nil => exact ⟨h, fun _ hm => nomatch hm⟩
  | cons a as ih =>
    simp only [appSpine, List.foldl_cons] at h
    obtain ⟨hha, has⟩ := ih h
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hha
    exact ⟨hha.1, fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hha.2
      · exact has x hx'⟩

private theorem peelAll_liftLooseBVars :
    ∀ (e : KExpr) (n c : Nat),
      (peelAll (e.liftLooseBVars n c)).1 =
        (peelAll e).1.zipIdx.map (fun p => p.1.liftLooseBVars n (c + p.2)) ∧
      (peelAll (e.liftLooseBVars n c)).2 =
        (peelAll e).2.liftLooseBVars n (c + (peelAll e).1.length)
  | .forallE d b m, n, c => by
    simp only [Expr.liftLooseBVars, peelAll]
    obtain ⟨h1, h2⟩ := peelAll_liftLooseBVars b n (c + 1)
    refine ⟨?_, ?_⟩
    · rw [h1]
      simp only [List.zipIdx_cons, Nat.add_zero, List.map_cons, List.map_map]
      congr 1
      have hzip : ∀ (l : List KExpr) (s : Nat),
          (l.zipIdx (s + 1)).map (fun p => p.1.liftLooseBVars n (c + p.2)) =
          (l.zipIdx s).map (fun p => p.1.liftLooseBVars n (c + 1 + p.2)) := by
        intro l
        induction l with
        | nil => intro _; rfl
        | cons x xs ih =>
          intro s
          simp only [List.zipIdx_cons, List.map_cons]
          congr 1
          · congr 1; omega
          · exact ih (s + 1)
      exact (hzip (peelAll b).1 0).symm
    · rw [h2]; simp only [List.length_cons]; congr 1; omega
  | .bvar i, n, c => by
    simp only [Expr.liftLooseBVars]; split <;> simp [peelAll, Expr.liftLooseBVars, *]
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .app _ _, _, _
  | .lam _ _ _, _, _ | .letE _ _ _ _, _, _ | .lit _, _, _ | .proj _ _ _, _, _ => by
    simp [Expr.liftLooseBVars, peelAll]

private theorem mentionsConst_liftLooseBVars (k : KKey) :
    ∀ (e : KExpr) (n c : Nat), (e.liftLooseBVars n c).mentionsConst k = e.mentionsConst k
  | .bvar i, n, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ t, n, c => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst, mentionsConst_liftLooseBVars k t n c]
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst,
      mentionsConst_liftLooseBVars k f n c, mentionsConst_liftLooseBVars k a n c]
  | .lam t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst,
      mentionsConst_liftLooseBVars k t n c, mentionsConst_liftLooseBVars k b n (c + 1)]
  | .forallE t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst,
      mentionsConst_liftLooseBVars k t n c, mentionsConst_liftLooseBVars k b n (c + 1)]
  | .letE t v b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst,
      mentionsConst_liftLooseBVars k t n c, mentionsConst_liftLooseBVars k v n c,
      mentionsConst_liftLooseBVars k b n (c + 1)]
  | .proj _ _ e, n, c => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst, mentionsConst_liftLooseBVars k e n c]

private theorem getAppArgs_liftLooseBVars (n c : Nat) :
    ∀ (e : KExpr), (e.liftLooseBVars n c).getAppArgs = e.getAppArgs.map (Expr.liftLooseBVars n c)
  | .app f a => by
    simp only [Expr.liftLooseBVars, Expr.getAppArgs, List.map_append, List.map_singleton]
    rw [getAppArgs_liftLooseBVars n c f]
  | .bvar i => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _ | .forallE _ _ _
  | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

private theorem mentionsConst_ihDoms_false {k : KKey} {rm : List Nat} {norm : List KExpr}
    {fop : List Nat} {motiveBase nFields minorSaved : Nat} {elim : KLevel} :
    ∀ (j : Nat) (ri : List Nat) (ihs : List KExpr),
      ihDoms rm norm fop motiveBase nFields minorSaved elim j ri = some ihs →
      (∀ d ∈ ihs, d.mentionsConst k = false) →
      ∀ (m : Nat) (fieldIdx : Nat) (dom : KExpr),
        ri[m]? = some fieldIdx → norm[fieldIdx]? = some dom →
        let memIdx := (rm[j + m]?).getD 0
        let tnp := (fop[memIdx]?).getD 0
        (∀ d ∈ (peelAll dom).1, d.mentionsConst k = false) ∧
        (∀ a ∈ ((peelAll dom).2.getAppArgs).drop tnp, a.mentionsConst k = false) := by
  intro j ri
  induction ri generalizing j with
  | nil => intro _ _ _ m _ _ hm; simp at hm
  | cons fi rest ih =>
    intro ihs hihs hmc m fieldIdx dom hm hdom
    simp only [ihDoms] at hihs
    cases hd0 : norm[fi]? with
    | none => simp [hd0] at hihs
    | some dom0 =>
      simp only [hd0] at hihs
      cases hrest : ihDoms rm norm fop motiveBase nFields minorSaved elim (j + 1) rest with
      | none => simp [hrest] at hihs
      | some ihRest =>
        simp only [hrest, Option.map_some, Option.some.injEq] at hihs
        subst hihs
        cases m with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          have hdeq : dom0 = dom := Option.some.inj (hd0.symm.trans hdom)
          subst dom0
          have hfirst := hmc _ List.mem_cons_self
          obtain ⟨hbody, hfds⟩ := mentionsConst_wrapForalls_false hfirst
          simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hbody
          obtain ⟨-, hargs⟩ := mentionsConst_appSpine_false hbody.1
          obtain ⟨hp1, hp2⟩ := peelAll_liftLooseBVars dom (nFields - fi + j) 0
          constructor
          · intro d hd_mem
            obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hd_mem
            have hzip_mem : (d, idx) ∈ (peelAll dom).1.zipIdx := by
              rw [List.mem_iff_getElem?]
              exact ⟨idx, by simp [List.getElem?_zipIdx, hidx]⟩
            have hmem_l : d.liftLooseBVars (nFields - fi + j) (0 + idx) ∈
                (peelAll (dom.liftLooseBVars (nFields - fi + j) 0)).1 := by
              rw [hp1]
              exact List.mem_map.mpr ⟨(d, idx), hzip_mem, rfl⟩
            have := hfds _ hmem_l
            rwa [mentionsConst_liftLooseBVars] at this
          · intro a ha_mem
            have hmem_l : a.liftLooseBVars (nFields - fi + j) (0 + (peelAll dom).1.length) ∈
                ((peelAll (dom.liftLooseBVars (nFields - fi + j) 0)).2.getAppArgs).drop
                  ((fop[(rm[j + 0]?).getD 0]?).getD 0) := by
              rw [hp2, getAppArgs_liftLooseBVars, ← List.map_drop]
              exact List.mem_map.mpr ⟨a, ha_mem, rfl⟩
            have := hargs _ hmem_l
            rwa [mentionsConst_liftLooseBVars] at this
        | succ m' =>
          have hrec := ih (j + 1) ihRest hrest (fun d hd => hmc d (List.mem_cons_of_mem _ hd))
            m' fieldIdx dom hm hdom
          simpa [Nat.add_assoc, Nat.add_comm 1 m'] using hrec

private theorem peelCtorParams_eq_of_depth {V : ReconView} {f depth₁ depth₂ specLift : Nat}
    {aux : Bool} {sp : List KExpr} (h : aux = false → depth₁ = depth₂) :
    ∀ (m j : Nat) (ty : KExpr), (aux = true → j + m ≤ sp.length) →
      peelCtorParams V f depth₁ specLift aux sp m j ty =
      peelCtorParams V f depth₂ specLift aux sp m j ty := by
  intro m
  induction m with
  | zero => intro _ _ _; rfl
  | succ m ih =>
    intro j ty hsp
    simp only [peelCtorParams]
    cases binderOf V f ty with
    | none => rfl
    | some ob =>
      cases ob with
      | none => rfl
      | some p =>
        have hsub : Binding.FamilyRecon.ctorSubstParamFor j depth₁ specLift aux sp =
            Binding.FamilyRecon.ctorSubstParamFor j depth₂ specLift aux sp := by
          unfold Binding.FamilyRecon.ctorSubstParamFor
          cases aux with
          | false => rw [h rfl]
          | true =>
            have hjlt : j < sp.length := by have := hsp rfl; omega
            simp [List.getElem?_eq_getElem hjlt]
        rw [hsub]
        exact ih (j + 1) _ (fun ha => by have := hsp ha; omega)

private theorem minorDoms_get_mem {V : ReconView} {f : Nat} {es : List FlatEntry} {fop : List Nat}
    {aux : Bool} {sp : List KExpr} {us : List KLevel} {nrp nMot motiveBase selfMemIdx : Nat}
    {blk : _root_.Address} {idx : Nat} {elim : KLevel} :
    ∀ (cs : List Nat) (prev : Nat) (ms : List KExpr),
      minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim prev cs = some ms →
      ∀ (i c : Nat), cs[i]? = some c →
        ∃ cty np m, V.ctor blk idx c = some (cty, np) ∧
          minorAt V f es fop (V.key (V.ctorAddr blk idx c)) cty np aux sp us nrp nMot
            (prev + i) motiveBase selfMemIdx elim = some m ∧ m ∈ ms := by
  intro cs
  induction cs with
  | nil => intro _ _ _ _ _ hc; simp at hc
  | cons c0 cs' ih =>
    intro prev ms hms i c hi
    simp only [minorDoms] at hms
    cases hc0 : V.ctor blk idx c0 with
    | none => simp [hc0] at hms
    | some p =>
      obtain ⟨cty0, np0⟩ := p
      simp only [hc0] at hms
      cases hm0 : minorAt V f es fop (V.key (V.ctorAddr blk idx c0)) cty0 np0 aux sp us nrp nMot
          prev motiveBase selfMemIdx elim with
      | none => simp [hm0] at hms
      | some m0 =>
        simp only [hm0] at hms
        cases hrest : minorDoms V f es fop aux sp us nrp nMot motiveBase selfMemIdx blk idx elim
            (prev + 1) cs' with
        | none => simp [hrest] at hms
        | some ms' =>
          simp only [hrest, Option.map_some, Option.some.injEq] at hms
          subst hms
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
            subst hi
            exact ⟨cty0, np0, m0, hc0, by simpa using hm0, List.mem_cons_self⟩
          | succ i' =>
            obtain ⟨cty, np, m, hvc, hma, hmem⟩ := ih (prev + 1) ms' hrest i' c hi
            exact ⟨cty, np, m, hvc, by simpa [Nat.add_assoc, Nat.add_comm 1 i'] using hma,
              List.mem_cons_of_mem _ hmem⟩

private theorem allMinors_mem_at {V : ReconView} {f : Nat} {fullEs : List FlatEntry}
    {fop : List Nat} {nrp nMot motiveBase : Nat} {elim : KLevel} :
    ∀ (l : List FlatEntry) (prev pos : Nat) (allM : List KExpr),
      allMinors V f fullEs fop nrp nMot motiveBase elim l prev pos = some allM →
      ∀ (k : Nat) (e : FlatEntry), l[k]? = some e →
        ∃ (info : IndData) (prev' : Nat) (ms : List KExpr),
          V.ind e.addr = some (some info) ∧
          minorDoms V f fullEs fop e.aux e.params e.levels nrp nMot motiveBase (pos + k)
            info.blk info.idx elim prev' (List.range info.nctors) = some ms ∧
          ∀ m ∈ ms, m ∈ allM := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ _ hk; simp at hk
  | cons e0 rest ih =>
    intro prev pos allM hall k e hk
    simp only [allMinors] at hall
    cases hi0 : V.ind e0.addr with
    | none => simp [hi0] at hall
    | some opt0 =>
      cases opt0 with
      | none => simp [hi0] at hall
      | some info0 =>
        simp only [hi0] at hall
        cases hmd0 : minorDoms V f fullEs fop e0.aux e0.params e0.levels nrp nMot motiveBase pos
            info0.blk info0.idx elim prev (List.range info0.nctors) with
        | none => simp [hmd0] at hall
        | some ms0 =>
          simp only [hmd0] at hall
          cases hrest : allMinors V f fullEs fop nrp nMot motiveBase elim rest
              (prev + ms0.length) (pos + 1) with
          | none => simp [hrest] at hall
          | some msRest =>
            simp only [hrest, Option.map_some, Option.some.injEq] at hall
            subst hall
            cases k with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
              subst hk
              exact ⟨info0, prev, ms0, hi0, by simpa using hmd0,
                fun m hm => List.mem_append_left _ hm⟩
            | succ k' =>
              obtain ⟨info, prev', ms, hvi, hmd, hsub⟩ :=
                ih (prev + ms0.length) (pos + 1) msRest hrest k' e hk
              exact ⟨info, prev', ms, hvi, by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hmd,
                fun m hm => List.mem_append_right _ (hsub m hm)⟩

private theorem ruleBodies_renameConsts_of_fixed {V : ReconView} {f : KKey → KKey} {fuel : Nat}
    {es : List FlatEntry} {fop : List Nat} {peersC peersW : List _root_.Address}
    {nP nMot nMin : Nat} {us recLvls : List KLevel} {aux : Bool} {sp : List KExpr}
    {elim : KLevel} {blk : _root_.Address} {idx off : Nat}
    (hpeers : ∀ (j : Nat) aC, peersC[j]? = some aC →
      ∃ aW, peersW[j]? = some aW ∧ f (V.key aC) = V.key aW) :
    ∀ (cs : List Nat) (bsC : List KExpr),
      (∀ c ∈ cs, ∀ cty np after fds ri rm ret norm,
        V.ctor blk idx c = some (cty, np) →
        peelCtorParams V fuel np 0 aux sp np 0
          (Binding.FamilyFlat.exprInstLevels us cty) = some after →
        fieldsClassify V fuel es 0 0 after = some (fds, ri, rm, ret, norm) →
        ∀ (j fieldIdx : Nat) (dom : KExpr),
          ri[j]? = some fieldIdx → norm[fieldIdx]? = some dom →
          let memIdx := (rm[j]?).getD 0
          let tnp := (fop[memIdx]?).getD 0
          (∀ d ∈ (peelAll dom).1, d.renameConsts f = d) ∧
          (∀ a ∈ ((peelAll dom).2.getAppArgs).drop tnp, a.renameConsts f = a)) →
      ruleBodies V fuel es fop peersC nP nMot nMin us recLvls aux sp elim blk idx off cs =
        some bsC →
      ruleBodies V fuel es fop peersW nP nMot nMin us recLvls aux sp elim blk idx off cs =
        some (bsC.map (Expr.renameConsts f)) := by
  intro cs
  induction cs with
  | nil =>
    intro bsC _ h
    simp only [ruleBodies, Option.some.injEq] at h ⊢
    subst h; rfl
  | cons c cs' ih =>
    intro bsC hfix h
    simp only [ruleBodies] at h ⊢
    cases hvc : V.ctor blk idx c with
    | none => simp [hvc] at h
    | some p =>
      obtain ⟨cty, np⟩ := p
      simp only [hvc] at h
      cases hrbC : ruleBody V fuel es fop peersC cty (off + c) nP nMot nMin np us recLvls aux sp
          elim with
      | none => simp [hrbC] at h
      | some bC =>
        simp only [hrbC] at h
        cases hrest : ruleBodies V fuel es fop peersC nP nMot nMin us recLvls aux sp elim blk idx
            off cs' with
        | none => simp [hrest] at h
        | some bsC' =>
          simp only [hrest, Option.map_some, Option.some.injEq] at h
          subst h
          have hrbW : ruleBody V fuel es fop peersW cty (off + c) nP nMot nMin np us recLvls aux sp
              elim = some (bC.renameConsts f) := by
            unfold ruleBody at hrbC ⊢
            cases hpf : peelForalls np (Binding.FamilyFlat.exprInstLevels us cty) with
            | none => simp [hpf] at hrbC
            | some raw =>
              simp only [hpf] at hrbC ⊢
              cases hpc : peelCtorParams V fuel np 0 aux sp np 0
                  (Binding.FamilyFlat.exprInstLevels us cty) with
              | none => simp [hpc] at hrbC
              | some after =>
                simp only [hpc] at hrbC ⊢
                cases hfc : fieldsClassify V fuel es 0 0 after with
                | none => simp [hfc] at hrbC
                | some res =>
                  obtain ⟨fds, ri, rm, ret, norm⟩ := res
                  simp only [hfc] at hrbC ⊢
                  split at hrbC
                  · next hlen =>
                    simp only [hlen, ↓reduceIte]
                    refine applyIhs_renameConsts hpeers 0 ri _ _ bC ?_ ?_ hrbC
                    · rw [fieldBVars_renameConsts]; rfl
                    · intro j fi dom hri hdom
                      obtain ⟨h1, h2⟩ := hfix c List.mem_cons_self cty np after fds ri rm ret norm
                        hvc hpc hfc j fi dom hri hdom
                      have hfix_lift : ∀ (e : KExpr) (n cut : Nat),
                          e.renameConsts f = e → (e.liftLooseBVars n cut).renameConsts f =
                            e.liftLooseBVars n cut := by
                        intro e n cut he
                        rw [renameConsts_liftLooseBVars_wb, he]
                      have h1_step := peelAll_liftLooseBVars dom ((peelAll raw).1.length - fi) 0
                      have h2_step := peelAll_liftLooseBVars
                        (dom.liftLooseBVars ((peelAll raw).1.length - fi) 0)
                        (nMot + nMin) (peelAll raw).1.length
                      constructor
                      · intro d hd
                        rw [h2_step.1] at hd
                        obtain ⟨⟨d₁, i₁⟩, hd₁, rfl⟩ := List.mem_map.mp hd
                        have hd₁_mem :
                            d₁ ∈ (peelAll (dom.liftLooseBVars ((peelAll raw).1.length - fi) 0)).1 :=
                          mem_of_mem_zipIdx_wb hd₁
                        rw [h1_step.1] at hd₁_mem
                        obtain ⟨⟨d₀, i₀⟩, hd₀, rfl⟩ := List.mem_map.mp hd₁_mem
                        have hd₀_mem : d₀ ∈ (peelAll dom).1 := mem_of_mem_zipIdx_wb hd₀
                        exact hfix_lift _ _ _ (hfix_lift _ _ _ (h1 d₀ hd₀_mem))
                      · intro a ha
                        rw [h2_step.2, h1_step.2, getAppArgs_liftLooseBVars,
                          getAppArgs_liftLooseBVars, ← List.map_drop, ← List.map_drop] at ha
                        obtain ⟨a₁, ha₁, rfl⟩ := List.mem_map.mp ha
                        obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha₁
                        exact hfix_lift _ _ _ (hfix_lift _ _ _
                          (h2 a₀ (by simpa only [Nat.zero_add] using ha₀)))
                  · cases hrbC
          dsimp only
          rw [hrbW, ih bsC' (fun c' hc' => hfix c' (List.mem_cons_of_mem _ hc')) hrest]
          rfl

private theorem liftIndices_getElem? (doms : List KExpr) (shift i : Nat) :
    (liftIndices doms shift)[i]? = (doms[i]?).map (fun d => d.liftLooseBVars shift i) := by
  unfold liftIndices
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases doms[i]? <;> simp

/-- **Peer renaming on `ruleBodiesAt` from absence of renamed keys in `recTypeAt`**: whenever
`recTypeAt` mentions no constant moved by `f`, and every constructor `c` of entry `k` has parameter
count matching `nP` (when `aux = false`) or bounded by `ek.params.length` (when `aux = true`),
renaming `ruleBodiesAt` at `peersC` by `f` produces `ruleBodiesAt` at `peersW`. -/
theorem ruleBodiesAt_renameConsts_of_recTypeAt {V : ReconView} {f : KKey → KKey}
    {fuel : Nat} {es : List FlatEntry} {off nP nMot nMin nl k : Nat}
    {peersC peersW : List _root_.Address} {R : KExpr} {bsC : List KExpr}
    (hpeers : ∀ (j : Nat) aC, peersC[j]? = some aC →
      ∃ aW, peersW[j]? = some aW ∧ f (V.key aC) = V.key aW)
    (hR : recTypeAt V fuel es off nP k = some R)
    (hR_fix : ∀ q, f q ≠ q → R.mentionsConst q = false)
    (hnp_match : ∀ (ek : FlatEntry) (self : IndData), es[k]? = some ek →
      V.ind ek.addr = some (some self) →
      ∀ c cty np, c < self.nctors → V.ctor self.blk self.idx c = some (cty, np) →
        (ek.aux = false → np = nP) ∧ (ek.aux = true → np ≤ ek.params.length))
    (hbs : ruleBodiesAt V fuel es off nP nMot nMin nl k peersC = some bsC) :
    ruleBodiesAt V fuel es off nP nMot nMin nl k peersW = some (bsC.map (Expr.renameConsts f)) := by
  unfold ruleBodiesAt at hbs ⊢
  cases hek : es[k]? with
  | none => simp [hek] at hbs
  | some ek =>
    simp only [hek] at hbs ⊢
    cases hself : V.ind ek.addr with
    | none => simp [hself] at hbs
    | some optS =>
      cases optS with
      | none => simp [hself] at hbs
      | some self =>
        cases hfop : flatOwnParams V es with
        | none => simp [hself, hfop] at hbs
        | some fop =>
          cases hcb : ctorsBefore V es k with
          | none => simp [hself, hfop, hcb] at hbs
          | some cb =>
            simp only [hself, hfop, hcb] at hbs ⊢
            unfold recTypeAt at hR
            cases he0 : es[0]? with
            | none => simp [he0] at hR
            | some e0 =>
              simp only [he0, hek] at hR
              cases hprim : V.ind e0.addr with
              | none => simp [hprim] at hR
              | some optP =>
                cases optP with
                | none => simp [hprim] at hR
                | some prim =>
                  simp only [hprim, hself] at hR
                  cases hcd : Binding.FamilyRecon.collectDoms V fuel nP
                      (Binding.FamilyFlat.exprInstLevels
                        ((List.range prim.nl).map fun i => Level.param (off + i)) prim.ty) with
                  | none => simp [hcd] at hR
                  | some pDoms =>
                    obtain ⟨paramDoms, _⟩ := pDoms
                    simp only [hcd] at hR
                    cases hmot : Binding.FamilyRecon.allMotives V fuel (elimLevel off) nP es 0 with
                    | none => simp [hmot] at hR
                    | some motDoms =>
                      simp only [hmot, hfop] at hR
                      cases hmin : allMinors V fuel es fop nP es.length nP (elimLevel off) es 0 0 with
                      | none => simp [hmin] at hR
                      | some minDoms =>
                        simp only [hmin] at hR
                        cases hpm : Binding.FamilyRecon.peelMotiveParams nP ek.aux ek.params self.np 0
                            (Binding.FamilyFlat.exprInstLevels ek.levels self.ty) with
                        | none => simp [hpm] at hR
                        | some selfAfter =>
                          simp only [hpm] at hR
                          cases hidx : Binding.FamilyRecon.collectDoms V fuel self.ni selfAfter with
                          | none => simp [hidx] at hR
                          | some idxRaw =>
                            simp only [hidx, Option.some.injEq] at hR
                            subst hR
                            have hmin_nomove : ∀ q, f q ≠ q → ∀ m ∈ minDoms, m.mentionsConst q = false := by
                              intro q hq
                              have h1 := mentionsConst_wrapForalls_false (hR_fix q hq)
                              have h2 := mentionsConst_wrapForalls_false h1.1
                              exact (mentionsConst_wrapForalls_false h2.1).2
                            obtain ⟨info, prev', ms, hvi, hmd, hms_sub⟩ :=
                              allMinors_mem_at es 0 0 minDoms hmin k ek hek
                            have hinfo_eq : info = self :=
                              Option.some.inj (Option.some.inj (hvi.symm.trans hself))
                            subst info
                            refine ruleBodies_renameConsts_of_fixed hpeers (List.range self.nctors) bsC
                              ?_ hbs
                            intro c hc_mem cty np after fds ri rm ret norm hvc hpc hfc j fi dom hri hdom
                            have hclt : c < self.nctors := List.mem_range.mp hc_mem
                            have hc_get : (List.range self.nctors)[c]? = some c := by
                              simp [List.getElem?_range hclt]
                            obtain ⟨cty', np', m, hvc', hma, hm_in⟩ :=
                              minorDoms_get_mem (List.range self.nctors) prev' ms hmd c c hc_get
                            have hpair : (cty', np') = (cty, np) := Option.some.inj (hvc'.symm.trans hvc)
                            injection hpair with hcty_eq hnp_eq
                            subst cty' np'
                            obtain ⟨hnp_f, hnp_t⟩ := hnp_match ek self hek hself c cty np hclt hvc
                            have hpc_eq :
                                peelCtorParams V fuel nP 0 ek.aux ek.params np 0
                                  (Binding.FamilyFlat.exprInstLevels ek.levels cty) =
                                some after := by
                              rw [peelCtorParams_eq_of_depth (fun hf => (hnp_f hf).symm) np 0 _
                                (fun ht => by simpa using hnp_t ht)]
                              exact hpc
                            unfold minorAt at hma
                            dsimp only at hma
                            rw [hpc_eq] at hma
                            dsimp only at hma
                            rw [hfc] at hma
                            dsimp only at hma
                            cases hih : ihDoms rm (liftIndices norm (es.length + (prev' + c))) fop nP
                                fds.length (nP + es.length + (prev' + c)) (elimLevel off) 0 ri with
                            | none => simp [hih] at hma
                            | some ihs =>
                              simp only [hih, Option.some.injEq] at hma
                              subst hma
                              have hdom_lift :
                                  (liftIndices norm (es.length + (prev' + c)))[fi]? =
                                    some (dom.liftLooseBVars (es.length + (prev' + c)) fi) := by
                                rw [liftIndices_getElem?, hdom]; rfl
                              have hmc_pair : ∀ q, f q ≠ q →
                                  (∀ d ∈ (peelAll dom).1, d.mentionsConst q = false) ∧
                                  (∀ a ∈ ((peelAll dom).2.getAppArgs).drop ((fop[(rm[j]?).getD 0]?).getD 0),
                                    a.mentionsConst q = false) := by
                                intro q hq
                                have hm_q := hmin_nomove q hq _ (hms_sub _ hm_in)
                                have h1 := mentionsConst_wrapForalls_false hm_q
                                have h2 := mentionsConst_wrapForalls_false h1.1
                                obtain ⟨hpeel1, hpeel2⟩ :=
                                  mentionsConst_ihDoms_false 0 ri ihs hih h2.2 j fi
                                    (dom.liftLooseBVars (es.length + (prev' + c)) fi) hri hdom_lift
                                obtain ⟨hp1, hp2⟩ :=
                                  peelAll_liftLooseBVars dom (es.length + (prev' + c)) fi
                                constructor
                                · intro d hd_mem
                                  obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hd_mem
                                  have hzip : (d, idx) ∈ (peelAll dom).1.zipIdx := by
                                    rw [List.mem_iff_getElem?]
                                    exact ⟨idx, by simp [List.getElem?_zipIdx, hidx]⟩
                                  have hmem_l : d.liftLooseBVars (es.length + (prev' + c)) (fi + idx) ∈
                                      (peelAll (dom.liftLooseBVars (es.length + (prev' + c)) fi)).1 := by
                                    rw [hp1]; exact List.mem_map.mpr ⟨(d, idx), hzip, rfl⟩
                                  have := hpeel1 _ hmem_l
                                  rwa [mentionsConst_liftLooseBVars] at this
                                · intro a ha_mem
                                  have hmem_l : a.liftLooseBVars (es.length + (prev' + c))
                                        (fi + (peelAll dom).1.length) ∈
                                      ((peelAll (dom.liftLooseBVars (es.length + (prev' + c)) fi)).2.getAppArgs).drop
                                        ((fop[(rm[0 + j]?).getD 0]?).getD 0) := by
                                    rw [hp2, getAppArgs_liftLooseBVars, ← List.map_drop]
                                    exact List.mem_map.mpr ⟨a, by simpa only [Nat.zero_add] using ha_mem, rfl⟩
                                  have := hpeel2 _ hmem_l
                                  rwa [mentionsConst_liftLooseBVars] at this
                              exact ⟨fun d hd => renameConsts_eq_self_of_not_mentions d
                                  (fun q hq => (hmc_pair q hq).1 d hd),
                                fun a ha => renameConsts_eq_self_of_not_mentions a
                                  (fun q hq => (hmc_pair q hq).2 a ha)⟩

private theorem whnfTele_keys {V : ReconView} {S : _root_.Address → Prop} (hC : V.ClosedOn S)
    {fuel : Nat} :
    ∀ (n : Nat) (e r : KExpr), RKeysAt V S e → whnfTele V fuel n e = some r → RKeysAt V S r := by
  intro n
  induction n with
  | zero => intro _ _ _ h; simp [whnfTele] at h
  | succ n ih =>
    intro e r hK h
    simp only [whnfTele] at h
    cases hh : hnf V fuel e with
    | none => simp [hh] at h
    | some w =>
      obtain ⟨-, hkw⟩ := Binding.FamilyRecon.hnf_leOn (ReconView.LeOn.refl V S) hC
        (Nat.le_refl _) hK hh
      simp only [hh] at h
      cases hi : Binding.FamilyRecon.isForall w with
      | none =>
        simp only [hi, Option.some.injEq] at h
        subst h; exact hkw
      | some p =>
        obtain ⟨d, b, m⟩ := p
        simp only [hi] at h
        cases ht : whnfTele V fuel n b with
        | none => simp [ht] at h
        | some b' =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hkd, hkb⟩ := Binding.FamilyRecon.isForall_keys hi hkw
          have hkb' := ih b b' hkb ht
          intro k hk
          cases hk with
          | allTy hd => exact hkd k hd
          | allBody hb => exact hkb' k hb

private theorem fieldsClassify_norm_keys {V : ReconView} {S : _root_.Address → Prop}
    (hC : V.ClosedOn S) {fuel : Nat} {es : List FlatEntry} {liftBy : Nat} :
    ∀ (ty : KExpr) (fidx : Nat) (fds : List KExpr) (ri rm : List Nat) (ret : KExpr)
      (norm : List KExpr),
      RKeysAt V S ty → fieldsClassify V fuel es liftBy fidx ty = some (fds, ri, rm, ret, norm) →
      ∀ nd ∈ norm, RKeysAt V S nd := by
  intro ty
  induction ty with
  | forallE d b m ihd ihb =>
    intro fidx fds ri rm ret norm hK h
    simp only [fieldsClassify] at h
    cases hw : whnfTele V fuel fuel d with
    | none => simp [hw] at h
    | some nd0 =>
      simp only [hw] at h
      cases hrest : fieldsClassify V fuel es liftBy (fidx + 1) b with
      | none => simp [hrest] at h
      | some res =>
        obtain ⟨fds', ri', rm', ret', norm'⟩ := res
        simp only [hrest] at h
        have hnd0 : RKeysAt V S nd0 := whnfTele_keys hC fuel d nd0 (fun k hk => hK k (.allTy hk)) hw
        have hnorm' : ∀ nd ∈ norm', RKeysAt V S nd :=
          ihb (fidx + 1) fds' ri' rm' ret' norm' (fun k hk => hK k (.allBody hk)) hrest
        cases hrf : Binding.FamilyRecon.isRecField V es (liftBy + fidx) nd0 with
        | some _ =>
          rw [hrf] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, -, -, -, rfl⟩ := h
          intro nd hnd
          rcases List.mem_cons.mp hnd with rfl | hnd'
          · exact hnd0
          · exact hnorm' nd hnd'
        | none =>
          rw [hrf] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, -, -, -, rfl⟩ := h
          intro nd hnd
          rcases List.mem_cons.mp hnd with rfl | hnd'
          · exact hnd0
          · exact hnorm' nd hnd'
  | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _ | lit _
  | proj _ _ _ =>
    intro _ _ _ _ _ norm _ h
    simp only [fieldsClassify, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, -, -, rfl⟩ := h
    intro _ hm; exact nomatch hm

private theorem rKeysAt_peelAll {V : ReconView} {S : _root_.Address → Prop} :
    ∀ (e : KExpr), RKeysAt V S e →
      (∀ d ∈ (peelAll e).1, RKeysAt V S d) ∧ RKeysAt V S (peelAll e).2
  | .forallE d b m, h => by
    simp only [peelAll]
    have ⟨h1, h2⟩ := rKeysAt_peelAll b (fun k hk => h k (.allBody hk))
    refine ⟨fun x hx => ?_, h2⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact fun k hk => h k (.allTy hk)
    · exact h1 x hx'
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
  | .lam _ _ _, h | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h =>
    ⟨(fun _ hm => nomatch hm), h⟩

private theorem rKeysAt_getAppArgs {V : ReconView} {S : _root_.Address → Prop} :
    ∀ (e : KExpr), RKeysAt V S e → ∀ a ∈ e.getAppArgs, RKeysAt V S a
  | .app f x, h => by
    intro a ha
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact rKeysAt_getAppArgs f (fun k hk => h k (.appFn hk)) a ha
    · exact fun k hk => h k (.appArg hk)
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _ _, _
  | .forallE _ _ _, _ | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ =>
    fun _ ha => nomatch ha

private theorem renameConsts_of_rKeysAt {V : ReconView} {S : _root_.Address → Prop}
    {f : KKey → KKey}
    (hfix : ∀ k, f k ≠ k → ∃ a, V.addr k = some a ∧ ¬ S a) :
    ∀ (e : KExpr), RKeysAt V S e → e.renameConsts f = e := by
  intro e hK
  refine renameConsts_eq_self_of_not_mentions e fun k hk => ?_
  obtain ⟨a, ha, hnotS⟩ := hfix k hk
  -- If `e.mentionsConst k = true`, then `KeyIn k e`, contradicting `hnotS` via `hK`.
  have hmc_keyIn : ∀ (x : KExpr), x.mentionsConst k = true → KeyIn k x := by
    intro x
    induction x with
    | bvar _ | sort _ | lit _ => intro hm; simp [Expr.mentionsConst] at hm
    | fvar _ t ih =>
      intro hm; simp [Expr.mentionsConst] at hm; exact .fvarTy (ih hm)
    | const n us =>
      intro hm; simp only [Expr.mentionsConst, beq_iff_eq] at hm; subst hm; exact .const us
    | app g a ihf iha =>
      intro hm; simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
      rcases hm with h1 | h2
      · exact .appFn (ihf h1)
      · exact .appArg (iha h2)
    | lam t b _ iht ihb =>
      intro hm; simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
      rcases hm with h1 | h2
      · exact .lamTy (iht h1)
      · exact .lamBody (ihb h2)
    | forallE t b _ iht ihb =>
      intro hm; simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
      rcases hm with h1 | h2
      · exact .allTy (iht h1)
      · exact .allBody (ihb h2)
    | letE t v b _ iht ihv ihb =>
      intro hm; simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
      rcases hm with (h1 | h2) | h3
      · exact .letTy (iht h1)
      · exact .letVal (ihv h2)
      · exact .letBody (ihb h3)
    | proj s i x ih =>
      intro hm; simp only [Expr.mentionsConst, Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with rfl | h2
      · exact .proj i x
      · exact .projBody (ih h2)
  cases hm : e.mentionsConst k with
  | false => rfl
  | true => exact (hnotS (hK k (hmc_keyIn e hm) a ha)).elim

/-- **Peer renaming on `ruleBodiesAt` from a closed set of addresses**: whenever `V` is closed on
`S`, entry `k` lies in `S` (`REntryAt`), and every constant moved by `f` names an address outside
`S`, renaming `ruleBodiesAt` at `peersC` by `f` produces `ruleBodiesAt` at `peersW`. -/
theorem ruleBodiesAt_renameConsts_of_closed {V : ReconView} {S : _root_.Address → Prop}
    {f : KKey → KKey} {fuel : Nat} {es : List FlatEntry} {off nP nMot nMin nl k : Nat}
    {peersC peersW : List _root_.Address} {bsC : List KExpr}
    (hC : V.ClosedOn S)
    (hpeers : ∀ (j : Nat) aC, peersC[j]? = some aC →
      ∃ aW, peersW[j]? = some aW ∧ f (V.key aC) = V.key aW)
    (hfix : ∀ q, f q ≠ q → ∃ a, V.addr q = some a ∧ ¬ S a)
    (hent : ∀ ek, es[k]? = some ek → REntryAt V S ek)
    (hbs : ruleBodiesAt V fuel es off nP nMot nMin nl k peersC = some bsC) :
    ruleBodiesAt V fuel es off nP nMot nMin nl k peersW = some (bsC.map (Expr.renameConsts f)) := by
  unfold ruleBodiesAt at hbs ⊢
  cases hek : es[k]? with
  | none => simp [hek] at hbs
  | some ek =>
    simp only [hek] at hbs ⊢
    cases hself : V.ind ek.addr with
    | none => simp [hself] at hbs
    | some optS =>
      cases optS with
      | none => simp [hself] at hbs
      | some self =>
        cases hfop : flatOwnParams V es with
        | none => simp [hself, hfop] at hbs
        | some fop =>
          cases hcb : ctorsBefore V es k with
          | none => simp [hself, hfop, hcb] at hbs
          | some cb =>
            simp only [hself, hfop, hcb] at hbs ⊢
            have hekS := hent ek hek
            have hblkS : S self.blk := hC.indBlk ek.addr self hekS.addr hself
            refine ruleBodies_renameConsts_of_fixed hpeers (List.range self.nctors) bsC ?_ hbs
            intro c _ cty np after fds ri rm ret norm hvc hpc hfc j fi dom hri hdom
            have hctyS : RKeysAt V S cty := hC.ctorTy self.blk self.idx c cty np hblkS hvc
            have hafterS : RKeysAt V S after :=
              (Binding.FamilyRecon.peelCtorParams_leOn (ReconView.LeOn.refl V S) hC (Nat.le_refl _)
                hekS.params np 0 _ after (Binding.FamilyRecon.rk_exprInstLevels _ hctyS) hpc).2
            have hdomS : RKeysAt V S dom :=
              fieldsClassify_norm_keys hC after 0 fds ri rm ret norm hafterS hfc dom
                (List.mem_of_getElem? hdom)
            obtain ⟨h1, h2⟩ := rKeysAt_peelAll dom hdomS
            exact ⟨fun d hd => renameConsts_of_rKeysAt hfix d (h1 d hd),
              fun a ha => renameConsts_of_rKeysAt hfix a
                (rKeysAt_getAppArgs _ h2 a (List.mem_of_mem_drop ha))⟩

/-! ## Major-premise syntactic equality -/

private theorem liftLooseBVars_lowerBVars_of_not_hasBVarIn :
    ∀ (e : KExpr) (n c : Nat),
      Binding.FamilyFlat.hasBVarIn c (c + n) e = false →
      (e.lowerBVars n c).liftLooseBVars n c = e
  | .bvar i, n, c, h => by
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [Expr.lowerBVars]
    split
    · next hge =>
      simp only [Expr.liftLooseBVars]
      have hge' : i ≥ c + n := by omega
      have hge2 : c ≤ i - n := by omega
      simp [hge2]
      omega
    · next hlt =>
      simp only [Expr.liftLooseBVars]
      have hlt2 : ¬ c ≤ i := by omega
      simp [hlt2]
  | .fvar _ t, n, c, _ => by simp [Expr.lowerBVars, Expr.liftLooseBVars]
  | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, n, c, h => by
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff] at h
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn f n c h.1,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn a n c h.2]
  | .lam t b _, n, c, h => by
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff] at h
    have h2 : Binding.FamilyFlat.hasBVarIn (c + 1) (c + 1 + n) b = false := by
      simpa [Nat.add_assoc, Nat.add_comm n 1] using h.2
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn t n c h.1,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn b n (c + 1) h2]
  | .forallE t b _, n, c, h => by
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff] at h
    have h2 : Binding.FamilyFlat.hasBVarIn (c + 1) (c + 1 + n) b = false := by
      simpa [Nat.add_assoc, Nat.add_comm n 1] using h.2
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn t n c h.1,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn b n (c + 1) h2]
  | .letE t v b _, n, c, h => by
    simp only [Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff] at h
    have h2 : Binding.FamilyFlat.hasBVarIn (c + 1) (c + 1 + n) b = false := by
      simpa [Nat.add_assoc, Nat.add_comm n 1] using h.2
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn t n c h.1.1,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn v n c h.1.2,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn b n (c + 1) h2]
  | .proj _ _ e, n, c, h => by
    simp only [Binding.FamilyFlat.hasBVarIn] at h
    simp [Expr.lowerBVars, Expr.liftLooseBVars,
      liftLooseBVars_lowerBVars_of_not_hasBVarIn e n c h]

/-- **Major-premise domain exact equality for auxiliary (nested) and plain recursors**:
given two recursor types (at positional level parameters) whose `mI`-th domains have the same
head `const (keyOf t e.addr) e.levels` and index suffix `(List.range (mI - rP)).map (fun i =>
.bvar (mI - rP - 1 - i))`, and whose parameter prefixes agree after lowering (or are the canonical
parameter bvars when `aux = false`), their `getAppFn` and `getAppArgs` are syntactically equal. -/
theorem majorDom_pos_eq_of_pins {dC dW : KExpr} {hd : KExpr} {nP kIdx shift : Nat}
    {pins : List KExpr}
    (hfnC : dC.getAppFn = hd) (hfnW : dW.getAppFn = hd)
    (hlenC : dC.getAppArgs.length = nP + kIdx) (hlenW : dW.getAppArgs.length = nP + kIdx)
    (hdropC : dC.getAppArgs.drop nP = (List.range kIdx).map fun i => .bvar (kIdx - 1 - i))
    (hdropW : dW.getAppArgs.drop nP = (List.range kIdx).map fun i => .bvar (kIdx - 1 - i))
    (hlowC : (dC.getAppArgs.take nP).map (Expr.lowerBVars shift 0) = pins)
    (hlowW : (dW.getAppArgs.take nP).map (Expr.lowerBVars shift 0) = pins)
    (hnoC : ∀ x ∈ dC.getAppArgs.take nP, Binding.FamilyFlat.hasBVarIn 0 shift x = false)
    (hnoW : ∀ x ∈ dW.getAppArgs.take nP, Binding.FamilyFlat.hasBVarIn 0 shift x = false) :
    dW.getAppFn = dC.getAppFn ∧ dW.getAppArgs = dC.getAppArgs := by
  have htakeC : dC.getAppArgs.take nP = pins.map (Expr.liftLooseBVars shift 0) := by
    rw [← hlowC, List.map_map]
    exact (map_id_of_mem_wb fun x hx =>
      liftLooseBVars_lowerBVars_of_not_hasBVarIn x shift 0 (by simpa using hnoC x hx)).symm
  have htakeW : dW.getAppArgs.take nP = pins.map (Expr.liftLooseBVars shift 0) := by
    rw [← hlowW, List.map_map]
    exact (map_id_of_mem_wb fun x hx =>
      liftLooseBVars_lowerBVars_of_not_hasBVarIn x shift 0 (by simpa using hnoW x hx)).symm
  refine ⟨hfnW.trans hfnC.symm, ?_⟩
  rw [← List.take_append_drop nP dW.getAppArgs, ← List.take_append_drop nP dC.getAppArgs,
    htakeW, htakeC, hdropW, hdropC]

private theorem peelForalls_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) (e : KExpr),
      peelForalls n (e.instantiateLevelParams ps us) =
        (peelForalls n e).map (Expr.instantiateLevelParams ps us)
  | 0, _ => rfl
  | n + 1, .forallE _ b _ => peelForalls_instantiateLevelParams ps us n b
  | n + 1, .bvar _ | n + 1, .fvar _ _ | n + 1, .sort _ | n + 1, .const _ _
  | n + 1, .app _ _ | n + 1, .lam _ _ _ | n + 1, .letE _ _ _ _ | n + 1, .lit _
  | n + 1, .proj _ _ _ => rfl

private theorem getAppFn_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr), (e.instantiateLevelParams ps us).getAppFn =
      e.getAppFn.instantiateLevelParams ps us
  | .app f _ => getAppFn_instantiateLevelParams ps us f
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

private theorem getAppArgs_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr), (e.instantiateLevelParams ps us).getAppArgs =
      e.getAppArgs.map (Expr.instantiateLevelParams ps us)
  | .app f a => by
    simp only [Expr.instantiateLevelParams, Expr.getAppArgs, List.map_append, List.map_singleton]
    rw [getAppArgs_instantiateLevelParams ps us f]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ _
  | .forallE _ _ _ | .letE _ _ _ _ | .lit _ | .proj _ _ _ => rfl

/-- `stripPis mI` agrees with `peelForalls mI` on the remaining expression. -/
theorem stripPis_iff_peelForalls :
    ∀ (n : Nat) (e res : KExpr),
      peelForalls n e = some res ↔ ∃ bs, e.stripPis n = some (bs, res)
  | 0, e, res => by
    simp only [peelForalls, Expr.stripPis, Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h; exact ⟨[], rfl, h⟩
    · rintro ⟨_, _, h⟩; exact h
  | n + 1, e, res => by
    cases e with
    | forallE d b m =>
      simp only [peelForalls]
      constructor
      · intro h
        obtain ⟨bs, hbs⟩ := (stripPis_iff_peelForalls n b res).mp h
        exact ⟨(d, m) :: bs, Ix.Kernel.Semantics.stripPis_succ_forallE hbs⟩
      · rintro ⟨bs, hbs⟩
        obtain ⟨d', b', m', bs0, heq, hs0⟩ := Ix.Kernel.Semantics.stripPis_succ_inv hbs
        injection heq with _ hb _
        subst hb
        exact (stripPis_iff_peelForalls n b res).mpr ⟨bs0, hs0⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _
    | letE _ _ _ _ | lit _ | proj _ _ _ =>
      simp only [peelForalls, reduceCtorEq, false_iff, not_exists]
      intro bs h
      obtain ⟨_, _, _, _, heq, _⟩ := Ix.Kernel.Semantics.stripPis_succ_inv h
      cases heq

/-- `Core.piDomAt mI e = some d` iff `binderDomAfter mI e = some d`. -/
theorem piDomAt_eq_binderDomAfter : ∀ (mI : Nat) (e : KExpr),
    Core.piDomAt mI e = binderDomAfter mI e
  | 0, .forallE _ _ _ => rfl
  | 0, .bvar _ | 0, .fvar _ _ | 0, .sort _ | 0, .const _ _ | 0, .app _ _
  | 0, .lam _ _ _ | 0, .letE _ _ _ _ | 0, .lit _ | 0, .proj _ _ _ => rfl
  | mI + 1, .forallE _ b _ => piDomAt_eq_binderDomAfter mI b
  | mI + 1, .bvar _ | mI + 1, .fvar _ _ | mI + 1, .sort _ | mI + 1, .const _ _ | mI + 1, .app _ _
  | mI + 1, .lam _ _ _ | mI + 1, .letE _ _ _ _ | mI + 1, .lit _ | mI + 1, .proj _ _ _ => rfl

/-- Transport exact major-premise `getAppFn` and `getAppArgs` equality from positional level
parameters (`posOf ps`) back to `ps`. -/
theorem majorDom_of_posOf_perm {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {mI : Nat} {tyC tyW dC_pos dW_pos : KExpr}
    (hC : binderDomAfter mI (Core.posOf ps tyC) = some dC_pos)
    (hW : binderDomAfter mI (Core.posOf ps tyW) = some dW_pos)
    (hfn : dW_pos.getAppFn = dC_pos.getAppFn)
    (hargs : dW_pos.getAppArgs = dC_pos.getAppArgs) :
    ∃ DW DC, Core.piDomAt mI tyW = some DW ∧ Core.piDomAt mI tyC = some DC ∧
      DW.getAppFn = DC.getAppFn ∧ DW.getAppArgs = DC.getAppArgs := by
  have inv_bd : ∀ (ty d_pos : KExpr), binderDomAfter mI (Core.posOf ps ty) = some d_pos →
      Core.piDomAt mI ty = some (d_pos.instantiateLevelParams (List.range ps.length) (ps.map .param)) := by
    intro ty d_pos hb
    unfold binderDomAfter at hb
    cases hp : peelForalls mI (Core.posOf ps ty) with
    | none => simp [hp] at hb
    | some r =>
      cases r with
      | forallE d b m =>
        simp only [hp, Option.some.injEq] at hb
        subst hb
        rw [piDomAt_eq_binderDomAfter, ← Decl.posOf_perm_inv hperm ty]
        unfold binderDomAfter
        rw [peelForalls_instantiateLevelParams, hp]
        rfl
      | _ => simp [hp] at hb
  refine ⟨dW_pos.instantiateLevelParams (List.range ps.length) (ps.map .param),
    dC_pos.instantiateLevelParams (List.range ps.length) (ps.map .param),
    inv_bd tyW dW_pos hW, inv_bd tyC dC_pos hC, ?_, ?_⟩
  · rw [getAppFn_instantiateLevelParams, getAppFn_instantiateLevelParams, hfn]
  · rw [getAppArgs_instantiateLevelParams, getAppArgs_instantiateLevelParams, hargs]

/-- `WrapDom` on a term headed by a non-definition constant cannot consume, so it is `WrapRel`. -/
theorem wrapDom_not_defn_to_wrapRel {find? : KKey → Option (ConstantInfo .anon)}
    {d d' : KExpr} {k : KKey} {us : List KLevel}
    (h : WrapDom find? d d') (hfn : d.getAppFn = .const k us)
    (hnotdef : ∀ cv v hint, find? k ≠ some (.defnInfo cv v hint)) :
    WrapRel find? d d' := by
  cases h with
  | keep hw => exact hw
  | consume hc _ =>
    have hwa : Ix.Kernel.Semantics.wrapperArity find? k = none := by
      unfold Ix.Kernel.Semantics.wrapperArity
      cases hf : find? k with
      | none => rfl
      | some ci =>
        cases ci with
        | defnInfo cv v hint => exact (hnotdef cv v hint hf).elim
        | _ => rfl
    unfold consumeWrapper at hc
    rw [hfn] at hc
    cases hargs : d.getAppArgs with
    | nil => simp [hargs] at hc
    | cons a rest => simp [hargs, hwa] at hc

private theorem wrapRel_letFree_appSpine_const_aux {find? : KKey → Option (ConstantInfo .anon)}
    {k : KKey} {us : List KLevel} :
    ∀ (rargs : List KExpr) {d : KExpr},
      WrapRel find? d (Binding.FamilyRecon.appSpine (.const k us) rargs.reverse) →
      d.getAppArgs.length = rargs.length ∧
        ((∀ a ∈ rargs, ∃ i, a = .bvar i) → d.getAppArgs = rargs.reverse)
  | [], d, hw => by
    simp only [List.reverse_nil, Binding.FamilyRecon.appSpine, List.foldl_nil] at hw
    cases hw with
    | const _ => simp [Expr.getAppArgs]
  | a :: rest, d, hw => by
    have hfold : Binding.FamilyRecon.appSpine (.const k us) (a :: rest).reverse =
        .app (Binding.FamilyRecon.appSpine (.const k us) rest.reverse) a := by
      simp [Binding.FamilyRecon.appSpine, List.reverse_cons]
    rw [hfold] at hw
    cases hw with
    | app hwf hwa =>
      rename_i d1 d2
      obtain ⟨hlen, hbvars⟩ := wrapRel_letFree_appSpine_const_aux rest hwf
      refine ⟨by simp [Expr.getAppArgs, hlen], fun hall => ?_⟩
      obtain ⟨i, rfl⟩ := hall a List.mem_cons_self
      have hd2 : d2 = .bvar i := by
        cases hwa with
        | bvar => rfl
      rw [Expr.getAppArgs, hd2, hbvars (fun b hb => hall b (List.mem_cons_of_mem _ hb)),
        List.reverse_cons]

/-- A term related by `WrapRel` to an `appSpine` headed by a constant has the same argument count,
and identical arguments whenever every argument on the right is a `.bvar`. -/
theorem wrapRel_appSpine_const {find? : KKey → Option (ConstantInfo .anon)}
    {k : KKey} {us : List KLevel} {args : List KExpr} {d : KExpr}
    (hw : WrapRel find? d (Binding.FamilyRecon.appSpine (.const k us) args)) :
    d.getAppArgs.length = args.length ∧
      ((∀ a ∈ args, ∃ i, a = .bvar i) → d.getAppArgs = args) := by
  have h := wrapRel_letFree_appSpine_const_aux args.reverse (by simpa using hw)
  simpa using h

/-- `hasBVarIn` is invariant under `Core.ExprLvEq`. -/
theorem hasBVarIn_eq_of_exprLvEq {a b : KExpr} (h : Core.ExprLvEq a b) :
    ∀ lo hi, Binding.FamilyFlat.hasBVarIn lo hi a = Binding.FamilyFlat.hasBVarIn lo hi b := by
  induction h with
  | bvar | fvar _ | sort _ | const _ | lit => intro _ _; rfl
  | app _ _ ihf iha =>
    intro lo hi; simp only [Binding.FamilyFlat.hasBVarIn, ihf lo hi, iha lo hi]
  | lam _ _ iht ihb =>
    intro lo hi; simp only [Binding.FamilyFlat.hasBVarIn, iht lo hi, ihb (lo + 1) (hi + 1)]
  | forallE _ _ iht ihb =>
    intro lo hi; simp only [Binding.FamilyFlat.hasBVarIn, iht lo hi, ihb (lo + 1) (hi + 1)]
  | letE _ _ _ iht ihv ihb =>
    intro lo hi
    simp only [Binding.FamilyFlat.hasBVarIn, iht lo hi, ihv lo hi, ihb (lo + 1) (hi + 1)]
  | proj _ ih => intro lo hi; exact ih lo hi

/-- A term lifted by `n` at cutoff `c` has no loose variable in `[c, c + n)`. -/
theorem hasBVarIn_liftLooseBVars_false :
    ∀ (e : KExpr) (n c : Nat),
      Binding.FamilyFlat.hasBVarIn c (c + n) (e.liftLooseBVars n c) = false
  | .bvar i, n, c => by
    simp only [Expr.liftLooseBVars]
    split <;> simp only [Binding.FamilyFlat.hasBVarIn, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp only [Expr.liftLooseBVars, Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    exact ⟨hasBVarIn_liftLooseBVars_false f n c, hasBVarIn_liftLooseBVars_false a n c⟩
  | .lam t b _, n, c => by
    simp only [Expr.liftLooseBVars, Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    refine ⟨hasBVarIn_liftLooseBVars_false t n c, ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm 1 n] using hasBVarIn_liftLooseBVars_false b n (c + 1)
  | .forallE t b _, n, c => by
    simp only [Expr.liftLooseBVars, Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    refine ⟨hasBVarIn_liftLooseBVars_false t n c, ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm 1 n] using hasBVarIn_liftLooseBVars_false b n (c + 1)
  | .letE t v b _, n, c => by
    simp only [Expr.liftLooseBVars, Binding.FamilyFlat.hasBVarIn, Bool.or_eq_false_iff]
    refine ⟨⟨hasBVarIn_liftLooseBVars_false t n c, hasBVarIn_liftLooseBVars_false v n c⟩, ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm 1 n] using hasBVarIn_liftLooseBVars_false b n (c + 1)
  | .proj _ _ e, n, c => hasBVarIn_liftLooseBVars_false e n c

/-! ## Symmetric wrapper transport, `TwinRuleMatch`, and rule scoping -/

private theorem consumeStar_congr_left {find? : KKey → Option (ConstantInfo .anon)}
    {t₁ t₂ a : KExpr} (h : ExprLvEq t₁ t₂) (hs : ConsumeStar find? t₂ a) :
    ∃ a₁, ConsumeStar find? t₁ a₁ ∧ ExprLvEq a₁ a := by
  induction hs generalizing t₁ with
  | refl => exact ⟨t₁, .refl t₁, h⟩
  | step hc _ ih =>
    obtain ⟨m₁, hc₁, hm⟩ := consumeWrapper_congr h hc
    obtain ⟨a₁, hs₁, ha⟩ := ih hm
    exact ⟨a₁, .step hc₁ hs₁, ha⟩

private theorem consumeStar_instantiateLevelParams {find? : KKey → Option (ConstantInfo .anon)}
    (ps : List LevelParam) (us : List KLevel) {t a : KExpr}
    (hs : ConsumeStar find? t a) :
    ConsumeStar find? (t.instantiateLevelParams ps us) (a.instantiateLevelParams ps us) := by
  induction hs with
  | refl => exact .refl _
  | step hc _ ih => exact .step (consumeWrapper_instantiateLevelParams ps us hc) ih

private theorem consumeStar_liftLooseBVars {find? : KKey → Option (ConstantInfo .anon)}
    (n c : Nat) {t a : KExpr} (hs : ConsumeStar find? t a) :
    ConsumeStar find? (t.liftLooseBVars n c) (a.liftLooseBVars n c) := by
  induction hs with
  | refl => exact .refl _
  | step hc _ ih => exact .step (consumeWrapper_liftLooseBVars n c hc) ih

/-- `SymWrapT` respects `ExprLvEq` on the left. -/
theorem symWrapT_congr_exprLvEq_left {find? : KKey → Option (ConstantInfo .anon)}
    {d₁ d₁' d₂ : KExpr} (h : ExprLvEq d₁' d₁) (hs : SymWrapT find? d₁ d₂) :
    SymWrapT find? d₁' d₂ := by
  induction hs generalizing d₁' with
  | bvar i => cases h; exact .bvar i
  | fvar i _ _ => cases h; exact .fvar i _ _
  | sort huv => cases h with | sort hu => exact .sort (fun φ => (hu φ).trans (huv φ))
  | const hlv => cases h with | const hu => exact .const (forall2_eval_trans_left hu hlv)
  | lit l => cases h; exact .lit l
  | app _ _ ihf iha => cases h with | app hf ha => exact .app (ihf hf) (iha ha)
  | lamL hpw hcs _ _ ihd ihb =>
    cases h with
    | lam ht hb =>
      obtain ⟨a₁, hcs₁, ha⟩ := consumeStar_congr_left ht hcs
      exact .lamL hpw hcs₁ (ihd ha) (ihb hb)
  | lamR hpw hcs _ _ ihd ihb =>
    cases h with
    | lam ht hb => exact .lamR hpw hcs (ihd ht) (ihb hb)
  | forallEL hpw hcs _ _ ihd ihb =>
    cases h with
    | forallE ht hb =>
      obtain ⟨a₁, hcs₁, ha⟩ := consumeStar_congr_left ht hcs
      exact .forallEL hpw hcs₁ (ihd ha) (ihb hb)
  | forallER hpw hcs _ _ ihd ihb =>
    cases h with
    | forallE ht hb => exact .forallER hpw hcs (ihd ht) (ihb hb)
  | proj _ ih => cases h with | proj he => exact .proj (ih he)

/-- `SymWrapT` respects `ExprLvEq` on the right. -/
theorem symWrapT_congr_exprLvEq_right {find? : KKey → Option (ConstantInfo .anon)}
    {d₁ d₂ d₂' : KExpr} (hs : SymWrapT find? d₁ d₂) (h : ExprLvEq d₂ d₂') :
    SymWrapT find? d₁ d₂' :=
  (symWrapT_congr_exprLvEq_left h.symm hs.symm).symm

/-- `SymWrapT` commutes with `Expr.instantiateLevelParams`. -/
theorem symWrapT_instantiateLevelParams {find? : KKey → Option (ConstantInfo .anon)}
    (ps : List LevelParam) (us : List KLevel) {d₁ d₂ : KExpr} (h : SymWrapT find? d₁ d₂) :
    SymWrapT find? (d₁.instantiateLevelParams ps us) (d₂.instantiateLevelParams ps us) := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i _ _ => exact .fvar i _ _
  | sort huv => exact .sort (level_eval_subst_congr ps us huv)
  | const hlv => exact .const (forall2_eval_subst ps us hlv)
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lamL hpw hcs _ _ ihd ihb =>
    exact .lamL (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw])
      (consumeStar_instantiateLevelParams ps us hcs) ihd ihb
  | lamR hpw hcs _ _ ihd ihb =>
    exact .lamR (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw])
      (consumeStar_instantiateLevelParams ps us hcs) ihd ihb
  | forallEL hpw hcs _ _ ihd ihb =>
    exact .forallEL (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw])
      (consumeStar_instantiateLevelParams ps us hcs) ihd ihb
  | forallER hpw hcs _ _ ihd ihb =>
    exact .forallER (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw])
      (consumeStar_instantiateLevelParams ps us hcs) ihd ihb
  | proj _ ih => exact .proj ih

/-- Move `SymWrapT` from positional level parameters (`posOf ps`) back to `ps`. -/
theorem symWrapT_of_posOf_perm {find? : KKey → Option (ConstantInfo .anon)}
    {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length)) {d₁ d₂ : KExpr}
    (h : SymWrapT find? (Core.posOf ps d₁) (Core.posOf ps d₂)) :
    SymWrapT find? d₁ d₂ := by
  have h' := symWrapT_instantiateLevelParams (List.range ps.length) (ps.map .param) h
  rwa [Decl.posOf_perm_inv hperm d₁, Decl.posOf_perm_inv hperm d₂] at h'

/-- `SymWrapT` commutes with `Expr.liftLooseBVars`. -/
theorem symWrapT_liftLooseBVars {find? : KKey → Option (ConstantInfo .anon)}
    {d₁ d₂ : KExpr} (h : SymWrapT find? d₁ d₂) :
    ∀ n c, SymWrapT find? (d₁.liftLooseBVars n c) (d₂.liftLooseBVars n c) := by
  induction h with
  | bvar i => intro n c; simp only [Expr.liftLooseBVars]; split <;> exact .bvar _
  | fvar i _ _ => intro _ _; exact .fvar i _ _
  | sort huv => intro _ _; exact .sort huv
  | const hlv => intro _ _; exact .const hlv
  | lit l => intro _ _; exact .lit l
  | app _ _ ihf iha => intro n c; exact .app (ihf n c) (iha n c)
  | lamL hpw hcs _ _ ihd ihb =>
    intro n c
    exact .lamL hpw (consumeStar_liftLooseBVars n c hcs) (ihd n c) (ihb n (c + 1))
  | lamR hpw hcs _ _ ihd ihb =>
    intro n c
    exact .lamR hpw (consumeStar_liftLooseBVars n c hcs) (ihd n c) (ihb n (c + 1))
  | forallEL hpw hcs _ _ ihd ihb =>
    intro n c
    exact .forallEL hpw (consumeStar_liftLooseBVars n c hcs) (ihd n c) (ihb n (c + 1))
  | forallER hpw hcs _ _ ihd ihb =>
    intro n c
    exact .forallER hpw (consumeStar_liftLooseBVars n c hcs) (ihd n c) (ihb n (c + 1))
  | proj _ ih => intro n c; exact .proj (ih n c)

theorem symWrapT_peelForalls {find? : KKey → Option (ConstantInfo .anon)} :
    ∀ (n : Nat) {d₁ d₂ r₁ r₂ : KExpr}, SymWrapT find? d₁ d₂ →
      peelForalls n d₁ = some r₁ → peelForalls n d₂ = some r₂ → SymWrapT find? r₁ r₂
  | 0, _, _, _, _, h, h1, h2 => by
    simp only [peelForalls, Option.some.injEq] at h1 h2; subst h1 h2; exact h
  | n + 1, d₁, d₂, r₁, r₂, h, h1, h2 => by
    cases d₁ <;> simp [peelForalls] at h1
    cases d₂ <;> simp [peelForalls] at h2
    cases h with
    | forallEL _ _ _ hb | forallER _ _ _ hb => exact symWrapT_peelForalls n hb h1 h2

theorem symWrapT_of_lamsAlong {find? : KKey → Option (ConstantInfo .anon)} {elim : KLevel} :
    ∀ {n : Nat} {lC lW pC pW rC rW : KExpr},
      SymWrapT find? pC pW →
      LamsAlong elim n lC pC rC → LamsAlong elim n lW pW rW →
      SymWrapT find? rC rW → SymWrapT find? lC lW
  | 0, _, _, _, _, _, _, _, hC, hW, hr => by cases hC; cases hW; exact hr
  | n + 1, _, _, _, _, _, _, hP, hC, hW, hr => by
    cases hC with
    | succ hpwC hdomC hC' =>
      cases hW with
      | succ hpwW hdomW hW' =>
        cases hP with
        | forallEL _ hcs hdom hb =>
          obtain ⟨a', hcs', ha'⟩ := consumeStar_congr_left hdomC hcs
          exact .lamL (hpwC.trans hpwW.symm) hcs'
            (symWrapT_congr_exprLvEq_right (symWrapT_congr_exprLvEq_left ha' hdom) hdomW.symm)
            (symWrapT_of_lamsAlong hb hC' hW' hr)
        | forallER _ hcs hdom hb =>
          obtain ⟨a', hcs', ha'⟩ := consumeStar_congr_left hdomW hcs
          exact .lamR (hpwC.trans hpwW.symm) hcs'
            (symWrapT_congr_exprLvEq_left hdomC (symWrapT_congr_exprLvEq_right hdom ha'.symm))
            (symWrapT_of_lamsAlong hb hC' hW' hr)

theorem letFree_of_exprLvEq {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂) :
    letFree e₁ = letFree e₂ := by
  induction h with
  | bvar | fvar _ | sort _ | const _ | lit => rfl
  | app _ _ ihf iha => simp [letFree, ihf, iha]
  | lam _ _ iht ihb => simp [letFree, iht, ihb]
  | forallE _ _ iht ihb => simp [letFree, iht, ihb]
  | letE _ _ _ _ _ _ => rfl
  | proj _ ih => exact ih

theorem exprLvEq_to_wrapT_empty {e₁ e₂ : KExpr} (h : ExprLvEq e₁ e₂)
    (hlf : letFree e₁ = true) :
    WrapT (fun _ : KKey => (none : Option (ConstantInfo .anon))) e₁ e₂ := by
  induction h with
  | bvar => exact .bvar _
  | fvar _ => exact .fvar _ _ _
  | sort hu => exact .sort hu
  | const hus => exact .const (Binding.FamilyRecon.wrapLevels_of_lvEqList hus)
  | lit => exact .lit _
  | app _ _ ihf iha =>
    simp only [letFree, Bool.and_eq_true] at hlf
    exact .app (ihf hlf.1) (iha hlf.2)
  | lam _ _ iht ihb =>
    simp only [letFree, Bool.and_eq_true] at hlf
    exact .lam rfl (.refl _) (iht hlf.1) (ihb hlf.2)
  | forallE _ _ iht ihb =>
    simp only [letFree, Bool.and_eq_true] at hlf
    exact .forallE rfl (.refl _) (iht hlf.1) (ihb hlf.2)
  | letE _ _ _ _ _ _ => simp [letFree] at hlf
  | proj _ ih => exact .proj (ih hlf)

private theorem lamsAlong_letFree {elim : KLevel} :
    ∀ {n : Nat} {l p r : KExpr}, LamsAlong elim n l p r → letFree l = true → letFree r = true
  | 0, _, _, _, .zero, h => h
  | _ + 1, _, _, _, .succ _ _ hr, h => by
    simp only [letFree, Bool.and_eq_true] at h
    exact lamsAlong_letFree hr h.2

private theorem liftLooseBVars_eq_forallE {n c : Nat} {e d b : KExpr} {m : Ix.Kernel.BinderMeta}
    (h : e.liftLooseBVars n c = .forallE d b m) :
    ∃ d₀ b₀, e = .forallE d₀ b₀ m := by
  cases e with
  | bvar i => simp only [Expr.liftLooseBVars] at h; split at h <;> cases h
  | forallE d₀ b₀ m₀ =>
    simp only [Expr.liftLooseBVars, Expr.forallE.injEq] at h
    exact ⟨d₀, b₀, by rw [h.2.2]⟩
  | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ =>
    simp [Expr.liftLooseBVars] at h

private theorem consumeStar_forallE_eq {find? : KKey → Option (ConstantInfo .anon)}
    {d b a : KExpr} {m : Ix.Kernel.BinderMeta}
    (h : ConsumeStar find? (.forallE d b m) a) : a = .forallE d b m := by
  cases h with
  | refl => rfl
  | step hc _ => simp [consumeWrapper, Expr.getAppFn] at hc

/-- **Symmetric rule comparison from `RuleFollows`**: lifts `SymWrapT` from the recursor types to
the renamed rule right-hand sides. -/
theorem symWrapT_rule_of_ruleFollows {find? : KKey → Option (ConstantInfo .anon)}
    {f : KKey → KKey} {tyC tyW rhsC rhsW cbC cbW : KExpr}
    {nP nMot nMin minor nf : Nat} {elim : KLevel}
    (hty : SymWrapT find? tyC tyW) (hty_fix : tyC.renameConsts f = tyC)
    (hC : RuleFollows tyC nP nMot nMin minor nf elim rhsC cbC)
    (hW : RuleFollows tyW nP nMot nMin minor nf elim rhsW cbW)
    (hcb : ExprLvEq (cbC.renameConsts f) cbW)
    (hlfW : letFree rhsW = true) :
    SymWrapT find? (rhsC.renameConsts f) rhsW := by
  obtain ⟨afterC, mdomC, restC, sbC, mmC, hlam1C, hpeelC, hlam2C, hsbC⟩ := hC
  obtain ⟨afterW, mdomW, restW, sbW, mmW, hlam1W, hpeelW, hlam2W, hsbW⟩ := hW
  have hlam1C' : LamsAlong elim (nP + nMot + nMin) (rhsC.renameConsts f) tyC
      (afterC.renameConsts f) := by
    have h := lamsAlong_renameConsts f hlam1C
    rwa [hty_fix] at h
  have hpeelC' : peelForalls (nP + nMot + minor) tyC =
      some (.forallE (mdomC.renameConsts f) (restC.renameConsts f) mmC) := by
    have h := peelForalls_renameConsts f (nP + nMot + minor) hpeelC
    rwa [hty_fix] at h
  have hmdom_fix : mdomC.renameConsts f = mdomC := by
    have h := Option.some.inj (hpeelC'.symm.trans hpeelC)
    injection h
  have hlam2C' : LamsAlong elim nf (afterC.renameConsts f)
      (mdomC.liftLooseBVars (nMin - minor) 0) (sbC.renameConsts f) := by
    have h := lamsAlong_renameConsts f hlam2C
    rw [renameConsts_liftLooseBVars_wb, hmdom_fix] at h
    exact h
  have hsb_lv : ExprLvEq (sbC.renameConsts f) sbW :=
    ((exprLvEq_renameConsts f hsbC).trans hcb).trans hsbW.symm
  have hlf_sbW : letFree sbW = true := lamsAlong_letFree hlam2W (lamsAlong_letFree hlam1W hlfW)
  have hlf_sbC : letFree (sbC.renameConsts f) = true := by
    rw [letFree_of_exprLvEq hsb_lv]; exact hlf_sbW
  have hsb : SymWrapT find? (sbC.renameConsts f) sbW :=
    SymWrapT.of_wrapT ((exprLvEq_to_wrapT_empty hsb_lv hlf_sbC).mono_empty (find? := find?))
  have hafter : SymWrapT find? (afterC.renameConsts f) afterW := by
    cases nf with
    | zero => cases hlam2C; cases hlam2W; exact hsb
    | succ nf' =>
      have hpeel_s := symWrapT_peelForalls (nP + nMot + minor) hty hpeelC hpeelW
      have hdomC_fa : ∃ d b m, mdomC = .forallE d b m := by
        generalize hm : mdomC.liftLooseBVars (nMin - minor) 0 = mL at hlam2C
        cases hlam2C
        obtain ⟨d₀, b₀, heq⟩ := liftLooseBVars_eq_forallE hm
        exact ⟨d₀, b₀, _, heq⟩
      have hdomW_fa : ∃ d b m, mdomW = .forallE d b m := by
        generalize hm : mdomW.liftLooseBVars (nMin - minor) 0 = mL at hlam2W
        cases hlam2W
        obtain ⟨d₀, b₀, heq⟩ := liftLooseBVars_eq_forallE hm
        exact ⟨d₀, b₀, _, heq⟩
      have hdomM : SymWrapT find? mdomC mdomW := by
        cases hpeel_s with
        | forallEL _ hcs hd _ =>
          obtain ⟨d₀, b₀, m₀, rfl⟩ := hdomC_fa
          have ha := consumeStar_forallE_eq hcs; subst ha; exact hd
        | forallER _ hcs hd _ =>
          obtain ⟨d₀, b₀, m₀, rfl⟩ := hdomW_fa
          have ha := consumeStar_forallE_eq hcs; subst ha; exact hd
      exact symWrapT_of_lamsAlong (symWrapT_liftLooseBVars hdomM (nMin - minor) 0) hlam2C' hlam2W hsb
  exact symWrapT_of_lamsAlong hty hlam1C' hlam1W hafter

private theorem lamsAlong_to_lamDomAlong {elim : KLevel} :
    ∀ {n : Nat} {l p r : KExpr},
      LamsAlong elim n l p r → letFree l = true →
      LamDomAlong n l p r ∧ letFree r = true
  | 0, _, _, _, .zero, hlf => ⟨.zero, hlf⟩
  | _ + 1, _, _, _, .succ _ hdom hrest, hlf => by
    simp only [letFree, Bool.and_eq_true] at hlf
    obtain ⟨hL, hlfR⟩ := lamsAlong_to_lamDomAlong hrest hlf.2
    exact ⟨.succ (exprLvEq_to_wrapT_empty hdom hlf.1) hL, hlfR⟩

private theorem lamsAlong_to_stripLams {elim : KLevel} {n : Nat} {l p r : KExpr}
    (h : LamsAlong elim n l p r) : stripLams n l = some r := by
  induction h with
  | zero => rfl
  | succ _ _ _ ih => exact ih

private theorem stripLams_of_exprLvEq :
    ∀ (n : Nat) {e₁ e₂ r₂ : KExpr},
      ExprLvEq e₁ e₂ → stripLams n e₂ = some r₂ →
      ∃ r₁, stripLams n e₁ = some r₁ ∧ ExprLvEq r₁ r₂
  | 0, _, _, _, h, hs => by
    simp only [stripLams, Option.some.injEq] at hs; subst hs; exact ⟨_, rfl, h⟩
  | n + 1, _, _, _, h, hs => by
    cases h with
    | lam _ hb => exact stripLams_of_exprLvEq n hb hs
    | bvar | fvar | sort | const | app | forallE | letE | lit | proj => simp [stripLams] at hs

private theorem wrapT_empty_instantiateLevelParams (ps : List LevelParam) (us : List KLevel)
    {e₁ e₂ : KExpr}
    (h : WrapT (fun _ : KKey => (none : Option (ConstantInfo .anon))) e₁ e₂) :
    WrapT (fun _ : KKey => (none : Option (ConstantInfo .anon)))
      (e₁.instantiateLevelParams ps us) (e₂.instantiateLevelParams ps us) := by
  induction h with
  | bvar i => exact .bvar i
  | fvar i _ _ => exact .fvar i _ _
  | sort huv => exact .sort (level_eval_subst_congr ps us huv)
  | const hlv => exact .const (forall2_eval_subst ps us hlv)
  | lit l => exact .lit l
  | app _ _ ihf iha => exact .app ihf iha
  | lam hpw hs _ _ ihd ihb =>
    rcases hs.eq_of_empty with rfl
    exact .lam (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw])
      (.refl _) ihd ihb
  | forallE hpw hs _ _ ihd ihb =>
    rcases hs.eq_of_empty with rfl
    exact .forallE (show Level.substPW ps us _ = Level.substPW ps us _ by rw [hpw])
      (.refl _) ihd ihb
  | proj _ ih => exact .proj ih

private theorem lamDomAlong_instantiateLevelParams (ps : List LevelParam) (us : List KLevel)
    {n : Nat} {l p r : KExpr} (h : LamDomAlong n l p r) :
    LamDomAlong n (l.instantiateLevelParams ps us) (p.instantiateLevelParams ps us)
      (r.instantiateLevelParams ps us) := by
  induction h with
  | zero => exact .zero
  | succ hdom _ ih => exact .succ (wrapT_empty_instantiateLevelParams ps us hdom) ih

private theorem stripLams_instantiateLevelParams (ps : List LevelParam) (us : List KLevel) :
    ∀ (n : Nat) {e r : KExpr},
      stripLams n e = some r →
      stripLams n (e.instantiateLevelParams ps us) = some (r.instantiateLevelParams ps us)
  | 0, _, _, h => by simp only [stripLams, Option.some.injEq] at h ⊢; rw [h]
  | n + 1, .lam _ b _, _, h => stripLams_instantiateLevelParams ps us n h
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .forallE _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => by
    simp [stripLams] at h

private theorem liftLooseBVars_instantiateLevelParams_wb (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (n c : Nat),
      (e.liftLooseBVars n c).instantiateLevelParams ps us =
        (e.instantiateLevelParams ps us).liftLooseBVars n c
  | .bvar i, n, c => by simp only [Expr.liftLooseBVars, Expr.instantiateLevelParams]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_wb ps us f n c,
      liftLooseBVars_instantiateLevelParams_wb ps us a n c]
  | .lam t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_wb ps us t n c,
      liftLooseBVars_instantiateLevelParams_wb ps us b n (c + 1)]
  | .forallE t b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_wb ps us t n c,
      liftLooseBVars_instantiateLevelParams_wb ps us b n (c + 1)]
  | .letE t v b _, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_wb ps us t n c,
      liftLooseBVars_instantiateLevelParams_wb ps us v n c,
      liftLooseBVars_instantiateLevelParams_wb ps us b n (c + 1)]
  | .proj _ _ e, n, c => by
    simp [Expr.liftLooseBVars, Expr.instantiateLevelParams,
      liftLooseBVars_instantiateLevelParams_wb ps us e n c]

/-- The constructor offset `cbk + c` of any constructor `c < self.nctors` of entry `k` is strictly
below the total constructor count `ctorsBefore V es es.length`. -/
theorem ctorsBefore_add_lt_total {V : ReconView} :
    ∀ (es : List FlatEntry) (k cbk total : Nat) (ek : FlatEntry) (self : IndData) (c : Nat),
      es[k]? = some ek → V.ind ek.addr = some (some self) →
      ctorsBefore V es k = some cbk →
      ctorsBefore V es es.length = some total →
      c < self.nctors →
      cbk + c < total
  | [], _, _, _, _, _, _, hek, _, _, _, _ => by simp at hek
  | e :: rest, 0, cbk, total, ek, self, c, hek, hself, hcbk, htot, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hek
    subst hek
    simp only [ctorsBefore, Option.some.injEq] at hcbk
    subst hcbk
    simp only [List.length_cons, ctorsBefore, hself] at htot
    cases hr : ctorsBefore V rest rest.length with
    | none => simp [hr] at htot
    | some t' =>
      simp only [hr, Option.some.injEq] at htot
      omega
  | e :: rest, k + 1, cbk, total, ek, self, c, hek, hself, hcbk, htot, hc => by
    simp only [List.getElem?_cons_succ] at hek
    simp only [List.length_cons, ctorsBefore] at hcbk htot
    cases hi : V.ind e.addr with
    | none => simp [hi] at hcbk
    | some opt =>
      cases opt with
      | none => simp [hi] at hcbk
      | some i₀ =>
        simp only [hi] at hcbk htot
        cases hc' : ctorsBefore V rest k with
        | none => simp [hc'] at hcbk
        | some cb' =>
          cases ht' : ctorsBefore V rest rest.length with
          | none => simp [ht'] at htot
          | some t' =>
            simp only [hc', Option.some.injEq] at hcbk
            simp only [ht', Option.some.injEq] at htot
            have hlt := ctorsBefore_add_lt_total rest k cb' t' ek self c hek hself hc' ht' hc
            omega

private theorem letFree_instantiateLevelParams_wb (ps : List LevelParam) (us : List KLevel) :
    ∀ (e : KExpr), letFree (e.instantiateLevelParams ps us) = letFree e
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ | .letE _ _ _ _ => rfl
  | .app g a => by
    simp [Expr.instantiateLevelParams, letFree,
      letFree_instantiateLevelParams_wb ps us g, letFree_instantiateLevelParams_wb ps us a]
  | .lam t b _ => by
    simp [Expr.instantiateLevelParams, letFree,
      letFree_instantiateLevelParams_wb ps us t, letFree_instantiateLevelParams_wb ps us b]
  | .forallE t b _ => by
    simp [Expr.instantiateLevelParams, letFree,
      letFree_instantiateLevelParams_wb ps us t, letFree_instantiateLevelParams_wb ps us b]
  | .proj _ _ e => letFree_instantiateLevelParams_wb ps us e

private theorem stripLams_renameConsts_wb (f : KKey → KKey) :
    ∀ (n : Nat) {e r : KExpr},
      stripLams n e = some r → stripLams n (e.renameConsts f) = some (r.renameConsts f)
  | 0, _, _, h => by simp only [stripLams, Option.some.injEq] at h ⊢; rw [h]
  | n + 1, .lam _ b _, _, h => stripLams_renameConsts_wb f n h
  | _ + 1, .bvar _, _, h | _ + 1, .fvar _ _, _, h | _ + 1, .sort _, _, h
  | _ + 1, .const _ _, _, h | _ + 1, .app _ _, _, h | _ + 1, .forallE _ _ _, _, h
  | _ + 1, .letE _ _ _ _, _, h | _ + 1, .lit _, _, h | _ + 1, .proj _ _ _, _, h => by
    simp [stripLams] at h

/-- **Build `TwinRuleMatch` at level parameters `ps`** from `SymWrapT` on loaded types and
`RuleFollows` on both canonical and twin rules. -/
theorem twinRuleMatch_of_ruleFollows {find? : KKey → Option (ConstantInfo .anon)}
    {f : KKey → KKey} {ps : List LevelParam} (hperm : ps.Perm (List.range ps.length))
    {tyC_ld tyW_ld tyW' rC_rhs rhsC_ld rW'_rhs rhsW_ld cbC cbW : KExpr}
    {nP nMot nMin minor nf : Nat} {elim : KLevel}
    (hty_sym : SymWrapT find? tyC_ld tyW_ld)
    (htyC_fix : tyC_ld.renameConsts f = tyC_ld)
    (htyW_eq : Core.posOf ps tyW' = tyW_ld)
    (hrhsC_lv : ExprLvEq (Core.posOf ps rC_rhs) rhsC_ld)
    (hrhsW_eq : Core.posOf ps rW'_rhs = rhsW_ld)
    (hlfW : letFree rW'_rhs = true)
    (hmin_lt : minor < nMin)
    (hC : RuleFollows tyC_ld nP nMot nMin minor nf elim rhsC_ld cbC)
    (hW : RuleFollows tyW_ld nP nMot nMin minor nf elim rhsW_ld cbW)
    (hcb : ExprLvEq (cbC.renameConsts f) cbW) :
    TwinRuleMatch find? f tyW' rC_rhs rW'_rhs := by
  have hlfW_ld : letFree rhsW_ld = true := by
    rw [← hrhsW_eq]; unfold Core.posOf; rw [letFree_instantiateLevelParams_wb]; exact hlfW
  have hsym_ld : SymWrapT find? (rhsC_ld.renameConsts f) rhsW_ld :=
    symWrapT_rule_of_ruleFollows hty_sym htyC_fix hC hW hcb hlfW_ld
  have hsym_pos : SymWrapT find? (Core.posOf ps (rC_rhs.renameConsts f)) (Core.posOf ps rW'_rhs) := by
    rw [hrhsW_eq]
    unfold Core.posOf
    rw [← renameConsts_instantiateLevelParams]
    exact symWrapT_congr_exprLvEq_left (exprLvEq_renameConsts f hrhsC_lv) hsym_ld
  have hsym_fin : SymWrapT find? (rC_rhs.renameConsts f) rW'_rhs :=
    symWrapT_of_posOf_perm hperm hsym_pos
  obtain ⟨afterC, _, _, sbC_ld, _, hlam1C, _, hlam2C, hsbC⟩ := hC
  obtain ⟨afterW_pos, mdomW_pos, restW_pos, sbW_pos, mmW, hlam1W, hpeelW, hlam2W, hsbW⟩ := hW
  obtain ⟨hLD1_pos, hlf_afterW⟩ := lamsAlong_to_lamDomAlong hlam1W hlfW_ld
  obtain ⟨hLD2_pos, hlf_sbW⟩ := lamsAlong_to_lamDomAlong hlam2W hlf_afterW
  have hSC_ld : stripLams (nP + nMot + nMin + nf) rhsC_ld = some sbC_ld := by
    rw [Ix.Kernel.Semantics.stripLams_add, lamsAlong_to_stripLams hlam1C]
    exact lamsAlong_to_stripLams hlam2C
  obtain ⟨sbC_pos, hSC_pos, hsbC_pos_lv⟩ := stripLams_of_exprLvEq _ hrhsC_lv hSC_ld
  have hsb_pos_lv : ExprLvEq (sbC_pos.renameConsts f) sbW_pos :=
    ((exprLvEq_renameConsts f (hsbC_pos_lv.trans hsbC)).trans hcb).trans hsbW.symm
  have hlf_sbC_pos : letFree (sbC_pos.renameConsts f) = true := by
    rw [letFree_of_exprLvEq hsb_pos_lv]; exact hlf_sbW
  have hBase_pos : WrapT (fun _ : KKey => (none : Option (ConstantInfo .anon)))
      (sbC_pos.renameConsts f) sbW_pos :=
    exprLvEq_to_wrapT_empty hsb_pos_lv hlf_sbC_pos
  let inst : KExpr → KExpr := Expr.instantiateLevelParams (List.range ps.length) (ps.map .param)
  have hinst_tyW : tyW_ld.instantiateLevelParams (List.range ps.length) (ps.map .param) = tyW' := by
    rw [← htyW_eq]; exact Decl.posOf_perm_inv hperm tyW'
  have hinst_rhsW : rhsW_ld.instantiateLevelParams (List.range ps.length) (ps.map .param) = rW'_rhs := by
    rw [← hrhsW_eq]; exact Decl.posOf_perm_inv hperm rW'_rhs
  have hLD1 : LamDomAlong (nP + nMot + nMin) rW'_rhs tyW' (inst afterW_pos) := by
    have h := lamDomAlong_instantiateLevelParams (List.range ps.length) (ps.map .param) hLD1_pos
    rwa [hinst_rhsW, hinst_tyW] at h
  have hSC_base : stripLams (nP + nMot + nMin + nf) rC_rhs = some (inst sbC_pos) := by
    have h := stripLams_instantiateLevelParams (List.range ps.length) (ps.map .param) _ hSC_pos
    rwa [Decl.posOf_perm_inv hperm rC_rhs] at h
  have hSC : stripLams (nP + nMot + nMin + nf) (rC_rhs.renameConsts f) =
      some ((inst sbC_pos).renameConsts f) := by
    have h := stripLams_renameConsts_wb f (nP + nMot + nMin + nf) hSC_base
    exact h
  have hBase : WrapT (fun _ : KKey => (none : Option (ConstantInfo .anon)))
      ((inst sbC_pos).renameConsts f) (inst sbW_pos) := by
    have h := wrapT_empty_instantiateLevelParams (List.range ps.length) (ps.map .param) hBase_pos
    rw [← renameConsts_instantiateLevelParams] at h
    exact h
  refine ⟨hsym_fin, nP + nMot + nMin, nf, inst afterW_pos, inst sbW_pos, (inst sbC_pos).renameConsts f,
    hLD1, ?_, hSC, hBase⟩
  right
  have hpeelW_inst : peelForalls (nP + nMot + minor) tyW' =
      some (.forallE (inst mdomW_pos) (inst restW_pos)
        { mmW with pw := Level.substPW (List.range ps.length) (ps.map .param) mmW.pw }) := by
    have h := peelForalls_instantiateLevelParams (List.range ps.length) (ps.map .param)
      (nP + nMot + minor) tyW_ld
    rw [hinst_tyW, hpeelW] at h
    exact h
  obtain ⟨bs, hStripP⟩ := (stripPis_iff_peelForalls _ _ _).mp hpeelW_inst
  have hLD2 : LamDomAlong nf (inst afterW_pos)
      ((inst mdomW_pos).liftLooseBVars ((nP + nMot + nMin) - (nP + nMot + minor)) 0)
      (inst sbW_pos) := by
    have hsub : (nP + nMot + nMin) - (nP + nMot + minor) = nMin - minor := by omega
    rw [hsub, ← liftLooseBVars_instantiateLevelParams_wb]
    exact lamDomAlong_instantiateLevelParams (List.range ps.length) (ps.map .param) hLD2_pos
  exact ⟨nP + nMot + minor, bs, inst mdomW_pos, inst restW_pos, _, by omega, hStripP, hLD2⟩

/-! ### `allLevelParamsDefined` and `constsResolve` from `TwinRuleMatch` -/

private def binderPWDefinedWb (lps : List LevelParam) : KExpr → Bool
  | .bvar _ | .sort _ | .const _ _ | .lit _ => true
  | .fvar _ ty => binderPWDefinedWb lps ty
  | .app f a => binderPWDefinedWb lps f && binderPWDefinedWb lps a
  | .lam ty b m | .forallE ty b m =>
    (binderPWDefinedWb lps ty && binderPWDefinedWb lps b) && m.pw.paramsDefined lps
  | .letE ty v b _ =>
    (binderPWDefinedWb lps ty && binderPWDefinedWb lps v) && binderPWDefinedWb lps b
  | .proj _ _ e => binderPWDefinedWb lps e

private theorem binderPWDefinedWb_of_allLPD {lps : List LevelParam} :
    ∀ (e : KExpr), e.allLevelParamsDefined lps = true → binderPWDefinedWb lps e = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ ty, h => binderPWDefinedWb_of_allLPD ty h
  | .app f a, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [binderPWDefinedWb, Bool.and_eq_true]
    exact ⟨binderPWDefinedWb_of_allLPD f h.1, binderPWDefinedWb_of_allLPD a h.2⟩
  | .lam ty b m, h | .forallE ty b m, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [binderPWDefinedWb, Bool.and_eq_true]
    exact ⟨⟨binderPWDefinedWb_of_allLPD ty h.1.1, binderPWDefinedWb_of_allLPD b h.1.2⟩, h.2⟩
  | .letE ty v b _, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [binderPWDefinedWb, Bool.and_eq_true]
    exact ⟨⟨binderPWDefinedWb_of_allLPD ty h.1.1, binderPWDefinedWb_of_allLPD v h.1.2⟩,
      binderPWDefinedWb_of_allLPD b h.2⟩
  | .proj _ _ e, h => binderPWDefinedWb_of_allLPD e h

private theorem binderPWDefinedWb_liftLooseBVars (lps : List LevelParam) (n : Nat) :
    ∀ (e : KExpr) (c : Nat), binderPWDefinedWb lps (e.liftLooseBVars n c) = binderPWDefinedWb lps e
  | .bvar i, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp [Expr.liftLooseBVars, binderPWDefinedWb,
      binderPWDefinedWb_liftLooseBVars lps n f c, binderPWDefinedWb_liftLooseBVars lps n a c]
  | .lam ty b _, c | .forallE ty b _, c => by
    simp [Expr.liftLooseBVars, binderPWDefinedWb,
      binderPWDefinedWb_liftLooseBVars lps n ty c, binderPWDefinedWb_liftLooseBVars lps n b (c + 1)]
  | .letE ty v b _, c => by
    simp [Expr.liftLooseBVars, binderPWDefinedWb,
      binderPWDefinedWb_liftLooseBVars lps n ty c, binderPWDefinedWb_liftLooseBVars lps n v c,
      binderPWDefinedWb_liftLooseBVars lps n b (c + 1)]
  | .proj _ _ e, c => binderPWDefinedWb_liftLooseBVars lps n e c

private theorem binderPWDefinedWb_of_wrapT_empty {lps : List LevelParam} {e₁ e₂ : KExpr}
    (h : WrapT (fun _ : KKey => (none : Option (ConstantInfo .anon))) e₁ e₂) :
    e₂.hasFvar = false → binderPWDefinedWb lps e₁ = true → binderPWDefinedWb lps e₂ = true := by
  induction h with
  | bvar | sort | const | lit => intro _ _; rfl
  | fvar => intro hfv _; simp [Expr.hasFvar] at hfv
  | app _ _ ihf iha =>
    intro hfv h1
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [binderPWDefinedWb, Bool.and_eq_true] at h1 ⊢
    exact ⟨ihf hfv.1 h1.1, iha hfv.2 h1.2⟩
  | lam hpw hs _ _ ihd ihb =>
    rcases hs.eq_of_empty with rfl
    intro hfv h1
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [binderPWDefinedWb, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨ihd hfv.1 h1.1.1, ihb hfv.2 h1.1.2⟩, hpw ▸ h1.2⟩
  | forallE hpw hs _ _ ihd ihb =>
    rcases hs.eq_of_empty with rfl
    intro hfv h1
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [binderPWDefinedWb, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨ihd hfv.1 h1.1.1, ihb hfv.2 h1.1.2⟩, hpw ▸ h1.2⟩
  | proj _ ih => intro hfv h1; exact ih hfv h1

private theorem hasFvar_of_lamDomAlong_wb :
    ∀ {n : Nat} {l p r : KExpr}, LamDomAlong n l p r → l.hasFvar = false → r.hasFvar = false
  | 0, _, _, _, .zero, h => h
  | _ + 1, _, _, _, .succ _ hrest, h => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact hasFvar_of_lamDomAlong_wb hrest h.2

private theorem binderPWDefinedWb_of_stripLams {lps : List LevelParam} :
    ∀ (n : Nat) {e r : KExpr},
      stripLams n e = some r → binderPWDefinedWb lps e = true → binderPWDefinedWb lps r = true
  | 0, _, _, h, hb => by simp only [stripLams, Option.some.injEq] at h; subst h; exact hb
  | n + 1, .lam _ b _, _, h, hb => by
    simp only [binderPWDefinedWb, Bool.and_eq_true] at hb
    exact binderPWDefinedWb_of_stripLams n h hb.1.2
  | _ + 1, .bvar _, _, h, _ | _ + 1, .fvar _ _, _, h, _ | _ + 1, .sort _, _, h, _
  | _ + 1, .const _ _, _, h, _ | _ + 1, .app _ _, _, h, _ | _ + 1, .forallE _ _ _, _, h, _
  | _ + 1, .letE _ _ _ _, _, h, _ | _ + 1, .lit _, _, h, _ | _ + 1, .proj _ _ _, _, h, _ => by
    simp [stripLams] at h

private theorem binderPWDefinedWb_of_stripPis {lps : List LevelParam} :
    ∀ (n : Nat) {e r : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis n = some (bs, r) → binderPWDefinedWb lps e = true → binderPWDefinedWb lps r = true
  | 0, _, _, _, h, hb => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hb
  | n + 1, _, _, _, h, hb => by
    obtain ⟨_, _, _, _, rfl, hs0⟩ := Ix.Kernel.Semantics.stripPis_succ_inv h
    simp only [binderPWDefinedWb, Bool.and_eq_true] at hb
    exact binderPWDefinedWb_of_stripPis n hs0 hb.1.2

private theorem symWrapT_of_stripLams {find? : KKey → Option (ConstantInfo .anon)} :
    ∀ {n : Nat} {lC lW p rC rW : KExpr},
      SymWrapT find? lC lW → LamDomAlong n lW p rW → stripLams n lC = some rC →
      SymWrapT find? rC rW
  | 0, _, _, _, _, _, hS, .zero, hSC => by
    simp only [stripLams, Option.some.injEq] at hSC; subst hSC; exact hS
  | _ + 1, _, _, _, _, _, hS, .succ _ hrest, hSC => by
    cases hS with
    | lamL _ _ _ hb | lamR _ _ _ hb => exact symWrapT_of_stripLams hb hrest hSC

private theorem binderPWDefinedWb_of_lamDomAlong {find? : KKey → Option (ConstantInfo .anon)}
    {lps : List LevelParam} :
    ∀ {n : Nat} {lC lW p rW : KExpr},
      SymWrapT find? lC lW → LamDomAlong n lW p rW → lW.hasFvar = false →
      binderPWDefinedWb lps p = true → binderPWDefinedWb lps lC = true →
      binderPWDefinedWb lps rW = true → binderPWDefinedWb lps lW = true
  | 0, _, _, _, _, _, .zero, _, _, _, hr => hr
  | _ + 1, _, _, _, _, hSym, .succ hdom hrest, hfv, hP, hC, hr => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [binderPWDefinedWb, Bool.and_eq_true] at hP ⊢
    cases hSym with
    | lamL hpw _ _ hb | lamR hpw _ _ hb =>
      simp only [binderPWDefinedWb, Bool.and_eq_true] at hC
      exact ⟨⟨binderPWDefinedWb_of_wrapT_empty hdom.symm_empty hfv.1 hP.1.1,
        binderPWDefinedWb_of_lamDomAlong hb hrest hfv.2 hP.1.2 hC.1.2 hr⟩, hpw ▸ hC.2⟩

private theorem allLPD_liftLooseBVars_wb {lps : List LevelParam} (n : Nat) :
    ∀ (e : KExpr) (c : Nat),
      e.allLevelParamsDefined lps = true → (e.liftLooseBVars n c).allLevelParamsDefined lps = true
  | .bvar i, c, _ => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _, h | .sort _, _, h | .const _ _, _, h | .lit _, _, h => h
  | .app f a, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLPD_liftLooseBVars_wb n f c h.1, allLPD_liftLooseBVars_wb n a c h.2⟩
  | .lam ty b _, c, h | .forallE ty b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_liftLooseBVars_wb n ty c h.1.1, allLPD_liftLooseBVars_wb n b (c + 1) h.1.2⟩, h.2⟩
  | .letE ty v b _, c, h => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.liftLooseBVars, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_liftLooseBVars_wb n ty c h.1.1, allLPD_liftLooseBVars_wb n v c h.1.2⟩,
      allLPD_liftLooseBVars_wb n b (c + 1) h.2⟩
  | .proj _ _ e, c, h => allLPD_liftLooseBVars_wb n e c h

private theorem allLPD_instantiate1Lift_wb {lps : List LevelParam} {v : KExpr}
    (hv : v.allLevelParamsDefined lps = true) :
    ∀ (b : KExpr) (j : Nat),
      b.allLevelParamsDefined lps = true →
      (b.instantiate1Lift v j).allLevelParamsDefined lps = true
  | .bvar i, j, _ => by
    simp only [Expr.instantiate1Lift]
    split
    · exact allLPD_liftLooseBVars_wb j v 0 hv
    · split <;> rfl
  | .fvar _ _, _, hb | .sort _, _, hb | .const _ _, _, hb | .lit _, _, hb => hb
  | .app f a, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨allLPD_instantiate1Lift_wb hv f j hb.1, allLPD_instantiate1Lift_wb hv a j hb.2⟩
  | .lam ty b _, j, hb | .forallE ty b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_instantiate1Lift_wb hv ty j hb.1.1,
      allLPD_instantiate1Lift_wb hv b (j + 1) hb.1.2⟩, hb.2⟩
  | .letE ty val b _, j, hb => by
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1Lift, Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨allLPD_instantiate1Lift_wb hv ty j hb.1.1, allLPD_instantiate1Lift_wb hv val j hb.1.2⟩,
      allLPD_instantiate1Lift_wb hv b (j + 1) hb.2⟩
  | .proj _ _ e, j, hb => allLPD_instantiate1Lift_wb hv e j hb

private theorem annotates_allLPD_of_binderPW_wb {lps : List LevelParam} {e' e₀ : KExpr}
    (hann : IxVM.Consistency.Annotates e' e₀) (hpw : binderPWDefinedWb lps e' = true)
    (hdef : e₀.allLevelParamsDefined lps = true) :
    e'.allLevelParamsDefined lps = true := by
  induction hann with
  | bvar | sort | const | lit => exact hdef
  | fvar _ ih => exact ih hpw hdef
  | app _ _ ihf iha =>
    simp only [binderPWDefinedWb, Bool.and_eq_true] at hpw
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨ihf hpw.1 hdef.1, iha hpw.2 hdef.2⟩
  | lam _ _ iht ihb | forallE _ _ iht ihb =>
    simp only [binderPWDefinedWb, Bool.and_eq_true] at hpw
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef ⊢
    exact ⟨⟨iht hpw.1.1 hdef.1.1, ihb hpw.1.2 hdef.1.2⟩, hpw.2⟩
  | proj _ ihe => exact ihe hpw hdef
  | letE _ ih =>
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hdef
    exact ih hpw (allLPD_instantiate1Lift_wb hdef.1.2 _ 0 hdef.2)

/-- **Level-parameter scoping from `TwinRuleMatch` and `Annotates`**: `rW'.rhs` gets its binder
`pw` bits from `tyW'` and `rC.rhs.renameConsts f` via `TwinRuleMatch`, and its sorts/constants from
the unannotated rule `rW.rhs`. -/
theorem allLevelParamsDefined_of_twinRuleMatch {find? : KKey → Option (ConstantInfo .anon)}
    {f : KKey → KKey} {lps : List LevelParam} {tyW' rhsC rhsW' rhsW₀ : KExpr}
    (hMatch : TwinRuleMatch find? f tyW' rhsC rhsW')
    (hfvW' : rhsW'.hasFvar = false)
    (hty_lpd : tyW'.allLevelParamsDefined lps = true)
    (hrhsC_lpd : (rhsC.renameConsts f).allLevelParamsDefined lps = true)
    (hann : IxVM.Consistency.Annotates rhsW' rhsW₀)
    (hrhsW₀_lpd : rhsW₀.allLevelParamsDefined lps = true) :
    rhsW'.allLevelParamsDefined lps = true := by
  obtain ⟨hSym, nPre, nf, afterW, sbW, sbC, hLam1, hMid, hSC, hBase⟩ := hMatch
  have hpw_ty := binderPWDefinedWb_of_allLPD tyW' hty_lpd
  have hpw_C := binderPWDefinedWb_of_allLPD (rhsC.renameConsts f) hrhsC_lpd
  have hpw_sbC := binderPWDefinedWb_of_stripLams (nPre + nf) hSC hpw_C
  have hfv_afterW := hasFvar_of_lamDomAlong_wb hLam1 hfvW'
  have hpw_W' : binderPWDefinedWb lps rhsW' = true := by
    rcases hMid with ⟨rfl, rfl⟩ | ⟨iMin, bs, mdomW, restW, mmW, _, hStripP, hLam2⟩
    · have hpw_sbW := binderPWDefinedWb_of_wrapT_empty hBase hfv_afterW hpw_sbC
      exact binderPWDefinedWb_of_lamDomAlong hSym hLam1 hfvW' hpw_ty hpw_C hpw_sbW
    · have hfv_sbW := hasFvar_of_lamDomAlong_wb hLam2 hfv_afterW
      have hpw_sbW := binderPWDefinedWb_of_wrapT_empty hBase hfv_sbW hpw_sbC
      rw [Ix.Kernel.Semantics.stripLams_add] at hSC
      cases hSC1 : stripLams nPre (rhsC.renameConsts f) with
      | none => rw [hSC1] at hSC; cases hSC
      | some afterC =>
        have hSym_after := symWrapT_of_stripLams hSym hLam1 hSC1
        have hpw_afterC := binderPWDefinedWb_of_stripLams nPre hSC1 hpw_C
        have hpw_peel := binderPWDefinedWb_of_stripPis iMin hStripP hpw_ty
        simp only [binderPWDefinedWb, Bool.and_eq_true] at hpw_peel
        have hpw_mdomL : binderPWDefinedWb lps (mdomW.liftLooseBVars (nPre - iMin) 0) = true := by
          rw [binderPWDefinedWb_liftLooseBVars]; exact hpw_peel.1.1
        have hpw_afterW := binderPWDefinedWb_of_lamDomAlong hSym_after hLam2 hfv_afterW
          hpw_mdomL hpw_afterC hpw_sbW
        exact binderPWDefinedWb_of_lamDomAlong hSym hLam1 hfvW' hpw_ty hpw_C hpw_afterW
  exact annotates_allLPD_of_binderPW_wb hann hpw_W' hrhsW₀_lpd

private theorem constsResolve_liftLooseBVars_wb (env : Ix.Kernel.Env .anon) (n : Nat) :
    ∀ (e : KExpr) (c : Nat), (e.liftLooseBVars n c).constsResolve env = e.constsResolve env
  | .bvar i, c => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, c => by
    simp [Expr.liftLooseBVars, Expr.constsResolve,
      constsResolve_liftLooseBVars_wb env n f c, constsResolve_liftLooseBVars_wb env n a c]
  | .lam ty b _, c | .forallE ty b _, c => by
    simp [Expr.liftLooseBVars, Expr.constsResolve,
      constsResolve_liftLooseBVars_wb env n ty c, constsResolve_liftLooseBVars_wb env n b (c + 1)]
  | .letE ty v b _, c => by
    simp [Expr.liftLooseBVars, Expr.constsResolve,
      constsResolve_liftLooseBVars_wb env n ty c, constsResolve_liftLooseBVars_wb env n v c,
      constsResolve_liftLooseBVars_wb env n b (c + 1)]
  | .proj _ _ e, c => by
    simp [Expr.liftLooseBVars, Expr.constsResolve, constsResolve_liftLooseBVars_wb env n e c]

private theorem constsResolve_of_wrapT_empty {env : Ix.Kernel.Env .anon} {e₁ e₂ : KExpr}
    (h : WrapT (fun _ : KKey => (none : Option (ConstantInfo .anon))) e₁ e₂) :
    e₂.hasFvar = false → e₁.constsResolve env = true → e₂.constsResolve env = true := by
  induction h with
  | bvar | sort => intro _ _; rfl
  | const | lit => intro _ h1; exact h1
  | fvar => intro hfv _; simp [Expr.hasFvar] at hfv
  | app _ _ ihf iha =>
    intro hfv h1
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.constsResolve, Bool.and_eq_true] at h1 ⊢
    exact ⟨ihf hfv.1 h1.1, iha hfv.2 h1.2⟩
  | lam _ hs _ _ ihd ihb =>
    rcases hs.eq_of_empty with rfl
    intro hfv h1
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.constsResolve, Bool.and_eq_true] at h1 ⊢
    exact ⟨ihd hfv.1 h1.1, ihb hfv.2 h1.2⟩
  | forallE _ hs _ _ ihd ihb =>
    rcases hs.eq_of_empty with rfl
    intro hfv h1
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.constsResolve, Bool.and_eq_true] at h1 ⊢
    exact ⟨ihd hfv.1 h1.1, ihb hfv.2 h1.2⟩
  | proj _ ih =>
    intro hfv h1
    simp only [Expr.constsResolve, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, ih hfv h1.2⟩

private theorem constsResolve_of_stripLams_wb {env : Ix.Kernel.Env .anon} :
    ∀ (n : Nat) {e r : KExpr},
      stripLams n e = some r → e.constsResolve env = true → r.constsResolve env = true
  | 0, _, _, h, hc => by simp only [stripLams, Option.some.injEq] at h; subst h; exact hc
  | n + 1, .lam _ b _, _, h, hc => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    exact constsResolve_of_stripLams_wb n h hc.2
  | _ + 1, .bvar _, _, h, _ | _ + 1, .fvar _ _, _, h, _ | _ + 1, .sort _, _, h, _
  | _ + 1, .const _ _, _, h, _ | _ + 1, .app _ _, _, h, _ | _ + 1, .forallE _ _ _, _, h, _
  | _ + 1, .letE _ _ _ _, _, h, _ | _ + 1, .lit _, _, h, _ | _ + 1, .proj _ _ _, _, h, _ => by
    simp [stripLams] at h

private theorem constsResolve_of_stripPis_wb {env : Ix.Kernel.Env .anon} :
    ∀ (n : Nat) {e r : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis n = some (bs, r) → e.constsResolve env = true → r.constsResolve env = true
  | 0, _, _, _, h, hc => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hc
  | n + 1, _, _, _, h, hc => by
    obtain ⟨_, _, _, _, rfl, hs0⟩ := Ix.Kernel.Semantics.stripPis_succ_inv h
    simp only [Expr.constsResolve, Bool.and_eq_true] at hc
    exact constsResolve_of_stripPis_wb n hs0 hc.2

private theorem constsResolve_of_lamDomAlong {env : Ix.Kernel.Env .anon} :
    ∀ {n : Nat} {lW p rW : KExpr},
      LamDomAlong n lW p rW → lW.hasFvar = false →
      p.constsResolve env = true → rW.constsResolve env = true → lW.constsResolve env = true
  | 0, _, _, _, .zero, _, _, hr => hr
  | _ + 1, _, _, _, .succ hdom hrest, hfv, hP, hr => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    simp only [Expr.constsResolve, Bool.and_eq_true] at hP ⊢
    exact ⟨constsResolve_of_wrapT_empty hdom.symm_empty hfv.1 hP.1,
      constsResolve_of_lamDomAlong hrest hfv.2 hP.2 hr⟩

/-- **Constant resolution from `TwinRuleMatch`**: every constant in `rW'.rhs` resolves in `envSelf`
whenever `tyW'` and `rC.rhs.renameConsts f` resolve in `envSelf`. -/
theorem constsResolve_of_twinRuleMatch {find? : KKey → Option (ConstantInfo .anon)}
    {envSelf : Ix.Kernel.Env .anon} {f : KKey → KKey} {tyW' rhsC rhsW' : KExpr}
    (hMatch : TwinRuleMatch find? f tyW' rhsC rhsW')
    (hfvW' : rhsW'.hasFvar = false)
    (hty_cr : tyW'.constsResolve envSelf = true)
    (hrhsC_cr : (rhsC.renameConsts f).constsResolve envSelf = true) :
    rhsW'.constsResolve envSelf = true := by
  obtain ⟨_, nPre, nf, afterW, sbW, sbC, hLam1, hMid, hSC, hBase⟩ := hMatch
  have hcr_sbC := constsResolve_of_stripLams_wb (nPre + nf) hSC hrhsC_cr
  have hfv_afterW := hasFvar_of_lamDomAlong_wb hLam1 hfvW'
  rcases hMid with ⟨rfl, rfl⟩ | ⟨iMin, bs, mdomW, restW, mmW, _, hStripP, hLam2⟩
  · have hcr_sbW := constsResolve_of_wrapT_empty hBase hfv_afterW hcr_sbC
    exact constsResolve_of_lamDomAlong hLam1 hfvW' hty_cr hcr_sbW
  · have hfv_sbW := hasFvar_of_lamDomAlong_wb hLam2 hfv_afterW
    have hcr_sbW := constsResolve_of_wrapT_empty hBase hfv_sbW hcr_sbC
    have hcr_peel := constsResolve_of_stripPis_wb iMin hStripP hty_cr
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr_peel
    have hcr_mdomL : (mdomW.liftLooseBVars (nPre - iMin) 0).constsResolve envSelf = true := by
      rw [constsResolve_liftLooseBVars_wb]; exact hcr_peel.1
    have hcr_afterW := constsResolve_of_lamDomAlong hLam2 hfv_afterW hcr_mdomL hcr_sbW
    exact constsResolve_of_lamDomAlong hLam1 hfvW' hty_cr hcr_afterW

end IxVM.Refinement.Typing.TwinFamily
