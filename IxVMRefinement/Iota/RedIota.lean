import IxVMRefinement.Iota.Major
import IxVMRefinement.Iota.RecKernel

/-! # `red_iota`: `Red.iota` on a prepared major

The step fires the rule IxVM finds by the major's constructor index; `Red.iota` looks the rule
up by the constructor's key. The two agree: the record at the inductive-projection address IxVM
computes from the constructor's block and index (`compute_iprj_addr`, the major premise's head by
the circuit's guard) is that projection record, the major premise's head has a record
(`EnvFacts.recMajorRecord`), so `EnvFacts.recRules` keys rule `j` by constructor `j` of that
member, which is the loaded constructor's key (its name). The rest of `Red.iota`'s premises are
read off the circuit's comparisons (`iota_cmp`), its certificates (`iota_certs`) and the store's
shape of a rule's major premise: a plain rule's from `EnvFacts.recPlain`, a nested rule's from
the store invariant (`EnvFacts.store`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open Ix.Kernel.Rules (Red DefEqList)
open Ix.Kernel.Expr (instantiateList instantiateList_nil)
open IxVM.Refinement.KernelLevels (RepKLevel)

set_option linter.unusedVariables false

/-! ## The spine before the major premise -/

theorem params_inst {As : List KExpr} (hAc : ∀ a ∈ As, a.looseBVarsBounded 0 = true)
    {n m : Nat} (hn : n ≤ m) (hm : m ≤ As.length) :
    ((List.range n).map fun i => (Ix.Kernel.Expr.bvar (m - 1 - i)).instantiateList
      (As.take m).reverse 0) = As.take n := by
  have hc : ∀ v ∈ (As.take m).reverse, v.looseBVarsBounded 0 = true := fun v hv =>
    hAc v (List.mem_of_mem_take (List.mem_reverse.mp hv))
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range]
    rw [instList_bvar (j := m - 1 - i) hc (by simp; omega), List.getElem_reverse]
    simp only [List.getElem_take]
    congr 1
    simp only [List.length_take]
    omega

theorem indices_inst {As : List KExpr} (hAc : ∀ a ∈ As, a.looseBVarsBounded 0 = true)
    {r m : Nat} (hr : r ≤ m) (hm : m ≤ As.length) :
    ((List.range (m - r)).map fun i => (Ix.Kernel.Expr.bvar (m - r - 1 - i)).instantiateList
      (As.take m).reverse 0) = (As.take m).drop r := by
  have hc : ∀ v ∈ (As.take m).reverse, v.looseBVarsBounded 0 = true := fun v hv =>
    hAc v (List.mem_of_mem_take (List.mem_reverse.mp hv))
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
    rw [instList_bvar (j := m - r - 1 - i) hc (by simp; omega), List.getElem_reverse]
    simp only [List.getElem_take]
    congr 1
    simp only [List.length_take]
    omega

theorem piDomAt_of_stripPis : ∀ (n : Nat) (T : KExpr) {pre : List (KExpr × Ix.Kernel.BinderMeta)}
    {dom body : KExpr} {bm : Ix.Kernel.BinderMeta},
    T.stripPis n = some (pre, .forallE dom body bm) → piDomAt n T = some dom
  | 0, T, pre, dom, body, bm, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  | n + 1, T, pre, dom, body, bm, h => by
    cases T with
    | forallE ty b m =>
      cases hs : b.stripPis n with
      | none => simp [Ix.Kernel.Expr.stripPis, hs] at h
      | some pr =>
        obtain ⟨bs, e⟩ := pr
        simp only [Ix.Kernel.Expr.stripPis, hs, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact piDomAt_of_stripPis n b hs
    | _ => simp [Ix.Kernel.Expr.stripPis] at h

/-- The domain of the major premise, instantiated at the recursor's levels and the spine
before it. -/
theorem major_dom_inst {T D : KExpr} {mI : Nat} {ks : List Ix.Kernel.LevelParam}
    {us : List KLevel} {As : List KExpr} (hD : piDomAt mI T = some D) (hm : mI ≤ As.length) :
    Specs.Whnf.piDomInst (T.instantiateLevelParams ks us) (As.take mI) mI =
      some ((D.instantiateLevelParams ks us).instantiateList (As.take mI).reverse 0) := by
  rw [piDomInst_of_piDomAt mI _ (As.take mI) _ (piDomAt_instLP ks us mI T D hD)
    (by simp; omega), List.take_take, Nat.min_self]

theorem find_name {env : Ix.Kernel.Env .anon} {k : KKey} {ci : Ix.Kernel.ConstantInfo .anon}
    (h : env.find? k = some ci) : ci.name = k := by
  have := List.find?_some h
  simpa using this

theorem val_toUInt64_toNat (i : F) : ((ZMod.val i).toUInt64).toNat = ZMod.val i := by
  simp only [UInt64.toNat_ofNat', Nat.toUInt64_eq]
  have : ZMod.val i < 18446744069414584321 := ZMod.val_lt i
  rw [Nat.mod_eq_of_lt (by omega)]

theorem ite3_one {a b c : Prop} [Decidable a] [Decidable b] [Decidable c]
    (h : (if a then (1 : F) else 0) * (if b then 1 else 0) * (if c then 1 else 0) = 1) :
    a ∧ b ∧ c := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp_all

theorem tml_lbb {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {As : List KExpr} {p : SourceValue F} (hAs : TmL κ d Γ h As p) :
    ∀ a ∈ As, a.looseBVarsBounded 0 = true := by
  induction hAs with
  | nil _ => intro a ha; cases ha
  | cons _ hx _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Tm.looseBVarsBounded hx
    · exact ih a ha

/-- A loaded `Ctor` constant's counts, key and type. -/
theorem CIRep.ctor_fields {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty blk ind cidx np nf u : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon}
    (r : CIRep κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u]) ci) :
    ∃ cv nP nF, ci = .ctorInfo cv nP nF ∧ ValRep κ h nl ty cv ∧ np = .field (nP : F) ∧
      nf = .field (nF : F) ∧ (nP < 72057594037927936 ∧ nF < 72057594037927936) ∧
      ∃ (b : Bytes.Address) (i j : F), Bytes.RepAddressRef addrTy h b blk ∧ ind = .field i ∧
        cidx = .field j ∧ cv.name = κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j)) := by
  generalize hv : (Value.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u] :
    SourceValue F) = v at r
  cases r
  case ctor hvr hnp hnf hcounts hkey =>
    injection hv with _ _ hl
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨_, _, _, rfl, hvr, hnp, hnf, hcounts, hkey⟩
  all_goals (injection hv with _ hc' _; exact absurd hc' (by decide))

/-! ## The kernel step -/

/-- **`Red.iota` from the circuit's checks**: the recursor stored at `k` and its rule `rl` for
the major's constructor (`rl.ctor`), with the comparisons `iota_cmp` makes and the
certificates `iota_certs` gives, fire. -/
theorem iota_fire (c : Ctx) (hc : CoreFacts c) {d : Nat} {k : KKey}
    {cv : Ix.Kernel.ConstantVal .anon} {mI rP : Nat}
    {rls : List (Ix.Kernel.RecRule .anon)} {rl : Ix.Kernel.RecRule .anon} {us usj : List KLevel}
    {cvj : Ix.Kernel.ConstantVal .anon} {nP nF : Nat} {As MA : List KExpr}
    (hfind : c.env.find? k = some (.recInfo cv mI rP rls)) (hrl : rl ∈ rls)
    (hcj : c.env.find? rl.ctor = some (.ctorInfo cvj nP nF))
    (hlen : us.length = cv.levelParams.length) (hAl : mI + 1 ≤ As.length)
    (hAc : ∀ a ∈ As, a.looseBVarsBounded 0 = true) (hMA : MA.length = nP + nF)
    (hred : Red c.env d (As.getD mI (.bvar 0))
      (Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA))
    (hcmp : ∃ (MD : KExpr) (k' : KKey) (mus : List KLevel),
      Specs.Whnf.piDomInst (cv.type.instantiateLevelParams cv.levelParams us) (As.take mI) mI =
        some MD ∧ MD.getAppFn = .const k' mus ∧ LvEqList usj mus ∧
      DefEqList c.env d (MA.take nP) (MD.getAppArgs.take nP) ∧
      (mI ≠ rP → ∃ RES, Ix.Kernel.piResidual
          (cvj.type.instantiateLevelParams cvj.levelParams usj) MA = some RES ∧
        DefEqList c.env d (RES.getAppArgs.drop nP) (MD.getAppArgs.drop nP)))
    (hc1 : Specs.Whnf.CertsR c.env d true (cv.type.instantiateLevelParams cv.levelParams us)
      (As.take mI ++ [Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA]))
    (hc2 : Specs.Whnf.CertsR c.env d true (cvj.type.instantiateLevelParams cvj.levelParams usj)
      MA) :
    Red c.env d (Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1)))
      (Ix.Kernel.Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (As.take rP ++ MA.drop nP)) := by
  have hst := hc.env.store
  obtain ⟨hnd, hfire, -⟩ := hc.env.recRules k cv mI rP rls hfind
  obtain ⟨hni, cvj', nF', hcj'⟩ := hfire rl hrl
  rw [hcj] at hcj'
  obtain ⟨rfl, hnP, rfl⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj (Option.some.inj hcj')
  subst hnP
  obtain ⟨-, hnF, harity⟩ := hc.env.ruleCtorArity k cv mI rP rls hfind rl hrl cvj _ _ hcj
  have hrecAr := hc.env.recArity k cv mI rP rls hfind rl hrl
  obtain ⟨MD, k', mus, hMD, hMDfn, hmus, hpar, hidx⟩ := hcmp
  obtain ⟨cvj2, -, hplain, hpinlen, -, -⟩ := (hst.rec_ctors k cv mI rP rls hfind rl hrl).1
  obtain ⟨-, -, -, -, -, h6, -⟩ := hst.wf _ (List.mem_of_find?_eq_some hfind)
  -- the major premise's domain: its head levels, its parameters, its indices
  have key : ∃ (D : KExpr) (T : KKey) (ls0 : List KLevel) (P0 : List KExpr),
      piDomAt mI cv.type = some D ∧ D.getAppFn = .const T ls0 ∧
      D.getAppArgs = P0 ++ (List.range (mI - rP)).map (fun i => .bvar (mI - rP - 1 - i)) ∧
      P0.length = rl.ctorParams ∧ rP ≤ mI ∧
      ((∀ φ, Ix.Kernel.Level.EvalEqList φ usj
          (ls0.map (Ix.Kernel.Level.subst cv.levelParams us))) →
        ∀ φ, Ix.Kernel.Level.EvalEqList φ usj
          (Ix.Kernel.recFireComparands rl cv.levelParams us cvj.levelParams
            (As.take (mI + 1)) rP).1) ∧
      (P0.map (fun a => (a.instantiateLevelParams cv.levelParams us).instantiateList
          (As.take mI).reverse 0) =
        (Ix.Kernel.recFireComparands rl cv.levelParams us cvj.levelParams
          (As.take (mI + 1)) rP).2) := by
    rcases hst.recRules_fire_cases hfind hrl with hpl | ⟨lvls, pins, hnest⟩
    · obtain ⟨D, T, hD, hDfn, hDtake, hDdrop⟩ :=
        hc.env.recPlain k cv mI rP rls rl cvj _ _ hfind hrl hpl hcj
      have hrp := hplain hpl
      simp only [Ix.Kernel.Expr.recRulePlain, Bool.and_eq_true, decide_eq_true_eq] at hrp
      obtain ⟨⟨hnr, hrm⟩, -⟩ := hrp
      refine ⟨D, T, cvj.levelParams.map .param,
        (List.range rl.ctorParams).map (fun i => .bvar (mI - 1 - i)), hD, hDfn, ?_, by simp, hrm,
        ?_, ?_⟩
      · rw [← List.take_append_drop rl.ctorParams D.getAppArgs, hDtake, hDdrop]
      · intro hφ φ
        have := hφ φ
        rw [List.map_map] at this
        simp only [Ix.Kernel.recFireComparands, hpl]
        exact this
      · simp only [Ix.Kernel.recFireComparands, hpl, List.map_map, List.take_take,
          Nat.min_eq_left (show rl.ctorParams ≤ mI + 1 by omega)]
        rw [← params_inst hAc (n := rl.ctorParams) (m := mI) (by omega) (by omega)]
        apply List.map_congr_left
        intro i hi
        rfl
    · obtain ⟨-, -, -, -, hn⟩ := h6 cv mI rP rls rfl rl hrl
      obtain ⟨hrm, -, hpins, pre, dom, body, bm, D, hstrip, hdomfn, hdomargs⟩ := hn lvls pins hnest
      have hpl := hpinlen lvls pins hnest
      refine ⟨dom, D, lvls, _, piDomAt_of_stripPis mI _ hstrip, hdomfn, hdomargs,
        by simp [hpl], hrm, ?_, ?_⟩
      · intro hφ φ
        simp only [Ix.Kernel.recFireComparands, hnest]
        exact hφ φ
      · simp only [Ix.Kernel.recFireComparands, hnest, List.map_map]
        apply List.map_congr_left
        intro p hp
        try simp only [Function.comp_apply]
        have hsplit : (As.take mI).reverse =
            ((As.take mI).drop rP).reverse ++ ((As.take mI).take rP).reverse := by
          rw [← List.reverse_append, List.take_append_drop]
        have hlen' : ((As.take mI).drop rP).reverse.length = mI - rP := by
          simp; omega
        have hcl : ∀ v ∈ ((As.take mI).drop rP).reverse ++ ((As.take mI).take rP).reverse,
            v.looseBVarsBounded 0 = true := by
          intro v hv
          rw [← hsplit] at hv
          exact hAc v (List.mem_of_mem_take (List.mem_reverse.mp hv))
        rw [instLP_lift, hsplit, ← hlen', instList_lift_append hcl, List.take_take,
          List.take_take, Nat.min_eq_left (show rP ≤ mI by omega),
          Nat.min_eq_left (show rP ≤ mI + 1 by omega)]
        rcases Nat.eq_zero_or_pos rP with h0 | hpos
        · subst h0
          simp [Ix.Kernel.Expr.instSpine, instantiateList_nil]
        · rw [Ix.Kernel.Expr.instSpine_eq_instantiateList (As.take rP) (rP - 1) _
            (by simp; omega)]
  obtain ⟨D, T, ls0, P0, hD, hDfn, hDargs, hP0, hrm, hlv, hpc⟩ := key
  have hdom := major_dom_inst (ks := cv.levelParams) (us := us) (As := As) hD (by omega)
  rw [hMD] at hdom
  obtain rfl := Option.some.inj hdom
  have hfnI : (D.instantiateLevelParams cv.levelParams us).getAppFn =
      .const T (ls0.map (Ix.Kernel.Level.subst cv.levelParams us)) := by
    rw [Ix.Kernel.Expr.getAppFn_instantiateLevelParams, hDfn]
    rfl
  obtain ⟨hfn, hargs⟩ := instList_constHead hfnI (As.take mI).reverse 0
  rw [hfn] at hMDfn
  injection hMDfn with _ hmus'
  subst hmus'
  have hMDargs : ((D.instantiateLevelParams cv.levelParams us).instantiateList
      (As.take mI).reverse 0).getAppArgs =
      P0.map (fun a => (a.instantiateLevelParams cv.levelParams us).instantiateList
        (As.take mI).reverse 0) ++ (As.take mI).drop rP := by
    rw [hargs, Ix.Kernel.Expr.getAppArgs_instantiateLevelParams, hDargs,
      ← indices_inst hAc hrm (by omega)]
    simp only [List.map_append, List.map_map] <;> rfl
  have hP0' : (P0.map (fun a => (a.instantiateLevelParams cv.levelParams us).instantiateList
      (As.take mI).reverse 0)).length = rl.ctorParams := by simp [hP0]
  rw [hMDargs, List.take_left' hP0'] at hpar
  -- `Red.iota` at the spine up to the major premise
  have heA : (Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1))).getAppArgs =
      As.take (mI + 1) := by
    rw [getAppArgs_mkAppN]; rfl
  have hMA' : (Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA).getAppArgs = MA := by
    rw [getAppArgs_mkAppN]; rfl
  have htake : (As.take (mI + 1)).take mI = As.take mI := by
    rw [List.take_take, Nat.min_eq_left (show mI ≤ mI + 1 by omega)]
  have hget : (As.take (mI + 1)).getD mI (.bvar 0) = As.getD mI (.bvar 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (show mI < mI + 1 by omega),
      ← List.getD_eq_getElem?_getD]
  have hcert1 : Ix.Kernel.Rules.Certs c.env d true
      (cv.type.instantiateLevelParams cv.levelParams us)
      ((Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1))).getAppArgs.take mI ++
        [Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA]) := by
    rw [heA, htake]
    refine Specs.Whnf.CertsR.toCerts hc1
      (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _ ?_)
    simp only [List.length_append, List.length_take, List.length_singleton,
      Nat.min_eq_left (show mI ≤ As.length by omega)]
    exact hrecAr
  have hcert2 : Ix.Kernel.Rules.Certs c.env d true
      (cvj.type.instantiateLevelParams cvj.levelParams usj)
      (Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA).getAppArgs := by
    rw [hMA']
    refine Specs.Whnf.CertsR.toCerts hc2
      (Specs.Whnf.stripPis_isSome_instantiateLevelParams _ _ _ _ ?_)
    rw [hMA]
    exact harity
  have hparK : rl.compareParams = true → DefEqList c.env d
      ((Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA).getAppArgs.take rl.ctorParams)
      (Ix.Kernel.recFireComparands rl cv.levelParams us cvj.levelParams
        (Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1))).getAppArgs rP).2 := by
    intro _
    rw [hMA', heA, ← hpc]
    exact hpar
  have hargsE : (Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1))).getAppArgs.take rP ++
      (Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA).getAppArgs.drop rl.ctorParams =
      As.take rP ++ MA.drop rl.ctorParams := by
    rw [heA, hMA', List.take_take, Nat.min_eq_left (show rP ≤ mI + 1 by omega)]
  by_cases hmr : mI = rP
  · have h := Red.iota (env := c.env) (d := d)
      (e := Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1))) (c := k) (us := us)
      (cv := cv) (mI := mI) (rP := rP) (rules := rls)
      (major := Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA) (cj := rl.ctor) (usj := usj)
      (cvj := cvj) (cnP := rl.ctorParams) (cnF := nF) (rl := rl) (residual := .bvar 0)
      (by rw [getAppFn_mkAppN]; rfl) hfind (by rw [heA]; simp; omega) hlen
      (by rw [heA, hget]; exact hred) (by rw [getAppFn_mkAppN]; rfl) hcj
      (find_ctor_of_nodup hnd hrl) (by rw [hMA', hMA, hnF]) hni
      (by rw [heA]; exact hlv hmus) hparK hcert1 hcert2
      (fun hne => absurd hmr hne) (fun hne => absurd hmr hne)
    rw [hargsE] at h
    exact h
  · obtain ⟨RES, hRES, hRESd⟩ := hidx hmr
    rw [hMDargs, List.drop_left' hP0'] at hRESd
    have h := Red.iota (env := c.env) (d := d)
      (e := Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1))) (c := k) (us := us)
      (cv := cv) (mI := mI) (rP := rP) (rules := rls)
      (major := Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA) (cj := rl.ctor) (usj := usj)
      (cvj := cvj) (cnP := rl.ctorParams) (cnF := nF) (rl := rl) (residual := RES)
      (by rw [getAppFn_mkAppN]; rfl) hfind (by rw [heA]; simp; omega) hlen
      (by rw [heA, hget]; exact hred) (by rw [getAppFn_mkAppN]; rfl) hcj
      (find_ctor_of_nodup hnd hrl) (by rw [hMA', hMA, hnF]) hni
      (by rw [heA]; exact hlv hmus) hparK hcert1 hcert2
      (fun _ => by rw [hMA']; exact hRES)
      (fun _ => by rw [heA, htake]; exact hRESd)
    rw [hargsE] at h
    exact h

/-! ## The step -/

theorem rulesRep_descent {κ : _root_.Address → KKey} {h : Heap F}
    {ps : List Ix.Kernel.LevelParam} {j : Nat} {p : SourceValue F}
    {rls : List (Ix.Kernel.RecRule .anon)} (r : RulesRep κ h ps j p rls) :
    RomBound.HeapDescent h (.enum krrListEnum) p rls.length := by
  induction r with
  | nil cell => exact .here cell (by simp [Value.type])
  | cons cell _ _ ih => exact .down cell (by simp [Value.type]) (by simp [RomBound.cellArgs]) ih

/-- **`KernelWhnf::red_iota`**: the major's head is a constructor whose block and index give
the major premise's head (the guard); the rule at the constructor's index, at a major of the
constructor's arity and levels, fires when the comparisons (`iota_cmp`) and the certificates
(`iota_certs`) answer; the reduct is the rule's right-hand side at the recursor's levels applied
to the prefix, the constructor's fields and the rest of the spine (`Red.iota`, `iota_fire`). -/
theorem red_iota_step (c : Ctx) (hc : CoreFacts c) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::red_iota" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.red_iota c args h r h' calls := by
  intro rc rt lvls sp np nm nmi ni rules rp major types hargs good hrc d Γ htypes k us nl kf cv mI
    rP rls p As M hrr hlen hp hmh hAs hM hred x hr
  subst hargs
  rcases Obs.«KernelWhnf::red_iota».obs ev with
    ⟨m2, cs13, x_mh, x_margs, x_caddr, x_clvls, m70, p78, cs84, x_cnl, x_cty, x_cblock, x_cind, x_cidx, x_cnp, x_cnf, w101, v153, m156, cs164, v167, m170, cs178, m212, cs223, x_rfields, x_rrhs, m266, x273, y274, m275, x281, y282, m283, cs292, v295, x302, y303, m304, cs313, cs337, v340, cs360, v363, x370, m372, cs381, v393, x401, v420, v452, m453, cs463, v482, m483, cs493, m513, x521, y522, m523, cs532, cs618, v623, v624, v628, m645, cs653, v735, m736, cs746, v765, m766, cs776, v780, m789, cs797, v816, m817, cs827, v831, m840, cs848, v870, m879, cs887, v891, m900, cs908, v912, ev15, ld51, ev86, ld80, ev180, ev166, heq210, ev225, ev315, op331, op309, ev294, op354, ev339, op288, ev383, op377, ev362, op280, op416, op408, op435, ev465, ev495, ev534, ev655, op685, op721, ev620, op528, ev748, ev799, ev778, ev850, ev829, he871, op933, ev910, ev889, he935, hc936⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he0, -, -⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he0, -, -⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he0, -, -⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he0, -, -⟩ |
    ⟨-, -, -, -, -, -, -, -, he0, -, -⟩
  · subst he935 hc936
    obtain ⟨-, rfl⟩ := tuple2_inj (hr.symm.trans he871)
    obtain ⟨⟨hfind, u0, blk0, idx0, hci⟩, hus⟩ := hrr
    obtain ⟨p', i', m', mi', hval, hnp, hni, hnm, hnmi, hrP, hmI, hrPmI, hmIb, hrules⟩ :=
      CIRep.recr_fields hci
    subst hnp hni hnm hnmi
    have e15 := ObsFn.heap_extends ev15
    have e86 := ObsFn.heap_extends ev86
    have e180 := ObsFn.heap_extends ev180
    have e166 := ObsFn.heap_extends ev166
    have e225 := ObsFn.heap_extends ev225
    have e315 := ObsFn.heap_extends ev315
    have e294 := ObsFn.heap_extends ev294
    have e339 := ObsFn.heap_extends ev339
    have e383 := ObsFn.heap_extends ev383
    have e362 := ObsFn.heap_extends ev362
    have e465 := ObsFn.heap_extends ev465
    have e495 := ObsFn.heap_extends ev495
    have e534 := ObsFn.heap_extends ev534
    have e655 := ObsFn.heap_extends ev655
    have e620 := ObsFn.heap_extends ev620
    have e748 := ObsFn.heap_extends ev748
    have e799 := ObsFn.heap_extends ev799
    have e778 := ObsFn.heap_extends ev778
    have e850 := ObsFn.heap_extends ev850
    have e829 := ObsFn.heap_extends ev829
    have e910 := ObsFn.heap_extends ev910
    have V266 := e315.trans (e294.trans (e339.trans (e383.trans e362)))
    have Z212 := e180.trans (e166.trans e225)
    have Z266 := Z212.trans V266
    have Z483 := Z266.trans (e465.trans e495)
    have Z645 := Z483.trans (e534.trans e655)
    have Z513 := Z645.trans e620
    have Z766 := Z513.trans (e748.trans (e799.trans e778))
    have Z817 := Z766.trans (e850.trans e829)
    have X70 := e15.trans e86
    -- the major: a constructor applied to its arguments
    obtain ⟨hd0, sp0, H, MA, he1, hH, hMA, rfl⟩ := ih.get (.subst .collect_spine) (by lt_calls)
      ev15 major rfl (good.sub fun z hz => by simp [hz]) d Γ 0 M hM
    obtain ⟨rfl, rfl⟩ := tuple2_inj he1
    obtain ⟨ca, usj, rfl, hca, husj⟩ := hH.const_of_load ld51
    obtain ⟨cci, hcfind, cv0, hcld, hcci⟩ := ih.get (.callees .get_ci) (by lt_calls) ev86 x_caddr
      ca rfl (good.sub fun z hz => by simp [hz]) hca
    rw [ld80] at hcld
    injection hcld with hcv
    subst hcv
    obtain ⟨cvj, nP, nF, rfl, hvalj, hcnp, hcnf, ⟨hnPb, hnFb⟩, b, i, j, hb, hcind, hcidx, hname⟩ :=
      CIRep.ctor_fields hcci
    subst hcnp hcnf hcind hcidx
    obtain ⟨hcnl, hcnlb, -, hcty⟩ := hvalj
    subst hcnl
    -- the guard: the constructor's inductive projection is the major premise's head
    obtain ⟨a', ha', -, hrec⟩ := ih.get (.defEq .compute_iprj_addr) (by lt_calls) ev180 x_cblock
      (.field i) rfl (good.sub fun z hz => by simp [hz]) b i hb rfl
    obtain ⟨hae, -⟩ := Lib.address_eq_spec ev166 ha'
      (Bytes.repAddressRef_heapMono₂ addrTy (X70.trans e180) hp)
    have hap : a' = p := by
      by_contra hne
      rw [heq210, ite_eq_right hne] at hae
      exact NatAux.field_one_ne_zero hae
    subst hap
    -- the rule IxVM takes by the constructor's index
    have hrules156 := hrules.mono (X70.trans (e180.trans e166))
    obtain ⟨idx, rl, hrlidx, hj, hnf, hrhs⟩ := ih.get (.whnf .find_rule) (by lt_calls) ev225 rules
      (.field j) rfl (good.sub fun z hz => by simp [hz]) cv.levelParams 0 rls hrules156 x_rfields
      x_rrhs rfl
    have hrl : rl ∈ rls := List.mem_of_getElem? hrlidx
    obtain ⟨hidxl, -⟩ := List.getElem?_eq_some_iff.mp hrlidx
    have hrlsb : rls.length < 2 ^ 39 := RomBound.bounded_descent_lt good.2
      (c := ⟨"KernelWhnf::find_rule", [rules, .field j], m156⟩) (by simp) (by simp)
      (rulesRep_descent hrules156)
    injection hj with hj
    have hvj : ZMod.val j = idx := by
      rw [hj, Nat.zero_add, NatAux.val_natCast (n := idx) (by omega)]
    -- the rule is the major's constructor's
    obtain ⟨us0, hmh0⟩ := hmh
    obtain ⟨cm, hcm⟩ := hc.env.recMajorRecord k cv mI rP rls (ixAddr a') us0 hfind
      (List.ne_nil_of_mem hrl) hmh0
    obtain ⟨hnd, hfire, hkeys⟩ := hc.env.recRules k cv mI rP rls hfind
    have hctor := hkeys (ixAddr a') cm _ us0 hmh0 hcm (hrec cm hcm) idx rl hrlidx
    simp only [val_toUInt64_toNat] at hctor
    have hctor' : rl.ctor = c.κ (ixAddr ca) := by
      rw [hctor, ← hvj, ← hname]
      exact find_name hcfind
    rw [← hctor'] at hcfind hred hM
    -- the shape checks: the major's arity and the constructor's level count
    have hMA2 : c.tml d Γ m212 MA x_margs := tml_mono (e86.trans Z212) hMA
    obtain ⟨hx302, -⟩ := Lib.Lists.length_spec (t := kexprTy) (R := TmE c.κ d Γ)
      (by rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev315)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hMA2)
    subst hx302
    have hy303 := NatAux.add_ok op331
    subst hy303
    have hv295 := NatAux.sub_ok op309
    subst hv295
    obtain ⟨hx281, -⟩ := Lib.is_zero_field ev294
    subst hx281
    subst hnf
    have hv340 := NatAux.sub_ok op354
    subst hv340
    obtain ⟨hy282, -⟩ := Lib.is_zero_field ev339
    subst hy282
    have hx273 := NatAux.mul_ok op288
    subst hx273
    obtain ⟨ls, hls, hlseqv⟩ := id husj
    have hls275 := hls.mono (e86.trans (Z212.trans (e315.trans (e294.trans e339))))
    have hls275' : RepList klevelListEnum RepKLevel m275 ls x_clvls := by
      rw [klevelListEnum_eq]; exact hls275
    obtain ⟨hx370, -⟩ := Lib.Lists.length_spec (t := klevelTy) (R := RepKLevel)
      (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev383)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol]; exact hls275')
    subst hx370
    have hv363 := NatAux.sub_ok op377
    subst hv363
    obtain ⟨hy274, -⟩ := Lib.is_zero_field ev362
    subst hy274
    obtain ⟨hz1, -, hz3⟩ := ite3_one (NatAux.field_inj (NatAux.mul_ok op280)).symm
    have hMAb : MA.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_margs], m212⟩) (by simp)
      (by simp) hMA2
    have hMAlen : MA.length = nP + nF := by
      have h1 : ((MA.length : Nat) : F) = ((nP + nF : Nat) : F) := by
        push_cast; exact sub_eq_zero.mp hz1
      exact (NatAux.natCast_inj (by omega) (by omega)).mp h1
    have hlsb : ls.length < 2 ^ 39 := RomBound.bounded_length_lt good.2
      (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_clvls], m275⟩) (by simp)
      (by simp) hls275'
    have hlslen : ls.length = cvj.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (sub_eq_zero.mp hz3)
    have husjlen : usj.length = cvj.levelParams.length :=
      (LvEqList.length_eq hlseqv).trans hlslen
    -- the counts
    have hv401 := NatAux.add_ok op416
    subst hv401
    have hv393 := NatAux.add_ok op408
    subst hv393
    have hv420 := NatAux.add_ok op435
    subst hv420
    rw [← hrP] at ev799
    rw [← hmI] at ev495 ev534 op685 op933
    have hmIv : ZMod.val (mI : F) = mI := NatAux.val_natCast (by omega)
    have hrPv : ZMod.val (rP : F) = rP := NatAux.val_natCast (by omega)
    have hnPv : ZMod.val (nP : F) = nP := NatAux.val_natCast (by omega)
    -- the stored terms at the use's levels
    obtain ⟨-, halpd, -, -, -, h6, -⟩ := hc.env.store.wf _ (List.mem_of_find?_eq_some hfind)
    have halpd' : cv.type.allLevelParamsDefined cv.levelParams = true := halpd
    obtain ⟨-, halpdj, -⟩ := hc.env.store.wf _ (List.mem_of_find?_eq_some hcfind)
    have halpdj' : cvj.type.allLevelParamsDefined cvj.levelParams = true := halpdj
    obtain ⟨-, halpdR, -, -, -⟩ := h6 cv mI rP rls rfl rl hrl
    have hRT0 := ih.get (.subst .expr_inst_levels) (by lt_calls) ev465 rt lvls rfl
      (good.sub fun z hz => by simp [hz]) Γ 0 _ us ((hval.2.2.2 0 Γ).mono (X70.trans Z266))
      (hus.mono (X70.trans Z266))
    rw [hlen, posOf_inst hlen halpd'] at hRT0
    have hRT := TmC.of_depth_zero hRT0
    -- the spine before the major
    obtain ⟨hmIle, hpre⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev495)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono (X70.trans (Z266.trans e465)) hAs)
    rw [hmIv, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hpre
    rw [hmIv] at hmIle
    -- the comparisons and the certificates both answer
    obtain ⟨u521, w522, rfl, rfl⟩ := NatAux.binop_fields op528
    have huw := (NatAux.field_inj (NatAux.mul_ok op528)).symm
    have hu0 : (Value.field u521 : SourceValue F) ≠ .field 0 := fun e =>
      left_ne_zero_of_mul_eq_one huw (Value.field.inj e)
    have hw0 : (Value.field w522 : SourceValue F) ≠ .field 0 := fun e =>
      right_ne_zero_of_mul_eq_one huw (Value.field.inj e)
    have hcmp := ih.get (.whnf .iota_cmp) (by lt_calls) ev534 rc v452 v482 (.field (mI : F))
      x_cty x_clvls (.field (nP : F)) x_margs (.field i') types rfl
      (good.sub fun z hz => by simp [hz]) (RCRep.mono (X70.trans Z483) hrc) d Γ
      (types_mono (X70.trans Z483) htypes) (cv.type.instantiateLevelParams cv.levelParams us)
      (As.take mI) (mI : F) (posOf cvj.levelParams cvj.type) usj (nP : F) MA i' (hRT.mono e495)
      hpre rfl (hcty.mono Z483) (husj.mono (e86.trans Z483)) rfl (tml_mono (e86.trans Z483) hMA)
      rfl hu0
    obtain ⟨MD, k', mus, hMD, hMDfn, hmus, hpar, hidxc⟩ := hcmp
    rw [hmIv] at hMD
    rw [hnPv] at hpar hidxc
    rw [husjlen, posOf_inst husjlen halpdj'] at hidxc
    have hidx' : mI ≠ rP → ∃ RES, Ix.Kernel.piResidual
        (cvj.type.instantiateLevelParams cvj.levelParams usj) MA = some RES ∧
        DefEqList c.env d (RES.getAppArgs.drop nP) (MD.getAppArgs.drop nP) := fun hne =>
      hidxc (by
        intro hi0
        apply hne
        have h1 : (mI : F) = (rP : F) := by rw [hmI, hrP, hi0, add_zero]
        exact (NatAux.natCast_inj (by omega) (by omega)).mp h1)
    have hM523 := hM.mono (X70.trans Z483 |>.trans e534)
    have hra := Lib.Lists.snoc_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>».symbol]; exact ev655)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact tml_mono e534 hpre)
      hM523
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hra
    have hv624 := NatAux.add_ok op685
    subst hv624
    have hv628 := NatAux.add_ok op721
    subst hv628
    have hralen : (As.take mI ++ [Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA]).length =
        mI + 1 := by
      simp only [List.length_append, List.length_take, List.length_singleton]; omega
    have hrab : (As.take mI ++ [Ix.Kernel.Expr.mkAppN (.const rl.ctor usj) MA]).length < 2 ^ 39 :=
      RomBound.bounded_length_lt good.2
        (c := ⟨"KernelWhnf::iota_certs", [rc, v452, v623, .field ((mI : F) + 1), x_cty, x_clvls,
          x_margs, .field ((nP : F) + (nF : F)), types], m645⟩) (by simp) (by simp) hra
    have hcerts := ih.get (.whnf .iota_certs) (by lt_calls) ev620 rc v452 v623 _ x_cty x_clvls
      x_margs _ types rfl (good.sub fun z hz => by simp [hz]) (RCRep.mono (X70.trans Z645) hrc) d
      Γ (types_mono (X70.trans Z645) htypes) _ _ (posOf cvj.levelParams cvj.type) usj MA
      (hRT.mono (e495.trans (e534.trans e655))) hra
      (by rw [hralen, Nat.cast_add, Nat.cast_one]) (hcty.mono Z645)
      (husj.mono (e86.trans Z645)) (tml_mono (e86.trans Z645) hMA)
      (by rw [hMAlen, Nat.cast_add]) hrab hMAb hw0
    obtain ⟨hc1, hc2⟩ := hcerts
    rw [husjlen, posOf_inst husjlen halpdj'] at hc2
    -- the reduct
    have hRHS0 := ih.get (.subst .expr_inst_levels) (by lt_calls) ev748 x_rrhs lvls rfl
      (good.sub fun z hz => by simp [hz]) Γ 0 _ us
      ((hrhs 0 Γ).mono (V266.trans (e465.trans (e495.trans (e534.trans (e655.trans e620))))))
      (hus.mono (X70.trans Z513))
    rw [hlen, posOf_inst hlen halpdR] at hRHS0
    obtain ⟨-, hpreR⟩ := Lib.Lists.take_spec (t := kexprTy) (R := TmE c.κ d Γ) tmE_heapMono₂
      (by rw [Obs.Names.«Lists::take<&KernelTypes::KExprNode>».symbol]; exact ev799)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono (X70.trans (Z513.trans e748)) hAs)
    rw [hrPv, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hpreR
    have hr1 := ih.get (.whnf .apply_spine) (by lt_calls) ev778 v735 v780 rfl
      (good.sub fun z hz => by simp [hz]) d Γ 0 _ (As.take rP) ((hRHS0.of_depth_zero d).mono e799)
      hpreR
    obtain ⟨-, hdropMA, -⟩ := Lib.Lists.drop_spec nP (t := kexprTy) (R := TmE c.κ d Γ) hnPv
      (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev850)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono (e86.trans Z766) hMA)
    rw [hnPv, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hdropMA
    have hr2 := ih.get (.whnf .apply_spine) (by lt_calls) ev829 v765 v831 rfl
      (good.sub fun z hz => by simp [hz]) d Γ 0 _ (MA.drop nP) (hr1.mono e850)
      (tml_mono e850 hdropMA)
    have hv912 := NatAux.add_ok op933
    subst hv912
    have hval1 : ZMod.val ((mI : F) + 1) = mI + 1 := by
      rw [show ((mI : F) + 1) = ((mI + 1 : Nat) : F) from (Nat.cast_succ mI).symm]
      exact NatAux.val_natCast (by omega)
    obtain ⟨hAl, hdropAs, -⟩ := Lib.Lists.drop_spec (mI + 1) (t := kexprTy) (R := TmE c.κ d Γ)
      hval1 (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev910)
      (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]
          exact tml_mono (X70.trans Z817) hAs)
    rw [hval1, Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol] at hdropAs
    rw [hval1] at hAl
    have hr3 := ih.get (.whnf .apply_spine) (by lt_calls) ev889 v816 v891 rfl
      (good.sub fun z hz => by simp [hz]) d Γ 0 _ (As.drop (mI + 1)) (hr2.mono e910)
      (tml_mono e910 hdropAs)
    refine ⟨_, hr3, ?_⟩
    show Red c.env d (Ix.Kernel.Expr.mkAppN (.const k us) As) (Ix.Kernel.Expr.mkAppN
      (Ix.Kernel.Expr.mkAppN (Ix.Kernel.Expr.mkAppN
        (rl.rhs.instantiateLevelParams cv.levelParams us) (As.take rP)) (MA.drop nP))
      (As.drop (mI + 1)))
    have hfire := iota_fire c hc hfind hrl hcfind hlen hAl (tml_lbb hAs) hMAlen hred
      ⟨MD, k', mus, hMD, hMDfn, hmus, hpar, hidx'⟩ hc1 hc2
    have hsplit : Ix.Kernel.Expr.mkAppN (.const k us) As = Ix.Kernel.Expr.mkAppN
        (Ix.Kernel.Expr.mkAppN (.const k us) (As.take (mI + 1))) (As.drop (mI + 1)) := by
      rw [mkAppN_mkAppN, List.take_append_drop]
    rw [mkAppN_mkAppN _ (As.take rP) (MA.drop nP), hsplit]
    exact red_mkAppN _ hfire
  all_goals exact (tag_zero_ne_one (he0.symm.trans hr)).elim

end IxVM.Refinement.Core
