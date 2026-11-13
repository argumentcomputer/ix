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

end IxVM.Refinement.Core
