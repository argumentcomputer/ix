import IxVMRefinement.Binding.FamilyReconBVars
import IxVMRefinement.Obs.KernelWhnf
import IxVMRefinement.Obs.KernelCheck11

/-! # The reconstruction's head normalization on `TmOExact` (without `UnfoldAnswers` or `ProjAnswers`)

`KernelCheck::recon_whnf_spine` (and `recon_whnf`) on open exact terms is the model's `hnfSpine V`
(and `hnf V`), derived from elementary single-call store-read predicates:

* `AddrOf κ V`: `V.addr (κ a) = some a`.
* `DefnAnswers κ V`: `Ingress::get_ci` matches `V.unfold` on `Defn` vs non-`Defn`.
* `IndAnswers κ V`: `Ingress::get_ci` matches `V.ind` on `Induct` vs non-`Induct`.
* `CtorOfAnswers V`: `Ingress::get_ci` matches `V.ctorOf` on `Ctor` vs non-`Ctor`.
* `ModeledAnswers V`: `KernelModeled::block_is_modeled` matches `V.modeled`.

From these five single-call predicates, this module proves:
* `apply_spine_spec` (`KernelWhnf::apply_spine` is `mkAppN`, preserving `NotLet`),
* `type_sort_never_zeta_spec` (`KernelWhnf::type_sort_never_zeta` is `typeSortNever`),
* `red_unfold_spec` (`KernelWhnf::red_unfold` refines `V.unfold`),
* `red_proj_zeta_spec` (`KernelWhnf::red_proj_zeta` refines `projStep V`),
* `recon_whnf_spine_spec` and `recon_whnf_spec` (refining `hnfSpine V` / `hnf V`, with `NotLet`). -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum klevelListEnum addrTy ixAddr
  Resolved ProjPermitted)
open IxVM.Refinement.Decl (TmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList substLevel)
open IxVM.Refinement.Binding.FamilyFlat (exprInstLevels)
open IxVM (F)

set_option maxHeartbeats 2400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

section

variable {κ : _root_.Address → KKey}

/-! ## `apply_spine` -/

/-- **`KernelWhnf::apply_spine(head, spine)`** is `mkAppN`, preserving `NotLet` whenever the head
is `NotLet`. -/
theorem apply_spine_spec (Sp : List KExpr) :
    ∀ {xh xsp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {H : KExpr},
      ObsFn Obs.W "KernelWhnf::apply_spine" [xh, xsp] h r h' cs →
      TmOExact κ h H xh → NotLet h xh → RepList kexprListEnum (TmOExact κ) h Sp xsp →
      Heap.Extends h h' ∧ TmOExact κ h' (Ix.Kernel.Expr.mkAppN H Sp) r ∧ NotLet h' r := by
  induction Sp with
  | nil =>
    intro xh xsp r h h' cs H ev hH hnl hS
    rcases Obs.«KernelWhnf::apply_spine».obs ev with
      ⟨ld, rfl, rfl, -⟩ | ⟨x_a, x_rest, cs', m, ld, -, -, -⟩
    · exact ⟨Heap.Extends.refl _, hH, hnl⟩
    · obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hS ld
      cases hzs
  | cons A As ih =>
    intro xh xsp r h h' cs H ev hH _ hS
    rcases Obs.«KernelWhnf::apply_spine».obs ev with
      ⟨ld, -, -, -⟩ | ⟨x_a, x_rest, cs', m, ld, hm, ev', -⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hS ld
    · obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hS ld
      injection hzs with hz1 hz2
      rw [← hz1] at hz
      rw [← hz2] at hzs'
      subst hm
      have ext : Heap.Extends h (h ++ [.construct "KernelTypes::KExprNode" "App" [xh, x_a]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨k₁, r₁⟩ := hH
      obtain ⟨k₂, r₂⟩ := hz
      have happ : TmOExact κ (h ++ [.construct "KernelTypes::KExprNode" "App" [xh, x_a]]) (.app H A)
          (.ptr (.enum "KernelTypes::KExprNode") h.length) :=
        ⟨max k₁ k₂, .app (by simp)
          (tmExact_depth_le (r₁.mono ext) _ (Nat.le_max_left _ _))
          (tmExact_depth_le (r₂.mono ext) _ (Nat.le_max_right _ _))⟩
      have hnlApp : NotLet (h ++ [.construct "KernelTypes::KExprNode" "App" [xh, x_a]])
          (.ptr (.enum "KernelTypes::KExprNode") h.length) :=
        notLet_of_cell (by simp) (by decide)
      obtain ⟨ext', hr, hnlr⟩ := ih ev' happ hnlApp (tmOExactList_mono ext hzs')
      exact ⟨ext.trans ext', hr, hnlr⟩

/-! ## `type_sort_never_zeta` -/

private theorem typeSortNever_not_forall_not_sort {h : Heap F} {E : KExpr} {p v : SourceValue F}
    (hE : TmOExact κ h E p) (ld : loadValue h p = .ok v)
    (hf : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs)
    (hs : ∀ vs : List (SourceValue F), vs.length = 1 → v ≠ .construct kexprEnum "Srt" vs)
    (hl : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs)
    (n : Nat) (us : List KLevel) : typeSortNever E n us = false := by
  obtain ⟨k, ht⟩ := hE
  cases ht with
  | forallE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hf _ rfl hv).elim
  | sort cell _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hs _ rfl hv).elim
  | letE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv
    exact (hl _ rfl hv).elim
  | bvarFree _ _ _ hd => omega
  | bvarLocal .. | const .. | app .. | lam .. | litNat .. | litStr .. | proj .. =>
    cases n <;> rfl

/-- **`KernelWhnf::type_sort_never_zeta`** decides `typeSortNever E n us` bidirectionally on
`TmOExact`. -/
theorem type_sort_never_zeta_spec {E : KExpr} {n : Nat} {us : List KLevel}
    {xty xlvls r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 18446744069414584321) (hE : TmOExact κ h E xty) (hus : RepKLevelList h us xlvls)
    (hbnd : IxVM.Consistency.Bounded cs)
    (ev : ObsFn W "KernelWhnf::type_sort_never_zeta" [xty, .field (n : F), xlvls] h r h' cs) :
    r = .field (if typeSortNever E n us then 1 else 0) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono hbnd hs
  match Obs.«KernelWhnf::type_sort_never_zeta».obs ev with
  | .Forall_n0 (ld_bolbylmd := ld) (hv_cgupxtmg := hv) (he_jwdquhsj := hr) .. =>
    subst hr
    obtain ⟨D, B, ℓ, rfl, -, -, -⟩ := TmOExact.forallE_of_load hE ld
    have hn0 : n = 0 := field_natCast_eq_zero hn hv
    subst hn0; rfl
  | .Forall_other (x_body := xbody) (cs_bgxcogsh := cs1) (v_qodywepd := vn)
      (ld_bolbylmd := ld) (hne_pigtkltp := hne) (op_zolfdmjq := op)
      (ev_sqhwxzgg := e1) (hc_hkhtpxta := hc) .. =>
    obtain ⟨D, B, ℓ, rfl, -, hB, -⟩ := TmOExact.forallE_of_load hE ld
    have hnz : n ≠ 0 := field_natCast_ne_zero hn hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain rfl := evalBinOp_sub_succ m op
    have hlt : cs1.length < cs.length := by rw [hc]; simp
    exact type_sort_never_zeta_spec (by omega) hB hus (sub fun c hc' => by rw [hc]; simp [hc']) e1
  | .Srt_n0 (x_l := xl) (v_bjumgskp := vl) (m_etsdnfpa := m1)
      (cs_xbqhqjym := cs1) (cs_fcwfomrw := cs2) (ld_bolbylmd := ld) (hv_nnibqruc := hv)
      (ev_pvmsdakl := e1) (ev_ssgoqbcd := e2) (hc_fdglgoab := hc) .. =>
    obtain ⟨l, rfl, rl⟩ := TmOExact.sort_of_load hE ld
    have hn0 : n = 0 := field_natCast_eq_zero hn hv
    subst hn0
    obtain ⟨-, rl', -⟩ := IxVM.Refinement.Levels.levelInstParams_obs e1
      (sub fun c hc' => by rw [hc]; simp [hc']) rl hus
    obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelIsNotZero_step e2 vl rfl (substLevel l us) rl'
    exact hr
  | .Srt_other (ld_bolbylmd := ld) (hne_nuvqzzco := hne) (he_krkybuoo := hr) .. =>
    subst hr
    obtain ⟨l, rfl, -⟩ := TmOExact.sort_of_load hE ld
    have hnz : n ≠ 0 := field_natCast_ne_zero hn hne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl
  | .Let (x_v := xv) (x_b := xb) (v_pbclftxd := v') (m_fhppzpwh := m')
      (cs_yqrxeseo := cs1) (cs_inrgosoo := cs2) (ld_bolbylmd := ld)
      (ev_gemvpjgn := e1) (ev_juseplax := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hE ld
    have hv' := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact type_sort_never_zeta_spec hn hv' (hus.mono e1.heap_extends)
      (sub fun c hc' => by rw [hc]; simp [hc']) e2
  | .other (v_hirlhoca := v) (ld_bolbylmd := ld) (hne_pgoqiggy := hnf)
      (hne_dvcijcri := hns) (hne_ttotnwna := hnl) (he_vpckpvxl := hr) .. =>
    subst hr
    rw [typeSortNever_not_forall_not_sort hE ld hnf hns hnl n us]
    rfl
termination_by cs.length

/-! ## Elementary single-call store-read predicates -/

/-- The view's key-address map inverts `κ`. -/
def AddrOf (κ : _root_.Address → KKey) (V : ReconView) : Prop :=
  ∀ a : _root_.Address, V.addr (κ a) = some a

/-- **`Ingress::get_ci` matches `V.unfold` on `Defn` vs non-`Defn`.** -/
def DefnAnswers (κ : _root_.Address → KKey) (V : ReconView) : Prop :=
  ∀ {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs → loadValue m p = .ok ci →
    (∀ xnl xty xval xsf xh,
      ci = .construct "KernelTypes::KConstantInfo" "Defn" [xnl, xty, xval, xsf, xh] →
      ∃ (nl : Nat) (val : KExpr),
        xnl = .field (nl : F) ∧ nl < 4294967296 ∧ TmOExact κ m val xval ∧
        ∀ us, V.unfold (κ (ixAddr a)) us =
          if us.length = nl then some (some (exprInstLevels us val)) else some none) ∧
    ((∀ vs : List (SourceValue F), vs.length = 5 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Defn" vs) →
      ∀ us, V.unfold (κ (ixAddr a)) us = some none)

/-- **`Ingress::get_ci` matches `V.ind` on `Induct` vs non-`Induct`.** -/
def IndAnswers (κ : _root_.Address → KKey) (V : ReconView) : Prop :=
  ∀ {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs → loadValue m p = .ok ci →
    (∀ xnl xty xnp xni xnc xrec xblk xidx,
      ci = .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx] →
      ∃ (d : IndData) (ba : Bytes.Address),
        V.ind (ixAddr a) = some (some d) ∧
        d.nl < 4294967296 ∧ d.np < 4294967296 ∧ d.ni < 4294967296 ∧
        d.nctors < 4294967296 ∧ d.idx < 4294967296 ∧
        xnl = .field (d.nl : F) ∧ TmOExact κ m d.ty xty ∧
        xnp = .field (d.np : F) ∧ xni = .field (d.ni : F) ∧ xnc = .field (d.nctors : F) ∧
        ixAddr ba = d.blk ∧ Bytes.RepAddressRef addrTy m ba xblk ∧ xidx = .field (d.idx : F)) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Induct" vs) →
      V.ind (ixAddr a) = some none)

/-- **`Ingress::get_ci` matches `V.ctorOf` on `Ctor` vs non-`Ctor`.** -/
def CtorOfAnswers (V : ReconView) : Prop :=
  ∀ {xa p ci : SourceValue F} {h m : Heap F} {cs : List (Call F)} {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa →
    ObsFn W "Ingress::get_ci" [xa] h p m cs → loadValue m p = .ok ci →
    (∀ xnl xty xblk xind xcidx xnp xnf xuns,
      ci = .construct "KernelTypes::KConstantInfo" "Ctor"
        [xnl, xty, xblk, xind, xcidx, xnp, xnf, xuns] →
      ∃ (d : CtorData) (ba : Bytes.Address),
        V.ctorOf (ixAddr a) = some (some d) ∧
        d.nl < 4294967296 ∧ d.ind < 4294967296 ∧ d.np < 4294967296 ∧ d.nf < 4294967296 ∧
        xnl = .field (d.nl : F) ∧ ixAddr ba = d.blk ∧ Bytes.RepAddressRef addrTy m ba xblk ∧
        xind = .field (d.ind : F) ∧ xnp = .field (d.np : F) ∧ xnf = .field (d.nf : F)) ∧
    ((∀ vs : List (SourceValue F), vs.length = 8 →
        ci ≠ .construct "KernelTypes::KConstantInfo" "Ctor" vs) →
      V.ctorOf (ixAddr a) = some none)

/-- **`KernelModeled::block_is_modeled` matches `V.modeled`.** -/
def ModeledAnswers (V : ReconView) : Prop :=
  ∀ {xblk r : SourceValue F} {h m : Heap F} {cs : List (Call F)} {ba : Bytes.Address},
    Bytes.RepAddressRef addrTy h ba xblk →
    ObsFn W "KernelModeled::block_is_modeled" [xblk] h r m cs →
    ∃ b : Bool, V.modeled (ixAddr ba) = some b ∧ r = .field (if b then 1 else 0)

/-! ## `red_unfold` and `red_proj_zeta` from elementary store reads -/

private theorem klevel_length {us : List KLevel} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs)
    (hl : RepKLevelList h us l) : r = .field (us.length : F) ∧ h' = h :=
  Lib.Lists.length_spec (t := .ptr (.named "KernelTypes::KLevelNode" [])) (R := RepKLevel)
    (by rw [Obs.Names.«Lists::length<&KernelTypes::KLevelNode>».symbol]; exact ev)
    (by rw [← IxVM.Refinement.Levels.klevelList_names]; exact hl)

/-- **`KernelWhnf::red_unfold`** after `Ingress::get_ci` refines `V.unfold` on `TmOExact`. -/
theorem red_unfold_spec {V : ReconView} (hD : DefnAnswers κ V)
    {xa xl p ci v : SourceValue F} {h m m' : Heap F} {cs₁ cs₂ : List (Call F)}
    {a : Bytes.Address} {us : List KLevel}
    (ra : Bytes.RepAddressRef addrTy h a xa) (rus : RepKLevelList m us xl)
    (evg : ObsFn W "Ingress::get_ci" [xa] h p m cs₁) (ldci : loadValue m p = .ok ci)
    (evu : ObsFn W "KernelWhnf::red_unfold" [ci, xl] m v m' cs₂)
    (bd : IxVM.Consistency.Bounded cs₂) :
    (∀ xb, v = .tuple [.field 1, xb] →
      ∃ b, V.unfold (κ (ixAddr a)) us = some (some b) ∧ TmOExact κ m' b xb) ∧
    ((∀ xb, v ≠ .tuple [.field 1, xb]) → V.unfold (κ (ixAddr a)) us = some none) := by
  obtain ⟨hyes, hno⟩ := hD ra evg ldci
  match Obs.«KernelWhnf::red_unfold».obs evu with
  | .Defn_n0 (x_nl := xnl) (x_value := xval) (x54 := xlen) (m56 := m1) (cs65 := csl)
      (v84 := vres) (m93 := m2) (cs101 := csi) (hv15 := hci) (ev67 := evl)
      (op61 := op) (he85 := hr) (ev103 := evi) (he120 := hh) (hc121 := hc) .. =>
    subst hr hh
    obtain ⟨nl, val, rfl, hnl, hval, hunf⟩ := hyes _ _ _ _ _ hci
    obtain ⟨rfl, rfl⟩ := klevel_length evl rus
    have hus_lt : us.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xl], m⟩) (by rw [hc]; simp) (by simp) rus
    have heq : us.length = nl := binop_sub_eq_zero_nat (by omega) (by omega) op
    refine ⟨fun xb hxb => ?_, fun hnt => (hnt vres rfl).elim⟩
    injection hxb with hpair
    injection hpair with _ hpair2
    injection hpair2 with hxb'
    subst hxb'
    have binst : IxVM.Consistency.Bounded csi :=
      RomBound.bounded_mono bd (fun c hc' => by rw [hc]; simp [hc'])
    refine ⟨exprInstLevels us val, by rw [hunf us, if_pos heq],
      expr_inst_levels_tmOExact binst hval rus evi⟩
  | .Defn_other (x_nl := xnl) (x_value := xval) (x54 := xlen) (m56 := m1)
      (hv15 := hci) (ev67 := evl) (op61 := op) (hne122 := hne) (he130 := hr) .. =>
    subst hr
    obtain ⟨nl, val, rfl, hnl, -, hunf⟩ := hyes _ _ _ _ _ hci
    obtain ⟨rfl, rfl⟩ := klevel_length evl rus
    have hneq : us.length ≠ nl := binop_sub_ne_nat op hne
    refine ⟨fun xb hxb => ?_, fun _ => by rw [hunf us, if_neg hneq]⟩
    injection hxb with hpair; injection hpair with h0 _
    exact absurd (Value.field.inj h0) (by decide)
  | .Thm_n0 (hne146 := hnd) (he209 := hr) .. =>
    subst hr
    refine ⟨fun xb hxb => ?_, fun _ => hno hnd us⟩
    injection hxb with hpair; injection hpair with h2 _
    exact absurd (Value.field.inj h2) (by decide)
  | .Thm_other (hne146 := hnd) (he254 := hr) .. =>
    subst hr
    refine ⟨fun xb hxb => ?_, fun _ => hno hnd us⟩
    injection hxb with hpair; injection hpair with h0 _
    exact absurd (Value.field.inj h0) (by decide)
  | .other (hne146 := hnd) (he278 := hr) .. =>
    subst hr
    refine ⟨fun xb hxb => ?_, fun _ => hno hnd us⟩
    injection hxb with hpair; injection hpair with h0 _
    exact absurd (Value.field.inj h0) (by decide)

private theorem field_mul_bool {b₁ b₂ : Bool} {v : SourceValue F}
    (op : evalBinOp .mul (.field (if b₁ then 1 else 0)) (.field (if b₂ then 1 else 0)) = .ok v) :
    v = .field (if (b₁ && b₂) then 1 else 0) := by
  cases b₁ <;> cases b₂ <;> (simp only [evalBinOp, Bool.and_false, Bool.and_true, Bool.false_and,
    Bool.true_and, ↓reduceIte] at op ⊢; injection op with hv; rw [← hv]; simp)

private theorem is_zero_sub_nat {a b : Nat} (ha : a < 18446744069414584321)
    (hb : b < 18446744069414584321) {v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (op : evalBinOp .sub (.field (a : F)) (.field (b : F)) = .ok v)
    (ev : ObsFn W "Fields::is_zero" [v] h r h' cs) :
    r = .field (if a == b then 1 else 0) ∧ h' = h := by
  obtain rfl := evalBinOp_sub_field op
  obtain ⟨hr, hh⟩ := Lib.is_zero_field ev
  refine ⟨hr.trans ?_, hh⟩
  by_cases hab : a = b
  · subst hab; simp
  · have hne : (a : F) - (b : F) ≠ 0 := fun h0 => hab (natCast_inj_small ha hb (sub_eq_zero.mp h0))
    have hbf : (a == b) = false := beq_eq_false_iff_ne.mpr hab
    rw [if_neg hne, hbf]; rfl

private theorem is_zero_nat {a : Nat} (ha : a < 18446744069414584321)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Fields::is_zero" [.field (a : F)] h r h' cs) :
    r = .field (if a == 0 then 1 else 0) ∧ h' = h := by
  obtain ⟨hr, hh⟩ := Lib.is_zero_field ev
  refine ⟨hr.trans ?_, hh⟩
  by_cases ha0 : a = 0
  · subst ha0; simp
  · have hne : (a : F) ≠ 0 := fun h0 => ha0 (natCast_inj_small ha (by decide) (by simpa using h0))
    have hbf : (a == 0) = false := beq_eq_false_iff_ne.mpr ha0
    rw [if_neg hne, hbf]; rfl

private theorem red_proj_gate_eval
    {cd : CtorData} {sd : IndData} {ba_c ba_s : Bytes.Address}
    {cus : List KLevel} {args : List KExpr} {i : F}
    (hcb : ixAddr ba_c = cd.blk) (hsb : ixAddr ba_s = sd.blk)
    (hcd_nl : cd.nl < 4294967296) (hcd_ind : cd.ind < 4294967296)
    (hcd_np : cd.np < 4294967296) (hcd_nf : cd.nf < 4294967296)
    (hsd_nl : sd.nl < 4294967296) (hsd_np : sd.np < 4294967296)
    (hsd_ni : sd.ni < 4294967296) (hsd_nc : sd.nctors < 4294967296)
    (hsd_idx : sd.idx < 4294967296)
    {h m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 : Heap F}
    {xcblk xsblk xargs xclvls : SourceValue F}
    {v_eq v_sub1 y_z1 x_m1 v_sub2 y_z2 v_g1 y_z3 v_sub3 y_z4 x_m2 v_sub4 y_z5 v_g2
     x_alen y_add v_sub5 x_z6 x_llen v_sub6 y_z7 v_g3 x_m3 x_m4 y_lt v_out : SourceValue F}
    {cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 : List (Call F)}
    (r_cblk : Bytes.RepAddressRef addrTy h ba_c xcblk)
    (r_sblk : Bytes.RepAddressRef addrTy h ba_s xsblk)
    (r_args : RepList kexprListEnum (TmOExact κ) h args xargs)
    (r_clvls : RepKLevelList h cus xclvls)
    (hargs_lt : args.length < 2 ^ 39) (hclvls_lt : cus.length < 2 ^ 39)
    (ev1 : ObsFn W "Bytes::address_eq" [xcblk, xsblk] h v_eq m1 cs1)
    (op1 : evalBinOp .sub (.field (cd.ind : F)) (.field (sd.idx : F)) = .ok v_sub1)
    (ev2 : ObsFn W "Fields::is_zero" [v_sub1] m1 y_z1 m2 cs2)
    (op2 : evalBinOp .mul v_eq y_z1 = .ok x_m1)
    (op3 : evalBinOp .sub (.field (sd.nl : F)) (.field (cd.nl : F)) = .ok v_sub2)
    (ev3 : ObsFn W "Fields::is_zero" [v_sub2] m2 y_z2 m3 cs3)
    (op4 : evalBinOp .mul x_m1 y_z2 = .ok v_g1)
    (ev4 : ObsFn W "Fields::is_zero" [.field (sd.ni : F)] m3 y_z3 m4 cs4)
    (op5 : evalBinOp .sub (.field (sd.nctors : F)) (.field 1) = .ok v_sub3)
    (ev5 : ObsFn W "Fields::is_zero" [v_sub3] m4 y_z4 m5 cs5)
    (op6 : evalBinOp .mul y_z3 y_z4 = .ok x_m2)
    (op7 : evalBinOp .sub (.field (sd.np : F)) (.field (cd.np : F)) = .ok v_sub4)
    (ev6 : ObsFn W "Fields::is_zero" [v_sub4] m5 y_z5 m6 cs6)
    (op8 : evalBinOp .mul x_m2 y_z5 = .ok v_g2)
    (ev7 : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [xargs] m6 x_alen m7 cs7)
    (op9 : evalBinOp .add (.field (cd.np : F)) (.field (cd.nf : F)) = .ok y_add)
    (op10 : evalBinOp .sub x_alen y_add = .ok v_sub5)
    (ev8 : ObsFn W "Fields::is_zero" [v_sub5] m7 x_z6 m8 cs8)
    (ev9 : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [xclvls] m8 x_llen m9 cs9)
    (op11 : evalBinOp .sub x_llen (.field (cd.nl : F)) = .ok v_sub6)
    (ev10 : ObsFn W "Fields::is_zero" [v_sub6] m9 y_z7 m10 cs10)
    (op12 : evalBinOp .mul x_z6 y_z7 = .ok v_g3)
    (op13 : evalBinOp .mul v_g1 v_g2 = .ok x_m3)
    (op14 : evalBinOp .mul x_m3 v_g3 = .ok x_m4)
    (ev11 : ObsFn W "UInt32::less_than_fields" [.field i, .field (cd.nf : F)] m10 y_lt m11 cs11)
    (op15 : evalBinOp .mul x_m4 y_lt = .ok v_out) :
    v_out = .field (if projGate cd sd cus args i.val then 1 else 0) ∧ m11 = h ∧
      i.val < 4294967296 := by
  obtain ⟨hv_eq, rfl⟩ := Lib.address_eq_spec ev1 r_cblk r_sblk
  have hblk_eq : (if ba_c = ba_s then (1 : F) else 0) = if cd.blk == sd.blk then 1 else 0 := by
    rw [← hcb, ← hsb]
    by_cases hba : ba_c = ba_s
    · subst hba; simp
    · have hne : ixAddr ba_c ≠ ixAddr ba_s := fun h => hba (ixAddr_inj h)
      have hbf : (ixAddr ba_c == ixAddr ba_s) = false := beq_eq_false_iff_ne.mpr hne
      rw [if_neg hba, hbf]; rfl
  rw [hblk_eq] at hv_eq; subst hv_eq
  obtain ⟨hy_z1, rfl⟩ := is_zero_sub_nat (by omega) (by omega) op1 ev2; subst hy_z1
  obtain rfl := field_mul_bool op2
  obtain ⟨hy_z2, rfl⟩ := is_zero_sub_nat (by omega) (by omega) op3 ev3; subst hy_z2
  obtain rfl := field_mul_bool op4
  obtain ⟨hy_z3, rfl⟩ := is_zero_nat (by omega) ev4; subst hy_z3
  obtain ⟨hy_z4, rfl⟩ := is_zero_sub_nat (by omega) (by decide) (b := 1) op5 ev5; subst hy_z4
  obtain rfl := field_mul_bool op6
  obtain ⟨hy_z5, rfl⟩ := is_zero_sub_nat (by omega) (by omega) op7 ev6; subst hy_z5
  obtain rfl := field_mul_bool op8
  obtain ⟨rfl, rfl⟩ := kexpr_length ev7 r_args
  obtain rfl := binop_add_nat op9
  obtain ⟨hx_z6, rfl⟩ := is_zero_sub_nat (by omega) (by omega) op10 ev8; subst hx_z6
  obtain ⟨rfl, rfl⟩ := klevel_length ev9 r_clvls
  obtain ⟨hy_z7, rfl⟩ := is_zero_sub_nat (by omega) (by omega) op11 ev10; subst hy_z7
  obtain rfl := field_mul_bool op12
  obtain rfl := field_mul_bool op13
  obtain rfl := field_mul_bool op14
  obtain ⟨hi32, -, hlt_iff, hlt_bin, rfl⟩ := Lib.less_than_fields_field ev11
  rw [fval_natCast (by omega)] at hlt_iff
  have hy_lt : y_lt = .field (if decide (i.val < cd.nf) then 1 else 0) := by
    by_cases hlt : i.val < cd.nf
    · rw [decide_eq_true hlt]; exact hlt_iff.mpr hlt
    · rw [decide_eq_false hlt]
      rcases hlt_bin with h0 | h1
      · exact h0
      · exact absurd (hlt_iff.mp h1) hlt
  subst hy_lt
  obtain rfl := field_mul_bool op15
  refine ⟨?_, rfl, hi32⟩
  congr 1; congr 1
  simp only [projGate, Bool.and_assoc]

/-- **`KernelWhnf::red_proj_zeta`** refines `projStep V` exactly on `TmOExact` from the four
single-call store predicates (without `ProjAnswers`). -/
theorem red_proj_zeta_spec {V : ReconView}
    (hA : AddrOf κ V) (hI : IndAnswers κ V) (hC : CtorOfAnswers V) (hM : ModeledAnswers V)
    {xs xw v : SourceValue F} {i : F} {h m' : Heap F} {cs : List (Call F)}
    {a : Bytes.Address} {W0 : KExpr}
    (ra : Bytes.RepAddressRef addrTy h a xs) (hW : TmOExact κ h W0 xw)
    (bd : IxVM.Consistency.Bounded cs)
    (ev : ObsFn W "KernelWhnf::red_proj_zeta" [xs, .field i, xw] h v m' cs) :
    (∀ xf, v = .tuple [.field 1, xf] →
      ∃ y, projStep V (κ (ixAddr a)) (ZMod.val i) W0 = some (some y) ∧ TmOExact κ m' y xf) ∧
    ((∀ xf, v ≠ .tuple [.field 1, xf]) →
      projStep V (κ (ixAddr a)) (ZMod.val i) W0 = some none) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono bd hs
  match Obs.«KernelWhnf::red_proj_zeta».obs ev with
  | .other (m_ojfleyqm := m1) (cs_mtergxtu := cs1) (x_head := xhd) (x_args := xargs)
      (v_hirlhoca := vh) (ev_dnbgofcn := evsp) (ld_bolbylmd := ldh) (hne_uulqutnf := hneC)
      (he_jjavcari := hr) (hc_kjrxaxhl := hc) .. =>
    subst hr
    obtain ⟨hfn, hnl, -⟩ := collect_spine_zeta_spec hW
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    refine ⟨fun xf hxf => ?_, fun _ => ?_⟩
    · injection hxf with hp; injection hp with h0 _
      exact absurd (Value.field.inj h0) (by decide)
    · unfold projStep
      cases hf : W0.getAppFn with
      | const ck cus => exact (tmOExact_not_const hfn hnl ldh hneC ck cus hf).elim
      | _ => rfl
  | .Const_other (m_ojfleyqm := m1) (cs_mtergxtu := cs1) (x_head := xhd) (x_args := xargs)
      (x_caddr := xca) (x_clvls := xcl) (v_jknrfqpi := vci) (m_tdzaboly := m2)
      (p_fvrbdqgt := pci) (cs_tkdqmhev := cs2) (ev_dnbgofcn := evsp) (ld_bolbylmd := ldh)
      (ev_ceowrmgg := evg1) (ld_hkyzglrm := ld1) (hne_vqxhmvra := hneCt)
      (he_uzvmrkan := hr) (hc_cnrhqnxp := hc) .. =>
    subst hr
    obtain ⟨hfn, -, -⟩ := collect_spine_zeta_spec hW
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, cus, hfn_eq, rca, -⟩ := TmOExact.const_of_load hfn ldh
    have hct_none := (hC rca evg1 ld1).2 hneCt
    refine ⟨fun xf hxf => ?_, fun _ => ?_⟩
    · injection hxf with hp; injection hp with h0 _
      exact absurd (Value.field.inj h0) (by decide)
    · unfold projStep; rw [hfn_eq, hA, hct_none]
  | .Const_Ctor_other (m_ojfleyqm := m1) (cs_mtergxtu := cs1) (x_head := xhd) (x_args := xargs)
      (x_caddr := xca) (x_clvls := xcl) (m_tdzaboly := m2) (p_fvrbdqgt := pci1)
      (cs_tkdqmhev := cs2) (v_alxmatcq := vci2) (m_rzlfecwb := m3) (p_murouqmk := pci2)
      (cs_bqjhgrbx := cs3) (ev_dnbgofcn := evsp) (ld_bolbylmd := ldh) (ev_ceowrmgg := evg1)
      (ld_hkyzglrm := ld1) (ev_fruvizab := evg2) (ld_vandvewq := ld2) (hne_khtbpjqu := hneI)
      (he_bbqcmsby := hr) (hc_vyvcmlcc := hc) .. =>
    subst hr
    obtain ⟨hfn, -, -⟩ := collect_spine_zeta_spec hW
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, cus, hfn_eq, rca, -⟩ := TmOExact.const_of_load hfn ldh
    obtain ⟨cd, _, hcd, -⟩ := (hC rca evg1 ld1).1 _ _ _ _ _ _ _ _ rfl
    have ra2 := Bytes.repAddressRef_heapMono₂ addrTy (evsp.heap_extends.trans evg1.heap_extends) ra
    have hind_none := (hI ra2 evg2 ld2).2 hneI
    refine ⟨fun xf hxf => ?_, fun _ => ?_⟩
    · injection hxf with hp; injection hp with h0 _
      exact absurd (Value.field.inj h0) (by decide)
    · unfold projStep; rw [hfn_eq, hA, hcd, hA, hind_none]
  | .Const_Ctor_Induct_other (m_ojfleyqm := m1) (cs_mtergxtu := cs1) (x_head := xhd)
      (x_args := xargs) (x_caddr := xca) (x_clvls := xcl) (m_tdzaboly := m2) (p_fvrbdqgt := pci1)
      (cs_tkdqmhev := cs2) (x_cnl := xcnl) (x_cblock := xcblk) (x_cind := xcind)
      (x_nparams := xnp) (x_nfields := xnf) (m_rzlfecwb := m3) (p_murouqmk := pci2)
      (cs_bqjhgrbx := cs3) (x_snl := xsnl) (x_sty := xsty) (x_snp := xsnp) (x_sni := xsni)
      (x_snc := xsnc) (x_sblock := xsblk) (x_sidx := xsidx)
      (ev_dnbgofcn := evsp) (ld_bolbylmd := ldh) (ev_ceowrmgg := evg1) (ld_hkyzglrm := ld1)
      (ev_fruvizab := evg2) (ld_vandvewq := ld2) (ev_kveftqvh := ev1) (op_hkoxximr := op1)
      (ev_mkroeoak := ev2) (op_zdhdqgje := op2) (op_mcowbhvd := op3) (ev_odufttua := ev3)
      (op_mpewyhtv := op4) (ev_ngufkkyx := ev4) (op_wtwcenmr := op5) (ev_lxmejyli := ev5)
      (op_zydyxzyl := op6) (op_illucsyw := op7) (ev_ixaxnlzx := ev6) (op_whihqlmc := op8)
      (ev_vsxxjcgq := ev7) (op_ytetfspj := op9) (op_kbkuxszt := op10) (ev_wewjikok := ev8)
      (ev_rwmzpqjs := ev9) (op_btgsfrlq := op11) (ev_gnprnthg := ev10) (op_wmaayhol := op12)
      (op_dtckxtdo := op13) (op_npuzaeri := op14) (ev_ujcdgijd := ev11) (op_ckuavxuo := op15)
      (hne_mvqylmzn := hneG) (he_lyliuouj := hr) (hc_mvtaqtmk := hc) .. =>
    subst hr
    obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec hW
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, cus, hfn_eq, rca, rcl⟩ := TmOExact.const_of_load hfn ldh
    obtain ⟨cd, bac, hcd, hcd_nl, hcd_ind, hcd_np, hcd_nf, rfl, hcb, r_cblk, rfl, rfl, rfl⟩ :=
      (hC rca evg1 ld1).1 _ _ _ _ _ _ _ _ rfl
    have ext12 := evsp.heap_extends.trans evg1.heap_extends
    obtain ⟨sd, bas, hsd, hsd_nl, hsd_np, hsd_ni, hsd_nc, hsd_idx, rfl, -, rfl, rfl, rfl, hsb,
        r_sblk, rfl⟩ :=
      (hI (Bytes.repAddressRef_heapMono₂ addrTy ext12 ra) evg2 ld2).1 _ _ _ _ _ _ _ _ rfl
    have ext_g12 := evg1.heap_extends.trans evg2.heap_extends
    have hargs3 := tmOExactList_mono ext_g12 hargs
    have hcl3 := rcl.mono ext_g12
    have hargs_lt : W0.getAppArgs.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xargs], _⟩) (by rw [hc]; simp) (by simp)
        (tmOExactList_mono
          (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
            (ev4.heap_extends.trans (ev5.heap_extends.trans ev6.heap_extends))))) hargs3)
    have hclvls_lt : cus.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xcl], _⟩) (by rw [hc]; simp) (by simp)
        (hcl3.mono (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
          (ev4.heap_extends.trans (ev5.heap_extends.trans (ev6.heap_extends.trans
            (ev7.heap_extends.trans ev8.heap_extends))))))))
    obtain ⟨hgate, -, -⟩ := red_proj_gate_eval hcb hsb hcd_nl hcd_ind hcd_np hcd_nf
      hsd_nl hsd_np hsd_ni hsd_nc hsd_idx
      (Bytes.repAddressRef_heapMono₂ addrTy evg2.heap_extends r_cblk) r_sblk hargs3 hcl3
      hargs_lt hclvls_lt ev1 op1 ev2 op2 op3 ev3 op4 ev4 op5 ev5 op6 op7 ev6 op8 ev7 op9 op10 ev8
      ev9 op11 ev10 op12 op13 op14 ev11 op15
    have hgf : projGate cd sd cus W0.getAppArgs i.val = false := by
      cases hg : projGate cd sd cus W0.getAppArgs i.val
      · rfl
      · rw [hg] at hgate; exact (hneG hgate).elim
    refine ⟨fun xf hxf => ?_, fun _ => ?_⟩
    · injection hxf with hp; injection hp with h0 _
      exact absurd (Value.field.inj h0) (by decide)
    · unfold projStep; rw [hfn_eq, hA, hcd, hA, hsd, hgf]; rfl
  | .Const_Ctor_Induct_n1_other (m_ojfleyqm := m1) (cs_mtergxtu := cs1) (x_head := xhd)
      (x_args := xargs) (x_caddr := xca) (x_clvls := xcl) (m_tdzaboly := m2) (p_fvrbdqgt := pci1)
      (cs_tkdqmhev := cs2) (x_cnl := xcnl) (x_cblock := xcblk) (x_cind := xcind)
      (x_nparams := xnp) (x_nfields := xnf) (m_rzlfecwb := m3) (p_murouqmk := pci2)
      (cs_bqjhgrbx := cs3) (x_snl := xsnl) (x_sty := xsty) (x_snp := xsnp) (x_sni := xsni)
      (x_snc := xsnc) (x_sblock := xsblk) (x_sidx := xsidx)
      (ev_dnbgofcn := evsp) (ld_bolbylmd := ldh) (ev_ceowrmgg := evg1) (ld_hkyzglrm := ld1)
      (ev_fruvizab := evg2) (ld_vandvewq := ld2) (ev_kveftqvh := ev1) (op_hkoxximr := op1)
      (ev_mkroeoak := ev2) (op_zdhdqgje := op2) (op_mcowbhvd := op3) (ev_odufttua := ev3)
      (op_mpewyhtv := op4) (ev_ngufkkyx := ev4) (op_wtwcenmr := op5) (ev_lxmejyli := ev5)
      (op_zydyxzyl := op6) (op_illucsyw := op7) (ev_ixaxnlzx := ev6) (op_whihqlmc := op8)
      (ev_vsxxjcgq := ev7) (op_ytetfspj := op9) (op_kbkuxszt := op10) (ev_wewjikok := ev8)
      (ev_rwmzpqjs := ev9) (op_btgsfrlq := op11) (ev_gnprnthg := ev10) (op_wmaayhol := op12)
      (op_dtckxtdo := op13) (op_npuzaeri := op14) (ev_ujcdgijd := ev11) (op_ckuavxuo := op15)
      (ev_kjhrvkku := evmod) (hne_dnwjfyfz := hneM) (he_xziewoec := hr) (hc_ldpbsnvd := hc) .. =>
    subst hr
    obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec hW
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, cus, hfn_eq, rca, rcl⟩ := TmOExact.const_of_load hfn ldh
    obtain ⟨cd, bac, hcd, hcd_nl, hcd_ind, hcd_np, hcd_nf, rfl, hcb, r_cblk, rfl, rfl, rfl⟩ :=
      (hC rca evg1 ld1).1 _ _ _ _ _ _ _ _ rfl
    have ext12 := evsp.heap_extends.trans evg1.heap_extends
    obtain ⟨sd, bas, hsd, hsd_nl, hsd_np, hsd_ni, hsd_nc, hsd_idx, rfl, -, rfl, rfl, rfl, hsb,
        r_sblk, rfl⟩ :=
      (hI (Bytes.repAddressRef_heapMono₂ addrTy ext12 ra) evg2 ld2).1 _ _ _ _ _ _ _ _ rfl
    have ext_g12 := evg1.heap_extends.trans evg2.heap_extends
    have hargs3 := tmOExactList_mono ext_g12 hargs
    have hcl3 := rcl.mono ext_g12
    have hargs_lt : W0.getAppArgs.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xargs], _⟩) (by rw [hc]; simp) (by simp)
        (tmOExactList_mono
          (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
            (ev4.heap_extends.trans (ev5.heap_extends.trans ev6.heap_extends))))) hargs3)
    have hclvls_lt : cus.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xcl], _⟩) (by rw [hc]; simp) (by simp)
        (hcl3.mono (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
          (ev4.heap_extends.trans (ev5.heap_extends.trans (ev6.heap_extends.trans
            (ev7.heap_extends.trans ev8.heap_extends))))))))
    obtain ⟨hgate, hm_eq, -⟩ := red_proj_gate_eval hcb hsb hcd_nl hcd_ind hcd_np hcd_nf
      hsd_nl hsd_np hsd_ni hsd_nc hsd_idx
      (Bytes.repAddressRef_heapMono₂ addrTy evg2.heap_extends r_cblk) r_sblk hargs3 hcl3
      hargs_lt hclvls_lt ev1 op1 ev2 op2 op3 ev3 op4 ev4 op5 ev5 op6 op7 ev6 op8 ev7 op9 op10 ev8
      ev9 op11 ev10 op12 op13 op14 ev11 op15
    subst hm_eq
    have hgt : projGate cd sd cus W0.getAppArgs i.val = true := by
      cases hg : projGate cd sd cus W0.getAppArgs i.val
      · rw [hg] at hgate; exact absurd (Value.field.inj hgate) (by decide)
      · rfl
    obtain ⟨bm, hbm, hbm_r⟩ := hM r_sblk evmod
    rw [hsb] at hbm
    have hbt : bm = true := by
      cases bm
      · exact (hneM hbm_r).elim
      · rfl
    subst hbt
    refine ⟨fun xf hxf => ?_, fun _ => ?_⟩
    · injection hxf with hp; injection hp with h0 _
      exact absurd (Value.field.inj h0) (by decide)
    · unfold projStep; rw [hfn_eq, hA, hcd, hA, hsd, hgt, if_pos rfl, hbm]
  | .Const_Ctor_Induct_n1_n0_other (m_ojfleyqm := m1) (cs_mtergxtu := cs1) (x_head := xhd)
      (x_args := xargs) (x_caddr := xca) (x_clvls := xcl) (m_tdzaboly := m2) (p_fvrbdqgt := pci1)
      (cs_tkdqmhev := cs2) (x_cnl := xcnl) (x_cblock := xcblk) (x_cind := xcind)
      (x_nparams := xnp) (x_nfields := xnf) (m_rzlfecwb := m3) (p_murouqmk := pci2)
      (cs_bqjhgrbx := cs3) (x_snl := xsnl) (x_sty := xsty) (x_snp := xsnp) (x_sni := xsni)
      (x_snc := xsnc) (x_sblock := xsblk) (x_sidx := xsidx)
      (ev_dnbgofcn := evsp) (ld_bolbylmd := ldh) (ev_ceowrmgg := evg1) (ld_hkyzglrm := ld1)
      (ev_fruvizab := evg2) (ld_vandvewq := ld2) (ev_kveftqvh := ev1) (op_hkoxximr := op1)
      (ev_mkroeoak := ev2) (op_zdhdqgje := op2) (op_mcowbhvd := op3) (ev_odufttua := ev3)
      (op_mpewyhtv := op4) (ev_ngufkkyx := ev4) (op_wtwcenmr := op5) (ev_lxmejyli := ev5)
      (op_zydyxzyl := op6) (op_illucsyw := op7) (ev_ixaxnlzx := ev6) (op_whihqlmc := op8)
      (ev_vsxxjcgq := ev7) (op_ytetfspj := op9) (op_kbkuxszt := op10) (ev_wewjikok := ev8)
      (ev_rwmzpqjs := ev9) (op_btgsfrlq := op11) (ev_gnprnthg := ev10) (op_wmaayhol := op12)
      (op_dtckxtdo := op13) (op_npuzaeri := op14) (ev_ujcdgijd := ev11) (op_ckuavxuo := op15)
      (ev_kjhrvkku := evmod) (ev_iburkzei := evtsn) (hne_hashxtwn := hneT)
      (he_airsfoxk := hr) (hc_iaaxxtji := hc) .. =>
    subst hr
    obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec hW
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, cus, hfn_eq, rca, rcl⟩ := TmOExact.const_of_load hfn ldh
    obtain ⟨cd, bac, hcd, hcd_nl, hcd_ind, hcd_np, hcd_nf, rfl, hcb, r_cblk, rfl, rfl, rfl⟩ :=
      (hC rca evg1 ld1).1 _ _ _ _ _ _ _ _ rfl
    have ext12 := evsp.heap_extends.trans evg1.heap_extends
    obtain ⟨sd, bas, hsd, hsd_nl, hsd_np, hsd_ni, hsd_nc, hsd_idx, rfl, hsty, rfl, rfl, rfl, hsb,
        r_sblk, rfl⟩ :=
      (hI (Bytes.repAddressRef_heapMono₂ addrTy ext12 ra) evg2 ld2).1 _ _ _ _ _ _ _ _ rfl
    have ext_g12 := evg1.heap_extends.trans evg2.heap_extends
    have hargs3 := tmOExactList_mono ext_g12 hargs
    have hcl3 := rcl.mono ext_g12
    have hargs_lt : W0.getAppArgs.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xargs], _⟩) (by rw [hc]; simp) (by simp)
        (tmOExactList_mono
          (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
            (ev4.heap_extends.trans (ev5.heap_extends.trans ev6.heap_extends))))) hargs3)
    have hclvls_lt : cus.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xcl], _⟩) (by rw [hc]; simp) (by simp)
        (hcl3.mono (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
          (ev4.heap_extends.trans (ev5.heap_extends.trans (ev6.heap_extends.trans
            (ev7.heap_extends.trans ev8.heap_extends))))))))
    obtain ⟨hgate, hm_eq, -⟩ := red_proj_gate_eval hcb hsb hcd_nl hcd_ind hcd_np hcd_nf
      hsd_nl hsd_np hsd_ni hsd_nc hsd_idx
      (Bytes.repAddressRef_heapMono₂ addrTy evg2.heap_extends r_cblk) r_sblk hargs3 hcl3
      hargs_lt hclvls_lt ev1 op1 ev2 op2 op3 ev3 op4 ev4 op5 ev5 op6 op7 ev6 op8 ev7 op9 op10 ev8
      ev9 op11 ev10 op12 op13 op14 ev11 op15
    subst hm_eq
    have hgt : projGate cd sd cus W0.getAppArgs i.val = true := by
      cases hg : projGate cd sd cus W0.getAppArgs i.val
      · rw [hg] at hgate; exact absurd (Value.field.inj hgate) (by decide)
      · rfl
    obtain ⟨bm, hbm, hbm_r⟩ := hM r_sblk evmod
    rw [hsb] at hbm
    have hbf : bm = false := by
      cases bm
      · rfl
      · exact absurd (Value.field.inj hbm_r) (by decide)
    subst hbf
    have htsn := type_sort_never_zeta_spec (by omega) (hsty.mono evmod.heap_extends)
      (hcl3.mono evmod.heap_extends) (sub fun c hc' => by rw [hc]; simp [hc']) evtsn
    have htf : typeSortNever sd.ty sd.np cus = false := by
      cases ht : typeSortNever sd.ty sd.np cus
      · rfl
      · rw [ht] at htsn; exact (hneT htsn).elim
    refine ⟨fun xf hxf => ?_, fun _ => ?_⟩
    · injection hxf with hp; injection hp with h0 _
      exact absurd (Value.field.inj h0) (by decide)
    · unfold projStep; rw [hfn_eq, hA, hcd, hA, hsd, hgt, if_pos rfl, hbm, htf]; rfl
  | .Const_Ctor_Induct_n1_n0_n1 (m_ojfleyqm := m1) (cs_mtergxtu := cs1) (x_head := xhd)
      (x_args := xargs) (x_caddr := xca) (x_clvls := xcl) (m_tdzaboly := m2) (p_fvrbdqgt := pci1)
      (cs_tkdqmhev := cs2) (x_cnl := xcnl) (x_cblock := xcblk) (x_cind := xcind)
      (x_nparams := xnp) (x_nfields := xnf) (m_rzlfecwb := m3) (p_murouqmk := pci2)
      (cs_bqjhgrbx := cs3) (x_snl := xsnl) (x_sty := xsty) (x_snp := xsnp) (x_sni := xsni)
      (x_snc := xsnc) (x_sblock := xsblk) (x_sidx := xsidx) (v_bjnhiibm := vfield)
      (v_gmikqusq := vidx)
      (ev_dnbgofcn := evsp) (ld_bolbylmd := ldh) (ev_ceowrmgg := evg1) (ld_hkyzglrm := ld1)
      (ev_fruvizab := evg2) (ld_vandvewq := ld2) (ev_kveftqvh := ev1) (op_hkoxximr := op1)
      (ev_mkroeoak := ev2) (op_zdhdqgje := op2) (op_mcowbhvd := op3) (ev_odufttua := ev3)
      (op_mpewyhtv := op4) (ev_ngufkkyx := ev4) (op_wtwcenmr := op5) (ev_lxmejyli := ev5)
      (op_zydyxzyl := op6) (op_illucsyw := op7) (ev_ixaxnlzx := ev6) (op_whihqlmc := op8)
      (ev_vsxxjcgq := ev7) (op_ytetfspj := op9) (op_kbkuxszt := op10) (ev_wewjikok := ev8)
      (ev_rwmzpqjs := ev9) (op_btgsfrlq := op11) (ev_gnprnthg := ev10) (op_wmaayhol := op12)
      (op_dtckxtdo := op13) (op_npuzaeri := op14) (ev_ujcdgijd := ev11) (op_ckuavxuo := op15)
      (ev_kjhrvkku := evmod) (ev_iburkzei := evtsn) (he_apqfdctr := hr)
      (op_fkacnbfp := op_idx) (ev_wvzzmegf := evlk) (he_brmzxasb := hh) (hc_iijtlgjg := hc) .. =>
    subst hr hh
    obtain ⟨hfn, -, hargs⟩ := collect_spine_zeta_spec hW
      (sub fun c hc' => by rw [hc]; simp [hc']) evsp
    obtain ⟨ca, cus, hfn_eq, rca, rcl⟩ := TmOExact.const_of_load hfn ldh
    obtain ⟨cd, bac, hcd, hcd_nl, hcd_ind, hcd_np, hcd_nf, rfl, hcb, r_cblk, rfl, rfl, rfl⟩ :=
      (hC rca evg1 ld1).1 _ _ _ _ _ _ _ _ rfl
    have ext12 := evsp.heap_extends.trans evg1.heap_extends
    obtain ⟨sd, bas, hsd, hsd_nl, hsd_np, hsd_ni, hsd_nc, hsd_idx, rfl, hsty, rfl, rfl, rfl, hsb,
        r_sblk, rfl⟩ :=
      (hI (Bytes.repAddressRef_heapMono₂ addrTy ext12 ra) evg2 ld2).1 _ _ _ _ _ _ _ _ rfl
    have ext_g12 := evg1.heap_extends.trans evg2.heap_extends
    have hargs3 := tmOExactList_mono ext_g12 hargs
    have hcl3 := rcl.mono ext_g12
    have hargs_lt : W0.getAppArgs.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xargs], _⟩) (by rw [hc]; simp) (by simp)
        (tmOExactList_mono
          (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
            (ev4.heap_extends.trans (ev5.heap_extends.trans ev6.heap_extends))))) hargs3)
    have hclvls_lt : cus.length < 2 ^ 39 :=
      RomBound.bounded_length_lt bd (c := ⟨_, [xcl], _⟩) (by rw [hc]; simp) (by simp)
        (hcl3.mono (ev1.heap_extends.trans (ev2.heap_extends.trans (ev3.heap_extends.trans
          (ev4.heap_extends.trans (ev5.heap_extends.trans (ev6.heap_extends.trans
            (ev7.heap_extends.trans ev8.heap_extends))))))))
    obtain ⟨hgate, hm_eq, hi32⟩ := red_proj_gate_eval hcb hsb hcd_nl hcd_ind hcd_np hcd_nf
      hsd_nl hsd_np hsd_ni hsd_nc hsd_idx
      (Bytes.repAddressRef_heapMono₂ addrTy evg2.heap_extends r_cblk) r_sblk hargs3 hcl3
      hargs_lt hclvls_lt ev1 op1 ev2 op2 op3 ev3 op4 ev4 op5 ev5 op6 op7 ev6 op8 ev7 op9 op10 ev8
      ev9 op11 ev10 op12 op13 op14 ev11 op15
    subst hm_eq
    have hgt : projGate cd sd cus W0.getAppArgs i.val = true := by
      cases hg : projGate cd sd cus W0.getAppArgs i.val
      · rw [hg] at hgate; exact absurd (Value.field.inj hgate) (by decide)
      · rfl
    obtain ⟨bm, hbm, hbm_r⟩ := hM r_sblk evmod
    rw [hsb] at hbm
    have hbf : bm = false := by
      cases bm
      · rfl
      · exact absurd (Value.field.inj hbm_r) (by decide)
    subst hbf
    have htsn := type_sort_never_zeta_spec (by omega) (hsty.mono evmod.heap_extends)
      (hcl3.mono evmod.heap_extends) (sub fun c hc' => by rw [hc]; simp [hc']) evtsn
    have htt : typeSortNever sd.ty sd.np cus = true := by
      cases ht : typeSortNever sd.ty sd.np cus
      · rw [ht] at htsn; exact absurd (Value.field.inj htsn) (by decide)
      · rfl
    refine ⟨fun xf hxf => ?_, fun hnt => (hnt vfield rfl).elim⟩
    injection hxf with hp; injection hp with _ hp2; injection hp2 with hxf'
    subst hxf'
    have hi_cast : (.field i : SourceValue F) = .field (i.val : F) := by
      congr 1; exact (ZMod.natCast_zmod_val i).symm
    rw [hi_cast] at op_idx
    obtain rfl := binop_add_nat op_idx
    have hargs_lk := tmOExactList_mono (evmod.heap_extends.trans evtsn.heap_extends) hargs3
    obtain ⟨⟨y, hy, hyr⟩, rfl⟩ := kexpr_lookup evlk hargs_lk
    rw [fval_natCast (by omega)] at hy
    refine ⟨y, ?_, hyr⟩
    unfold projStep
    rw [hfn_eq, hA, hcd, hA, hsd, hgt, if_pos rfl, hbm, htt, if_pos rfl, hy]

/-! ## Fuel and head normalization -/

/-- **`hnfSpine V` reaches `e'` from `e` on the spine `sp`**: at every fuel from some fuel on. -/
def HnfTo (V : ReconView) (e : KExpr) (sp : List KExpr) (e' : KExpr) : Prop :=
  ∃ n₀, ∀ n, n₀ ≤ n → hnfSpine V n e sp = some e'

theorem HnfTo.exists {V : ReconView} {e e' : KExpr} {sp : List KExpr} (h : HnfTo V e sp e') :
    ∃ n, hnfSpine V n e sp = some e' :=
  let ⟨n₀, hn⟩ := h; ⟨n₀, hn n₀ le_rfl⟩

theorem HnfTo.step {V : ReconView} {e e₁ e' : KExpr} {sp sp₁ : List KExpr}
    (hstep : ∀ n, hnfSpine V (n + 1) e sp = hnfSpine V n e₁ sp₁) (h : HnfTo V e₁ sp₁ e') :
    HnfTo V e sp e' := by
  obtain ⟨n₀, hn⟩ := h
  refine ⟨n₀ + 1, fun n hle => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hstep]
  exact hn m (by omega)

theorem HnfTo.done {V : ReconView} {e e' : KExpr} {sp : List KExpr}
    (hdone : ∀ n, hnfSpine V (n + 1) e sp = some e') : HnfTo V e sp e' := by
  refine ⟨1, fun n hle => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hdone m

private theorem tmExact_proj_resolved {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {E : KExpr} {p x y z : SourceValue F} {a : Bytes.Address} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Proj" [x, y, z]))
    (ha : Bytes.RepAddressRef addrTy h a x) : Resolved (κ (ixAddr a)) := by
  cases rep with
  | @proj _ _ _ _ a' _ _ res _ cell ra re =>
    obtain ⟨-, hxs⟩ := IxVM.Refinement.Core.load_cell cell hl
    injection hxs with hx
    subst hx
    have e : a' = a := Bytes.repAddressRef_inj U32.Goldilocks.compatible ra ha
    rw [← e]
    exact res
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _ | litStr cell _ _ =>
    exact (IxVM.Refinement.Core.load_cell_ne cell hl (by decide)).elim

private theorem hnfSpine_stuck_exact {V : ReconView} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p v : SourceValue F} (rep : TmExact κ d Γ h k E p)
    (hl : loadValue h p = .ok v)
    (happ : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "App" vs)
    (hlam : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Lam" vs)
    (hconst : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "Const" vs)
    (hlet : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs)
    (hproj : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Proj" vs)
    (sp : List KExpr) (n : Nat) :
    hnfSpine V (n + 1) E sp = some (Ix.Kernel.Expr.mkAppN E sp) := by
  cases rep with
  | app cell _ _ =>
    rw [Lib.load_enum_cell cell] at hl; injection hl with hv; exact (happ _ rfl hv.symm).elim
  | lam cell _ _ _ =>
    rw [Lib.load_enum_cell cell] at hl; injection hl with hv; exact (hlam _ rfl hv.symm).elim
  | const cell _ _ =>
    rw [Lib.load_enum_cell cell] at hl; injection hl with hv; exact (hconst _ rfl hv.symm).elim
  | letE cell _ _ _ =>
    rw [Lib.load_enum_cell cell] at hl; injection hl with hv; exact (hlet _ rfl hv.symm).elim
  | proj cell _ _ =>
    rw [Lib.load_enum_cell cell] at hl; injection hl with hv; exact (hproj _ rfl hv.symm).elim
  | bvarLocal _ _ _ | bvarFree _ _ _ _ | sort _ _ | forallE _ _ _ _ | litNat _ _ _
  | litStr _ _ _ => rfl

/-- **`KernelCheck::recon_whnf_spine(rc, head, spine)` is `hnfSpine V`** on `TmOExact`, with
`NotLet` on the output, from the five single-call store predicates. -/
theorem recon_whnf_spine_spec {V : ReconView}
    (hA : AddrOf κ V) (hD : DefnAnswers κ V) (hI : IndAnswers κ V)
    (hC : CtorOfAnswers V) (hM : ModeledAnswers V) :
    ∀ (N : Nat) {xrc xe xsp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
      {Sp : List KExpr}, cs.length < N →
      ObsFn W "KernelCheck::recon_whnf_spine" [xrc, xe, xsp] h r h' cs →
      IxVM.Consistency.Bounded cs → TmOExact κ h E xe →
      RepList kexprListEnum (TmOExact κ) h Sp xsp →
      Heap.Extends h h' ∧ ∃ E', HnfTo V E Sp E' ∧ TmOExact κ h' E' r ∧ NotLet h' r := by
  intro N
  induction N with
  | zero => intro _ _ _ _ _ _ _ _ _ hlen; exact absurd hlen (Nat.not_lt_zero _)
  | succ N ih =>
    intro xrc xe xsp r h h' cs E Sp hlen ev hbnd hE hS
    have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
      fun hs => RomBound.bounded_mono hbnd hs
    have hext : Heap.Extends h h' := ObsFn.heap_extends ev
    obtain ⟨kE, rE⟩ := hE
    match Obs.«KernelCheck::recon_whnf_spine».obsx ev with
    | .App (x_f := xf) (x_a := xa) (cs_izjldmac := cs1) (m_bbyzgutu := m1)
        (ld_bolbylmd := ld) (hm_edpnchks := hm) (ev_liflsqzo := ev1) (hc_xkhdrnsx := hc) .. =>
      subst hm
      obtain ⟨Ef, Ea, rfl, rf, ra⟩ := rE.app_of_load ld
      have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [xa, xsp]]) :=
        Heap.Extends.snoc _ _
      have hS' := Lib.rep_store_cons tmOExact_heapMono₂ (TmOExact.ofTmExact ra) hS
      obtain ⟨-, E', hto, hr, hnl⟩ := ih (by rw [hc] at hlen; simp at hlen; omega) ev1
        (sub fun c hc' => by rw [hc]; simp [hc']) ((TmOExact.ofTmExact rf).mono ext) hS'
      exact ⟨hext, E', HnfTo.step (fun _ => rfl) hto, hr, hnl⟩
    | .Lam_Cons (x_body := xbody) (x_a := xa) (x_rest := xrest) (cs_qmvpbbie := cs2)
        (v_ggmnfawe := v1) (m_ptxuxmew := m1) (cs_xiwgvbym := cs1)
        (ld_bolbylmd := ld) (ld_mgdxvnfg := lds) (ev_gpnobhya := evi)
        (ev_kossixkw := ev1) (hc_qvdsoavs := hc) .. =>
      obtain ⟨T, B, ℓ, rfl, -, rB, -⟩ := rE.lam_of_load ld
      obtain ⟨A, As, rfl, hA1, hAs⟩ := IxVM.Refinement.Core.RepList.cons_of_load hS lds
      have hinst := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc'])
        (TmOExact.ofTmExact rB) hA1 evi
      obtain ⟨-, E', hto, hr, hnl⟩ := ih (by rw [hc] at hlen; simp at hlen; omega) ev1
        (sub fun c hc' => by rw [hc]; simp [hc']) hinst (tmOExactList_mono evi.heap_extends hAs)
      exact ⟨hext, E', HnfTo.step (fun _ => rfl) hto, hr, hnl⟩
    | .Lam_Nil (ld_bolbylmd := ld) (ld_mgdxvnfg := lds) (he_qcfircfw := hr)
        (he_mnrwwkgr := hh) .. =>
      subst hr hh
      obtain ⟨T, B, ℓ, rfl, -, -, -⟩ := rE.lam_of_load ld
      obtain rfl := IxVM.Refinement.Core.RepList.nil_of_load hS lds
      have hnl : NotLet h xe := ⟨_, ld, fun _ _ h => by injection h with _ hc; exact absurd hc (by decide)⟩
      exact ⟨hext, _, HnfTo.done fun _ => rfl, ⟨kE, rE⟩, hnl⟩
    | .Const_n1_bind (x_addr := xaddr) (x_lvls := xlvls) (m_tdzaboly := m2) (cs_rziuyuaw := cs2)
        (v_iqukuotq := vci) (m_zxxyeiga := m1) (p_lnqccfus := pci) (cs_axpnhoxg := cs1)
        (x_body := xbody) (cs_lmbvbikz := cs3) (ld_bolbylmd := ld) (ev_bhmgkkza := evg)
        (ld_kabykbto := ldci) (ev_cijhqsqa := evu) (ev_vyxbtslj := ev1) (hc_vqjdujfq := hc) .. =>
      obtain ⟨a, us, rfl, ra, rus⟩ := rE.const_of_load ld
      obtain ⟨hyes, -⟩ := red_unfold_spec hD ra (rus.mono evg.heap_extends) evg ldci evu
        (sub fun c hc' => by rw [hc]; simp [hc'])
      obtain ⟨b, hub, hb⟩ := hyes xbody rfl
      have ext := evg.heap_extends.trans evu.heap_extends
      obtain ⟨-, E', hto, hr, hnl⟩ := ih (by rw [hc] at hlen; simp at hlen; omega) ev1
        (sub fun c hc' => by rw [hc]; simp [hc']) hb (tmOExactList_mono ext hS)
      exact ⟨hext, E', HnfTo.step (fun _ => by simp [hnfSpine, hub]) hto, hr, hnl⟩
    | .Const_other (x_addr := xaddr) (x_lvls := xlvls) (v_jknrfqpi := vu) (m_tdzaboly := m2)
        (cs_rziuyuaw := cs2) (v_iqukuotq := vci) (m_zxxyeiga := m1) (p_lnqccfus := pci)
        (cs_axpnhoxg := cs1) (cs_gmxujosg := cs3) (ld_bolbylmd := ld) (ev_bhmgkkza := evg)
        (ld_kabykbto := ldci) (ev_cijhqsqa := evu) (ev_wgzmcbja := eva) (hc_cnrhqnxp := hc)
        (hnt_wbosofze := hnt) .. =>
      obtain ⟨a, us, rfl, ra, rus⟩ := rE.const_of_load ld
      obtain ⟨-, hno⟩ := red_unfold_spec hD ra (rus.mono evg.heap_extends) evg ldci evu
        (sub fun c hc' => by rw [hc]; simp [hc'])
      have hun := hno hnt
      have ext := evg.heap_extends.trans evu.heap_extends
      have hnl0 : NotLet h xe := ⟨_, ld, fun _ _ h => by injection h with _ hc; exact absurd hc (by decide)⟩
      obtain ⟨-, hr, hnl⟩ := apply_spine_spec Sp eva (TmOExact.mono ext ⟨kE, rE⟩)
        (hnl0.mono ext) (tmOExactList_mono ext hS)
      exact ⟨hext, _, HnfTo.done fun _ => by simp [hnfSpine, hun], hr, hnl⟩
    | .Let (x_val := xval) (x_body := xbody) (cs_rzfcbnis := cs2) (v_fjpmimbl := v1)
        (m_jfbjeidy := m1) (cs_swwhkahe := cs1) (ld_bolbylmd := ld) (ev_gfkycmwo := evi)
        (ev_bzamebpj := ev1) (hc_qubwlzze := hc) .. =>
      obtain ⟨T, V0, B, rfl, -, rV, rB⟩ := rE.letE_of_load ld
      have hinst := expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc'])
        (TmOExact.ofTmExact rB) (TmOExact.ofTmExact rV) evi
      obtain ⟨-, E', hto, hr, hnl⟩ := ih (by rw [hc] at hlen; simp at hlen; omega) ev1
        (sub fun c hc' => by rw [hc]; simp [hc']) hinst (tmOExactList_mono evi.heap_extends hS)
      exact ⟨hext, E', hto, hr, hnl⟩
    | .Proj_n1_bind (x_s := xs) (x_i := xi) (x_inner := xinner) (v_wckthhnn := vw)
        (m_aztoikcu := ma) (cs_vldecewa := csw) (m_xiabcmuc := mx) (cs_dqottkop := csp)
        (x_field := xfield) (cs_liiaseeo := cs1) (ld_bolbylmd := ld) (ev_kciamzqg := evw)
        (ev_qxfoztai := evp) (ev_xvwhkuco := ev1) (hc_hxfzpbii := hc) .. =>
      obtain ⟨a, i, Es, rfl, rfl, ra, rEs⟩ := rE.proj_of_load ld
      obtain ⟨cs_s, m_d, hmd, evs, hcw⟩ := Obs.«KernelCheck::recon_whnf».obs evw
      subst hmd
      have extd : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
      obtain ⟨extw, W0, htoW, hW, -⟩ := ih
        (by rw [hc, hcw] at hlen; simp at hlen; omega) evs
        (sub fun c hc' => by rw [hc, hcw]; simp [hc']) ((TmOExact.ofTmExact rEs).mono extd)
        (Lib.rep_store_nil h)
      have exta := extd.trans extw
      obtain ⟨hyes, -⟩ := red_proj_zeta_spec hA hI hC hM
        (Bytes.repAddressRef_heapMono₂ addrTy exta ra) hW
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      obtain ⟨y, hy, hyr⟩ := hyes xfield rfl
      have extx := exta.trans evp.heap_extends
      obtain ⟨-, E', hto, hr, hnl⟩ := ih (by rw [hc] at hlen; simp at hlen; omega) ev1
        (sub fun c hc' => by rw [hc]; simp [hc']) hyr (tmOExactList_mono extx hS)
      obtain ⟨n1, hn1⟩ := htoW
      obtain ⟨n2, hn2⟩ := hto
      refine ⟨hext, E', ⟨max n1 n2 + 1, fun n hle => ?_⟩, hr, hnl⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [hnfSpine, hn1 m (by omega), hy]
      exact hn2 m (by omega)
    | .Proj_other (x_s := xs) (x_i := xi) (x_inner := xinner) (v_wckthhnn := vw)
        (m_aztoikcu := ma) (cs_vldecewa := csw) (v_maitkftz := vp) (m_xiabcmuc := mx)
        (cs_dqottkop := csp) (cs_yxibpzpu := csa) (m_ccdxmojk := mc)
        (ld_bolbylmd := ld) (ev_kciamzqg := evw) (ev_qxfoztai := evp) (hm_bxkmumhu := hmc)
        (ev_zocgnssu := eva) (hc_idnhlnac := hc) (hnt_ywgwxtxn := hnt) .. =>
      obtain ⟨a, i, Es, rfl, rfl, ra, rEs⟩ := rE.proj_of_load ld
      have hres := tmExact_proj_resolved rE ld ra
      have hperm := rE.toTm.proj_permitted ld ra
      subst hmc
      obtain ⟨cs_s, m_d, hmd, evs, hcw⟩ := Obs.«KernelCheck::recon_whnf».obs evw
      subst hmd
      have extd : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
      obtain ⟨extw, W0, htoW, hW, -⟩ := ih
        (by rw [hc, hcw] at hlen; simp at hlen; omega) evs
        (sub fun c hc' => by rw [hc, hcw]; simp [hc']) ((TmOExact.ofTmExact rEs).mono extd)
        (Lib.rep_store_nil h)
      have exta := extd.trans extw
      obtain ⟨-, hno⟩ := red_proj_zeta_spec hA hI hC hM
        (Bytes.repAddressRef_heapMono₂ addrTy exta ra) hW
        (sub fun c hc' => by rw [hc]; simp [hc']) evp
      have hps := hno hnt
      have extx := evp.heap_extends
      have extc : Heap.Extends mx
          (mx ++ [.construct "KernelTypes::KExprNode" "Proj" [xs, .field i, vw]]) :=
        Heap.Extends.snoc _ _
      obtain ⟨kW, rW⟩ := hW
      have hnode : TmOExact κ (mx ++ [.construct "KernelTypes::KExprNode" "Proj" [xs, .field i, vw]])
          (.proj (κ (ixAddr a)) (ZMod.val i) W0)
          (.ptr (.enum "KernelTypes::KExprNode") mx.length) :=
        ⟨kW, .proj (by simp)
          (Bytes.repAddressRef_heapMono₂ addrTy ((exta.trans extx).trans extc) ra)
          (rW.mono (extx.trans extc))⟩
      have hnlP : NotLet (mx ++ [.construct "KernelTypes::KExprNode" "Proj" [xs, .field i, vw]])
          (.ptr (.enum "KernelTypes::KExprNode") mx.length) :=
        notLet_of_cell (by simp) (by decide)
      obtain ⟨-, hr, hnl⟩ := apply_spine_spec Sp eva hnode hnlP
        (tmOExactList_mono ((exta.trans extx).trans extc) hS)
      obtain ⟨n1, hn1⟩ := htoW
      refine ⟨hext, _, ⟨n1 + 1, fun n hle => ?_⟩, hr, hnl⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [hnfSpine, hn1 m (by omega), hps]
    | .other (v_hirlhoca := v) (cs_dainthco := csa) (ld_bolbylmd := ld)
        (hne_ebjedqqk := hne_app) (hne_yypcejwr := hne_lam) (hne_uulqutnf := hne_const)
        (hne_ttotnwna := hne_let) (hne_dhsxwcwn := hne_proj) (ev_crofnell := eva) .. =>
      have hnl0 : NotLet h xe := ⟨v, ld, hne_let⟩
      obtain ⟨-, hr, hnl⟩ := apply_spine_spec Sp eva ⟨kE, rE⟩ hnl0 hS
      exact ⟨hext, _, HnfTo.done fun n =>
        hnfSpine_stuck_exact rE ld hne_app hne_lam hne_const hne_let hne_proj Sp n, hr, hnl⟩

/-- **`KernelCheck::recon_whnf(rc, e)` is `hnf V`** on `TmOExact`, yielding `NotLet`. -/
theorem recon_whnf_spec {V : ReconView}
    (hA : AddrOf κ V) (hD : DefnAnswers κ V) (hI : IndAnswers κ V)
    (hC : CtorOfAnswers V) (hM : ModeledAnswers V)
    {xrc xe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
    (ev : ObsFn W "KernelCheck::recon_whnf" [xrc, xe] h r h' cs)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E xe) :
    Heap.Extends h h' ∧ ∃ E', HnfTo V E [] E' ∧ TmOExact κ h' E' r ∧ NotLet h' r := by
  obtain ⟨cs1, m, hm, ev1, hc⟩ := Obs.«KernelCheck::recon_whnf».obs ev
  subst hm
  have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Nil" []]) := Heap.Extends.snoc _ _
  obtain ⟨ext', hr⟩ := recon_whnf_spine_spec hA hD hI hC hM (cs1.length + 1) (Nat.lt_succ_self _)
    ev1 (RomBound.bounded_mono hbnd fun c hc' => by rw [hc]; simp [hc']) (hE.mono ext)
    (Lib.rep_store_nil h)
  exact ⟨ext.trans ext', hr⟩

end

end IxVM.Refinement.Binding.FamilyRecon
