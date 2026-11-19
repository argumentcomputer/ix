import IxVMRefinement.Binding.FamilyReconSubst
import IxVMRefinement.Levels.Spec
import IxVMRefinement.Nat.Levels
import IxVMRefinement.Nat.Basic
import IxVMRefinement.Nat.Utf8
import IxVMRefinement.Lib.Bytes
import IxVMRefinement.Obs.KernelCheck3
import IxVMRefinement.Obs.KernelCheck13
import IxVMRefinement.Obs.KernelCheck14

/-! # Zeta-transparent heads, telescopes, spines, and exact structural equality

This module refines the zeta-transparent helpers of `KernelCheck` directly on `TmOExact` (without
`CoreGood` or any no-let premise):

* `TmOExact.*_of_load`: node inversion lemmas for `TmOExact`.
* `NotLet`: a heap pointer whose cell is not a `KExprNode::Let`.
* `zeta_head_spec`: `KernelCheck::zeta_head` preserves `TmOExact` and yields `NotLet`.
* `peel_n_foralls_zeta_spec`: `KernelCheck::peel_n_foralls_zeta` computes `peelForalls` exactly,
  stepping through any intervening `Let` cells.
* `collect_spine_zeta_spec`: `KernelCheck::collect_spine_zeta` computes `(E.getAppFn, E.getAppArgs)`
  exactly, with a `NotLet` head.
* Standalone bidirectional equality specs (`pw_eq_exact`, `klimbs_eq_exact`, `bytestream_eq_exact`,
  `literal_eq_exact`, `level_list_struct_eq_exact`) and exact syntactic equality
  `kexpr_zeta_struct_eq_exact` and `spec_params_zeta_eq_exact` when `Function.Injective κ`. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum klitEnum kexprListEnum
  limbListEnum byteListEnum addrTy ixAddr limbsVal StrBytes)
open IxVM.Refinement.Core.LevelsAux
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList glistCmp_refines)
open IxVM.Refinement.Decl (TmExact TmCExact)
open IxVM.Refinement.Binding.FamilyFlat (peelForalls)
open Ix.Kernel (Expr PropWhen)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Arithmetic & address helpers -/

theorem ixAddr_inj : Function.Injective ixAddr := by
  intro a b h
  cases a with
  | mk arr1 h1 =>
    cases b with
    | mk arr2 h2 =>
      have harr : arr1 = arr2 := congrArg ByteArray.data (congrArg Address.hash h)
      subst harr
      rfl

theorem evalBinOp_sub_succ (n : Nat) {v : SourceValue F}
    (op : evalBinOp .sub (.field ((n + 1 : Nat) : F)) (.field (1 : F)) = .ok v) :
    v = .field (n : F) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  congr 1
  push_cast
  ring

theorem succ_field_ne_zero (n : Nat) (hn : n < 18446744069414584320) :
    (.field ((n + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
  intro h
  injection h with h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega : n + 1 < 18446744069414584321), ZMod.val_zero] at hv
  omega

theorem evalBinOp_sub_field {a b : F} {v : SourceValue F}
    (op : evalBinOp .sub (.field a) (.field b) = .ok v) : v = .field (a - b) := by
  simp only [evalBinOp] at op
  injection op with hv
  exact hv.symm

/-! ## `TmOExact` node inversion helpers -/

theorem TmOExact.bvar_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xi : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "BVar" [xi])) :
    ∃ i : F, xi = .field i ∧ ZMod.val i < 9223372036854775808 ∧ E = .bvar (ZMod.val i) := by
  obtain ⟨k, rep⟩ := hp
  obtain ⟨i, rfl, hsm, hcase⟩ := rep.bvar_of_load ld
  rcases hcase with ⟨_, rfl⟩ | ⟨_, hd, _⟩
  · exact ⟨i, rfl, hsm, rfl⟩
  · omega

theorem TmOExact.sort_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xl : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Srt" [xl])) :
    ∃ l : KLevel, E = .sort l ∧ RepKLevel h l xl := by
  obtain ⟨k, rep⟩ := hp
  exact rep.sort_of_load ld

theorem TmOExact.const_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xa xls : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Const" [xa, xls])) :
    ∃ (a : Bytes.Address) (ls : List KLevel),
      E = .const (κ (ixAddr a)) ls ∧ Bytes.RepAddressRef addrTy h a xa ∧ RepKLevelList h ls xls := by
  obtain ⟨k, rep⟩ := hp
  exact rep.const_of_load ld

theorem TmOExact.app_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xf xa : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "App" [xf, xa])) :
    ∃ Ef Ea, E = .app Ef Ea ∧ TmOExact κ h Ef xf ∧ TmOExact κ h Ea xa := by
  obtain ⟨k, rep⟩ := hp
  obtain ⟨Ef, Ea, rfl, hf, ha⟩ := rep.app_of_load ld
  exact ⟨Ef, Ea, rfl, ⟨k, hf⟩, ⟨k, ha⟩⟩

theorem TmOExact.lam_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xt xb xl : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lam" [xt, xb, xl])) :
    ∃ T B ℓ, E = .lam T B (bmeta ℓ) ∧ TmOExact κ h T xt ∧ TmOExact κ h B xb ∧
      RepKLevel h ℓ xl := by
  obtain ⟨k, rep⟩ := hp
  obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := rep.lam_of_load ld
  exact ⟨T, B, ℓ, rfl, ⟨k, ht⟩, ⟨k + 1, hb⟩, hl⟩

theorem TmOExact.forallE_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xt xb xl : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [xt, xb, xl])) :
    ∃ T B ℓ, E = .forallE T B (bmeta ℓ) ∧ TmOExact κ h T xt ∧ TmOExact κ h B xb ∧
      RepKLevel h ℓ xl := by
  obtain ⟨k, rep⟩ := hp
  obtain ⟨T, B, ℓ, rfl, ht, hb, hl⟩ := rep.forallE_of_load ld
  exact ⟨T, B, ℓ, rfl, ⟨k, ht⟩, ⟨k + 1, hb⟩, hl⟩

theorem TmOExact.letE_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xt xv xb : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Let" [xt, xv, xb])) :
    ∃ T V B, E = B.instantiate1Lift V 0 ∧ TmOExact κ h T xt ∧ TmOExact κ h V xv ∧
      TmOExact κ h B xb := by
  obtain ⟨k, rep⟩ := hp
  obtain ⟨T, V, B, rfl, ht, hv, hb⟩ := rep.letE_of_load ld
  exact ⟨T, V, B, rfl, ⟨k, ht⟩, ⟨k, hv⟩, ⟨k + 1, hb⟩⟩

theorem TmOExact.proj_of_load {κ : _root_.Address → KKey} {h : Heap F} {E : KExpr}
    {p xa xi xe : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Proj" [xa, xi, xe])) :
    ∃ (a : Bytes.Address) (i : F) (Es : KExpr),
      xi = .field i ∧ E = .proj (κ (ixAddr a)) (ZMod.val i) Es ∧
      Bytes.RepAddressRef addrTy h a xa ∧ TmOExact κ h Es xe := by
  obtain ⟨k, rep⟩ := hp
  obtain ⟨a, i, Es, rfl, rfl, ra, he⟩ := rep.proj_of_load ld
  exact ⟨a, i, Es, rfl, rfl, ra, ⟨k, he⟩⟩

/-! ## `NotLet` predicate and `TmOExact` inversion on `NotLet` cells -/

/-- A heap pointer whose loaded node is not `KExprNode::Let`. -/
def NotLet (h : Heap F) (p : SourceValue F) : Prop :=
  ∃ v, loadValue h p = .ok v ∧
    ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs

theorem NotLet.mono {h h' : Heap F} {p : SourceValue F}
    (ext : Heap.Extends h h') (hn : NotLet h p) : NotLet h' p := by
  obtain ⟨v, ld, hne⟩ := hn
  exact ⟨v, loadValue_heapMono₂ ext ld, hne⟩

theorem notLet_of_cell {h : Heap F} {addr : Nat} {tag : String} {args : List (SourceValue F)}
    (cell : h[addr]? = some (.construct kexprEnum tag args)) (ht : tag ≠ "Let") :
    NotLet h (.ptr (.enum kexprEnum) addr) := by
  refine ⟨.construct kexprEnum tag args, Lib.load_enum_cell cell, fun vs _ heq => ?_⟩
  injection heq with _ hc _
  exact ht hc

theorem NotLet.ne_let {h : Heap F} {p t v b : SourceValue F} (hn : NotLet h p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Let" [t, v, b])) : False := by
  obtain ⟨val, ld0, hne⟩ := hn
  rw [ld] at ld0
  injection ld0 with hval
  exact hne [t, v, b] rfl hval.symm

/-- On a `NotLet` cell, a non-`App` node cannot represent `.app _ _`. -/
theorem not_app_of_notLet {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F}
    (hp : TmOExact κ h E p) (ld : loadValue h p = .ok v)
    (hneApp : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "App" vs)
    (hneLet : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Let" vs) :
    E.getAppFn = E ∧ E.getAppArgs = [] := by
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | bvarLocal .. => exact ⟨rfl, rfl⟩
  | bvarFree _ _ _ hd => omega
  | sort .. => exact ⟨rfl, rfl⟩
  | const .. => exact ⟨rfl, rfl⟩
  | app cell _ _ =>
    have hld := Lib.load_enum_cell cell
    rw [ld] at hld
    injection hld with hv
    exact (hneApp _ rfl hv).elim
  | lam .. => exact ⟨rfl, rfl⟩
  | forallE .. => exact ⟨rfl, rfl⟩
  | letE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell
    rw [ld] at hld
    injection hld with hv
    exact (hneLet _ rfl hv).elim
  | litNat .. => exact ⟨rfl, rfl⟩
  | litStr .. => exact ⟨rfl, rfl⟩
  | proj .. => exact ⟨rfl, rfl⟩

/-! ## `zeta_head`, `peel_n_foralls_zeta`, `collect_spine_zeta` -/

/-- **`KernelCheck::zeta_head`** reduces leading `Let` nodes to a `NotLet` pointer representing the
exact same `KExpr`. -/
theorem zeta_head_spec {κ : _root_.Address → KKey} {h h' : Heap F}
    {E : KExpr} {p r : SourceValue F} {cs : List (Call F)}
    (hp : TmOExact κ h E p) (bd : IxVM.Consistency.Bounded cs)
    (ev : ObsFn W "KernelCheck::zeta_head" [p] h r h' cs) :
    TmOExact κ h' E r ∧ NotLet h' r := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono bd hs
  match Obs.«KernelCheck::zeta_head».obs ev with
  | .Let (x_v := xv) (x_b := xb) (v_qpqrsosc := v') (m_fhppzpwh := m') (cs_yqrxeseo := cs1)
      (cs_oidztzzr := cs2) (ld_bolbylmd := ld) (ev_gemvpjgn := e1) (ev_gdcezqsl := e2)
      (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hp ld
    have hv' : TmOExact κ m' (B.instantiate1Lift V 0) v' :=
      expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact zeta_head_spec hv' (sub fun c hc' => by rw [hc]; simp [hc']) e2
  | .other (v_hirlhoca := v) (ld_bolbylmd := ld) (hne_ttotnwna := hne)
      (he_bjyieayr := hr) (he_ksmcubva := hh) .. =>
    subst hr hh
    exact ⟨hp, v, ld, hne⟩
termination_by cs.length

/-- **`KernelCheck::peel_n_foralls_zeta`** peels `n` leading `Forall` binders through any
intervening `Let` nodes, matching `peelForalls n E` exactly. -/
theorem peel_n_foralls_zeta_spec {κ : _root_.Address → KKey} :
    ∀ (n : Nat) {h h' : Heap F} {E : KExpr} {p r : SourceValue F} {cs : List (Call F)},
      n < 18446744069414584321 → TmOExact κ h E p → IxVM.Consistency.Bounded cs →
      ObsFn W "KernelCheck::peel_n_foralls_zeta" [p, .field (n : F)] h r h' cs →
      ∃ B, peelForalls n E = some B ∧ TmOExact κ h' B r := by
  intro n h h' E p r cs hn hp bd ev
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono bd hs
  cases n with
  | zero =>
    match Obs.«KernelCheck::peel_n_foralls_zeta».obs ev with
    | .n0 (he_whiproaa := hr) (he_bzwoglyf := hh) .. =>
      subst hr hh
      exact ⟨E, rfl, hp⟩
    | .other_Forall (hne_xjnibfzs := hne) .. | .other_Let (hne_xjnibfzs := hne) .. =>
      exact (hne (by simp)).elim
  | succ n =>
    match Obs.«KernelCheck::peel_n_foralls_zeta».obs ev with
    | .n0 (hv_fdljvuxp := hv) .. =>
      exact (succ_field_ne_zero n (by omega) hv).elim
    | .other_Forall (x_body := xb) (v_fpjmyxdi := vn) (cs_eadgpktx := cs1)
        (ld_hdultwxn := ld) (op_czjgbwao := op) (ev_imkwftmt := e1) (hc_ydqmxojp := hc) .. =>
      obtain ⟨D, B, ℓ, rfl, -, hb, -⟩ := TmOExact.forallE_of_load hp ld
      have hvn := evalBinOp_sub_succ n op
      subst hvn
      have hlt : cs1.length < cs.length := by rw [hc]; simp
      exact peel_n_foralls_zeta_spec n (by omega) hb
        (sub fun c hc' => by rw [hc]; simp [hc']) e1
    | .other_Let (x_v := xv) (x_b := xb) (v_qsxgsldq := v') (m_vopdadin := m')
        (cs_cuwzkjio := cs1) (cs_webebuuu := cs2) (ld_hdultwxn := ld)
        (ev_mtsqvowg := e1) (ev_vgbqehni := e2) (hc_thparjte := hc) .. =>
      obtain ⟨T, V, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hp ld
      have hv' : TmOExact κ m' (B.instantiate1Lift V 0) v' :=
        expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
      have hlt : cs2.length < cs.length := by
        rw [hc]; simp only [List.length_cons, List.length_append]; omega
      exact peel_n_foralls_zeta_spec (n + 1) hn hv'
        (sub fun c hc' => by rw [hc]; simp [hc']) e2
termination_by _ _ _ _ _ _ cs => cs.length

private theorem kexprList_names :
    kexprListEnum = (Instance.mk "Lists::Node" [.ref (.enum kexprEnum)]).symbol := by
  decide

private theorem kexprSnoc_names :
    Obs.Names.«Lists::snoc<&KernelTypes::KExprNode>» =
      (Instance.mk "Lists::snoc" [.ref (.enum kexprEnum)]).symbol := by
  decide

/-- **`KernelCheck::collect_spine_zeta`** splits an expression into `(E.getAppFn, E.getAppArgs)`
through any intervening `Let` nodes, leaving a `NotLet` head. -/
theorem collect_spine_zeta_spec {κ : _root_.Address → KKey} {h h' : Heap F}
    {E : KExpr} {p hd args : SourceValue F} {cs : List (Call F)}
    (hp : TmOExact κ h E p) (bd : IxVM.Consistency.Bounded cs)
    (ev : ObsFn W "KernelCheck::collect_spine_zeta" [p] h (.tuple [hd, args]) h' cs) :
    TmOExact κ h' E.getAppFn hd ∧ NotLet h' hd ∧
      RepList kexprListEnum (TmOExact κ) h' E.getAppArgs args := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono bd hs
  match Obs.«KernelCheck::collect_spine_zeta».obs ev with
  | .App (x_f := xf) (x_a := xa) (m_jqajpums := m1) (cs_vfqnrvid := cs1)
      (x_head := xhd) (x_args := xargs) (v_artqopmv := vsnoc) (m_ivjtjdtv := m2)
      (cs_ylwmksdk := cs2) (ld_bolbylmd := ld) (ev_gsaollmr := e1) (he_elcfuhxw := hres)
      (ev_atvhnvai := e2) (he_yhlvgkyp := hh) (hc_xkhdrnsx := hc) .. =>
    injection hres with hpair
    injection hpair with hhd hpair2
    injection hpair2 with hargs
    subst hhd hargs hh
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := TmOExact.app_of_load hp ld
    have hlt : cs1.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨hfn, hnl, hlist⟩ := collect_spine_zeta_spec hf
      (sub fun c hc' => by rw [hc]; simp [hc']) e1
    have hlist' : RepList (Instance.mk "Lists::Node" [.ref (.enum kexprEnum)]).symbol
        (TmOExact κ) m1 Ef.getAppArgs xargs := by
      rwa [← kexprList_names]
    rw [kexprSnoc_names] at e2
    have hsnoc := Lib.Lists.snoc_spec (tmOExact_heapMono₂ (κ := κ)) e2 hlist'
      (ha.mono e1.heap_extends)
    rw [← kexprList_names] at hsnoc
    have hgetFn : (Expr.app Ef Ea).getAppFn = Ef.getAppFn := rfl
    have hgetArgs : (Expr.app Ef Ea).getAppArgs = Ef.getAppArgs ++ [Ea] := rfl
    rw [hgetFn, hgetArgs]
    exact ⟨hfn.mono e2.heap_extends, hnl.mono e2.heap_extends, hsnoc⟩
  | .Let (x_v := xv) (x_b := xb) (v_boczwtnf := v') (m_fhppzpwh := m')
      (cs_yqrxeseo := cs1) (cs_vizhzyfr := cs2) (ld_bolbylmd := ld)
      (ev_gemvpjgn := e1) (ev_tmtbszvp := e2) (hc_qubwlzze := hc) .. =>
    obtain ⟨T, V, B, rfl, -, hv, hb⟩ := TmOExact.letE_of_load hp ld
    have hv' : TmOExact κ m' (B.instantiate1Lift V 0) v' :=
      expr_inst1_tmOExact (sub fun c hc' => by rw [hc]; simp [hc']) hb hv e1
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    exact collect_spine_zeta_spec hv' (sub fun c hc' => by rw [hc]; simp [hc']) e2
  | .other (v_hirlhoca := v) (m_ffdijcfq := m1) (ld_bolbylmd := ld)
      (hne_ebjedqqk := hneApp) (hne_ttotnwna := hneLet) (he_jjavcari := hres)
      (hm_gscsglcu := hm1) (he_yrjjshnd := hh) .. =>
    injection hres with hpair
    injection hpair with hhd hpair2
    injection hpair2 with hargs
    subst hhd hargs hh hm1
    obtain ⟨hfn, hargs⟩ := not_app_of_notLet hp ld hneApp hneLet
    rw [hfn, hargs]
    have ext : Heap.Extends h
        (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) :=
      Heap.Extends.snoc _ _
    have hnil : RepList kexprListEnum (TmOExact κ)
        (h ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) []
        (.ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») h.length) :=
      .nil (by simp)
    exact ⟨hp.mono ext, NotLet.mono ext ⟨v, ld, hneLet⟩, hnil⟩
termination_by cs.length

/-! ## Standalone exact equality specs (binder data, literals, level lists) -/

/-- `KernelLevels::pw_eq` decides `la.zeronessOf = lb.zeronessOf` without `CoreGood`. -/
theorem pw_eq_exact {h h' : Heap F} {la lb : KLevel} {pa pb r : SourceValue F}
    {cs : List (Call F)}
    (ha : RepKLevel h la pa) (hb : RepKLevel h lb pb)
    (ev : ObsFn W "KernelLevels::pw_eq" [pa, pb] h r h' cs) :
    r = .field (if la.zeronessOf = lb.zeronessOf then 1 else 0) := by
  rw [zeronessOf_eq la, zeronessOf_eq lb]
  rcases Obs.«KernelLevels::pw_eq».obs ev with
    ⟨m2, cs12, x_sa, m37, cs47, x_nb, x_sb, ev14, ev49, op87, he108, he109, hc110⟩ |
    ⟨m2, cs12, x_na, x_sa, m37, cs47, x_nb, x_sb, cs118, v121, m123, cs131, ev14, ev49, op87,
      hne111, ev133, ev120, hc150⟩ |
    ⟨m2, cs12, x_na, x_sa, m37, cs47, x_nb, x_sb, v71, ev14, ev49, op87, hne151, he155, he156,
      hc157⟩
  · obtain ⟨spa, hra, -⟩ := zero_set_spec ha ev14
    obtain ⟨spb, hrb, -⟩ := zero_set_spec (hb.mono (ObsFn.heap_extends ev14)) ev49
    have fa : (zeroSet la).1 = true := flag_eq_one (pair_inj hra).1.symm
    obtain ⟨rfl, -⟩ := pair_inj hrb
    have fb : (zeroSet lb).1 = true := ((flag_sub_inv (a := true) op87).mp rfl).symm
    rw [he108, toPW_never fa, toPW_never fb, ite_eq_left rfl]
  · have e14 := ObsFn.heap_extends ev14
    have e49 := ObsFn.heap_extends ev49
    obtain ⟨spa, hra, hsa⟩ := zero_set_spec ha ev14
    obtain ⟨spb, hrb, hsb⟩ := zero_set_spec (hb.mono e14) ev49
    obtain ⟨rfl, rfl⟩ := pair_inj hra
    obtain ⟨rfl, rfl⟩ := pair_inj hrb
    have fa : (zeroSet la).1 = false := flag_ne_one hne111
    have fb : (zeroSet lb).1 = false := by
      rw [← fa]
      exact ((flag_sub_inv op87).mp rfl).symm
    obtain ⟨hv, rfl⟩ := glistCmp_refines (repGL_mono hsa e49) hsb ev133.erase
    subst hv
    obtain ⟨hr, -⟩ := Lib.is_zero_field ev120
    have hpw := ifAllZero_eq_iff_eq (zeroSet_pairwise la) (zeroSet_pairwise lb)
    rw [hr, toPW_ifAllZero fa, toPW_ifAllZero fb]
    by_cases hab : (zeroSet la).2 = (zeroSet lb).2
    · rw [ite_eq_left ((glistCmp_cast_eq_zero_iff _ _).mpr hab), ite_eq_left (hpw.mpr hab)]
    · rw [ite_eq_right (fun e => hab ((glistCmp_cast_eq_zero_iff _ _).mp e)),
        ite_eq_right (fun e => hab (hpw.mp e))]
  · obtain ⟨spa, hra, -⟩ := zero_set_spec ha ev14
    obtain ⟨spb, hrb, -⟩ := zero_set_spec (hb.mono (ObsFn.heap_extends ev14)) ev49
    obtain ⟨rfl, -⟩ := pair_inj hra
    obtain ⟨rfl, -⟩ := pair_inj hrb
    have hne : (zeroSet la).1 ≠ (zeroSet lb).1 := fun e => hne151 ((flag_sub_inv op87).mpr e)
    rw [he155]
    cases fa : (zeroSet la).1 <;> cases fb : (zeroSet lb).1
    · exact absurd (fa.trans fb.symm) hne
    · rw [toPW_ifAllZero fa, toPW_never fb, ite_eq_right (PropWhen.ifAllZero_ne_never _)]
    · rw [toPW_never fa, toPW_ifAllZero fb, ite_eq_right (Ne.symm (PropWhen.ifAllZero_ne_never _))]
    · exact absurd (fa.trans fb.symm) hne

theorem bmeta_eq_iff {la lb : KLevel} : bmeta la = bmeta lb ↔ la.zeronessOf = lb.zeronessOf := by
  constructor
  · intro h; exact congrArg Ix.Kernel.BinderMeta.pw h
  · intro h; unfold bmeta; rw [h]

theorem klimbs_eq_exact {h h' : Heap F} {la lb : List UInt64} {pa pb r : SourceValue F}
    {cs : List (Call F)}
    (ha : RepList limbListEnum RepU64 h la pa) (hb : RepList limbListEnum RepU64 h lb pb)
    (ev : ObsFn W "KernelLevels::klimbs_eq" [pa, pb] h r h' cs) :
    r = .field (if la = lb then 1 else 0) ∧ h' = h := by
  rcases Obs.«KernelLevels::klimbs_eq».obs ev with
    ⟨ld12, ld31, he39, he40, hc41⟩ |
    ⟨v20, ld12, ld31, hne42, he46, he47, hc48⟩ |
    ⟨x_la, x_ra, ld12, ld77, he85, he86, hc87⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, m106, cs116, cs152, ld12, ld77, ev118, ev154, hc171⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, m106, cs116, ld12, ld77, ev118, he177, he178, hc179⟩
  · obtain rfl := Core.RepList.nil_of_load ha ld12
    obtain rfl := Core.RepList.nil_of_load hb ld31
    exact ⟨by rw [he39, ite_eq_left rfl], he40⟩
  · obtain rfl := Core.RepList.nil_of_load ha ld12
    refine ⟨?_, he47⟩
    rw [he46]
    cases lb with
    | nil =>
      have hl := load_nil hb
      rw [ld31] at hl
      injection hl with hv
      exact absurd hv (hne42 [] rfl)
    | cons _ _ => simp
  · obtain ⟨x, xs, rfl, -, -⟩ := Core.RepList.cons_of_load ha ld12
    obtain rfl := Core.RepList.nil_of_load hb ld77
    exact ⟨by rw [he85]; simp, he86⟩
  · obtain ⟨x, xs, rfl, hx, hxs⟩ := Core.RepList.cons_of_load ha ld12
    obtain ⟨y, ys, rfl, hy, hys⟩ := Core.RepList.cons_of_load hb ld77
    obtain ⟨heq, rfl⟩ := Lib.u64_eq_spec hx hy ev118
    have hxy : x = y := by
      by_contra hne
      rw [ite_eq_right (fun e => hne (UInt64.toNat_inj.mp e))] at heq
      exact one_ne_zero (Value.field.inj heq)
    subst hxy
    have hlt : cs152.length < cs.length := by
      rw [hc171]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨hr, hh⟩ := klimbs_eq_exact hxs hys ev154
    exact ⟨by rw [hr]; simp, hh⟩
  · obtain ⟨x, xs, rfl, hx, -⟩ := Core.RepList.cons_of_load ha ld12
    obtain ⟨y, ys, rfl, hy, -⟩ := Core.RepList.cons_of_load hb ld77
    obtain ⟨heq, rfl⟩ := Lib.u64_eq_spec hx hy ev118
    have hxy : x ≠ y := by
      intro e; subst e
      rw [ite_eq_left rfl] at heq
      exact zero_ne_one (Value.field.inj heq)
    exact ⟨by rw [he177, ite_eq_right (fun e => hxy (List.cons.inj e).1)], he178⟩
termination_by cs.length

theorem bytestream_eq_exact {h h' : Heap F} {xs ys : List UInt8} {pa pb r : SourceValue F}
    {cs : List (Call F)}
    (ha : Bytes.RepByteStream byteListEnum h xs pa)
    (hb : Bytes.RepByteStream byteListEnum h ys pb)
    (ev : ObsFn W "KernelLevels::bytestream_eq" [pa, pb] h r h' cs) :
    r = .field (if xs = ys then 1 else 0) ∧ h' = h := by
  rcases Obs.«KernelLevels::bytestream_eq».obs ev with
    ⟨ld12, ld31, he39, he40, hc41⟩ |
    ⟨v20, ld12, ld31, hne42, he46, he47, hc48⟩ |
    ⟨x_ba, x_ra, ld12, ld77, he85, he86, hc87⟩ |
    ⟨x_ba, x_ra, x_bb, x_rb, m106, x114, y115, m116, cs125, cs139, cs157, ld12, ld77, ev127,
      ev141, op121, ev159, hc176⟩ |
    ⟨x_ba, x_ra, x_bb, x_rb, v105, m106, x114, y115, m116, cs125, cs139, ld12, ld77, ev127, ev141,
      op121, hne177, he181, he182, hc183⟩
  · obtain rfl := Core.RepList.nil_of_load ha ld12
    obtain rfl := Core.RepList.nil_of_load hb ld31
    exact ⟨by rw [he39, ite_eq_left rfl], he40⟩
  · obtain rfl := Core.RepList.nil_of_load ha ld12
    refine ⟨?_, he47⟩
    rw [he46]
    cases ys with
    | nil =>
      have hl := load_nil hb
      rw [ld31] at hl
      injection hl with hv
      exact absurd hv (hne42 [] rfl)
    | cons _ _ => simp
  · obtain ⟨x, xs', rfl, -, -⟩ := Core.RepList.cons_of_load ha ld12
    obtain rfl := Core.RepList.nil_of_load hb ld77
    exact ⟨by rw [he85]; simp, he86⟩
  · obtain ⟨x, xs', rfl, hx, hxs⟩ := Core.RepList.cons_of_load ha ld12
    obtain ⟨y, ys', rfl, hy, hys⟩ := Core.RepList.cons_of_load hb ld77
    obtain ⟨e1, rfl⟩ := Lib.u8_to_field_spec ev127
    obtain ⟨e2, rfl⟩ := Lib.u8_to_field_spec ev141
    have hx' : x114 = .field (x.toNat : F) := e1.trans hx
    have hy' : y115 = .field (y.toNat : F) := e2.trans hy
    rw [hx', hy'] at op121
    have hxy : x = y := (byte_sub_inv op121).mp rfl
    subst hxy
    have hlt : cs157.length < cs.length := by
      rw [hc176]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨hr, hh⟩ := bytestream_eq_exact hxs hys ev159
    exact ⟨by rw [hr]; simp, hh⟩
  · obtain ⟨x, xs', rfl, hx, -⟩ := Core.RepList.cons_of_load ha ld12
    obtain ⟨y, ys', rfl, hy, -⟩ := Core.RepList.cons_of_load hb ld77
    obtain ⟨e1, rfl⟩ := Lib.u8_to_field_spec ev127
    obtain ⟨e2, rfl⟩ := Lib.u8_to_field_spec ev141
    have hx' : x114 = .field (x.toNat : F) := e1.trans hx
    have hy' : y115 = .field (y.toNat : F) := e2.trans hy
    rw [hx', hy'] at op121
    have hxy : x ≠ y := fun e => hne177 ((byte_sub_inv op121).mpr e)
    exact ⟨by rw [he181, ite_eq_right (fun e => hxy (List.cons.inj e).1)], he182⟩
termination_by cs.length

theorem strBytes_eq_iff {s₁ s₂ : String} {b₁ b₂ : List UInt8}
    (h₁ : StrBytes s₁ b₁) (h₂ : StrBytes s₂ b₂) : s₁ = s₂ ↔ b₁ = b₂ := by
  constructor
  · intro hs
    subst hs
    obtain ⟨c₁, hc₁⟩ := IxVM.Refinement.Core.Utf8Aux.exists_strBytes_iff.mp ⟨s₁, h₁⟩
    obtain ⟨c₂, hc₂⟩ := IxVM.Refinement.Core.Utf8Aux.exists_strBytes_iff.mp ⟨s₁, h₂⟩
    have hs₁ := IxVM.Refinement.Core.Utf8Aux.strBytes_eq_ofList h₁ hc₁
    have hs₂ := IxVM.Refinement.Core.Utf8Aux.strBytes_eq_ofList h₂ hc₂
    have hc : c₁ = c₂ := by
      have hof : String.ofList c₁ = String.ofList c₂ := hs₁.symm.trans hs₂
      have := congrArg String.toList hof
      simpa only [String.toList_ofList] using this
    rw [← hc₁, ← hc₂, hc]
  · intro hb
    subst hb
    exact Option.some.inj (h₁.symm.trans h₂)

theorem literal_eq_exact {h h' : Heap F} {la lb : IxVM.Refinement.Core.Specs.Levels.LitData}
    {pa pb r : SourceValue F} {cs : List (Call F)}
    (ha : IxVM.Refinement.Core.Specs.Levels.LitRep h la pa)
    (hb : IxVM.Refinement.Core.Specs.Levels.LitRep h lb pb)
    (ev : ObsFn W "KernelLevels::literal_eq" [pa, pb] h r h' cs) :
    r = .field (if la = lb then 1 else 0) ∧ h' = h := by
  rcases Obs.«KernelLevels::literal_eq».obs ev with
    ⟨x_na, x_nb, cs46, hv15, hv36, ev48, hc65⟩ |
    ⟨x_na, hv15, hne66, he70, he71, hc72⟩ |
    ⟨x_sa, x_sb, cs109, hne73, hv78, hv99, ev111, hc128⟩ |
    ⟨x_sa, hne73, hv78, hne129, he133, he134, hc135⟩
  · subst hv15 hv36
    obtain ⟨la', rfl, hla⟩ := lit_nat_inv ha
    obtain ⟨lb', rfl, hlb⟩ := lit_nat_inv hb
    obtain ⟨hr, hh⟩ := klimbs_eq_exact hla hlb ev48
    exact ⟨by rw [hr]; simp, hh⟩
  · subst hv15
    obtain ⟨la', rfl, -⟩ := lit_nat_inv ha
    refine ⟨?_, he71⟩
    rw [he70]
    cases lb with
    | nat lb' =>
      obtain ⟨lp, hlp, -⟩ := hb
      exact absurd hlp (hne66 [lp] rfl)
    | str _ => simp
  · subst hv78 hv99
    obtain ⟨la', rfl, hla⟩ := lit_str_inv ha
    obtain ⟨lb', rfl, hlb⟩ := lit_str_inv hb
    obtain ⟨hr, hh⟩ := bytestream_eq_exact hla hlb ev111
    exact ⟨by rw [hr]; simp, hh⟩
  · subst hv78
    obtain ⟨la', rfl, -⟩ := lit_str_inv ha
    refine ⟨?_, he134⟩
    rw [he133]
    cases lb with
    | str lb' =>
      obtain ⟨bp, hbp, -⟩ := hb
      exact absurd hbp (hne129 [bp] rfl)
    | nat _ => simp

theorem level_list_struct_eq_exact {h h' : Heap F} {la lb : List KLevel}
    {pa pb r : SourceValue F} {cs : List (Call F)}
    (ha : RepKLevelList h la pa) (hb : RepKLevelList h lb pb)
    (ev : ObsFn W "KernelCheck::level_list_struct_eq" [pa, pb] h r h' cs) :
    r = .field (if la = lb then 1 else 0) ∧ h' = h := by
  match Obs.«KernelCheck::level_list_struct_eq».obs ev with
  | .Nil_Nil (ld12 := ld1) (ld31 := ld2) (he39 := hr) (he40 := hh) .. =>
    rw [← IxVM.Refinement.Levels.klevelList_names] at ld1 ld2
    obtain rfl := Lib.rep_nil_of_load ha ld1
    obtain rfl := Lib.rep_nil_of_load hb ld2
    exact ⟨by rw [hr, ite_eq_left rfl], hh⟩
  | .Nil_other (v20 := v) (ld12 := ld1) (ld31 := ld2) (hne42 := hne) (he46 := hr)
      (he47 := hh) .. =>
    rw [← IxVM.Refinement.Levels.klevelList_names] at ld1
    obtain rfl := Lib.rep_nil_of_load ha ld1
    refine ⟨?_, hh⟩
    rw [hr]
    cases lb with
    | nil =>
      cases hb with
      | nil cell =>
        have hld := Lib.load_enum_cell cell
        rw [← IxVM.Refinement.Levels.klevelList_names] at hld
        rw [ld2] at hld
        injection hld with hv
        rw [IxVM.Refinement.Levels.klevelList_names] at hv
        exact absurd hv (hne [] rfl)
    | cons _ _ => simp
  | .Cons_Nil (ld12 := ld1) (ld77 := ld2) (he85 := hr) (he86 := hh) .. =>
    rw [← IxVM.Refinement.Levels.klevelList_names] at ld1 ld2
    obtain ⟨_, _, rfl, -, -⟩ := Lib.rep_cons_of_load ha ld1
    obtain rfl := Lib.rep_nil_of_load hb ld2
    exact ⟨by rw [hr]; simp, hh⟩
  | .Cons_Cons_n1 (x_x := xx) (x_xr := xxr) (x_y := xy) (x_yr := xyr) (m106 := m1)
      (cs117 := cs1) (cs143 := cs2) (ld12 := ld1) (ld77 := ld2) (ev119 := e1)
      (ev145 := e2) (hc162 := hc) .. =>
    rw [← IxVM.Refinement.Levels.klevelList_names] at ld1 ld2
    obtain ⟨x, xs, rfl, hx, hxs⟩ := Lib.rep_cons_of_load ha ld1
    obtain ⟨y, ys, rfl, hy, hys⟩ := Lib.rep_cons_of_load hb ld2
    obtain ⟨heq, rfl⟩ := IxVM.Refinement.Levels.levelStructEq_step e1 xx xy rfl x y hx hy
    have hxy : x = y := by
      by_cases hbeq : (x == y) = true
      · exact eq_of_beq hbeq
      · rw [Bool.not_eq_true] at hbeq
        rw [hbeq] at heq
        exact absurd (Value.field.inj heq) (by decide)
    subst hxy
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    obtain ⟨hr, hh⟩ := level_list_struct_eq_exact hxs hys e2
    exact ⟨by rw [hr]; simp, hh⟩
  | .Cons_Cons_other (x_x := xx) (x_xr := xxr) (x_y := xy) (x_yr := xyr) (v105 := v)
      (m106 := m1) (cs117 := cs1) (ld12 := ld1) (ld77 := ld2) (ev119 := e1)
      (hne163 := hne) (he167 := hr) (he168 := hh) .. =>
    rw [← IxVM.Refinement.Levels.klevelList_names] at ld1 ld2
    obtain ⟨x, xs, rfl, hx, -⟩ := Lib.rep_cons_of_load ha ld1
    obtain ⟨y, ys, rfl, hy, -⟩ := Lib.rep_cons_of_load hb ld2
    obtain ⟨heq, rfl⟩ := IxVM.Refinement.Levels.levelStructEq_step e1 xx xy rfl x y hx hy
    have hxy : x ≠ y := by
      intro h; subst h
      rw [beq_self_eq_true] at heq
      exact hne heq
    exact ⟨by rw [hr, ite_eq_right (fun e => hxy (List.cons.inj e).1)], hh⟩
termination_by cs.length

/-! ## Exact bidirectional structural equality (`kexpr_zeta_struct_eq`, `spec_params_zeta_eq`) -/

private theorem tmOExact_not_bvar {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 1 → v ≠ .construct kexprEnum "BVar" vs) :
    ∀ i, E ≠ .bvar i := by
  intro i hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | bvarLocal cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | bvarFree _ _ _ hd => omega
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | _ => cases hE

private theorem tmOExact_not_sort {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 1 → v ≠ .construct kexprEnum "Srt" vs) :
    ∀ l, E ≠ .sort l := by
  intro l hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | sort cell _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | bvarFree _ _ _ hd => omega
  | _ => cases hE

private theorem tmOExact_not_const {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "Const" vs) :
    ∀ c ls, E ≠ .const c ls := by
  intro c ls hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | const cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | bvarFree _ _ _ hd => omega
  | _ => cases hE

private theorem tmOExact_not_app {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct kexprEnum "App" vs) :
    ∀ f a, E ≠ .app f a := by
  intro f a hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | app cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | bvarFree _ _ _ hd => omega
  | _ => cases hE

private theorem tmOExact_not_lam {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Lam" vs) :
    ∀ t b m, E ≠ .lam t b m := by
  intro t b m hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | lam cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | bvarFree _ _ _ hd => omega
  | _ => cases hE

private theorem tmOExact_not_forall {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs) :
    ∀ t b m, E ≠ .forallE t b m := by
  intro t b m hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | forallE cell _ _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | bvarFree _ _ _ hd => omega
  | _ => cases hE

private theorem tmOExact_not_lit {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 1 → v ≠ .construct kexprEnum "Lit" vs) :
    ∀ l, E ≠ .lit l := by
  intro l hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | litNat cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | litStr cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | bvarFree _ _ _ hd => omega
  | _ => cases hE

private theorem tmOExact_not_proj {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p v : SourceValue F} (hp : TmOExact κ h E p) (hnl : NotLet h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Proj" vs) :
    ∀ s i e, E ≠ .proj s i e := by
  intro s i e hE
  obtain ⟨k, ht⟩ := hp
  cases ht with
  | proj cell _ _ =>
    have hld := Lib.load_enum_cell cell; rw [ld] at hld; injection hld with hv; exact hne _ rfl hv
  | letE cell _ _ _ => exact hnl.ne_let (Lib.load_enum_cell cell)
  | bvarFree _ _ _ hd => omega
  | _ => cases hE

private theorem tmOExact_lit_rep {κ : _root_.Address → KKey} {h : Heap F}
    {E : KExpr} {p xl : SourceValue F} (hp : TmOExact κ h E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Lit" [xl])) :
    ∃ (ldat : IxVM.Refinement.Core.Specs.Levels.LitData),
      IxVM.Refinement.Core.Specs.Levels.LitRep h ldat xl ∧
      ((∃ limbs, ldat = .nat limbs ∧ IxVM.Refinement.Core.NatAux.Canon limbs ∧
          E = .lit (.natVal (limbsVal limbs))) ∨
       (∃ bs s, ldat = .str bs ∧ StrBytes s bs ∧ E = .lit (.strVal s))) := by
  obtain ⟨k, ht⟩ := hp
  rcases ht.toTm.lit_of_load ld with
    ⟨lp, limbs, hxl, rl, hc, rfl⟩ | ⟨bp, bs, s, hxl, rb, hs, rfl⟩
  · exact ⟨.nat limbs, ⟨lp, hxl, rl⟩, .inl ⟨limbs, rfl, hc, rfl⟩⟩
  · exact ⟨.str bs, ⟨bp, hxl, rb⟩, .inr ⟨bs, s, rfl, hs, rfl⟩⟩

private theorem zeta_struct_eq_bundle {κ : _root_.Address → KKey} (hinj : Function.Injective κ) :
    ∀ (fname : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)),
      ObsFn W fname args h r h' cs → IxVM.Consistency.Bounded cs →
      (fname = "KernelCheck::kexpr_zeta_struct_eq" →
        ∀ (p₁ p₂ : SourceValue F) (E₁ E₂ : KExpr),
          args = [p₁, p₂] → TmOExact κ h E₁ p₁ → TmOExact κ h E₂ p₂ →
          r = .field (if E₁ = E₂ then 1 else 0)) ∧
      (fname = "KernelCheck::kexpr_zeta_binder_eq" →
        ∀ (ta ba la tb bb lb : SourceValue F) (Ta Ba Tb Bb : KExpr) (ℓa ℓb : KLevel),
          args = [ta, ba, la, tb, bb, lb] →
          TmOExact κ h Ta ta → TmOExact κ h Ba ba → RepKLevel h ℓa la →
          TmOExact κ h Tb tb → TmOExact κ h Bb bb → RepKLevel h ℓb lb →
          r = .field (if bmeta ℓa = bmeta ℓb ∧ Ta = Tb ∧ Ba = Bb then 1 else 0)) := by
  refine ObsFn.strong_induction (W := W)
    (P := fun fname args h r h' cs => IxVM.Consistency.Bounded cs →
      (fname = "KernelCheck::kexpr_zeta_struct_eq" →
        ∀ (p₁ p₂ : SourceValue F) (E₁ E₂ : KExpr),
          args = [p₁, p₂] → TmOExact κ h E₁ p₁ → TmOExact κ h E₂ p₂ →
          r = .field (if E₁ = E₂ then 1 else 0)) ∧
      (fname = "KernelCheck::kexpr_zeta_binder_eq" →
        ∀ (ta ba la tb bb lb : SourceValue F) (Ta Ba Tb Bb : KExpr) (ℓa ℓb : KLevel),
          args = [ta, ba, la, tb, bb, lb] →
          TmOExact κ h Ta ta → TmOExact κ h Ba ba → RepKLevel h ℓa la →
          TmOExact κ h Tb tb → TmOExact κ h Bb bb → RepKLevel h ℓb lb →
          r = .field (if bmeta ℓa = bmeta ℓb ∧ Ta = Tb ∧ Ba = Bb then 1 else 0)))
    (fun fname args h r h' cs ev ih bd => by
      have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
        fun hs => RomBound.bounded_mono bd hs
      refine ⟨fun hfn p₁ p₂ E₁ E₂ hargs h₁ h₂ => ?_,
        fun hfn ta ba la tb bb lb Ta Ba Tb Bb ℓa ℓb hargs hTa hBa hℓa hTb hBb hℓb => ?_⟩
      · subst hfn hargs
        match Obs.«KernelCheck::kexpr_zeta_struct_eq».obs ev with
        | .BVar_BVar_n0 (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (x_ia := xia) (x_ib := xib)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_plsvaejj := ld2)
            (op_hgewkjyg := op) (he_grokaklj := hr) (hc_emtjylqx := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨ia, rfl, -, rfl⟩ := TmOExact.bvar_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨ib, rfl, -, rfl⟩ := TmOExact.bvar_of_load hvb ld2
          have hsub := evalBinOp_sub_field op
          have heq : ia = ib := sub_eq_zero.mp (Value.field.inj hsub.symm)
          subst heq
          simp
        | .BVar_BVar_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (x_ia := xia) (x_ib := xib)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_plsvaejj := ld2)
            (op_hgewkjyg := op) (hne_xxyahirz := hne) (he_ygkbeupr := hr) (hc_dijhgtbe := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨ia, rfl, -, rfl⟩ := TmOExact.bvar_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨ib, rfl, -, rfl⟩ := TmOExact.bvar_of_load hvb ld2
          have hsub := evalBinOp_sub_field op
          have hne' : ia ≠ ib := fun h => hne (hsub.trans (by rw [h, sub_self]))
          rw [ite_eq_right (fun h => hne' (ZMod.val_injective _ (Expr.bvar.inj h)))]
        | .BVar_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_wfmbpjng := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_plsvaejj := ld2)
            (hne_zgbdqdcb := hne) (he_cxjmouws := hr) (hc_kwsgizgm := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨ia, rfl, -, rfl⟩ := TmOExact.bvar_of_load (hva.mono e2.heap_extends) ld1
          rw [ite_eq_right (fun h => tmOExact_not_bvar hvb hnlb ld2 hne ia.val h.symm)]
        | .Srt_Srt (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_la := xla) (x_lb := xlb) (ev_dkmtahfq := e1) (ev_yasdpozq := e2)
            (ld_bolbylmd := ld1) (ld_upncaagw := ld2) (ev_buayrzlf := e3)
            (hc_hyhzyqgt := hc) .. =>
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨la, rfl, rla⟩ := TmOExact.sort_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨lb, rfl, rlb⟩ := TmOExact.sort_of_load hvb ld2
          obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelStructEq_step e3 xla xlb rfl la lb rla rlb
          rw [hr]
          by_cases h : la = lb
          · subst h; simp
          · have hb : (la == lb) = false := beq_eq_false_iff_ne.mpr h
            rw [hb]; simp [h]
        | .Srt_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_nhziumwg := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_upncaagw := ld2)
            (hne_felpnpwn := hne) (he_krkybuoo := hr) (hc_hziarpzk := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨la, rfl, -⟩ := TmOExact.sort_of_load (hva.mono e2.heap_extends) ld1
          rw [ite_eq_right (fun h => tmOExact_not_sort hvb hnlb ld2 hne la h.symm)]
        | .Const_Const_n1 (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_ca := xca) (x_lsa := xlsa) (x_cb := xcb) (x_lsb := xlsb)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_hkyzglrm := ld2)
            (ev_zfaquxkc := e3) (ev_emmujvhv := e4) (hc_gxzzolpu := hc) .. =>
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨aa, lsa, rfl, raa, rlsa⟩ := TmOExact.const_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨ab, lsb, rfl, rab, rlsb⟩ := TmOExact.const_of_load hvb ld2
          obtain ⟨heq, rfl⟩ := Lib.address_eq_spec e3 raa rab
          have hab : aa = ab := by
            by_contra hne; rw [ite_eq_right hne] at heq
            exact absurd (Value.field.inj heq) (by decide)
          subst hab
          obtain ⟨hr, -⟩ := level_list_struct_eq_exact rlsa rlsb e4
          rw [hr]; simp
        | .Const_Const_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_ca := xca) (x_lsa := xlsa) (x_cb := xcb) (x_lsb := xlsb)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_hkyzglrm := ld2)
            (ev_zfaquxkc := e3) (hne_fsnweywm := hne) (he_cmugkrjm := hr) (hc_iozyrnpo := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨aa, lsa, rfl, raa, -⟩ := TmOExact.const_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨ab, lsb, rfl, rab, -⟩ := TmOExact.const_of_load hvb ld2
          obtain ⟨heq, -⟩ := Lib.address_eq_spec e3 raa rab
          have hab : aa ≠ ab := fun h => by subst h; rw [ite_eq_left rfl] at heq; exact hne heq
          rw [ite_eq_right (fun h => hab (ixAddr_inj (hinj (Expr.const.inj h).1)))]
        | .Const_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_jknrfqpi := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_hkyzglrm := ld2)
            (hne_nkozldxe := hne) (he_dqihycfj := hr) (hc_cnrhqnxp := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨aa, lsa, rfl, -, -⟩ := TmOExact.const_of_load (hva.mono e2.heap_extends) ld1
          rw [ite_eq_right (fun h => tmOExact_not_const hvb hnlb ld2 hne _ _ h.symm)]
        | .App_App_n1 (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_fa := xfa) (x_aa := xaa) (x_fb := xfb) (x_ab := xab)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_jdpbrpwd := ld2)
            (ev_qpbdiktk := e3) (ev_nimuxdlf := e4) (hc_lgectalr := hc) .. =>
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨Ef₁, Ea₁, rfl, hf₁, ha₁⟩ := TmOExact.app_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨Ef₂, Ea₂, rfl, hf₂, ha₂⟩ := TmOExact.app_of_load hvb ld2
          have hfeq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e3
            (sub fun c hc' => by rw [hc]; simp [hc'])).1 rfl xfa xfb Ef₁ Ef₂ rfl hf₁ hf₂
          have hf : Ef₁ = Ef₂ := by
            by_contra hne; rw [ite_eq_right hne] at hfeq
            exact absurd (Value.field.inj hfeq) (by decide)
          subst hf
          have haeq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e4
            (sub fun c hc' => by rw [hc]; simp [hc'])).1 rfl xaa xab Ea₁ Ea₂ rfl
            (ha₁.mono e3.heap_extends) (ha₂.mono e3.heap_extends)
          rw [haeq]; simp
        | .App_App_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_fa := xfa) (x_aa := xaa) (x_fb := xfb) (x_ab := xab)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_jdpbrpwd := ld2)
            (ev_qpbdiktk := e3) (hne_uxmrfcba := hne) (he_seecanle := hr) (hc_hqtvxjwb := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨Ef₁, Ea₁, rfl, hf₁, -⟩ := TmOExact.app_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨Ef₂, Ea₂, rfl, hf₂, -⟩ := TmOExact.app_of_load hvb ld2
          have hfeq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e3
            (sub fun c hc' => by rw [hc]; simp [hc'])).1 rfl xfa xfb Ef₁ Ef₂ rfl hf₁ hf₂
          have hf : Ef₁ ≠ Ef₂ := fun h => by subst h; rw [ite_eq_left rfl] at hfeq; exact hne hfeq
          rw [ite_eq_right (fun h => hf (Expr.app.inj h).1)]
        | .App_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_cdzwhmyt := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_jdpbrpwd := ld2)
            (hne_hriwjjoq := hne) (he_ksqgfajs := hr) (hc_imahflfm := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨Ef₁, Ea₁, rfl, -, -⟩ := TmOExact.app_of_load (hva.mono e2.heap_extends) ld1
          rw [ite_eq_right (fun h => tmOExact_not_app hvb hnlb ld2 hne _ _ h.symm)]
        | .Lam_Lam (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_ta := xta) (x_ba := xba) (x_la := xla) (x_tb := xtb) (x_bb := xbb) (x_lb := xlb)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_mgdxvnfg := ld2)
            (ev_wqkqunod := e3) (hc_qgmmesqa := hc) .. =>
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨Ta, Ba, ℓa, rfl, hta, hba, hla⟩ := TmOExact.lam_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨Tb, Bb, ℓb, rfl, htb, hbb, hlb⟩ := TmOExact.lam_of_load hvb ld2
          have hbeq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e3
            (sub fun c hc' => by rw [hc]; simp [hc'])).2 rfl xta xba xla xtb xbb xlb
            Ta Ba Tb Bb ℓa ℓb rfl hta hba hla htb hbb hlb
          rw [hbeq]
          congr 1
          exact if_congr (by constructor
            · rintro ⟨hm, ht, hb⟩; rw [hm, ht, hb]
            · intro h; obtain ⟨ht, hb, hm⟩ := Expr.lam.inj h; exact ⟨hm, ht, hb⟩) rfl rfl
        | .Lam_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_twnyxrgg := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_mgdxvnfg := ld2)
            (hne_xlqxdenb := hne) (he_xedhcvzi := hr) (hc_kjyrsefa := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨Ta, Ba, ℓa, rfl, -, -, -⟩ := TmOExact.lam_of_load (hva.mono e2.heap_extends) ld1
          rw [ite_eq_right (fun h => tmOExact_not_lam hvb hnlb ld2 hne _ _ _ h.symm)]
        | .Forall_Forall (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_da := xda) (x_xa := xxa) (x_la := xla) (x_db := xdb) (x_xb := xxb) (x_lb := xlb)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_ugduqnkn := ld2)
            (ev_rbltvbke := e3) (hc_qynhidow := hc) .. =>
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨Ta, Ba, ℓa, rfl, hta, hba, hla⟩ :=
            TmOExact.forallE_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨Tb, Bb, ℓb, rfl, htb, hbb, hlb⟩ := TmOExact.forallE_of_load hvb ld2
          have hbeq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e3
            (sub fun c hc' => by rw [hc]; simp [hc'])).2 rfl xda xxa xla xdb xxb xlb
            Ta Ba Tb Bb ℓa ℓb rfl hta hba hla htb hbb hlb
          rw [hbeq]
          congr 1
          exact if_congr (by constructor
            · rintro ⟨hm, ht, hb⟩; rw [hm, ht, hb]
            · intro h; obtain ⟨ht, hb, hm⟩ := Expr.forallE.inj h; exact ⟨hm, ht, hb⟩) rfl rfl
        | .Forall_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_lrjojuby := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_ugduqnkn := ld2)
            (hne_ygvycxyu := hne) (he_zxmbyfva := hr) (hc_hkhtpxta := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨Ta, Ba, ℓa, rfl, -, -, -⟩ :=
            TmOExact.forallE_of_load (hva.mono e2.heap_extends) ld1
          rw [ite_eq_right (fun h => tmOExact_not_forall hvb hnlb ld2 hne _ _ _ h.symm)]
        | .Let (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1)
            (hc_qubwlzze := hc) .. =>
          obtain ⟨-, hnla⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          exact ((hnla.mono e2.heap_extends).ne_let ld1).elim
        | .Lit_Lit (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_la := xla) (x_lb := xlb) (ev_dkmtahfq := e1) (ev_yasdpozq := e2)
            (ld_bolbylmd := ld1) (ld_ptpxgqds := ld2) (ev_wrcoxtmu := e3)
            (hc_nsbluauc := hc) .. =>
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨da, rda, hda⟩ := tmOExact_lit_rep (hva.mono e2.heap_extends) ld1
          obtain ⟨db, rdb, hdb⟩ := tmOExact_lit_rep hvb ld2
          obtain ⟨hr, -⟩ := literal_eq_exact rda rdb e3
          rw [hr]
          congr 1
          refine if_congr ?_ rfl rfl
          rcases hda with ⟨la, rfl, hca, rfl⟩ | ⟨ba, sa, rfl, hsa, rfl⟩ <;>
          rcases hdb with ⟨lb, rfl, hcb, rfl⟩ | ⟨bb, sb, rfl, hsb, rfl⟩
          · constructor
            · intro h; injection h with h; subst h; rfl
            · intro h
              have hv : limbsVal la = limbsVal lb := by
                injection h with h'; injection h'
              exact congrArg _ (IxVM.Refinement.Core.NatAux.canon_inj hca hcb hv)
          · constructor <;> (intro h; cases h)
          · constructor <;> (intro h; cases h)
          · constructor
            · intro h; injection h with h; subst h
              exact congrArg (fun s => Expr.lit (.strVal s)) ((strBytes_eq_iff hsa hsb).mpr rfl)
            · intro h
              have hs : sa = sb := by injection h with h'; injection h'
              exact congrArg _ ((strBytes_eq_iff hsa hsb).mp hs)
        | .Lit_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_sbguokbx := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_ptpxgqds := ld2)
            (hne_yxzlpqgw := hne) (he_srzasnzc := hr) (hc_vizqtvau := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨_, _, hda⟩ := tmOExact_lit_rep (hva.mono e2.heap_extends) ld1
          rcases hda with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩
          · rw [ite_eq_right (fun h => tmOExact_not_lit hvb hnlb ld2 hne _ h.symm)]
          · rw [ite_eq_right (fun h => tmOExact_not_lit hvb hnlb ld2 hne _ h.symm)]
        | .Proj_Proj_n1_n0 (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (x_sa := xsa) (x_fa2 := xfa) (x_ea := xea) (x_sb := xsb) (x_fb2 := xfb) (x_eb := xeb)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_ggorfniu := ld2)
            (ev_njfmqxdm := e3) (op_uvgqsrln := op) (ev_azarbcnx := e4)
            (hc_gywgrwem := hc) .. =>
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨aa, ia, Ea, rfl, rfl, raa, hea⟩ :=
            TmOExact.proj_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨ab, ib, Eb, rfl, rfl, rab, heb⟩ := TmOExact.proj_of_load hvb ld2
          obtain ⟨heq, rfl⟩ := Lib.address_eq_spec e3 raa rab
          have hab : aa = ab := by
            by_contra hne; rw [ite_eq_right hne] at heq
            exact absurd (Value.field.inj heq) (by decide)
          subst hab
          have hi : ia = ib := sub_eq_zero.mp (Value.field.inj (evalBinOp_sub_field op).symm)
          subst hi
          have heeq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e4
            (sub fun c hc' => by rw [hc]; simp [hc'])).1 rfl xea xeb Ea Eb rfl hea heb
          rw [heeq]; simp
        | .Proj_Proj_n1_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_ggorfniu := ld2)
            (ev_njfmqxdm := e3) (op_uvgqsrln := op) (hne_diaticjo := hne)
            (he_pjebkznh := hr) (hc_meiekgzc := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨aa, ia, Ea, rfl, rfl, raa, -⟩ :=
            TmOExact.proj_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨ab, ib, Eb, rfl, rfl, rab, -⟩ := TmOExact.proj_of_load hvb ld2
          have hsub := evalBinOp_sub_field op
          have hi : ia ≠ ib := fun h => hne (hsub.trans (by rw [h, sub_self]))
          rw [ite_eq_right (fun h => hi (ZMod.val_injective _ (Expr.proj.inj h).2.1))]
        | .Proj_Proj_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_ggorfniu := ld2)
            (ev_njfmqxdm := e3) (hne_zhhnixky := hne) (he_qypaxutd := hr)
            (hc_wmbrixkz := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, -⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨aa, ia, Ea, rfl, rfl, raa, -⟩ :=
            TmOExact.proj_of_load (hva.mono e2.heap_extends) ld1
          obtain ⟨ab, ib, Eb, rfl, rfl, rab, -⟩ := TmOExact.proj_of_load hvb ld2
          obtain ⟨heq, -⟩ := Lib.address_eq_spec e3 raa rab
          have hab : aa ≠ ab := fun h => by subst h; rw [ite_eq_left rfl] at heq; exact hne heq
          rw [ite_eq_right (fun h => hab (ixAddr_inj (hinj (Expr.proj.inj h).1)))]
        | .Proj_other (v_yahvaeuc := va) (m_rasepwbe := m1) (cs_gjslryle := cs1)
            (v_yhvxairr := vb) (m_awietpfd := m2) (cs_bokxvske := cs2) (v_maitkftz := v)
            (ev_dkmtahfq := e1) (ev_yasdpozq := e2) (ld_bolbylmd := ld1) (ld_ggorfniu := ld2)
            (hne_kplmouma := hne) (he_zzcuztba := hr) (hc_idnhlnac := hc) .. =>
          subst hr
          obtain ⟨hva, -⟩ := zeta_head_spec h₁ (sub fun c hc' => by rw [hc]; simp [hc']) e1
          obtain ⟨hvb, hnlb⟩ := zeta_head_spec (h₂.mono e1.heap_extends)
            (sub fun c hc' => by rw [hc]; simp [hc']) e2
          obtain ⟨aa, ia, Ea, rfl, rfl, -, -⟩ :=
            TmOExact.proj_of_load (hva.mono e2.heap_extends) ld1
          rw [ite_eq_right (fun h => tmOExact_not_proj hvb hnlb ld2 hne _ _ _ h.symm)]
      · subst hfn hargs
        match Obs.«KernelCheck::kexpr_zeta_binder_eq».obs ev with
        | .n1_n1 (ev_bvivxpnr := e1) (ev_aofpzgku := e2) (ev_bcksgtkp := e3)
            (hc_ujasjucw := hc) .. =>
          have hpw := pw_eq_exact hℓa hℓb e1
          have hm : bmeta ℓa = bmeta ℓb := by
            rw [bmeta_eq_iff]
            by_contra hne; rw [ite_eq_right hne] at hpw
            exact absurd (Value.field.inj hpw) (by decide)
          have hteq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e2
            (sub fun c hc' => by rw [hc]; simp [hc'])).1 rfl ta tb Ta Tb rfl
            (hTa.mono e1.heap_extends) (hTb.mono e1.heap_extends)
          have ht : Ta = Tb := by
            by_contra hne; rw [ite_eq_right hne] at hteq
            exact absurd (Value.field.inj hteq) (by decide)
          subst ht
          have ext12 := e1.heap_extends.trans e2.heap_extends
          have hbeq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e3
            (sub fun c hc' => by rw [hc]; simp [hc'])).1 rfl ba bb Ba Bb rfl
            (hBa.mono ext12) (hBb.mono ext12)
          rw [hbeq]
          simp [hm]
        | .n1_other (ev_bvivxpnr := e1) (ev_aofpzgku := e2) (hne_qnsahksn := hne)
            (he_flopnzhy := hr) (hc_lfsktsxj := hc) .. =>
          subst hr
          have hteq := (ih _ _ _ _ _ _ (by rw [hc]; simp; omega) e2
            (sub fun c hc' => by rw [hc]; simp [hc'])).1 rfl ta tb Ta Tb rfl
            (hTa.mono e1.heap_extends) (hTb.mono e1.heap_extends)
          have ht : Ta ≠ Tb := fun h => by subst h; rw [ite_eq_left rfl] at hteq; exact hne hteq
          rw [ite_eq_right (fun h => ht h.2.1)]
        | .other (ev_bvivxpnr := e1) (hne_rehascgg := hne) (he_vpckpvxl := hr) .. =>
          subst hr
          have hpw := pw_eq_exact hℓa hℓb e1
          have hm : bmeta ℓa ≠ bmeta ℓb := fun h => by
            rw [bmeta_eq_iff] at h
            rw [ite_eq_left h] at hpw
            exact hne hpw
          rw [ite_eq_right (fun h => hm h.1)] )

/-- **`KernelCheck::kexpr_zeta_struct_eq`** decides syntactic equality of two exact `KExpr`s
bidirectionally whenever `κ` is injective. -/
theorem kexpr_zeta_struct_eq_exact {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {h h' : Heap F} {E₁ E₂ : KExpr} {p₁ p₂ r : SourceValue F} {cs : List (Call F)}
    (h₁ : TmOExact κ h E₁ p₁) (h₂ : TmOExact κ h E₂ p₂)
    (bd : IxVM.Consistency.Bounded cs)
    (ev : ObsFn W "KernelCheck::kexpr_zeta_struct_eq" [p₁, p₂] h r h' cs) :
    r = .field (if E₁ = E₂ then 1 else 0) :=
  (zeta_struct_eq_bundle hinj _ _ _ _ _ _ ev bd).1 rfl p₁ p₂ E₁ E₂ rfl h₁ h₂

/-- **`KernelCheck::spec_params_zeta_eq`** decides list equality of two exact `KExpr` lists
bidirectionally whenever `κ` is injective. -/
theorem spec_params_zeta_eq_exact {κ : _root_.Address → KKey} (hinj : Function.Injective κ)
    {h h' : Heap F} {xs ys : List KExpr} {px py r : SourceValue F}
    {cs : List (Call F)}
    (hx : RepList kexprListEnum (TmOExact κ) h xs px)
    (hy : RepList kexprListEnum (TmOExact κ) h ys py)
    (bd : IxVM.Consistency.Bounded cs)
    (ev : ObsFn W "KernelCheck::spec_params_zeta_eq" [px, py] h r h' cs) :
    r = .field (if xs = ys then 1 else 0) := by
  have sub : ∀ {cs' : List (Call F)}, (∀ c ∈ cs', c ∈ cs) → IxVM.Consistency.Bounded cs' :=
    fun hs => RomBound.bounded_mono bd hs
  match Obs.«KernelCheck::spec_params_zeta_eq».obs ev with
  | .Nil_Nil (ld_bolbylmd := ld1) (ld_vplaigqg := ld2) (he_ptgtdktu := hr) .. =>
    obtain rfl := Core.RepList.nil_of_load hx ld1
    obtain rfl := Core.RepList.nil_of_load hy ld2
    rw [hr, ite_eq_left rfl]
  | .Nil_other (v_lekjiumn := v) (ld_bolbylmd := ld1) (ld_vplaigqg := ld2)
      (hne_akcscckh := hne) (he_kmfczmgt := hr) .. =>
    obtain rfl := Core.RepList.nil_of_load hx ld1
    rw [hr]
    cases ys with
    | nil =>
      cases hy with
      | nil cell =>
        have hld := Lib.load_enum_cell cell
        rw [ld2] at hld
        injection hld with hv
        exact absurd hv (hne [] rfl)
    | cons _ _ => simp
  | .Cons_Nil (ld_bolbylmd := ld1) (ld_txwzgqvr := ld2) (he_jkiddynw := hr) .. =>
    obtain ⟨_, _, rfl, -, -⟩ := Core.RepList.cons_of_load hx ld1
    obtain rfl := Core.RepList.nil_of_load hy ld2
    rw [hr]; simp
  | .Cons_Cons_n1 (x_x := xx) (x_xr := xxr) (x_y := xy) (x_yr := xyr)
      (cs_noorzezv := cs1) (cs_ixmjjldq := cs2) (ld_bolbylmd := ld1) (ld_txwzgqvr := ld2)
      (ev_vzplvuse := e1) (ev_kzuapeok := e2) (hc_givorsyo := hc) .. =>
    obtain ⟨x, xs', rfl, hx1, hxs⟩ := Core.RepList.cons_of_load hx ld1
    obtain ⟨y, ys', rfl, hy1, hys⟩ := Core.RepList.cons_of_load hy ld2
    have hxyeq := kexpr_zeta_struct_eq_exact hinj hx1 hy1
      (sub fun c hc' => by rw [hc]; simp [hc']) e1
    have hxy : x = y := by
      by_contra hne; rw [ite_eq_right hne] at hxyeq
      exact absurd (Value.field.inj hxyeq) (by decide)
    subst hxy
    have hlt : cs2.length < cs.length := by
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    have hrest := spec_params_zeta_eq_exact hinj
      (tmOExactList_mono e1.heap_extends hxs)
      (tmOExactList_mono e1.heap_extends hys)
      (sub fun c hc' => by rw [hc]; simp [hc']) e2
    rw [hrest]; simp
  | .Cons_Cons_other (x_x := xx) (x_xr := xxr) (x_y := xy) (x_yr := xyr)
      (cs_noorzezv := cs1) (ld_bolbylmd := ld1) (ld_txwzgqvr := ld2)
      (ev_vzplvuse := e1) (hne_gadltmfj := hne) (he_bjqpniqr := hr) (hc_ixgblxxm := hc) .. =>
    obtain ⟨x, xs', rfl, hx1, -⟩ := Core.RepList.cons_of_load hx ld1
    obtain ⟨y, ys', rfl, hy1, -⟩ := Core.RepList.cons_of_load hy ld2
    have hxyeq := kexpr_zeta_struct_eq_exact hinj hx1 hy1
      (sub fun c hc' => by rw [hc]; simp [hc']) e1
    have hxy : x ≠ y := fun h => by subst h; rw [ite_eq_left rfl] at hxyeq; exact hne hxyeq
    rw [hr, ite_eq_right (fun h => hxy (List.cons.inj h).1)]
termination_by cs.length

end IxVM.Refinement.Binding.FamilyRecon
