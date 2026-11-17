import IxVMRefinement.StatementRel.LoadedReads
import IxVMRefinement.Assembly.RecordReadBare

/-! # A checked record: its check evidence and its reading, for one declaration

The claim walk checks an address by loading its record and running
`KernelCheck::check_const` on the loaded constant (`Claim.CheckedAtFull`). For a standalone
definition, theorem, opaque or axiom record this module turns that into the two things a
declaration step and the public statement need, about one and the same declaration:

* the check evidence the step consumes (`Assembly.CheckedConstOrigin`): the heap terms of the
  type and value represent annotations of the declared type and value, on the heaps of the
  observed `k_ensure_sort` and `k_check` runs;
* the record at the address declares the constant that declaration installs (`Reads`).

The evidence alone does not say that its declared type and value are the record's: the
reading does, and both are produced here from the one load. No run of the kernel's stream
reader is involved; the declared type and value are the kernel reader's conversions of the
record's expressions in the reading context (`LoadedReads.defn_reading`), and they are well
scoped because the circuit validated them (`KernelCheck::validate_expr_well_scoped`).

The reducibility hint of a definition is free: the evidence and the reading hold for every
hint, the same on both sides.
-/

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency

private theorem mem_sublist_of_cons_left {α : Type} {x : α} {ys cs : List α}
    (h : ∀ c ∈ x :: ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_cons_of_mem _ hm)

private theorem mem_sublist_of_append_right {α : Type} {xs ys cs : List α}
    (h : ∀ c ∈ xs ++ ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_append_right _ hm)

/-- `KernelCheck::is_unsafe_ci` on a definition in Lean's logic returns `0` and leaves the
heap unchanged. -/
private theorem is_unsafe_ci_defnValShape_safe {d : Ixon.Definition}
    {tyPtr valPtr hint v1 : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (hsafe : Ix.Kernel.Reader.safetyDecline d = none)
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [L1.defnValShape d tyPtr valPtr hint] h v1 m2 cs) :
    v1 = .field 0 ∧ m2 = h := by
  cases hk : d.kind with
  | defn =>
    have hs : d.safety = .safe := by
      rw [Ix.Kernel.Reader.safetyDecline, hk] at hsafe
      cases hds : d.safety with
      | safe => rfl
      | unsaf => rw [hds] at hsafe; exact absurd hsafe (by decide)
      | part => rw [hds] at hsafe; exact absurd hsafe (by decide)
    simp only [L1.defnValShape, hk, hs] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Defn_Safe _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Defn_other _ _ _ _ _ _ hv hne _ _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      exact (hne [] rfl (by simpa [L1.repDefSafetyVal] using hs_eq.symm)).elim
    | Axiom _ _ _ hv | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | opaq =>
    have hns : (d.safety == .unsaf) = false := by
      simpa [Ix.Kernel.Reader.safetyDecline, Ix.Kernel.Reader.safetyDeclineOf, hk] using hsafe
    simp only [L1.defnValShape, hk, hns] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Opaque _ _ _ _ _ _ _ hv he hr _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hu_eq⟩
      rw [← hu_eq] at he
      exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Thm _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv
  | thm =>
    simp only [L1.defnValShape, hk] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Thm _ _ _ _ _ _ he hr _ => exact ⟨he, hr⟩
    | Axiom _ _ _ hv | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
    | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
      simp [Core.kciEnum] at hv

private theorem is_unsafe_ci_axio_safe {ax : Ixon.Axiom}
    {tyPtr v1 : SourceValue F} {h m2 : Heap F} {cs : List (Call F)}
    (hsafe : ax.isUnsafe = false)
    (ev : ObsFn Core.W "KernelCheck::is_unsafe_ci"
      [.construct Core.kciEnum "Axiom"
        [.field (ax.lvls.toNat : F), tyPtr, L1.repBoolField ax.isUnsafe]] h v1 m2 cs) :
    v1 = .field 0 ∧ m2 = h := by
  cases «KernelCheck::is_unsafe_ci».obs ev with
  | Axiom _ _ _ hv he hr _ =>
    simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
    rcases hv with ⟨_, _, hu⟩
    simp [hsafe, L1.repBoolField] at hu
    exact ⟨he.trans hu.symm, hr⟩
  | Defn_Safe _ _ _ _ _ hv | Defn_other _ _ _ _ _ _ hv
  | Thm _ _ _ _ _ hv | Opaque _ _ _ _ _ _ _ hv | Quot _ _ _ _ _ _ _ hv
  | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv
  | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv =>
    simp [Core.kciEnum] at hv

section Checked

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)}

/-- **The check of a loaded definition, theorem or opaque payload, against its reading.**
The payload was converted with no `recur` in scope (`hraw_d`), its type and value read as
`ty₀`, `val₀` in the reading context, and `KernelCheck::check_const` ran on the converted
value. Then the readings are well scoped, and for every hint the declaration of the payload
under the key of `decl_addr` has its check evidence, and installs the constant the payload
declares. -/
theorem checkedDefn_core (ht : t.check = .ok ()) (hbound : Bounded calls)
    {E : Ixon.Env} {bAddr decl_addr : _root_.Address} {order_role : List _root_.Address}
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant} {d : Ixon.Definition}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {ty₀ val₀ : Ix.Kernel.Expr .anon}
    (hdecl_not_role : decl_addr ∉ order_role)
    (hsafe_decl : Ix.Kernel.Reader.safetyDecline d = none)
    {lim : Nat} {m_chk h'_chk : Heap F} {rc ap v r_chk : SourceValue F}
    {cs_chk : List (Call F)} {blobs : List (_root_.Address × ByteArray)}
    (hrc_m : Claim.RCFullRep t bAddr lim m_chk rc)
    (hblob : ∀ x bs, (x, bs) ∈ blobs → blob x = some bs)
    (hraw_d : L1.RawDefnValRep src.refs.toList [] src.univs.toList src.sharing.toList blobs
      m_chk d v)
    (hty : (exprReader t blob src id self).read d.typ = .ok ty₀)
    (hval : (exprReader t blob src id self).read d.value = .ok val₀)
    (ev_chk : ObsFn Core.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ty₀.looseBVarsBounded 0 = true ∧
    ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
    val₀.looseBVarsBounded 0 = true ∧
    val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
    ∀ hn : Ix.Kernel.ReducibilityHint, ∃ decl : Ix.Kernel.Declaration .anon,
      Assembly.CheckedConstOrigin calls t bAddr E order_role decl ∧
      IxVM.Consistency.installs decl =
        [defnConst d.kind ⟨keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀ hn] := by
  obtain ⟨hnlvls, tyPtr, valPtr, hintVal, rfl, raw_ty, raw_val⟩ := hraw_d
  have hkeyAt := readCtx_keyAt_inv ht blob
  have hrd_ty_rp : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.typ = .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  have hrd_val_rp : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam (List.range d.lvls.toNat)) self).read d.value = .ok val₀ := by
    rw [Assembly.recParam_range]
    exact hval
  cases hk : d.kind with
  | defn =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Defn"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repDefSafetyVal d.safety, hintVal] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
    | Thm | Opaque | Quot
    | Induct_n0 | Induct_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Defn v1 m2 cs12 x_nlvls x_ty x_val _ _ _ m299 cs309 _ m336 cs346 v372 m373 cs383 m404
        _ m417 cs427 _ m447 cs457 cs479 m508
        ev14 _ hv269 ev311 ev348 hm412 ev385 ev429 ev459 hm516 ev481 hc520 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe_decl ev14
      subst v1; subst m2
      rw [hv_shape] at hv269
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv269
      obtain ⟨hxn, hxt, hxv, -, -⟩ := hv269
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right (mem_sublist_of_cons_left (by rwa [hc520] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs383, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs3)
      have hs5 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs4)
      have hs6 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs5)
      have hcl_kc := hs6 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left hs6
      obtain ⟨cs_sr1, ev_sr1, hcs427⟩ := Assembly.assert_safety_zero_spec ev429
      obtain ⟨cs_sr2, ev_sr2, hcs457⟩ := Assembly.assert_safety_zero_spec ev459
      have ext_336_404 : Heap.Extends m336 m404 := by rw [hm412]; exact Heap.Extends.snoc _ _
      have ext_447_508 : Heap.Extends m447 m508 := by rw [hm516]; exact Heap.Extends.snoc _ _
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_ty (Heap.Extends.refl m_chk) hty ev311 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_val ev311.heap_extends hval ev348 hcl_v2
      have ext_m_404 : Heap.Extends m_chk m404 :=
        ev311.heap_extends.trans (ev348.heap_extends.trans ext_336_404)
      have ext_373_508 : Heap.Extends m373 m508 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_447_508)
      have ext_404_508 : Heap.Extends m404 m508 := ev385.heap_extends.trans ext_373_508
      have ext_m_508 : Heap.Extends m_chk m508 := ext_m_404.trans ext_404_508
      obtain ⟨ty', hty_ann, hty_tmc_m⟩ :=
        raw_ty.toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls) hkeyAt
          (fun _ _ _ _ h => nomatch h) hblob hrd_ty_rp hty_lbb hty_def
      obtain ⟨val', hval_ann, hval_tmc_m⟩ :=
        raw_val.toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls) hkeyAt
          (fun _ _ _ _ h => nomatch h) hblob hrd_val_rp hval_lbb hval_def
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev311
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev311.heap_extends hval_tmc_m) hval_ann hval_def ev348
      have hty_tmc_404 := Core.TmC.mono ext_m_404 hty_tmc_m
      have hval_tmc_508 := Core.TmC.mono ext_m_508 hval_tmc_m
      refine ⟨hty_lbb, hty_def, hval_lbb, hval_def, fun hn => ?_⟩
      exact ⟨.defnDecl ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀ hn,
        .defnDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm412 hty_tmc_404 (hrc_m.mono ext_m_404) ev385 hcl_es hsub_es
          ext_373_508 hm516 (Core.TmC.mono ext_404_508 hty_tmc_404) hval_tmc_508
          (hrc_m.mono ext_m_508) ev481 hcl_kc hsub_kc, rfl⟩
  | thm =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Thm" [.field (d.lvls.toNat : F), tyPtr, valPtr] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn
    | Opaque | Quot
    | Induct_n0 | Induct_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Thm v1 m2 cs12 x_nlvls x_ty x_val _ m544 cs554 _ m581 cs591 v617 m618 cs628 m649
        v672 m675 cs683 m696 _ m716 cs726 _ m746 cs756 cs778 m807
        ev14 _ _ hv526 ev556 ev593 hm657 ev630 hm704 ev685 heq714 ev728 ev758 hm815 ev780 hc819 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe_decl ev14
      subst v1; subst m2
      subst v672
      rw [hv_shape] at hv526
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv526
      obtain ⟨hxn, hxt, hxv⟩ := hv526
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right (mem_sublist_of_cons_left (by rwa [hc819] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs628, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs3)
      have hcl_le := hs4 _ List.mem_cons_self
      have hsub_le : ∀ cl ∈ cs683, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs4) cl (List.mem_append_left _ hm)
      have hs5 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs4)
      have hs6 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs5)
      have hs7 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs6)
      have hcl_kc := hs7 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left hs7
      obtain ⟨cs_sr1, ev_sr1, hcs726⟩ := Assembly.assert_safety_zero_spec ev728
      obtain ⟨cs_sr2, ev_sr2, hcs756⟩ := Assembly.assert_safety_zero_spec ev758
      have ext_581_649 : Heap.Extends m581 m649 := by rw [hm657]; exact Heap.Extends.snoc _ _
      have ext_618_696 : Heap.Extends m618 m696 := by rw [hm704]; exact Heap.Extends.snoc _ _
      have ext_746_807 : Heap.Extends m746 m807 := by rw [hm815]; exact Heap.Extends.snoc _ _
      have ext_m_649 : Heap.Extends m_chk m649 :=
        ev556.heap_extends.trans (ev593.heap_extends.trans ext_581_649)
      have ext_649_675 : Heap.Extends m649 m675 :=
        ev630.heap_extends.trans (ext_618_696.trans ev685.heap_extends)
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_ty (Heap.Extends.refl m_chk) hty ev556 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_val ev556.heap_extends hval ev593 hcl_v2
      have ext_675_807 : Heap.Extends m675 m807 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_746_807)
      have ext_649_807 : Heap.Extends m649 m807 := ext_649_675.trans ext_675_807
      have ext_m_807 : Heap.Extends m_chk m807 := ext_m_649.trans ext_649_807
      obtain ⟨ty', hty_ann, hty_tmc_m⟩ :=
        raw_ty.toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls) hkeyAt
          (fun _ _ _ _ h => nomatch h) hblob hrd_ty_rp hty_lbb hty_def
      obtain ⟨val', hval_ann, hval_tmc_m⟩ :=
        raw_val.toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls) hkeyAt
          (fun _ _ _ _ h => nomatch h) hblob hrd_val_rp hval_lbb hval_def
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev556
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev556.heap_extends hval_tmc_m) hval_ann hval_def ev593
      have hty_tmc_649 := Core.TmC.mono ext_m_649 hty_tmc_m
      have hval_tmc_807 := Core.TmC.mono ext_m_807 hval_tmc_m
      refine ⟨hty_lbb, hty_def, hval_lbb, hval_def, fun hn => ?_⟩
      exact ⟨.thmDecl ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀,
        .thmDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm657 hty_tmc_649 (hrc_m.mono ext_m_649) ev630 hcl_es hsub_es
          hm704 ev685 hcl_le hsub_le
          ext_675_807 hm815 (Core.TmC.mono ext_649_807 hty_tmc_649) hval_tmc_807
          (hrc_m.mono ext_m_807) ev780 hcl_kc hsub_kc, rfl⟩
  | opaq =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Opaque"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repBoolField (d.safety == .unsaf)] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn | Thm
    | Quot
    | Induct_n0 | Induct_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Opaque v1 m2 cs12 x_nlvls x_ty x_val _ _ m849 cs859 _ m886 cs896 v922 m923 cs933 m954
        _ m967 cs977 _ m997 cs1007 cs1029 m1058
        ev14 _ _ _ hv825 ev861 ev898 hm962 ev935 ev979 ev1009 hm1066 ev1031 hc1070 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe hsafe_decl ev14
      subst v1; subst m2
      rw [hv_shape] at hv825
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv825
      obtain ⟨hxn, hxt, hxv, -⟩ := hv825
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right (mem_sublist_of_cons_left (by rwa [hc1070] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs933, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs3)
      have hs5 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs4)
      have hs6 := mem_sublist_of_append_right (mem_sublist_of_cons_left hs5)
      have hcl_kc := hs6 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left hs6
      obtain ⟨cs_sr1, ev_sr1, hcs977⟩ := Assembly.assert_safety_zero_spec ev979
      obtain ⟨cs_sr2, ev_sr2, hcs1007⟩ := Assembly.assert_safety_zero_spec ev1009
      have ext_886_954 : Heap.Extends m886 m954 := by rw [hm962]; exact Heap.Extends.snoc _ _
      have ext_997_1058 : Heap.Extends m997 m1058 := by rw [hm1066]; exact Heap.Extends.snoc _ _
      obtain ⟨_, hty_lbb, hty_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_ty (Heap.Extends.refl m_chk) hty ev861 hcl_v1
      obtain ⟨_, hval_lbb, hval_def⟩ :=
        Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob) (self := self) hbound
          hnlvls raw_val ev861.heap_extends hval ev898 hcl_v2
      have ext_m_954 : Heap.Extends m_chk m954 :=
        ev861.heap_extends.trans (ev898.heap_extends.trans ext_886_954)
      have ext_923_1058 : Heap.Extends m923 m1058 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_997_1058)
      have ext_954_1058 : Heap.Extends m954 m1058 := ev935.heap_extends.trans ext_923_1058
      have ext_m_1058 : Heap.Extends m_chk m1058 := ext_m_954.trans ext_954_1058
      obtain ⟨ty', hty_ann, hty_tmc_m⟩ :=
        raw_ty.toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls) hkeyAt
          (fun _ _ _ _ h => nomatch h) hblob hrd_ty_rp hty_lbb hty_def
      obtain ⟨val', hval_ann, hval_tmc_m⟩ :=
        raw_val.toTmC
          (recurAddrs := []) (κ := Core.keyOf t) (ps := List.range d.lvls.toNat)
          (by simp) (by simpa using hnlvls) hkeyAt
          (fun _ _ _ _ h => nomatch h) hblob hrd_val_rp hval_lbb hval_def
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev861
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev861.heap_extends hval_tmc_m) hval_ann hval_def ev898
      have hty_tmc_954 := Core.TmC.mono ext_m_954 hty_tmc_m
      have hval_tmc_1058 := Core.TmC.mono ext_m_1058 hval_tmc_m
      refine ⟨hty_lbb, hty_def, hval_lbb, hval_def, fun hn => ?_⟩
      exact ⟨.opaqueDecl ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀,
        .opaqueDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm962 hty_tmc_954 (hrc_m.mono ext_m_954) ev935 hcl_es hsub_es
          ext_923_1058 hm1066 (Core.TmC.mono ext_954_1058 hty_tmc_954) hval_tmc_1058
          (hrc_m.mono ext_m_1058) ev1031 hcl_kc hsub_kc, rfl⟩

variable {E : Ixon.Env}

/-- **A checked standalone definition, theorem or opaque record.** The walk checked `a`
(`Claim.CheckedAtFull`), the run's store holds the record `c` there, in Lean's logic. Then
there are the readings `ty₀`, `val₀` of its type and value such that for every hint there is
one declaration with

* its check evidence (`Assembly.CheckedConstOrigin`, what the walked-constant step consumes),
* which installs exactly the constant `defnConst d.kind ⟨keyOf t a, …, ty₀⟩ val₀ hn`,
* which the record at `a` declares (`Reads`).

So a step that stores what the declaration installs (`StoredAs`) stores a reading of the
record at `a`, with the hint the declaration was given. -/
theorem checkedAtFull_defn (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) {bAddr a : _root_.Address} {order_role : List _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} (hrec : Ix.Cert.recordAt E a = some c)
    (hinfo : c.info = .defn d) (hlogic : InLogic c) (hnot_role : a ∉ order_role)
    (hchk : Claim.CheckedAtFull calls bAddr t a) :
    ∃ ty₀ val₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.typ = .ok ty₀ ∧
      (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value = .ok val₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      val₀.looseBVarsBounded 0 = true ∧
      val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      ∀ hn : Ix.Kernel.ReducibilityHint, ∃ decl : Ix.Kernel.Declaration .anon,
        Assembly.CheckedConstOrigin calls t bAddr E order_role decl ∧
        IxVM.Consistency.installs decl =
          [defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn] ∧
        Reads t E a (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, hrc_pre, hrc_m, ha_pre, ha_m, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := Assembly.checkedAtFull_loadedL1 hbound hchk
  obtain ⟨-, -, v', hld', hraw⟩ := loadedL1_record hS hsub_ld hhash_ld hblake_ld hL1 hrec
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨blobs, hb_ld, raw⟩ := hraw
  have hblob := hS.blob_of_table hload_ld hsub_ld hb_ld
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    defn_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic hblob raw
  obtain ⟨h1, h2, h3, h4, hdecl⟩ :=
    checkedDefn_core (E := E) (order_role := order_role) (decl_addr := a) ht hbound hnot_role
      hsafe hrc_m hblob raw' hty hval ev_chk hsub_chk
  refine ⟨ty₀, val₀, hty, hval, h1, h2, h3, h4, fun hn => ?_⟩
  obtain ⟨decl, hcco, hinst⟩ := hdecl hn
  exact ⟨decl, hcco, hinst, hreads hn⟩

/-- **A checked axiom record**, at an address no inert role is bound to. The declaration of
the record has its check evidence, and where it installs a constant (it installs none at
the key of `Quot.sound`, which the quotient package holds), the record at `a` declares that
constant. -/
theorem checkedAtFull_axiom (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) {bAddr a : _root_.Address} {order_role : List _root_.Address}
    {c : Ixon.Constant} {ax : Ixon.Axiom} (hrec : Ix.Cert.recordAt E a = some c)
    (hinfo : c.info = .axio ax) (hlogic : InLogic c) (hinert : ¬ InertAt t a)
    (hnot_role : a ∉ order_role) (hchk : Claim.CheckedAtFull calls bAddr t a) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E.blobs.get? x) c id (fun _ => none)).read ax.typ = .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ax.lvls.toNat) = true ∧
      Assembly.CheckedConstOrigin calls t bAddr E order_role
        (.axiomDecl ⟨keyOf t a, List.range ax.lvls.toNat, ty₀⟩) ∧
      Reads t E a (.axiomInfo ⟨keyOf t a, List.range ax.lvls.toNat, ty₀⟩) := by
  have hsafe : ax.isUnsafe = false := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    bytes, E_ld, hrc_pre, hrc_m, ha_pre, ha_m, hhash_ld, hblake_ld, hload_ld, hL1,
    hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := Assembly.checkedAtFull_loadedL1 hbound hchk
  obtain ⟨-, -, v', hld', hraw⟩ := loadedL1_record hS hsub_ld hhash_ld hblake_ld hL1 hrec
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨blobs, hb_ld, raw⟩ := hraw
  have hblob := hS.blob_of_table hload_ld hsub_ld hb_ld
  obtain ⟨ty₀, hty, hreads, -⟩ :=
    axio_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic (inertKey_false_of_not_inertAt ht hinert)
      hblob raw
  obtain ⟨hnlvls, tyPtr, rfl, raw_ty⟩ := raw
  have hkeyAt := readCtx_keyAt_inv ht (fun x => E.blobs.get? x)
  have hrd_ty_rp : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam (List.range ax.lvls.toNat)) (fun _ => none)).read ax.typ =
      .ok ty₀ := by
    rw [Assembly.recParam_range]
    exact hty
  cases «KernelCheck::check_const».obs ev_chk with
  | Defn | Thm | Opaque | Quot
  | Induct_n0 | Induct_other
  | Ctor_n0_n0 | Ctor_n0_other | Ctor_other
  | Rec_n0 | Rec_other =>
    simp_all [Core.kciEnum]
  | Axiom_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ _ =>
    have h10 := (is_unsafe_ci_axio_safe hsafe ev14).1
    exact absurd (congrArg ZMod.val (Value.field.inj h10)) (by decide)
  | Axiom_other_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heq249 _ _ _ =>
    exact absurd (congrArg ZMod.val (Value.field.inj heq249)) (by decide)
  | Axiom_other_other v1 m2 cs12 x_nlvls x_ty _ _ m56 cs66 v92 m93 cs103 m124 _ m137 cs147
      v189 m190 cs201 ev14 hv37 ev68 hm132 ev105 ev149 _ ev203 hne255 _ _ hc263 =>
    obtain ⟨hv1, hm2⟩ := is_unsafe_ci_axio_safe hsafe ev14
    subst v1; subst m2
    simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv37
    obtain ⟨hx_nl, hx_ty, -⟩ := hv37
    subst x_nlvls; subst x_ty
    have hsub1 := mem_sublist_of_append_right
      (mem_sublist_of_cons_left (by rwa [hc263] at hsub_chk))
    have hcl_val := hsub1 _ List.mem_cons_self
    have hsub2 := mem_sublist_of_append_right (mem_sublist_of_cons_left hsub1)
    have hcl_es := hsub2 _ List.mem_cons_self
    have hsub_es : ∀ cl ∈ cs103, cl ∈ calls :=
      fun cl hm => (mem_sublist_of_cons_left hsub2) cl (List.mem_append_left _ hm)
    have hsub3 := mem_sublist_of_append_right (mem_sublist_of_cons_left hsub2)
    have hsub4 := mem_sublist_of_append_right (mem_sublist_of_cons_left hsub3)
    have hcl_ax := hsub4 _ List.mem_cons_self
    have hsub_ax := mem_sublist_of_cons_left hsub4
    obtain ⟨cs_sr, ev_sr, hcs147⟩ := Assembly.assert_safety_zero_spec ev149
    have ext_m56_m124 : Heap.Extends m56 m124 := by
      rw [hm132]; exact Heap.Extends.snoc _ _
    have ext_m_m93 : Heap.Extends m_chk m93 :=
      ev68.heap_extends.trans (ext_m56_m124.trans ev105.heap_extends)
    obtain ⟨_, hty_lbb, hty_def⟩ :=
      Assembly.validate_expr_well_scoped_spec (cx := readCtx t (fun x => E.blobs.get? x))
        (self := fun _ => none) hbound hnlvls raw_ty (Heap.Extends.refl m_chk) hty ev68 hcl_val
    have ext_m_m124 : Heap.Extends m_chk m124 := ev68.heap_extends.trans ext_m56_m124
    have raw_ty_m124 := raw_ty.mono ext_m_m124 (fun _ hm => hm)
    obtain ⟨ty', hty_ann, hty_tmc⟩ :=
      raw_ty_m124.toTmC (κ := Core.keyOf t) (ps := List.range ax.lvls.toNat)
        (by simp) (by simpa using hnlvls) hkeyAt (by simp) hblob hrd_ty_rp hty_lbb hty_def
    have ext_m_m137 : Heap.Extends m_chk m137 := ext_m_m93.trans ev_sr.heap_extends
    exact ⟨ty₀, hty, hty_lbb, hty_def,
      .axiomDecl hnot_role hrec hinfo hsafe hnlvls hty_lbb hty_def hty_ann
        hm132 hty_tmc (hrc_m.mono ext_m_m124) ev105 hcl_es hsub_es
        ev_sr.heap_extends (hrc_m.mono ext_m_m137) (Core.S0.addr_mono ext_m_m137 ha_m)
        ev203 hne255 hcl_ax hsub_ax, hreads⟩

/-! ## Over the claim walk

The claim phase's store is a run store, and every address the walk reached holds a record
there with its check (`Claim.WalkedL6`). So for every walked standalone definition, theorem
or opaque record in Lean's logic, the evidence and the reading exist over the one store of
records the run hashed. -/

/-- The role table the walk ran under is well formed. -/
theorem walkedL6_tableCheck {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (hw : Claim.WalkedL6 calls t E₀ seeds) : t.check = .ok () := by
  obtain ⟨bAddr, ⟨rb, -, -, hadm⟩, -⟩ := hw
  exact ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed

/-- **Every walked standalone definition, theorem or opaque record has its check evidence
and its reading over the run's store.** `E₀` is the claim phase's store (`LoadedBy calls E₀`,
`Claim.WalkedL6`): every record and blob in it is a byte string the run hashed. -/
theorem walkedL6_defn_reads (hbound : Bounded calls) {E₀ : Ixon.Env}
    {seeds : List _root_.Address} (hload : LoadedBy calls E₀)
    (hw : Claim.WalkedL6 calls t E₀ seeds) :
    ∃ (bAddr : _root_.Address) (Wk : _root_.Address → Prop), (∀ a ∈ seeds, Wk a) ∧
      ∀ (a : _root_.Address) (c : Ixon.Constant) (d : Ixon.Definition)
        (order_role : List _root_.Address),
        Wk a → Ix.Cert.recordAt E₀ a = some c → c.info = .defn d → InLogic c →
        a ∉ order_role →
        ∃ ty₀ val₀ : Ix.Kernel.Expr .anon, ∀ hn : Ix.Kernel.ReducibilityHint,
          ∃ decl : Ix.Kernel.Declaration .anon,
            Assembly.CheckedConstOrigin calls t bAddr E₀ order_role decl ∧
            IxVM.Consistency.installs decl =
              [defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn] ∧
            Reads t E₀ a (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) := by
  have ht := walkedL6_tableCheck hw
  have hS := RunStore.of_walkedL6 hload hw
  obtain ⟨bAddr, -, -, -, -, -, Wk, rank, hseeds, -, hchecked⟩ := hw
  refine ⟨bAddr, Wk, hseeds, fun a c d order_role hwk hrec hinfo hlogic hnot_role => ?_⟩
  obtain ⟨c', hrec', hchk⟩ := hchecked a hwk
  rw [hrec] at hrec'
  have hcc : c = c' := Option.some.inj hrec'
  subst hcc
  rcases hchk with ⟨ms, hms, -⟩ | hchk
  · rw [hinfo] at hms
    cases hms
  · obtain ⟨ty₀, val₀, -, -, -, -, -, -, hdecl⟩ :=
      checkedAtFull_defn ht hbound hS hrec hinfo hlogic hnot_role hchk
    exact ⟨ty₀, val₀, hdecl⟩

end Checked

end IxVM.Refinement.LoadedReads
