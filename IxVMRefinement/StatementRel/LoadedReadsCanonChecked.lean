import IxVMRefinement.StatementRel.LoadedReadsCanon
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Decl.DeclWalkedConst

/-! # A checked definition record stores its canonical constant

The walk checks an address by loading its record and running `KernelCheck::check_const` on the
loaded constant (`Claim.CheckedAtFull`, `Claim.MutsMemberCheckedAtFull`). For a definition,
theorem or opaque record this module produces the check evidence a declaration step consumes
(`Decl.CheckedConstOriginAt`) directly from that witness, with the declaration as it is stored
named: it is the canonical annotated constant of the record and its reading
(`LoadedReads.canonDefn`), not an annotation taken from an existential. The heap terms of the
evidence are represented under the keying of the prefix, given that the prefix stores the
references the record uses.

So the two inputs of the step about one record come from one place: the check evidence
(`checkedAtFull_defn_canon`, `mutsMember_defn_canon`) and the reload of the constant it stores
(`reloadsAs_defn_cons`, `reloadsAs_member_cons`), both about `canonDefn`.
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

private theorem mem_sublist_of_cons_left_c {α : Type} {x : α} {ys cs : List α}
    (h : ∀ c ∈ x :: ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_cons_of_mem _ hm)

private theorem mem_sublist_of_append_right_c {α : Type} {xs ys cs : List α}
    (h : ∀ c ∈ xs ++ ys, c ∈ cs) : ∀ c ∈ ys, c ∈ cs :=
  fun c hm => h c (List.mem_append_right _ hm)

/-- `KernelCheck::is_unsafe_ci` on a definition in Lean's logic returns `0` and leaves the
heap unchanged. -/
private theorem is_unsafe_ci_defnValShape_safe_c {d : Ixon.Definition}
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

private theorem toUInt64_toNat_cc {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

section Checked

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)}

/-- **The check of a loaded definition, theorem or opaque payload, for a named stored
declaration.** `KernelCheck::check_const` ran on a converted definition value whose type and
value pointers represent, under the keying `κ`, annotations `ty'`, `val'` of well-scoped
readings `ty₀`, `val₀`. Then for every hint the declaration of the readings under the key of
`decl_addr` has its check evidence at `κ`, with the declaration of the annotations as the one
stored. -/
theorem checkedDefn_at {κ : _root_.Address → Core.KKey}
    {E : Ixon.Env} {bAddr decl_addr : _root_.Address} {order_role : List _root_.Address}
    {d : Ixon.Definition} {ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon}
    (hdecl_not_role : decl_addr ∉ order_role)
    (hsafe_decl : Ix.Kernel.Reader.safetyDecline d = none)
    {lim : Nat} {m_chk h'_chk : Heap F} {rc ap r_chk tyPtr valPtr hintVal : SourceValue F}
    {cs_chk : List (Call F)}
    (hrc_m : Claim.RCFullRep t bAddr lim m_chk rc)
    (hnlvls : d.lvls.toNat < 4294967296)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hval_lbb : val₀.looseBVarsBounded 0 = true)
    (hval_def : val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true)
    (hty_ann : Annotates ty' ty₀) (hval_ann : Annotates val' val₀)
    (hty_tmc_m : Core.TmC κ m_chk (Core.posOf (List.range d.lvls.toNat) ty') tyPtr)
    (hval_tmc_m : Core.TmC κ m_chk (Core.posOf (List.range d.lvls.toNat) val') valPtr)
    (ev_chk : ObsFn Core.W "KernelCheck::check_const"
      [rc, L1.defnValShape d tyPtr valPtr hintVal, ap] m_chk r_chk h'_chk cs_chk)
    (hsub_chk : ∀ cl ∈ cs_chk, cl ∈ calls) :
    ∀ hn : Ix.Kernel.ReducibilityHint,
      Decl.CheckedConstOriginAt κ lim calls t bAddr E order_role
        (defnDecl d.kind ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
        (defnDecl d.kind ⟨Core.keyOf t decl_addr, List.range d.lvls.toNat, ty'⟩ val' hn) := by
  cases hk : d.kind with
  | defn =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Defn"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repDefSafetyVal d.safety, hintVal] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
    | Thm | Opaque | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Defn v1 m2 cs12 x_nlvls x_ty x_val _ _ _ m299 cs309 _ m336 cs346 v372 m373 cs383 m404
        _ m417 cs427 _ m447 cs457 cs479 m508
        ev14 _ hv269 ev311 ev348 hm412 ev385 ev429 ev459 hm516 ev481 hc520 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe_c hsafe_decl ev14
      subst v1; subst m2
      rw [hv_shape] at hv269
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv269
      obtain ⟨hxn, hxt, hxv, -, -⟩ := hv269
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c (by rwa [hc520] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs383, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left_c hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs3)
      have hs5 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs4)
      have hs6 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs5)
      have hcl_kc := hs6 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left_c hs6
      obtain ⟨cs_sr1, ev_sr1, hcs427⟩ := Assembly.assert_safety_zero_spec ev429
      obtain ⟨cs_sr2, ev_sr2, hcs457⟩ := Assembly.assert_safety_zero_spec ev459
      have ext_336_404 : Heap.Extends m336 m404 := by rw [hm412]; exact Heap.Extends.snoc _ _
      have ext_447_508 : Heap.Extends m447 m508 := by rw [hm516]; exact Heap.Extends.snoc _ _
      have ext_m_404 : Heap.Extends m_chk m404 :=
        ev311.heap_extends.trans (ev348.heap_extends.trans ext_336_404)
      have ext_373_508 : Heap.Extends m373 m508 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_447_508)
      have ext_404_508 : Heap.Extends m404 m508 := ev385.heap_extends.trans ext_373_508
      have ext_m_508 : Heap.Extends m_chk m508 := ext_m_404.trans ext_404_508
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev311
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev311.heap_extends hval_tmc_m) hval_ann hval_def ev348
      have hty_tmc_404 := Core.TmC.mono ext_m_404 hty_tmc_m
      have hval_tmc_508 := Core.TmC.mono ext_m_508 hval_tmc_m
      intro hn
      exact .defnDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm412 hty_tmc_404 (hrc_m.mono ext_m_404) ev385 hcl_es hsub_es
          ext_373_508 hm516 (Core.TmC.mono ext_404_508 hty_tmc_404) hval_tmc_508
          (hrc_m.mono ext_m_508) ev481 hcl_kc hsub_kc
  | thm =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Thm" [.field (d.lvls.toNat : F), tyPtr, valPtr] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn
    | Opaque | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Thm v1 m2 cs12 x_nlvls x_ty x_val _ m544 cs554 _ m581 cs591 v617 m618 cs628 m649
        v672 m675 cs683 m696 _ m716 cs726 _ m746 cs756 cs778 m807
        ev14 _ _ hv526 ev556 ev593 hm657 ev630 hm704 ev685 heq714 ev728 ev758 hm815 ev780 hc819 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe_c hsafe_decl ev14
      subst v1; subst m2
      subst v672
      rw [hv_shape] at hv526
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv526
      obtain ⟨hxn, hxt, hxv⟩ := hv526
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c (by rwa [hc819] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs628, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left_c hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs3)
      have hcl_le := hs4 _ List.mem_cons_self
      have hsub_le : ∀ cl ∈ cs683, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left_c hs4) cl (List.mem_append_left _ hm)
      have hs5 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs4)
      have hs6 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs5)
      have hs7 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs6)
      have hcl_kc := hs7 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left_c hs7
      obtain ⟨cs_sr1, ev_sr1, hcs726⟩ := Assembly.assert_safety_zero_spec ev728
      obtain ⟨cs_sr2, ev_sr2, hcs756⟩ := Assembly.assert_safety_zero_spec ev758
      have ext_581_649 : Heap.Extends m581 m649 := by rw [hm657]; exact Heap.Extends.snoc _ _
      have ext_618_696 : Heap.Extends m618 m696 := by rw [hm704]; exact Heap.Extends.snoc _ _
      have ext_746_807 : Heap.Extends m746 m807 := by rw [hm815]; exact Heap.Extends.snoc _ _
      have ext_m_649 : Heap.Extends m_chk m649 :=
        ev556.heap_extends.trans (ev593.heap_extends.trans ext_581_649)
      have ext_649_675 : Heap.Extends m649 m675 :=
        ev630.heap_extends.trans (ext_618_696.trans ev685.heap_extends)
      have ext_675_807 : Heap.Extends m675 m807 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_746_807)
      have ext_649_807 : Heap.Extends m649 m807 := ext_649_675.trans ext_675_807
      have ext_m_807 : Heap.Extends m_chk m807 := ext_m_649.trans ext_649_807
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev556
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev556.heap_extends hval_tmc_m) hval_ann hval_def ev593
      have hty_tmc_649 := Core.TmC.mono ext_m_649 hty_tmc_m
      have hval_tmc_807 := Core.TmC.mono ext_m_807 hval_tmc_m
      intro hn
      exact .thmDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm657 hty_tmc_649 (hrc_m.mono ext_m_649) ev630 hcl_es hsub_es
          hm704 ev685 hcl_le hsub_le
          ext_675_807 hm815 (Core.TmC.mono ext_649_807 hty_tmc_649) hval_tmc_807
          (hrc_m.mono ext_m_807) ev780 hcl_kc hsub_kc
  | opaq =>
    have hv_shape : L1.defnValShape d tyPtr valPtr hintVal =
        .construct Core.kciEnum "Opaque"
          [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repBoolField (d.safety == .unsaf)] := by
      simp [L1.defnValShape, hk]
    cases «KernelCheck::check_const».obs ev_chk with
    | Axiom_n1 | Axiom_other_n0 | Axiom_other_other | Defn | Thm
    | Quot
    | Induct_n0 | Induct_other_n0 | Induct_other_other
    | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
    | Rec_n0 | Rec_other =>
      simp_all [L1.defnValShape, Core.kciEnum]
    | Opaque v1 m2 cs12 x_nlvls x_ty x_val _ _ m849 cs859 _ m886 cs896 v922 m923 cs933 m954
        _ m967 cs977 _ m997 cs1007 cs1029 m1058
        ev14 _ _ _ hv825 ev861 ev898 hm962 ev935 ev979 ev1009 hm1066 ev1031 hc1070 =>
      obtain ⟨hv1, hm2⟩ := is_unsafe_ci_defnValShape_safe_c hsafe_decl ev14
      subst v1; subst m2
      rw [hv_shape] at hv825
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv825
      obtain ⟨hxn, hxt, hxv, -⟩ := hv825
      subst x_nlvls; subst x_ty; subst x_val
      have hs1 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c (by rwa [hc1070] at hsub_chk))
      have hcl_v1 := hs1 _ List.mem_cons_self
      have hs2 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs1)
      have hcl_v2 := hs2 _ List.mem_cons_self
      have hs3 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs2)
      have hcl_es := hs3 _ List.mem_cons_self
      have hsub_es : ∀ cl ∈ cs933, cl ∈ calls :=
        fun cl hm => (mem_sublist_of_cons_left_c hs3) cl (List.mem_append_left _ hm)
      have hs4 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs3)
      have hs5 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs4)
      have hs6 := mem_sublist_of_append_right_c (mem_sublist_of_cons_left_c hs5)
      have hcl_kc := hs6 _ List.mem_cons_self
      have hsub_kc := mem_sublist_of_cons_left_c hs6
      obtain ⟨cs_sr1, ev_sr1, hcs977⟩ := Assembly.assert_safety_zero_spec ev979
      obtain ⟨cs_sr2, ev_sr2, hcs1007⟩ := Assembly.assert_safety_zero_spec ev1009
      have ext_886_954 : Heap.Extends m886 m954 := by rw [hm962]; exact Heap.Extends.snoc _ _
      have ext_997_1058 : Heap.Extends m997 m1058 := by rw [hm1066]; exact Heap.Extends.snoc _ _
      have ext_m_954 : Heap.Extends m_chk m954 :=
        ev861.heap_extends.trans (ev898.heap_extends.trans ext_886_954)
      have ext_923_1058 : Heap.Extends m923 m1058 :=
        ev_sr1.heap_extends.trans (ev_sr2.heap_extends.trans ext_997_1058)
      have ext_954_1058 : Heap.Extends m954 m1058 := ev935.heap_extends.trans ext_923_1058
      have ext_m_1058 : Heap.Extends m_chk m1058 := ext_m_954.trans ext_954_1058
      have hty_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls hty_tmc_m hty_ann hty_def ev861
      have hval_out_def := Core.Scope.validatedAnnotation_positional
        hnlvls (Core.TmC.mono ev861.heap_extends hval_tmc_m) hval_ann hval_def ev898
      have hty_tmc_954 := Core.TmC.mono ext_m_954 hty_tmc_m
      have hval_tmc_1058 := Core.TmC.mono ext_m_1058 hval_tmc_m
      intro hn
      exact .opaqueDecl hdecl_not_role hnlvls hty_lbb hty_def hval_lbb hval_def hty_ann hval_ann
          hty_out_def hval_out_def
          hm962 hty_tmc_954 (hrc_m.mono ext_m_954) ev935 hcl_es hsub_es
          ext_923_1058 hm1066 (Core.TmC.mono ext_954_1058 hty_tmc_954) hval_tmc_1058
          (hrc_m.mono ext_m_1058) ev1031 hcl_kc hsub_kc

variable {E : Ixon.Env}

/-- **A checked standalone definition, theorem or opaque record stores its canonical
constant.** The walk checked `a` (`Claim.CheckedAtFull`), the run's store holds the record `c`
there, in Lean's logic, and the prefix `env` stores the references the record uses. Then there
are a group limit, the readings `ty₀`, `val₀` of its type and value, well scoped, and their
canonical annotations `ty'`, `val'` (`canonAnn`, at roots `0` and `1`) such that for every
hint:

* the declaration of the reading has its check evidence at the prefix's keying
  (`Decl.CheckedConstOriginAt`, what the walked-constant step consumes), and the declaration
  it stores is the declaration of the canonical annotations: it installs the canonical
  constant (`installs_defnDecl`, `canonDefn_eq`);
* the declaration of the reading installs the constant the record at `a` declares (`Reads`).

The constant the evidence stores is thus the one `reloadsAs_defn_cons` reloads. -/
theorem checkedAtFull_defn_canon (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) {bAddr a : _root_.Address} {order_role : List _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} (hrec : Ix.Cert.recordAt E a = some c)
    (hinfo : c.info = .defn d) (hlogic : InLogic c) (hnot_role : a ∉ order_role)
    (hchk : Claim.CheckedAtFull calls bAddr t a)
    {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env c) :
    ∃ (lim : Nat) (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.typ = .ok ty₀ ∧
      (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value = .ok val₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      val₀.looseBVarsBounded 0 = true ∧
      val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      canonAnn c (List.range d.lvls.toNat) 0 d.typ ty₀ = some ty' ∧
      canonAnn c (List.range d.lvls.toNat) (0 + 1) d.value val₀ = some val' ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedConstOriginAt (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ lim calls t bAddr
          E order_role
          (defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val' hn) ∧
        Reads t E a (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) := by
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hinfo] at hl
    exact hl
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, rfl⟩ := ha_pre
  obtain ⟨rawBytes, c', hh, hba, hex, hres⟩ := L1.get_ci_trace_spec ha'_ref ev_ld
  have hc : c = c' := (hS.record_eq hrec (Core.hashed_mono hsub_ld hh) hba hex).symm
  subst hc
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v', hhp, built, hld', htr⟩ := hres
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    defn_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht
      (hS.recordOf_of_recordAt hrec) hinfo hlogic hblob htr.toRaw
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    checkedDefn_core (E := E) (order_role := order_role) (decl_addr := Core.ixAddr a') ht
      hbound hnot_role hsafe hrc_m hblob raw' hty hval ev_chk hsub_chk
  have hrecur : L1.defnRecurAddrs d (Core.ixAddr a') = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnRecurAddrs, hf]
  rw [hrecur] at htr
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr
  subst hv
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon ht hnlvls hagree rty built hpT hlT hty h1 h2
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    annotation_canon ht hnlvls hagree rval built hpV hlV hval h3 h4
  have heT : ∀ i, i ∈ exprRefIdxs d.typ → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_left _ hi)
  have heV : ∀ i, i ∈ exprRefIdxs d.value → i ∈ usedRefIdxs c := by
    intro i hi
    unfold usedRefIdxs
    rw [hinfo]
    exact List.mem_append_right _ (List.mem_append_right _ hi)
  have htmT' := Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := some lim) rty heT hstored htmT
  have htmV' := Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := some lim) rval heV hstored htmV
  exact ⟨lim, ty₀, val₀, ty', val', hty, hval, h1, h2, h3, h4, hcT, hcV, fun hn =>
    ⟨checkedDefn_at (E := E) (order_role := order_role) (decl_addr := Core.ixAddr a')
      hnot_role hsafe hrc_m hnlvls h1 h2 h3 h4 hannT hannV htmT' htmV' ev_chk hsub_chk hn,
      hreads hn⟩⟩

/-- **A checked member of a definition block stores its canonical constant.** The store holds
the block `cb` at `B`, in Lean's logic; the walk checked member `k`, the definition `d`; the
prefix `env` stores the references the block uses. Then there are a group limit, the readings
`ty₀`, `val₀` of the member's type and value in the block, well scoped, and their canonical
annotations `ty'`, `val'` (at the member's root offset in the block and the next root) such
that for every hint the declaration of the reading has its check evidence at the prefix's
keying, storing the declaration of the canonical annotations, and installs the constant the
member's projection record declares (`Reads`). -/
theorem mutsMember_defn_canon (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) (hcov : HashedRecordsStored calls E) {bAddr B : _root_.Address}
    {order_role : List _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {k : Nat} {d : Ixon.Definition} (hrecB : Ix.Cert.recordAt E B = some cb)
    (hmuts : cb.info = .muts ms) (hk : ms[k]? = some (.defn d)) (hlogic : InLogic cb)
    (hnot_role : memberAddr B k (.defn d) ∉ order_role)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t B ms k)
    {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env cb) :
    ∃ (lim : Nat) (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read d.typ = .ok ty₀ ∧
      (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read d.value =
        .ok val₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      val₀.looseBVarsBounded 0 = true ∧
      val₀.allLevelParamsDefined (List.range d.lvls.toNat) = true ∧
      canonAnn cb (List.range d.lvls.toNat) ((L1.mutsRootOffset ms.toList k : Nat) : F) d.typ
        ty₀ = some ty' ∧
      canonAnn cb (List.range d.lvls.toNat) (((L1.mutsRootOffset ms.toList k : Nat) : F) + 1)
        d.value val₀ = some val' ∧
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedConstOriginAt (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ lim calls t bAddr
          E order_role
          (defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' hn) ∧
        Reads t E (memberAddr B k (.defn d))
          (defnConst d.kind
            ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn) := by
  obtain ⟨hk64, hchk, hrec⟩ := mutsMember_record hbound hS hcov hm hk
  have hmem' : Ixon.MutConst.defn d ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk)
  have hsafe : Ix.Kernel.Reader.safetyDecline d = none := by
    have hl := hlogic
    unfold InLogic at hl
    rw [hmuts] at hl
    exact hl (.defn d) hmem'
  obtain ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchk
  obtain ⟨a', ha'_ref, haddr⟩ := ha_pre
  obtain ⟨rawBytes, c', hh, hba, hex, hres⟩ := L1.get_ci_trace_spec ha'_ref ev_ld
  have hc : memberProjection B k (.defn d) = c' :=
    (hS.record_eq hrec (Core.hashed_mono hsub_ld hh) (hba.trans haddr) hex).symm
  subst hc
  have hinfo : (memberProjection B k (.defn d)).info = .dPrj ⟨k.toUInt64, B⟩ := rfl
  unfold L1.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', d', blobs, tree, v', hhB, haB, hexB, hcb, hms, hhp, built,
    hld', htr⟩ := hres
  have hcb_eq : cb = cb' :=
    (hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB).symm
  subst hcb_eq
  have hms_eq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hms_eq
  have hms' : ms[k.toUInt64.toNat]? = some (.defn d') := by
    rw [← Array.getElem?_toList]
    exact hms
  rw [toUInt64_toNat_cc hk64] at hms'
  have hd : d = d' := Ixon.MutConst.defn.inj (Option.some.inj (hk.symm.trans hms'))
  subst hd
  rw [hld] at hld'
  injection hld' with hvv
  subst hvv
  have htr' : L1.DefnTraceRep cb.refs.toList (L1.defnMemberRecurAddrs d B ms.toList)
      cb.univs.toList cb.sharing.toList blobs tree
      ((L1.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) m_chk d v := htr
  rw [toUInt64_toNat_cc hk64] at htr'
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨raw', ty₀, val₀, hty, hval, hreads, -⟩ :=
    dprj_reading (store := recordOf E) (blob := fun x => E.blobs.get? x) ht hk64
      (hS.recordOf_of_recordAt hrecB) hmuts hk hlogic (hS.recordOf_of_recordAt hrec) hblob
      htr'.toRaw
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    checkedDefn_core (E := E) (order_role := order_role)
      (decl_addr := memberAddr B k (.defn d)) ht hbound hnot_role hsafe hrc_m hblob raw' hty
      hval ev_chk hsub_chk
  have hrecur : L1.defnMemberRecurAddrs d B ms.toList = [] := by
    have hf := (L1.defnIsUnsafeCI_eq_false_iff d).mpr hsafe
    simp [L1.defnMemberRecurAddrs, hf]
  rw [hrecur] at htr'
  obtain ⟨hnlvls, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := htr'
  subst hv
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon ht hnlvls hagree rty built hpT hlT hty h1 h2
  obtain ⟨val', hcV, hannV, htmV⟩ :=
    annotation_canon ht hnlvls hagree rval built hpV hlV hval h3 h4
  have hused : ∀ i, i ∈ exprRefIdxs d.typ ++ exprRefIdxs d.value → i ∈ usedRefIdxs cb := by
    intro i hi
    unfold usedRefIdxs
    rw [hmuts]
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.defn d, hmem', hi⟩)
  have htmT' := Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := some lim) rty
    (fun i hi => hused i (List.mem_append_left _ hi)) hstored htmT
  have htmV' := Decl.tmC_stored_of_usedRefs (E₀ := E) (lim := some lim) rval
    (fun i hi => hused i (List.mem_append_right _ hi)) hstored htmV
  exact ⟨lim, ty₀, val₀, ty', val', hty, hval, h1, h2, h3, h4, hcT, hcV, fun hn =>
    ⟨checkedDefn_at (E := E) (order_role := order_role)
      (decl_addr := memberAddr B k (.defn d)) hnot_role hsafe hrc_m hnlvls h1 h2 h3 h4
      hannT hannV htmT' htmV' ev_chk hsub_chk hn, hreads hn⟩⟩

/-! ## The two inputs of a step, together -/

/-- **The inputs of the walked-constant step for a standalone definition, theorem or opaque
record, from the walk's check alone.** The walk checked `a`, the run's store `E` holds the
record `c` there, in Lean's logic, and the prefix `env` stores the references the record
uses. Then there are a group limit, readings `ty₀`, `val₀` and annotations `ty'`, `val'` such
that for every hint:

* the declaration of the reading has its check evidence at the prefix's keying, storing the
  declaration of the annotations (`hchk` of `Decl.walkedConst_step`);
* it installs the constant the record at `a` declares (`Reads`);
* every constant the stored declaration installs reloads under the prefix that stores it, at
  every store `E'` that holds the record `c` at `a` (exact decoding) and at least the blobs
  of `E` (the reload input of the step, in the form the step takes it).

Nothing else is assumed about `E'`: the runs a reload speaks of are only required to be good
for `E'`. -/
theorem checkedAtFull_defn_step (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) {bAddr a : _root_.Address} {order_role : List _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition} (hrec : Ix.Cert.recordAt E a = some c)
    (hinfo : c.info = .defn d) (hlogic : InLogic c) (hnot_role : a ∉ order_role)
    (hchk : Claim.CheckedAtFull calls bAddr t a)
    {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env c) :
    ∃ (lim : Nat) (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedConstOriginAt (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ lim calls t bAddr
          E order_role
          (defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val' hn) ∧
        Reads t E a (defnConst d.kind ⟨keyOf t a, List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
        ∀ E' : Ixon.Env, recordOf E' a = some c →
          (∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b) →
          ∀ cn ∈ IxVM.Consistency.installs
              (defnDecl d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val' hn),
            Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  obtain ⟨lim, ty₀, val₀, ty', val', hty, hval, h1, h2, h3, h4, hcT, hcV, hall⟩ :=
    checkedAtFull_defn_canon ht hbound hS hrec hinfo hlogic hnot_role hchk hstored
  refine ⟨lim, ty₀, val₀, ty', val', fun hn =>
    ⟨(hall hn).1, (hall hn).2, fun E' hrec' hblobs cn hcn => ?_⟩⟩
  rw [installs_defnDecl] at hcn
  have hcn' : cn = defnConst d.kind ⟨Core.keyOf t a, List.range d.lvls.toNat, ty'⟩ val' hn :=
    List.mem_singleton.mp hcn
  subst hcn'
  exact reloadsAs_defn_cons ht hrec' hinfo hlogic hblobs hty hval h1 h2 h3 h4 hstored
    (canonDefn_eq hcT hcV)

/-- **The inputs of the walked-constant step for a member of a definition block.** As
`checkedAtFull_defn_step`, for member `k` of the block `cb` at `B`: the reload holds at every
store `E'` that holds the member's projection record at its constant address, the block at
`B` (exact decodings) and at least the blobs of `E`. -/
theorem mutsMember_defn_step (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : RunStore calls E) (hcov : HashedRecordsStored calls E) {bAddr B : _root_.Address}
    {order_role : List _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {k : Nat} {d : Ixon.Definition} (hrecB : Ix.Cert.recordAt E B = some cb)
    (hmuts : cb.info = .muts ms) (hk : ms[k]? = some (.defn d)) (hlogic : InLogic cb)
    (hnot_role : memberAddr B k (.defn d) ∉ order_role)
    (hm : Claim.MutsMemberCheckedAtFull calls bAddr t B ms k)
    {env : Ix.Kernel.Env .anon} (hstored : Decl.UsedRefsStored t env cb) :
    ∃ (lim : Nat) (ty₀ val₀ ty' val' : Ix.Kernel.Expr .anon),
      ∀ hn : Ix.Kernel.ReducibilityHint,
        Decl.CheckedConstOriginAt (Core.Ctx.stored ⟨E, env, t, some lim⟩).κ lim calls t bAddr
          E order_role
          (defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn)
          (defnDecl d.kind
            ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' hn) ∧
        Reads t E (memberAddr B k (.defn d))
          (defnConst d.kind
            ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ hn) ∧
        ∀ E' : Ixon.Env,
          recordOf E' (memberAddr B k (.defn d)) = some (memberProjection B k (.defn d)) →
          recordOf E' B = some cb →
          (∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b) →
          ∀ cn ∈ IxVM.Consistency.installs
              (defnDecl d.kind
                ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
                hn),
            Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  obtain ⟨hk64, -, -⟩ := mutsMember_record hbound hS hcov hm hk
  obtain ⟨lim, ty₀, val₀, ty', val', hty, hval, h1, h2, h3, h4, hcT, hcV, hall⟩ :=
    mutsMember_defn_canon ht hbound hS hcov hrecB hmuts hk hlogic hnot_role hm hstored
  refine ⟨lim, ty₀, val₀, ty', val', fun hn =>
    ⟨(hall hn).1, (hall hn).2, fun E' hproj' hblock' hblobs cn hcn => ?_⟩⟩
  rw [installs_defnDecl] at hcn
  have hcn' : cn = defnConst d.kind
      ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' hn :=
    List.mem_singleton.mp hcn
  subst hcn'
  exact reloadsAs_member_cons ht hk64 hproj' hblock' hmuts hk hlogic hblobs hty hval h1 h2
    h3 h4 hstored (canonDefn_eq hcT hcV)

end Checked

end IxVM.Refinement.LoadedReads
