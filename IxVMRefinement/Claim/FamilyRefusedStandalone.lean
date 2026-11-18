import IxVMRefinement.L1.Decode
import IxVMRefinement.StatementRel.LoadedReads
import IxVMRefinement.Lib.Lists
import IxVMRefinement.Lib.Words
import IxVMRefinement.Obs.KernelModeled

/-! # A family check whose family record is a standalone recursor record fails

`KernelCheck::check_const` checks a recursor whose family block is modeled through
`KernelModeled::check_family(rc, family, rec_block)`, with `rec_block` the block field of the
loaded recursor. For a standalone recursor record (`Ixon.ConstantInfo.recr`) that field is the
record's own address: `Ingress::get_ci`'s `Recr` arm passes the address to
`Convert::convert_recursor` as the block. Such a family check never succeeds.
`KernelModeled::family_recs` answers the one-element list of the record (its `Recr` arm), so
the family check passes `n_recs = 1` to `KernelModeled::check_recs`, whose first iteration
asserts `nmot = n_recs` and `1 < nmot` ("a modeled recursor family with one motive"). This
holds of any standalone recursor record, one of a modeled family included: such a record is
refused by the family check.

* `check_recs_single_refused`: `check_recs` on a non-empty list with `n_recs = 1` fails.
* `check_family_standalone_refused`: a family check whose family record is a standalone
  recursor record of the run's store fails.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

/-- **`KernelModeled::check_recs` fails on a non-empty list with one recursor claimed**: its
first iteration asserts `nmot = n_recs` and `1 < nmot`. -/
theorem check_recs_single_refused
    {x_rc x_ta x_recs x_models x_src x_dst x_aset x_s x_k x_np x_uo x_bnl x_fam x_form
      r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {b : Bytes.Address}
    {bs : List Bytes.Address}
    (hrep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (b :: bs) x_recs)
    (ev : ObsFn Obs.W "KernelModeled::check_recs"
      [x_rc, x_ta, x_recs, x_models, x_src, x_dst, x_aset, x_s, .field 1, x_k, x_np, x_uo,
        x_bnl, x_fam, x_form] h r h' cs) : False := by
  match Obs.«KernelModeled::check_recs».obs ev with
  | .Nil (ld12 := ld12) .. => exact absurd (Lib.rep_nil_of_load hrep ld12) (by simp)
  | .Cons (heq273 := hmot) (ev298 := evlt) (heq320 := hlt) .. =>
    subst hmot hlt
    obtain ⟨-, -, hiff, -, -⟩ := Lib.less_than_fields_field evlt
    exact absurd (hiff.mp rfl) (lt_irrefl _)

/-- **A family check whose family record is a standalone recursor record of the run's store
fails** (module docstring): `family_recs` answers the record alone, and `check_recs` refuses a
family of one recursor. -/
theorem check_family_standalone_refused {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_b x_rb r : SourceValue F} {h h' : Heap F} {ab : Bytes.Address}
    (hrb : Bytes.RepAddressRef addrTy h ab x_rb)
    (ev : ObsFn Obs.W "KernelModeled::check_family" [x_rc, x_b, x_rb] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} {rcr : Ixon.Recursor}
    (hc : IxVM.Consistency.recordOf E₀ (ixAddr ab) = some c) (hinfo : c.info = .recr rcr) :
    False := by
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (m105 := m105) (m784 := m784) (m840 := m840) (m_pjcdckev := mR) (m1293 := m1293)
      (v839 := v839) (v861 := v861) (cs850 := cs850) (sg112 := sg112)
      (ev126 := ev126) (ev148 := ev148) (ev194 := ev194) (ev_yqjbwijz := evo) (ev231 := ev231)
      (ev266 := ev266) (ev309 := ev309) (ev344 := ev344) (ev403 := ev403) (ev435 := ev435)
      (ev465 := ev465) (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
      (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817) (ev796 := ev796)
      (ev852 := ev852) (ev_ursqbimm := evr) (ev874 := ev874) (ev896 := ev896) (ev960 := ev960)
      (ev939 := ev939) (ev1011 := ev1011) (ev990 := ev990) (ev_edyzsqzv := evm1)
      (ev_gkddqxhv := evcc) (ev_ittpynob := evm2) (ev_biaifgpd := evm3) (ev1203 := ev1203)
      (ev_cwwgzxtj := evfl) (ev1246 := ev1246) (ev_mitevvsv := evln) (ev_rqpeovbn := evz1)
      (ev_xrhmaojz := evz2) (ev_whimdwjd := evvg) (ev1305 := ev1305) (ev1343 := ev1343)
      (hc1474 := hc1474) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. =>
        rw [he33]
        exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have e784 : Heap.Extends h m784 := by
      refine e0.trans ?_
      refine ev126.heap_extends.trans ?_
      refine ev148.heap_extends.trans ?_
      refine ev194.heap_extends.trans ?_
      refine evo.heap_extends.trans ?_
      refine ev231.heap_extends.trans ?_
      refine ev266.heap_extends.trans ?_
      refine ev309.heap_extends.trans ?_
      refine ev344.heap_extends.trans ?_
      refine ev403.heap_extends.trans ?_
      refine ev435.heap_extends.trans ?_
      refine ev465.heap_extends.trans ?_
      refine ev513.heap_extends.trans ?_
      refine ev601.heap_extends.trans ?_
      refine ev634.heap_extends.trans ?_
      refine ev664.heap_extends.trans ?_
      refine ev686.heap_extends.trans ?_
      refine ev716.heap_extends.trans ?_
      refine ev759.heap_extends.trans ?_
      refine ev817.heap_extends.trans ?_
      exact ev796.heap_extends
    have hrb784 : Bytes.RepAddressRef addrTy m784 ab x_rb :=
      Bytes.repAddressRef_heapMono₂ addrTy e784 hrb
    -- `family_recs` answers the record alone: the record it loads is the stored recursor
    have hlist : RepList addrListEnum (Bytes.RepAddressRef addrTy) m840 [ab] v839 := by
      match Obs.«KernelModeled::family_recs».obs ev852 with
      | .Muts (cs12 := cs12) (ev14 := ev14) (hc165 := hcf) .. =>
        exfalso
        have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl =>
          hsub cl (by rw [hc1474]; simp [show cl ∈ cs850 by rw [hcf]; simp [hcl]])
        obtain ⟨-, bytes, c', -, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
          L1.load_verified_constant_decode_bounded hrb784 ev14
        have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
          (Core.hashed_mono hsub12 hh) haddr hexact
        subst hcc
        obtain ⟨infoVal, -, -, -, -, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
        have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
        rw [hinfo] at hinfoRep
        obtain ⟨rv, hv, -⟩ := hinfoRep
        exact absurd (Value.construct.inj (hinfo_eq.trans hv)).2.1 (by decide)
      | .Recr (m2 := m2) (m197 := m197) (ev14 := ev14) (he183 := he183) (hm182 := hm182)
          (hm205 := hm205) .. =>
        subst hm205
        subst he183
        subst hm182
        have hb' : Bytes.RepAddressRef addrTy
            (m2 ++ [.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Nil" []]) ab x_rb :=
          Bytes.repAddressRef_heapMono₂ addrTy
            (ev14.heap_extends.trans (Heap.Extends.snoc m2 _)) hrb784
        exact Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy) hb'
          (Lib.rep_store_nil m2)
    -- its length is one
    have eR : Heap.Extends m840 mR := evr.heap_extends
    have ev874' : ObsFn Obs.W (Instance.mk "Lists::length" [.ptr (.array .field 32)]).symbol
        [v839] mR v861 _ _ := by
      rw [Obs.Names.«Lists::length<&[Field; 32]>».symbol]; exact ev874
    have hlR : RepList (Instance.mk "Lists::Node" [.ptr (.array .field 32)]).symbol
        (Bytes.RepAddressRef addrTy) mR [ab] v839 := by
      rw [Obs.Names.«Lists::Node<&[Field; 32]>».symbol]
      exact RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) eR hlist
    obtain ⟨hv861, -⟩ := Lib.Lists.length_spec ev874' hlR
    have h1 : ((([ab] : List Bytes.Address).length : Nat) : F) = 1 := by simp
    rw [hv861, h1] at ev1343
    -- `check_recs` refuses a family of one recursor
    have e1293 : Heap.Extends m840 m1293 := by
      refine eR.trans ?_
      refine ev874.heap_extends.trans ?_
      refine ev896.heap_extends.trans ?_
      refine ev960.heap_extends.trans ?_
      refine ev939.heap_extends.trans ?_
      refine ev1011.heap_extends.trans ?_
      refine ev990.heap_extends.trans ?_
      refine evm1.heap_extends.trans ?_
      refine evcc.heap_extends.trans ?_
      refine evm2.heap_extends.trans ?_
      refine evm3.heap_extends.trans ?_
      refine ev1203.heap_extends.trans ?_
      refine evfl.heap_extends.trans ?_
      refine ev1246.heap_extends.trans ?_
      refine evln.heap_extends.trans ?_
      refine evz1.heap_extends.trans ?_
      refine evz2.heap_extends.trans ?_
      refine evvg.heap_extends.trans ?_
      exact ev1305.heap_extends
    exact check_recs_single_refused
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) e1293 hlist) ev1343

end IxVM.Refinement.Claim
