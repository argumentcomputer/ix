import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled5

/-! # Heap-chained call readings of `KernelModeled::check_family` and its callees

Structured, heap-chained readings of the generated paths of `KernelModeled::check_family`,
`members_val`, `member_val`, `family_refs_ok`, `assert_inner_refs_safe`, and `check_recs`.
Each sub-call carries its exact input and output heaps (`SubCall`), its membership in the
caller's call list, and linear-time call-list inclusion (`peel_call` / `peel_last`), so
downstream proofs chain `Heap.Extends` across every stage of the check without losing heap
equations or simplifying large call-list concatenations.

* `SubCall`, `CallSub`: one sub-call at explicit heaps `(h₁, h₂)`, with call-list membership
  and inclusion;
* `CheckFamilyChain`, `checkFamily_chain`: full heap chain of `check_family` from initial
  payload/witness/advice checks through table construction, `members_val` (types, ctors, recs),
  `family_refs_ok`, and `check_recs`;
* `MembersValCons`, `membersVal_step` and `MemberValChain`, `memberVal_chain`: element-wise
  member-to-model checks;
* `FamilyRefsOkChain`, `familyRefsOk_chain` and `AssertInnerRefsSafeChain`,
  `assertInnerRefsSafe_chain`: reference safety and non-block checks on the family record;
* `CheckRecsCons`, `checkRecs_step`: one recursor iteration of `check_recs`, including
  `peel_collect` (with constrained `Nil` accumulators), `spec_params_ptr_eq`,
  `rec_major_pins`, `lower_pins`, `k_ensure_sort`, `rec_to_parent_addr`, `get_ci` of parent,
  `check_recursor_canonical_at`, `check_rec_header_lets`, `check_rules` (sharing the exact
  `rp = (np + n) + nmin` value), and the recursive `check_recs` call with `k' = k + 1`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

set_option linter.unusedVariables false

/-! ## Heap-chained sub-calls and linear call-list peeling -/

/-- Inclusion of call lists: every call in `sub` belongs to `sup`. -/
abbrev CallSub (sub sup : List (Call F)) : Prop := ∀ cl ∈ sub, cl ∈ sup

/-- **A sub-call of `calls` at explicit heaps**: `f` at `args`, starting at `h₁` and returning
`v` at `h₂` with child calls `cs`, with both the call itself and all of `cs` in `calls`. -/
structure SubCall (calls : List (Call F)) (f : String) (args : List (SourceValue F))
    (h₁ : Heap F) (v : SourceValue F) (h₂ : Heap F) where
  cs : List (Call F)
  obs : ObsFn Obs.W f args h₁ v h₂ cs
  mem : (⟨f, args, h₁⟩ : Call F) ∈ calls
  sub : CallSub cs calls

theorem SubCall.extends {calls : List (Call F)} {f : String} {args : List (SourceValue F)}
    {h₁ h₂ : Heap F} {v : SourceValue F} (s : SubCall calls f args h₁ v h₂) :
    Heap.Extends h₁ h₂ :=
  s.obs.heap_extends

def SubCall.mono {calls₁ calls₂ : List (Call F)} {f : String} {args : List (SourceValue F)}
    {h₁ h₂ : Heap F} {v : SourceValue F} (hsub : CallSub calls₁ calls₂)
    (s : SubCall calls₁ f args h₁ v h₂) : SubCall calls₂ f args h₁ v h₂ :=
  ⟨s.cs, s.obs, hsub _ s.mem, fun cl hcl => hsub cl (s.sub cl hcl)⟩

private theorem callSub_refl (xs : List (Call F)) : CallSub xs xs := fun _ h => h

private theorem callSub_of_eq {xs calls : List (Call F)} (h : calls = xs) : CallSub xs calls := by
  subst h
  exact callSub_refl calls

private theorem callSub_append_left {xs ys sup : List (Call F)} (h : CallSub (xs ++ ys) sup) :
    CallSub xs sup :=
  fun cl hcl => h cl (List.mem_append_left ys hcl)

private theorem callSub_append_right {xs ys sup : List (Call F)} (h : CallSub (xs ++ ys) sup) :
    CallSub ys sup :=
  fun cl hcl => h cl (List.mem_append_right xs hcl)

private def peel_call {calls rest cs : List (Call F)} {f : String}
    {args : List (SourceValue F)} {h₁ h₂ : Heap F} {v : SourceValue F}
    (h : CallSub (⟨f, args, h₁⟩ :: (cs ++ rest)) calls)
    (ev : ObsFn Obs.W f args h₁ v h₂ cs) :
    SubCall calls f args h₁ v h₂ ×' CallSub rest calls :=
  ⟨⟨cs, ev, h _ List.mem_cons_self,
      fun cl hcl => h cl (List.mem_cons_of_mem _ (List.mem_append_left rest hcl))⟩,
   fun cl hcl => h cl (List.mem_cons_of_mem _ (List.mem_append_right cs hcl))⟩

private def peel_last {calls cs : List (Call F)} {f : String}
    {args : List (SourceValue F)} {h₁ h₂ : Heap F} {v : SourceValue F}
    (h : CallSub (⟨f, args, h₁⟩ :: cs) calls)
    (ev : ObsFn Obs.W f args h₁ v h₂ cs) :
    SubCall calls f args h₁ v h₂ :=
  ⟨cs, ev, h _ List.mem_cons_self, fun cl hcl => h cl (List.mem_cons_of_mem _ hcl)⟩

/-! ## `check_family` -/

/-- **Full heap-chained decomposition of an observed `KernelModeled::check_family` call.** -/
structure CheckFamilyChain (rc b rb : SourceValue F)
    (h_in h_out : Heap F) (calls : List (Call F)) where
  vSeg : SourceValue F
  m105 : Heap F
  cs107 : List (Call F)
  sg112 : Obs.«KernelModeled::check_family».Seg1 rc b rb h_in vSeg m105 cs107
  subSeg : CallSub cs107 calls
  -- Payload stream, order check, witnesses, advice
  payload : SourceValue F
  m114 : Heap F
  evReadPayload : SubCall calls "KernelModeled::read_payload" [b] m105 payload m114
  xRb : SourceValue F
  s1 : SourceValue F
  m136 : Heap F
  evGetRb : SubCall calls "IxonDeserialize::get_address" [payload] m114 (.tuple [xRb, s1]) m136
  m184 : Heap F
  evRbEq : SubCall calls "Bytes::address_eq" [xRb, rb] m136 (.field 1) m184
  vOrd : SourceValue F
  mOrd : Heap F
  evInOrder : SubCall calls "KernelRoles::assert_in_order" [rc, rb] m184 vOrd mOrd
  nAdv : SourceValue F
  s2 : SourceValue F
  m219 : Heap F
  evCountAdv : SubCall calls "KernelModeled::get_count" [s1] mOrd (.tuple [nAdv, s2]) m219
  advList : SourceValue F
  s3 : SourceValue F
  m254 : Heap F
  evGetAdv : SubCall calls "KernelModeled::get_addrs" [s2, nAdv] m219 (.tuple [advList, s3]) m254
  nWit : SourceValue F
  s4 : SourceValue F
  m297 : Heap F
  evCountWit : SubCall calls "KernelModeled::get_count" [s3] m254 (.tuple [nWit, s4]) m297
  outside : SourceValue F
  s5 : SourceValue F
  m332 : Heap F
  evCheckWit : SubCall calls "KernelModeled::check_witnesses" [rc, b, s4, nWit] m297
    (.tuple [outside, s5]) m332
  wset : SourceValue F
  m391 : Heap F
  evWset : SubCall calls "KernelClaim::addr_set_build"
    [outside, .construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []] m332 wset m391
  vCont : SourceValue F
  m423 : Heap F
  evContRefs : SubCall calls "KernelModeled::container_recs_refs" [rc, outside, wset] m391
    vCont m423
  aset : SourceValue F
  m453 : Heap F
  evCheckAdv : SubCall calls "KernelModeled::check_advice_records"
    [rc, advList, .construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [], wset] m423
    aset m453
  -- Block and family-record tables (`CallTables.family_tables` inputs)
  members : SourceValue F
  wSh : SourceValue F
  wRf : SourceValue F
  wUn : SourceValue F
  wBd : SourceValue F
  m501 : Heap F
  evLoadBlk : SubCall calls "Ingress::load_verified_constant" [b] m453
    (.construct "Ixon::Constant" "Mk"
      [.construct "Ixon::ConstantInfo" "Muts" [members], wSh, wRf, wUn, wBd]) m501
  nInd : SourceValue F
  m589 : Heap F
  evLenMem : SubCall calls Obs.Names.«Lists::length<Ixon::MutConst>» [members] m501 nInd m589
  m624 : Heap F
  evIndcCnt : SubCall calls "KernelModeled::muts_indc_count" [members] m589 nInd m624
  np : SourceValue F
  m652 : Heap F
  evNParams : SubCall calls "KernelModeled::block_nparams" [members] m624 np m652
  tys : SourceValue F
  m674 : Heap F
  evTypes : SubCall calls "Ingress::build_recur_addrs" [members, b] m652 tys m674
  tyM : SourceValue F
  s6 : SourceValue F
  m704 : Heap F
  evTypeMods : SubCall calls "KernelModeled::get_addrs" [s5, nInd] m674 (.tuple [tyM, s6]) m704
  ctors : SourceValue F
  m747 : Heap F
  evCtors : SubCall calls "KernelModeled::block_ctor_addrs" [members, b, .field 0] m704 ctors m747
  nCtors : SourceValue F
  m807 : Heap F
  evLenCtors : SubCall calls Obs.Names.«Lists::length<&[Field; 32]>» [ctors] m747 nCtors m807
  ctorM : SourceValue F
  s7 : SourceValue F
  m784 : Heap F
  evCtorMods : SubCall calls "KernelModeled::get_addrs" [s6, nCtors] m807 (.tuple [ctorM, s7]) m784
  recs : SourceValue F
  m840 : Heap F
  evRecs : SubCall calls "KernelModeled::family_recs" [rb] m784 recs m840
  vNoRole : SourceValue F
  mNoRole : Heap F
  evNoRole : SubCall calls "KernelModeled::assert_no_role" [rc, recs] m840 vNoRole mNoRole
  nRecs : SourceValue F
  m862 : Heap F
  evLenRecs : SubCall calls Obs.Names.«Lists::length<&[Field; 32]>» [recs] mNoRole nRecs m862
  recM : SourceValue F
  s8 : SourceValue F
  m884 : Heap F
  evRecMods : SubCall calls "KernelModeled::get_addrs" [s7, nRecs] m862 (.tuple [recM, s8]) m884
  ctorRec : SourceValue F
  m950 : Heap F
  evSrcTail : SubCall calls Obs.Names.«Lists::concat<&[Field; 32]>» [ctors, recs] m884 ctorRec m950
  src : SourceValue F
  m927 : Heap F
  evSrc : SubCall calls Obs.Names.«Lists::concat<&[Field; 32]>» [tys, ctorRec] m950 src m927
  ctorRecM : SourceValue F
  m1001 : Heap F
  evDstTail : SubCall calls Obs.Names.«Lists::concat<&[Field; 32]>» [ctorM, recM] m927
    ctorRecM m1001
  dst : SourceValue F
  m978 : Heap F
  evDst : SubCall calls Obs.Names.«Lists::concat<&[Field; 32]>» [tyM, ctorRecM] m1001 dst m978
  -- Member checks (`members_val`)
  vTysVal : SourceValue F
  mTysVal : Heap F
  evTysVal : SubCall calls "KernelModeled::members_val" [tys, tyM, src, dst, aset, src] m978
    vTysVal mTysVal
  later : SourceValue F
  mLater : Heap F
  evLater : SubCall calls Obs.Names.«Lists::concat<&[Field; 32]>» [ctors, recs] mTysVal
    later mLater
  vCtorsVal : SourceValue F
  mCtorsVal : Heap F
  evCtorsVal : SubCall calls "KernelModeled::members_val" [ctors, ctorM, src, dst, aset, later]
    mLater vCtorsVal mCtorsVal
  vRecsVal : SourceValue F
  mRecsVal : Heap F
  evRecsVal : SubCall calls "KernelModeled::members_val" [recs, recM, src, dst, aset, recs]
    mCtorsVal vRecsVal mRecsVal
  -- Elimination level / flat block checks, reference checks, recursor loop
  bnl : SourceValue F
  uo : SourceValue F
  m1191 : Heap F
  evBlockElim : SubCall calls "KernelModeled::block_elim" [rc, tys] mRecsVal
    (.tuple [bnl, uo]) m1191
  mRefs : Heap F
  extAfterElim : Heap.Extends m1191 mRefs
  vRefs : SourceValue F
  m1293 : Heap F
  evRefsOk : SubCall calls "KernelModeled::family_refs_ok" [rc, rb, b, wset] mRefs vRefs m1293
  s9 : SourceValue F
  evCheckRecs : SubCall calls "KernelModeled::check_recs"
    [rc, tys, recs, recM, src, dst, aset, s8, nRecs, .field 0, np, uo, bnl, recs, .field 0]
    m1293 s9 h_out
  ldS9Nil : loadValue h_out s9 = .ok (.construct Obs.Names.«Lists::Node<Field>» "Nil" [])

theorem CheckFamilyChain.ext_m105_m453 {rc b rb : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)} (C : CheckFamilyChain rc b rb h h' calls) :
    Heap.Extends C.m105 C.m453 :=
  C.evReadPayload.extends.trans (C.evGetRb.extends.trans (C.evRbEq.extends.trans
    (C.evInOrder.extends.trans (C.evCountAdv.extends.trans (C.evGetAdv.extends.trans
      (C.evCountWit.extends.trans (C.evCheckWit.extends.trans (C.evWset.extends.trans
        (C.evContRefs.extends.trans C.evCheckAdv.extends)))))))))

theorem CheckFamilyChain.ext_m453_m978 {rc b rb : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)} (C : CheckFamilyChain rc b rb h h' calls) :
    Heap.Extends C.m453 C.m978 :=
  C.evLoadBlk.extends.trans (C.evLenMem.extends.trans (C.evIndcCnt.extends.trans
    (C.evNParams.extends.trans (C.evTypes.extends.trans (C.evTypeMods.extends.trans
      (C.evCtors.extends.trans (C.evLenCtors.extends.trans (C.evCtorMods.extends.trans
        (C.evRecs.extends.trans (C.evNoRole.extends.trans (C.evLenRecs.extends.trans
          (C.evRecMods.extends.trans (C.evSrcTail.extends.trans (C.evSrc.extends.trans
            (C.evDstTail.extends.trans C.evDst.extends)))))))))))))))

theorem CheckFamilyChain.ext_m978_m1293 {rc b rb : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)} (C : CheckFamilyChain rc b rb h h' calls) :
    Heap.Extends C.m978 C.m1293 :=
  C.evTysVal.extends.trans (C.evLater.extends.trans (C.evCtorsVal.extends.trans
    (C.evRecsVal.extends.trans (C.evBlockElim.extends.trans
      (C.extAfterElim.trans C.evRefsOk.extends)))))

/-- **Heap-chained reading of an observed `KernelModeled::check_family` call.** -/
theorem checkFamily_chain {rc b rb r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_family" [rc, b, rb] h r h' calls) :
    Nonempty (CheckFamilyChain rc b rb h h' calls) := by
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (sg112 := sg) (ev126 := e126) (ev148 := e148) (ev194 := e194) (heq217 := q217)
      (ev_yqjbwijz := eOrd) (ev231 := e231) (ev266 := e266) (ev309 := e309) (ev344 := e344)
      (ev403 := e403) (ev435 := e435) (ev465 := e465) (ev513 := e513) (ev601 := e601)
      (ev634 := e634) (heq650 := q650) (ev664 := e664) (ev686 := e686) (ev716 := e716)
      (ev759 := e759) (ev817 := e817) (ev796 := e796) (ev852 := e852) (ev_ursqbimm := eNoRole)
      (ev874 := e874) (ev896 := e896) (ev960 := e960) (ev939 := e939) (ev1011 := e1011)
      (ev990 := e990) (ev_edyzsqzv := eTysV) (ev_gkddqxhv := eLater) (ev_ittpynob := eCtorsV)
      (ev_biaifgpd := eRecsV) (ev1203 := eElim) (ev_cwwgzxtj := eFlat) (ev1246 := eNest)
      (ev_mitevvsv := eLenF) (ev_rqpeovbn := eZ1) (ev_xrhmaojz := eZ2) (ev_whimdwjd := eValG)
      (ev1305 := eRefs) (ev1343 := eChk) (ld1465 := lS9) (he1473 := hEqH) (hc1474 := hc) .. =>
    subst q217 q650 hEqH
    have h0 := callSub_of_eq hc
    have hSubSeg := callSub_append_left h0
    have hr := callSub_append_right h0
    let ⟨s126, hr⟩ := peel_call hr e126
    let ⟨s148, hr⟩ := peel_call hr e148
    let ⟨s194, hr⟩ := peel_call hr e194
    let ⟨sOrd, hr⟩ := peel_call hr eOrd
    let ⟨s231, hr⟩ := peel_call hr e231
    let ⟨s266, hr⟩ := peel_call hr e266
    let ⟨s309, hr⟩ := peel_call hr e309
    let ⟨s344, hr⟩ := peel_call hr e344
    let ⟨s403, hr⟩ := peel_call hr e403
    let ⟨s435, hr⟩ := peel_call hr e435
    let ⟨s465, hr⟩ := peel_call hr e465
    let ⟨s513, hr⟩ := peel_call hr e513
    let ⟨s601, hr⟩ := peel_call hr e601
    let ⟨s634, hr⟩ := peel_call hr e634
    let ⟨s664, hr⟩ := peel_call hr e664
    let ⟨s686, hr⟩ := peel_call hr e686
    let ⟨s716, hr⟩ := peel_call hr e716
    let ⟨s759, hr⟩ := peel_call hr e759
    let ⟨s817, hr⟩ := peel_call hr e817
    let ⟨s796, hr⟩ := peel_call hr e796
    let ⟨s852, hr⟩ := peel_call hr e852
    let ⟨sNoRole, hr⟩ := peel_call hr eNoRole
    let ⟨s874, hr⟩ := peel_call hr e874
    let ⟨s896, hr⟩ := peel_call hr e896
    let ⟨s960, hr⟩ := peel_call hr e960
    let ⟨s939, hr⟩ := peel_call hr e939
    let ⟨s1011, hr⟩ := peel_call hr e1011
    let ⟨s990, hr⟩ := peel_call hr e990
    let ⟨sTysV, hr⟩ := peel_call hr eTysV
    let ⟨sLater, hr⟩ := peel_call hr eLater
    let ⟨sCtorsV, hr⟩ := peel_call hr eCtorsV
    let ⟨sRecsV, hr⟩ := peel_call hr eRecsV
    let ⟨sElim, hr⟩ := peel_call hr eElim
    let ⟨sFlat, hr⟩ := peel_call hr eFlat
    let ⟨sNest, hr⟩ := peel_call hr eNest
    let ⟨sLenF, hr⟩ := peel_call hr eLenF
    let ⟨sZ1, hr⟩ := peel_call hr eZ1
    let ⟨sZ2, hr⟩ := peel_call hr eZ2
    let ⟨sValG, hr⟩ := peel_call hr eValG
    let ⟨sRefs, hr⟩ := peel_call hr eRefs
    let sChk := peel_last hr eChk
    exact
      ⟨{ vSeg := _, m105 := _, cs107 := _, sg112 := sg
         subSeg := hSubSeg
         payload := _, m114 := _, evReadPayload := s126
         xRb := _, s1 := _, m136 := _, evGetRb := s148
         m184 := _, evRbEq := s194
         vOrd := _, mOrd := _, evInOrder := sOrd
         nAdv := _, s2 := _, m219 := _, evCountAdv := s231
         advList := _, s3 := _, m254 := _, evGetAdv := s266
         nWit := _, s4 := _, m297 := _, evCountWit := s309
         outside := _, s5 := _, m332 := _, evCheckWit := s344
         wset := _, m391 := _, evWset := s403
         vCont := _, m423 := _, evContRefs := s435
         aset := _, m453 := _, evCheckAdv := s465
         members := _, wSh := _, wRf := _, wUn := _, wBd := _, m501 := _, evLoadBlk := s513
         nInd := _, m589 := _, evLenMem := s601
         m624 := _, evIndcCnt := s634
         np := _, m652 := _, evNParams := s664
         tys := _, m674 := _, evTypes := s686
         tyM := _, s6 := _, m704 := _, evTypeMods := s716
         ctors := _, m747 := _, evCtors := s759
         nCtors := _, m807 := _, evLenCtors := s817
         ctorM := _, s7 := _, m784 := _, evCtorMods := s796
         recs := _, m840 := _, evRecs := s852
         vNoRole := _, mNoRole := _, evNoRole := sNoRole
         nRecs := _, m862 := _, evLenRecs := s874
         recM := _, s8 := _, m884 := _, evRecMods := s896
         ctorRec := _, m950 := _, evSrcTail := s960
         src := _, m927 := _, evSrc := s939
         ctorRecM := _, m1001 := _, evDstTail := s1011
         dst := _, m978 := _, evDst := s990
         vTysVal := _, mTysVal := _, evTysVal := sTysV
         later := _, mLater := _, evLater := sLater
         vCtorsVal := _, mCtorsVal := _, evCtorsVal := sCtorsV
         vRecsVal := _, mRecsVal := _, evRecsVal := sRecsV
         bnl := _, uo := _, m1191 := _, evBlockElim := sElim
         mRefs := _, extAfterElim := sFlat.extends.trans (sNest.extends.trans (sLenF.extends.trans
           (sZ1.extends.trans (sZ2.extends.trans sValG.extends))))
         vRefs := _, m1293 := _, evRefsOk := sRefs
         s9 := _, evCheckRecs := sChk
         ldS9Nil := lS9 }⟩

/-! ## `members_val` and `member_val` -/

/-- **One `Cons` step of `KernelModeled::members_val`, heap-chained.** -/
structure MembersValCons (members models src dst aset later r : SourceValue F)
    (h h' : Heap F) (calls : List (Call F)) where
  xM : SourceValue F
  xRest : SourceValue F
  xMd : SourceValue F
  xMrest : SourceValue F
  vM : SourceValue F
  mMid : Heap F
  ldMembers : loadValue h members =
    .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [xM, xRest])
  ldModels : loadValue h models =
    .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [xMd, xMrest])
  evMember : SubCall calls "KernelModeled::member_val" [xM, xMd, src, dst, aset, later] h vM mMid
  evRest : SubCall calls "KernelModeled::members_val" [xRest, xMrest, src, dst, aset, later]
    mMid r h'

/-- **Heap-chained step of `KernelModeled::members_val`.** -/
theorem membersVal_step {members models src dst aset later r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::members_val" [members, models, src, dst, aset, later]
      h r h' calls) :
    (loadValue h members = .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Nil" []) ∧
      h' = h) ∨
    Nonempty (MembersValCons members models src dst aset later r h h' calls) := by
  match Obs.«KernelModeled::members_val».obs ev with
  | .Nil (ld12 := l12) (he23 := hEq) .. => exact Or.inl ⟨l12, hEq⟩
  | .Cons (ld12 := l12) (ld52 := l52) (ev80 := e80) (ev126 := e126) (hc167 := hc) .. =>
    have h0 := callSub_of_eq hc
    let ⟨sM, hr⟩ := peel_call h0 e80
    let sRest := peel_last hr e126
    exact Or.inr ⟨⟨_, _, _, _, _, _, l12, l52, sM, sRest⟩⟩

/-- **Full heap-chained decomposition of `KernelModeled::member_val`.** -/
structure MemberValChain (m md src dst aset later : SourceValue F) (h h' : Heap F)
    (calls : List (Call F)) where
  m15 : Heap F
  evInAset : SubCall calls "KernelClaim::addr_set_member" [md, aset] h (.field 1) m15
  p : SourceValue F
  ci : SourceValue F
  m65 : Heap F
  evGetM : SubCall calls "Ingress::get_ci" [m] m15 p m65
  ldM : loadValue m65 p = .ok ci
  nl : SourceValue F
  ty : SourceValue F
  m50 : Heap F
  evLvlsTy : SubCall calls "KernelModeled::ci_lvls_type" [ci] m65 (.tuple [nl, ty]) m50
  mMent : Heap F
  evNoMent : SubCall calls "KernelModeled::expr_mentions_addrs" [ty, later] m50 (.field 0) mMent
  pm : SourceValue F
  mty : SourceValue F
  w1 : SourceValue F
  w2 : SourceValue F
  w3 : SourceValue F
  m101 : Heap F
  evGetMd : SubCall calls "Ingress::get_ci" [md] mMent pm m101
  ldMd : loadValue m101 pm =
    .ok (.construct "KernelTypes::KConstantInfo" "Defn" [nl, mty, w1, w2, w3])
  ren : SourceValue F
  m216 : Heap F
  evRen : SubCall calls "KernelModeled::rename" [ty, src, dst] m101 ren m216
  evEq : SubCall calls "KernelCheck::kexpr_struct_eq" [ren, mty] m216 (.field 1) h'

/-- **Heap-chained reading of an observed `KernelModeled::member_val` call.** -/
theorem memberVal_chain {m md src dst aset later r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::member_val" [m, md, src, dst, aset, later] h r h' calls) :
    Nonempty (MemberValChain m md src dst aset later h h' calls) := by
  match Obs.«KernelModeled::member_val».obs ev with
  | .run (ev25 := e25) (heq48 := q48) (ev78 := e78) (ld72 := l72) (ev62 := e62)
      (ev_nczzuuzf := eMent) (heq_pbkckosz := qMent) (ev117 := e117) (ld111 := l111)
      (heq187 := qNl) (ev226 := e226) (ev212 := e212) (heq264 := q264) (he268 := hEq)
      (hc269 := hc) .. =>
    subst q48 qMent qNl q264 hEq
    have h0 := callSub_of_eq hc
    let ⟨s25, hr⟩ := peel_call h0 e25
    let ⟨s78, hr⟩ := peel_call hr e78
    let ⟨s62, hr⟩ := peel_call hr e62
    let ⟨sMent, hr⟩ := peel_call hr eMent
    let ⟨s117, hr⟩ := peel_call hr e117
    let ⟨s226, hr⟩ := peel_call hr e226
    let s212 := peel_last hr e212
    exact
      ⟨{ m15 := _, evInAset := s25
         p := _, ci := _, m65 := _, evGetM := s78
         ldM := l72
         nl := _, ty := _, m50 := _, evLvlsTy := s62
         mMent := _, evNoMent := sMent
         pm := _, mty := _, w1 := _, w2 := _, w3 := _, m101 := _, evGetMd := s117
         ldMd := l111
         ren := _, m216 := _, evRen := s226
         evEq := s212 }⟩

/-! ## `family_refs_ok` and `assert_inner_refs_safe` -/

/-- **Heap-chained decomposition of `KernelModeled::family_refs_ok`.** -/
structure FamilyRefsOkChain (rc rb b wset r : SourceValue F) (h h' : Heap F)
    (calls : List (Call F)) where
  w1 : SourceValue F
  w2 : SourceValue F
  refs : SourceValue F
  w3 : SourceValue F
  w4 : SourceValue F
  m2 : Heap F
  evLoadRb : SubCall calls "Ingress::load_verified_constant" [rb] h
    (.construct "Ixon::Constant" "Mk" [w1, w2, refs, w3, w4]) m2
  mGo : Heap F
  extToIdxs : Heap.Extends m2 mGo
  used : SourceValue F
  mIdxs : Heap F
  evIdxs : SubCall calls "KernelClaim::const_idxs_of"
    [.construct "Ixon::Constant" "Mk" [w1, w2, refs, w3, w4]] mGo used mIdxs
  evInner : SubCall calls "KernelModeled::assert_inner_refs_safe" [rc, refs, used] mIdxs r h'

/-- **Heap-chained reading of an observed `KernelModeled::family_refs_ok` call.** -/
theorem familyRefsOk_chain {rc rb b wset r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::family_refs_ok" [rc, rb, b, wset] h r h' calls) :
    Nonempty (FamilyRefsOkChain rc rb b wset r h h' calls) := by
  match Obs.«KernelModeled::family_refs_ok».obs ev with
  | .run (ev14 := e14) (ev36 := e36) (ev_ycrqbsja := eI1) (ev_nhomjxfq := eI2)
      (ev_kfwmaaqi := eGo) (ev_ozxzdina := eIdx) (ev_tnqzszcy := eIn) (hc222 := hc) .. =>
    have h0 := callSub_of_eq hc
    let ⟨s14, hr⟩ := peel_call h0 e14
    let ⟨s36, hr⟩ := peel_call hr e36
    let ⟨sI1, hr⟩ := peel_call hr eI1
    let ⟨sI2, hr⟩ := peel_call hr eI2
    let ⟨sGo, hr⟩ := peel_call hr eGo
    let ⟨sIdx, hr⟩ := peel_call hr eIdx
    let sIn := peel_last hr eIn
    exact
      ⟨{ w1 := _, w2 := _, refs := _, w3 := _, w4 := _, m2 := _, evLoadRb := s14
         mGo := _, extToIdxs := s36.extends.trans (sI1.extends.trans (sI2.extends.trans sGo.extends))
         used := _, mIdxs := _, evIdxs := sIdx
         evInner := sIn }⟩

/-- **Heap-chained decomposition of `KernelModeled::assert_inner_refs_safe`.** -/
structure AssertInnerRefsSafeChain (rc refs used r : SourceValue F) (h h' : Heap F)
    (calls : List (Call F)) where
  vSafe : SourceValue F
  mSafe : Heap F
  evSafe : SubCall calls "KernelClaim::assert_safe_used_refs"
    [rc, refs, used, .field 0, .construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []]
    h vSafe mSafe
  vNotBlk : SourceValue F
  mNotBlk : Heap F
  evNotBlk : SubCall calls "KernelModeled::assert_used_not_block" [refs, used, .field 0]
    mSafe vNotBlk mNotBlk
  evInOrd : SubCall calls "KernelModeled::assert_used_in_order" [rc, refs, used, .field 0]
    mNotBlk r h'

/-- **Heap-chained reading of an observed `KernelModeled::assert_inner_refs_safe` call.** -/
theorem assertInnerRefsSafe_chain {rc refs used r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::assert_inner_refs_safe" [rc, refs, used] h r h' calls) :
    Nonempty (AssertInnerRefsSafeChain rc refs used r h h' calls) := by
  match Obs.«KernelModeled::assert_inner_refs_safe».obs ev with
  | .run (ev_mxwoukvn := eS) (ev_hemnmxwe := eB) (ev_xsejfvgw := eO) (hc_sgljalbe := hc) .. =>
    have h0 := callSub_of_eq hc
    let ⟨sS, hr⟩ := peel_call h0 eS
    let ⟨sB, hr⟩ := peel_call hr eB
    let sO := peel_last hr eO
    exact ⟨⟨_, _, sS, _, _, sB, sO⟩⟩

/-! ## `check_recs` -/

/-- **One `Cons` iteration of `KernelModeled::check_recs`, fully heap-chained.** -/
structure CheckRecsCons (rc tys recs models src dst aset s n k np uo bnl fam form r :
    SourceValue F) (h h' : Heap F) (calls : List (Call F)) where
  x : SourceValue F
  rest : SourceValue F
  rm : SourceValue F
  mrest : SourceValue F
  ldRecs : loadValue h recs =
    .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [x, rest])
  ldModels : loadValue h models =
    .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [rm, mrest])
  p : SourceValue F
  m67 : Heap F
  evGetRec : SubCall calls "Ingress::get_ci" [x] h p m67
  nl : SourceValue F
  ty : SourceValue F
  ni : SourceValue F
  nmin : SourceValue F
  rules : SourceValue F
  blk : SourceValue F
  idx : SourceValue F
  ldRec : loadValue m67 p = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
    [nl, ty, np, ni, n, nmin, rules, .field 0, .field 0, blk, idx])
  m473 : Heap F
  ext473 : Heap.Extends m67 m473
  vScope : SourceValue F
  m511 : Heap F
  evScope : SubCall calls "KernelCheck::validate_expr_well_scoped" [ty, .field 0, nl]
    m473 vScope m511
  m561 : Heap F
  evNoMent : SubCall calls "KernelModeled::expr_mentions_addrs" [ty, fam] m511 (.field 0) m561
  mNil1 : Heap F
  hNil1 : mNil1 = m561 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]
  wPeel1 : SourceValue F
  pd : SourceValue F
  mP1 : Heap F
  evPeel1 : SubCall calls "KernelModeled::peel_collect"
    [ty, np, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m561.length]
    mNil1 (.tuple [wPeel1, pd]) mP1
  ren : SourceValue F
  mRen : Heap F
  evRen : SubCall calls "KernelModeled::rename" [ty, src, dst] mP1 ren mRen
  mNil2 : Heap F
  hNil2 : mNil2 = mRen ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]
  wPeel2 : SourceValue F
  pdm : SourceValue F
  mP2 : Heap F
  evPeel2 : SubCall calls "KernelModeled::peel_collect"
    [ren, np, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») mRen.length]
    mNil2 (.tuple [wPeel2, pdm]) mP2
  mEq : Heap F
  evParamEq : SubCall calls "KernelCheck::spec_params_ptr_eq" [pd, pdm] mP2 (.field 1) mEq
  xNpN : SourceValue F
  rp : SourceValue F
  opNpN : evalBinOp .add np n = .ok xNpN
  opRp : evalBinOp .add xNpN nmin = .ok rp
  wP1 : SourceValue F
  wP2 : SourceValue F
  pins : SourceValue F
  mPins : Heap F
  evPins : SubCall calls "KernelModeled::rec_major_pins" [ty, rp, ni] mEq
    (.tuple [wP1, wP2, pins]) mPins
  nmotNmin : SourceValue F
  opNmotNmin : evalBinOp .add n nmin = .ok nmotNmin
  vLower : SourceValue F
  mLP : Heap F
  evLowerPins : SubCall calls "KernelModeled::lower_pins" [pins, nmotNmin] mPins vLower mLP
  mNilSort : Heap F
  hNilSort : mNilSort =
    mLP ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]
  vSort : SourceValue F
  m596 : Heap F
  evSort : SubCall calls "KernelInfer::k_ensure_sort"
    [rc, ty, .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») mLP.length]
    mNilSort vSort m596
  m669 : Heap F
  ext669 : Heap.Extends m596 m669
  parAddr : SourceValue F
  m698 : Heap F
  evParent : SubCall calls "KernelCheck::rec_to_parent_addr" [ty, np, n, nmin, ni] m669
    parAddr m698
  parPtr : SourceValue F
  parCi : SourceValue F
  mPar : Heap F
  evGetParent : SubCall calls "Ingress::get_ci" [parAddr] m698 parPtr mPar
  ldParent : loadValue mPar parPtr = .ok parCi
  form' : SourceValue F
  mCan : Heap F
  evCanon : SubCall calls "KernelCheck::check_recursor_canonical_at"
    [rc, .construct "KernelTypes::KConstantInfo" "Rec"
      [nl, ty, np, ni, n, nmin, rules, .field 0, .field 0, blk, idx],
      x, parCi, parAddr, uo, bnl, form] mPar form' mCan
  vHL : SourceValue F
  m838 : Heap F
  evHeaderLets : SubCall calls "KernelCheck::check_rec_header_lets" [ty, np, n, nmin, ni]
    mCan vHL m838
  s' : SourceValue F
  m892 : Heap F
  evRules : SubCall calls "KernelModeled::check_rules"
    [rc, rm, nl, ty, rp, ni, rules, src, dst, aset, s] m838 s' m892
  k' : SourceValue F
  opKNext : evalBinOp .add k (.field 1) = .ok k'
  evNext : SubCall calls "KernelModeled::check_recs"
    [rc, tys, rest, mrest, src, dst, aset, s', n, k', np, uo, bnl, fam, form'] m892 r h'

theorem CheckRecsCons.ext_h_m838
    {rc tys recs models src dst aset s n k np uo bnl fam form r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (C : CheckRecsCons rc tys recs models src dst aset s n k np uo bnl fam form r h h' calls) :
    Heap.Extends h C.m838 := by
  have e1 : Heap.Extends C.m561 C.mNil1 := by rw [C.hNil1]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends C.mRen C.mNil2 := by rw [C.hNil2]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends C.mLP C.mNilSort := by rw [C.hNilSort]; exact Heap.Extends.snoc _ _
  exact C.evGetRec.extends.trans (C.ext473.trans (C.evScope.extends.trans (C.evNoMent.extends.trans
    (e1.trans (C.evPeel1.extends.trans (C.evRen.extends.trans (e2.trans (C.evPeel2.extends.trans
      (C.evParamEq.extends.trans (C.evPins.extends.trans (C.evLowerPins.extends.trans
        (e3.trans (C.evSort.extends.trans (C.ext669.trans (C.evParent.extends.trans
          (C.evGetParent.extends.trans (C.evCanon.extends.trans
            C.evHeaderLets.extends)))))))))))))))))

/-- **Heap-chained step of `KernelModeled::check_recs`.** -/
theorem checkRecs_step {rc tys recs models src dst aset s n k np uo bnl fam form r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::check_recs"
      [rc, tys, recs, models, src, dst, aset, s, n, k, np, uo, bnl, fam, form] h r h' calls) :
    (loadValue h recs = .ok (.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Nil" []) ∧
      r = s ∧ h' = h) ∨
    Nonempty (CheckRecsCons rc tys recs models src dst aset s n k np uo bnl fam form r h h' calls) := by
  match Obs.«KernelModeled::check_recs».obs ev with
  | .Nil (ld12 := l12) (he21 := hR) (he22 := hH) .. => exact Or.inl ⟨l12, hR, hH⟩
  | .Cons (x_yytxvchu := xNpN) (v_czbmphqy := xRp) (x950 := xNpN2) (v909 := xRp2)
      (ld12 := l12) (ld51 := l51) (ev82 := e82) (ld76 := l76) (heq190 := qk)
      (heq217 := qu) (heq245 := qnp) (heq273 := qnmot) (ev298 := e298) (ev359 := e359)
      (ev345 := e345) (ev403 := e403) (ev485 := e485) (ev523 := e523) (ev571 := e571)
      (heq594 := qM) (hm_odcsfbbr := hNil1) (ev_uprevpxl := eP1) (ev_svgicqcr := eRen)
      (hm_owdmgqhw := hNil2) (ev_oqkxxxxs := eP2) (ev_eejlfykm := eEq) (heq_wxopjlsu := qEq)
      (op_eindxttr := opA) (op_smkbhtsz := opB) (ev_uoyvrvop := ePins) (op_dynlujbu := opC)
      (ev_akrqpecc := eLP) (hm635 := hNilS) (ev608 := eSort) (ev652 := eSaf1) (ev681 := eSaf2)
      (ev710 := ePar) (ev_uoummlhs := eGetP) (ld_memczquv := lPar) (ev_tjosvhyt := eCan)
      (ev850 := eHL) (op965 := opA2) (op957 := opB2) (ev904 := eRules) (op1107 := opK)
      (ev1016 := eNext) (hc1137 := hc) .. =>
    subst qk qu qnp qnmot qM qEq
    have hA : xNpN2 = xNpN := Except.ok.inj (opA2.symm.trans opA)
    subst hA
    have hB : xRp2 = xRp := Except.ok.inj (opB2.symm.trans opB)
    subst hB
    have h0 := callSub_of_eq hc
    let ⟨s82, hr⟩ := peel_call h0 e82
    let ⟨s298, hr⟩ := peel_call hr e298
    let ⟨s359, hr⟩ := peel_call hr e359
    let ⟨s345, hr⟩ := peel_call hr e345
    let ⟨s403, hr⟩ := peel_call hr e403
    let ⟨s485, hr⟩ := peel_call hr e485
    let ⟨s523, hr⟩ := peel_call hr e523
    let ⟨s571, hr⟩ := peel_call hr e571
    let ⟨sP1, hr⟩ := peel_call hr eP1
    let ⟨sRen, hr⟩ := peel_call hr eRen
    let ⟨sP2, hr⟩ := peel_call hr eP2
    let ⟨sEq, hr⟩ := peel_call hr eEq
    let ⟨sPins, hr⟩ := peel_call hr ePins
    let ⟨sLP, hr⟩ := peel_call hr eLP
    let ⟨sSort, hr⟩ := peel_call hr eSort
    let ⟨sSaf1, hr⟩ := peel_call hr eSaf1
    let ⟨sSaf2, hr⟩ := peel_call hr eSaf2
    let ⟨sPar, hr⟩ := peel_call hr ePar
    let ⟨sGetP, hr⟩ := peel_call hr eGetP
    let ⟨sCan, hr⟩ := peel_call hr eCan
    let ⟨sHL, hr⟩ := peel_call hr eHL
    let ⟨sRules, hr⟩ := peel_call hr eRules
    let sNext := peel_last hr eNext
    exact Or.inr
      ⟨{ x := _, rest := _, rm := _, mrest := _, ldRecs := l12
         ldModels := l51
         p := _, m67 := _, evGetRec := s82
         nl := _, ty := _, ni := _, nmin := _, rules := _, blk := _, idx := _, ldRec := l76
         m473 := _, ext473 := s298.extends.trans (s359.extends.trans (s345.extends.trans
           (s403.extends.trans s485.extends)))
         vScope := _, m511 := _, evScope := s523
         m561 := _, evNoMent := s571
         mNil1 := _, hNil1 := hNil1
         wPeel1 := _, pd := _, mP1 := _, evPeel1 := sP1
         ren := _, mRen := _, evRen := sRen
         mNil2 := _, hNil2 := hNil2
         wPeel2 := _, pdm := _, mP2 := _, evPeel2 := sP2
         mEq := _, evParamEq := sEq
         xNpN := _, rp := _, opNpN := opA
         opRp := opB
         wP1 := _, wP2 := _, pins := _, mPins := _, evPins := sPins
         nmotNmin := _, opNmotNmin := opC
         vLower := _, mLP := _, evLowerPins := sLP
         mNilSort := _, hNilSort := hNilS
         vSort := _, m596 := _, evSort := sSort
         m669 := _, ext669 := sSaf1.extends.trans sSaf2.extends
         parAddr := _, m698 := _, evParent := sPar
         parPtr := _, parCi := _, mPar := _, evGetParent := sGetP
         ldParent := lPar
         form' := _, mCan := _, evCanon := sCan
         vHL := _, m838 := _, evHeaderLets := sHL
         s' := _, m892 := _, evRules := sRules
         k' := _, opKNext := opK
         evNext := sNext }⟩

end IxVM.Refinement.Typing.FamilyAlias
