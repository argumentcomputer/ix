import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Core.Rep
import IxVMRefinement.Obs.KernelModeled3

/-! # The advice records a family check lists itself

`check_family` walks the advice addresses its payload lists with
`check_advice_records(rc, advice, Nil, wset)` under its own role context `rc`. That walk, and not
the advice walk of a family check nested in its calls (a container's recursor's check runs one, and
so may the check of a basis role's record and its closure), is the family check's own advice
list. Recorded calls do not mark which call made which, so the walk is read off the family check's
unfolding, `«KernelModeled::check_family».Path.run` (generated, `Obs/KernelModeled3.lean`): a
`Prop`, whose fields a definition cannot read. `FamilyOwnAdvice` is therefore a copy of that
constructor with the walk's list `advAs` read at the walk's heap (`m423`, the walk's argument
`x_advice`). **It depends on the generated `«KernelModeled::check_family».Path.run`: when the batch
regenerates `check_family`, this constructor is copied again** (the binder names of the advice list
and the walk's heap are the ones to update).

* `FamilyOwnAdvice`, `FamilyOwnAdvice.path`: the family check's unfolding with its own advice list;
* `FamilyCallOwn`: the observed family check of `B` with the record at `rb` at the limit `lim`, its
  calls `cs` among the run's, with its own advice list;
* `AdviceListedIn`: an address of that list. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Obs
open IxVM (F)

set_option linter.unusedVariables false

/-- **The family check's unfolding with its own advice list**: the constructor of
`«KernelModeled::check_family».Path`, with the list `advAs` that the family check's own advice walk
(`ev465`) reads at its heap `m423` from its argument `x_advice`. -/
inductive FamilyOwnAdvice (x_rc x_block x_rec_block : SourceValue F) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) (calls : List (Call F)) (advAs : List Bytes.Address) :
    Prop where
  | run
      (v104 : SourceValue F) (m105 : Heap F) (cs107 : List (Call F)) (v113 : SourceValue F) (m114 : Heap F) (cs124 : List (Call F)) (m136 : Heap F) (cs146 : List (Call F)) (x_rb : SourceValue F) (x_s1 : SourceValue F) (v181 : SourceValue F) (m184 : Heap F) (cs192 : List (Call F)) (v_coqqixsf : SourceValue F) (m_judpcwze : Heap F) (cs_qdpfxbys : List (Call F)) (m219 : Heap F) (cs229 : List (Call F)) (x_n_a : SourceValue F) (x_s2 : SourceValue F) (m254 : Heap F) (cs264 : List (Call F)) (x_advice : SourceValue F) (x_s3 : SourceValue F) (m297 : Heap F) (cs307 : List (Call F)) (x_n_w : SourceValue F) (x_s4 : SourceValue F) (m332 : Heap F) (cs342 : List (Call F)) (x_outside : SourceValue F) (x_s5 : SourceValue F) (v390 : SourceValue F) (m391 : Heap F) (cs401 : List (Call F)) (v422 : SourceValue F) (m423 : Heap F) (cs433 : List (Call F)) (v452 : SourceValue F) (m453 : Heap F) (cs463 : List (Call F)) (m501 : Heap F) (cs511 : List (Call F)) (w538 : SourceValue F) (w539 : SourceValue F) (w540 : SourceValue F) (w541 : SourceValue F) (x_members : SourceValue F) (v588 : SourceValue F) (m589 : Heap F) (cs599 : List (Call F)) (v621 : SourceValue F) (m624 : Heap F) (cs632 : List (Call F)) (v651 : SourceValue F) (m652 : Heap F) (cs662 : List (Call F)) (v673 : SourceValue F) (m674 : Heap F) (cs684 : List (Call F)) (m704 : Heap F) (cs714 : List (Call F)) (x_type_models : SourceValue F) (x_s6 : SourceValue F) (v746 : SourceValue F) (m747 : Heap F) (cs757 : List (Call F)) (m784 : Heap F) (cs794 : List (Call F)) (v798 : SourceValue F) (m807 : Heap F) (cs815 : List (Call F)) (x_ctor_models : SourceValue F) (x_s7 : SourceValue F) (v839 : SourceValue F) (m840 : Heap F) (cs850 : List (Call F)) (v_ljrrbtrv : SourceValue F) (m_pjcdckev : Heap F) (cs_faqayeqo : List (Call F)) (v_pehslahh : SourceValue F) (m_qvdvjtit : Heap F) (cs_fintoksh : List (Call F)) (v861 : SourceValue F) (m862 : Heap F) (cs872 : List (Call F)) (m884 : Heap F) (cs894 : List (Call F)) (x_rec_models : SourceValue F) (x_s8 : SourceValue F) (v926 : SourceValue F) (m927 : Heap F) (cs937 : List (Call F)) (v941 : SourceValue F) (m950 : Heap F) (cs958 : List (Call F)) (v977 : SourceValue F) (m978 : Heap F) (cs988 : List (Call F)) (v992 : SourceValue F) (m1001 : Heap F) (cs1009 : List (Call F)) (v_bywohujs : SourceValue F) (m_poohxluf : Heap F) (cs_kvoimdyk : List (Call F)) (v_vvlojrvi : SourceValue F) (m_hqdlbapi : Heap F) (cs_oespsyhf : List (Call F)) (v_cpznqbet : SourceValue F) (m_pzytquge : Heap F) (cs_meprltek : List (Call F)) (v_gsjohlrb : SourceValue F) (m_lukcasbb : Heap F) (cs_cfwtnbsy : List (Call F)) (m1191 : Heap F) (cs1201 : List (Call F)) (x_bnl : SourceValue F) (x_univ_offset : SourceValue F) (v_qwfkpklj : SourceValue F) (m_ialrkdmk : Heap F) (cs_pblrtsmj : List (Call F)) (v1233 : SourceValue F) (m1234 : Heap F) (cs1244 : List (Call F)) (v_tabgyphp : SourceValue F) (m_gmcvdxbt : Heap F) (cs_haaqvnwp : List (Call F)) (v_arypxepi : SourceValue F) (m_soowcubw : Heap F) (y_xxqgtlpp : SourceValue F) (cs_owchsduj : List (Call F)) (v_tpfunfpk : SourceValue F) (m_yarikpkl : Heap F) (x_gwlxyjol : SourceValue F) (y_ukzxkjha : SourceValue F) (m_jbcuvwlm : Heap F) (cs_rffscqgg : List (Call F)) (y_svqhibng : SourceValue F) (cs_exeqqufq : List (Call F)) (v_btzwyhmz : SourceValue F) (x_eezzidwb : SourceValue F) (y_jggqqrgl : SourceValue F) (v1292 : SourceValue F) (m1293 : Heap F) (cs1303 : List (Call F)) (v1330 : SourceValue F) (m1331 : Heap F) (cs1341 : List (Call F))
      (sg112 : «KernelModeled::check_family».Seg1 x_rc x_block x_rec_block h v104 m105 cs107)
      (ev126 : ObsFn Obs.W "KernelModeled::read_payload" [x_block] m105 v113 m114 cs124)
      (ev148 : ObsFn Obs.W "IxonDeserialize::get_address" [v113] m114 (.tuple [x_rb, x_s1]) m136 cs146)
      (ev194 : ObsFn Obs.W "Bytes::address_eq" [x_rb, x_rec_block] m136 v181 m184 cs192)
      (heq217 : (v181 : SourceValue F) = (.field 1))
      (ev_yqjbwijz : ObsFn Obs.W "KernelRoles::assert_in_order" [x_rc, x_rec_block] m184 v_coqqixsf m_judpcwze cs_qdpfxbys)
      (ev231 : ObsFn Obs.W "KernelModeled::get_count" [x_s1] m_judpcwze (.tuple [x_n_a, x_s2]) m219 cs229)
      (ev266 : ObsFn Obs.W "KernelModeled::get_addrs" [x_s2, x_n_a] m219 (.tuple [x_advice, x_s3]) m254 cs264)
      (ev309 : ObsFn Obs.W "KernelModeled::get_count" [x_s3] m254 (.tuple [x_n_w, x_s4]) m297 cs307)
      (ev344 : ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_block, x_s4, x_n_w] m297 (.tuple [x_outside, x_s5]) m332 cs342)
      (ev403 : ObsFn Obs.W "KernelClaim::addr_set_build" [x_outside, (.construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [])] m332 v390 m391 cs401)
      (ev435 : ObsFn Obs.W "KernelModeled::container_recs_refs" [x_rc, x_outside, v390] m391 v422 m423 cs433)
      (ev465 : ObsFn Obs.W "KernelModeled::check_advice_records" [x_rc, x_advice, (.construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []), v390] m423 v452 m453 cs463)
      (ev513 : ObsFn Obs.W "Ingress::load_verified_constant" [x_block] m453 (.construct "Ixon::Constant" "Mk" [(.construct "Ixon::ConstantInfo" "Muts" [x_members]), w538, w539, w540, w541]) m501 cs511)
      (ev601 : ObsFn Obs.W Names.«Lists::length<Ixon::MutConst>» [x_members] m501 v588 m589 cs599)
      (ev634 : ObsFn Obs.W "KernelModeled::muts_indc_count" [x_members] m589 v621 m624 cs632)
      (heq650 : (v621 : SourceValue F) = v588)
      (ev664 : ObsFn Obs.W "KernelModeled::block_nparams" [x_members] m624 v651 m652 cs662)
      (ev686 : ObsFn Obs.W "Ingress::build_recur_addrs" [x_members, x_block] m652 v673 m674 cs684)
      (ev716 : ObsFn Obs.W "KernelModeled::get_addrs" [x_s5, v588] m674 (.tuple [x_type_models, x_s6]) m704 cs714)
      (ev759 : ObsFn Obs.W "KernelModeled::block_ctor_addrs" [x_members, x_block, (.field 0)] m704 v746 m747 cs757)
      (ev817 : ObsFn Obs.W Names.«Lists::length<&[Field; 32]>» [v746] m747 v798 m807 cs815)
      (ev796 : ObsFn Obs.W "KernelModeled::get_addrs" [x_s6, v798] m807 (.tuple [x_ctor_models, x_s7]) m784 cs794)
      (ev852 : ObsFn Obs.W "KernelModeled::family_recs" [x_rec_block] m784 v839 m840 cs850)
      (ev_ursqbimm : ObsFn Obs.W "KernelModeled::assert_no_role" [x_rc, v839] m840 v_ljrrbtrv m_pjcdckev cs_faqayeqo)
      (ev_srfmazjk : ObsFn Obs.W "KernelModeled::assert_no_type_role" [x_rc, v673] m_pjcdckev v_pehslahh m_qvdvjtit cs_fintoksh)
      (ev874 : ObsFn Obs.W Names.«Lists::length<&[Field; 32]>» [v839] m_qvdvjtit v861 m862 cs872)
      (ev896 : ObsFn Obs.W "KernelModeled::get_addrs" [x_s7, v861] m862 (.tuple [x_rec_models, x_s8]) m884 cs894)
      (ev960 : ObsFn Obs.W Names.«Lists::concat<&[Field; 32]>» [v746, v839] m884 v941 m950 cs958)
      (ev939 : ObsFn Obs.W Names.«Lists::concat<&[Field; 32]>» [v673, v941] m950 v926 m927 cs937)
      (ev1011 : ObsFn Obs.W Names.«Lists::concat<&[Field; 32]>» [x_ctor_models, x_rec_models] m927 v992 m1001 cs1009)
      (ev990 : ObsFn Obs.W Names.«Lists::concat<&[Field; 32]>» [x_type_models, v992] m1001 v977 m978 cs988)
      (ev_edyzsqzv : ObsFn Obs.W "KernelModeled::members_val" [v673, x_type_models, v926, v977, v452, v926] m978 v_bywohujs m_poohxluf cs_kvoimdyk)
      (ev_gkddqxhv : ObsFn Obs.W Names.«Lists::concat<&[Field; 32]>» [v746, v839] m_poohxluf v_cpznqbet m_pzytquge cs_meprltek)
      (ev_ittpynob : ObsFn Obs.W "KernelModeled::members_val" [v746, x_ctor_models, v926, v977, v452, v_cpznqbet] m_pzytquge v_vvlojrvi m_hqdlbapi cs_oespsyhf)
      (ev_biaifgpd : ObsFn Obs.W "KernelModeled::members_val" [v839, x_rec_models, v926, v977, v452, v839] m_hqdlbapi v_gsjohlrb m_lukcasbb cs_cfwtnbsy)
      (ev1203 : ObsFn Obs.W "KernelModeled::block_elim" [x_rc, v673] m_lukcasbb (.tuple [x_bnl, x_univ_offset]) m1191 cs1201)
      (ev_cwwgzxtj : ObsFn Obs.W "KernelCheck::build_flat_block" [x_rec_block, x_block, x_univ_offset] m1191 v_qwfkpklj m_ialrkdmk cs_pblrtsmj)
      (ev1246 : ObsFn Obs.W "KernelModeled::check_nested_aux" [x_block, v_qwfkpklj] m_ialrkdmk v1233 m1234 cs1244)
      (ev_mitevvsv : ObsFn Obs.W Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>» [v_qwfkpklj] m1234 y_xxqgtlpp m_soowcubw cs_owchsduj)
      (op_jmfoqaec : evalBinOp .sub (v861 : SourceValue F) (y_xxqgtlpp : SourceValue F) = .ok v_arypxepi)
      (ev_rqpeovbn : ObsFn Obs.W "Fields::is_zero" [v_arypxepi] m_soowcubw v_tabgyphp m_gmcvdxbt cs_haaqvnwp)
      (ev_xrhmaojz : ObsFn Obs.W "Fields::is_zero" [v861] m_gmcvdxbt x_gwlxyjol m_jbcuvwlm cs_rffscqgg)
      (ev_whimdwjd : ObsFn Obs.W "KernelRoles::rc_validates_group" [x_rc] m_jbcuvwlm y_svqhibng m_yarikpkl cs_exeqqufq)
      (op_qfbltjlu : evalBinOp .sub ((.field 1) : SourceValue F) (y_svqhibng : SourceValue F) = .ok y_ukzxkjha)
      (op_cnutjuwu : evalBinOp .mul (x_gwlxyjol : SourceValue F) (y_ukzxkjha : SourceValue F) = .ok v_tpfunfpk)
      (op_ymhwloon : evalBinOp .add (v_tabgyphp : SourceValue F) (v_tpfunfpk : SourceValue F) = .ok x_eezzidwb)
      (op_mvhbzaru : evalBinOp .mul (v_tabgyphp : SourceValue F) (v_tpfunfpk : SourceValue F) = .ok y_jggqqrgl)
      (op_zaucahqq : evalBinOp .sub (x_eezzidwb : SourceValue F) (y_jggqqrgl : SourceValue F) = .ok v_btzwyhmz)
      (heq_sujkqzii : (v_btzwyhmz : SourceValue F) = (.field 1))
      (ev1305 : ObsFn Obs.W "KernelModeled::family_refs_ok" [x_rc, x_rec_block, x_block, v390] m_yarikpkl v1292 m1293 cs1303)
      (ev1343 : ObsFn Obs.W "KernelModeled::check_recs" [x_rc, v673, v839, x_rec_models, v926, v977, v452, x_s8, v861, (.field 0), v651, x_univ_offset, x_bnl, v839, (.field 0)] m1293 v1330 m1331 cs1341)
      (ld1465 : loadValue m1331 v1330 = .ok (.construct Names.«Lists::Node<Field>» "Nil" []))
      (he1472 : r = (.tuple []))
      (he1473 : h' = m1331)
      (hc1474 : calls = (cs107 ++ ((⟨"KernelModeled::read_payload", [x_block], m105⟩ : Call F) :: (cs124 ++ ((⟨"IxonDeserialize::get_address", [v113], m114⟩ : Call F) :: (cs146 ++ ((⟨"Bytes::address_eq", [x_rb, x_rec_block], m136⟩ : Call F) :: (cs192 ++ ((⟨"KernelRoles::assert_in_order", [x_rc, x_rec_block], m184⟩ : Call F) :: (cs_qdpfxbys ++ ((⟨"KernelModeled::get_count", [x_s1], m_judpcwze⟩ : Call F) :: (cs229 ++ ((⟨"KernelModeled::get_addrs", [x_s2, x_n_a], m219⟩ : Call F) :: (cs264 ++ ((⟨"KernelModeled::get_count", [x_s3], m254⟩ : Call F) :: (cs307 ++ ((⟨"KernelModeled::check_witnesses", [x_rc, x_block, x_s4, x_n_w], m297⟩ : Call F) :: (cs342 ++ ((⟨"KernelClaim::addr_set_build", [x_outside, (.construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [])], m332⟩ : Call F) :: (cs401 ++ ((⟨"KernelModeled::container_recs_refs", [x_rc, x_outside, v390], m391⟩ : Call F) :: (cs433 ++ ((⟨"KernelModeled::check_advice_records", [x_rc, x_advice, (.construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []), v390], m423⟩ : Call F) :: (cs463 ++ ((⟨"Ingress::load_verified_constant", [x_block], m453⟩ : Call F) :: (cs511 ++ ((⟨Names.«Lists::length<Ixon::MutConst>», [x_members], m501⟩ : Call F) :: (cs599 ++ ((⟨"KernelModeled::muts_indc_count", [x_members], m589⟩ : Call F) :: (cs632 ++ ((⟨"KernelModeled::block_nparams", [x_members], m624⟩ : Call F) :: (cs662 ++ ((⟨"Ingress::build_recur_addrs", [x_members, x_block], m652⟩ : Call F) :: (cs684 ++ ((⟨"KernelModeled::get_addrs", [x_s5, v588], m674⟩ : Call F) :: (cs714 ++ ((⟨"KernelModeled::block_ctor_addrs", [x_members, x_block, (.field 0)], m704⟩ : Call F) :: (cs757 ++ ((⟨Names.«Lists::length<&[Field; 32]>», [v746], m747⟩ : Call F) :: (cs815 ++ ((⟨"KernelModeled::get_addrs", [x_s6, v798], m807⟩ : Call F) :: (cs794 ++ ((⟨"KernelModeled::family_recs", [x_rec_block], m784⟩ : Call F) :: (cs850 ++ ((⟨"KernelModeled::assert_no_role", [x_rc, v839], m840⟩ : Call F) :: (cs_faqayeqo ++ ((⟨"KernelModeled::assert_no_type_role", [x_rc, v673], m_pjcdckev⟩ : Call F) :: (cs_fintoksh ++ ((⟨Names.«Lists::length<&[Field; 32]>», [v839], m_qvdvjtit⟩ : Call F) :: (cs872 ++ ((⟨"KernelModeled::get_addrs", [x_s7, v861], m862⟩ : Call F) :: (cs894 ++ ((⟨Names.«Lists::concat<&[Field; 32]>», [v746, v839], m884⟩ : Call F) :: (cs958 ++ ((⟨Names.«Lists::concat<&[Field; 32]>», [v673, v941], m950⟩ : Call F) :: (cs937 ++ ((⟨Names.«Lists::concat<&[Field; 32]>», [x_ctor_models, x_rec_models], m927⟩ : Call F) :: (cs1009 ++ ((⟨Names.«Lists::concat<&[Field; 32]>», [x_type_models, v992], m1001⟩ : Call F) :: (cs988 ++ ((⟨"KernelModeled::members_val", [v673, x_type_models, v926, v977, v452, v926], m978⟩ : Call F) :: (cs_kvoimdyk ++ ((⟨Names.«Lists::concat<&[Field; 32]>», [v746, v839], m_poohxluf⟩ : Call F) :: (cs_meprltek ++ ((⟨"KernelModeled::members_val", [v746, x_ctor_models, v926, v977, v452, v_cpznqbet], m_pzytquge⟩ : Call F) :: (cs_oespsyhf ++ ((⟨"KernelModeled::members_val", [v839, x_rec_models, v926, v977, v452, v839], m_hqdlbapi⟩ : Call F) :: (cs_cfwtnbsy ++ ((⟨"KernelModeled::block_elim", [x_rc, v673], m_lukcasbb⟩ : Call F) :: (cs1201 ++ ((⟨"KernelCheck::build_flat_block", [x_rec_block, x_block, x_univ_offset], m1191⟩ : Call F) :: (cs_pblrtsmj ++ ((⟨"KernelModeled::check_nested_aux", [x_block, v_qwfkpklj], m_ialrkdmk⟩ : Call F) :: (cs1244 ++ ((⟨Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>», [v_qwfkpklj], m1234⟩ : Call F) :: (cs_owchsduj ++ ((⟨"Fields::is_zero", [v_arypxepi], m_soowcubw⟩ : Call F) :: (cs_haaqvnwp ++ ((⟨"Fields::is_zero", [v861], m_gmcvdxbt⟩ : Call F) :: (cs_rffscqgg ++ ((⟨"KernelRoles::rc_validates_group", [x_rc], m_jbcuvwlm⟩ : Call F) :: (cs_exeqqufq ++ ((⟨"KernelModeled::family_refs_ok", [x_rc, x_rec_block, x_block, v390], m_yarikpkl⟩ : Call F) :: (cs1303 ++ ((⟨"KernelModeled::check_recs", [x_rc, v673, v839, x_rec_models, v926, v977, v452, x_s8, v861, (.field 0), v651, x_univ_offset, x_bnl, v839, (.field 0)], m1293⟩ : Call F) :: cs1341)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

      (hadv : RepList addrListEnum (Bytes.RepAddressRef addrTy) m423 advAs x_advice)

/-- The family check's unfolding with its own advice list is the family check's unfolding. -/
theorem FamilyOwnAdvice.path {x_rc x_block x_rec_block : SourceValue F} {h : Heap F}
    {r : SourceValue F} {h' : Heap F} {calls : List (Call F)} {advAs : List Bytes.Address}
    (w : FamilyOwnAdvice x_rc x_block x_rec_block h r h' calls advAs) :
    «KernelModeled::check_family».Path x_rc x_block x_rec_block h r h' calls := by
  obtain ⟨v104, m105, cs107, v113, m114, cs124, m136, cs146, x_rb, x_s1, v181, m184, cs192, v_coqqixsf, m_judpcwze, cs_qdpfxbys, m219, cs229, x_n_a, x_s2, m254, cs264, x_advice, x_s3, m297, cs307, x_n_w, x_s4, m332, cs342, x_outside, x_s5, v390, m391, cs401, v422, m423, cs433, v452, m453, cs463, m501, cs511, w538, w539, w540, w541, x_members, v588, m589, cs599, v621, m624, cs632, v651, m652, cs662, v673, m674, cs684, m704, cs714, x_type_models, x_s6, v746, m747, cs757, m784, cs794, v798, m807, cs815, x_ctor_models, x_s7, v839, m840, cs850, v_ljrrbtrv, m_pjcdckev, cs_faqayeqo, v_pehslahh, m_qvdvjtit, cs_fintoksh, v861, m862, cs872, m884, cs894, x_rec_models, x_s8, v926, m927, cs937, v941, m950, cs958, v977, m978, cs988, v992, m1001, cs1009, v_bywohujs, m_poohxluf, cs_kvoimdyk, v_vvlojrvi, m_hqdlbapi, cs_oespsyhf, v_cpznqbet, m_pzytquge, cs_meprltek, v_gsjohlrb, m_lukcasbb, cs_cfwtnbsy, m1191, cs1201, x_bnl, x_univ_offset, v_qwfkpklj, m_ialrkdmk, cs_pblrtsmj, v1233, m1234, cs1244, v_tabgyphp, m_gmcvdxbt, cs_haaqvnwp, v_arypxepi, m_soowcubw, y_xxqgtlpp, cs_owchsduj, v_tpfunfpk, m_yarikpkl, x_gwlxyjol, y_ukzxkjha, m_jbcuvwlm, cs_rffscqgg, y_svqhibng, cs_exeqqufq, v_btzwyhmz, x_eezzidwb, y_jggqqrgl, v1292, m1293, cs1303, v1330, m1331, cs1341, sg112, ev126, ev148, ev194, heq217, ev_yqjbwijz, ev231, ev266, ev309, ev344, ev403, ev435, ev465, ev513, ev601, ev634, heq650, ev664, ev686, ev716, ev759, ev817, ev796, ev852, ev_ursqbimm, ev_srfmazjk, ev874, ev896, ev960, ev939, ev1011, ev990, ev_edyzsqzv, ev_gkddqxhv, ev_ittpynob, ev_biaifgpd, ev1203, ev_cwwgzxtj, ev1246, ev_mitevvsv, op_jmfoqaec, ev_rqpeovbn, ev_xrhmaojz, ev_whimdwjd, op_qfbltjlu, op_cnutjuwu, op_ymhwloon, op_mvhbzaru, op_zaucahqq, heq_sujkqzii, ev1305, ev1343, ld1465, he1472, he1473, hc1474, -⟩ := w
  exact ⟨v104, m105, cs107, v113, m114, cs124, m136, cs146, x_rb, x_s1, v181, m184, cs192, v_coqqixsf, m_judpcwze, cs_qdpfxbys, m219, cs229, x_n_a, x_s2, m254, cs264, x_advice, x_s3, m297, cs307, x_n_w, x_s4, m332, cs342, x_outside, x_s5, v390, m391, cs401, v422, m423, cs433, v452, m453, cs463, m501, cs511, w538, w539, w540, w541, x_members, v588, m589, cs599, v621, m624, cs632, v651, m652, cs662, v673, m674, cs684, m704, cs714, x_type_models, x_s6, v746, m747, cs757, m784, cs794, v798, m807, cs815, x_ctor_models, x_s7, v839, m840, cs850, v_ljrrbtrv, m_pjcdckev, cs_faqayeqo, v_pehslahh, m_qvdvjtit, cs_fintoksh, v861, m862, cs872, m884, cs894, x_rec_models, x_s8, v926, m927, cs937, v941, m950, cs958, v977, m978, cs988, v992, m1001, cs1009, v_bywohujs, m_poohxluf, cs_kvoimdyk, v_vvlojrvi, m_hqdlbapi, cs_oespsyhf, v_cpznqbet, m_pzytquge, cs_meprltek, v_gsjohlrb, m_lukcasbb, cs_cfwtnbsy, m1191, cs1201, x_bnl, x_univ_offset, v_qwfkpklj, m_ialrkdmk, cs_pblrtsmj, v1233, m1234, cs1244, v_tabgyphp, m_gmcvdxbt, cs_haaqvnwp, v_arypxepi, m_soowcubw, y_xxqgtlpp, cs_owchsduj, v_tpfunfpk, m_yarikpkl, x_gwlxyjol, y_ukzxkjha, m_jbcuvwlm, cs_rffscqgg, y_svqhibng, cs_exeqqufq, v_btzwyhmz, x_eezzidwb, y_jggqqrgl, v1292, m1293, cs1303, v1330, m1331, cs1341, sg112, ev126, ev148, ev194, heq217, ev_yqjbwijz, ev231, ev266, ev309, ev344, ev403, ev435, ev465, ev513, ev601, ev634, heq650, ev664, ev686, ev716, ev759, ev817, ev796, ev852, ev_ursqbimm, ev_srfmazjk, ev874, ev896, ev960, ev939, ev1011, ev990, ev_edyzsqzv, ev_gkddqxhv, ev_ittpynob, ev_biaifgpd, ev1203, ev_cwwgzxtj, ev1246, ev_mitevvsv, op_jmfoqaec, ev_rqpeovbn, ev_xrhmaojz, ev_whimdwjd, op_qfbltjlu, op_cnutjuwu, op_ymhwloon, op_mvhbzaru, op_zaucahqq, heq_sujkqzii, ev1305, ev1343, ld1465, he1472, he1473, hc1474⟩

/-- **The family check of the block at `B` with the family record at `rb`, with its own advice
list**: `check_family [rc, B, rb]` observed with calls `cs` under a role context at `lim` with the
table at `bAddr`, the call and its calls in the run, and the list `advAs` its own advice walk
reads (`FamilyOwnAdvice`). -/
def FamilyCallOwn (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (B rb : _root_.Address) (lim : Option Nat) (cs : List (Call F))
    (advAs : List Bytes.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ S0.addr h xb B ∧ S0.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    FamilyOwnAdvice rc xb xrb h r h' cs advAs ∧
    (⟨"KernelModeled::check_family", [rc, xb, xrb], h⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs, cl ∈ calls)

/-- **The family check's own advice walk**: a `check_advice_records` call under the family check's
role context, at an extension of the family check's heap where the list is read, with its calls
among the family check's. -/
theorem FamilyOwnAdvice.walk {x_rc x_block x_rec_block : SourceValue F} {h : Heap F}
    {r : SourceValue F} {h' : Heap F} {calls : List (Call F)} {advAs : List Bytes.Address}
    (w : FamilyOwnAdvice x_rc x_block x_rec_block h r h' calls advAs) :
    ∃ (m m' : Heap F) (xadv seen wset v : SourceValue F) (cs₁ : List (Call F)),
      Heap.Extends h m ∧ RepList addrListEnum (Bytes.RepAddressRef addrTy) m advAs xadv ∧
      ObsFn Obs.W "KernelModeled::check_advice_records" [x_rc, xadv, seen, wset] m v m' cs₁ ∧
      ∀ cl ∈ cs₁, cl ∈ calls := by
  match w with
  | .run (m105 := m105) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := evo) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309) (ev344 := ev344)
      (ev403 := ev403) (ev435 := ev435) (ev465 := ev465) (hc1474 := hc) (hadv := hadv) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. =>
        rw [he33]
        exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    refine ⟨_, _, _, _, _, _, _, e0.trans (ev126.heap_extends.trans (ev148.heap_extends.trans
      (ev194.heap_extends.trans (evo.heap_extends.trans (ev231.heap_extends.trans
      (ev266.heap_extends.trans (ev309.heap_extends.trans (ev344.heap_extends.trans
      (ev403.heap_extends.trans ev435.heap_extends))))))))), hadv, ev465, fun cl hcl => ?_⟩
    rw [hc]
    simp [hcl]

/-- **An advice record listed by a family check itself**: an address of the family check's own
advice list. -/
def AdviceListedIn (advAs : List Bytes.Address) (a : _root_.Address) : Prop :=
  ∃ b ∈ advAs, ixAddr b = a

end IxVM.Refinement.Typing
