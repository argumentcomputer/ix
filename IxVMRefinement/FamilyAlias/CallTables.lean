import IxVMRefinement.FamilyAlias.CallStreams
import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Assembly.FamilyArm

/-! # The tables `check_family` renames over

`KernelModeled::check_family` builds two tables of addresses and renames every term it checks by
them: `src`, the block's types (`Ingress::build_recur_addrs`), its constructors
(`KernelModeled::block_ctor_addrs`) and the family record's recursors
(`KernelModeled::family_recs`); and `dst`, a model for each, read off the payload in that order
(`KernelModeled::get_addrs`, three times). This module reads both tables off the check:

* `FamilyTables`: the six lists and the two tables, represented at a heap, the members' lists as
  the block and the family record give them, and a model for each member;
* `family_payload_stream`: the payload is a stream where the models start
  (`read_payload`, `get_address`, `get_count`, `get_addrs`, `check_witnesses`);
* `family_tables`: the tables, from the steps of the check that build them;
* `check_family_tables`: the same, from an observed check;
* `famAddr_mem_src`: a constant address of the block or of the family record is in `src`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false

/-! ## Sizes -/

private theorem length_le_sum_map {α : Type} (f : α → Nat) (hf : ∀ a, 1 ≤ f a) (l : List α) :
    l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := hf a
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **A block's constructors are no more than its members' resource sizes.** -/
theorem ctorAddrsFrom_length_le (B : _root_.Address) :
    ∀ (ms : List Ixon.MutConst) (p : Nat),
      (ctorAddrsFrom B ms p).length ≤ (ms.map Ixon.MutConst.resourceSize).sum
  | [], _ => by simp [ctorAddrsFrom]
  | .indc ind :: rest, p => by
    have ih := ctorAddrsFrom_length_le B rest (p + 1)
    have e : ctorAddrsFrom B (.indc ind :: rest) p =
        (List.range ind.ctors.size).map (cprjAddr B p) ++ ctorAddrsFrom B rest (p + 1) := rfl
    have h2 := length_le_sum_map Ixon.Constructor.resourceSize
      (fun ct => by dsimp only [Ixon.Constructor.resourceSize]; omega) ind.ctors.toList
    have h3 : (ind.ctors.toList.map Ixon.Constructor.resourceSize).sum ≤
        (Ixon.MutConst.indc ind).resourceSize := by
      dsimp only [Ixon.MutConst.resourceSize, Ixon.Inductive.resourceSize]
      omega
    rw [Array.length_toList] at h2
    rw [e, List.length_append, List.length_map, List.length_range, List.map_cons, List.sum_cons]
    omega
  | .defn d :: rest, p => by
    have ih := ctorAddrsFrom_length_le B rest (p + 1)
    have e : ctorAddrsFrom B (.defn d :: rest) p = ctorAddrsFrom B rest (p + 1) := rfl
    rw [e, List.map_cons, List.sum_cons]
    omega
  | .recr r :: rest, p => by
    have ih := ctorAddrsFrom_length_le B rest (p + 1)
    have e : ctorAddrsFrom B (.recr r :: rest) p = ctorAddrsFrom B rest (p + 1) := rfl
    rw [e, List.map_cons, List.sum_cons]
    omega

/-- **A block record's members' resource sizes are below its own.** -/
theorem muts_sum_le {c : Ixon.Constant} {ms : Array Ixon.MutConst} (h : c.info = .muts ms) :
    (ms.toList.map Ixon.MutConst.resourceSize).sum ≤ c.resourceSize := by
  have h2 : c.info.resourceSize ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  rw [h] at h2
  dsimp [Ixon.ConstantInfo.resourceSize] at h2
  omega

/-- **A constructor of an inductive member is among the block's constructor addresses.** -/
theorem mem_ctorAddrsFrom (B : _root_.Address) :
    ∀ (ms : List Ixon.MutConst) (p i : Nat) (ind : Ixon.Inductive) (j : Nat),
      ms[i]? = some (.indc ind) → j < ind.ctors.size →
      cprjAddr B (p + i) j ∈ ctorAddrsFrom B ms p
  | [], _, _, _, _, hi, _ => by simp at hi
  | m :: rest, p, 0, ind, j, hi, hj => by
    have e : m = .indc ind := by simpa using hi
    subst e
    have e2 : ctorAddrsFrom B (.indc ind :: rest) p =
        (List.range ind.ctors.size).map (cprjAddr B p) ++ ctorAddrsFrom B rest (p + 1) := rfl
    rw [e2, Nat.add_zero]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  | m :: rest, p, i + 1, ind, j, hi, hj => by
    have ih := mem_ctorAddrsFrom B rest (p + 1) i ind j (by simpa using hi) hj
    have e3 : p + 1 + i = p + (i + 1) := by omega
    rw [e3] at ih
    cases m with
    | indc ind' =>
      have e2 : ctorAddrsFrom B (.indc ind' :: rest) p =
          (List.range ind'.ctors.size).map (cprjAddr B p) ++ ctorAddrsFrom B rest (p + 1) := rfl
      rw [e2]
      exact List.mem_append_right _ ih
    | defn d =>
      have e2 : ctorAddrsFrom B (.defn d :: rest) p = ctorAddrsFrom B rest (p + 1) := rfl
      rw [e2]
      exact ih
    | recr r =>
      have e2 : ctorAddrsFrom B (.recr r :: rest) p = ctorAddrsFrom B rest (p + 1) := rfl
      rw [e2]
      exact ih

/-- **A family record read by `KernelModeled::family_recs` has fewer than `2^33` members**: its
load is a block load, whose record's resource size is below `2^33`. -/
theorem family_recs_bound {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {b : Bytes.Address} {x_rb v : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h b x_rb)
    (ev : ObsFn W "KernelModeled::family_recs" [x_rb] h v h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hrb : FamRecRecord E₀ (ixAddr b) crb rs) : rs.size < 8589934592 := by
  match Obs.«KernelModeled::family_recs».obs ev with
  | .Muts (cs12 := cs12) (ev14 := ev14) (hc165 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨cb, ms, hbl, -⟩ := Claim.load_block_head hb ev14
    obtain ⟨-, hlt⟩ := (hbl.mono hsub12).record hS hrb.record
    have := Claim.muts_size_le hrb.muts
    omega
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc209 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨-, bytes, c, hsz, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      Ingress.load_verified_constant_decode_bounded hb ev14
    have haddr' : _root_.Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr b := haddr
    have hrecb : recordOf E₀ (ixAddr b) = some c := by
      rw [← haddr']
      exact Claim.recordOf_of_hashed hH (Core.hashed_mono hsub12 hh)
        (by simpa only [ByteArray.size, List.size_toArray] using hsz) hexact
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [← hinfo_eq] at hinfoRep
    obtain ⟨rcr, hrc, -⟩ := Ingress.repConstantInfo_recr_inv hinfoRep
    have e1 : c = crb := Option.some.inj (hrecb.symm.trans hrb.record)
    subst e1
    rw [hrb.muts] at hrc
    cases hrc

/-! ## The tables -/

/-- **The address tables of one family check**, at the heap `h`: the block's types `typeAs`, its
constructors `ctorAs` and the family record's recursors `recAs`, as the block at `B` (members
`ms`) and the family record at `rb` (members `rs`) give them; a model for each (`typeMs`,
`ctorMs`, `recMs`); the table `src` of the members and the table `dst` of the models, in that
order. -/
structure FamilyTables (B rb : _root_.Address) (ms rs : Array Ixon.MutConst) (h : Heap F)
    (typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address)
    (xtA xcA xrA xtM xcM xrM xsrc xdst : SourceValue F) : Prop where
  typesRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA
  ctorsRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h ctorAs xcA
  recsRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h recAs xrA
  typeModelsRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeMs xtM
  ctorModelsRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h ctorMs xcM
  recModelsRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h recMs xrM
  srcRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (typeAs ++ (ctorAs ++ recAs)) xsrc
  dstRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h (typeMs ++ (ctorMs ++ recMs)) xdst
  types : typeAs.map ixAddr =
    ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m)
  ctors : ctorAs.map ixAddr = ctorAddrsFrom B ms.toList 0
  recs : recAs.map ixAddr =
    rs.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo rb i m)
  typeModels : typeMs.length = typeAs.length
  ctorModels : ctorMs.length = ctorAs.length
  recModels : recMs.length = recAs.length

/-- The tables at an extension of the heap. -/
theorem FamilyTables.mono {B rb : _root_.Address} {ms rs : Array Ixon.MutConst} {h h' : Heap F}
    {typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address}
    {xtA xcA xrA xtM xcM xrM xsrc xdst : SourceValue F} (ext : Heap.Extends h h')
    (T : FamilyTables B rb ms rs h typeAs ctorAs recAs typeMs ctorMs recMs xtA xcA xrA xtM xcM
      xrM xsrc xdst) :
    FamilyTables B rb ms rs h' typeAs ctorAs recAs typeMs ctorMs recMs xtA xcA xrA xtM xcM xrM
      xsrc xdst :=
  { typesRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.typesRep
    ctorsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.ctorsRep
    recsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.recsRep
    typeModelsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.typeModelsRep
    ctorModelsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.ctorModelsRep
    recModelsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.recModelsRep
    srcRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.srcRep
    dstRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext T.dstRep
    types := T.types
    ctors := T.ctors
    recs := T.recs
    typeModels := T.typeModels
    ctorModels := T.ctorModels
    recModels := T.recModels }

/-- The two tables have one model for each member. -/
theorem FamilyTables.length_eq {B rb : _root_.Address} {ms rs : Array Ixon.MutConst} {h : Heap F}
    {typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address}
    {xtA xcA xrA xtM xcM xrM xsrc xdst : SourceValue F}
    (T : FamilyTables B rb ms rs h typeAs ctorAs recAs typeMs ctorMs recMs xtA xcA xrA xtM xcM
      xrM xsrc xdst) :
    (typeAs ++ (ctorAs ++ recAs)).length = (typeMs ++ (ctorMs ++ recMs)).length := by
  simp only [List.length_append, T.typeModels, T.ctorModels, T.recModels]

/-! ## The payload up to the models -/

/-- **The payload is a stream where the models start**: `read_payload` gives a stream
(`read_payload_stream`); the family record's address (`IxonDeserialize::get_address`, then
`KernelRoles::assert_in_order` at it), the
advice list (`get_count`, `get_addrs`) and the witnesses (`get_count`, `check_witnesses`) each
leave one. -/
theorem family_payload_stream {xb xrb v113 x_rb x_s1 v181 x_n_a x_s2 x_advice x_s3 x_n_w x_s4 x_rc
      x_outside x_s5 v_ord : SourceValue F}
    {m105 m114 m136 m184 m184' m219 m254 m297 m332 : Heap F}
    {cs124 cs146 cs192 cs_ord cs229 cs264 cs307 cs342 : List (Call F)}
    (ev126 : ObsFn W "KernelModeled::read_payload" [xb] m105 v113 m114 cs124)
    (ev148 : ObsFn W "IxonDeserialize::get_address" [v113] m114 (.tuple [x_rb, x_s1]) m136 cs146)
    (ev194 : ObsFn W "Bytes::address_eq" [x_rb, xrb] m136 v181 m184 cs192)
    (evOrd : ObsFn W "KernelRoles::assert_in_order" [x_rc, xrb] m184 v_ord m184' cs_ord)
    (ev231 : ObsFn W "KernelModeled::get_count" [x_s1] m184' (.tuple [x_n_a, x_s2]) m219 cs229)
    (ev266 : ObsFn W "KernelModeled::get_addrs" [x_s2, x_n_a] m219 (.tuple [x_advice, x_s3]) m254
      cs264)
    (ev309 : ObsFn W "KernelModeled::get_count" [x_s3] m254 (.tuple [x_n_w, x_s4]) m297 cs307)
    (ev344 : ObsFn W "KernelModeled::check_witnesses" [x_rc, xb, x_s4, x_n_w] m297
      (.tuple [x_outside, x_s5]) m332 cs342) :
    ∃ bytes : List UInt8, Ingress.Stream m332 bytes x_s5 := by
  obtain ⟨-, b0, hs0⟩ := read_payload_stream ev126
  obtain ⟨a, rem, x_t, x_s1', -, htup, -, hs1, -, -⟩ := Decl.get_address_spec hs0 ev148
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  rw [← htup.2] at hs1
  obtain ⟨b2, hs2⟩ :=
    get_count_stream ((hs1.mono ev194.heap_extends).mono evOrd.heap_extends) ev231
  obtain ⟨-, -, b3, -, -, -, hs3, -⟩ := Decl.get_addrs_spec hs2 ev266
  obtain ⟨b4, hs4⟩ := get_count_stream hs3 ev309
  exact check_witnesses_stream hs4 ev344

private theorem repMutConst_heapMono' : HeapMono₂ Ingress.RepMutConst :=
  fun _ _ _ _ ext r => Ingress.RepMutConst.mono ext r

/-- **The tables of a family check, from the steps that build them**: the block's load
(`Ingress::load_verified_constant`), identified with the block's record; the types
(`Ingress::build_recur_addrs`), the constructors (`block_ctor_addrs`) and the recursors
(`family_recs`) with their counts (`Lists::length`); a model for each, read off the payload
(`get_addrs`, three times, at the counts); and the two tables (`Lists::concat`, twice each). The
counts are the lists' lengths because a loaded record's resource size is below `2^33`. Also: the
recursors' count, and the payload is a stream where the rules' theorems start. -/
theorem family_tables {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {b b' : Bytes.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ (ixAddr b) cb ms) (hR : FamRecRecord E₀ (ixAddr b') crb rs)
    {xb xrb x_members w538 w539 w540 w541 v588 v621 v651 v673 x_s5 x_type_models x_s6 v746 v798
      x_ctor_models x_s7 v839 v861 x_rec_models x_s8 v941 v926 v992 v977 rc v_nr v_ntr : SourceValue F}
    {bytes : List UInt8}
    {m453 m501 m589 m624 m652 m674 m704 m747 m807 m784 m840 m840' m840'' m862 m884 m950 m927 m1001
      m978 : Heap F}
    {cs511 cs599 cs632 cs662 cs684 cs714 cs757 cs815 cs794 cs850 cs_nr cs_ntr cs872 cs894 cs958 cs937
      cs1009 cs988 : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy m453 b xb) (hrb : Bytes.RepAddressRef addrTy m453 b' xrb)
    (hs5 : Ingress.Stream m453 bytes x_s5)
    (ev513 : ObsFn W "Ingress::load_verified_constant" [xb] m453
      (.construct "Ixon::Constant" "Mk"
        [.construct "Ixon::ConstantInfo" "Muts" [x_members], w538, w539, w540, w541]) m501 cs511)
    (ev601 : ObsFn W Obs.Names.«Lists::length<Ixon::MutConst>» [x_members] m501 v588 m589 cs599)
    (ev634 : ObsFn W "KernelModeled::muts_indc_count" [x_members] m589 v621 m624 cs632)
    (ev664 : ObsFn W "KernelModeled::block_nparams" [x_members] m624 v651 m652 cs662)
    (ev686 : ObsFn W "Ingress::build_recur_addrs" [x_members, xb] m652 v673 m674 cs684)
    (ev716 : ObsFn W "KernelModeled::get_addrs" [x_s5, v588] m674 (.tuple [x_type_models, x_s6])
      m704 cs714)
    (ev759 : ObsFn W "KernelModeled::block_ctor_addrs" [x_members, xb, .field 0] m704 v746 m747
      cs757)
    (ev817 : ObsFn W Obs.Names.«Lists::length<&[Field; 32]>» [v746] m747 v798 m807 cs815)
    (ev796 : ObsFn W "KernelModeled::get_addrs" [x_s6, v798] m807 (.tuple [x_ctor_models, x_s7])
      m784 cs794)
    (ev852 : ObsFn W "KernelModeled::family_recs" [xrb] m784 v839 m840 cs850)
    (evNoRole : ObsFn W "KernelModeled::assert_no_role" [rc, v839] m840 v_nr m840' cs_nr)
    (evNoTypeRole : ObsFn W "KernelModeled::assert_no_type_role" [rc, v673] m840' v_ntr m840'' cs_ntr)
    (ev874 : ObsFn W Obs.Names.«Lists::length<&[Field; 32]>» [v839] m840'' v861 m862 cs872)
    (ev896 : ObsFn W "KernelModeled::get_addrs" [x_s7, v861] m862 (.tuple [x_rec_models, x_s8])
      m884 cs894)
    (ev960 : ObsFn W Obs.Names.«Lists::concat<&[Field; 32]>» [v746, v839] m884 v941 m950 cs958)
    (ev939 : ObsFn W Obs.Names.«Lists::concat<&[Field; 32]>» [v673, v941] m950 v926 m927 cs937)
    (ev1011 : ObsFn W Obs.Names.«Lists::concat<&[Field; 32]>» [x_ctor_models, x_rec_models] m927
      v992 m1001 cs1009)
    (ev990 : ObsFn W Obs.Names.«Lists::concat<&[Field; 32]>» [x_type_models, v992] m1001 v977 m978
      cs988)
    (hsub511 : ∀ cl ∈ cs511, cl ∈ calls) (hsub850 : ∀ cl ∈ cs850, cl ∈ calls)
    (hbd : Bounded cs757) :
    ∃ typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address,
      FamilyTables (ixAddr b) (ixAddr b') ms rs m978 typeAs ctorAs recAs typeMs ctorMs recMs
        v673 v746 v839 x_type_models x_ctor_models x_rec_models v926 v977 ∧
      v861 = .field (recAs.length : F) ∧ ∃ bytes' : List UInt8, Ingress.Stream m978 bytes' x_s8 := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  have x874 : Heap.Extends m840 m862 :=
    evNoRole.heap_extends.trans (evNoTypeRole.heap_extends.trans ev874.heap_extends)
  -- the block
  obtain ⟨cb', ms', hbl, hrep⟩ := Claim.load_block_head hb ev513
  obtain ⟨hrec, hinfo⟩ := (hbl.mono hsub511).stored hH
  have e1 : cb = cb' := Option.some.inj (hB.record.symm.trans hrec)
  subst e1
  have e2 : ms = ms' := Ixon.ConstantInfo.muts.inj (hB.muts.symm.trans hinfo)
  subst e2
  have hres : cb.resourceSize < 8589934592 := ((hbl.mono hsub511).record hS hB.record).2
  have hsz : ms.size ≤ cb.resourceSize := Claim.muts_size_le hB.muts
  have hsum := muts_sum_le hB.muts
  have hlen_ms : ms.toList.length = ms.size := Array.length_toList
  -- the heaps
  have X927 : Heap.Extends m927 m978 := ev1011.heap_extends.trans ev990.heap_extends
  have X884 : Heap.Extends m884 m978 :=
    ev960.heap_extends.trans (ev939.heap_extends.trans X927)
  have X840 : Heap.Extends m840 m978 := x874.trans (ev896.heap_extends.trans X884)
  have X784 : Heap.Extends m784 m978 := ev852.heap_extends.trans X840
  have X747 : Heap.Extends m747 m978 := ev817.heap_extends.trans (ev796.heap_extends.trans X784)
  have X704 : Heap.Extends m704 m978 := ev759.heap_extends.trans X747
  have X674 : Heap.Extends m674 m978 := ev716.heap_extends.trans X704
  have x652 : Heap.Extends m501 m652 :=
    ev601.heap_extends.trans (ev634.heap_extends.trans ev664.heap_extends)
  have x704 : Heap.Extends m501 m704 :=
    x652.trans (ev686.heap_extends.trans ev716.heap_extends)
  have x784 : Heap.Extends m704 m784 :=
    ev759.heap_extends.trans (ev817.heap_extends.trans ev796.heap_extends)
  -- the count of the members
  have ev601' : ObsFn W (Instance.mk "Lists::length" [.named "Ixon::MutConst" []]).symbol
      [x_members] m501 v588 m589 cs599 := by
    rw [Obs.Names.«Lists::length<Ixon::MutConst>».symbol]; exact ev601
  have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::MutConst" []]).symbol
      Ingress.RepMutConst m501 ms.toList x_members := by
    rw [Obs.Names.«Lists::Node<Ixon::MutConst>».symbol]; exact hrep
  obtain ⟨hv588, -⟩ := Lib.Lists.length_spec ev601' hl'
  subst hv588
  -- the types
  have hmems := Route.membersRep_of_repMutConstList
    (RepLinkedList.mono repMutConst_heapMono' x652 hrep)
  obtain ⟨-, typeAs, htA, htmap⟩ := Ingress.build_recur_addrs_spec hmems
    (Bytes.repAddressRef_heapMono₂ addrTy (ev513.heap_extends.trans x652) hb) ev686
  have htlen : typeAs.length = ms.toList.length := by
    have e := congrArg List.length htmap
    simpa only [List.length_map, List.length_mapIdx] using e
  obtain ⟨nT, typeMs, bT, hnT, hlenT, htM, hs6, -⟩ := Decl.get_addrs_spec
    (hs5.mono (ev513.heap_extends.trans (x652.trans ev686.heap_extends))) ev716
  injection hnT with hnT'
  have hT : typeMs.length = typeAs.length := by
    rw [hlenT, ← hnT', SubstAux.val_natCast (n := ms.toList.length) (by omega), htlen]
  -- the constructors
  have ev759' : ObsFn W "KernelModeled::block_ctor_addrs"
      [x_members, xb, .field ((0 : Nat) : F)] m704 v746 m747 cs757 := by
    rw [Nat.cast_zero]
    exact ev759
  obtain ⟨ctorAs, hcA, hcmap, -⟩ := block_ctor_addrs_spec ms.toList 0 (by omega)
    (fun ind hi => by
      obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.mp hi
      have := Claim.ctors_size_le hB.muts hi'
      omega)
    hbd (Bytes.repAddressRef_heapMono₂ addrTy (ev513.heap_extends.trans x704) hb)
    (RepLinkedList.mono repMutConst_heapMono' x704 hrep) ev759'
  have hclen : ctorAs.length < 8589934592 := by
    have e := congrArg List.length hcmap
    rw [List.length_map] at e
    have := ctorAddrsFrom_length_le (ixAddr b) ms.toList 0
    omega
  obtain ⟨hv798, -⟩ := Decl.addrList_length_spec hcA ev817
  subst hv798
  obtain ⟨nC, ctorMs, bC, hnC, hlenC, hcM, hs7, -⟩ := Decl.get_addrs_spec
    (hs6.mono (ev759.heap_extends.trans ev817.heap_extends)) ev796
  injection hnC with hnC'
  have hC : ctorMs.length = ctorAs.length := by
    rw [hlenC, ← hnC', SubstAux.val_natCast (n := ctorAs.length) (by omega)]
  -- the recursors
  have hrb784 : Bytes.RepAddressRef addrTy m784 b' xrb :=
    Bytes.repAddressRef_heapMono₂ addrTy (ev513.heap_extends.trans (x704.trans x784)) hrb
  obtain ⟨recAs, hrA, hrmap⟩ := family_recs_list hH hrb784 ev852 hsub850 hR
  have hrsz := family_recs_bound hS hH hrb784 ev852 hsub850 hR
  have hrlen : recAs.length = rs.size := by
    have e := congrArg List.length hrmap
    simpa only [List.length_map, List.length_mapIdx, Array.length_toList] using e
  obtain ⟨hv861, -⟩ := Decl.addrList_length_spec
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (evNoRole.heap_extends.trans evNoTypeRole.heap_extends) hrA) ev874
  subst hv861
  obtain ⟨nR, recMs, bR, hnR, hlenR, hrM, hs8, -⟩ := Decl.get_addrs_spec
    (hs7.mono (ev852.heap_extends.trans x874)) ev896
  injection hnR with hnR'
  have hR' : recMs.length = recAs.length := by
    rw [hlenR, ← hnR', SubstAux.val_natCast (n := recAs.length) (by omega)]
  -- the two tables
  have hsrc1 := Decl.addrList_concat_spec
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (ev817.heap_extends.trans (ev796.heap_extends.trans (ev852.heap_extends.trans
        (x874.trans ev896.heap_extends)))) hcA)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (x874.trans ev896.heap_extends) hrA) ev960
  have hsrc := Decl.addrList_concat_spec
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (ev716.heap_extends.trans (ev759.heap_extends.trans (ev817.heap_extends.trans
        (ev796.heap_extends.trans (ev852.heap_extends.trans (x874.trans
          (ev896.heap_extends.trans ev960.heap_extends))))))) htA) hsrc1 ev939
  have hdst1 := Decl.addrList_concat_spec
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (ev852.heap_extends.trans (x874.trans (ev896.heap_extends.trans
        (ev960.heap_extends.trans ev939.heap_extends)))) hcM)
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (ev960.heap_extends.trans ev939.heap_extends) hrM) ev1011
  have hdst := Decl.addrList_concat_spec
    (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (ev759.heap_extends.trans (ev817.heap_extends.trans (ev796.heap_extends.trans
        (ev852.heap_extends.trans (x874.trans (ev896.heap_extends.trans
          (ev960.heap_extends.trans (ev939.heap_extends.trans ev1011.heap_extends)))))))) htM)
    hdst1 ev990
  refine ⟨typeAs, ctorAs, recAs, typeMs, ctorMs, recMs,
    { typesRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) X674 htA
      ctorsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) X747 hcA
      recsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) X840 hrA
      typeModelsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) X704 htM
      ctorModelsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) X784 hcM
      recModelsRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) X884 hrM
      srcRep := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) X927 hsrc
      dstRep := hdst
      types := htmap
      ctors := hcmap
      recs := hrmap
      typeModels := hT
      ctorModels := hC
      recModels := hR' }, rfl, bR, hs8.mono X884⟩

/-- **`KernelModeled::block_nparams`** reads the parameter count of the block's first inductive
member as a field element below `2^56`. -/
theorem block_nparams_spec {h h' : Heap F} {ms : Array Ixon.MutConst}
    {x_members r : SourceValue F} {cs : List (Call F)}
    (hrep : RepList Obs.Names.«Lists::Node<Ixon::MutConst>» Ingress.RepMutConst h ms.toList x_members)
    (ev : ObsFn W "KernelModeled::block_nparams" [x_members] h r h' cs) :
    ∀ ind₀, ms[0]? = some (.indc ind₀) →
      ind₀.params.toNat < 72057594037927936 ∧ r = .field (ind₀.params.toNat : F) := by
  match Obs.«KernelModeled::block_nparams».obs ev with
  | .run (x_params := x_params) (v102 := v102) (ld12 := ld12) (ev115 := ev115) (he173 := hr) .. =>
    obtain ⟨m0, rest, hms_cons, hm0_rep, -⟩ := Lib.rep_cons_of_load hrep ld12
    intro ind₀ h0
    have hm0_eq : m0 = .indc ind₀ := by
      have h0' : ms.toList[0]? = some (.indc ind₀) := by rw [Array.getElem?_toList]; exact h0
      rw [hms_cons] at h0'
      exact Option.some.inj h0'
    subst hm0_eq
    obtain ⟨iv, hiv_eq, typPtr, ctorsPtr, hind_eq, -, -⟩ := hm0_rep
    injection hiv_eq with _ _ hargs1
    injection hargs1 with hiv _
    rw [hind_eq] at hiv
    injection hiv with _ _ hargs2
    injection hargs2 with _ hargs2
    injection hargs2 with _ hargs2
    injection hargs2 with hparams_eq _
    rw [hparams_eq] at ev115
    obtain ⟨hlt, hval, -⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value h ind₀.params) ev115
    rw [hr]
    exact ⟨hlt, hval⟩

/-- **The tables of an observed family check** (`family_tables` at the check's unfolding), at a
heap that extends the check's. The calls of the check are among the run's; the check's own calls
are good for some context. -/
theorem check_family_tables {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {b b' : Bytes.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ (ixAddr b) cb ms) (hR : FamRecRecord E₀ (ixAddr b') crb rs)
    {rc xb xrb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h b xb) (hrb : Bytes.RepAddressRef addrTy h b' xrb)
    (ev : ObsFn W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (hbd : Bounded cs) :
    ∃ (m : Heap F) (typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address)
      (xtA xcA xrA xtM xcM xrM xsrc xdst : SourceValue F),
      Heap.Extends h m ∧
      FamilyTables (ixAddr b) (ixAddr b') ms rs m typeAs ctorAs recAs typeMs ctorMs recMs
        xtA xcA xrA xtM xcM xrM xsrc xdst := by
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (sg112 := sg) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := evOrd) (ev231 := ev231)
      (ev266 := ev266) (ev309 := ev309) (ev344 := ev344) (ev403 := ev403) (ev435 := ev435)
      (ev465 := ev465) (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
      (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817) (ev796 := ev796)
      (ev852 := ev852) (ev_ursqbimm := evNoRole) (ev_srfmazjk := evNoTypeRole) (ev874 := ev874) (ev896 := ev896)
      (ev960 := ev960) (ev939 := ev939)
      (ev1011 := ev1011) (ev990 := ev990) (hc1474 := hc) .. =>
    have e0 := Decl.check_family_seg1_inv sg
    have x874 : Heap.Extends _ _ :=
      evNoRole.heap_extends.trans (evNoTypeRole.heap_extends.trans ev874.heap_extends)
    have x332 := ev126.heap_extends.trans (ev148.heap_extends.trans (ev194.heap_extends.trans
      (evOrd.heap_extends.trans
      (ev231.heap_extends.trans (ev266.heap_extends.trans (ev309.heap_extends.trans
        ev344.heap_extends))))))
    have x453 := ev403.heap_extends.trans (ev435.heap_extends.trans ev465.heap_extends)
    obtain ⟨bytes, hs5⟩ :=
      family_payload_stream ev126 ev148 ev194 evOrd ev231 ev266 ev309 ev344
    obtain ⟨typeAs, ctorAs, recAs, typeMs, ctorMs, recMs, T, -, -⟩ := family_tables hS hH hB hR
      (Bytes.repAddressRef_heapMono₂ addrTy (e0.trans (x332.trans x453)) hb)
      (Bytes.repAddressRef_heapMono₂ addrTy (e0.trans (x332.trans x453)) hrb)
      (hs5.mono x453) ev513 ev601 ev634 ev664 ev686 ev716 ev759 ev817 ev796 ev852 evNoRole
      evNoTypeRole ev874
      ev896
      ev960 ev939 ev1011 ev990
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      (bounded_sub (fun cl hcl => by rw [hc]; simp [hcl]) hbd)
    exact ⟨_, typeAs, ctorAs, recAs, typeMs, ctorMs, recMs, _, _, _, _, _, _, _, _,
      e0.trans (x332.trans (x453.trans (ev513.heap_extends.trans (ev601.heap_extends.trans
        (ev634.heap_extends.trans (ev664.heap_extends.trans (ev686.heap_extends.trans
          (ev716.heap_extends.trans (ev759.heap_extends.trans (ev817.heap_extends.trans
            (ev796.heap_extends.trans (ev852.heap_extends.trans (x874.trans
              (ev896.heap_extends.trans (ev960.heap_extends.trans (ev939.heap_extends.trans
                (ev1011.heap_extends.trans ev990.heap_extends))))))))))))))))), T⟩

/-! ## The family's constant addresses are in `src` -/

/-- **A constant address of the block or of the family record is in `src`**: a member of the
block is among its types, a constructor among its constructors, a member of the family record
among its recursors; the family record has no constructor (its members are recursors). -/
theorem famAddr_mem_src {E₀ : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    {h : Heap F} {typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address}
    {xtA xcA xrA xtM xcM xrM xsrc xdst : SourceValue F}
    (T : FamilyTables B rb ms rs h typeAs ctorAs recAs typeMs ctorMs recMs xtA xcA xrA xtM xcM
      xrM xsrc xdst)
    {x : _root_.Address} (hx : FamAddr B cb rb crb x) :
    x ∈ (typeAs ++ (ctorAs ++ recAs)).map ixAddr := by
  rw [List.map_append, List.map_append, T.types, T.ctors, T.recs]
  rcases hx with ⟨⟨-, hs⟩ | ⟨ms', i, m, hms, hm, hxm⟩⟩ | ⟨⟨-, hs⟩ | ⟨rs', i, m, hrs, hm, hxm⟩⟩
  · exact (standalone_not_block hs ⟨ms, hB.muts⟩).elim
  · have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hms.symm.trans hB.muts)
    subst e
    have hm' : ms'.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
    rcases hxm with rfl | ⟨ind, j, rfl, hj, rfl⟩
    · have hget : (ms'.toList.mapIdx fun i m =>
          projAddr (Specs.Callees.memberProjInfo B i m))[i]? = some (memberAddr B i m) := by
        rw [List.getElem?_mapIdx, hm']
        simp [LoadedReads.memberAddr_eq_projAddr]
      exact List.mem_append_left _ (List.mem_of_getElem? hget)
    · refine List.mem_append_right _ (List.mem_append_left _ ?_)
      have := mem_ctorAddrsFrom B ms'.toList 0 i ind j hm' hj
      rw [Nat.zero_add] at this
      rw [LoadedReads.ctorAddr_eq_cprjAddr]
      exact this
  · exact (standalone_not_block hs ⟨rs, hR.muts⟩).elim
  · have e : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hR.muts)
    subst e
    have hm' : rs'.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
    rcases hxm with rfl | ⟨ind, j, rfl, hj, rfl⟩
    · have hget : (rs'.toList.mapIdx fun i m =>
          projAddr (Specs.Callees.memberProjInfo rb i m))[i]? = some (memberAddr rb i m) := by
        rw [List.getElem?_mapIdx, hm']
        simp [LoadedReads.memberAddr_eq_projAddr]
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_of_getElem? hget))
    · obtain ⟨r', hr'⟩ := hR.recrs _ (List.mem_of_getElem? hm')
      cases hr'

end IxVM.Refinement.Typing.FamilyAlias
