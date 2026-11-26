import IxVMRefinement.FamilyAlias.CallRekey
import IxVM.Obs.KernelModeled
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Callees.RouteDispatch
import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Ingress.Ingress
import IxVMRefinement.Assembly.FamilyFold

/-! # The address lists `check_family` renames over

`KernelModeled::check_family` renames over `src`, the concatenation of three address lists: the
block's types (`Ingress::build_recur_addrs` of the block's members), its constructors
(`KernelModeled::block_ctor_addrs`) and the family record's recursors
(`KernelModeled::family_recs`). This module reads each list off its function, as the addresses
it represents:

* `member_ctor_addrs_spec`: the constructor addresses of one inductive member, from a position
  on (`KernelCheck::projection_addr_ctor` at each);
* `block_ctor_addrs_spec`: the constructor addresses of the block's inductive members in order
  (`ctorAddrsFrom`);
* `family_recs_list`: the addresses of the members of a family record that is a block of
  recursors (`Ingress::build_recur_addrs` of its members). -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false

/-! ## A member's constructors -/

private theorem bytes_to_addr_bounded {bp r : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "Blake3::bytes_to_addr" [bp] h r h' calls)
    (hbd : Bounded calls) (hbytes : RepBytes h bytes bp) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = Address.blake3Pure ⟨bytes.toArray⟩ := by
  have hstream : Ingress.Stream h bytes bp := by
    change Bytes.RepByteStream IxVM.Refinement.byteStreamEnum h bytes bp
    have e : (IxVM.Refinement.byteStreamEnum : String) = byteListEnum := rfl
    rw [e]
    exact hbytes
  obtain ⟨v1, m2, cs12, v23, m24, cs31, ev14, he27, hm26, ev33, hc42⟩ :=
    Obs.«Blake3::bytes_to_addr».obs ev
  obtain ⟨-, rfl⟩ := Ingress.hash_spec hstream ev14
  obtain ⟨rfl, hm24⟩ := Ingress.digest_bytes_spec ev33
  subst m24
  have hcall : (⟨"Blake3::hash", [bp], h⟩ : Call F) ∈ calls := by
    rw [hc42]; simp
  have hlen : bytes.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbd hcall (by simp) hbytes
  have hnat : Blake3.Pure.NativeInput bytes := Nat.lt_trans hlen (by decide)
  let d : Bytes.Address := Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes)
  have hd_eq : d = Blake3.Pure.digest bytes :=
    Aiur.Library.Blake3.hash_model_spec bytes hnat
  have hty : (Ingress.digestV d).type = addrTy := by
    have hf : (Value.type ∘ Ingress.bv : UInt8 → Aiur.Ty) = fun _ => .field :=
      funext fun b => by rw [Function.comp_apply, Ingress.bv, Value.type]
    rw [Ingress.digestV, Ingress.type_tuple, List.map_map, hf, List.map_const', Vector.length_toList]
  refine ⟨d, ?_, ?_⟩
  · refine ⟨m2.length, Ingress.digestV d, ?_, ?_, ?_⟩
    · rw [he27]; exact congrArg (fun t => Value.ptr t m2.length) hty
    · rw [hm26, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    · exact Ingress.repAddress_iff.mpr rfl
  · rw [hd_eq, ProjAddrAux.blake3Pure_eq_ixAddr]

theorem projection_addr_ctor_bounded {i j : F} {bp r : SourceValue F}
    {b : Bytes.Address} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::projection_addr_ctor" [.field i, .field j, bp] h r h' calls)
    (hbd : Bounded calls) (hb : Bytes.RepAddressRef addrTy h b bp) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j) := by
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  obtain ⟨v1, m2, cs12, v23, m24, cs34, m114, m127, m140, m153, v165, m166, cs176, m189, cs204,
    ev14, ev36, hm122, hm135, hm148, hm161, hm197, ev178, ev206, hc215⟩ :=
    Obs.«KernelCheck::projection_addr_ctor».obs ev
  obtain ⟨ni, hni, hxi, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  obtain ⟨nj, hnj, hxj, rfl, hm24⟩ := Lib.u64_from_field_spec ev36
  injection hxi with hxi
  injection hxj with hxj
  have hvali : ZMod.val i = ni := by
    rw [hxi]; exact SubstAux.val_natCast (by omega)
  have hvalj : ZMod.val j = nj := by
    rw [hxj]; exact SubstAux.val_natCast (by omega)
  have e1 : Heap.Extends m24 m114 := by rw [hm122]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m114 m127 := by rw [hm135]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m127 m140 := by rw [hm148]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m140 m153 := by rw [hm161]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m153 m189 := by rw [hm197]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m189 := by
    rw [← hm2, ← hm24]
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m189[m24.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm122]; simp)
  have c2 : m189[m114.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm135]; simp)
  have c3 : m189[m127.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm148]; simp)
  have c4 : m189[m140.length]? = some (.construct Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm161]; simp)
  have c5 : m189[m153.length]? = some (.construct byteListEnum "Nil" []) := by
    rw [hm197]; simp
  have hrepi : RepU64 m189 (ZMod.val i).toUInt64 (TagN.u64Value ni) := by
    rw [hvali]
    have e := Lib.repU64_ofNatLT m189 (m := ni) (Nat.lt_trans hni (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hrepj : RepU64 m189 (ZMod.val j).toUInt64 (TagN.u64Value nj) := by
    rw [hvalj]
    have e := Lib.repU64_ofNatLT m189 (m := nj) (Nat.lt_trans hnj (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Specs.Callees.ProjInfoRep m189
      (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [TagN.u64Value ni, TagN.u64Value nj, bp]]) := by
    simp only [Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value ni, TagN.u64Value nj, bp, b, rfl, hrepi, hrepj,
      Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  let c0 : ScopedCtx := ScopedCtx.unrestricted ⟨{}, .empty, default, none⟩
  have hbytes := put_constant_step c0 ev178 _ _
    (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩) [] rfl
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  rw [List.append_nil] at hbytes
  obtain ⟨a, ha, haddr⟩ := bytes_to_addr_bounded ev206
    (bounded_sub (by rw [hc215]; intro x hx; simp [hx]) hbd) hbytes
  refine ⟨a, ha, ?_⟩
  rw [haddr, Array.toArray_toList]
  rfl

/-- **`KernelModeled::member_ctor_addrs`**: from position `j` on, `cnt` constructor addresses of
the member at `p` of the block at `b`, in order. -/
theorem member_ctor_addrs_spec {b : Bytes.Address} {xb : SourceValue F} {p n : F} :
    ∀ (cnt j : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      j + cnt = ZMod.val n → Bounded cs → Bytes.RepAddressRef addrTy h b xb →
      ObsFn W "KernelModeled::member_ctor_addrs" [xb, .field p, .field n, .field (j : F)] h r h'
        cs →
      ∃ as : List Bytes.Address, RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as r ∧
        as.map ixAddr = (List.range' j cnt).map (cprjAddr (ixAddr b) (ZMod.val p)) ∧
        Heap.Extends h h'
  | 0, j, r, h, h', cs, hjn, hbd, hb, ev => by
    rcases Obs.«KernelModeled::member_ctor_addrs».obs ev with
      ⟨op, hr, hh, -⟩ | ⟨v1, v45, v46, m48, cs56, m84, cs92, v98, op, hne, hr, hh, ev58, op133,
        ev94, hc⟩
    · subst hr hh
      exact ⟨[], Lib.rep_store_nil h, rfl, Heap.Extends.snoc _ _⟩
    · exfalso
      have hnj : n = (j : F) := by
        have e := SubstAux.natCast_val n
        rw [← hjn, Nat.add_zero] at e
        exact e.symm
      exact hne (by rw [SubstAux.sub_ok op, hnj, sub_self])
  | cnt + 1, j, r, h, h', cs, hjn, hbd, hb, ev => by
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hlt := ZMod.val_lt n
    have hjv : ZMod.val (j : F) = j := SubstAux.val_natCast (by omega)
    rcases Obs.«KernelModeled::member_ctor_addrs».obs ev with
      ⟨op, hr, hh, -⟩ | ⟨v1, v45, v46, m48, cs56, m84, cs92, v98, op, hne, hr, hh, ev58, op133,
        ev94, hc⟩
    · exfalso
      have e := SubstAux.sub_ok op
      have hnj : n = (j : F) := sub_eq_zero.mp (Value.field.inj e).symm
      rw [hnj, hjv] at hjn
      omega
    · subst hr hh hc
      obtain ⟨a, ha, hax⟩ := projection_addr_ctor_bounded ev58
        (bounded_sub (fun x hx => by simp [hx]) hbd) hb
      have e98 : v98 = .field ((j + 1 : Nat) : F) := by
        rw [SubstAux.add_ok op133, Nat.cast_succ]
      subst e98
      have x1 := ev58.heap_extends
      obtain ⟨as, has, hmap, x2⟩ := member_ctor_addrs_spec cnt (j + 1) (by omega)
        (bounded_sub (fun x hx => by simp [hx]) hbd)
        (Bytes.repAddressRef_heapMono₂ addrTy x1 hb) ev94
      refine ⟨a :: as, Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
        (Bytes.repAddressRef_heapMono₂ addrTy x2 ha) has, ?_,
        x1.trans (x2.trans (Heap.Extends.snoc _ _))⟩
      rw [List.range'_succ, List.map_cons, List.map_cons, hmap, hax, hjv]

/-! ## The block's constructors -/

private theorem repMutConst_heapMono : HeapMono₂ Ingress.RepMutConst :=
  fun _ _ _ _ ext r => Ingress.RepMutConst.mono ext r

/-- **The constructor addresses of a block's inductive members from position `p` on**, member by
member, each member's in order. -/
def ctorAddrsFrom (B : _root_.Address) : List Ixon.MutConst → Nat → List _root_.Address
  | [], _ => []
  | .indc ind :: rest, p =>
    (List.range ind.ctors.size).map (cprjAddr B p) ++ ctorAddrsFrom B rest (p + 1)
  | _ :: rest, p => ctorAddrsFrom B rest (p + 1)

/-- **`KernelModeled::block_ctor_addrs`**: the constructor addresses of the block's members from
position `p` on (`ctorAddrsFrom`). The members are read as the block's load represents them; the
bounds hold at a loaded record, whose resource size is below `2^33` (`Claim.BlockLoad.record`,
`Claim.muts_size_le`, `Claim.ctors_size_le`). -/
theorem block_ctor_addrs_spec {b : Bytes.Address} {xb : SourceValue F} :
    ∀ (ms : List Ixon.MutConst) (p : Nat) {x_members r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      p + ms.length < 1099511627776 →
      (∀ ind, Ixon.MutConst.indc ind ∈ ms → ind.ctors.size < 1099511627776) →
      Bounded cs → Bytes.RepAddressRef addrTy h b xb →
      RepList Ingress.mutConstListEnum Ingress.RepMutConst h ms x_members →
      ObsFn W "KernelModeled::block_ctor_addrs" [x_members, xb, .field (p : F)] h r h' cs →
      ∃ as : List Bytes.Address, RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as r ∧
        as.map ixAddr = ctorAddrsFrom (ixAddr b) ms p ∧ Heap.Extends h h'
  | [], p, x_members, r, h, h', cs, hp, hsz, hbd, hb, hms, ev => by
    match Obs.«KernelModeled::block_ctor_addrs».obs ev with
    | .Nil (he24 := hr) (hm23 := hm) .. =>
      subst hr hm
      exact ⟨[], Lib.rep_store_nil h, rfl, Heap.Extends.snoc _ _⟩
    | .Cons (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hms ld
      cases he
  | m :: rest, p, x_members, r, h, h', cs, hp, hsz, hbd, hb, hms, ev => by
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    match Obs.«KernelModeled::block_ctor_addrs».obs ev with
    | .Nil (ld12 := ld) .. =>
      exact absurd (Lib.rep_nil_of_load hms ld) (List.cons_ne_nil _ _)
    | .Cons (x_ctors := x_ctors) (v124 := v124) (m127 := m127) (cs135 := cs135) (v140 := v140)
        (m157 := m157) (cs165 := cs165) (v196 := v196) (ld12 := ld)
        (ev167 := e1) (ev137 := e2) (op224 := op) (ev193 := e3) (ev123 := e4) (hc226 := hc) .. =>
      subst hc
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load hms ld
      injection heq with h1 h2
      subst h1 h2
      cases m with
      | defn d =>
        obtain ⟨dv, hv, -⟩ := hm
        simp at hv
      | recr r' =>
        obtain ⟨rv, hv, -⟩ := hm
        simp at hv
      | indc ind =>
        obtain ⟨iv, hv, hind⟩ := hm
        injection hv with _ _ hargs
        injection hargs with hiv _
        subst hiv
        obtain ⟨typPtr, ctorsPtr, hv2, -, hctors⟩ := hind
        injection hv2 with _ _ hargs2
        have hx : x_ctors = ctorsPtr := by
          have e := congrArg (fun l : List (SourceValue F) => l.getD 5 (.field 0)) hargs2
          simpa using e
        subst hx
        have e1' : ObsFn W (Instance.mk "Lists::length" [.named "Ixon::Constructor" []]).symbol
            [x_ctors] h v140 m157 cs165 := by
          rw [Obs.Names.«Lists::length<Ixon::Constructor>».symbol]
          exact e1
        have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::Constructor" []]).symbol
            Ingress.RepConstructor h ind.ctors.toList x_ctors := by
          rw [Obs.Names.«Lists::Node<Ixon::Constructor>».symbol]
          exact hctors
        obtain ⟨hv140, hm157⟩ := Lib.Lists.length_spec e1' hl'
        subst hv140
        subst m157
        have hsz0 : ind.ctors.size < 1099511627776 := hsz ind (List.mem_cons_self ..)
        have hlen : ind.ctors.toList.length = ind.ctors.size := Array.length_toList
        have hpv : ZMod.val (p : F) = p := SubstAux.val_natCast (by simp at hp; omega)
        have e2' : ObsFn W "KernelModeled::member_ctor_addrs"
            [xb, .field (p : F), .field (ind.ctors.toList.length : F), .field ((0 : Nat) : F)]
            h v124 m127 cs135 := by
          rw [Nat.cast_zero]
          exact e2
        have x2 := e2.heap_extends
        obtain ⟨as₁, has₁, hmap₁, -⟩ := member_ctor_addrs_spec
          ind.ctors.toList.length 0
          (by rw [SubstAux.val_natCast (n := ind.ctors.toList.length) (by omega)]; omega)
          (bounded_sub (fun x hx => by simp [hx]) hbd) hb e2'
        have e196 : v196 = .field ((p + 1 : Nat) : F) := by
          rw [SubstAux.add_ok op, Nat.cast_succ]
        subst e196
        have x3 := e3.heap_extends
        obtain ⟨as₂, has₂, hmap₂, -⟩ := block_ctor_addrs_spec rest (p + 1)
          (by simp at hp; omega)
          (fun ind' hi => hsz ind' (List.mem_cons_of_mem _ hi))
          (bounded_sub (fun x hx => by simp [hx]) hbd)
          (Bytes.repAddressRef_heapMono₂ addrTy x2 hb)
          (RepLinkedList.mono repMutConst_heapMono x2 hrest) e3
        refine ⟨as₁ ++ as₂, Decl.addrList_concat_spec
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) x3 has₁) has₂ e4, ?_,
          x2.trans (x3.trans e4.heap_extends)⟩
        show _ = (List.range ind.ctors.size).map (cprjAddr (ixAddr b) p) ++
          ctorAddrsFrom (ixAddr b) rest (p + 1)
        rw [List.map_append, hmap₁, hmap₂, hpv, hlen, ← List.range_eq_range']

/-! ## The family record's recursors -/

/-- **`KernelModeled::family_recs` at a family record that is a block of recursors**: the
addresses of its members' projection records, in order (`Ingress::build_recur_addrs`). -/
theorem family_recs_list {calls : List (Call F)} {E₀ : Ixon.Env}
    (hH : LoadedReads.HashedRecordsStored calls E₀) {b : Bytes.Address} {x_rb v : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hb : Bytes.RepAddressRef addrTy h b x_rb)
    (ev : ObsFn W "KernelModeled::family_recs" [x_rb] h v h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hrb : FamRecRecord E₀ (ixAddr b) crb rs) :
    ∃ as : List Bytes.Address, RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as v ∧
      as.map ixAddr = rs.toList.mapIdx fun i m =>
        projAddr (Specs.Callees.memberProjInfo (ixAddr b) i m) := by
  match Obs.«KernelModeled::family_recs».obs ev with
  | .Muts (m2 := m2) (m123 := m123) (cs12 := cs12) (ev14 := ev14) (ev113 := ev113)
      (ev133 := ev133) (ev148 := ev148) (hc165 := hc) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨cb, ms, hbl, hrep⟩ := Claim.load_block_head hb ev14
    obtain ⟨hrec, hinfo⟩ := (hbl.mono hsub12).stored hH
    have e1 : cb = crb := Option.some.inj (hrec.symm.trans hrb.record)
    subst e1
    have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hinfo.symm.trans hrb.muts)
    subst e2
    have ext : Heap.Extends m2 m123 := ev113.heap_extends.trans ev133.heap_extends
    have hmems :=
      Route.membersRep_of_repMutConstList (RepLinkedList.mono repMutConst_heapMono ext hrep)
    have hb2 : Bytes.RepAddressRef addrTy m123 b x_rb :=
      Bytes.repAddressRef_heapMono₂ addrTy (ev14.heap_extends.trans ext) hb
    obtain ⟨-, as, has, hmap⟩ := Ingress.build_recur_addrs_spec hmems hb2 ev148
    exact ⟨as, has, hmap⟩
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

end IxVM.Refinement.Typing.FamilyAlias
