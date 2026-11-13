import IxVMRefinement.Callees.PutConstant
import IxVMRefinement.Core.RomBound
import IxVMRefinement.L1.Blake3
import IxVMRefinement.Obs.Ingress0
import IxVMRefinement.Obs.KernelCheck9

/-! # Projection-record addresses and BLAKE3 hashing

Step lemmas for:
* `Blake3::bytes_to_addr`: hashes a represented byte stream (`RepBytes`) under `Good` and stores
  its 32-byte BLAKE3 digest (`Address.blake3Pure`);
* `KernelCheck::projection_addr_ctor`: builds, serializes, and hashes the constructor-projection
  record `(i, j, block)` (`cprjAddr`);
* `Ingress::build_recur_addrs`: builds, serializes, and hashes the member-projection records of a
  mutual block in order (`projAddr (memberProjInfo ...)`). -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ProjAddrAux

theorem blake3Pure_eq_ixAddr (bytes : List UInt8) :
    Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr (Blake3.Pure.digest bytes) := by
  first
  | rfl
  | (simp [Address.blake3Pure, Blake3.Pure.hash, ixAddr]; done)
  | (unfold Address.blake3Pure Blake3.Pure.hash ixAddr; simp)

end ProjAddrAux

/-- `Blake3::bytes_to_addr`: hashes a represented byte list under `Good` and returns a pointer
to its 32-byte BLAKE3 digest. -/
theorem bytes_to_addr_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Blake3::bytes_to_addr" args h r h' calls) :
    ∀ bp (bytes : List UInt8), args = [bp] → Good c calls → RepBytes h bytes bp →
      ∃ a : Bytes.Address, RepAddr h' a r ∧ ixAddr a = Address.blake3Pure ⟨bytes.toArray⟩ := by
  intro bp bytes hargs good hbytes
  subst hargs
  have hstream : L1.Stream h bytes bp := by
    change Bytes.RepByteStream L1.byteStreamEnum h bytes bp
    have e : (L1.byteStreamEnum : String) = byteListEnum := rfl
    rw [e]
    exact hbytes
  obtain ⟨v1, m2, cs12, v23, m24, cs31, ev14, he27, hm26, ev33, hc42⟩ :=
    Obs.«Blake3::bytes_to_addr».obs ev
  obtain ⟨-, rfl⟩ := L1.hash_spec hstream ev14
  obtain ⟨rfl, hm24⟩ := L1.digest_bytes_spec ev33
  subst m24
  have hcall : (⟨"Blake3::hash", [bp], h⟩ : Call F) ∈ calls := by
    rw [hc42]; simp
  have hlen : bytes.length < 2 ^ 39 :=
    RomBound.bounded_length_lt good.2 hcall (by simp) hbytes
  have hnat : Blake3.Pure.NativeInput bytes := by
    show bytes.length < 2 ^ 64
    omega
  let d : Bytes.Address := Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes)
  have hd_eq : d = Blake3.Pure.digest bytes :=
    Aiur.Library.Blake3.hash_model_spec bytes hnat
  have hty : (L1.digestV d).type = addrTy := by
    simp [L1.digestV, L1.bv, addrTy, Value.type, List.map_map]
  refine ⟨d, ?_, ?_⟩
  · refine ⟨m2.length, L1.digestV d, ?_, ?_, ?_⟩
    · rw [he27, hty]
    · rw [hm26]; simp
    · simp [L1.digestV, L1.bv]
  · rw [hd_eq, ProjAddrAux.blake3Pure_eq_ixAddr]

/-- `KernelCheck::projection_addr_ctor`: builds, serializes, and hashes the constructor-projection
record `(i, j, block)` (`cprjAddr`). -/
theorem projection_addr_ctor_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::projection_addr_ctor" args h r h' calls) :
    Specs.Callees.projection_addr_ctor c args h r h' calls := by
  intro i j bp b hargs good hb
  subst hargs
  obtain ⟨v1, m2, cs12, v23, m24, cs34, m114, m127, m140, m153, v165, m166, cs176, m189, cs204,
    ev14, ev36, hm122, hm135, hm148, hm161, hm197, ev178, ev206, hc215⟩ :=
    Obs.«KernelCheck::projection_addr_ctor».obs ev
  obtain ⟨ni, hni, hxi, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  obtain ⟨nj, hnj, hxj, rfl, hm24⟩ := Lib.u64_from_field_spec ev36
  injection hxi with hxi
  injection hxj with hxj
  have hvali : ZMod.val i = ni := by
    rw [hxi]; exact ProjAddrAux.val_natCast_small (by omega)
  have hvalj : ZMod.val j = nj := by
    rw [hxj]; exact ProjAddrAux.val_natCast_small (by omega)
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
    have e := Lib.repU64_ofNatLT m189 (m := ni) (by omega)
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hrepj : RepU64 m189 (ZMod.val j).toUInt64 (TagN.u64Value nj) := by
    rw [hvalj]
    have e := Lib.repU64_ofNatLT m189 (m := nj) (by omega)
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Specs.Callees.ProjInfoRep m189
      (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "CPrj"
        [.construct "Ixon::ConstructorProj" "Mk" [TagN.u64Value ni, TagN.u64Value nj, bp]]) := by
    simp only [Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value ni, TagN.u64Value nj, bp, b, rfl, hrepi, hrepj,
      Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := put_constant_step c ev178 _ _
    (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩) [] rfl
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  have hgood_bta : Good c cs204 :=
    good.sub (by rw [hc215]; intro x hx; simp [hx])
  obtain ⟨a, ha, haddr⟩ := bytes_to_addr_step c ev206 v165 _ rfl hgood_bta hbytes
  refine ⟨a, ha, ?_⟩
  rw [haddr, ProjAddrAux.bytes_mk_toList]
  rfl

namespace ProjAddrAux

theorem muts_member_at_spec :
    ∀ (k : Nat) {ms : List Ixon.MutConst} {lp r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      (hk : k < ms.length) → ms.length < 2 ^ 39 →
      Specs.Callees.MembersRep h ms lp →
      ObsFn W "Ingress::muts_member_at" [lp, .field (k : F)] h r h' calls →
      Specs.Callees.MutShape h ms[k] r ∧ h' = h := by
  intro k
  induction k with
  | zero =>
    intro ms lp r h h' calls hk _ hms ev
    cases Obs.«Ingress::muts_member_at».obs ev with
    | n0 x_m x_rest ld12 _ rfl rfl _ =>
      obtain ⟨z, zs, he, hz, -⟩ := Lib.rep_cons_of_load hms ld12
      subst he
      exact ⟨hz, rfl⟩
    | other _ _ _ _ _ hne48 _ _ _ =>
      exact absurd (by simp) hne48
  | succ k ih =>
    intro ms lp r h h' calls hk hlen hms ev
    cases Obs.«Ingress::muts_member_at».obs ev with
    | n0 _ _ _ hv43 _ _ _ =>
      have hk0 := natCast_eq_zero_of_lt (m := k + 1) (by omega) (Value.field.inj hv43)
      omega
    | other x_m x_rest cs55 v59 ld12 _ op80 ev57 _ =>
      obtain ⟨z, zs, he, -, hzs⟩ := Lib.rep_cons_of_load hms ld12
      subst he
      have hv59 : v59 = .field (k : F) := by
        rw [Lib.sub_one_inv op80]
        push_cast
        ring_nf
      rw [hv59] at ev57
      simp only [List.length_cons] at hk hlen
      exact ih (by omega) (by omega) hzs ev57

theorem projection_addr_spec (c : Ctx) {ms : List Ixon.MutConst} {b : Bytes.Address}
    {i : Nat} {lp bp r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hi : i < ms.length) (hlen : ms.length < 2 ^ 39)
    (good : Good c calls)
    (hms : Specs.Callees.MembersRep h ms lp)
    (hb : RepAddr h b bp)
    (ev : ObsFn W "Ingress::projection_addr" [lp, bp, .field (i : F)] h r h' calls) :
    ∃ a : Bytes.Address, RepAddr h' a r ∧
      ixAddr a = projAddr (Specs.Callees.memberProjInfo (ixAddr b) i ms[i]) := by
  obtain ⟨v1, m2, cs12, v31, m32, cs42, v198, m199, cs201, m231, m244, m257, m270, v282, m283,
    cs293, m306, cs321, ev14, ev44, sg206, hm239, hm252, hm265, hm278, hm314, ev295, ev323,
    hc332⟩ := Obs.«Ingress::projection_addr».obs ev
  obtain ⟨hmem, rfl⟩ := muts_member_at_spec i hi hlen hms ev14
  obtain ⟨ni, hni, hxi, rfl, rfl⟩ := Lib.u64_from_field_spec ev44
  injection hxi with hxi
  have hni_eq : ni = i := by
    have hv := congrArg ZMod.val hxi
    rw [val_natCast_small (by omega), val_natCast_small (by omega)] at hv
    exact hv.symm
  subst hni_eq
  have e1 : Heap.Extends m199 m231 := by rw [hm239]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m231 m244 := by rw [hm252]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m244 m257 := by rw [hm265]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m257 m270 := by rw [hm278]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m270 m306 := by rw [hm314]; exact Heap.Extends.snoc _ _
  have c1 : m306[m199.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm239]; simp)
  have c2 : m306[m231.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm252]; simp)
  have c3 : m306[m244.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm265]; simp)
  have c4 : m306[m257.length]? = some (.construct Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm278]; simp)
  have c5 : m306[m270.length]? = some (.construct byteListEnum "Nil" []) := by
    rw [hm314]; simp
  have hrepi : RepU64 m306 i.toUInt64 (TagN.u64Value i) := by
    have e := Lib.repU64_ofNatLT m306 (m := i) (by omega)
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hseg : m199 = h ∧
      Specs.Callees.ProjInfoRep m306
        (Specs.Callees.memberProjInfo (ixAddr b) i ms[i]) v198 := by
    rcases hmem with ⟨x, hmc⟩
    cases hmi : ms[i] with
    | defn d =>
      rw [hmi, Specs.Callees.mutCtor] at hmc
      cases sg206 with
      | Defn _ _ rfl rfl _ =>
        have E : Heap.Extends m199 m306 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
        refine ⟨rfl, ?_⟩
        simp only [Specs.Callees.memberProjInfo, Specs.Callees.ProjInfoRep]
        exact ⟨TagN.u64Value i, bp, b, rfl, hrepi, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
      | Indc _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Recr _ _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
    | indc d =>
      rw [hmi, Specs.Callees.mutCtor] at hmc
      cases sg206 with
      | Defn _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Indc _ _ _ rfl rfl _ =>
        have E : Heap.Extends m199 m306 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
        refine ⟨rfl, ?_⟩
        simp only [Specs.Callees.memberProjInfo, Specs.Callees.ProjInfoRep]
        exact ⟨TagN.u64Value i, bp, b, rfl, hrepi, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
      | Recr _ _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
    | recr d =>
      rw [hmi, Specs.Callees.mutCtor] at hmc
      cases sg206 with
      | Defn _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Indc _ _ hv _ _ _ =>
        rw [hmc] at hv; injection hv with _ hc _; exact absurd hc (by decide)
      | Recr _ _ _ _ rfl rfl _ =>
        have E : Heap.Extends m199 m306 := e1.trans (e2.trans (e3.trans (e4.trans e5)))
        refine ⟨rfl, ?_⟩
        simp only [Specs.Callees.memberProjInfo, Specs.Callees.ProjInfoRep]
        exact ⟨TagN.u64Value i, bp, b, rfl, hrepi, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := put_constant_step c ev295 _ _
    (Specs.Callees.memberProjInfo (ixAddr b) i ms[i]) [] rfl
    ⟨_, _, _, _, _, rfl, hseg.2, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  have hgood_bta : Good c cs321 :=
    good.sub (by rw [hc332]; intro x hx; simp [hx])
  obtain ⟨a, ha, haddr⟩ := bytes_to_addr_step c ev323 v282 _ rfl hgood_bta hbytes
  refine ⟨a, ha, ?_⟩
  rw [haddr, bytes_mk_toList]
  rfl

theorem drop_succ_of_drop_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) {x : α} {rest : List α},
      xs.drop i = x :: rest →
        ∃ (hi : i < xs.length), xs[i] = x ∧ xs.drop (i + 1) = rest := by
  intro xs
  induction xs with
  | nil =>
    intro i x rest h
    simp at h
  | cons y ys ih =>
    intro i x rest h
    cases i with
    | zero =>
      simp only [List.drop_zero, List.cons.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by simp, rfl, rfl⟩
    | succ k =>
      simp only [List.drop_succ_cons] at h
      obtain ⟨hk, hget, hdrop⟩ := ih k h
      exact ⟨by simp [hk], hget, hdrop⟩

theorem mapIdx_cons_eq {α β : Type} (f : Nat → α → β) (x : α) (xs : List α) :
    (x :: xs).mapIdx f = f 0 x :: xs.mapIdx (fun k y => f (k + 1) y) := by
  apply List.ext_getElem?
  intro n
  cases n with
  | zero => simp [List.getElem?_mapIdx]
  | succ k => simp [List.getElem?_mapIdx]

theorem build_recur_addrs_walk_spec (c : Ctx) {ms : List Ixon.MutConst} {b : Bytes.Address}
    {lp bp : SourceValue F} (hlen : ms.length < 2 ^ 39) :
    ∀ (cur : List Ixon.MutConst) {i : Nat} {cur_p r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      ms.drop i = cur →
      Good c calls →
      Specs.Callees.MembersRep h ms lp →
      RepAddr h b bp →
      Specs.Callees.MembersRep h cur cur_p →
      ObsFn W "Ingress::build_recur_addrs_walk" [lp, bp, cur_p, .field (i : F)] h r h' calls →
      ∃ as : List Bytes.Address, RepList addrListEnum RepAddr h' as r ∧
        as.map ixAddr =
          cur.mapIdx fun k m => projAddr (Specs.Callees.memberProjInfo (ixAddr b) (i + k) m) := by
  intro cur
  induction cur with
  | nil =>
    intro i cur_p r h h' calls _ _ _ _ hcur ev
    cases Obs.«Ingress::build_recur_addrs_walk».obs ev with
    | Nil _ he24 hm23 _ =>
      subst he24 hm23
      exact ⟨[], Lib.rep_store_nil h, rfl⟩
    | Cons _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ _ =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hcur ld12
      cases he
  | cons m rest ih =>
    intro i cur_p r h h' calls hdrop good hms hb hcur ev
    cases Obs.«Ingress::build_recur_addrs_walk».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hcur ld12
    | Cons w36 x_rest v55 v56 m58 cs66 m94 cs102 v108 ld12 he51 hm50 ev68 op143 ev104 hc145 =>
      obtain ⟨z, zs, he, -, hrest_rep⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with rfl rfl
      obtain ⟨hi, hmi, hdrop'⟩ := drop_succ_of_drop_cons ms i hdrop
      have hgood1 : Good c cs66 := good.sub (by rw [hc145]; intro x hx; simp [hx])
      have hgood2 : Good c cs102 := good.sub (by rw [hc145]; intro x hx; simp [hx])
      obtain ⟨a, ha, ha_addr⟩ := projection_addr_spec c hi hlen hgood1 hms hb ev68
      rw [hmi] at ha_addr
      have ext1 := ev68.heap_extends
      have hms' : Specs.Callees.MembersRep m58 ms lp :=
        RepLinkedList.mono (fun _ hx => hx) ext1 hms
      have hb' : RepAddr m58 b bp := Bytes.repAddressRef_heapMono₂ addrTy ext1 hb
      have hrest_rep' : Specs.Callees.MembersRep m58 rest x_rest :=
        RepLinkedList.mono (fun _ hx => hx) ext1 hrest_rep
      have hv108 : v108 = .field ((i + 1 : Nat) : F) := by
        rw [add_field_inv op143]
        push_cast
        rfl
      rw [hv108] at ev104
      obtain ⟨as_tail, has_tail, hmap_tail⟩ :=
        ih hdrop' hgood2 hms' hb' hrest_rep' ev104
      have ha' : RepAddr m94 a v55 := Bytes.repAddressRef_heapMono₂ addrTy ev104.heap_extends ha
      subst he51 hm50
      refine ⟨a :: as_tail,
        Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy) ha' has_tail, ?_⟩
      rw [List.map_cons, ha_addr, hmap_tail, mapIdx_cons_eq]
      simp only [Nat.add_zero]
      congr 1
      apply List.ext_getElem?
      intro k
      simp only [List.getElem?_mapIdx]
      cases rest[k]? with
      | none => rfl
      | some mk =>
        simp only [Option.map_some, Option.some.injEq]
        rw [show i + 1 + k = i + (k + 1) by omega]

end ProjAddrAux

/-- `Ingress::build_recur_addrs`: builds, serializes, and hashes the projection records of a
mutual block's members in order. -/
theorem build_recur_addrs_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "Ingress::build_recur_addrs" args h r h' calls) :
    Specs.Callees.build_recur_addrs c args h r h' calls := by
  intro lp bp ms b hargs good hms hb
  subst hargs
  obtain ⟨cs4, ev6, hc38⟩ := Obs.«Ingress::build_recur_addrs».obs ev
  have hcall : (⟨"Ingress::build_recur_addrs_walk", [lp, bp, lp, .field 0], h⟩ : Call F) ∈ calls := by
    rw [hc38]; simp
  have hlen : ms.length < 2 ^ 39 :=
    RomBound.bounded_length_lt good.2 hcall (by simp) hms
  have hgood4 : Good c cs4 := good.sub (by rw [hc38]; intro x hx; simp [hx])
  have ev6' : ObsFn W "Ingress::build_recur_addrs_walk" [lp, bp, lp, .field ((0 : Nat) : F)]
      h r h' cs4 := by
    simpa using ev6
  obtain ⟨as, has, hmap⟩ :=
    ProjAddrAux.build_recur_addrs_walk_spec c hlen ms (i := 0) (by simp) hgood4 hms hb hms ev6'
  refine ⟨as, has, ?_⟩
  simpa using hmap

end IxVM.Refinement.Core
