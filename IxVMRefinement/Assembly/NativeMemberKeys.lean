import IxVMRefinement.Assembly.NativeReaderKeys
import IxVMRefinement.L1.Ingress

/-! # Local naming conditions for actual block members

Only the particular reconstructed address matters to a member's key. If it is role-bound,
it must resolve to that member in the selected store. For an unbound address reconstruction
suffices. This separates the local coverage obligation from unrelated bound projections.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader

/-- A reconstructed member has the core key when its own bound projection resolves.
No coverage of other bound addresses is assumed. -/
theorem streamContext_memberKey_of_local_resolution {cx : Ctx .anon} {table : RoleTable}
    {prelude : Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ingress.Blobs} {hint : ConstRef _root_.Address → Option ReducibilityHint}
    (context : cx = Admission.streamContext _root_.Address.admissionHash table prelude constants blobs hint)
    (authentic : AuthenticExactStore cx.store) (checked : table.check = .ok ())
    {ref : ConstRef _root_.Address} {address : _root_.Address}
    (unique : ∀ other, resolve cx.store other = some ref → other = address)
    (notSingleton : singletonAt cx.store ref = none)
    (reconstructed : cx.reconstruct ref = some address)
    (boundResolved : ∀ role, (role, address) ∈ table.bound.toList →
      resolve cx.store address = some ref) :
    cx.memberKey ref = .ok (Core.keyOf table address) := by
  subst cx
  let cx := Admission.streamContext _root_.Address.admissionHash table prelude constants blobs hint
  have roles : cx.roles = bindingsOf cx.store table := rfl
  change cx.memberKey ref = _
  cases roleAt : cx.roles.names[ref]? with
  | some key =>
    obtain ⟨role, rfl⟩ := Ix.Cert.ReaderUnits.bindingsOf_keyed cx.store table ref key (by rwa [← roles])
    obtain ⟨other, bound, resolved⟩ := Ix.Cert.ReaderKeys.bindings_role_origin cx.store table (by rwa [← roles])
    have same := unique other resolved
    subst other
    rw [keyOf_eq_of_bound checked bound]
    unfold Ctx.memberKey
    rw [roleAt]
    rfl
  | none =>
    have unbound : ∀ role, (role, address) ∉ table.bound.toList := by
      intro role member
      have named := Ix.Cert.ReadingKeys.bindings_bound checked member (boundResolved role member) unique
      rw [← roles, roleAt] at named
      cases named
    have addressOf : cx.addressOf ref = .ok address := by
      unfold Ctx.addressOf
      cases cached : cx.keys.address[ref]? with
      | some other =>
        rw [unique other (cx.keys.address_sound ref other cached)]
        rfl
      | none =>
        rw [notSingleton, reconstructed]
        rfl
    unfold Ctx.memberKey
    rw [roleAt, addressOf]
    simp only [bind, Except.bind]
    cases cached : cx.keys.byAddress[address]? with
    | none => exact congrArg Except.ok (keyOf_eq_of_unbound unbound).symm
    | some key =>
      have lookup : cx.keyAt address = .ok key := by
        unfold Ctx.keyAt
        rw [cached]
        rfl
      have keyEq := streamContext_keyAt_ok_inv authentic checked lookup
      rw [keyEq]
      rfl

/-- The inductive member's reconstruction is its canonical projection address. -/
theorem projectionAddress_iprj {store : Store} {owner : _root_.Address}
    {source : Ixon.Constant} {members : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive}
    (stored : store owner = some source) (shape : source.info = .muts members)
    (member : members[i]? = some (.indc ind)) (bound : i < UInt64.size) :
    Admission.projectionAddress _root_.Address.admissionHash store (.member owner i) =
      some (Core.iprjAddr owner i) := by
  have roundtrip : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt bound
  have projection := Egress.ProjectionReads.inductive ⟨i.toUInt64, owner⟩
  have reading : Egress.ProjectionReads
      ⟨.iPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ .inductive (.member owner i) := by
    simpa only [roundtrip] using projection
  have written := Egress.writeProjection_of_reading reading
  unfold Admission.projectionAddress
  simp [stored, shape, member, written, Except.toOption, _root_.Address.admissionHash_eq,
    Core.iprjAddr, Core.projAddr]

/-- The recursor member's reconstruction is its canonical projection address. -/
theorem projectionAddress_rprj {store : Store} {owner : _root_.Address}
    {source : Ixon.Constant} {members : Array Ixon.MutConst} {i : Nat} {recursor : Ixon.Recursor}
    (stored : store owner = some source) (shape : source.info = .muts members)
    (member : members[i]? = some (.recr recursor)) (bound : i < UInt64.size) :
    Admission.projectionAddress _root_.Address.admissionHash store (.member owner i) =
      some (Core.rprjAddr owner i) := by
  have roundtrip : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt bound
  have projection := Egress.ProjectionReads.recursor ⟨i.toUInt64, owner⟩
  have reading : Egress.ProjectionReads
      ⟨.rPrj ⟨i.toUInt64, owner⟩, #[], #[], #[], #[]⟩ .recursor (.member owner i) := by
    simpa only [roundtrip] using projection
  have written := Egress.writeProjection_of_reading reading
  unfold Admission.projectionAddress
  simp [stored, shape, member, written, Except.toOption, _root_.Address.admissionHash_eq,
    Core.rprjAddr, Core.projAddr]

/-- An actual mutual member needs resolution only at its own role-bound projection.
This covers the inductive and recursor keys used by native recursive references. -/
theorem streamContext_memberKey_member_of_local_resolution {cx : Ctx .anon} {table : RoleTable}
    {prelude : Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ingress.Blobs} {hint : ConstRef _root_.Address → Option ReducibilityHint}
    (context : cx = Admission.streamContext _root_.Address.admissionHash table prelude constants blobs hint)
    (authentic : AuthenticExactStore cx.store) (checked : table.check = .ok ())
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {i : Nat} {member : Ixon.MutConst}
    (stored : cx.store owner = some source) (shape : source.info = .muts members)
    (memberAt : members[i]? = some member) (bound : i < UInt64.size)
    (boundResolved : ∀ role,
      (role, Core.projAddr (Core.Specs.Callees.memberProjInfo owner i member)) ∈ table.bound.toList →
      resolve cx.store (Core.projAddr (Core.Specs.Callees.memberProjInfo owner i member)) =
        some (.member owner i)) :
    cx.memberKey (.member owner i) =
      .ok (Core.keyOf table (Core.projAddr (Core.Specs.Callees.memberProjInfo owner i member))) := by
  let projection : Ixon.Constant :=
    ⟨Core.Specs.Callees.memberProjInfo owner i member, #[], #[], #[], #[]⟩
  have projectionAt : Ix.Cert.ReadingKeys.projectionAt cx.store (.member owner i) = some projection := by
    cases member <;> simp [Ix.Cert.ReadingKeys.projectionAt, Ix.Cert.ReadingKeys.memberAt,
      stored, shape, memberAt, projection, Core.Specs.Callees.memberProjInfo]
  have unique : ∀ other, resolve cx.store other = some (.member owner i) →
      other = Core.projAddr (Core.Specs.Callees.memberProjInfo owner i member) := by
    intro other resolved
    unfold resolve at resolved
    obtain ⟨value, found, sourceRead⟩ := Option.bind_eq_some_iff.mp resolved
    rcases Ix.Cert.ReadingKeys.resolveSource_cases sourceRead with ⟨sameRef, notBlock⟩ | projected
    · injection sameRef with ownerEq _
      subst other
      have sameValue := Option.some.inj (found.symm.trans stored)
      subst value
      exact (notBlock members shape).elim
    · rw [projectionAt] at projected
      injection projected with valueEq
      subst value
      obtain ⟨bytes, hashed, decoded⟩ := authentic other projection found
      have projectionFacts := projectionAt_empty_and_proj projectionAt
      have encoded := (deConstantExact_proj_eq_serConstant decoded projectionFacts.1 projectionFacts.2).1
      rw [encoded] at hashed
      exact hashed.symm
  have notSingleton : singletonAt cx.store (.member owner i) = none := by
    cases i with
    | zero => simp [singletonAt, stored, shape]
    | succ _ => rfl
  have reconstructed : cx.reconstruct (.member owner i) =
      some (Core.projAddr (Core.Specs.Callees.memberProjInfo owner i member)) := by
    rw [context]
    change Admission.projectionAddress _root_.Address.admissionHash
      (Admission.streamContext _root_.Address.admissionHash table prelude constants blobs hint).store
        (.member owner i) = _
    have stored' := stored
    rw [context] at stored'
    cases member with
    | defn value => exact projectionAddress_dprj stored' shape memberAt bound
    | indc value => exact projectionAddress_iprj stored' shape memberAt bound
    | recr value => exact projectionAddress_rprj stored' shape memberAt bound
  exact streamContext_memberKey_of_local_resolution context authentic checked unique notSingleton
    reconstructed boundResolved

/-- One recursive-reference occurrence needs the key of its own selected member. The
occurrence supplies its projected address and wire index; only that bound projection needs
resolution in the reader store. -/
theorem streamContext_block_self_key_at {cx : Ctx .anon} {table : RoleTable}
    {prelude : Prelude .anon} {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ingress.Blobs} {hint : ConstRef _root_.Address → Option ReducibilityHint}
    (context : cx = Admission.streamContext _root_.Address.admissionHash table prelude constants blobs hint)
    (authentic : AuthenticExactStore cx.store) (checked : table.check = .ok ())
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    (stored : cx.store owner = some source) (shape : source.info = .muts members)
    {index : Nat} {address : _root_.Address} {reading : ReadM (Key .anon)} {key : Key .anon}
    (bound : index < UInt64.size)
    (addressAt : (L1.blockRecurAddrs owner members.toList)[index]? = some address)
    (callback : (if index < members.size then some (cx.memberKey (.member owner index)) else none) =
      some reading)
    (read : reading = .ok key)
    (boundResolved : ∀ role, (role, address) ∈ table.bound.toList →
      resolve cx.store address = some (.member owner index)) :
    key = Core.keyOf table address := by
  have inside : index < members.size := by
    have present := (List.getElem?_eq_some_iff.mp addressAt).1
    simpa [L1.blockRecurAddrs_eq_mapIdx] using present
  have memberAt : members[index]? = some members[index] := Array.getElem?_eq_getElem inside
  have projected : (L1.blockRecurAddrs owner members.toList)[index]? =
      some (Core.projAddr (Core.Specs.Callees.memberProjInfo owner index members[index])) := by
    rw [L1.blockRecurAddrs_eq_mapIdx]
    rw [List.getElem?_eq_getElem (by simpa using inside), List.getElem_mapIdx]
    simp only [Array.getElem_toList]
  have addressEq : address = Core.projAddr (Core.Specs.Callees.memberProjInfo owner index members[index]) :=
    Option.some.inj (addressAt.symm.trans projected)
  have called : cx.memberKey (.member owner index) = .ok key := by
    have callbackEq : cx.memberKey (.member owner index) = reading := by
      simpa only [inside, ↓reduceIte, Option.some.injEq] using callback
    exact callbackEq.trans read
  have named := streamContext_memberKey_member_of_local_resolution context authentic checked
    stored shape memberAt bound (by rwa [← addressEq])
  rw [← addressEq] at named
  exact Except.ok.inj (called.symm.trans named)


end IxVM.Refinement.Assembly
