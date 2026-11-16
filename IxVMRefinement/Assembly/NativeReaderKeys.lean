import IxVMRefinement.Assembly.ProjSafe

/-! # Reader member keys for native constructors

Canonical projection reconstruction and authentic record resolution identify the constructor
member key with the key used by the Source role table. No semantic-store premise is required.
-/

namespace IxVM.Refinement.Assembly

/-- A constructor projection is reconstructed at its canonical address. -/
theorem projectionAddress_cprj {store : Ix.Kernel.Reader.Store}
    (owner : _root_.Address) (i j : Nat) (hi : i < UInt64.size) (hj : j < UInt64.size) :
    Ix.Kernel.Admission.projectionAddress _root_.Address.admissionHash store (.ctor owner i j) =
      some (Core.cprjAddr owner i j) := by
  have hi_toNat : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt hi
  have hj_toNat : j.toUInt64.toNat = j := UInt64.toNat_ofNat_of_lt hj
  have reading : Ix.Kernel.Egress.ProjectionReads
      ⟨.cPrj ⟨i.toUInt64, j.toUInt64, owner⟩, #[], #[], #[], #[]⟩ .constructor (.ctor owner i j) := by
    simpa only [hi_toNat, hj_toNat] using
      Ix.Kernel.Egress.ProjectionReads.constructor ⟨i.toUInt64, j.toUInt64, owner⟩
  have written := Ix.Kernel.Egress.writeProjection_of_reading reading
  unfold Ix.Kernel.Admission.projectionAddress
  simp [written, Except.toOption, _root_.Address.admissionHash_eq, Core.cprjAddr, Core.projAddr]

/-- The authentic reader context and Source role table agree on a known constructor's name.
The actual projection-hash observation supplies the stored-projection agreement premise. -/
theorem streamContext_memberKey_cprj {t : Ix.Kernel.RoleTable}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    {constants : List (_root_.Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    (hauth : AuthenticExactStore
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store)
    (hchk : t.check = .ok ())
    {owner : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i j : Nat} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (hcb : (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
      owner = some cb)
    (hinfo : cb.info = .muts ms)
    (hms : ms[i]? = some (.indc ind))
    (hct : ind.ctors[j]? = some ctor) (hindex : ctor.cidx.toNat = j)
    (hi : i < UInt64.size) (hj : j < UInt64.size)
    (hbound_stored : ∀ r a_b, (r, a_b) ∈ t.bound.toList →
      ∃ c_b, (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
        a_b = some c_b)
    (hcprj_eq : ∀ c',
      (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).store
        (Core.cprjAddr owner i j) = some c' →
      c' = ⟨.cPrj ⟨i.toUInt64, j.toUInt64, owner⟩, #[], #[], #[], #[]⟩) :
    (Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint).memberKey
      (.ctor owner i j) = .ok (Core.keyOf t (Core.cprjAddr owner i j)) := by
  let cx := Ix.Kernel.Admission.streamContext _root_.Address.admissionHash t pre constants blobs hint
  change cx.store owner = some cb at hcb
  change cx.memberKey (.ctor owner i j) = .ok (Core.keyOf t (Core.cprjAddr owner i j))
  let c_proj : Ixon.Constant := ⟨.cPrj ⟨i.toUInt64, j.toUInt64, owner⟩, #[], #[], #[], #[]⟩
  have hi_toNat : i.toUInt64.toNat = i := UInt64.toNat_ofNat_of_lt hi
  have hj_toNat : j.toUInt64.toNat = j := UInt64.toNat_ofNat_of_lt hj
  have ctorIndex : ctor.cidx = j.toUInt64 := UInt64.ext (hindex.trans hj_toNat.symm)
  have hres_proj : ∀ {a' : _root_.Address}, cx.store a' = some c_proj →
      Ix.Kernel.Reader.resolve cx.store a' = some (.ctor owner i j) := by
    intro a' ha'
    unfold Ix.Kernel.Reader.resolve Ix.Kernel.Reader.resolveSource
    simp [ha', c_proj, Ix.Kernel.Reader.emptyTables, hcb, hinfo, hi_toNat, hj_toNat, hms, hct, ctorIndex]
  have hres_inv : ∀ {a' : _root_.Address},
      Ix.Kernel.Reader.resolve cx.store a' = some (.ctor owner i j) →
      a' = Core.cprjAddr owner i j := by
    intro a' ha'
    unfold Ix.Kernel.Reader.resolve at ha'
    obtain ⟨c', hc', hsrc⟩ := Option.bind_eq_some_iff.mp ha'
    rcases Ix.Cert.ReadingKeys.resolveSource_cases hsrc with ⟨heq, hns⟩ | hpat
    · cases heq
    · simp only [Ix.Cert.ReadingKeys.projectionAt, Option.some.injEq] at hpat
      rcases hpat with rfl
      obtain ⟨bytes, hbl, hdec⟩ := hauth a' c_proj hc'
      obtain ⟨hbs, _⟩ := deConstantExact_proj_eq_serConstant hdec rfl trivial
      rw [hbs] at hbl
      exact hbl.symm
  have hroles : cx.roles = Ix.Kernel.Reader.bindingsOf cx.store t := rfl
  cases hrole : cx.roles.names[Ix.Kernel.ConstRef.ctor owner i j]? with
  | some k =>
    obtain ⟨r, rfl⟩ := Ix.Cert.ReaderUnits.bindingsOf_keyed cx.store t (.ctor owner i j) k
      (by rwa [← hroles])
    obtain ⟨a', hmem', hres'⟩ := Ix.Cert.ReaderKeys.bindings_role_origin cx.store t
      (by rwa [← hroles])
    have ha'_eq := hres_inv hres'
    subst ha'_eq
    rw [keyOf_eq_of_bound hchk hmem']
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole]
    rfl
  | none =>
    have hunb : ∀ r, (r, Core.cprjAddr owner i j) ∉ t.bound.toList := by
      intro r hm
      obtain ⟨c_b, hc_b⟩ := hbound_stored r (Core.cprjAddr owner i j) hm
      have hc_eq := hcprj_eq c_b hc_b
      subst hc_eq
      have hres_b := hres_proj hc_b
      have hbind := Ix.Cert.ReadingKeys.bindings_bound hchk hm hres_b (fun _ h' => hres_inv h')
      rw [← hroles, hrole] at hbind
      cases hbind
    rw [keyOf_eq_of_unbound hunb]
    have hsing_none : Ix.Kernel.Reader.singletonAt cx.store (.ctor owner i j) = none := rfl
    have hrec_addr : cx.reconstruct (.ctor owner i j) = some (Core.cprjAddr owner i j) :=
      projectionAddress_cprj (store := cx.store) owner i j hi hj
    have ha_of : cx.addressOf (.ctor owner i j) = .ok (Core.cprjAddr owner i j) := by
      unfold Ix.Kernel.Reader.Ctx.addressOf
      cases haddr : cx.keys.address[Ix.Kernel.ConstRef.ctor owner i j]? with
      | some a' =>
        have hsnd := cx.keys.address_sound (.ctor owner i j) a' haddr
        rw [hres_inv hsnd]
        rfl
      | none =>
        rw [hsing_none, hrec_addr]
        rfl
    have hcompat : Ix.Cert.ReaderKeys.ReconCompatible cx (· = .ctor owner i j) := by
      intro ref a' href _ _ _ hrec hcached
      subst href
      rw [hrec_addr] at hrec
      injection hrec with ha'_eq
      subst ha'_eq
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcached
      have hsnd := cx.keys.byAddress_sound (Core.cprjAddr owner i j) v hv
      cases hst_p : cx.store (Core.cprjAddr owner i j) with
      | none => simp [Ix.Kernel.Reader.keyOfAddress, Ix.Kernel.Reader.resolve, hst_p] at hsnd
      | some c' =>
        have hc' := hcprj_eq c' hst_p
        subst hc'
        exact hres_proj hst_p
    unfold Ix.Kernel.Reader.Ctx.memberKey
    rw [hrole, ha_of]
    simp only [bind, Except.bind]
    cases hby : cx.keys.byAddress[Core.cprjAddr owner i j]? with
    | none => rfl
    | some v =>
      have hres_d := Ix.Cert.ReaderKeys.addressOf_resolves_of_cached hcompat rfl hrole ha_of
        (by rw [hby]; rfl)
      have hsnd := cx.keys.byAddress_sound (Core.cprjAddr owner i j) v hby
      have hv : v = .id (Core.cprjAddr owner i j) := by
        simpa [Ix.Kernel.Reader.keyOfAddress, hres_d, hrole, Ix.Kernel.Mode.addressId?] using hsnd.symm
      rw [hv]
      rfl

end IxVM.Refinement.Assembly
