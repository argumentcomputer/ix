import IxVMRefinement.Assembly.L7
import Ix.Cert.FallbackStore

/-! # Role-aware sub-store construction, `RolePreludeInputs`, multi-walk union, and `coreEnvRole`

Provides the Phase-2 store infrastructure backing `WalkedBareBridgeRole`:

* `RolePreludeInputs`: parametric role-table / committed-fallback interface matching `W4-Roles`'s
  proven exports (`fallbackHashed`, `preludeFor_of_readerTable`,
  `literalSupportBound_of_readerTable`, `fallback_record_agree`, `fallback_blob_agree`,
  `fallback_not_padding`, `prelude_in_bindingSeeds`);
* `TableAdmittedAt` unpacking: authentic bytes, `Ixon.deConstantExact`, `recordAt E_role` on
  `order_role`, `pre.records ⊆ order_role`, and `UsedRecordRef` → `idxOf` decrease on `order_role`;
* `ClosedSubwalk`, `WkAll`, `rankAll`, `SeedReach`, and `closedSubwalk_of_recsClosed`: combines
  `WalkedL6`'s seed closure with `Claim.RecsClosed` sub-walks;
* `addBlobSupplements`, `roleSuppOf`, `subEnvRole`, `roleTwoTierRank`, and `coreEnvRole`: builds
  the combined role+seed store `E` and core-backing store `coreEnvRole`, proving `DrawsRoleLocal`,
  authenticated records/blobs, `UsedClosureOrderAt`, `Core.Good`, and `L1.EnvDecoded`. -/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-! ## Parametric role-prelude interface (`RolePreludeInputs`) -/

/-- Role-validation and committed-fallback facts consumed by `Assembly/Bridge.lean`, matching the
proven exports of `RoleVal/{CommittedData,CommittedPrelude,ReaderTable}.lean` with zero cross-lane
imports and zero kernel hex expansion. -/
structure RolePreludeInputs : Prop where
  fallbackHashed : Ix.Cert.RoleClosure.FallbackHashed
  preludeFor_of_readerTable :
    ∀ {clm : Ix.Claim} {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
      {t : Ix.Kernel.RoleTable},
      IxVM.Consistency.ReaderTable clm V b →
      Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t →
      ∃ pre, Ix.Kernel.Reader.preludeFor (md := .anon) t = .ok pre
  literalSupportBound_of_readerTable :
    ∀ {clm : Ix.Claim} {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
      {t : Ix.Kernel.RoleTable},
      IxVM.Consistency.ReaderTable clm V b →
      Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b = .ok t →
      IxVM.Refinement.LiteralSupportBound t
  fallback_record_agree :
    ∀ {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env},
      (∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra) →
      IxVM.Consistency.LoadedBy calls E₀ →
      ∀ {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon},
        Ix.Kernel.Reader.preludeFor t = .ok pre →
        ∀ {a : _root_.Address} {c : Ixon.Constant}, (a, c) ∈ pre.records ++ pre.evidence →
        ∀ {lc : Ixon.LazyConstant}, E₀.consts.get? a = some lc →
        V.HashedCollision extra calls ∨ (lc.rawBytes = Ixon.serConstant c ∧ c.wireWF)
  fallback_blob_agree :
    ∀ {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env},
      (∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra) →
      IxVM.Consistency.LoadedBy calls E₀ →
      ∀ {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon},
        Ix.Kernel.Reader.preludeFor t = .ok pre →
        ∀ {a : _root_.Address} {blob raw : ByteArray}, (a, blob) ∈ pre.blobs →
        E₀.blobs.get? a = some raw →
        V.HashedCollision extra calls ∨ raw = blob
  fallback_not_padding :
    ∀ {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon},
      Ix.Kernel.Reader.preludeFor t = .ok pre →
      ∀ {a : _root_.Address} {c : Ixon.Constant}, (a, c) ∈ pre.records ++ pre.evidence →
        a ≠ Ix.HostAdmission.Merkle.padding
  prelude_in_bindingSeeds :
    ∀ {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon},
      Ix.Kernel.Reader.preludeFor t = .ok pre →
      ∀ {a : _root_.Address} {c : Ixon.Constant}, (a, c) ∈ pre.records →
        IxVM.Refinement.BindingSeeds t a ∨
        ∃ a' c', (a', c') ∈ pre.records ∧
          IxVM.Refinement.BindingSeeds t a' ∧
          Ix.Cert.ownerOf a' c' = a ∧ a ≠ a'

/-- Every record `(a, c)` in `pre.records ++ pre.evidence` has `Ixon.serConstant c` in
`committedImages`, pure BLAKE3 digest `a`, wire well-formedness `c.wireWF`, and non-padding address
`a ≠ Ix.HostAdmission.Merkle.padding`. -/
theorem RolePreludeInputs.serConstant_mem_committedImages (hRP : RolePreludeInputs)
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence) :
    Ixon.serConstant c ∈ IxVM.Consistency.committedImages ∧
      _root_.Address.blake3Pure (Ixon.serConstant c) = a ∧
      c.wireWF ∧
      a ≠ Ix.HostAdmission.Merkle.padding := by
  obtain ⟨hauth, hwf⟩ := Ix.Cert.FallbackStore.fallback_authentic hRP.fallbackHashed hpre hmem
  rw [_root_.Address.admissionHash_eq] at hauth
  obtain ⟨hr, he⟩ := Ix.Cert.ReaderFallback.preludeFor_records hpre
  have hrow : ∃ row ∈ (Ix.Kernel.Reader.RoleData.prelude ++
      Ix.Kernel.Reader.RoleData.evidence).toList,
      Ix.Kernel.Reader.addressOfHex row.1 = some a ∧
      ∃ raw, bytesOfHex row.2 = some raw ∧
        Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
          Ix.Kernel.Reader.preludeMaxUnivNodes raw = .ok c := by
    rcases Array.mem_append.mp hmem with h1 | h2
    · obtain ⟨row, hrow, hrest⟩ := Ix.Cert.FallbackStore.decoded_rows "prelude"
        Ix.Kernel.Reader.RoleData.prelude hr (a, c) (Array.mem_toList_iff.mpr h1)
      exact ⟨row, by simp [Array.toList_append, hrow], hrest⟩
    · obtain ⟨row, hrow, hrest⟩ := Ix.Cert.FallbackStore.decoded_rows "evidence"
        Ix.Kernel.Reader.RoleData.evidence he (a, c) (Array.mem_toList_iff.mpr h2)
      exact ⟨row, by simp [Array.toList_append, hrow], hrest⟩
  obtain ⟨row, hrow_mem, _, raw, hraw_hex, hde_can⟩ := hrow
  obtain ⟨-, -, hser⟩ := Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hde_can
  have himg : Ixon.serConstant c ∈ IxVM.Consistency.committedImages := by
    rw [hser]
    unfold IxVM.Consistency.committedImages
    rw [List.mem_filterMap]
    refine ⟨row.2, ?_, hraw_hex⟩
    rw [List.mem_map]
    refine ⟨row, ?_, rfl⟩
    rw [Array.toList_append]
    exact List.mem_append_left _ hrow_mem
  exact ⟨himg, hauth.symm, hwf, hRP.fallback_not_padding hpre hmem⟩

/-- Under `¬ V.HashedCollision extra calls` and exact decoding on `E₀`, any record present in `E₀`
at an address of `pre.records ++ pre.evidence` decodes to the committed fallback constant `c`. -/
theorem RolePreludeInputs.fallback_recordAt_agree (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env}
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hnoCol : ¬ V.HashedCollision extra calls)
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence)
    {lc : Ixon.LazyConstant} (hget : E₀.consts.get? a = some lc) :
    lc.rawBytes = Ixon.serConstant c ∧ c.wireWF ∧ Ix.Cert.recordAt E₀ a = some c := by
  rcases hRP.fallback_record_agree hcomm_extra hload hpre hmem hget with hcol | ⟨hraw, hwf⟩
  · exact absurd hcol hnoCol
  · obtain ⟨c', hlc_c', hex⟩ := hexact₀ a lc hget
    rw [hraw, Ixon.Verify.deConstantExact_serConstant c hwf] at hex
    injection hex with hce
    subst hce
    refine ⟨hraw, hwf, ?_⟩
    unfold Ix.Cert.recordAt
    rw [hget]
    exact hlc_c'

/-! ## Unpacking `TableAdmittedAt` (`Authentic`, `RecordsRead`, `pre.records ⊆ order_role`) -/

private theorem recordsRead_mem_spec {limits : Ix.Kernel.Admission.Limits}
    {records : Ix.Kernel.Admission.Records} {constants : Ix.Kernel.Ingress.Constants}
    (h : Ix.Kernel.Admission.RecordsRead limits records constants) :
    ∀ {a : _root_.Address} {raw : ByteArray}, (a, raw) ∈ records →
      ∃ c, (a, c) ∈ constants ∧ Ixon.serConstant c = raw ∧ c.wireWF ∧
        Ixon.deConstantExact raw = .ok c := by
  induction h with
  | nil => intro _ _ hm; nomatch hm
  | cons reads _ ih =>
    intro a raw hm
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq
      have hex := Ixon.Verify.deConstantExact_serConstant _ reads.wire
      rw [reads.encoded] at hex
      exact ⟨_, List.mem_cons_self, reads.encoded, reads.wire, hex⟩
    · obtain ⟨c, hc, hser, hwf, hex⟩ := ih htl
      exact ⟨c, List.mem_cons_of_mem _ hc, hser, hwf, hex⟩

/-- Unpacks `UniqueKeys`, `Authentic`, and `RecordsRead` from `hadm.prepareWith`. -/
theorem TableAdmittedAt.prepareWith_unpack
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role) :
    Ix.Kernel.Admission.UniqueKeys (Ix.Cert.recordsOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) ∧
    Ix.Kernel.Admission.Authentic _root_.Address.admissionHash
      (Ix.Cert.recordsOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) ∧
    ∃ constants, Ix.Kernel.Admission.RecordsRead limits
      (Ix.Cert.recordsOf E_role order_role) constants := by
  have h := hadm.prepareWith
  unfold Ix.Kernel.Admission.prepareWith at h
  cases hf : Ix.Kernel.Admission.preflight limits (Ix.Cert.recordsOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role) with
  | error e => simp [hf, Except.mapError, bind, Except.bind] at h
  | ok _ =>
    cases hu : Ix.Kernel.Admission.uniqueKeys (Ix.Cert.recordsOf E_role order_role)
        (Ix.Cert.blobsOf E_role order_role) with
    | error e => simp [hf, hu, Except.mapError, bind, Except.bind] at h
    | ok _ =>
      cases ha : Ix.Kernel.Admission.authenticate _root_.Address.admissionHash
          (Ix.Cert.recordsOf E_role order_role) (Ix.Cert.blobsOf E_role order_role) with
      | error e => simp [hf, hu, ha, Except.mapError, bind, Except.bind] at h
      | ok _ =>
        cases hb : Ix.Kernel.Admission.admitBinding _root_.Address.admissionHash b with
        | error e => simp [hf, hu, ha, hb, Except.mapError, bind, Except.bind] at h
        | ok _ =>
          cases hd : Ix.Kernel.Admission.decodeRecords limits
              (Ix.Cert.recordsOf E_role order_role) with
          | error e => simp [hf, hu, ha, hb, hd, Except.mapError, bind, Except.bind] at h
          | ok constants =>
            exact ⟨(Ix.Kernel.Admission.uniqueKeys_ok_iff _ _).mp hu,
              (Ix.Kernel.Admission.authenticate_ok_iff _ _ _).mp ha,
              constants, (Ix.Kernel.Admission.decodeRecords_ok_iff _ _ _).mp hd⟩

/-- Every `a ∈ order_role` is stored in `E_role.consts` with pure-BLAKE3 authenticated `rawBytes`,
canonical encoding `serConstant c = lc.rawBytes`, wire-WF `c`, exact decoding
`deConstantExact lc.rawBytes = .ok c`, `recordAt E_role a = some c`, and `V.Preimage a lc.rawBytes`. -/
theorem TableAdmittedAt.order_record_spec
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    {a : _root_.Address} (ha : a ∈ order_role) :
    ∃ lc c, E_role.consts.get? a = some lc ∧
      lc.get? = some c ∧
      Ix.Cert.recordAt E_role a = some c ∧
      _root_.Address.blake3Pure lc.rawBytes = a ∧
      Ixon.serConstant c = lc.rawBytes ∧
      c.wireWF ∧
      Ixon.deConstantExact lc.rawBytes = .ok c ∧
      V.Preimage a lc.rawBytes := by
  obtain ⟨_, hauth, constants, hread⟩ := hadm.prepareWith_unpack
  have hcont := hadm.orderStored a ha
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?] at hcont
  obtain ⟨lc, hget⟩ := Option.isSome_iff_exists.mp hcont
  have hmem_rec : (a, lc.rawBytes) ∈ Ix.Cert.recordsOf E_role order_role := by
    unfold Ix.Cert.recordsOf
    exact List.mem_filterMap.mpr ⟨a, ha, by rw [hget]; rfl⟩
  have hblk : _root_.Address.blake3Pure lc.rawBytes = a := by
    have h1 := hauth.1 (a, lc.rawBytes) hmem_rec
    rw [_root_.Address.admissionHash_eq] at h1
    exact h1.symm
  obtain ⟨c, _, hser, hwf, hex⟩ := recordsRead_mem_spec hread hmem_rec
  obtain ⟨⟨lcV, hgetV, hrawV⟩, hlc_get⟩ := hadm.viewConsts a ha lc hget
  have hlc_c := hlc_get c hex
  have hrecAt : Ix.Cert.recordAt E_role a = some c := by
    unfold Ix.Cert.recordAt
    rw [hget]
    exact hlc_c
  exact ⟨lc, c, hget, hlc_c, hrecAt, hblk, hser, hwf, hex, Or.inl ⟨lcV, hgetV, hrawV⟩⟩

/-- Every `(a, bytes) ∈ blobsOf E_role order_role` has pure-BLAKE3 digest `a`, is stored in
`V.env.blobs` (`V.Preimage a bytes`), and `blobsOf E_role order_role` has distinct keys. -/
theorem TableAdmittedAt.blobs_spec
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role) :
    ((Ix.Cert.blobsOf E_role order_role).map Prod.fst).Nodup ∧
      ∀ a bytes, (a, bytes) ∈ Ix.Cert.blobsOf E_role order_role →
        _root_.Address.blake3Pure bytes = a ∧
        E_role.blobs.get? a = some bytes ∧
        V.env.blobs.get? a = some bytes ∧
        V.Preimage a bytes := by
  obtain ⟨huniq, hauth, _⟩ := hadm.prepareWith_unpack
  refine ⟨huniq.2, fun a bytes hm => ?_⟩
  have hblk : _root_.Address.blake3Pure bytes = a := by
    have h1 := hauth.2 (a, bytes) hm
    rw [_root_.Address.admissionHash_eq] at h1
    exact h1.symm
  unfold Ix.Cert.blobsOf at hm
  obtain ⟨hm_list, _⟩ := List.mem_filter.mp hm
  have hget_role : E_role.blobs.get? a = some bytes := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm_list
  have hget_view := hadm.draws.2 a bytes hget_role
  exact ⟨hblk, hget_role, hget_view, Or.inr (Or.inl hget_view)⟩

/-- At any address `a ∈ order_role` that also appears in `pre.records ++ pre.evidence`, `E_role`
stores the exact committed fallback constant `c_pre`. -/
theorem TableAdmittedAt.order_agrees_with_fallback (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    {a : _root_.Address} {c_pre : Ixon.Constant}
    (ha : a ∈ order_role) (hmem : (a, c_pre) ∈ pre.records ++ pre.evidence) :
    Ix.Cert.recordAt E_role a = some c_pre := by
  obtain ⟨lc, c, _, _, hrecAt, hblk_lc, _, _, hex_lc, hpreV⟩ := hadm.order_record_spec ha
  obtain ⟨himg, hblk_pre, hwf_pre, _⟩ := hRP.serConstant_mem_committedImages hadm.preludeFor hmem
  have hraw_eq := hadm.noCommittedCollision a lc.rawBytes (Ixon.serConstant c_pre)
    hpreV himg hblk_lc hblk_pre
  rw [hraw_eq, Ixon.Verify.deConstantExact_serConstant c_pre hwf_pre] at hex_lc
  injection hex_lc with hceq
  subst hceq
  exact hrecAt

/-- **Every committed prelude record `(a, c) ∈ pre.records` is in `order_role`** and stored as `c`
in `E_role`. -/
theorem TableAdmittedAt.prelude_mem_orderRole (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    {a : _root_.Address} {c : Ixon.Constant} (hmem : (a, c) ∈ pre.records) :
    a ∈ order_role ∧ Ix.Cert.recordAt E_role a = some c := by
  have ha_ord : a ∈ order_role := by
    rcases hRP.prelude_in_bindingSeeds hadm.preludeFor hmem with hb | ⟨a', c', hm', hb', hown, hne⟩
    · exact (hadm.closureOrder.complete a).mpr (.seed hb (hadm.seeds_in a hb))
    · have ha'_reach : Ix.Cert.CompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t) a' :=
        .seed hb' (hadm.seeds_in a' hb')
      have ha'_ord : a' ∈ order_role := (hadm.closureOrder.complete a').mpr ha'_reach
      have hrec' := hadm.order_agrees_with_fallback hRP ha'_ord (Array.mem_append_left _ hm')
      exact (hadm.closureOrder.complete a).mpr
        (.step ha'_reach ⟨c', hrec', Or.inl ⟨hown, hne⟩⟩)
  exact ⟨ha_ord, hadm.order_agrees_with_fallback hRP ha_ord (Array.mem_append_left _ hmem)⟩

/-! ## `ClosedSubwalk` union (`WkAll`, `rankAll`) across `WalkedL6` and `RecsClosed` sub-walks -/

/-- A `WalkEdge`-closed, rank-decreasing, checked subset of `E₀`. -/
structure ClosedSubwalk (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (W : _root_.Address → Prop) (rk : _root_.Address → Nat) : Prop where
  step : ∀ x y, W x → Core.S0.WalkEdge E₀ x y → W y ∧ rk y < rk x
  checked : ∀ x, W x → ∃ c, Ix.Cert.recordAt E₀ x = some c ∧
    ((∃ ms, c.info = .muts ms ∧
      ∀ (k : Nat), k < ms.size → Claim.MutsMemberCheckedAtFull calls bAddr t x ms k) ∨
     Claim.CheckedAtFull calls bAddr t x)

/-- Union of all `ClosedSubwalk`s for `(calls, bAddr, t, E₀)`. -/
def WkAll (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (x : _root_.Address) : Prop :=
  ∃ W rk, ClosedSubwalk calls bAddr t E₀ W rk ∧ W x

/-- Safe walked subset of `E₀`: in `WkAll` and not `OutsideLogicAt E₀`. -/
def WkSafe (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (x : _root_.Address) : Prop :=
  WkAll calls bAddr t E₀ x ∧ ¬ IxVM.Consistency.OutsideLogicAt E₀ x

private theorem wkAll_exists_nat {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {x : _root_.Address}
    (h : WkAll calls bAddr t E₀ x) :
    ∃ n : Nat, ∃ W rk, ClosedSubwalk calls bAddr t E₀ W rk ∧ W x ∧ rk x = n := by
  obtain ⟨W, rk, hcs, hwx⟩ := h
  exact ⟨rk x, W, rk, hcs, hwx, rfl⟩

/-- Minimum rank across all `ClosedSubwalk`s containing `x` (`0` outside `WkAll`). -/
noncomputable def rankAll (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (x : _root_.Address) : Nat :=
  letI := Classical.propDecidable
  if h : ∃ n : Nat, ∃ W rk, ClosedSubwalk calls bAddr t E₀ W rk ∧ W x ∧ rk x = n then
    Nat.find h
  else 0

theorem wkAll_of_closedSubwalk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {W : _root_.Address → Prop}
    {rk : _root_.Address → Nat}
    (hcs : ClosedSubwalk calls bAddr t E₀ W rk) {x : _root_.Address} (hx : W x) :
    WkAll calls bAddr t E₀ x :=
  ⟨W, rk, hcs, hx⟩

theorem rankAll_le_of_closedSubwalk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {W : _root_.Address → Prop}
    {rk : _root_.Address → Nat}
    (hcs : ClosedSubwalk calls bAddr t E₀ W rk) {x : _root_.Address} (hx : W x) :
    rankAll calls bAddr t E₀ x ≤ rk x := by
  classical
  have hex : ∃ n : Nat, ∃ W' rk', ClosedSubwalk calls bAddr t E₀ W' rk' ∧ W' x ∧ rk' x = n :=
    ⟨rk x, W, rk, hcs, hx, rfl⟩
  simp only [rankAll, hex, ↓reduceDIte]
  exact Nat.find_min' hex ⟨W, rk, hcs, hx, rfl⟩

/-- `(WkAll, rankAll)` is itself a `ClosedSubwalk`. -/
theorem wkAll_closedSubwalk (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) :
    ClosedSubwalk calls bAddr t E₀
      (WkAll calls bAddr t E₀) (rankAll calls bAddr t E₀) where
  step x y hx hedge := by
    classical
    have hex := wkAll_exists_nat hx
    have hfind := Nat.find_spec hex
    obtain ⟨W, rk, hcs, hwx, hrk_eq⟩ := hfind
    have hrk_all : rankAll calls bAddr t E₀ x = Nat.find hex := by
      simp only [rankAll, hex, ↓reduceDIte]
    obtain ⟨hwy, hlt⟩ := hcs.step x y hwx hedge
    have hle := rankAll_le_of_closedSubwalk hcs hwy
    exact ⟨⟨W, rk, hcs, hwy⟩, by omega⟩
  checked x hx := by
    obtain ⟨W, rk, hcs, hwx⟩ := hx
    exact hcs.checked x hwx

/-- If `WkSafe` holds at `x` and `ownerOf x cx ≠ x` (`recordAt E₀ x = some cx`), then `WkSafe` and
strict `rankAll` decrease hold at `ownerOf x cx` provided `ownerOf (ownerOf x cx) cb = ownerOf x cx`
(which holds whenever `cb` is not itself a projection, e.g., `.muts`). -/
theorem wkSafe_owner_of_nonproj {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {x : _root_.Address} {cx : Ixon.Constant}
    (hx : WkSafe calls bAddr t E₀ x) (hrec : Ix.Cert.recordAt E₀ x = some cx)
    (hne : Ix.Cert.ownerOf x cx ≠ x)
    (hcb_own : ∀ cb, Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf x cx) = some cb →
      Ix.Cert.ownerOf (Ix.Cert.ownerOf x cx) cb = Ix.Cert.ownerOf x cx) :
    WkSafe calls bAddr t E₀ (Ix.Cert.ownerOf x cx) ∧
      rankAll calls bAddr t E₀ (Ix.Cert.ownerOf x cx) < rankAll calls bAddr t E₀ x := by
  have hedge : Core.S0.WalkEdge E₀ x (Ix.Cert.ownerOf x cx) :=
    ⟨cx, hrec, Or.inl ⟨rfl, hne⟩⟩
  obtain ⟨hwk_own, hlt⟩ := (wkAll_closedSubwalk calls bAddr t E₀).step x _ hx.1 hedge
  refine ⟨⟨hwk_own, ?_⟩, hlt⟩
  rintro ⟨cb, hrec_cb, hbad⟩
  apply hx.2
  refine ⟨cx, hrec, Or.inr ⟨cb, hrec_cb, ?_⟩⟩
  rcases hbad with hnin | ⟨cb2, hrec2, hnin2⟩
  · exact hnin
  · rw [hcb_own cb hrec_cb] at hrec2
    rw [hrec_cb] at hrec2
    injection hrec2 with heq
    subst heq
    exact hnin2

/-- `(Wk, rank)` from `WalkedL6` directly forms a `ClosedSubwalk`. -/
theorem closedSubwalk_of_walked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hwk_step : ∀ a b, Wk a → Core.S0.WalkEdge E₀ a b → Wk b ∧ rank b < rank a)
    (hwk_chk : ∀ a, Wk a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧
      ((∃ ms, c.info = .muts ms ∧
        ∀ (k : Nat), k < ms.size → Claim.MutsMemberCheckedAtFull calls bAddr t a ms k) ∨
       Claim.CheckedAtFull calls bAddr t a)) :
    ClosedSubwalk calls bAddr t E₀ Wk rank :=
  { step := hwk_step, checked := hwk_chk }

private def minNatList : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: rest =>
    let m := minNatList (y :: rest)
    if x ≤ m then x else m

private theorem minNatList_le_of_mem : ∀ {xs : List Nat} {a : Nat}, a ∈ xs → minNatList xs ≤ a
  | [], _, h => nomatch h
  | [x], a, h => by
    rcases List.mem_singleton.mp h with rfl
    exact Nat.le_refl _
  | x :: y :: rest, a, h => by
    simp only [minNatList]
    rcases List.mem_cons.mp h with rfl | htl
    · split_ifs <;> omega
    · have ih := minNatList_le_of_mem htl
      split_ifs <;> omega

private theorem minNatList_mem_of_ne_nil : ∀ {xs : List Nat}, xs ≠ [] → minNatList xs ∈ xs
  | [], h => absurd rfl h
  | [x], _ => List.mem_cons_self
  | x :: y :: rest, _ => by
    simp only [minNatList]
    have hrec : minNatList (y :: rest) ∈ y :: rest := minNatList_mem_of_ne_nil (by simp)
    split_ifs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hrec

/-- Rank of `a` inside a `WalkedRec` list `recs` (`min` of `r.depth` at `r.addr = a`). -/
def recsRank {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    (recs : List (Claim.WalkedRec calls bAddr t)) (a : _root_.Address) : Nat :=
  minNatList ((recs.filter (fun r => r.addr == a)).map (·.depth))

/-- Any `Claim.RecsClosed` list `recs` forms a `ClosedSubwalk` on `E₀`. -/
theorem closedSubwalk_of_recsClosed {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (hconsts_complete : ∀ bytes c, IxVM.Refinement.Hashed calls bytes →
      bytes.size < 4294967296 → Ixon.deConstant bytes = .ok c →
      Ixon.deConstantExact bytes = .ok c →
      ∃ lc, E₀.consts.get? (_root_.Address.blake3Pure bytes) = some lc ∧
        lc.rawBytes = bytes ∧ lc.get? = some c)
    (recs : List (Claim.WalkedRec calls bAddr t))
    (hcl : Claim.RecsClosed recs) :
    ClosedSubwalk calls bAddr t E₀ (fun a => a ∈ recs.map (·.addr)) (recsRank recs) := by
  have hrecAt : ∀ r ∈ recs, Ix.Cert.recordAt E₀ r.addr = some r.c := by
    intro r hr
    obtain ⟨lc, hget, _, hlc_c⟩ :=
      hconsts_complete r.rawBytes r.c r.hhashed r.hsz r.hde r.hdeExact
    rw [r.hblake] at hget
    unfold Ix.Cert.recordAt
    rw [hget]
    exact hlc_c
  refine {
    step := fun a b ha ⟨c, hrec_a, hstep⟩ => ?_
    checked := fun a ha => ?_
  }
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp ha
    have hne : ((recs.filter (fun r => r.addr == r₀.addr)).map (·.depth)) ≠ [] := by
      intro hemp
      have hm : r₀.depth ∈ (recs.filter (fun r => r.addr == r₀.addr)).map (·.depth) :=
        List.mem_map.mpr ⟨r₀, List.mem_filter.mpr ⟨hr₀, beq_self_eq_true _⟩, rfl⟩
      rw [hemp] at hm
      cases hm
    obtain ⟨r_min, hr_filt, hdep⟩ := List.mem_map.mp (minNatList_mem_of_ne_nil hne)
    obtain ⟨hr_mem, hr_beq⟩ := List.mem_filter.mp hr_filt
    have hr_addr : r_min.addr = r₀.addr := beq_iff_eq.mp hr_beq
    have hrec_min := hrecAt r_min hr_mem
    rw [hr_addr, hrec_a] at hrec_min
    injection hrec_min with hc_eq
    obtain ⟨hown, hrefs⟩ := hcl r_min hr_mem
    rw [hr_addr, ← hc_eq] at hown
    rw [← hc_eq] at hrefs
    rcases hstep with ⟨rfl, hne_own⟩ | ⟨i, hi, hb⟩
    · obtain ⟨r', hr', ha', hlt'⟩ := hown hne_own
      have hle' : recsRank recs r'.addr ≤ r'.depth :=
        minNatList_le_of_mem
          (List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', beq_self_eq_true _⟩, rfl⟩)
      rw [ha'] at hle'
      exact ⟨List.mem_map.mpr ⟨r', hr', ha'⟩, by unfold recsRank at hle' ⊢; omega⟩
    · obtain ⟨r', hr', ha', hlt'⟩ := hrefs i hi b hb
      have hle' : recsRank recs r'.addr ≤ r'.depth :=
        minNatList_le_of_mem
          (List.mem_map.mpr ⟨r', List.mem_filter.mpr ⟨hr', beq_self_eq_true _⟩, rfl⟩)
      rw [ha'] at hle'
      exact ⟨List.mem_map.mpr ⟨r', hr', ha'⟩, by unfold recsRank at hle' ⊢; omega⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact ⟨r.c, hrecAt r hr, r.hchecked⟩

/-! ## Blob supplements (`addBlobSupplements`) and role supplements (`roleSuppOf`) -/

/-- Overlay blob entries `(a, bytes)` at addresses not already present in `m₀`. -/
def addBlobSupplements (m₀ : Std.HashMap _root_.Address ByteArray) :
    List (_root_.Address × ByteArray) → Std.HashMap _root_.Address ByteArray
  | [] => m₀
  | (a, bytes) :: rest =>
    let tail := addBlobSupplements m₀ rest
    if m₀.contains a then tail else tail.insert a bytes

theorem addBlobSupplements_get?_of_contains (m₀ : Std.HashMap _root_.Address ByteArray) :
    ∀ (blobs : List (_root_.Address × ByteArray)) {x : _root_.Address},
      m₀.contains x = true →
      (addBlobSupplements m₀ blobs).get? x = m₀.get? x
  | [], _, _ => rfl
  | (a, _) :: rest, x, hcx => by
    simp only [addBlobSupplements]
    have ih := addBlobSupplements_get?_of_contains m₀ rest hcx
    split
    · exact ih
    · rename_i hca
      have hne : a ≠ x := by
        intro heq
        rw [heq, hcx] at hca
        exact hca rfl
      have hbe : (a == x) = false := beq_eq_false_iff_ne.mpr hne
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
        ← Std.HashMap.get?_eq_getElem?]
      exact ih

theorem addBlobSupplements_get?_some_inv (m₀ : Std.HashMap _root_.Address ByteArray) :
    ∀ (blobs : List (_root_.Address × ByteArray)) {x : _root_.Address} {bytes : ByteArray},
      (addBlobSupplements m₀ blobs).get? x = some bytes →
      m₀.get? x = some bytes ∨ (m₀.contains x = false ∧ (x, bytes) ∈ blobs)
  | [], _, _, h => Or.inl h
  | (a, b₀) :: rest, x, bytes, h => by
    simp only [addBlobSupplements] at h
    split at h
    · rcases addBlobSupplements_get?_some_inv m₀ rest h with hm | ⟨hnc, hmem⟩
      · exact Or.inl hm
      · exact Or.inr ⟨hnc, List.mem_cons_of_mem _ hmem⟩
    · rename_i hca
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        injection h with hb
        subst hb
        have hax : a = x := beq_iff_eq.mp heq
        subst hax
        exact Or.inr ⟨Bool.eq_false_iff.mpr hca, List.mem_cons_self⟩
      · rw [← Std.HashMap.get?_eq_getElem?] at h
        rcases addBlobSupplements_get?_some_inv m₀ rest h with hm | ⟨hnc, hmem⟩
        · exact Or.inl hm
        · exact Or.inr ⟨hnc, List.mem_cons_of_mem _ hmem⟩

theorem addBlobSupplements_get?_of_mem_nodup (m₀ : Std.HashMap _root_.Address ByteArray) :
    ∀ {blobs : List (_root_.Address × ByteArray)} {x : _root_.Address} {bytes : ByteArray},
      (blobs.map Prod.fst).Nodup → (x, bytes) ∈ blobs → m₀.contains x = false →
      (addBlobSupplements m₀ blobs).get? x = some bytes
  | [], _, _, _, hm, _ => nomatch hm
  | (a, b₀) :: rest, x, bytes, hnd, hm, hnc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq
      simp only [addBlobSupplements, hnc, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true]
    · have hax : a ≠ x := by
        intro heq
        subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(a, bytes), htl, rfl⟩)
      have ih := addBlobSupplements_get?_of_mem_nodup m₀ hnd.2 htl hnc
      simp only [addBlobSupplements]
      split
      · exact ih
      · have hbe : (a == x) = false := beq_eq_false_iff_ne.mpr hax
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
          ← Std.HashMap.get?_eq_getElem?]
        exact ih

/-- Role-closure record supplements extracted from `(E_role, order_role)`. -/
def roleSuppOf (E_role : Ixon.Env) (order_role : List _root_.Address) : List SuppEntry :=
  order_role.filterMap fun a =>
    match E_role.consts.get? a, Ix.Cert.recordAt E_role a with
    | some lc, some c => some (a, lc.rawBytes, c)
    | _, _ => none

theorem mem_roleSuppOf_iff {E_role : Ixon.Env} {order_role : List _root_.Address}
    {a : _root_.Address} {raw : ByteArray} {c : Ixon.Constant} :
    (a, raw, c) ∈ roleSuppOf E_role order_role ↔
      a ∈ order_role ∧ ∃ lc, E_role.consts.get? a = some lc ∧
        Ix.Cert.recordAt E_role a = some c ∧ lc.rawBytes = raw := by
  simp only [roleSuppOf, List.mem_filterMap]
  constructor
  · rintro ⟨a', ha', hfn⟩
    cases hget : E_role.consts.get? a' with
    | none => rw [hget] at hfn; cases hfn
    | some lc =>
      cases hrec : Ix.Cert.recordAt E_role a' with
      | none => rw [hget, hrec] at hfn; cases hfn
      | some c' =>
        rw [hget, hrec] at hfn
        injection hfn with hprod
        rcases Prod.mk.inj hprod with ⟨ha, hrest⟩
        rcases Prod.mk.inj hrest with ⟨hraw, hc⟩
        subst ha; subst hraw; subst hc
        exact ⟨ha', lc, hget, hrec, rfl⟩
  · rintro ⟨ha, lc, hget, hrec, rfl⟩
    exact ⟨a, ha, by rw [hget, hrec]⟩

theorem roleSuppOf_nodup {E_role : Ixon.Env} {order_role : List _root_.Address}
    (hnd : order_role.Nodup) :
    ((roleSuppOf E_role order_role).map (·.1)).Nodup := by
  unfold roleSuppOf
  induction order_role with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.filterMap_cons]
    cases hget : E_role.consts.get? a with
    | none => exact ih hnd.2
    | some lc =>
      cases hrec : Ix.Cert.recordAt E_role a with
      | none => exact ih hnd.2
      | some c =>
        rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, ih hnd.2⟩
        intro hm
        obtain ⟨⟨a', raw', c'⟩, hm_fm, rfl⟩ := List.mem_map.mp hm
        have hm_all : (a', raw', c') ∈ roleSuppOf E_role rest := hm_fm
        exact hnd.1 (mem_roleSuppOf_iff.mp hm_all).1

/-! ## Role-aware sub-environment (`subEnvRole`) and `DrawsRoleLocal` -/

/-- Role-aware sub-environment keeping `Keep` from `E₀.consts`, adding `supp` at addresses absent
from `E₀.consts`, overlaying `roleBlobs` onto `E₀.blobs`, and setting `anonHints := {}`.
Note that `(subEnvRole E₀ Keep supp roleBlobs).consts = (subEnv E₀ Keep supp).consts`
definitionally, so all `subEnv` constant/record lemmas apply directly. -/
noncomputable def subEnvRole (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) (roleBlobs : List (_root_.Address × ByteArray)) : Ixon.Env where
  consts := addSupplements E₀.consts (restrictConsts E₀.consts Keep) supp
  blobs := addBlobSupplements E₀.blobs roleBlobs
  anonHints := {}
  roleBinding := none

@[simp]
theorem hintsOf_subEnvRole (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) (roleBlobs : List (_root_.Address × ByteArray)) :
    Ix.Cert.hintsOf (subEnvRole E₀ Keep supp roleBlobs) = fun _ => none := by
  funext r
  simp [Ix.Cert.hintsOf, subEnvRole]

theorem addSupplements_append_left
    (m₀ base : Std.HashMap _root_.Address Ixon.LazyConstant) :
    ∀ {supp₁ : List SuppEntry} (supp₂ : List SuppEntry)
      {x : _root_.Address} {raw : ByteArray} {c : Ixon.Constant},
      (supp₁.map (·.1)).Nodup → (x, raw, c) ∈ supp₁ → m₀.contains x = false →
      (addSupplements m₀ base (supp₁ ++ supp₂)).get? x = some (Claim.mkLazy raw c)
  | [], _, _, _, _, _, hm, _ => nomatch hm
  | (a, raw₀, c₀) :: rest, supp₂, x, raw, c, hnd, hm, hnc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with heq | htl
    · cases heq
      simp only [List.cons_append, addSupplements, hnc, Bool.false_eq_true, ↓reduceIte,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true]
    · have hax : a ≠ x := by
        intro heq
        subst heq
        exact hnd.1 (List.mem_map.mpr ⟨(a, raw, c), htl, rfl⟩)
      have ih := addSupplements_append_left m₀ base supp₂ hnd.2 htl hnc
      simp only [List.cons_append, addSupplements]
      split
      · exact ih
      · have hbe : (a == x) = false := beq_eq_false_iff_ne.mpr hax
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
          ← Std.HashMap.get?_eq_getElem?]
        exact ih

/-- **`DrawsRoleLocal` for `subEnvRole`** when every supplement entry comes from `V.env.consts` or
is a recursor record, and every supplemented blob comes from `V.env.blobs`. -/
theorem subEnvRole_drawsRoleLocal {E₀ E_view : Ixon.Env} (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) (roleBlobs : List (_root_.Address × ByteArray))
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      (∃ lcV, E_view.consts.get? a = some lcV ∧ lcV.rawBytes = raw) ∨
        IxVM.Refinement.IsRecursorRecord c)
    (hblobs : ∀ a bytes, (a, bytes) ∈ roleBlobs → E_view.blobs.get? a = some bytes) :
    DrawsRoleLocal (subEnvRole E₀ Keep supp roleBlobs) E₀ E_view := by
  refine ⟨fun a lc hget => ?_, fun a bytes hblob => ?_⟩
  · rcases subEnv_get?_some_inv E₀ Keep supp hget with ⟨_, hget₀⟩ | ⟨hnc, raw, c, hm, rfl⟩
    · exact Or.inl ⟨lc, hget₀, rfl⟩
    · refine Or.inr ⟨hnc, ?_⟩
      rcases hsupp a raw c hm with ⟨lcV, hgetV, hrawV⟩ | hrec
      · exact Or.inl ⟨lcV, hgetV, hrawV.trans (Claim.mkLazy_rawBytes raw c).symm⟩
      · exact Or.inr ⟨c, Claim.mkLazy_get? raw c, hrec⟩
  · rcases addBlobSupplements_get?_some_inv E₀.blobs roleBlobs hblob with hget₀ | ⟨hnc, hm⟩
    · exact Or.inl hget₀
    · exact Or.inr ⟨hnc, hblobs a bytes hm⟩

/-- Authenticated records/blobs and exact decoding on `subEnvRole`. -/
theorem subEnvRole_authentic_exact {calls : List (Call F)} {E₀ : Ixon.Env}
    {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    {roleBlobs : List (_root_.Address × ByteArray)}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧ Ixon.deConstantExact raw = .ok c)
    (hblobs : ∀ a bytes, (a, bytes) ∈ roleBlobs → _root_.Address.blake3Pure bytes = a) :
    (∀ a lc, (subEnvRole E₀ Keep supp roleBlobs).consts.get? a = some lc →
      _root_.Address.blake3Pure lc.rawBytes = a ∧
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c) ∧
    (∀ a bytes, (subEnvRole E₀ Keep supp roleBlobs).blobs.get? a = some bytes →
      _root_.Address.blake3Pure bytes = a) := by
  refine ⟨fun a lc hget => subEnv_consts_authentic_exact hload hexact₀ hsupp hget,
    fun a bytes hblob => ?_⟩
  rcases addBlobSupplements_get?_some_inv E₀.blobs roleBlobs hblob with hget₀ | ⟨_, hm⟩
  · exact (hload.2 a bytes hget₀).2
  · exact hblobs a bytes hm

/-- Under `¬ V.HashedCollision extra calls`, `subEnvRole` agrees with `E_role` on every record in
`order_role` and every blob in `blobsOf E_role order_role`. -/
theorem subEnvRole_agrees_on_role
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hnoCol : ¬ V.HashedCollision extra calls)
    {Keep : _root_.Address → Prop} (hkeep_role : ∀ a ∈ order_role, Keep a)
    (extraRec : List SuppEntry) :
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role ++ extraRec)
      (Ix.Cert.blobsOf E_role order_role)
    (∀ a ∈ order_role, Ix.Cert.recordAt E a = Ix.Cert.recordAt E_role a ∧
      E.consts.contains a = true) ∧
    (∀ a bytes, (a, bytes) ∈ Ix.Cert.blobsOf E_role order_role →
      E.blobs.get? a = some bytes) := by
  intro E
  refine ⟨fun a ha => ?_, fun a bytes hm => ?_⟩
  · obtain ⟨lc_r, c_r, hget_r, _, hrec_r, hblk_r, _, _, hex_r, hpreV⟩ := hadm.order_record_spec ha
    have hrec_eq : Ix.Cert.recordAt E a = some c_r := by
      cases hget₀ : E₀.consts.get? a with
      | some lc₀ =>
        obtain ⟨hh₀, hblk₀⟩ := hload.1 a lc₀ hget₀
        have hraw_eq : lc₀.rawBytes = lc_r.rawBytes := by
          by_contra hne
          exact hnoCol (Or.inl ⟨a, lc_r.rawBytes, lc₀.rawBytes, Or.inl hpreV, hh₀, hne, hblk₀⟩)
        obtain ⟨c₀, hlc₀_c, hex₀⟩ := hexact₀ a lc₀ hget₀
        rw [hraw_eq, hex_r] at hex₀
        injection hex₀ with hceq
        rw [← hceq] at hlc₀_c
        have hrec₀ : Ix.Cert.recordAt E₀ a = some c_r := by
          unfold Ix.Cert.recordAt
          rw [hget₀]
          exact hlc₀_c
        exact recordAt_subEnv_of_keep E₀ Keep _ (hkeep_role a ha) hrec₀
      | none =>
        have hnc : E₀.consts.contains a = false := by
          rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hget₀]
          rfl
        have hm_supp : (a, lc_r.rawBytes, c_r) ∈ roleSuppOf E_role order_role :=
          mem_roleSuppOf_iff.mpr ⟨ha, lc_r, hget_r, hrec_r, rfl⟩
        have hgetE := addSupplements_append_left E₀.consts (restrictConsts E₀.consts Keep) extraRec
          (roleSuppOf_nodup hadm.closureOrder.nodup) hm_supp hnc
        unfold Ix.Cert.recordAt
        change (E.consts.get? a >>= Ixon.LazyConstant.get?) = some c_r
        rw [show E.consts = addSupplements E₀.consts (restrictConsts E₀.consts Keep)
          (roleSuppOf E_role order_role ++ extraRec) from rfl, hgetE]
        rfl
    exact ⟨hrec_eq.trans hrec_r.symm, contains_of_recordAt hrec_eq⟩
  · obtain ⟨hnd_blobs, hblob_spec⟩ := hadm.blobs_spec
    obtain ⟨hblk_b, _, _, hpreV_b⟩ := hblob_spec a bytes hm
    cases hget_b0 : E₀.blobs.get? a with
    | some b₀ =>
      obtain ⟨hh₀, hblk₀⟩ := hload.2 a b₀ hget_b0
      have hbeq : b₀ = bytes := by
        by_contra hne
        exact hnoCol (Or.inl ⟨a, bytes, b₀, Or.inl hpreV_b, hh₀, hne, hblk₀⟩)
      subst hbeq
      have hcont : E₀.blobs.contains a = true := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hget_b0]
        rfl
      change (addBlobSupplements E₀.blobs (Ix.Cert.blobsOf E_role order_role)).get? a = some b₀
      rw [addBlobSupplements_get?_of_contains E₀.blobs _ hcont]
      exact hget_b0
    | none =>
      have hnc : E₀.blobs.contains a = false := by
        rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hget_b0]
        rfl
      exact addBlobSupplements_get?_of_mem_nodup E₀.blobs hnd_blobs hm hnc

/-! ## Stratified rank (`roleTwoTierRank`) and `UsedClosureOrderAt` on `subEnvRole` -/

/-- Stratified rank placing `order_role` first (ordered by `order_role.idxOf`) and all non-role
records after `order_role.length` (ordered by `twoTierRank Wk rank iblock`). -/
noncomputable def roleTwoTierRank (order_role : List _root_.Address)
    (Wk : _root_.Address → Prop) (rank : _root_.Address → Nat)
    (iblock : _root_.Address → _root_.Address) (a : _root_.Address) : Nat :=
  if a ∈ order_role then
    order_role.idxOf a
  else
    order_role.length + twoTierRank Wk rank iblock a

private theorem idxOf_lt_of_pairwise {α : Type} [BEq α] [LawfulBEq α] {R : α → α → Prop} :
    ∀ {xs : List α} {a b : α},
      xs.Pairwise R → a ∈ xs → b ∈ xs → ¬ R a b → a ≠ b →
      xs.idxOf b < xs.idxOf a
  | [], _, _, _, ha, _, _, _ => nomatch ha
  | x :: tl, a, b, hpw, ha, hb, hnot, hne => by
    rw [List.pairwise_cons] at hpw
    by_cases hbx : b = x
    · subst hbx
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hne)]
      omega
    · by_cases hax : a = x
      · subst hax
        have hb_tl : b ∈ tl := by
          rcases List.mem_cons.mp hb with rfl | htl
          · exact absurd rfl hbx
          · exact htl
        exact absurd (hpw.1 b hb_tl) hnot
      · have ha_tl : a ∈ tl := by
          rcases List.mem_cons.mp ha with rfl | htl
          · exact absurd rfl hax
          · exact htl
        have hb_tl : b ∈ tl := by
          rcases List.mem_cons.mp hb with rfl | htl
          · exact absurd rfl hbx
          · exact htl
        have ih := idxOf_lt_of_pairwise hpw.2 ha_tl hb_tl hnot hne
        rw [List.idxOf_cons_ne _ (Ne.symm hbx), List.idxOf_cons_ne _ (Ne.symm hax)]
        omega

/-- **`UsedClosureOrderAt` on `subEnvRole`** under `roleTwoTierRank`. -/
theorem subEnvRole_usedClosureOrderAt
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)}
    {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ E_role : Ixon.Env} {limits : Ix.Kernel.Admission.Limits}
    {order_role : List _root_.Address} {envA : Ix.Kernel.Env .anon}
    {pre : Ix.Kernel.Reader.Prelude .anon} {st_role : Ix.Kernel.Reader.State .anon}
    {decls_role : Array (Ix.Kernel.Reader.CDecl .anon)}
    (hadm : TableAdmittedAt V b t E_role limits order_role envA pre st_role decls_role)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (Keep : _root_.Address → Prop) (S : _root_.Address → Prop)
    {Wk : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (iblock : _root_.Address → _root_.Address)
    (hkeep_role : ∀ a ∈ order_role, Keep a)
    (hwk_keep : ∀ x, Wk x → Keep x)
    (hwk_owner : ∀ x c, Wk x → Ix.Cert.recordAt E₀ x = some c → Ix.Cert.ownerOf x c ≠ x →
      Wk (Ix.Cert.ownerOf x c) ∧ rank (Ix.Cert.ownerOf x c) < rank x)
    (hwk_edge_keep : ∀ x y, Wk x → Core.S0.WalkEdge E₀ x y → y ∉ order_role → Keep y →
      Wk y ∧ rank y < rank x)
    (hwk_rec : ∀ x, Wk x → ∃ c, Ix.Cert.recordAt E₀ x = some c)
    (hextra_kind : ∀ x c, x ∉ order_role → ¬ Wk x →
      Ix.Cert.recordAt (subEnvRole E₀ Keep (roleSuppOf E_role order_role)
        (Ix.Cert.blobsOf E_role order_role)) x = some c →
      IxVM.Refinement.IsRecursorRecord c ∨
        (c.sharing = #[] ∧ c.refs = #[] ∧ Ix.Cert.ownerOf x c ≠ x ∧
          (Ix.Cert.ownerOf x c ∈ order_role ∨
            Wk (Ix.Cert.ownerOf x c) ∨
            ∃ co, Ix.Cert.recordAt (subEnvRole E₀ Keep (roleSuppOf E_role order_role)
              (Ix.Cert.blobsOf E_role order_role)) (Ix.Cert.ownerOf x c) = some co ∧
              IxVM.Refinement.IsRecursorRecord co)))
    (hextra_refs : ∀ a c, a ∉ order_role → ¬ Wk a →
      Ix.Cert.recordAt (subEnvRole E₀ Keep (roleSuppOf E_role order_role)
        (Ix.Cert.blobsOf E_role order_role)) a = some c →
      IxVM.Refinement.IsRecursorRecord c →
      ∀ i ∈ IxVM.Consistency.usedRefIdxs c, ∀ r cr,
        c.refs[i]? = some r →
        Ix.Cert.recordAt (subEnvRole E₀ Keep (roleSuppOf E_role order_role)
          (Ix.Cert.blobsOf E_role order_role)) r = some cr →
        Ix.Cert.ownerOf r cr ≠ a →
        Ix.Cert.ownerOf r cr ∉ order_role →
        (Wk (Ix.Cert.ownerOf r cr) ∧ rank (Ix.Cert.ownerOf r cr) ≤ rank (iblock a)) ∨
          (¬ Wk (Ix.Cert.ownerOf r cr) ∧ rank (iblock (Ix.Cert.ownerOf r cr)) < rank (iblock a))) :
    let E := subEnvRole E₀ Keep (roleSuppOf E_role order_role)
      (Ix.Cert.blobsOf E_role order_role)
    IxVM.Consistency.UsedClosureOrderAt t E S
      (closureOrderByRank t E S (roleTwoTierRank order_role Wk rank iblock)) := by
  intro E
  have hagree : ∀ a ∈ order_role, Ix.Cert.recordAt E a = Ix.Cert.recordAt E_role a ∧
      E.consts.contains a = true := by
    have h := (subEnvRole_agrees_on_role hadm hload hexact₀ hnoCol hkeep_role []).1
    rwa [List.append_nil] at h
  have hown : ∀ a c, Ix.Cert.recordAt E a = some c →
      E.consts.contains (Ix.Cert.ownerOf a c) = true := by
    intro a c hrec
    by_cases ha_role : a ∈ order_role
    · have hrec_role : Ix.Cert.recordAt E_role a = some c := (hagree a ha_role).1.symm.trans hrec
      by_cases hown_eq : Ix.Cert.ownerOf a c = a
      · rw [hown_eq]
        exact (hagree a ha_role).2
      · have hreach_a := (hadm.closureOrder.complete a).mp ha_role
        have hreach_o : Ix.Cert.CompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t)
            (Ix.Cert.ownerOf a c) :=
          .step hreach_a ⟨c, hrec_role, Or.inl ⟨rfl, hown_eq⟩⟩
        exact (hagree _ ((hadm.closureOrder.complete _).mpr hreach_o)).2
    · by_cases hwa : Wk a
      · obtain ⟨c₀, hrec₀⟩ := hwk_rec a hwa
        have hrec' : Ix.Cert.recordAt E a = some c₀ :=
          recordAt_subEnv_of_keep E₀ Keep _ (hwk_keep a hwa) hrec₀
        rw [hrec] at hrec'
        injection hrec' with hceq
        subst hceq
        by_cases hown_eq : Ix.Cert.ownerOf a c = a
        · rw [hown_eq]
          exact contains_of_recordAt hrec
        · obtain ⟨hwb, _⟩ := hwk_owner a c hwa hrec₀ hown_eq
          obtain ⟨cb, hrec_b⟩ := hwk_rec _ hwb
          exact contains_of_recordAt
            (recordAt_subEnv_of_keep E₀ Keep _ (hwk_keep _ hwb) hrec_b)
      · rcases hextra_kind a c ha_role hwa hrec with hrec_k | ⟨_, _, _, hown_cls⟩
        · rw [isRecursorRecord_ownerOf_eq a hrec_k]
          exact contains_of_recordAt hrec
        · rcases hown_cls with hrole | hwb | ⟨co, hrec_o, _⟩
          · exact (hagree _ hrole).2
          · obtain ⟨cb, hrec_b⟩ := hwk_rec _ hwb
            exact contains_of_recordAt
              (recordAt_subEnv_of_keep E₀ Keep _ (hwk_keep _ hwb) hrec_b)
          · exact contains_of_recordAt hrec_o
  refine usedClosureOrderAt_closureOrderByRank hown fun a b _ _ href => ?_
  by_cases ha_role : a ∈ order_role
  · obtain ⟨c, hrec_a, i, hi, r, hr, cr, hrec_r, hown_r, hne_ba⟩ := href
    have hrec_role_a : Ix.Cert.recordAt E_role a = some c := (hagree a ha_role).1.symm.trans hrec_a
    have hr_cont : E_role.consts.contains r = true := hadm.usedRefs a ha_role c hrec_role_a i hi r hr
    have hr_mem : r ∈ c.refs := Array.mem_of_getElem? hr
    have hr_contains : c.refs.contains r = true := Array.contains_iff_mem.mpr hr_mem
    have hreach_a := (hadm.closureOrder.complete a).mp ha_role
    have hreach_r : Ix.Cert.CompiledReachAt t E_role (IxVM.Refinement.BindingSeeds t) r :=
      .step hreach_a ⟨c, hrec_role_a, Or.inr ⟨hr_contains, hr_cont⟩⟩
    have hr_role : r ∈ order_role := (hadm.closureOrder.complete r).mpr hreach_r
    have hrec_role_r : Ix.Cert.recordAt E_role r = some cr := (hagree r hr_role).1.symm.trans hrec_r
    have hb_role : b ∈ order_role := by
      by_cases hbr : b = r
      · rwa [hbr]
      · exact (hadm.closureOrder.complete b).mpr
          (.step hreach_r ⟨cr, hrec_role_r, Or.inl ⟨hown_r, hbr⟩⟩)
    have href_role : Ix.Cert.RecordRef E_role a b :=
      ⟨c, hrec_role_a, r, hr_mem, cr, hrec_role_r, hown_r, hne_ba⟩
    have hlt_idx := idxOf_lt_of_pairwise hadm.closureOrder.ordered ha_role hb_role
      (fun hn => hn href_role) hne_ba.symm
    simp only [roleTwoTierRank, ha_role, hb_role, ↓reduceIte]
    exact hlt_idx
  · by_cases hb_role : b ∈ order_role
    · have hlt_len : order_role.idxOf b < order_role.length := List.idxOf_lt_length_iff.mpr hb_role
      simp only [roleTwoTierRank, ha_role, hb_role, ↓reduceIte]
      omega
    · simp only [roleTwoTierRank, ha_role, hb_role, ↓reduceIte]
      by_cases hwa : Wk a
      · obtain ⟨c, hrec_a, i, hi, r, hr, cr, hrec_r, hown_r, _⟩ := href
        obtain ⟨c₀, hrec_a0⟩ := hwk_rec a hwa
        have hrec_a' : Ix.Cert.recordAt E a = some c₀ :=
          recordAt_subEnv_of_keep E₀ Keep _ (hwk_keep a hwa) hrec_a0
        rw [hrec_a] at hrec_a'
        injection hrec_a' with hc_eq
        subst hc_eq
        have hi_s0 : i ∈ Core.S0.usedRefIdxs c := by
          rw [usedRefIdxs_eq]
          exact hi
        have hedge_ar : Core.S0.WalkEdge E₀ a r := ⟨c, hrec_a0, Or.inr ⟨i, hi_s0, hr⟩⟩
        have hr_not_role : r ∉ order_role := by
          intro hr_role
          have hrec_role_r : Ix.Cert.recordAt E_role r = some cr :=
            (hagree r hr_role).1.symm.trans hrec_r
          by_cases hbr : b = r
          · rw [hbr] at hb_role
            exact hb_role hr_role
          · have hreach_r := (hadm.closureOrder.complete r).mp hr_role
            exact hb_role ((hadm.closureOrder.complete b).mpr
              (.step hreach_r ⟨cr, hrec_role_r, Or.inl ⟨hown_r, hbr⟩⟩))
        have hkeep_r : Keep r ∧ Ix.Cert.recordAt E₀ r = some cr := by
          rcases recordAt_subEnv_some_inv E₀ Keep (roleSuppOf E_role order_role) hrec_r with
            hkp | ⟨_, _, hm_r⟩
          · exact hkp
          · exact absurd (mem_roleSuppOf_iff.mp hm_r).1 hr_not_role
        obtain ⟨hwr, hlt_ra⟩ := hwk_edge_keep a r hwa hedge_ar hr_not_role hkeep_r.1
        have hwb_lt : Wk b ∧ rank b < rank a := by
          by_cases hbr : b = r
          · subst hbr
            exact ⟨hwr, hlt_ra⟩
          · obtain ⟨hwb, hlt_br⟩ := hwk_owner r cr hwr hkeep_r.2 (by rw [hown_r]; exact hbr)
            rw [hown_r] at hwb hlt_br
            exact ⟨hwb, Nat.lt_trans hlt_br hlt_ra⟩
        simp only [twoTierRank, hwa, hwb_lt.1, ↓reduceIte]
        omega
      · obtain ⟨c, hrec_a, i, hi, r, hr, cr, hrec_r, hown_r, hne_ba⟩ := href
        rcases hextra_kind a c ha_role hwa hrec_a with hrec_k | ⟨_, hrefs_emp, _, _⟩
        · have hex := hextra_refs a c ha_role hwa hrec_a hrec_k i hi r cr hr hrec_r
            (by rw [hown_r]; exact hne_ba) (by rwa [hown_r])
          rw [hown_r] at hex
          rcases hex with ⟨hwb, hle⟩ | ⟨hnwb, hlt⟩
          · simp only [twoTierRank, hwa, hwb, ↓reduceIte]
            omega
          · simp only [twoTierRank, hwa, hnwb, ↓reduceIte]
            omega
        · rw [hrefs_emp] at hr
          simp at hr

/-! ## Core-backing environment (`coreEnvRole`) for `Core.Good` and `L1.EnvDecoded` -/

/-- All committed fallback records (`pre.records ++ pre.evidence`) packaged as `SuppEntry` items. -/
def fallbackSupp (pre : Ix.Kernel.Reader.Prelude .anon) : List SuppEntry :=
  (pre.records ++ pre.evidence).toList.map fun (a, c) => (a, Ixon.serConstant c, c)

theorem fallbackSupp_nodup {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre) :
    ((fallbackSupp pre).map (·.1)).Nodup := by
  have hkeys := Ix.Cert.ReaderFallback.preludeFor_keys hpre
  unfold fallbackSupp
  rwa [List.map_map, show ((fun x : SuppEntry => x.1) ∘
    fun (p : _root_.Address × Ixon.Constant) => (p.1, Ixon.serConstant p.2, p.2)) = Prod.fst from rfl]

/-- Core-backing `Ixon.Env` extending `subEnvRole E₀ Keep supp roleBlobs` with every record in
`pre.records ++ pre.evidence`. -/
noncomputable def coreEnvRole (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) (roleBlobs : List (_root_.Address × ByteArray))
    (pre : Ix.Kernel.Reader.Prelude .anon) : Ixon.Env :=
  subEnvRole E₀
    (fun x => Keep x ∨ ∃ c, (x, c) ∈ pre.records ++ pre.evidence)
    (supp ++ fallbackSupp pre)
    roleBlobs

/-- Preimage lifting for `subEnvRole E₀ Keep supp roleBlobs`. -/
theorem subEnvRole_preimage_to_view {V : IxVM.Refinement.View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry} {roleBlobs : List (_root_.Address × ByteArray)}
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧
      (V.Preimage a raw ∨ IxVM.Refinement.Hashed calls raw ∨
        (raw ∈ extra ∧ a ≠ Ix.HostAdmission.Merkle.padding)))
    (hblobs : ∀ a bytes, (a, bytes) ∈ roleBlobs → V.Preimage a bytes)
    {x : _root_.Address} {held : ByteArray}
    (hpre : ({ env := subEnvRole E₀ Keep supp roleBlobs } : IxVM.Refinement.View).Preimage x held) :
    V.Preimage x held ∨
      (IxVM.Refinement.Hashed calls held ∧ _root_.Address.blake3Pure held = x) ∨
      (held ∈ extra ∧ _root_.Address.blake3Pure held = x ∧
        x ≠ Ix.HostAdmission.Merkle.padding) := by
  rcases hpre with ⟨lc, hget, rfl⟩ | hblob | ⟨rb, hrb, -, -⟩ | ⟨t, ht, -, -⟩
  · rcases subEnv_get?_some_inv E₀ Keep supp hget with ⟨_, hget₀⟩ | ⟨_, raw, c, hm, rfl⟩
    · exact Or.inr (Or.inl (hload.1 x lc hget₀))
    · simp only [Claim.mkLazy_rawBytes]
      obtain ⟨hblk, hsrc⟩ := hsupp x raw c hm
      rcases hsrc with hv | hh | ⟨hex, hne⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl ⟨hh, hblk⟩)
      · exact Or.inr (Or.inr ⟨hex, hblk, hne⟩)
  · rcases addBlobSupplements_get?_some_inv E₀.blobs roleBlobs hblob with hget₀ | ⟨_, hm⟩
    · exact Or.inr (Or.inl (hload.2 x held hget₀))
    · exact Or.inl (hblobs x held hm)
  · cases hrb
  · cases ht

/-- **`Core.Good` on `subEnvRole E₀ Keep supp roleBlobs`** from `¬ V.HashedCollision extra calls`. -/
theorem good_subEnvRole_of_noCollision {V : IxVM.Refinement.View} {extra : List ByteArray}
    {calls : List (Call F)} {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry} {roleBlobs : List (_root_.Address × ByteArray)}
    (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable) (lim : Option Nat)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧
      (V.Preimage a raw ∨ IxVM.Refinement.Hashed calls raw ∨
        (raw ∈ extra ∧ a ≠ Ix.HostAdmission.Merkle.padding)))
    (hblobs : ∀ a bytes, (a, bytes) ∈ roleBlobs → V.Preimage a bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hbound : IxVM.Consistency.Bounded calls) :
    Core.Good ⟨subEnvRole E₀ Keep supp roleBlobs, env, t, lim⟩ calls := by
  refine ⟨fun hcol => hnoCol ?_, hbound⟩
  rcases hcol with ⟨x, held, bytes, hsrc, hh, hne, hblk⟩ | ⟨bytes, hsrc, hpad⟩
  · refine Or.inl ⟨x, held, bytes, ?_, hh, hne, hblk⟩
    rcases hsrc with hpre | ⟨hmem, -⟩ | hh_held
    · rcases subEnvRole_preimage_to_view hload hsupp hblobs hpre with
        hv | hh' | ⟨hex, hblk_held, -⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inr hh')
      · exact Or.inr (Or.inl ⟨hex, hblk_held⟩)
    · cases hmem
    · exact Or.inr (Or.inr hh_held)
  · rcases hsrc with hpre | hh
    · rcases subEnvRole_preimage_to_view hload hsupp hblobs hpre with hv | ⟨hh', -⟩ | ⟨-, -, hne⟩
      · exact Or.inr ⟨bytes, Or.inl hv, hpad⟩
      · exact Or.inr ⟨bytes, Or.inr hh', hpad⟩
      · exact absurd rfl hne
    · exact Or.inr ⟨bytes, Or.inr hh, hpad⟩

/-- **`Core.Good` on `coreEnvRole E₀ Keep supp roleBlobs pre`** from `RolePreludeInputs` and
`¬ V.HashedCollision extra calls`. -/
theorem coreEnvRole_good (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env}
    {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    {roleBlobs : List (_root_.Address × ByteArray)}
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (env : Ix.Kernel.Env .anon) (lim : Option Nat)
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp →
      _root_.Address.blake3Pure raw = a ∧
      (V.Preimage a raw ∨ IxVM.Refinement.Hashed calls raw ∨
        (raw ∈ extra ∧ a ≠ Ix.HostAdmission.Merkle.padding)))
    (hblobs : ∀ a bytes, (a, bytes) ∈ roleBlobs → V.Preimage a bytes)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hbound : IxVM.Consistency.Bounded calls) :
    Core.Good ⟨coreEnvRole E₀ Keep supp roleBlobs pre, env, t, lim⟩ calls := by
  apply good_subEnvRole_of_noCollision env t lim hload _ hblobs hnoCol hbound
  intro a raw c hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact hsupp a raw c h1
  · unfold fallbackSupp at h2
    obtain ⟨⟨a', c'⟩, hmem, heq⟩ := List.mem_map.mp h2
    injection heq with ha hrest
    injection hrest with hraw hc
    subst ha; subst hraw; subst hc
    obtain ⟨himg, hblk, _, hnotPad⟩ :=
      hRP.serConstant_mem_committedImages hpre (Array.mem_toList_iff.mp hmem)
    exact ⟨hblk, Or.inr (Or.inr ⟨hcomm_extra _ himg, hnotPad⟩)⟩

/-- **`L1.EnvDecoded` on `coreEnvRole E₀ Keep supp roleBlobs pre`**. -/
theorem coreEnvRole_envDecoded (hRP : RolePreludeInputs)
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {seeds : List _root_.Address} {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    {roleBlobs : List (_root_.Address × ByteArray)}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    (hwalk : Claim.WalkedL6 calls t E₀ seeds)
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hsupp : ∀ a raw c, (a, raw, c) ∈ supp → Ixon.deConstantExact raw = .ok c) :
    L1.EnvDecoded (coreEnvRole E₀ Keep supp roleBlobs pre) := by
  apply subEnv_envDecoded_of_walkedL6 _ hwalk
  intro a raw c hm
  rcases List.mem_append.mp hm with h1 | h2
  · exact hsupp a raw c h1
  · unfold fallbackSupp at h2
    obtain ⟨⟨a', c'⟩, hmem, heq⟩ := List.mem_map.mp h2
    injection heq with ha hrest
    injection hrest with hraw hc
    subst ha; subst hraw; subst hc
    obtain ⟨_, _, hwf, _⟩ :=
      hRP.serConstant_mem_committedImages hpre (Array.mem_toList_iff.mp hmem)
    exact Ixon.Verify.deConstantExact_serConstant c' hwf

/-- Every record in `subEnvRole E₀ Keep supp roleBlobs` (when `(supp.map (·.1)).Nodup`) is also
stored identically in `coreEnvRole E₀ Keep supp roleBlobs pre`. -/
theorem recordAt_coreEnvRole_of_subEnvRole {E₀ : Ixon.Env} {Keep : _root_.Address → Prop}
    {supp : List SuppEntry} {roleBlobs : List (_root_.Address × ByteArray)}
    {pre : Ix.Kernel.Reader.Prelude .anon}
    (hnd : (supp.map (·.1)).Nodup)
    {a : _root_.Address} {c : Ixon.Constant}
    (hrec : Ix.Cert.recordAt (subEnvRole E₀ Keep supp roleBlobs) a = some c) :
    Ix.Cert.recordAt (coreEnvRole E₀ Keep supp roleBlobs pre) a = some c := by
  rcases recordAt_subEnv_some_inv E₀ Keep supp hrec with ⟨hk, hrec₀⟩ | ⟨hnc, raw, hm⟩
  · exact recordAt_subEnv_of_keep E₀ _ _ (Or.inl hk) hrec₀
  · unfold coreEnvRole subEnvRole Ix.Cert.recordAt
    dsimp only
    rw [addSupplements_append_left E₀.consts _ (fallbackSupp pre) hnd hm hnc]
    rfl

/-- Every committed fallback record `(a, c) ∈ pre.records ++ pre.evidence` is stored at `a` in
`coreEnvRole E₀ Keep supp roleBlobs pre` whenever `supp` agrees with `pre.records ++ pre.evidence`
on shared addresses. -/
theorem recordAt_coreEnvRole_of_fallback (hRP : RolePreludeInputs)
    {V : IxVM.Refinement.View} {extra : List ByteArray} {calls : List (Call F)} {E₀ : Ixon.Env}
    {Keep : _root_.Address → Prop} {supp : List SuppEntry}
    {roleBlobs : List (_root_.Address × ByteArray)}
    {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude .anon}
    (hcomm_extra : ∀ img ∈ IxVM.Consistency.committedImages, img ∈ extra)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hexact₀ : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ c, lc.get? = some c ∧ Ixon.deConstantExact lc.rawBytes = .ok c)
    (hnoCol : ¬ V.HashedCollision extra calls)
    (hpre : Ix.Kernel.Reader.preludeFor t = .ok pre)
    (hsupp_compat : ∀ a raw c' c, (a, raw, c') ∈ supp →
      (a, c) ∈ pre.records ++ pre.evidence → c' = c)
    {a : _root_.Address} {c : Ixon.Constant}
    (hmem : (a, c) ∈ pre.records ++ pre.evidence) :
    Ix.Cert.recordAt (coreEnvRole E₀ Keep supp roleBlobs pre) a = some c := by
  cases hget₀ : E₀.consts.get? a with
  | some lc =>
    obtain ⟨_, _, hrec₀⟩ :=
      hRP.fallback_recordAt_agree hcomm_extra hload hexact₀ hnoCol hpre hmem hget₀
    exact recordAt_subEnv_of_keep E₀ _ _ (Or.inr ⟨c, hmem⟩) hrec₀
  | none =>
    have hnc : E₀.consts.contains a = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, hget₀]
      rfl
    have hfb_nd := fallbackSupp_nodup hpre
    have hfb_mem : (a, Ixon.serConstant c, c) ∈ fallbackSupp pre :=
      List.mem_map.mpr ⟨(a, c), Array.mem_toList_iff.mpr hmem, rfl⟩
    unfold coreEnvRole subEnvRole Ix.Cert.recordAt
    dsimp only
    have hstep : ∀ (s₁ : List SuppEntry),
        (∀ raw c', (a, raw, c') ∈ s₁ → c' = c) →
        ∃ raw', (addSupplements E₀.consts
          (restrictConsts E₀.consts (fun x => Keep x ∨ ∃ c, (x, c) ∈ pre.records ++ pre.evidence))
          (s₁ ++ fallbackSupp pre)).get? a = some (Claim.mkLazy raw' c) := by
      intro s₁ hcompat₁
      induction s₁ with
      | nil =>
        exact ⟨Ixon.serConstant c,
          addSupplements_get?_of_mem_nodup E₀.consts _ hfb_nd hfb_mem hnc⟩
      | cons hd tl ih =>
        rcases hd with ⟨a₁, raw₁, c₁⟩
        simp only [List.cons_append, addSupplements]
        by_cases ha_eq : a₁ = a
        · subst ha_eq
          have hc_eq := hcompat₁ raw₁ c₁ List.mem_cons_self
          subst hc_eq
          simp only [hnc, Bool.false_eq_true, ↓reduceIte,
            Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_self_eq_true]
          exact ⟨raw₁, rfl⟩
        · obtain ⟨raw', ih'⟩ := ih (fun r' c' hm => hcompat₁ r' c' (List.mem_cons_of_mem _ hm))
          split
          · exact ⟨raw', ih'⟩
          · have hbe : (a₁ == a) = false := beq_eq_false_iff_ne.mpr ha_eq
            rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbe,
              ← Std.HashMap.get?_eq_getElem?]
            exact ⟨raw', ih'⟩
    obtain ⟨raw', hget'⟩ := hstep supp (fun raw c' hm => hsupp_compat a raw c' c hm hmem)
    rw [hget']
    rfl

/-- Every blob in `E := subEnvRole ...` is stored identically in `coreEnvRole ...`. -/
@[simp]
theorem blobs_coreEnvRole (E₀ : Ixon.Env) (Keep : _root_.Address → Prop)
    (supp : List SuppEntry) (roleBlobs : List (_root_.Address × ByteArray))
    (pre : Ix.Kernel.Reader.Prelude .anon) :
    (coreEnvRole E₀ Keep supp roleBlobs pre).blobs =
      (subEnvRole E₀ Keep supp roleBlobs).blobs :=
  rfl

end IxVM.Refinement.Assembly
