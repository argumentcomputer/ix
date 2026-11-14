import IxVMRefinement.Claim.DefaultAdmits
import IxVMRefinement.Claim.Walk

/-! # Obligation L6: Claim-phase soundness and walked-closure assembly

Assembles `IxVM.Consistency.ClaimPhase` and `IxVM.Consistency.L6` from:
* `verify_claim_decode_spec` (`Decode.lean`) for claim ingestion, BLAKE3 digest verification,
  role-table context loading under `ReaderTable`, and assumption-tree decoding;
* `assert_claimable_spec`, `run_check_transitive_spec`, and `walk_leaves_owned_spec`
  (`Walk.lean`) for seed-safety/inertness refusals and edge-closed record walking;
* `envOfRecs`, constructing the `Ixon.Env` witness `E₀` from the walked records and hashed
  blobs and discharging `LoadedBy`, `¬ OutsideLogicAt`, `¬ InertAt`, and `WalkedL6` (as well as
  `S0.Walked` under `ClaimExtraFacts`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Walked-closure seam for L6 -/

/-- Walked-closure predicate established by `IxVM::verify_claim`:
* records `E₀`'s role-binding and `LazyConstant` raw-bytes / exact-decode agreement;
* guards role-table evidence proof seeds by `E₀.consts.contains a = true` (matching
  `IxVM.Consistency.ReadIn` and `Ix.Cert.CompiledReachAt.seed`, since evidence theorems of unused
  roles are not loaded during `verify_claim`);
* records record presence plus `muts ∨ S0.CheckedAt` on the `S0.usedRefIdxs` closure. -/
def WalkedL6 (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (seeds : List _root_.Address) : Prop :=
  (∀ rb, E₀.roleBinding = some rb → Ix.Kernel.RoleTable.ofBytes rb.bytes = some t) ∧
  (∀ a lc, E₀.consts.get? a = some lc →
    lc.rawBytes.size < 4294967296 ∧
    ∃ c, lc.get? = some c ∧
      Ixon.deConstant lc.rawBytes = .ok c ∧
      Ixon.deConstantExact lc.rawBytes = .ok c) ∧
  ∃ Wk : _root_.Address → Prop,
    (∀ a, (a ∈ seeds ∨ (E₀.consts.contains a = true ∧
        ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList)) → Wk a) ∧
    (∀ a b, Wk a → (S0.WalkEdge E₀ a b ∨ Ix.Cert.GroundEdgeAt t E₀ a b) → Wk b) ∧
    ∀ a, Wk a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧
      ((∃ ms, c.info = .muts ms) ∨ S0.CheckedAt calls t a)

/-- Seams bundle equipping `S₀` with `WalkedL6`. -/
def S_L6 : IxVM.Consistency.Seams :=
  { S₀ with Walked := WalkedL6 }

/-! ## Constructing `E₀ : Ixon.Env` from walked records and hashed blobs -/

/-- Standalone `LazyConstant` wrapping `rawBytes` and pre-decoded constant `c`. -/
def mkLazy (rawBytes : ByteArray) (c : Ixon.Constant) : Ixon.LazyConstant :=
  { buf := rawBytes, off := 0, len := rawBytes.size, cache := some c }

@[simp]
theorem mkLazy_rawBytes (rawBytes : ByteArray) (c : Ixon.Constant) :
    (mkLazy rawBytes c).rawBytes = rawBytes := by
  simp [mkLazy, Ixon.LazyConstant.rawBytes]

@[simp]
theorem mkLazy_get? (rawBytes : ByteArray) (c : Ixon.Constant) :
    (mkLazy rawBytes c).get? = some c :=
  rfl

/-- Build `E₀.consts` from a list of walked records. -/
def buildConsts {calls : List (Call F)} {t : Ix.Kernel.RoleTable} :
    List (WalkedRec calls t) → Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => {}
  | r :: rs => (buildConsts rs).insert r.addr (mkLazy r.rawBytes r.c)

theorem buildConsts_get?_some_inv {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (recs : List (WalkedRec calls t)) {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : (buildConsts recs).get? a = some lc) :
    ∃ r ∈ recs, r.addr = a ∧ lc = mkLazy r.rawBytes r.c := by
  induction recs with
  | nil =>
    simp only [buildConsts, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h
    cases h
  | cons r rs ih =>
    simp only [buildConsts, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i heq
      injection h with hlc
      exact ⟨r, List.mem_cons_self, beq_iff_eq.mp heq, hlc.symm⟩
    · rw [← Std.HashMap.get?_eq_getElem?] at h
      obtain ⟨r', hr', ha', hlc'⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', ha', hlc'⟩

theorem buildConsts_contains_iff {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (recs : List (WalkedRec calls t)) (a : _root_.Address) :
    (buildConsts recs).contains a = true ↔ a ∈ recs.map (·.addr) := by
  induction recs with
  | nil =>
    simp [buildConsts, Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_empty]
  | cons r rs ih =>
    simp only [buildConsts, Std.HashMap.contains_eq_isSome_getElem?,
      Std.HashMap.getElem?_insert, List.map_cons, List.mem_cons]
    split
    · rename_i heq
      have ha : a = r.addr := (beq_iff_eq.mp heq).symm
      simp [ha]
    · rename_i hne
      have ha : a ≠ r.addr := fun h => hne (beq_iff_eq.mpr h.symm)
      rw [← Std.HashMap.contains_eq_isSome_getElem?, ih]
      simp [ha]

/-- Single-call `Blake3::hash` predicate matching `Hashed`. -/
def CallHashes (cl : Call F) (bytes : ByteArray) : Prop :=
  cl.name = blake3Hash ∧ ∃ input : SourceValue F,
    cl.args = [input] ∧ Bytes.RepByteStream byteStreamEnum cl.heap bytes.data.toList input

/-- Populate `E₀.blobs` with the byte strings hashed by `Blake3::hash` calls in `calls`. -/
noncomputable def buildBlobs : List (Call F) → Std.HashMap _root_.Address ByteArray
  | [] => {}
  | cl :: cls =>
    haveI := Classical.propDecidable (∃ bytes, CallHashes cl bytes)
    if hex : ∃ bytes, CallHashes cl bytes then
      let b0 := Classical.choose hex
      (buildBlobs cls).insert (Address.blake3Pure b0) b0
    else
      buildBlobs cls

theorem buildBlobs_get?_some_inv (calls : List (Call F)) {a : _root_.Address} {bytes : ByteArray}
    (h : (buildBlobs calls).get? a = some bytes) :
    Hashed calls bytes ∧ Address.blake3Pure bytes = a := by
  induction calls with
  | nil =>
    simp only [buildBlobs, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h
    cases h
  | cons cl cls ih =>
    simp only [buildBlobs] at h
    split at h
    · rename_i hex
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        injection h with hb
        subst hb
        exact ⟨⟨cl, List.mem_cons_self, Classical.choose_spec hex⟩, beq_iff_eq.mp heq⟩
      · rw [← Std.HashMap.get?_eq_getElem?] at h
        obtain ⟨hh, ha⟩ := ih h
        exact ⟨hashed_mono (fun _ hm => List.mem_cons_of_mem _ hm) hh, ha⟩
    · obtain ⟨hh, ha⟩ := ih h
      exact ⟨hashed_mono (fun _ hm => List.mem_cons_of_mem _ hm) hh, ha⟩

/-- Witness environment `E₀` built from the role binding `b`, walked records `recs`, and hashed
blobs of `calls`. -/
noncomputable def envOfRecs {t : Ix.Kernel.RoleTable} (b : Ix.Kernel.Admission.Binding)
    (calls : List (Call F)) (recs : List (WalkedRec calls t)) : Ixon.Env :=
  { consts := buildConsts recs
    blobs := buildBlobs calls
    roleBinding := some { address := b.address, bytes := b.bytes } }

theorem envOfRecs_loadedBy {t : Ix.Kernel.RoleTable} (b : Ix.Kernel.Admission.Binding)
    (calls : List (Call F)) (recs : List (WalkedRec calls t)) :
    IxVM.Consistency.LoadedBy calls (envOfRecs b calls recs) := by
  refine ⟨fun a lc hget => ?_, fun a bytes hget => buildBlobs_get?_some_inv calls hget⟩
  obtain ⟨r, -, rfl, rfl⟩ := buildConsts_get?_some_inv recs hget
  simpa using ⟨r.hhashed, r.hblake⟩

theorem recordAt_envOfRecs_inv {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {b : Ix.Kernel.Admission.Binding}
    (recs : List (WalkedRec calls t)) {a : _root_.Address} {c : Ixon.Constant}
    (hrec : Ix.Cert.recordAt (envOfRecs b calls recs) a = some c) :
    ∃ r ∈ recs, r.addr = a ∧ r.c = c := by
  unfold Ix.Cert.recordAt envOfRecs at hrec
  dsimp only at hrec
  cases hget : (buildConsts recs).get? a with
  | none => rw [hget] at hrec; cases hrec
  | some lc =>
    rw [hget] at hrec
    obtain ⟨r, hr, ha, rfl⟩ := buildConsts_get?_some_inv recs hget
    simp only [Option.bind_some, mkLazy_get?, Option.some.injEq] at hrec
    exact ⟨r, hr, ha, hrec⟩

/-! ## Non-collision dichotomy, seed safety, and walked closure -/

/-- Either `calls` hashed two distinct byte strings with the same pure BLAKE3 digest
(`V.HashedCollision`), or `Address.blake3Pure` is injective on `Hashed calls`. -/
theorem noColl_or_hashedCollision (V : View) (extra : List ByteArray) (calls : List (Call F)) :
    V.HashedCollision extra calls ∨
    (∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂) := by
  by_cases hcoll : ∃ b₁ b₂ : ByteArray,
      Hashed calls b₁ ∧ Hashed calls b₂ ∧
      Address.blake3Pure b₁ = Address.blake3Pure b₂ ∧ b₁ ≠ b₂
  · obtain ⟨b₁, b₂, hh₁, hh₂, hblk, hne⟩ := hcoll
    exact .inl (.inl ⟨Address.blake3Pure b₁, b₁, b₂,
      .inr (.inr ⟨hh₁, rfl⟩), hh₂, hne.symm, hblk.symm⟩)
  · right
    intro b₁ b₂ hh₁ hh₂ hblk
    by_contra hne
    exact hcoll ⟨b₁, b₂, hh₁, hh₂, hblk, hne⟩

theorem claimableSeed_not_outsideLogicAt {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {b : Ix.Kernel.Admission.Binding}
    (hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂)
    (recs : List (WalkedRec calls t)) {a : _root_.Address}
    (hs : ClaimableSeed calls t a) :
    ¬ IxVM.Consistency.OutsideLogicAt (envOfRecs b calls recs) a := by
  rintro ⟨c, hrec_a, hbad⟩
  obtain ⟨r, -, hr_addr, rfl⟩ := recordAt_envOfRecs_inv recs hrec_a
  obtain ⟨raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ := hs.selfSafe
  have heq₁ : r.rawBytes = raw₁ :=
    hnoColl r.rawBytes raw₁ r.hhashed hh₁ ((r.hblake.trans hr_addr).trans hb₁.symm)
  have hrc₁ : r.c = c₁ := by
    have h := r.hde
    rw [heq₁, hd₁] at h
    exact (Except.ok.inj h).symm
  rw [hrc₁] at hbad
  rcases hbad with hnot_c1 | ⟨cb, hrec_own, hnot_cb⟩
  · exact hnot_c1 hl₁
  · obtain ⟨rb, -, hrb_addr, rfl⟩ := recordAt_envOfRecs_inv recs hrec_own
    obtain ⟨raw₀, c₀, hh₀, hb₀, hd₀, hown⟩ := hs.ownerCase
    have heq₀ : r.rawBytes = raw₀ :=
      hnoColl r.rawBytes raw₀ r.hhashed hh₀ ((r.hblake.trans hr_addr).trans hb₀.symm)
    have hc10 : c₁ = c₀ := by
      have h := r.hde
      rw [hrc₁, heq₀, hd₀] at h
      exact (Except.ok.inj h).symm
    rw [← hc10] at hown
    rcases hown with hself | ⟨rawB, cb', hhB, hbB, hdB, hlB⟩
    · rw [hself] at hrb_addr
      have heqB : rb.rawBytes = raw₁ :=
        hnoColl rb.rawBytes raw₁ rb.hhashed hh₁ ((rb.hblake.trans hrb_addr).trans hb₁.symm)
      have hcb_eq : rb.c = c₁ := by
        have h := rb.hde
        rw [heqB, hd₁] at h
        exact (Except.ok.inj h).symm
      rw [hcb_eq] at hnot_cb
      exact hnot_cb hl₁
    · have heqB : rb.rawBytes = rawB :=
        hnoColl rb.rawBytes rawB rb.hhashed hhB ((rb.hblake.trans hrb_addr).trans hbB.symm)
      have hcb_eq : rb.c = cb' := by
        have h := rb.hde
        rw [heqB, hdB] at h
        exact (Except.ok.inj h).symm
      rw [hcb_eq] at hnot_cb
      exact hnot_cb hlB

theorem walkedL6_envOfRecs {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable}
    {seeds : List _root_.Address} (recs : List (WalkedRec calls t))
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hseeds : ∀ a ∈ seeds, a ∈ recs.map (·.addr))
    (hcl : RecsClosed recs) :
    WalkedL6 calls t (envOfRecs b calls recs) seeds := by
  obtain ⟨_, hwf_wire, hto, _, _, _⟩ := admitBinding_inv hadm
  have hof : Ix.Kernel.RoleTable.ofBytes b.bytes = some t :=
    (Ix.Kernel.RoleTable.ofBytes_eq_some_iff b.bytes t).mpr ⟨hwf_wire, hto.symm⟩
  refine ⟨?_, ?_, fun a => (envOfRecs b calls recs).consts.contains a = true, ?_, ?_, ?_⟩
  · intro rb hrb
    simp only [envOfRecs, Option.some.injEq] at hrb
    rw [← hrb]
    exact hof
  · intro a lc hget
    obtain ⟨r, -, rfl, rfl⟩ := buildConsts_get?_some_inv recs hget
    simpa only [mkLazy_rawBytes, mkLazy_get?] using ⟨r.hsz, r.c, rfl, r.hde, r.hdeExact⟩
  · intro a hseed
    rcases hseed with ha | ⟨hcont, -⟩
    · change (buildConsts recs).contains a = true
      exact (buildConsts_contains_iff recs a).mpr (hseeds a ha)
    · exact hcont
  · intro a b' _ hedge
    rcases hedge with ⟨c, hrec, hstep⟩ | hground
    · obtain ⟨r, hr, rfl, rfl⟩ := recordAt_envOfRecs_inv recs hrec
      obtain ⟨hown, hrefs⟩ := hcl r hr
      change (buildConsts recs).contains b' = true
      rw [buildConsts_contains_iff]
      rcases hstep with ⟨rfl, hne⟩ | ⟨i, hi, hb⟩
      · exact hown hne
      · exact hrefs i hi b' hb
    · exact hground.1
  · intro a hwk
    change (buildConsts recs).contains a = true at hwk
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hwk
    obtain ⟨lc, hget_elem⟩ := Option.isSome_iff_exists.mp hwk
    have hget : (buildConsts recs).get? a = some lc := by
      rw [Std.HashMap.get?_eq_getElem?]
      exact hget_elem
    obtain ⟨r, -, rfl, rfl⟩ := buildConsts_get?_some_inv recs hget
    refine ⟨r.c, ?_, r.hchecked⟩
    unfold Ix.Cert.recordAt envOfRecs
    dsimp only
    rw [hget]
    rfl

/-! ## Headline theorems: `ClaimPhase` and `L6` -/

/-- **Claim-phase soundness at `S_L6`** (`{ S₀ with Walked := WalkedL6 }`). -/
theorem claimPhase_L6 (hDef : Ix.Cert.RoleClosure.DefaultAdmits) :
    IxVM.Consistency.ClaimPhase S_L6 := by
  intro d value heap calls ev _hbound bytes c hde hpack hscope V seeds b hseeds hRT
  rcases verify_claim_decode_spec hDef ev hde hpack hscope hseeds hRT with
    hcoll | ⟨t, hadm, hbranch⟩
  · exact .inl hcoll
  rcases noColl_or_hashedCollision V
      (bytes :: b.bytes :: IxVM.Consistency.committedImages) calls with hcoll | hnoColl
  · exact .inl hcoll
  rcases hbranch with
    ⟨a, h₁, h₂, h₃, x_rc, x_a, v₁, v₂, cs₁, cs₂,
      rfl, hrc₁, ha₁, ev_ac, ev_rct, -, -, hsub₁, hsub₂⟩ |
    ⟨as, h₁, h₂, x_rc, x_leaves, v₁, cs₁,
      _, hmap_as, hrc₁, hl₁, ev_wlo, -, hsub₁⟩
  · obtain ⟨ext_ac, hseed_cs1⟩ := assert_claimable_spec hrc₁ ha₁ ev_ac
    have hseed_a : ClaimableSeed calls t a := hseed_cs1.mono hsub₁
    obtain ⟨_, recs_cs2, hmem_a, hcl_cs2⟩ :=
      run_check_transitive_spec (hrc₁.mono ext_ac) (S0.addr_mono ext_ac ha₁) ev_rct
    let recs := recs_cs2.map (WalkedRec.mono hsub₂)
    have hseeds_mem : ∀ x ∈ [a], x ∈ recs.map (·.addr) := by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      simpa only [recs, map_addr_walkedRec_mono] using hmem_a
    have hseeds_ok : ∀ x ∈ [a],
        ¬ IxVM.Consistency.OutsideLogicAt (envOfRecs b calls recs) x ∧
        ¬ IxVM.Consistency.InertAt t x := by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact ⟨claimableSeed_not_outsideLogicAt hnoColl recs hseed_a, hseed_a.notInert⟩
    exact .inr ⟨t, envOfRecs b calls recs, hadm,
      envOfRecs_loadedBy b calls recs, hseeds_ok,
      walkedL6_envOfRecs recs hadm hseeds_mem (hcl_cs2.mono hsub₂)⟩
  · rcases walk_leaves_owned_spec (V := V)
        (extra := bytes :: b.bytes :: IxVM.Consistency.committedImages)
        hadm (by simp) as hrc₁ hl₁ ev_wlo with
      hcoll | ⟨_, hseeds_cs1, recs_cs1, hmem_cs1, hcl_cs1⟩
    · exact .inl (hashedCollision_mono hsub₁ hcoll)
    · rw [hmap_as] at hseeds_cs1 hmem_cs1
      let recs := recs_cs1.map (WalkedRec.mono hsub₁)
      have hseeds_mem : ∀ x ∈ seeds, x ∈ recs.map (·.addr) := by
        intro x hx
        simpa only [recs, map_addr_walkedRec_mono] using hmem_cs1 x hx
      have hseeds_ok : ∀ x ∈ seeds,
          ¬ IxVM.Consistency.OutsideLogicAt (envOfRecs b calls recs) x ∧
          ¬ IxVM.Consistency.InertAt t x := by
        intro x hx
        have hs : ClaimableSeed calls t x := (hseeds_cs1 x hx).mono hsub₁
        exact ⟨claimableSeed_not_outsideLogicAt hnoColl recs hs, hs.notInert⟩
      exact .inr ⟨t, envOfRecs b calls recs, hadm,
        envOfRecs_loadedBy b calls recs, hseeds_ok,
        walkedL6_envOfRecs recs hadm hseeds_mem (hcl_cs1.mono hsub₁)⟩

/-- **Obligation `L6` at `S_L6`**. -/
theorem l6_L6 (hDef : Ix.Cert.RoleClosure.DefaultAdmits) :
    IxVM.Consistency.L6 S_L6 :=
  fun _ => claimPhase_L6 hDef

/-- **Claim-phase soundness at `S_L6`** from `DefaultTableBytesUnfolds` (which holds by `rfl`
once `Ix.Kernel.Reader.defaultTableBytes` delegates to `defaultTableBytesOf`). -/
theorem claimPhase_L6_of_unfolds (hUnf : DefaultTableBytesUnfolds) :
    IxVM.Consistency.ClaimPhase S_L6 :=
  claimPhase_L6 (defaultAdmits_of_unfolds hUnf)

/-- **Obligation `L6` at `S_L6`** from `DefaultTableBytesUnfolds`. -/
theorem l6_L6_of_unfolds (hUnf : DefaultTableBytesUnfolds) :
    IxVM.Consistency.L6 S_L6 :=
  l6_L6 (defaultAdmits_of_unfolds hUnf)

/-! ## Conditional bridge to provisional `S₀` -/

/-- Explicit hypothesis isolating the two provisional `S0.Walked` conjuncts beyond `WalkedL6`:
1. `evidenceStored`: every proof theorem in `t.evidence` is present in `E₀.consts` (provisional
   `S0.Walked` omits `E₀.consts.contains a = true` on `t.evidence` seeds);
2. `walkedInLogic`: every record in the `S0.usedRefIdxs` closure is `InLogic` (provisional
   `S0.usedRefIdxs` includes dead `c.sharing` entries that `Convert` never expands into `KExpr`
   for `assert_safety`). -/
structure ClaimExtraFacts : Prop where
  evidenceStored :
    ∀ (calls : List (Call F)) (b : Ix.Kernel.Admission.Binding) (t : Ix.Kernel.RoleTable)
      (E₀ : Ixon.Env) (seeds : List _root_.Address),
      Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t →
      IxVM.Consistency.LoadedBy calls E₀ →
      WalkedL6 calls t E₀ seeds →
      ∀ a, (∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList) →
        E₀.consts.contains a = true
  walkedInLogic :
    ∀ (calls : List (Call F)) (b : Ix.Kernel.Admission.Binding) (t : Ix.Kernel.RoleTable)
      (E₀ : Ixon.Env) (seeds : List _root_.Address) (Wk : _root_.Address → Prop),
      Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t →
      IxVM.Consistency.LoadedBy calls E₀ →
      (∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a) →
      (∀ a, (a ∈ seeds ∨ (E₀.consts.contains a = true ∧
          ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList)) → Wk a) →
      (∀ a b', Wk a → (S0.WalkEdge E₀ a b' ∨ Ix.Cert.GroundEdgeAt t E₀ a b') → Wk b') →
      (∀ a, Wk a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧
        ((∃ ms, c.info = .muts ms) ∨ S0.CheckedAt calls t a)) →
      ∀ a c, Wk a → Ix.Cert.recordAt E₀ a = some c → IxVM.Consistency.InLogic c

theorem walked_S₀_of_walkedL6
    (hExtra : ClaimExtraFacts)
    {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hseedOk : ∀ a ∈ seeds,
      ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a)
    (hwalk : WalkedL6 calls t E₀ seeds) :
    S0.Walked calls t E₀ seeds := by
  have hev := hExtra.evidenceStored calls b t E₀ seeds hadm hload hwalk
  obtain ⟨_, _, Wk, hwk_seed, hwk_edge, hwk_node⟩ := hwalk
  refine ⟨Wk, ?_, hwk_edge, ?_⟩
  · intro a h
    rcases h with ha | hev_a
    · exact hwk_seed a (.inl ha)
    · exact hwk_seed a (.inr ⟨hev a hev_a, hev_a⟩)
  · intro a hwk_a
    obtain ⟨c, hrec, hchk⟩ := hwk_node a hwk_a
    exact ⟨c, hrec,
      hExtra.walkedInLogic calls b t E₀ seeds Wk hadm hload hseedOk
        hwk_seed hwk_edge hwk_node a c hwk_a hrec,
      hchk⟩

/-- **Claim-phase soundness at provisional `S₀`**, given `ClaimExtraFacts`. -/
theorem claimPhase_S₀
    (hDef : Ix.Cert.RoleClosure.DefaultAdmits)
    (hExtra : ClaimExtraFacts) :
    IxVM.Consistency.ClaimPhase S₀ := by
  intro d value heap calls ev hbound bytes c hde hpack hscope V seeds b hseeds hRT
  rcases claimPhase_L6 hDef d value heap calls ev hbound bytes c hde hpack hscope
      V seeds b hseeds hRT with hcoll | ⟨t, E₀, hadm, hload, hseedOk, hwalk⟩
  · exact .inl hcoll
  · exact .inr ⟨t, E₀, hadm, hload, hseedOk,
      walked_S₀_of_walkedL6 hExtra hadm hload hseedOk hwalk⟩

/-- **Obligation `L6` at provisional `S₀`**, given `ClaimExtraFacts`. -/
theorem l6_S₀
    (hDef : Ix.Cert.RoleClosure.DefaultAdmits)
    (hExtra : ClaimExtraFacts) :
    IxVM.Consistency.L6 S₀ :=
  fun _ => claimPhase_S₀ hDef hExtra

/-- **Claim-phase soundness at provisional `S₀`** from `DefaultTableBytesUnfolds` and
`ClaimExtraFacts`. -/
theorem claimPhase_S₀_of_unfolds
    (hUnf : DefaultTableBytesUnfolds)
    (hExtra : ClaimExtraFacts) :
    IxVM.Consistency.ClaimPhase S₀ :=
  claimPhase_S₀ (defaultAdmits_of_unfolds hUnf) hExtra

/-- **Obligation `L6` at provisional `S₀`** from `DefaultTableBytesUnfolds` and
`ClaimExtraFacts`. -/
theorem l6_S₀_of_unfolds
    (hUnf : DefaultTableBytesUnfolds)
    (hExtra : ClaimExtraFacts) :
    IxVM.Consistency.L6 S₀ :=
  l6_S₀ (defaultAdmits_of_unfolds hUnf) hExtra

end IxVM.Refinement.Claim
