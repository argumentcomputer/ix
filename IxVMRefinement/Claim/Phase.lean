import IxVMRefinement.Claim.DefaultAdmits
import IxVMRefinement.Claim.Walk

/-! # Obligation L6: Claim-phase soundness and walked-closure assembly

Assembles `IxVM.Consistency.ClaimPhase` and `IxVM.Consistency.L6` from:
* `verify_claim_decode_spec` (`Decode.lean`) for claim ingestion, BLAKE3 digest verification,
  role-table context loading under `ReaderTable`, and assumption-tree decoding;
* `assert_claimable_spec`, `run_check_transitive_spec`, and `walk_leaves_owned_spec`
  (`Walk.lean`) for seed-safety/inertness refusals, member/constant `CheckedAtFull` witnesses, and
  depth-decreasing edge-closed record walking;
* `envOfRecs`, constructing the `Ixon.Env` witness `E₀` from all canonical constants and blobs
  hashed in `calls` together with the walked records `recs`, separating `Wk` from `E₀.consts`, and
  discharging `LoadedBy`, `¬ OutsideLogicAt`, `¬ InertAt`, and `WalkedL6` (as well as provisional
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

/-- Enriched walked-closure predicate established by `IxVM::verify_claim`:
* exposes the admitted role-binding `bAddr` (`admitBinding Address.admissionHash` and
  `RoleTable.ofBytes`);
* records `E₀.consts` size and exact-decode invariants (`deConstant` and `deConstantExact`);
* records completeness of `E₀.blobs` on all byte strings hashed in `calls` and completeness of
  `E₀.consts` on all canonical constants hashed in `calls`;
* separates the walked closure `(Wk, rank)` from `E₀.consts`, giving strict rank decrease
  `rank b < rank a` along every `S0.WalkEdge E₀ a b` together with full `CheckedAtFull` /
  `MutsMemberCheckedAtFull` check witnesses at every walked address. -/
def WalkedL6 (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (seeds : List _root_.Address) : Prop :=
  ∃ bAddr : _root_.Address,
    (∃ rb, E₀.roleBinding = some rb ∧ rb.address = bAddr ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨rb.address, rb.bytes⟩ = .ok t) ∧
    (∀ rb, E₀.roleBinding = some rb → Ix.Kernel.RoleTable.ofBytes rb.bytes = some t) ∧
    (∀ a lc, E₀.consts.get? a = some lc →
      lc.rawBytes.size < 4294967296 ∧
      ∃ c, lc.get? = some c ∧
        Ixon.deConstant lc.rawBytes = .ok c ∧
        Ixon.deConstantExact lc.rawBytes = .ok c) ∧
    (∀ bytes, Hashed calls bytes →
      E₀.blobs.get? (Address.blake3Pure bytes) = some bytes) ∧
    (∀ bytes c, Hashed calls bytes → bytes.size < 4294967296 →
      Ixon.deConstant bytes = .ok c → Ixon.deConstantExact bytes = .ok c →
      ∃ lc, E₀.consts.get? (Address.blake3Pure bytes) = some lc ∧
        lc.rawBytes = bytes ∧ lc.get? = some c) ∧
    ∃ (Wk : _root_.Address → Prop) (rank : _root_.Address → Nat),
      (∀ a ∈ seeds, Wk a) ∧
      (∀ a b, Wk a → S0.WalkEdge E₀ a b → Wk b ∧ rank b < rank a) ∧
      ∀ a, Wk a → ∃ c, Ix.Cert.recordAt E₀ a = some c ∧
        ((∃ ms, c.info = .muts ms ∧
          ∀ (k : Nat), k < ms.size → MutsMemberCheckedAtFull calls bAddr t a ms k) ∨
         CheckedAtFull calls bAddr t a)

/-- Seams bundle equipping `S₀` with `WalkedL6`. -/
def S_L6 : IxVM.Consistency.Seams :=
  { S₀ with Walked := WalkedL6 }

/-! ## Constructing `E₀ : Ixon.Env` from hashed constants, walked records, and hashed blobs -/

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

private theorem contains_insert_self {V : Type}
    (m : Std.HashMap _root_.Address V) (k : _root_.Address) (v : V) :
    (m.insert k v).contains k = true := by
  simp [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_insert]

private theorem contains_insert_of_eq {V : Type}
    (m : Std.HashMap _root_.Address V) {k k' : _root_.Address} (v : V) (heq : k = k') :
    (m.insert k v).contains k' = true := by
  subst heq
  exact contains_insert_self m k v

private theorem contains_insert_of_contains {V : Type}
    (m : Std.HashMap _root_.Address V) (k k' : _root_.Address) (v' : V)
    (h : m.contains k = true) :
    (m.insert k' v').contains k = true := by
  simp only [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_insert] at h ⊢
  split
  · rfl
  · exact h

/-- Single-call `Blake3::hash` predicate matching `Hashed`. -/
def CallHashes (cl : Call F) (bytes : ByteArray) : Prop :=
  cl.name = blake3Hash ∧ ∃ input : SourceValue F,
    cl.args = [input] ∧ Bytes.RepByteStream byteStreamEnum cl.heap bytes.data.toList input

/-- `Bytes.RepByteStream` determinism makes `CallHashes` functional per call `cl`. -/
theorem callHashes_det {cl : Call F} {bytes₁ bytes₂ : ByteArray}
    (h₁ : CallHashes cl bytes₁) (h₂ : CallHashes cl bytes₂) :
    bytes₁ = bytes₂ := by
  obtain ⟨_, input₁, hargs₁, hrep₁⟩ := h₁
  obtain ⟨_, input₂, hargs₂, hrep₂⟩ := h₂
  rw [hargs₁] at hargs₂
  injection hargs₂ with hinp
  subst hinp
  exact ByteArray.ext (Array.toList_inj.mp
    (Bytes.repByteStream_inj U32.Goldilocks.compatible hrep₁ hrep₂))

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

theorem buildBlobs_contains_of_hashed (calls : List (Call F)) {bytes : ByteArray}
    (hh : Hashed calls bytes) :
    (buildBlobs calls).contains (Address.blake3Pure bytes) = true := by
  induction calls with
  | nil =>
    obtain ⟨_, hmem, _⟩ := hh
    cases hmem
  | cons cl cls ih =>
    obtain ⟨cl', hmem, hch⟩ := hh
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp only [buildBlobs]
      split
      · rename_i hex
        have hb0 : Classical.choose hex = bytes :=
          callHashes_det (Classical.choose_spec hex) hch
        rw [hb0]
        exact contains_insert_self _ _ _
      · rename_i hnex
        exact absurd ⟨bytes, hch⟩ hnex
    · have hcont : (buildBlobs cls).contains (Address.blake3Pure bytes) = true :=
        ih ⟨cl', htl, hch⟩
      simp only [buildBlobs]
      split
      · exact contains_insert_of_contains _ _ _ _ hcont
      · exact hcont

theorem buildBlobs_get?_of_hashed {calls : List (Call F)}
    (hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂)
    {bytes : ByteArray} (hh : Hashed calls bytes) :
    (buildBlobs calls).get? (Address.blake3Pure bytes) = some bytes := by
  have hcont := buildBlobs_contains_of_hashed calls hh
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hcont
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hcont
  rw [← Std.HashMap.get?_eq_getElem?] at hb'
  obtain ⟨hh', hblk'⟩ := buildBlobs_get?_some_inv calls hb'
  have heq : b' = bytes := hnoColl b' bytes hh' hh hblk'
  rwa [heq] at hb'

/-- Canonical constant byte-image predicate matching `load_verified_constant`. -/
def IsCanonicalConst (bytes : ByteArray) (c : Ixon.Constant) : Prop :=
  bytes.size < 4294967296 ∧
  Ixon.deConstant bytes = .ok c ∧
  Ixon.deConstantExact bytes = .ok c

/-- Populate `E₀.consts` with all canonical constants hashed by `Blake3::hash` calls in `calls`. -/
noncomputable def buildAllConsts : List (Call F) → Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => {}
  | cl :: cls =>
    haveI := Classical.propDecidable (∃ bytes c, CallHashes cl bytes ∧ IsCanonicalConst bytes c)
    if hex : ∃ bytes c, CallHashes cl bytes ∧ IsCanonicalConst bytes c then
      let b0 := Classical.choose hex
      let c0 := Classical.choose (Classical.choose_spec hex)
      (buildAllConsts cls).insert (Address.blake3Pure b0) (mkLazy b0 c0)
    else
      buildAllConsts cls

theorem buildAllConsts_get?_some_inv (calls : List (Call F))
    {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : (buildAllConsts calls).get? a = some lc) :
    Hashed calls lc.rawBytes ∧
    Address.blake3Pure lc.rawBytes = a ∧
    lc.rawBytes.size < 4294967296 ∧
    ∃ c, lc.get? = some c ∧
      Ixon.deConstant lc.rawBytes = .ok c ∧
      Ixon.deConstantExact lc.rawBytes = .ok c := by
  induction calls with
  | nil =>
    simp only [buildAllConsts, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h
    cases h
  | cons cl cls ih =>
    simp only [buildAllConsts] at h
    split at h
    · rename_i hex
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
      split at h
      · rename_i heq
        injection h with hlc
        subst hlc
        obtain ⟨hch, hsz, hde, hdeEx⟩ := Classical.choose_spec (Classical.choose_spec hex)
        simpa only [mkLazy_rawBytes, mkLazy_get?] using
          ⟨⟨cl, List.mem_cons_self, hch⟩, beq_iff_eq.mp heq, hsz, _, rfl, hde, hdeEx⟩
      · rw [← Std.HashMap.get?_eq_getElem?] at h
        obtain ⟨hh, ha, hsz, c, hget_c, hde, hdeEx⟩ := ih h
        exact ⟨hashed_mono (fun _ hm => List.mem_cons_of_mem _ hm) hh,
          ha, hsz, c, hget_c, hde, hdeEx⟩
    · obtain ⟨hh, ha, hsz, c, hget_c, hde, hdeEx⟩ := ih h
      exact ⟨hashed_mono (fun _ hm => List.mem_cons_of_mem _ hm) hh,
        ha, hsz, c, hget_c, hde, hdeEx⟩

theorem buildAllConsts_contains_of_hashed (calls : List (Call F))
    {bytes : ByteArray} {c : Ixon.Constant}
    (hh : Hashed calls bytes) (hcan : IsCanonicalConst bytes c) :
    (buildAllConsts calls).contains (Address.blake3Pure bytes) = true := by
  induction calls with
  | nil =>
    obtain ⟨_, hmem, _⟩ := hh
    cases hmem
  | cons cl cls ih =>
    obtain ⟨cl', hmem, hch⟩ := hh
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp only [buildAllConsts]
      split
      · rename_i hex
        have hb0 : Classical.choose hex = bytes :=
          callHashes_det (Classical.choose_spec (Classical.choose_spec hex)).1 hch
        exact contains_insert_of_eq _ _ (congrArg Address.blake3Pure hb0)
      · rename_i hnex
        exact absurd ⟨bytes, c, hch, hcan⟩ hnex
    · have hcont := ih ⟨cl', htl, hch⟩
      simp only [buildAllConsts]
      split
      · exact contains_insert_of_contains _ _ _ _ hcont
      · exact hcont

/-- Overlay a list of walked records onto a base constant map. -/
def buildConstsOn {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    (base : Std.HashMap _root_.Address Ixon.LazyConstant) :
    List (WalkedRec calls bAddr t) → Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => base
  | r :: rs => (buildConstsOn base rs).insert r.addr (mkLazy r.rawBytes r.c)

theorem buildConstsOn_get?_some_inv {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable}
    (recs : List (WalkedRec calls bAddr t)) {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : (buildConstsOn (buildAllConsts calls) recs).get? a = some lc) :
    Hashed calls lc.rawBytes ∧
    Address.blake3Pure lc.rawBytes = a ∧
    lc.rawBytes.size < 4294967296 ∧
    ∃ c, lc.get? = some c ∧
      Ixon.deConstant lc.rawBytes = .ok c ∧
      Ixon.deConstantExact lc.rawBytes = .ok c := by
  induction recs with
  | nil => exact buildAllConsts_get?_some_inv calls h
  | cons r rs ih =>
    simp only [buildConstsOn, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i heq
      injection h with hlc
      subst hlc
      simpa only [mkLazy_rawBytes, mkLazy_get?] using
        ⟨r.hhashed, r.hblake.trans (beq_iff_eq.mp heq), r.hsz, r.c, rfl, r.hde, r.hdeExact⟩
    · rw [← Std.HashMap.get?_eq_getElem?] at h
      exact ih h

theorem buildConstsOn_contains_of_base {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable}
    (base : Std.HashMap _root_.Address Ixon.LazyConstant)
    (recs : List (WalkedRec calls bAddr t)) {a : _root_.Address}
    (ha : base.contains a = true) :
    (buildConstsOn base recs).contains a = true := by
  induction recs with
  | nil => exact ha
  | cons _ _ ih => exact contains_insert_of_contains _ _ _ _ ih

theorem buildConstsOn_contains_of_mem {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable}
    (base : Std.HashMap _root_.Address Ixon.LazyConstant)
    (recs : List (WalkedRec calls bAddr t)) {r : WalkedRec calls bAddr t}
    (hr : r ∈ recs) :
    (buildConstsOn base recs).contains r.addr = true := by
  induction recs with
  | nil => cases hr
  | cons r₀ rs ih =>
    rcases List.mem_cons.mp hr with rfl | htl
    · exact contains_insert_self _ _ _
    · exact contains_insert_of_contains _ _ _ _ (ih htl)

/-- Witness environment `E₀` built from the role binding `b`, all canonical constants hashed in
`calls` overlaid with `recs`, and all blobs hashed in `calls`. -/
noncomputable def envOfRecs {t : Ix.Kernel.RoleTable} (b : Ix.Kernel.Admission.Binding)
    (calls : List (Call F)) (recs : List (WalkedRec calls b.address t)) : Ixon.Env :=
  { consts := buildConstsOn (buildAllConsts calls) recs
    blobs := buildBlobs calls
    roleBinding := some { address := b.address, bytes := b.bytes } }

theorem envOfRecs_loadedBy {t : Ix.Kernel.RoleTable} (b : Ix.Kernel.Admission.Binding)
    (calls : List (Call F)) (recs : List (WalkedRec calls b.address t)) :
    IxVM.Consistency.LoadedBy calls (envOfRecs b calls recs) := by
  refine ⟨fun a lc hget => ?_, fun a bytes hget => buildBlobs_get?_some_inv calls hget⟩
  obtain ⟨hh, hblk, _, _⟩ := buildConstsOn_get?_some_inv recs hget
  exact ⟨hh, hblk⟩

theorem recordAt_envOfRecs_inv {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {b : Ix.Kernel.Admission.Binding}
    (recs : List (WalkedRec calls b.address t)) {a : _root_.Address} {c : Ixon.Constant}
    (hrec : Ix.Cert.recordAt (envOfRecs b calls recs) a = some c) :
    ∃ rawBytes : ByteArray,
      Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = a ∧
      Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c := by
  unfold Ix.Cert.recordAt envOfRecs at hrec
  dsimp only at hrec
  cases hget : (buildConstsOn (buildAllConsts calls) recs).get? a with
  | none => rw [hget] at hrec; cases hrec
  | some lc =>
    rw [hget] at hrec
    obtain ⟨hh, hblk, _, c', hget_c', hde, hdeEx⟩ := buildConstsOn_get?_some_inv recs hget
    simp only [Option.bind_some] at hrec
    rw [hrec] at hget_c'
    injection hget_c' with hc_eq
    subst hc_eq
    exact ⟨lc.rawBytes, hh, hblk, hde, hdeEx⟩

private theorem envOfRecs_consts_get?_of_contains {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {b : Ix.Kernel.Admission.Binding}
    (hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂)
    (recs : List (WalkedRec calls b.address t))
    {a : _root_.Address} {bytes : ByteArray} {c : Ixon.Constant}
    (hcont : (buildConstsOn (buildAllConsts calls) recs).contains a = true)
    (hh : Hashed calls bytes)
    (hblk : Address.blake3Pure bytes = a)
    (hde : Ixon.deConstant bytes = .ok c) :
    ∃ lc, (envOfRecs b calls recs).consts.get? a = some lc ∧
      lc.rawBytes = bytes ∧ lc.get? = some c := by
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hcont
  obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hcont
  rw [← Std.HashMap.get?_eq_getElem?] at hlc
  obtain ⟨hh_lc, hblk_lc, _, c', hget_c', hde_lc, _⟩ := buildConstsOn_get?_some_inv recs hlc
  have hraw : lc.rawBytes = bytes := hnoColl lc.rawBytes bytes hh_lc hh (hblk_lc.trans hblk.symm)
  rw [hraw] at hde_lc
  have hc_eq : c' = c := Except.ok.inj (hde_lc.symm.trans hde)
  subst hc_eq
  exact ⟨lc, hlc, hraw, hget_c'⟩

theorem recordAt_envOfRecs_of_mem {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {b : Ix.Kernel.Admission.Binding}
    (hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂)
    (recs : List (WalkedRec calls b.address t)) {r : WalkedRec calls b.address t}
    (hr : r ∈ recs) :
    Ix.Cert.recordAt (envOfRecs b calls recs) r.addr = some r.c := by
  have hcont := buildConstsOn_contains_of_mem (buildAllConsts calls) recs hr
  obtain ⟨lc, hget, _, hlc_c⟩ :=
    envOfRecs_consts_get?_of_contains hnoColl recs hcont r.hhashed r.hblake r.hde
  unfold Ix.Cert.recordAt
  rw [hget]
  simpa using hlc_c

/-! ## Non-collision dichotomy, seed safety, rank acyclicity, and walked closure -/

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
    (recs : List (WalkedRec calls b.address t)) {a : _root_.Address}
    (hs : ClaimableSeed calls t a) :
    ¬ IxVM.Consistency.OutsideLogicAt (envOfRecs b calls recs) a := by
  rintro ⟨c, hrec_a, hbad⟩
  obtain ⟨raw_a, hh_a, hb_a, hde_a, _⟩ := recordAt_envOfRecs_inv recs hrec_a
  obtain ⟨raw₁, c₁, hh₁, hb₁, hd₁, hl₁⟩ := hs.selfSafe
  have heq₁ : raw_a = raw₁ := hnoColl raw_a raw₁ hh_a hh₁ (hb_a.trans hb₁.symm)
  have hc₁ : c = c₁ := by
    have h := hde_a
    rw [heq₁, hd₁] at h
    exact (Except.ok.inj h).symm
  rw [hc₁] at hbad
  rcases hbad with hnot_c1 | ⟨cb, hrec_own, hnot_cb⟩
  · exact hnot_c1 hl₁
  · obtain ⟨raw_own, hh_own, hb_own, hde_own, _⟩ := recordAt_envOfRecs_inv recs hrec_own
    obtain ⟨raw₀, c₀, hh₀, hb₀, hd₀, hown⟩ := hs.ownerCase
    have heq₀ : raw_a = raw₀ := hnoColl raw_a raw₀ hh_a hh₀ (hb_a.trans hb₀.symm)
    have hc10 : c₁ = c₀ := by
      have h := hde_a
      rw [hc₁, heq₀, hd₀] at h
      exact (Except.ok.inj h).symm
    rw [← hc10] at hown
    rcases hown with hself | ⟨rawB, cb', hhB, hbB, hdB, hlB⟩
    · rw [hself] at hb_own
      have heqB : raw_own = raw₁ := hnoColl raw_own raw₁ hh_own hh₁ (hb_own.trans hb₁.symm)
      have hcb_eq : cb = c₁ := by
        have h := hde_own
        rw [heqB, hd₁] at h
        exact (Except.ok.inj h).symm
      rw [hcb_eq] at hnot_cb
      exact hnot_cb hl₁
    · have heqB : raw_own = rawB := hnoColl raw_own rawB hh_own hhB (hb_own.trans hbB.symm)
      have hcb_eq : cb = cb' := by
        have h := hde_own
        rw [heqB, hdB] at h
        exact (Except.ok.inj h).symm
      rw [hcb_eq] at hnot_cb
      exact hnot_cb hlB

private def minList : List Nat → Nat
  | [] => 0
  | [x] => x
  | x :: y :: xs =>
    let m := minList (y :: xs)
    if x ≤ m then x else m

private theorem minList_le_of_mem : ∀ {xs : List Nat} {d : Nat}, d ∈ xs → minList xs ≤ d
  | [], _, h => by cases h
  | [x], d, h => by
    rcases List.mem_singleton.mp h with rfl
    exact Nat.le_refl _
  | x :: y :: xs, d, h => by
    simp only [minList]
    rcases List.mem_cons.mp h with rfl | htl
    · split_ifs <;> omega
    · have hm := minList_le_of_mem htl
      split_ifs <;> omega

private theorem minList_mem_of_ne_nil : ∀ {xs : List Nat}, xs ≠ [] → minList xs ∈ xs
  | [], h => absurd rfl h
  | [x], _ => List.mem_cons_self
  | x :: y :: xs, _ => by
    simp only [minList]
    have hrec : minList (y :: xs) ∈ y :: xs := minList_mem_of_ne_nil (by simp)
    split_ifs
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hrec

private def depthsAt {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    (recs : List (WalkedRec calls bAddr t)) (a : _root_.Address) : List Nat :=
  (recs.filter (fun r => r.addr == a)).map (·.depth)

private def rankOfRecs {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    (recs : List (WalkedRec calls bAddr t)) (a : _root_.Address) : Nat :=
  minList (depthsAt recs a)

private theorem rankOfRecs_le_of_mem {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {recs : List (WalkedRec calls bAddr t)}
    {r : WalkedRec calls bAddr t} (hr : r ∈ recs) :
    rankOfRecs recs r.addr ≤ r.depth := by
  apply minList_le_of_mem
  unfold depthsAt
  exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, beq_self_eq_true _⟩, rfl⟩

private theorem exists_rec_eq_rankOfRecs {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {recs : List (WalkedRec calls bAddr t)} {a : _root_.Address}
    (ha : a ∈ recs.map (·.addr)) :
    ∃ r ∈ recs, r.addr = a ∧ r.depth = rankOfRecs recs a := by
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp ha
  have hne : depthsAt recs r₀.addr ≠ [] := by
    intro hempty
    have hmem : r₀.depth ∈ depthsAt recs r₀.addr :=
      List.mem_map.mpr ⟨r₀, List.mem_filter.mpr ⟨hr₀, beq_self_eq_true _⟩, rfl⟩
    rw [hempty] at hmem
    cases hmem
  have hmin := minList_mem_of_ne_nil hne
  obtain ⟨r, hr_filt, hdep⟩ := List.mem_map.mp hmin
  obtain ⟨hr_mem, hr_beq⟩ := List.mem_filter.mp hr_filt
  exact ⟨r, hr_mem, beq_iff_eq.mp hr_beq, hdep⟩

theorem walkedL6_envOfRecs {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address}
    (hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂)
    (recs : List (WalkedRec calls b.address t))
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hseeds : ∀ a ∈ seeds, a ∈ recs.map (·.addr))
    (hcl : RecsClosed recs) :
    WalkedL6 calls t (envOfRecs b calls recs) seeds := by
  obtain ⟨_, hwf_wire, hto, _, _, _⟩ := admitBinding_inv hadm
  have hof : Ix.Kernel.RoleTable.ofBytes b.bytes = some t :=
    (Ix.Kernel.RoleTable.ofBytes_eq_some_iff b.bytes t).mpr ⟨hwf_wire, hto.symm⟩
  refine ⟨b.address,
    ⟨{ address := b.address, bytes := b.bytes }, rfl, rfl, by cases b; exact hadm⟩,
    ?_, ?_, ?_, ?_,
    fun a => a ∈ recs.map (·.addr), rankOfRecs recs, hseeds, ?_, ?_⟩
  · intro rb hrb
    simp only [envOfRecs, Option.some.injEq] at hrb
    rw [← hrb]
    exact hof
  · intro a lc hget
    obtain ⟨_, _, hsz, c, hlc_c, hde, hdeEx⟩ := buildConstsOn_get?_some_inv recs hget
    exact ⟨hsz, c, hlc_c, hde, hdeEx⟩
  · intro bytes hh
    exact buildBlobs_get?_of_hashed hnoColl hh
  · intro bytes c hh hsz hde hdeEx
    have hcont := buildConstsOn_contains_of_base (buildAllConsts calls) recs
      (buildAllConsts_contains_of_hashed calls hh ⟨hsz, hde, hdeEx⟩)
    exact envOfRecs_consts_get?_of_contains hnoColl recs hcont hh rfl hde
  · intro a b' hwk ⟨c, hrec_a, hstep⟩
    obtain ⟨r_min, hr_min, hr_addr, hr_dep⟩ := exists_rec_eq_rankOfRecs hwk
    have hrec_min := recordAt_envOfRecs_of_mem hnoColl recs hr_min
    rw [hr_addr, hrec_a] at hrec_min
    injection hrec_min with hc_eq
    obtain ⟨hown, hrefs⟩ := hcl r_min hr_min
    rw [hr_addr, ← hc_eq] at hown
    rw [← hc_eq] at hrefs
    rcases hstep with ⟨rfl, hne⟩ | ⟨i, hi, hb⟩
    · obtain ⟨r', hr', ha', hlt'⟩ := hown hne
      have hle' := rankOfRecs_le_of_mem hr'
      rw [ha'] at hle'
      exact ⟨List.mem_map.mpr ⟨r', hr', ha'⟩, by omega⟩
    · obtain ⟨r', hr', ha', hlt'⟩ := hrefs i hi b' hb
      have hle' := rankOfRecs_le_of_mem hr'
      rw [ha'] at hle'
      exact ⟨List.mem_map.mpr ⟨r', hr', ha'⟩, by omega⟩
  · intro a hwk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hwk
    exact ⟨r.c, recordAt_envOfRecs_of_mem hnoColl recs hr, r.hchecked⟩

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
    obtain ⟨_, recs_cs2, hmem_a, hcl_cs2, _⟩ :=
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
      walkedL6_envOfRecs hnoColl recs hadm hseeds_mem (hcl_cs2.mono hsub₂)⟩
  · rcases walk_leaves_owned_spec (V := V)
        (extra := bytes :: b.bytes :: IxVM.Consistency.committedImages)
        hadm (by simp) as hrc₁ hl₁ ev_wlo with
      hcoll | ⟨_, hseeds_cs1, recs_cs1, hmem_cs1, hcl_cs1, _⟩
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
        walkedL6_envOfRecs hnoColl recs hadm hseeds_mem (hcl_cs1.mono hsub₁)⟩

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

/-- Explicit hypothesis isolating the provisional `S0.Walked` obligations beyond `WalkedL6`
(unconditional evidence-proof / ground-edge closure and `InLogic` on `S0.usedRefIdxs`). -/
structure ClaimExtraFacts : Prop where
  walkedBridge :
    ∀ (calls : List (Call F)) (b : Ix.Kernel.Admission.Binding) (t : Ix.Kernel.RoleTable)
      (E₀ : Ixon.Env) (seeds : List _root_.Address),
      Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t →
      IxVM.Consistency.LoadedBy calls E₀ →
      (∀ a ∈ seeds, ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a) →
      WalkedL6 calls t E₀ seeds →
      S0.Walked calls t E₀ seeds

theorem walked_S₀_of_walkedL6
    (hExtra : ClaimExtraFacts)
    {calls : List (Call F)} {b : Ix.Kernel.Admission.Binding} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {seeds : List _root_.Address}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash b = .ok t)
    (hload : IxVM.Consistency.LoadedBy calls E₀)
    (hseedOk : ∀ a ∈ seeds,
      ¬ IxVM.Consistency.OutsideLogicAt E₀ a ∧ ¬ IxVM.Consistency.InertAt t a)
    (hwalk : WalkedL6 calls t E₀ seeds) :
    S0.Walked calls t E₀ seeds :=
  hExtra.walkedBridge calls b t E₀ seeds hadm hload hseedOk hwalk

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
