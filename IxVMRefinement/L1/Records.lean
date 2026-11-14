import IxVMRefinement.L1.Ingress
import IxVMRefinement.Core.Seams
import IxVMRefinement.Obs.KernelCheck0
import IxC.Ixon.Verify.Framing
import Ix.Cert.Stream

/-! # L1 record seam (`LoadedL1`), `Records` obligation, and `LoadFacts` companions

Completes the `L1` (`Records`) layer by packaging `Ingress::get_ci`'s trace-level
outcome (`GetCIRawResult`, `get_ci_spec`) into an environment-level loaded-record
seam `LoadedL1` (`RawCIRep`, `RawCIPtrRep`) over a collision-proof `E₀ : Ixon.Env`
satisfying `LoadedBy cs E₀`:

1. **`LoadedL1` and `records_L1` / `l1_L1`**:
   `theorem records_L1 : IxVM.Consistency.Records { Core.S₀ with loaded := LoadedL1 }`
   and `theorem l1_L1 : IxVM.Consistency.L1 { Core.S₀ with loaded := LoadedL1 } := records_L1`,
   together with heap monotonicity (`RawCIRep.mono`, `RawCIPtrRep.mono`, `LoadedL1.mono`)
   and environment monotonicity (`RawCIRep.env_mono`, `RawCIPtrRep.env_mono`,
   `LoadedL1.env_mono`).
2. **Safety / `InLogic` / `OutsideLogicAt` & parent-block companions for `L6` and `L7`**:
   exact equivalence `defnIsUnsafeCI d = false ↔ Ix.Kernel.Reader.safetyDecline d = none`,
   observed-derivation specification `is_unsafe_ci_raw_spec` for `KernelCheck::is_unsafe_ci`
   connecting `.field 1` to `OutsideLogicAt E₀ a` and `.field 0` to `InLogic` / member
   safety, and unconditional parent-block presence `Ix.Cert.recordAt E₀ p.block = some cb`
   for all projection variants (`dPrj`, `iPrj`, `cPrj`, `rPrj`).
3. **Conditional `CIPtrRep` bridges (`∀ t : Ix.Kernel.RoleTable`)**:
   `RawCIRep.toCIRep`, `RawCIPtrRep.toCIPtrRep`, `LoadedL1.toCIPtrRep`, and direct
   projection-loader bridges `get_ci_iprj_toCIPtrRep` and `get_ci_cprj_toCIPtrRep`.
4. **`LoadFacts` companions (`Core/Good.lean`)**:
   `indRecord_of_get_ci` (and `StoredCanonical` / uncached variants),
   `inductRecord_raw_of_get_ci`, `inductRecord_of_get_ci_strong`, `inductRecord_of_get_ci`,
   and `canonical_of_wireWF` (plus `emptyTablesConstant_wireWF` and `projConstant_wireWF`). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Obs

/-! ## Section 1: `mkLazyConst`, `Std.HashMap` helpers, and collision-proof `Ixon.Env` builders -/

/-- Build a standalone cached `Ixon.LazyConstant` holding `raw` and `c`. -/
def mkLazyConst (raw : ByteArray) (c : Ixon.Constant) : Ixon.LazyConstant :=
  { buf := raw, off := 0, len := raw.size, cache := some c }

@[simp] theorem mkLazyConst_get? (raw : ByteArray) (c : Ixon.Constant) :
    (mkLazyConst raw c).get? = some c := rfl

@[simp] theorem mkLazyConst_rawBytes (raw : ByteArray) (c : Ixon.Constant) :
    (mkLazyConst raw c).rawBytes = raw := by
  simp [mkLazyConst, Ixon.LazyConstant.rawBytes]

private theorem recordAt_of_get? {E : Ixon.Env} {k : _root_.Address}
    {lc : Ixon.LazyConstant} {c : Ixon.Constant}
    (h1 : E.consts.get? k = some lc) (h2 : lc.get? = some c) :
    Ix.Cert.recordAt E k = some c := by
  unfold Ix.Cert.recordAt
  rw [h1]
  exact h2

private theorem hashmap_get?_empty {α : Type} (k : _root_.Address) :
    ({} : Std.HashMap _root_.Address α).get? k = none := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

private theorem hashmap_get?_insert_self {α : Type} (s : Std.HashMap _root_.Address α)
    (k : _root_.Address) (v : α) :
    (s.insert k v).get? k = some v := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]

private theorem hashmap_get?_insert_ne {α : Type} (s : Std.HashMap _root_.Address α)
    {k q : _root_.Address} (hne : k ≠ q) (v : α) :
    (s.insert k v).get? q = s.get? q := by
  have hbeq : (k == q) = false := by
    cases hb : (k == q)
    · rfl
    · exact absurd (beq_iff_eq.mp hb) hne
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbeq]
  simp [Std.HashMap.get?_eq_getElem?]

private theorem hashmap_get?_insert_inv {α : Type} {s : Std.HashMap _root_.Address α}
    {k q : _root_.Address} {v w : α}
    (h : (s.insert k v).get? q = some w) :
    (k = q ∧ w = v) ∨ s.get? q = some w := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i same
    injection h with hw
    exact .inl ⟨beq_iff_eq.mp same, hw.symm⟩
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    exact .inr h

private theorem hashmap_exists_get?_insert {α : Type} (s : Std.HashMap _root_.Address α)
    (k q : _root_.Address) (v : α) (hex : ∃ v₀, s.get? q = some v₀) :
    ∃ w, (s.insert k v).get? q = some w := by
  obtain ⟨v₀, hv₀⟩ := hex
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  split
  · exact ⟨v, rfl⟩
  · rw [← Std.HashMap.get?_eq_getElem?]
    exact ⟨v₀, hv₀⟩

/-- Fold a list of `(address, blobBytes)` pairs into `m`. -/
def foldBlobsAux (m : Std.HashMap _root_.Address ByteArray)
    (blobs : List (_root_.Address × ByteArray)) : Std.HashMap _root_.Address ByteArray :=
  blobs.foldl (fun acc p => acc.insert p.1 p.2) m

/-- Build `E₀.blobs` from the `(address, blobBytes)` pairs hashed during conversion. -/
def foldBlobs (blobs : List (_root_.Address × ByteArray)) :
    Std.HashMap _root_.Address ByteArray :=
  foldBlobsAux {} blobs

private theorem foldBlobsAux_get?_inv {m : Std.HashMap _root_.Address ByteArray}
    {blobs : List (_root_.Address × ByteArray)} {q : _root_.Address} {w : ByteArray} :
    (foldBlobsAux m blobs).get? q = some w → (q, w) ∈ blobs ∨ m.get? q = some w := by
  induction blobs generalizing m with
  | nil =>
    intro h
    exact .inr h
  | cons p rest ih =>
    intro h
    rcases ih h with hmem | hins
    · exact .inl (List.mem_cons_of_mem _ hmem)
    · rcases hashmap_get?_insert_inv hins with ⟨hk, hw⟩ | hm
      · refine .inl ?_
        rcases p with ⟨pa, pbs⟩
        dsimp only at hk hw
        subst hk hw
        exact List.Mem.head _
      · exact .inr hm

private theorem foldBlobs_mem_of_get? {blobs : List (_root_.Address × ByteArray)}
    {q : _root_.Address} {w : ByteArray}
    (h : (foldBlobs blobs).get? q = some w) : (q, w) ∈ blobs := by
  rcases foldBlobsAux_get?_inv h with hmem | hemp
  · exact hmem
  · rw [hashmap_get?_empty] at hemp
    cases hemp

private theorem foldBlobsAux_exists_of_exists {m : Std.HashMap _root_.Address ByteArray}
    {blobs : List (_root_.Address × ByteArray)} {q : _root_.Address} :
    (∃ v₀, m.get? q = some v₀) → ∃ w, (foldBlobsAux m blobs).get? q = some w := by
  induction blobs generalizing m with
  | nil =>
    intro hex
    exact hex
  | cons p rest ih =>
    intro hex
    exact ih (hashmap_exists_get?_insert m p.1 q p.2 hex)

private theorem foldBlobsAux_exists_of_mem {m : Std.HashMap _root_.Address ByteArray}
    {blobs : List (_root_.Address × ByteArray)} {q : _root_.Address} {bs : ByteArray} :
    (q, bs) ∈ blobs → ∃ w, (foldBlobsAux m blobs).get? q = some w := by
  induction blobs generalizing m with
  | nil =>
    intro hmem
    cases hmem
  | cons p rest ih =>
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact foldBlobsAux_exists_of_exists (m := m.insert q bs) ⟨bs, hashmap_get?_insert_self m q bs⟩
    · exact ih htl

private theorem foldBlobs_exists_of_mem {blobs : List (_root_.Address × ByteArray)}
    {q : _root_.Address} {bs : ByteArray}
    (hmem : (q, bs) ∈ blobs) :
    ∃ w, (foldBlobs blobs).get? q = some w ∧ (q, w) ∈ blobs := by
  obtain ⟨w, hw⟩ := foldBlobsAux_exists_of_mem (m := {}) hmem
  exact ⟨w, hw, foldBlobs_mem_of_get? hw⟩

/-- An explicit hash collision witnessed directly inside `E₀` (between `E₀.blobs` and `E₀.consts`
at the same address `x`). Combined with `LoadedBy cs E₀`, this immediately yields
`View.HashedCollision V committed cs` for any `V` and `committed`. -/
def EnvInternalCollision (E₀ : Ixon.Env) : Prop :=
  ∃ (x : _root_.Address) (d : ByteArray) (lc : Ixon.LazyConstant),
    E₀.blobs.get? x = some d ∧ E₀.consts.get? x = some lc ∧ d ≠ lc.rawBytes

theorem EnvInternalCollision.hashedCollision {E₀ : Ixon.Env} {cs : List (Call F)}
    (hl : IxVM.Consistency.LoadedBy cs E₀) (hc : EnvInternalCollision E₀)
    (V : View) (committed : List ByteArray) :
    V.HashedCollision committed cs := by
  obtain ⟨x, d, lc, hblob, hconst, hne⟩ := hc
  obtain ⟨hh_c, ha_c⟩ := hl.1 x lc hconst
  obtain ⟨hh_b, ha_b⟩ := hl.2 x d hblob
  exact .inl ⟨x, lc.rawBytes, d, .inr (.inr ⟨hh_c, ha_c⟩), hh_b, hne, ha_b⟩

/-- Every literal blob hashed during expression conversion is stored literally in `E₀.blobs` at its
BLAKE3 address, unless `E₀` already witnesses an explicit hash collision (`EnvInternalCollision`). -/
def BlobTableLoaded (E₀ : Ixon.Env) (blobs : List (_root_.Address × ByteArray)) : Prop :=
  (∀ ba bs, (ba, bs) ∈ blobs → E₀.blobs.get? ba = some bs ∧ Address.blake3Pure bs = ba) ∨
  EnvInternalCollision E₀

/-- Under `LoadedBy cs E₀` and `¬ V.HashedCollision committed cs`, every `(ba, bs) ∈ blobs` is
stored literally in `E₀.blobs` (`E₀.blobs.get? ba = some bs`). -/
theorem BlobTableLoaded.get_of_no_collision {E₀ : Ixon.Env} {cs : List (Call F)}
    {blobs : List (_root_.Address × ByteArray)} {V : View} {committed : List ByteArray}
    (hl : IxVM.Consistency.LoadedBy cs E₀)
    (nc : ¬ V.HashedCollision committed cs)
    (hb : BlobTableLoaded E₀ blobs) :
    ∀ ba bs, (ba, bs) ∈ blobs → E₀.blobs.get? ba = some bs ∧ Address.blake3Pure bs = ba := by
  rcases hb with hok | hcoll
  · exact hok
  · exact absurd (hcoll.hashedCollision hl V committed) nc

theorem BlobTableLoaded.env_mono {E₀ E₁ : Ixon.Env}
    {blobs : List (_root_.Address × ByteArray)}
    (hconsts : ∀ a lc, E₀.consts.get? a = some lc →
      ∃ lc', E₁.consts.get? a = some lc' ∧ lc'.rawBytes = lc.rawBytes)
    (hblobs : ∀ a bs, E₀.blobs.get? a = some bs → E₁.blobs.get? a = some bs)
    (hb : BlobTableLoaded E₀ blobs) :
    BlobTableLoaded E₁ blobs := by
  rcases hb with hok | ⟨x, d, lc, hbl, hco, hne⟩
  · refine .inl (fun ba bs hm => ?_)
    obtain ⟨hg, ha⟩ := hok ba bs hm
    exact ⟨hblobs ba bs hg, ha⟩
  · obtain ⟨lc', hco', hraw⟩ := hconsts x lc hco
    refine .inr ⟨x, d, lc', hblobs x d hbl, hco', ?_⟩
    rw [hraw]
    exact hne

/-- Given any base constant map `M` whose entries are hashed by `cs` under their keys and any
`blobs` with `HashedPairs cs blobs`, construct an `E₀ : Ixon.Env` preserving every existing lookup
in `M` while satisfying both `LoadedBy cs E₀` and `BlobTableLoaded E₀ blobs`. -/
private theorem build_env_with_blobs {cs : List (Call F)}
    (M : Std.HashMap _root_.Address Ixon.LazyConstant)
    (hM : ∀ k lc, M.get? k = some lc → Hashed cs lc.rawBytes ∧ Address.blake3Pure lc.rawBytes = k)
    {blobs : List (_root_.Address × ByteArray)}
    (hhp : HashedPairs cs blobs) :
    ∃ E₀ : Ixon.Env,
      (∀ k lc, M.get? k = some lc → E₀.consts.get? k = some lc) ∧
      IxVM.Consistency.LoadedBy cs E₀ ∧
      BlobTableLoaded E₀ blobs := by
  by_cases hfun : ∀ ba bs₁ bs₂, (ba, bs₁) ∈ blobs → (ba, bs₂) ∈ blobs → bs₁ = bs₂
  · let E₀ : Ixon.Env := { consts := M, blobs := foldBlobs blobs }
    refine ⟨E₀, fun _ _ h => h, ⟨hM, ?_⟩, .inl ?_⟩
    · intro ba bs hget
      have hmem := foldBlobs_mem_of_get? hget
      exact hhp (ba, bs) hmem
    · intro ba bs hmem
      obtain ⟨w, hw, hw_mem⟩ := foldBlobs_exists_of_mem hmem
      have heq : w = bs := hfun ba w bs hw_mem hmem
      rw [heq] at hw
      exact ⟨hw, (hhp (ba, bs) hmem).2⟩
  · have hex : ∃ ba bs₁ bs₂, (ba, bs₁) ∈ blobs ∧ (ba, bs₂) ∈ blobs ∧ bs₁ ≠ bs₂ :=
      Classical.byContradiction fun hno =>
        hfun fun ba bs₁ bs₂ hm1 hm2 =>
          Classical.byContradiction fun hne => hno ⟨ba, bs₁, bs₂, hm1, hm2, hne⟩
    obtain ⟨x, bs₁, bs₂, hm1, hm2, hne12⟩ := hex
    obtain ⟨hh1, ha1⟩ := hhp (x, bs₁) hm1
    obtain ⟨hh2, ha2⟩ := hhp (x, bs₂) hm2
    cases hMx : M.get? x with
    | some lc₀ =>
      have hd_choice : ∃ d, (d = bs₁ ∨ d = bs₂) ∧ d ≠ lc₀.rawBytes := by
        by_cases heq1 : bs₁ = lc₀.rawBytes
        · refine ⟨bs₂, .inr rfl, fun heq2 => hne12 (heq1.trans heq2.symm)⟩
        · exact ⟨bs₁, .inl rfl, heq1⟩
      obtain ⟨d, hd_or, hd_ne⟩ := hd_choice
      let E₀ : Ixon.Env := { consts := M, blobs := ({} : Std.HashMap _ _).insert x d }
      refine ⟨E₀, fun _ _ h => h, ⟨hM, ?_⟩,
        .inr ⟨x, d, lc₀, hashmap_get?_insert_self _ x d, hMx, hd_ne⟩⟩
      intro k w hget
      rcases hashmap_get?_insert_inv hget with ⟨hk, hw⟩ | hemp
      · subst hk hw
        rcases hd_or with rfl | rfl
        · exact ⟨hh1, ha1⟩
        · exact ⟨hh2, ha2⟩
      · rw [hashmap_get?_empty] at hemp
        cases hemp
    | none =>
      let lcX := mkLazyConst bs₂ default
      let M' := M.insert x lcX
      let E₀ : Ixon.Env := { consts := M', blobs := ({} : Std.HashMap _ _).insert x bs₁ }
      refine ⟨E₀, ?_, ⟨?_, ?_⟩,
        .inr ⟨x, bs₁, lcX, hashmap_get?_insert_self _ x bs₁,
          hashmap_get?_insert_self _ x lcX, by simp [lcX, hne12]⟩⟩
      · intro k lc hk
        have hxk : x ≠ k := by
          intro hxeq
          subst hxeq
          rw [hMx] at hk
          cases hk
        exact (hashmap_get?_insert_ne M hxk lcX).trans hk
      · intro k lc hget
        rcases hashmap_get?_insert_inv hget with ⟨hk, hlc⟩ | hm
        · subst hk hlc
          simp only [lcX, mkLazyConst_rawBytes]
          exact ⟨hh2, ha2⟩
        · exact hM k lc hm
      · intro k w hget
        rcases hashmap_get?_insert_inv hget with ⟨hk, hw⟩ | hemp
        · subst hk hw
          exact ⟨hh1, ha1⟩
        · rw [hashmap_get?_empty] at hemp
          cases hemp

/-! ## Section 2: `RawCIRep`, `RawCIPtrRep`, `LoadedL1`, Monotonicity, and `records_L1` / `l1_L1` -/

/-- Raw converted `KConstantInfo` value `v` on heap `h` for decoded constant `c` at address `a`,
with literal blobs and (for projection records) the parent mutual block `cb` recorded in `E₀`. -/
def RawCIRep (E₀ : Ixon.Env) (h : Heap F) (a : _root_.Address) (c : Ixon.Constant)
    (v : SourceValue F) : Prop :=
  match c.info with
  | .defn d =>
    ∃ blobs, BlobTableLoaded E₀ blobs ∧
      RawDefnValRep c.refs.toList (defnRecurAddrs d a) c.univs.toList c.sharing.toList blobs h d v
  | .axio ax =>
    ∃ blobs, BlobTableLoaded E₀ blobs ∧
      RawAxioValRep c.refs.toList [] c.univs.toList c.sharing.toList blobs h ax v
  | .quot q =>
    ∃ blobs, BlobTableLoaded E₀ blobs ∧
      RawQuotValRep c.refs.toList [] c.univs.toList c.sharing.toList blobs h q v
  | .recr rc =>
    ∃ blobs, BlobTableLoaded E₀ blobs ∧
      RawRecrValRep c.refs.toList [a] c.univs.toList c.sharing.toList blobs h rc a 0 v
  | .dPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (lcB : Ixon.LazyConstant) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (d : Ixon.Definition) (blobs : List (_root_.Address × ByteArray)),
      E₀.consts.get? p.block = some lcB ∧
      lcB.get? = some cb ∧
      Ix.Cert.recordAt E₀ p.block = some cb ∧
      Ixon.deConstantExact lcB.rawBytes = .ok cb ∧
      Ixon.deConstant lcB.rawBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.defn d) ∧
      BlobTableLoaded E₀ blobs ∧
      RawDefnValRep cb.refs.toList (defnMemberRecurAddrs d p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h d v
  | .iPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (lcB : Ixon.LazyConstant) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive) (blobs : List (_root_.Address × ByteArray)),
      E₀.consts.get? p.block = some lcB ∧
      lcB.get? = some cb ∧
      Ix.Cert.recordAt E₀ p.block = some cb ∧
      Ixon.deConstantExact lcB.rawBytes = .ok cb ∧
      Ixon.deConstant lcB.rawBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.indc ind) ∧
      BlobTableLoaded E₀ blobs ∧
      RawInductValRep cb.refs.toList (blockRecurAddrs p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h ind p.block p.idx.toNat v
  | .cPrj p =>
    p.idx.toNat < 72057594037927936 ∧ p.cidx.toNat < 72057594037927936 ∧
    ∃ (lcB : Ixon.LazyConstant) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive) (ct : Ixon.Constructor) (blobs : List (_root_.Address × ByteArray)),
      E₀.consts.get? p.block = some lcB ∧
      lcB.get? = some cb ∧
      Ix.Cert.recordAt E₀ p.block = some cb ∧
      Ixon.deConstantExact lcB.rawBytes = .ok cb ∧
      Ixon.deConstant lcB.rawBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.indc ind) ∧
      ind.ctors.toList[p.cidx.toNat]? = some ct ∧
      BlobTableLoaded E₀ blobs ∧
      RawCtorValRep cb.refs.toList (blockRecurAddrs p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h ct p.block p.idx.toNat v
  | .rPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (lcB : Ixon.LazyConstant) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (rc : Ixon.Recursor) (blobs : List (_root_.Address × ByteArray)),
      E₀.consts.get? p.block = some lcB ∧
      lcB.get? = some cb ∧
      Ix.Cert.recordAt E₀ p.block = some cb ∧
      Ixon.deConstantExact lcB.rawBytes = .ok cb ∧
      Ixon.deConstant lcB.rawBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.recr rc) ∧
      BlobTableLoaded E₀ blobs ∧
      RawRecrValRep cb.refs.toList (blockRecurAddrs p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs h rc p.block p.idx.toNat v
  | .muts _ => False

/-- Heap-pointer wrapper around `RawCIRep`. -/
def RawCIPtrRep (E₀ : Ixon.Env) (h : Heap F) (ptr : SourceValue F)
    (a : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∃ v, loadValue h ptr = .ok v ∧ RawCIRep E₀ h a c v

/-- **`LoadedL1`**: exact unconditional postcondition of `Ingress::get_ci` for `Seams.loaded`. -/
def LoadedL1 (E₀ : Ixon.Env) (h : Heap F) (ptr : SourceValue F) (bytes : ByteArray) : Prop :=
  ∃ c : Ixon.Constant,
    Ixon.deConstantExact bytes = .ok c ∧
    Ixon.deConstant bytes = .ok c ∧
    ConstantTablesValid c ∧
    RawCIPtrRep E₀ h ptr (Address.blake3Pure bytes) c

theorem RawCIRep.mono {E₀ : Ixon.Env} {h₁ h₂ : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RawCIRep E₀ h₁ a c v) :
    RawCIRep E₀ h₂ a c v := by
  unfold RawCIRep at r ⊢
  cases hc : c.info with
  | defn _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb, hraw.mono ext (fun _ hm => hm)⟩
  | axio _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb, hraw.mono ext (fun _ hm => hm)⟩
  | quot _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb, hraw.mono ext (fun _ hm => hm)⟩
  | recr _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb, hraw.mono ext (fun _ hm => hm)⟩
  | dPrj _ =>
    rw [hc] at r
    obtain ⟨hidx, lcB, cb, ms, d, blobs, h1, h2, h3, h4, h5, h6, h7, hb, hraw⟩ := r
    exact ⟨hidx, lcB, cb, ms, d, blobs, h1, h2, h3, h4, h5, h6, h7, hb,
      hraw.mono ext (fun _ hm => hm)⟩
  | iPrj _ =>
    rw [hc] at r
    obtain ⟨hidx, lcB, cb, ms, ind, blobs, h1, h2, h3, h4, h5, h6, h7, hb, hraw⟩ := r
    exact ⟨hidx, lcB, cb, ms, ind, blobs, h1, h2, h3, h4, h5, h6, h7, hb,
      hraw.mono ext (fun _ hm => hm)⟩
  | cPrj _ =>
    rw [hc] at r
    obtain ⟨hidx, hcidx, lcB, cb, ms, ind, ct, blobs, h1, h2, h3, h4, h5, h6, h7, h8, hb, hraw⟩ := r
    exact ⟨hidx, hcidx, lcB, cb, ms, ind, ct, blobs, h1, h2, h3, h4, h5, h6, h7, h8, hb,
      hraw.mono ext (fun _ hm => hm)⟩
  | rPrj _ =>
    rw [hc] at r
    obtain ⟨hidx, lcB, cb, ms, rc, blobs, h1, h2, h3, h4, h5, h6, h7, hb, hraw⟩ := r
    exact ⟨hidx, lcB, cb, ms, rc, blobs, h1, h2, h3, h4, h5, h6, h7, hb,
      hraw.mono ext (fun _ hm => hm)⟩
  | muts _ =>
    rw [hc] at r
    exact r

theorem RawCIPtrRep.mono {E₀ : Ixon.Env} {h₁ h₂ : Heap F} {ptr : SourceValue F}
    {a : _root_.Address} {c : Ixon.Constant}
    (ext : Heap.Extends h₁ h₂) (r : RawCIPtrRep E₀ h₁ ptr a c) :
    RawCIPtrRep E₀ h₂ ptr a c := by
  obtain ⟨v, hld, hraw⟩ := r
  exact ⟨v, loadValue_extend ext hld, hraw.mono ext⟩

theorem LoadedL1.mono {E₀ : Ixon.Env} {h₁ h₂ : Heap F} {ptr : SourceValue F} {bytes : ByteArray}
    (ext : Heap.Extends h₁ h₂) (r : LoadedL1 E₀ h₁ ptr bytes) :
    LoadedL1 E₀ h₂ ptr bytes := by
  obtain ⟨c, hex, hde, htv, hptr⟩ := r
  exact ⟨c, hex, hde, htv, hptr.mono ext⟩

theorem RawCIRep.env_mono {E₀ E₁ : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v : SourceValue F}
    (hconsts : ∀ k lc, E₀.consts.get? k = some lc →
      ∃ lc', E₁.consts.get? k = some lc' ∧ lc'.get? = lc.get? ∧ lc'.rawBytes = lc.rawBytes)
    (hblobs : ∀ k bs, E₀.blobs.get? k = some bs → E₁.blobs.get? k = some bs)
    (r : RawCIRep E₀ h a c v) :
    RawCIRep E₁ h a c v := by
  have hc_raw : ∀ k lc, E₀.consts.get? k = some lc →
      ∃ lc', E₁.consts.get? k = some lc' ∧ lc'.rawBytes = lc.rawBytes := by
    intro k lc hk
    obtain ⟨lc', h1, _, h3⟩ := hconsts k lc hk
    exact ⟨lc', h1, h3⟩
  unfold RawCIRep at r ⊢
  cases hc : c.info with
  | defn _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb.env_mono hc_raw hblobs, hraw⟩
  | axio _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb.env_mono hc_raw hblobs, hraw⟩
  | quot _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb.env_mono hc_raw hblobs, hraw⟩
  | recr _ =>
    rw [hc] at r
    obtain ⟨blobs, hb, hraw⟩ := r
    exact ⟨blobs, hb.env_mono hc_raw hblobs, hraw⟩
  | dPrj p =>
    rw [hc] at r
    obtain ⟨hidx, lcB, cb, ms, d, blobs, hgetB, hlcB, _, hexB, hdeB, hcb, hms, hb, hraw⟩ := r
    obtain ⟨lcB', hgetB', hget_eq, hraw_eq⟩ := hconsts p.block lcB hgetB
    have hlcB' : lcB'.get? = some cb := hget_eq.trans hlcB
    have hrecB' : Ix.Cert.recordAt E₁ p.block = some cb := recordAt_of_get? hgetB' hlcB'
    rw [← hraw_eq] at hexB hdeB
    exact ⟨hidx, lcB', cb, ms, d, blobs, hgetB', hlcB', hrecB', hexB, hdeB, hcb, hms,
      hb.env_mono hc_raw hblobs, hraw⟩
  | iPrj p =>
    rw [hc] at r
    obtain ⟨hidx, lcB, cb, ms, ind, blobs, hgetB, hlcB, _, hexB, hdeB, hcb, hms, hb, hraw⟩ := r
    obtain ⟨lcB', hgetB', hget_eq, hraw_eq⟩ := hconsts p.block lcB hgetB
    have hlcB' : lcB'.get? = some cb := hget_eq.trans hlcB
    have hrecB' : Ix.Cert.recordAt E₁ p.block = some cb := recordAt_of_get? hgetB' hlcB'
    rw [← hraw_eq] at hexB hdeB
    exact ⟨hidx, lcB', cb, ms, ind, blobs, hgetB', hlcB', hrecB', hexB, hdeB, hcb, hms,
      hb.env_mono hc_raw hblobs, hraw⟩
  | cPrj p =>
    rw [hc] at r
    obtain ⟨hidx, hcidx, lcB, cb, ms, ind, ct, blobs,
      hgetB, hlcB, _, hexB, hdeB, hcb, hms, hct, hb, hraw⟩ := r
    obtain ⟨lcB', hgetB', hget_eq, hraw_eq⟩ := hconsts p.block lcB hgetB
    have hlcB' : lcB'.get? = some cb := hget_eq.trans hlcB
    have hrecB' : Ix.Cert.recordAt E₁ p.block = some cb := recordAt_of_get? hgetB' hlcB'
    rw [← hraw_eq] at hexB hdeB
    exact ⟨hidx, hcidx, lcB', cb, ms, ind, ct, blobs, hgetB', hlcB', hrecB', hexB, hdeB,
      hcb, hms, hct, hb.env_mono hc_raw hblobs, hraw⟩
  | rPrj p =>
    rw [hc] at r
    obtain ⟨hidx, lcB, cb, ms, rc, blobs, hgetB, hlcB, _, hexB, hdeB, hcb, hms, hb, hraw⟩ := r
    obtain ⟨lcB', hgetB', hget_eq, hraw_eq⟩ := hconsts p.block lcB hgetB
    have hlcB' : lcB'.get? = some cb := hget_eq.trans hlcB
    have hrecB' : Ix.Cert.recordAt E₁ p.block = some cb := recordAt_of_get? hgetB' hlcB'
    rw [← hraw_eq] at hexB hdeB
    exact ⟨hidx, lcB', cb, ms, rc, blobs, hgetB', hlcB', hrecB', hexB, hdeB, hcb, hms,
      hb.env_mono hc_raw hblobs, hraw⟩
  | muts _ =>
    rw [hc] at r
    exact r

theorem RawCIPtrRep.env_mono {E₀ E₁ : Ixon.Env} {h : Heap F} {ptr : SourceValue F}
    {a : _root_.Address} {c : Ixon.Constant}
    (hconsts : ∀ k lc, E₀.consts.get? k = some lc →
      ∃ lc', E₁.consts.get? k = some lc' ∧ lc'.get? = lc.get? ∧ lc'.rawBytes = lc.rawBytes)
    (hblobs : ∀ k bs, E₀.blobs.get? k = some bs → E₁.blobs.get? k = some bs)
    (r : RawCIPtrRep E₀ h ptr a c) :
    RawCIPtrRep E₁ h ptr a c := by
  obtain ⟨v, hld, hraw⟩ := r
  exact ⟨v, hld, hraw.env_mono hconsts hblobs⟩

theorem LoadedL1.env_mono {E₀ E₁ : Ixon.Env} {h : Heap F} {ptr : SourceValue F}
    {bytes : ByteArray}
    (hconsts : ∀ k lc, E₀.consts.get? k = some lc →
      ∃ lc', E₁.consts.get? k = some lc' ∧ lc'.get? = lc.get? ∧ lc'.rawBytes = lc.rawBytes)
    (hblobs : ∀ k bs, E₀.blobs.get? k = some bs → E₁.blobs.get? k = some bs)
    (r : LoadedL1 E₀ h ptr bytes) :
    LoadedL1 E₁ h ptr bytes := by
  obtain ⟨c, hex, hde, htv, hptr⟩ := r
  exact ⟨c, hex, hde, htv, hptr.env_mono hconsts hblobs⟩

private theorem singleton_consts_hashed {cs : List (Call F)} {a : _root_.Address}
    {bytes : ByteArray} (c : Ixon.Constant)
    (hh : Hashed cs bytes) (ha : Address.blake3Pure bytes = a) :
    ∀ k lc, (({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a (mkLazyConst bytes c)).get? k =
      some lc → Hashed cs lc.rawBytes ∧ Address.blake3Pure lc.rawBytes = k := by
  intro k lc hget
  rcases hashmap_get?_insert_inv hget with ⟨hk, hlc⟩ | hemp
  · subst hk hlc
    simp only [mkLazyConst_rawBytes]
    exact ⟨hh, ha⟩
  · rw [hashmap_get?_empty] at hemp
    cases hemp

private theorem pair_consts_hashed {cs : List (Call F)} {a b : _root_.Address}
    {bytes blkBytes : ByteArray} (c cb : Ixon.Constant)
    (hh : Hashed cs bytes) (ha : Address.blake3Pure bytes = a)
    (hhB : Hashed cs blkBytes) (haB : Address.blake3Pure blkBytes = b) :
    ∀ k lc,
      ((({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a (mkLazyConst bytes c)).insert b
        (mkLazyConst blkBytes cb)).get? k = some lc →
      Hashed cs lc.rawBytes ∧ Address.blake3Pure lc.rawBytes = k := by
  intro k lc hget
  rcases hashmap_get?_insert_inv hget with ⟨hk, hlc⟩ | hinner
  · subst hk hlc
    simp only [mkLazyConst_rawBytes]
    exact ⟨hhB, haB⟩
  · exact singleton_consts_hashed c hh ha k lc hinner

/-- Package `GetCIRawResult` into a collision-proof `E₀ : Ixon.Env` satisfying `LoadedBy cs E₀`
and `LoadedL1 E₀ after ptr bytes`. -/
theorem get_ci_loadedL1_spec {a : Bytes.Address} {x_addr ptr : SourceValue F}
    {heap after : Heap F} {cs : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded cs)
    (ha : Bytes.RepAddressRef Core.addrTy heap a x_addr)
    (ev : ObsFn W "Ingress::get_ci" [x_addr] heap ptr after cs) :
    Heap.Extends heap after ∧
      ∃ (bytes : ByteArray) (E₀ : Ixon.Env),
        Hashed cs bytes ∧
        Address.blake3Pure bytes = Core.ixAddr a ∧
        IxVM.Consistency.LoadedBy cs E₀ ∧
        LoadedL1 E₀ after ptr bytes := by
  obtain ⟨ext, bytes, c, blobs, hhash, haddr, hexact, hde, htv, hhp, hres⟩ :=
    get_ci_spec hbounded ha ev
  let a0 := Core.ixAddr a
  unfold GetCIRawResult at hres
  cases hc : c.info with
  | defn d =>
    rw [hc] at hres
    obtain ⟨v, hld, hraw⟩ := hres
    let M := ({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)
    obtain ⟨E₀, _, hloaded, hblobs⟩ :=
      build_env_with_blobs M (singleton_consts_hashed c hhash haddr) hhp
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨blobs, hblobs, hraw⟩
  | axio ax =>
    rw [hc] at hres
    obtain ⟨v, hld, hraw⟩ := hres
    let M := ({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)
    obtain ⟨E₀, _, hloaded, hblobs⟩ :=
      build_env_with_blobs M (singleton_consts_hashed c hhash haddr) hhp
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨blobs, hblobs, hraw⟩
  | quot q =>
    rw [hc] at hres
    obtain ⟨v, hld, hraw⟩ := hres
    let M := ({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)
    obtain ⟨E₀, _, hloaded, hblobs⟩ :=
      build_env_with_blobs M (singleton_consts_hashed c hhash haddr) hhp
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨blobs, hblobs, hraw⟩
  | recr rc =>
    rw [hc] at hres
    obtain ⟨v, hld, hraw⟩ := hres
    let M := ({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)
    obtain ⟨E₀, _, hloaded, hblobs⟩ :=
      build_env_with_blobs M (singleton_consts_hashed c hhash haddr) hhp
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨blobs, hblobs, hraw⟩
  | dPrj p =>
    rw [hc] at hres
    obtain ⟨hidx56, blkBytes, cb, ms, d, v,
      hhB, haB, hexB, hdeB, hcb, hms, hld, hraw⟩ := hres
    let lcB := mkLazyConst blkBytes cb
    let M := (({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)).insert
      p.block lcB
    obtain ⟨E₀, hkeep, hloaded, hblobs⟩ :=
      build_env_with_blobs M (pair_consts_hashed c cb hhash haddr hhB haB) hhp
    have hgetB : E₀.consts.get? p.block = some lcB :=
      hkeep p.block lcB (hashmap_get?_insert_self _ p.block lcB)
    have hrecB : Ix.Cert.recordAt E₀ p.block = some cb := recordAt_of_get? hgetB rfl
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨hidx56, lcB, cb, ms, d, blobs, hgetB, rfl, hrecB,
      by simpa [lcB] using hexB, by simpa [lcB] using hdeB, hcb, hms, hblobs, hraw⟩
  | iPrj p =>
    rw [hc] at hres
    obtain ⟨hidx56, blkBytes, cb, ms, ind, v,
      hhB, haB, hexB, hdeB, hcb, hms, hld, hraw⟩ := hres
    let lcB := mkLazyConst blkBytes cb
    let M := (({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)).insert
      p.block lcB
    obtain ⟨E₀, hkeep, hloaded, hblobs⟩ :=
      build_env_with_blobs M (pair_consts_hashed c cb hhash haddr hhB haB) hhp
    have hgetB : E₀.consts.get? p.block = some lcB :=
      hkeep p.block lcB (hashmap_get?_insert_self _ p.block lcB)
    have hrecB : Ix.Cert.recordAt E₀ p.block = some cb := recordAt_of_get? hgetB rfl
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨hidx56, lcB, cb, ms, ind, blobs, hgetB, rfl, hrecB,
      by simpa [lcB] using hexB, by simpa [lcB] using hdeB, hcb, hms, hblobs, hraw⟩
  | cPrj p =>
    rw [hc] at hres
    obtain ⟨hidx56, hcidx56, blkBytes, cb, ms, ind, ct, v,
      hhB, haB, hexB, hdeB, hcb, hms, hct, hld, hraw⟩ := hres
    let lcB := mkLazyConst blkBytes cb
    let M := (({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)).insert
      p.block lcB
    obtain ⟨E₀, hkeep, hloaded, hblobs⟩ :=
      build_env_with_blobs M (pair_consts_hashed c cb hhash haddr hhB haB) hhp
    have hgetB : E₀.consts.get? p.block = some lcB :=
      hkeep p.block lcB (hashmap_get?_insert_self _ p.block lcB)
    have hrecB : Ix.Cert.recordAt E₀ p.block = some cb := recordAt_of_get? hgetB rfl
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨hidx56, hcidx56, lcB, cb, ms, ind, ct, blobs, hgetB, rfl, hrecB,
      by simpa [lcB] using hexB, by simpa [lcB] using hdeB, hcb, hms, hct, hblobs, hraw⟩
  | rPrj p =>
    rw [hc] at hres
    obtain ⟨hidx56, blkBytes, cb, ms, rc, v,
      hhB, haB, hexB, hdeB, hcb, hms, hld, hraw⟩ := hres
    let lcB := mkLazyConst blkBytes cb
    let M := (({} : Std.HashMap _root_.Address Ixon.LazyConstant).insert a0 (mkLazyConst bytes c)).insert
      p.block lcB
    obtain ⟨E₀, hkeep, hloaded, hblobs⟩ :=
      build_env_with_blobs M (pair_consts_hashed c cb hhash haddr hhB haB) hhp
    have hgetB : E₀.consts.get? p.block = some lcB :=
      hkeep p.block lcB (hashmap_get?_insert_self _ p.block lcB)
    have hrecB : Ix.Cert.recordAt E₀ p.block = some cb := recordAt_of_get? hgetB rfl
    refine ⟨ext, bytes, E₀, hhash, haddr, hloaded, c, hexact, hde, htv, v, hld, ?_⟩
    rw [haddr]
    simp only [RawCIRep, hc]
    exact ⟨hidx56, lcB, cb, ms, rc, blobs, hgetB, rfl, hrecB,
      by simpa [lcB] using hexB, by simpa [lcB] using hdeB, hcb, hms, hblobs, hraw⟩
  | muts _ =>
    rw [hc] at hres
    exact False.elim hres

/-- **`Records` at `{ Core.S₀ with loaded := LoadedL1 }`**: every bounded `Ingress::get_ci`
derivation returns a `LoadedL1` pointer over hashed records and blobs `LoadedBy cs E₀`. -/
theorem records_L1 : IxVM.Consistency.Records { Core.S₀ with loaded := LoadedL1 } := by
  intro args heap after ptr cs ev hbounded v a hargs haddr
  subst hargs
  obtain ⟨a', ha', rfl⟩ := haddr
  obtain ⟨_, bytes, E₀, hhash, hblake, hloaded, hL1⟩ :=
    get_ci_loadedL1_spec hbounded ha' ev
  exact ⟨bytes, E₀, hhash, hblake, hloaded, hL1⟩

/-- **Obligation `L1` at `{ Core.S₀ with loaded := LoadedL1 }`**. -/
theorem l1_L1 : IxVM.Consistency.L1 { Core.S₀ with loaded := LoadedL1 } :=
  records_L1

/-! ## Section 3: Safety / `InLogic` / `OutsideLogicAt` & `KernelCheck::is_unsafe_ci` Companions -/

/-- Exact equivalence between `defnIsUnsafeCI` (`Ingress::defn_is_unsafe_ci`) and the kernel
reader's `safetyDecline` policy (`Ix.Kernel.Reader.safetyDecline`). -/
theorem defnIsUnsafeCI_eq_false_iff (d : Ixon.Definition) :
    defnIsUnsafeCI d = false ↔ Ix.Kernel.Reader.safetyDecline d = none := by
  rcases d with ⟨kind, safety, lvls, typ, val, _⟩
  cases kind <;> cases safety <;> constructor <;>
    (intro h; first | rfl | cases h)

theorem defnIsUnsafeCI_eq_true_iff (d : Ixon.Definition) :
    defnIsUnsafeCI d = true ↔ Ix.Kernel.Reader.safetyDecline d ≠ none := by
  cases hb : defnIsUnsafeCI d
  · simp only [Bool.false_eq_true, false_iff, Classical.not_not]
    exact (defnIsUnsafeCI_eq_false_iff d).mp hb
  · simp only [true_iff]
    intro hnone
    have hf := (defnIsUnsafeCI_eq_false_iff d).mpr hnone
    rw [hb] at hf
    cases hf

/-- Unconditional parent-block presence in `E₀` for any projection constant satisfying `RawCIRep`. -/
theorem RawCIRep.owner_recordAt {E₀ : Ixon.Env} {h : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v : SourceValue F}
    (hraw : RawCIRep E₀ h a c v)
    (hproj : Ix.Cert.ownerOf a c ≠ a) :
    ∃ (lcB : Ixon.LazyConstant) (cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      E₀.consts.get? (Ix.Cert.ownerOf a c) = some lcB ∧
      lcB.get? = some cb ∧
      Ix.Cert.recordAt E₀ (Ix.Cert.ownerOf a c) = some cb ∧
      Ixon.deConstantExact lcB.rawBytes = .ok cb ∧
      Ixon.deConstant lcB.rawBytes = .ok cb ∧
      cb.info = .muts ms := by
  unfold RawCIRep at hraw
  unfold Ix.Cert.ownerOf at hproj ⊢
  cases hc : c.info with
  | defn _ | axio _ | quot _ | recr _ | muts _ =>
    rw [hc] at hproj
    exact absurd rfl hproj
  | dPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, lcB, cb, ms, _, _, h1, h2, h3, h4, h5, h6, _⟩ := hraw
    exact ⟨lcB, cb, ms, h1, h2, h3, h4, h5, h6⟩
  | iPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, lcB, cb, ms, _, _, h1, h2, h3, h4, h5, h6, _⟩ := hraw
    exact ⟨lcB, cb, ms, h1, h2, h3, h4, h5, h6⟩
  | cPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, _, lcB, cb, ms, _, _, _, h1, h2, h3, h4, h5, h6, _⟩ := hraw
    exact ⟨lcB, cb, ms, h1, h2, h3, h4, h5, h6⟩
  | rPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, lcB, cb, ms, _, _, h1, h2, h3, h4, h5, h6, _⟩ := hraw
    exact ⟨lcB, cb, ms, h1, h2, h3, h4, h5, h6⟩

private theorem is_unsafe_ci_defnValShape_spec {d : Ixon.Definition}
    {tyPtr valPtr hint r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::is_unsafe_ci" [defnValShape d tyPtr valPtr hint] h r h' calls) :
    r = repBoolField (defnIsUnsafeCI d) ∧ h' = h ∧ calls = [] := by
  cases hk : d.kind with
  | defn =>
    simp only [defnValShape, hk] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Axiom _ _ _ hv => simp at hv
    | Defn_Safe _ _ _ _ _ hv he hr hh =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      have hs : d.safety = .safe := by
        cases hds : d.safety <;> simp [repDefSafetyVal, hds] at hs_eq
        rfl
      simp [defnIsUnsafeCI, hk, hs, repBoolField, he, hr, hh]
    | Defn_other _ _ _ _ _ _ hv hne he hr hh =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hs_eq, _⟩
      subst hs_eq
      have hns : d.safety ≠ .safe := by
        intro hs
        exact hne [] rfl (by simp [repDefSafetyVal, hs])
      cases hds : d.safety with
      | safe => exact absurd hds hns
      | unsaf => simp [defnIsUnsafeCI, hk, hds, repBoolField, he, hr, hh]
      | part => simp [defnIsUnsafeCI, hk, hds, repBoolField, he, hr, hh]
    | Thm _ _ _ _ _ hv => simp at hv
    | Opaque _ _ _ _ _ _ _ hv => simp at hv
    | Quot _ _ _ _ _ _ _ hv => simp at hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
  | opaq =>
    simp only [defnValShape, hk] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Axiom _ _ _ hv => simp at hv
    | Defn_Safe _ _ _ _ _ hv => simp at hv
    | Defn_other _ _ _ _ _ _ hv => simp at hv
    | Thm _ _ _ _ _ hv => simp at hv
    | Opaque _ _ _ _ _ _ _ hv he hr hh =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rcases hv with ⟨_, _, _, _, _, hu_eq⟩
      subst hu_eq
      refine ⟨?_, hr, hh⟩
      rw [he]
      unfold defnIsUnsafeCI
      rw [hk]
      cases d.safety <;> rfl
    | Quot _ _ _ _ _ _ _ hv => simp at hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
  | thm =>
    simp only [defnValShape, hk] at ev
    cases «KernelCheck::is_unsafe_ci».obs ev with
    | Axiom _ _ _ hv => simp at hv
    | Defn_Safe _ _ _ _ _ hv => simp at hv
    | Defn_other _ _ _ _ _ _ hv => simp at hv
    | Thm _ _ _ _ _ hv he hr hh =>
      simp [defnIsUnsafeCI, hk, repBoolField, he, hr, hh]
    | Opaque _ _ _ _ _ _ _ hv => simp at hv
    | Quot _ _ _ _ _ _ _ hv => simp at hv
    | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv

/-- Observed-derivation specification for `KernelCheck::is_unsafe_ci` on any `v` satisfying
`RawCIRep E₀ h a c v`: returns `.field 0` or `.field 1` without heap growth or external calls,
and if `r = .field 1` while `Ix.Cert.recordAt E₀ a = some c`, then `OutsideLogicAt E₀ a` holds;
if `r = .field 0` on a standalone record, `InLogic c` holds. -/
theorem is_unsafe_ci_raw_spec {E₀ : Ixon.Env} {h h' : Heap F} {a : _root_.Address}
    {c : Ixon.Constant} {v r : SourceValue F} {calls : List (Call F)}
    (hraw : RawCIRep E₀ h a c v)
    (ev : ObsFn W "KernelCheck::is_unsafe_ci" [v] h r h' calls) :
    h' = h ∧ calls = [] ∧ (r = .field 0 ∨ r = .field 1) ∧
      (r = .field 1 → Ix.Cert.recordAt E₀ a = some c → IxVM.Consistency.OutsideLogicAt E₀ a) ∧
      (r = .field 0 → Ix.Cert.ownerOf a c = a → IxVM.Consistency.InLogic c) := by
  have bool_dichot : ∀ b : Bool, repBoolField b = .field 0 ∨ repBoolField b = .field 1 := by
    intro b; cases b <;> simp [repBoolField]
  have bool_true_of_one : ∀ {b : Bool}, repBoolField b = .field 1 → b = true := by
    intro b hb
    cases b
    · exact absurd (natCast_inj3 (by decide) (by decide) (Value.field.inj hb)) (by decide)
    · rfl
  have bool_false_of_zero : ∀ {b : Bool}, repBoolField b = .field 0 → b = false := by
    intro b hb
    cases b
    · rfl
    · exact absurd (natCast_inj3 (by decide) (by decide) (Value.field.inj hb)) (by decide)
  unfold RawCIRep at hraw
  cases hc : c.info with
  | defn d =>
    rw [hc] at hraw
    obtain ⟨_, _, _, _, _, _, rfl, _, _⟩ := hraw
    obtain ⟨hr, hh, hcs⟩ := is_unsafe_ci_defnValShape_spec ev
    refine ⟨hh, hcs, by rw [hr]; exact bool_dichot _, ?_, ?_⟩
    · intro hr1 hrec
      have htrue := bool_true_of_one (hr.symm.trans hr1)
      have hdecl := (defnIsUnsafeCI_eq_true_iff d).mp htrue
      exact ⟨c, hrec, .inl (by simp [IxVM.Consistency.InLogic, hc, hdecl])⟩
    · intro hr0 _
      have hfalse := bool_false_of_zero (hr.symm.trans hr0)
      have hnone := (defnIsUnsafeCI_eq_false_iff d).mp hfalse
      simp [IxVM.Consistency.InLogic, hc, hnone]
  | axio ax =>
    rw [hc] at hraw
    obtain ⟨_, _, _, _, rfl, _⟩ := hraw
    have hstep : r = repBoolField ax.isUnsafe ∧ h' = h ∧ calls = [] := by
      cases «KernelCheck::is_unsafe_ci».obs ev with
      | Axiom _ _ _ hv he hr hh =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
        rcases hv with ⟨_, _, _, _, hu⟩
        subst hu; exact ⟨he, hr, hh⟩
      | Defn_Safe _ _ _ _ _ hv => simp at hv
      | Defn_other _ _ _ _ _ _ hv => simp at hv
      | Thm _ _ _ _ _ hv => simp at hv
      | Opaque _ _ _ _ _ _ _ hv => simp at hv
      | Quot _ _ _ _ _ _ _ hv => simp at hv
      | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    obtain ⟨hr, hh, hcs⟩ := hstep
    refine ⟨hh, hcs, by rw [hr]; exact bool_dichot _, ?_, ?_⟩
    · intro hr1 hrec
      have htrue := bool_true_of_one (hr.symm.trans hr1)
      exact ⟨c, hrec, .inl (by simp [IxVM.Consistency.InLogic, hc, htrue])⟩
    · intro hr0 _
      have hfalse := bool_false_of_zero (hr.symm.trans hr0)
      simp [IxVM.Consistency.InLogic, hc, hfalse]
  | quot _ =>
    rw [hc] at hraw
    obtain ⟨_, _, _, _, rfl, _⟩ := hraw
    have hstep : r = .field 0 ∧ h' = h ∧ calls = [] := by
      cases «KernelCheck::is_unsafe_ci».obs ev with
      | Axiom _ _ _ hv => simp at hv
      | Defn_Safe _ _ _ _ _ hv => simp at hv
      | Defn_other _ _ _ _ _ _ hv => simp at hv
      | Thm _ _ _ _ _ hv => simp at hv
      | Opaque _ _ _ _ _ _ _ hv => simp at hv
      | Quot _ _ _ _ _ _ _ _ he hr hh => exact ⟨he, hr, hh⟩
      | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    obtain ⟨hr, hh, hcs⟩ := hstep
    refine ⟨hh, hcs, .inl hr, ?_, ?_⟩
    · intro hr1 _
      have h01 : ((0 : Nat) : F) = ((1 : Nat) : F) := by simpa using Value.field.inj (hr.symm.trans hr1)
      exact absurd (natCast_inj3 (by decide) (by decide) h01) (by decide)
    · intro _ _
      simp [IxVM.Consistency.InLogic, hc]
  | recr rc =>
    rw [hc] at hraw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hraw
    have hstep : r = repBoolField rc.isUnsafe ∧ h' = h ∧ calls = [] := by
      cases «KernelCheck::is_unsafe_ci».obs ev with
      | Axiom _ _ _ hv => simp at hv
      | Defn_Safe _ _ _ _ _ hv => simp at hv
      | Defn_other _ _ _ _ _ _ hv => simp at hv
      | Thm _ _ _ _ _ hv => simp at hv
      | Opaque _ _ _ _ _ _ _ hv => simp at hv
      | Quot _ _ _ _ _ _ _ hv => simp at hv
      | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv he hr hh =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
        rcases hv with ⟨_, _, _, _, _, _, _, _, _, _, hu, _, _⟩
        subst hu; exact ⟨he, hr, hh⟩
    obtain ⟨hr, hh, hcs⟩ := hstep
    refine ⟨hh, hcs, by rw [hr]; exact bool_dichot _, ?_, ?_⟩
    · intro hr1 hrec
      have htrue := bool_true_of_one (hr.symm.trans hr1)
      exact ⟨c, hrec, .inl (by simp [IxVM.Consistency.InLogic, hc, htrue])⟩
    · intro hr0 _
      have hfalse := bool_false_of_zero (hr.symm.trans hr0)
      simp [IxVM.Consistency.InLogic, hc, hfalse]
  | dPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, _, cb, ms, d, _, _, _, hrecB, _, _, hcb, hms, _, _, _, _, _, rfl, _, _⟩ := hraw
    obtain ⟨hr, hh, hcs⟩ := is_unsafe_ci_defnValShape_spec ev
    refine ⟨hh, hcs, by rw [hr]; exact bool_dichot _, ?_, ?_⟩
    · intro hr1 hrec
      have htrue := bool_true_of_one (hr.symm.trans hr1)
      have hdecl := (defnIsUnsafeCI_eq_true_iff d).mp htrue
      have hmem : Ixon.MutConst.defn d ∈ ms.toList := List.mem_of_getElem? hms
      refine ⟨c, hrec, .inr ⟨cb, ?_, ?_⟩⟩
      · simpa [Ix.Cert.ownerOf, hc] using hrecB
      · intro hin
        simp only [IxVM.Consistency.InLogic, hcb] at hin
        exact hdecl (hin (.defn d) hmem)
    · intro _ _
      simp [IxVM.Consistency.InLogic, hc]
  | iPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, _, cb, ms, ind, _, _, _, hrecB, _, _, hcb, hms, _,
      _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hraw
    have hstep : r = repBoolField ind.isUnsafe ∧ h' = h ∧ calls = [] := by
      cases «KernelCheck::is_unsafe_ci».obs ev with
      | Axiom _ _ _ hv => simp at hv
      | Defn_Safe _ _ _ _ _ hv => simp at hv
      | Defn_other _ _ _ _ _ _ hv => simp at hv
      | Thm _ _ _ _ _ hv => simp at hv
      | Opaque _ _ _ _ _ _ _ hv => simp at hv
      | Quot _ _ _ _ _ _ _ hv => simp at hv
      | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv he hr hh =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
        rcases hv with ⟨_, _, _, _, _, _, _, hu, _, _⟩
        subst hu; exact ⟨he, hr, hh⟩
      | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    obtain ⟨hr, hh, hcs⟩ := hstep
    refine ⟨hh, hcs, by rw [hr]; exact bool_dichot _, ?_, ?_⟩
    · intro hr1 hrec
      have htrue := bool_true_of_one (hr.symm.trans hr1)
      have hmem : Ixon.MutConst.indc ind ∈ ms.toList := List.mem_of_getElem? hms
      refine ⟨c, hrec, .inr ⟨cb, ?_, ?_⟩⟩
      · simpa [Ix.Cert.ownerOf, hc] using hrecB
      · intro hin
        simp only [IxVM.Consistency.InLogic, hcb] at hin
        have hm := hin (.indc ind) hmem
        simp [IxVM.Consistency.InLogicMut, htrue] at hm
    · intro _ _
      simp [IxVM.Consistency.InLogic, hc]
  | cPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, _, _, cb, ms, ind, ct, _, _, _, hrecB, _, _, hcb, hms, hct, _,
      _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hraw
    have hstep : r = repBoolField ct.isUnsafe ∧ h' = h ∧ calls = [] := by
      cases «KernelCheck::is_unsafe_ci».obs ev with
      | Axiom _ _ _ hv => simp at hv
      | Defn_Safe _ _ _ _ _ hv => simp at hv
      | Defn_other _ _ _ _ _ _ hv => simp at hv
      | Thm _ _ _ _ _ hv => simp at hv
      | Opaque _ _ _ _ _ _ _ hv => simp at hv
      | Quot _ _ _ _ _ _ _ hv => simp at hv
      | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv he hr hh =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
        rcases hv with ⟨_, _, _, _, _, _, _, _, _, hu⟩
        subst hu; exact ⟨he, hr, hh⟩
      | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
    obtain ⟨hr, hh, hcs⟩ := hstep
    refine ⟨hh, hcs, by rw [hr]; exact bool_dichot _, ?_, ?_⟩
    · intro hr1 hrec
      have htrue := bool_true_of_one (hr.symm.trans hr1)
      have hmem : Ixon.MutConst.indc ind ∈ ms.toList := List.mem_of_getElem? hms
      have hct_mem : ct ∈ ind.ctors.toList := List.mem_of_getElem? hct
      refine ⟨c, hrec, .inr ⟨cb, ?_, ?_⟩⟩
      · simpa [Ix.Cert.ownerOf, hc] using hrecB
      · intro hin
        simp only [IxVM.Consistency.InLogic, hcb] at hin
        have hm := (hin (.indc ind) hmem).2 ct hct_mem
        rw [htrue] at hm
        cases hm
    · intro _ _
      simp [IxVM.Consistency.InLogic, hc]
  | rPrj _ =>
    rw [hc] at hraw
    obtain ⟨_, _, cb, ms, rc, _, _, _, hrecB, _, _, hcb, hms, _,
      _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hraw
    have hstep : r = repBoolField rc.isUnsafe ∧ h' = h ∧ calls = [] := by
      cases «KernelCheck::is_unsafe_ci».obs ev with
      | Axiom _ _ _ hv => simp at hv
      | Defn_Safe _ _ _ _ _ hv => simp at hv
      | Defn_other _ _ _ _ _ _ hv => simp at hv
      | Thm _ _ _ _ _ hv => simp at hv
      | Opaque _ _ _ _ _ _ _ hv => simp at hv
      | Quot _ _ _ _ _ _ _ hv => simp at hv
      | Induct _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv => simp at hv
      | Rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv he hr hh =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
        rcases hv with ⟨_, _, _, _, _, _, _, _, _, _, hu, _, _⟩
        subst hu; exact ⟨he, hr, hh⟩
    obtain ⟨hr, hh, hcs⟩ := hstep
    refine ⟨hh, hcs, by rw [hr]; exact bool_dichot _, ?_, ?_⟩
    · intro hr1 hrec
      have htrue := bool_true_of_one (hr.symm.trans hr1)
      have hmem : Ixon.MutConst.recr rc ∈ ms.toList := List.mem_of_getElem? hms
      refine ⟨c, hrec, .inr ⟨cb, ?_, ?_⟩⟩
      · simpa [Ix.Cert.ownerOf, hc] using hrecB
      · intro hin
        simp only [IxVM.Consistency.InLogic, hcb] at hin
        have hm := hin (.recr rc) hmem
        simp [IxVM.Consistency.InLogicMut, htrue] at hm
    · intro _ _
      simp [IxVM.Consistency.InLogic, hc]
  | muts _ =>
    rw [hc] at hraw
    exact False.elim hraw

/-! ## Section 4: Conditional `CIRep` / `CIPtrRep` Bridges (`∀ t : Ix.Kernel.RoleTable`) -/

/-- Well-formedness and kernel-reader hypotheses under role table `t` and environment `E₀`
under which decoded constant `c` at address `a` reads as kernel `ConstantInfo` `ci₀`. -/
def RecordReadsAs (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (a : _root_.Address)
    (c : Ixon.Constant) (ci₀ : Ix.Kernel.ConstantInfo .anon) : Prop :=
  ¬ EnvInternalCollision E₀ ∧
  match c.info with
  | .defn d =>
    ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
      (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
      (name : Core.KKey) (ps : List Ix.Kernel.LevelParam)
      (ty₀ val₀ : Core.KExpr) (hn : Ix.Kernel.ReducibilityHint),
      ps.length = d.lvls.toNat ∧
      ps.Perm (List.range ps.length) ∧
      (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
      (∀ i x m k, (defnRecurAddrs d a)[i]? = some x → self i = some m → m = .ok k →
        k = Core.keyOf t x) ∧
      (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
      (Ix.Kernel.Reader.MemberReader.mk' cx c (Ix.Kernel.Reader.recParam ps) self).read d.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined ps = true ∧
      (Ix.Kernel.Reader.MemberReader.mk' cx c (Ix.Kernel.Reader.recParam ps) self).read d.value =
        .ok val₀ ∧
      val₀.looseBVarsBounded 0 = true ∧
      val₀.allLevelParamsDefined ps = true ∧
      ci₀ = match d.kind with
        | .defn => .defnInfo ⟨name, ps, ty₀⟩ val₀ hn
        | .opaq => .axiomInfo ⟨name, ps, ty₀⟩
        | .thm => .thmInfo ⟨name, ps, ty₀⟩ val₀
  | .axio ax =>
    ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
      (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
      (name : Core.KKey) (ps : List Ix.Kernel.LevelParam) (ty₀ : Core.KExpr),
      ps.length = ax.lvls.toNat ∧
      ps.Perm (List.range ps.length) ∧
      (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
      (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
      (Ix.Kernel.Reader.MemberReader.mk' cx c (Ix.Kernel.Reader.recParam ps) self).read ax.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined ps = true ∧
      ci₀ = .axiomInfo ⟨name, ps, ty₀⟩
  | .quot q =>
    Core.QuotKindRep (repQuotKindVal q.kind) ci₀ ∧
    ci₀.toConstantVal.levelParams.length = q.lvls.toNat ∧
    ci₀.toConstantVal.levelParams.Perm (List.range ci₀.toConstantVal.levelParams.length) ∧
    (∀ mI rP rls, ci₀ = .recInfo ci₀.toConstantVal mI rP rls →
      List.Forall₂ IxVM.Consistency.RuleStored rls rls) ∧
    ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
      (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)),
      (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
      (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
      (Ix.Kernel.Reader.MemberReader.mk' cx c
        (Ix.Kernel.Reader.recParam ci₀.toConstantVal.levelParams) self).read q.typ =
          .ok ci₀.toConstantVal.type ∧
      ci₀.toConstantVal.type.looseBVarsBounded 0 = true ∧
      ci₀.toConstantVal.type.allLevelParamsDefined ci₀.toConstantVal.levelParams = true
  | .recr rc =>
    (rc.k = true → rc.rules.size = 1) ∧
    ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
      (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
      (name : Core.KKey) (ps : List Ix.Kernel.LevelParam) (ty₀ : Core.KExpr)
      (rules₀ : List (Ix.Kernel.RecRule .anon)),
      (name = Core.keyOf t a ∨ name = Core.keyOf t (Core.rprjAddr a 0)) ∧
      ps.length = rc.lvls.toNat ∧
      ps.Perm (List.range ps.length) ∧
      (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
      (∀ i x m k, ([a] : List _root_.Address)[i]? = some x → self i = some m → m = .ok k →
        k = Core.keyOf t x) ∧
      (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
      (Ix.Kernel.Reader.MemberReader.mk' cx c (Ix.Kernel.Reader.recParam ps) self).read rc.typ =
        .ok ty₀ ∧
      ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined ps = true ∧
      List.Forall₂ (fun ru rl₀ =>
        rl₀.nfields = ru.fields.toNat ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx c (Ix.Kernel.Reader.recParam ps) self).read ru.rhs =
          .ok rl₀.rhs ∧
        rl₀.rhs.looseBVarsBounded 0 = true ∧
        rl₀.rhs.allLevelParamsDefined ps = true) rc.rules.toList rules₀ ∧
      ci₀ = .recInfo ⟨name, ps, ty₀⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀
  | .dPrj p =>
    ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (d : Ixon.Definition),
      Ix.Cert.recordAt E₀ p.block = some cb → cb.info = .muts ms →
      ms.toList[p.idx.toNat]? = some (.defn d) →
      ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
        (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
        (name : Core.KKey) (ps : List Ix.Kernel.LevelParam)
        (ty₀ val₀ : Core.KExpr) (hn : Ix.Kernel.ReducibilityHint),
        ps.length = d.lvls.toNat ∧
        ps.Perm (List.range ps.length) ∧
        (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
        (∀ i x m k, (defnMemberRecurAddrs d p.block ms.toList)[i]? = some x →
          self i = some m → m = .ok k → k = Core.keyOf t x) ∧
        (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read d.typ =
          .ok ty₀ ∧
        ty₀.looseBVarsBounded 0 = true ∧
        ty₀.allLevelParamsDefined ps = true ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read d.value =
          .ok val₀ ∧
        val₀.looseBVarsBounded 0 = true ∧
        val₀.allLevelParamsDefined ps = true ∧
        ci₀ = match d.kind with
          | .defn => .defnInfo ⟨name, ps, ty₀⟩ val₀ hn
          | .opaq => .axiomInfo ⟨name, ps, ty₀⟩
          | .thm => .thmInfo ⟨name, ps, ty₀⟩ val₀
  | .iPrj p =>
    ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E₀ p.block = some cb → cb.info = .muts ms →
      ms.toList[p.idx.toNat]? = some (.indc ind) →
      ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
        (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
        (name : Core.KKey) (ps : List Ix.Kernel.LevelParam)
        (ty₀ : Core.KExpr) (caps : Ix.Kernel.IndCaps .anon),
        name = Core.keyOf t (Core.iprjAddr p.block p.idx.toNat) ∧
        ps.length = ind.lvls.toNat ∧
        ps.Perm (List.range ps.length) ∧
        (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
        (∀ i x m k, (blockRecurAddrs p.block ms.toList)[i]? = some x →
          self i = some m → m = .ok k → k = Core.keyOf t x) ∧
        (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read ind.typ =
          .ok ty₀ ∧
        ty₀.looseBVarsBounded 0 = true ∧
        ty₀.allLevelParamsDefined ps = true ∧
        ci₀ = .indInfo ⟨name, ps, ty₀⟩ caps
  | .cPrj p =>
    ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive)
      (ct : Ixon.Constructor),
      Ix.Cert.recordAt E₀ p.block = some cb → cb.info = .muts ms →
      ms.toList[p.idx.toNat]? = some (.indc ind) →
      ind.ctors.toList[p.cidx.toNat]? = some ct →
      ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
        (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
        (name : Core.KKey) (ps : List Ix.Kernel.LevelParam) (ty₀ : Core.KExpr),
        name = Core.keyOf t (Core.cprjAddr p.block p.idx.toNat ct.cidx.toNat) ∧
        ps.length = ct.lvls.toNat ∧
        ps.Perm (List.range ps.length) ∧
        (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
        (∀ i x m k, (blockRecurAddrs p.block ms.toList)[i]? = some x →
          self i = some m → m = .ok k → k = Core.keyOf t x) ∧
        (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read ct.typ =
          .ok ty₀ ∧
        ty₀.looseBVarsBounded 0 = true ∧
        ty₀.allLevelParamsDefined ps = true ∧
        ci₀ = .ctorInfo ⟨name, ps, ty₀⟩ ct.params.toNat ct.fields.toNat
  | .rPrj p =>
    ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (rc : Ixon.Recursor),
      Ix.Cert.recordAt E₀ p.block = some cb → cb.info = .muts ms →
      ms.toList[p.idx.toNat]? = some (.recr rc) →
      (rc.k = true → rc.rules.size = 1) ∧
      ∃ (cx : Ix.Kernel.Reader.Ctx .anon)
        (self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey))
        (name : Core.KKey) (ps : List Ix.Kernel.LevelParam) (ty₀ : Core.KExpr)
        (rules₀ : List (Ix.Kernel.RecRule .anon)),
        (name = Core.keyOf t p.block ∨ name = Core.keyOf t (Core.rprjAddr p.block p.idx.toNat)) ∧
        ps.length = rc.lvls.toNat ∧
        ps.Perm (List.range ps.length) ∧
        (∀ x k, cx.keyAt x = .ok k → k = Core.keyOf t x) ∧
        (∀ i x m k, (blockRecurAddrs p.block ms.toList)[i]? = some x →
          self i = some m → m = .ok k → k = Core.keyOf t x) ∧
        (∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) ∧
        (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read rc.typ =
          .ok ty₀ ∧
        ty₀.looseBVarsBounded 0 = true ∧
        ty₀.allLevelParamsDefined ps = true ∧
        List.Forall₂ (fun ru rl₀ =>
          rl₀.nfields = ru.fields.toNat ∧
          (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read ru.rhs =
            .ok rl₀.rhs ∧
          rl₀.rhs.looseBVarsBounded 0 = true ∧
          rl₀.rhs.allLevelParamsDefined ps = true) rc.rules.toList rules₀ ∧
        ci₀ = .recInfo ⟨name, ps, ty₀⟩
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
          (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules₀
  | .muts _ => False

private theorem blob_lookup_of_loaded {E₀ : Ixon.Env} {blobs : List (_root_.Address × ByteArray)}
    {cx : Ix.Kernel.Reader.Ctx .anon}
    (hb : BlobTableLoaded E₀ blobs)
    (hnc : ¬ EnvInternalCollision E₀)
    (hcx : ∀ x bs, E₀.blobs.get? x = some bs → cx.blob x = some bs) :
    ∀ x bs, (x, bs) ∈ blobs → cx.blob x = some bs := by
  rcases hb with hok | hcoll
  · intro x bs hm
    exact hcx x bs (hok x bs hm).1
  · exact absurd hcoll hnc

/-- Bridge from `RawCIRep` to `StoredAs` and `Core.CIRep` for **every** `t : Ix.Kernel.RoleTable`. -/
theorem RawCIRep.toCIRep (t : Ix.Kernel.RoleTable) {E₀ : Ixon.Env} {h : Heap F}
    {a : _root_.Address} {c : Ixon.Constant} {v : SourceValue F}
    {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hraw : RawCIRep E₀ h a c v)
    (hrd : RecordReadsAs t E₀ a c ci₀) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci ci₀ ∧ Core.CIRep (Core.keyOf t) h v ci := by
  obtain ⟨hnc, hrd_body⟩ := hrd
  unfold RawCIRep at hraw
  cases hc : c.info with
  | defn _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨blobs, hb, raw⟩ := hraw
    obtain ⟨_, _, name, _, _, _, hn,
      hnl, hperm, hkey, hself, hcx_blob, hty_rd, hty_lbb, hty_def,
      hval_rd, hval_lbb, hval_def, rfl⟩ := hrd_body
    exact raw.toCIRep (name := name) hnl hperm hkey hself
      (blob_lookup_of_loaded hb hnc hcx_blob) hn
      hty_rd hty_lbb hty_def hval_rd hval_lbb hval_def
  | axio _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨blobs, hb, raw⟩ := hraw
    obtain ⟨_, _, name, _, _,
      hnl, hperm, hkey, hcx_blob, hty_rd, hty_lbb, hty_def, rfl⟩ := hrd_body
    exact raw.toCIRep (name := name) hnl hperm hkey (fun _ _ _ _ hm => by simp at hm)
      (blob_lookup_of_loaded hb hnc hcx_blob) hty_rd hty_lbb hty_def
  | quot _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨blobs, hb, raw⟩ := hraw
    obtain ⟨hqk, hnl, hperm, hrls, _, _, hkey, hcx_blob, hty_rd, hty_lbb, hty_def⟩ := hrd_body
    exact raw.toCIRep_stored hqk hnl hperm hrls hkey (fun _ _ _ _ hm => by simp at hm)
      (blob_lookup_of_loaded hb hnc hcx_blob) hty_rd hty_lbb hty_def
  | recr _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨blobs, hb, raw⟩ := hraw
    obtain ⟨hk_sz, _, _, _, _, _, _,
      hname, hnl, hperm, hkey, hself, hcx_blob, hty_rd, hty_lbb, hty_def, hrls_rd, rfl⟩ := hrd_body
    exact raw.toCIRep hname hnl hperm hkey hself
      (blob_lookup_of_loaded hb hnc hcx_blob) hty_rd hty_lbb hty_def hrls_rd hk_sz
  | dPrj _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨_, _, cb, ms, d, blobs, _, _, hrecB, _, _, hcb, hms, hb, raw⟩ := hraw
    obtain ⟨_, _, name, _, _, _, hn,
      hnl, hperm, hkey, hself, hcx_blob, hty_rd, hty_lbb, hty_def,
      hval_rd, hval_lbb, hval_def, rfl⟩ := hrd_body cb ms d hrecB hcb hms
    exact raw.toCIRep (name := name) hnl hperm hkey hself
      (blob_lookup_of_loaded hb hnc hcx_blob) hn
      hty_rd hty_lbb hty_def hval_rd hval_lbb hval_def
  | iPrj _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨_, _, cb, ms, ind, blobs, _, _, hrecB, _, _, hcb, hms, hb, raw⟩ := hraw
    obtain ⟨_, _, _, _, _, caps,
      hname, hnl, hperm, hkey, hself, hcx_blob, hty_rd, hty_lbb, hty_def, rfl⟩ :=
        hrd_body cb ms ind hrecB hcb hms
    exact raw.toCIRep hname hnl hperm hkey hself
      (blob_lookup_of_loaded hb hnc hcx_blob) caps hty_rd hty_lbb hty_def
  | cPrj _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨_, _, _, cb, ms, ind, ct, blobs, _, _, hrecB, _, _, hcb, hms, hct, hb, raw⟩ := hraw
    obtain ⟨_, _, _, _, _,
      hname, hnl, hperm, hkey, hself, hcx_blob, hty_rd, hty_lbb, hty_def, rfl⟩ :=
        hrd_body cb ms ind ct hrecB hcb hms hct
    exact raw.toCIRep hname hnl hperm hkey hself
      (blob_lookup_of_loaded hb hnc hcx_blob) hty_rd hty_lbb hty_def
  | rPrj _ =>
    rw [hc] at hraw hrd_body
    obtain ⟨_, _, cb, ms, rc, blobs, _, _, hrecB, _, _, hcb, hms, hb, raw⟩ := hraw
    obtain ⟨hk_sz, _, _, _, _, _, _,
      hname, hnl, hperm, hkey, hself, hcx_blob, hty_rd, hty_lbb, hty_def, hrls_rd, rfl⟩ :=
        hrd_body cb ms rc hrecB hcb hms
    exact raw.toCIRep hname hnl hperm hkey hself
      (blob_lookup_of_loaded hb hnc hcx_blob) hty_rd hty_lbb hty_def hrls_rd hk_sz
  | muts _ =>
    rw [hc] at hraw
    exact False.elim hraw

/-- Bridge from `RawCIPtrRep` to `StoredAs` and `Core.CIPtrRep` for **every** `t : Ix.Kernel.RoleTable`. -/
theorem RawCIPtrRep.toCIPtrRep (t : Ix.Kernel.RoleTable) {E₀ : Ixon.Env} {h : Heap F}
    {ptr : SourceValue F} {a : _root_.Address} {c : Ixon.Constant}
    {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hraw : RawCIPtrRep E₀ h ptr a c)
    (hrd : RecordReadsAs t E₀ a c ci₀) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci ci₀ ∧ Core.CIPtrRep (Core.keyOf t) h ptr ci := by
  obtain ⟨v, hld, hci⟩ := hraw
  obtain ⟨ci, hst, hrep⟩ := hci.toCIRep t hrd
  exact ⟨ci, hst, v, hld, hrep⟩

/-- Bridge from `LoadedL1` to `StoredAs` and `Core.CIPtrRep` for **every** `t : Ix.Kernel.RoleTable`. -/
theorem LoadedL1.toCIPtrRep (t : Ix.Kernel.RoleTable) {E₀ : Ixon.Env} {h : Heap F}
    {ptr : SourceValue F} {bytes : ByteArray}
    {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (hl : LoadedL1 E₀ h ptr bytes)
    (hrd : ∀ c, Ixon.deConstant bytes = .ok c →
      RecordReadsAs t E₀ (Address.blake3Pure bytes) c ci₀) :
    ∃ c ci, Ixon.deConstant bytes = .ok c ∧
      IxVM.Consistency.StoredAs ci ci₀ ∧ Core.CIPtrRep (Core.keyOf t) h ptr ci := by
  obtain ⟨c, _, hde, _, hptr⟩ := hl
  obtain ⟨ci, hst, hrep⟩ := hptr.toCIPtrRep t (hrd c hde)
  exact ⟨c, ci, hde, hst, hrep⟩

/-- Direct `Core.CIPtrRep` bridge for `Ingress::get_ci_iprj` (`LoadFacts.getIprj`). -/
theorem get_ci_iprj_toCIPtrRep {c : Core.Ctx} {bp ptr : SourceValue F} {i : F}
    {h h' : Heap F} {cs : List (Call F)} {b : Bytes.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {ps : List Ix.Kernel.LevelParam} {ty₀ : Core.KExpr} {caps : Ix.Kernel.IndCaps .anon}
    (hdecB : ∀ lc, c.E.consts.get? (Core.ixAddr b) = some lc →
      Ixon.deConstantExact lc.rawBytes = .ok cb)
    (ev : ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs)
    (hg : Core.Good c cs)
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (hrecB : Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb)
    (hcb : cb.info = .muts ms)
    (hms : ms.toList[ZMod.val i]? = some (.indc ind))
    (hnl : ps.length = ind.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    (hkey : ∀ x k, cx.keyAt x = .ok k → k = c.κ x)
    (hself : ∀ idx x m k, (blockRecurAddrs (Core.ixAddr b) ms.toList)[idx]? = some x →
      self idx = some m → m = .ok k → k = c.κ x)
    (hblob : ∀ x bs, Hashed cs bs → Address.blake3Pure bs = x → cx.blob x = some bs)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read
      ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci
        (.indInfo ⟨c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)), ps, ty₀⟩ caps) ∧
      Core.CIPtrRep c.κ h' ptr ci := by
  obtain ⟨_, _, blkBytes, cb', ms', ind', blobs, v,
    hhB, haB, hexB, _, hcb', hms', hhp, hld, raw⟩ := get_ci_iprj_spec hg.2 hb ev
  unfold Ix.Cert.recordAt at hrecB
  cases hgetB : c.E.consts.get? (Core.ixAddr b) with
  | none => rw [hgetB] at hrecB; cases hrecB
  | some lcB =>
    have hesc := Core.load_escape hgetB hg.1 blkBytes hhB haB
    rw [hesc, hdecB lcB hgetB] at hexB
    injection hexB with hcb_eq; subst hcb_eq
    rw [hcb] at hcb'; injection hcb' with hms_eq; subst hms_eq
    rw [hms] at hms'; injection hms' with hind_eq1; injection hind_eq1 with hind_eq; subst hind_eq
    obtain ⟨ci, hst, hrep⟩ :=
      raw.toCIRep rfl hnl hperm hkey hself
        (fun x bs hm => hblob x bs (hhp (x, bs) hm).1 (hhp (x, bs) hm).2)
        caps hty_rd hty_lbb hty_def
    exact ⟨ci, hst, v, hld, hrep⟩

/-- Direct `Core.CIPtrRep` bridge for `Ingress::get_ci_cprj` (`LoadFacts.getCprj`). -/
theorem get_ci_cprj_toCIPtrRep {c : Core.Ctx} {bp ptr : SourceValue F} {i j : F}
    {h h' : Heap F} {cs : List (Call F)} {b : Bytes.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    {cx : Ix.Kernel.Reader.Ctx .anon}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {ps : List Ix.Kernel.LevelParam} {ty₀ : Core.KExpr}
    (hdecB : ∀ lc, c.E.consts.get? (Core.ixAddr b) = some lc →
      Ixon.deConstantExact lc.rawBytes = .ok cb)
    (ev : ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs)
    (hg : Core.Good c cs)
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (hrecB : Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb)
    (hcb : cb.info = .muts ms)
    (hms : ms.toList[ZMod.val i]? = some (.indc ind))
    (hct : ind.ctors.toList[ZMod.val j]? = some ct)
    (hcidx_eq : ct.cidx.toNat = ZMod.val j)
    (hnl : ps.length = ct.lvls.toNat) (hperm : ps.Perm (List.range ps.length))
    (hkey : ∀ x k, cx.keyAt x = .ok k → k = c.κ x)
    (hself : ∀ idx x m k, (blockRecurAddrs (Core.ixAddr b) ms.toList)[idx]? = some x →
      self idx = some m → m = .ok k → k = c.κ x)
    (hblob : ∀ x bs, Hashed cs bs → Address.blake3Pure bs = x → cx.blob x = some bs)
    (hty_rd : (Ix.Kernel.Reader.MemberReader.mk' cx cb (Ix.Kernel.Reader.recParam ps) self).read
      ct.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined ps = true) :
    ∃ ci : Ix.Kernel.ConstantInfo .anon,
      IxVM.Consistency.StoredAs ci
        (.ctorInfo ⟨c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j)), ps, ty₀⟩
          ct.params.toNat ct.fields.toNat) ∧
      Core.CIPtrRep c.κ h' ptr ci := by
  obtain ⟨_, _, _, blkBytes, cb', ms', ind', ct', blobs, v,
    hhB, haB, hexB, _, hcb', hms', hct', hhp, hld, raw⟩ := get_ci_cprj_spec hg.2 hb ev
  unfold Ix.Cert.recordAt at hrecB
  cases hgetB : c.E.consts.get? (Core.ixAddr b) with
  | none => rw [hgetB] at hrecB; cases hrecB
  | some lcB =>
    have hesc := Core.load_escape hgetB hg.1 blkBytes hhB haB
    rw [hesc, hdecB lcB hgetB] at hexB
    injection hexB with hcb_eq; subst hcb_eq
    rw [hcb] at hcb'; injection hcb' with hms_eq; subst hms_eq
    rw [hms] at hms'; injection hms' with hind_eq1; injection hind_eq1 with hind_eq; subst hind_eq
    rw [hct] at hct'; injection hct' with hct_eq; subst hct_eq
    have hname : c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j)) =
        c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) ct.cidx.toNat) := by
      rw [hcidx_eq]
    obtain ⟨ci, hst, hrep⟩ :=
      raw.toCIRep hname hnl hperm hkey hself
        (fun x bs hm => hblob x bs (hhp (x, bs) hm).1 (hhp (x, bs) hm).2)
        hty_rd hty_lbb hty_def
    exact ⟨ci, hst, v, hld, hrep⟩

/-! ## Section 5: `LoadFacts` Companions (`indRecord`, `inductRecord`, `canonical`) -/

/-- Decode bridge for `Ix.Cert.Stream.StoredCanonical`: any stored entry at `x ∈ order` with
`lc.get? = some cst` satisfies `Ixon.deConstantExact lc.rawBytes = .ok cst`. -/
theorem deConstantExact_of_storedCanonical {E : Ixon.Env} {order : List _root_.Address}
    {x : _root_.Address} {lc : Ixon.LazyConstant} {cst : Ixon.Constant}
    (hcan : Ix.Cert.Stream.StoredCanonical E order) (hx : x ∈ order)
    (hlc : E.consts.get? x = some lc) (hget : lc.get? = some cst) :
    Ixon.deConstantExact lc.rawBytes = .ok cst := by
  obtain ⟨c', hc'_get, hwf, hser, _⟩ := hcan x hx lc hlc
  rw [hget] at hc'_get
  injection hc'_get with hc_eq
  subst hc_eq
  rw [← hser]
  exact Ixon.Verify.deConstantExact_serConstant cst hwf

/-- Decode bridge for uncached standalone `LazyConstant` entries (`lc.cache = none`, `lc.off = 0`,
`lc.len = lc.buf.size`). -/
theorem deConstantExact_of_uncached {lc : Ixon.LazyConstant} {cst : Ixon.Constant}
    (hnone : lc.cache = none) (hoff : lc.off = 0) (hlen : lc.len = lc.buf.size)
    (hget : lc.get? = some cst) :
    Ixon.deConstantExact lc.rawBytes = .ok cst := by
  simp only [Ixon.LazyConstant.get?, hnone] at hget
  have hraw : lc.rawBytes = lc.buf := by
    simp [Ixon.LazyConstant.rawBytes, hoff, hlen]
  rw [hraw]
  rw [hoff, hlen] at hget
  unfold Ixon.deConstantAt at hget
  simp only [Nat.zero_add, Nat.le_refl, ↓reduceIte] at hget
  cases hrun : (Ixon.Bounded.getConstant Ixon.loadMaxUnivNodes).run { idx := 0, bytes := lc.buf } with
  | error _ _ => simp [hrun, Except.toOption] at hget
  | ok val st =>
    simp only [hrun] at hget
    split at hget
    · rename_i hidx
      simp only [Except.toOption, Option.some.injEq] at hget
      subst hget
      have hprod := getConstant_of_bounded hrun
      unfold Ixon.deConstantExact Ixon.runGetExact EStateM.run
      rw [hprod]
      simp [hidx]
    · simp [Except.toOption] at hget

/-- Core `LoadFacts.indRecord` proof parameterized by per-entry `deConstantExact` agreement at
`ixAddr a` and `p.block`. -/
theorem indRecord_of_deConstantExact {c : Core.Ctx}
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a : Bytes.Address} {cm cb : Ixon.Constant} {p : Ixon.InductiveProj}
    {xs : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hdecA : ∀ lc, c.E.consts.get? (Core.ixAddr a) = some lc →
      Ixon.deConstantExact lc.rawBytes = .ok cm)
    (hdecB : ∀ lc, c.E.consts.get? p.block = some lc →
      Ixon.deConstantExact lc.rawBytes = .ok cb)
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (hg : Core.Good c cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hcm : Ix.Cert.recordAt c.E (Core.ixAddr a) = some cm)
    (hcm_info : cm.info = .iPrj p)
    (hcb : Ix.Cert.recordAt c.E p.block = some cb)
    (hcb_info : cb.info = .muts xs)
    (hxs : xs[p.idx.toNat]? = some (.indc ind)) :
    ∃ (nl ty u blk : SourceValue F) (b : Bytes.Address),
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [nl, ty, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
         .field (ind.ctors.size : F), u, blk, .field (p.idx.toNat : F)]) ∧
      Bytes.RepAddressRef Core.addrTy h' b blk ∧
      Core.ixAddr b = p.block ∧
      p.idx.toNat < 2 ^ 56 ∧
      ind.ctors.size < 2 ^ 56 := by
  obtain ⟨_, rawBytes, _, _, hhA, haA, hexA, _, _, _, hres⟩ :=
    get_ci_spec hg.2 ha ev
  unfold Ix.Cert.recordAt at hcm
  cases hgetA : c.E.consts.get? (Core.ixAddr a) with
  | none => rw [hgetA] at hcm; cases hcm
  | some lcA =>
    have hescA := Core.load_escape hgetA hg.1 rawBytes hhA haA
    rw [hescA, hdecA lcA hgetA] at hexA
    injection hexA with hcm_eq; subst hcm_eq
    simp only [GetCIRawResult, hcm_info] at hres
    obtain ⟨hidx56, blkBytes, _, _, _, _,
      hhB, haB, hexB, _, hcb', hms', hld, raw⟩ := hres
    unfold Ix.Cert.recordAt at hcb
    cases hgetB : c.E.consts.get? p.block with
    | none => rw [hgetB] at hcb; cases hcb
    | some lcB =>
      have hescB := Core.load_escape hgetB hg.1 blkBytes hhB haB
      rw [hescB, hdecB lcB hgetB] at hexB
      injection hexB with hcb_eq; subst hcb_eq
      rw [hcb_info] at hcb'; injection hcb' with hms_eq; subst hms_eq
      simp only [Array.getElem?_toList] at hms'
      rw [hxs] at hms'; injection hms' with hind_eq1; injection hind_eq1 with hind_eq; subst hind_eq
      obtain ⟨_, _, _, hct56, _, tyPtr, blkPtr, b, hb_eq, hb_rep, rfl, _⟩ := raw
      have hpow56 : (72057594037927936 : Nat) = 2 ^ 56 := by decide
      rw [hpow56] at hidx56 hct56
      exact ⟨.field (ind.lvls.toNat : F), tyPtr, repBoolField ind.isUnsafe, blkPtr, b,
        hld, hb_rep, hb_eq, hidx56, hct56⟩

/-- `LoadFacts.indRecord` companion (`Core/Good.lean:117-129`) under `EnvDecoded c.E`. -/
theorem indRecord_of_get_ci {c : Core.Ctx}
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a : Bytes.Address} {cm cb : Ixon.Constant} {p : Ixon.InductiveProj}
    {xs : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hdec : EnvDecoded c.E)
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (hg : Core.Good c cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hcm : Ix.Cert.recordAt c.E (Core.ixAddr a) = some cm)
    (hcm_info : cm.info = .iPrj p)
    (hcb : Ix.Cert.recordAt c.E p.block = some cb)
    (hcb_info : cb.info = .muts xs)
    (hxs : xs[p.idx.toNat]? = some (.indc ind)) :
    ∃ (nl ty u blk : SourceValue F) (b : Bytes.Address),
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [nl, ty, .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
         .field (ind.ctors.size : F), u, blk, .field (p.idx.toNat : F)]) ∧
      Bytes.RepAddressRef Core.addrTy h' b blk ∧
      Core.ixAddr b = p.block ∧
      p.idx.toNat < 2 ^ 56 ∧
      ind.ctors.size < 2 ^ 56 := by
  obtain ⟨lcA, hlcA, _, hexA, _⟩ := hdec.recordAt_deConstantExact hcm
  obtain ⟨lcB, hlcB, _, hexB, _⟩ := hdec.recordAt_deConstantExact hcb
  refine indRecord_of_deConstantExact ?_ ?_ ev hg ha hcm hcm_info hcb hcb_info hxs
  · intro lc hget; rw [hlcA] at hget; injection hget with e; subst e; exact hexA
  · intro lc hget; rw [hlcB] at hget; injection hget with e; subst e; exact hexB

private theorem val_cast_u56_rec {n : Nat} (hn : n < 72057594037927936) :
    ((n : F).val : Nat) = n := by
  have hmod : n < U32.Goldilocks.modulus := by
    have : U32.Goldilocks.modulus = 18446744069414584321 := by decide
    omega
  exact ZMod.val_cast_of_lt hmod

private theorem defnValShape_ne_induct (d : Ixon.Definition)
    (tyPtr valPtr hint nl ty np ni nc u blk idx : SourceValue F) :
    defnValShape d tyPtr valPtr hint ≠
      .construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx] := by
  cases hk : d.kind <;> simp [defnValShape, hk]

/-- Unconditional trace-level converse of `indRecord` (`Bounded cs` only): whenever `Ingress::get_ci`
at `a` returns a pointer loading `.construct kciEnum "Induct" [...]`, the loaded record `cm` at `a`
is `.iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩` AND the derivation hashed and decoded its parent
block `cb` at `Core.ixAddr b` with `cb.info = .muts xs` and `xs[(ZMod.val i).toUInt64.toNat]? =
some (.indc ind)`. -/
theorem inductRecord_raw_of_get_ci {addr ptr : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {a : Bytes.Address}
    {nl ty np ni nc u blk idx : SourceValue F}
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (hbounded : IxVM.Consistency.Bounded cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld_ind : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx])) :
    ∃ (rawBytes blkBytes : ByteArray) (cm cb : Ixon.Constant)
      (xs : Array Ixon.MutConst) (ind : Ixon.Inductive)
      (b : Bytes.Address) (i : F),
      Hashed cs rawBytes ∧
      Address.blake3Pure rawBytes = Core.ixAddr a ∧
      Ixon.deConstantExact rawBytes = .ok cm ∧
      Ixon.deConstant rawBytes = .ok cm ∧
      Hashed cs blkBytes ∧
      Address.blake3Pure blkBytes = Core.ixAddr b ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      Ixon.deConstant blkBytes = .ok cb ∧
      Bytes.RepAddressRef Core.addrTy h' b blk ∧
      idx = .field i ∧
      ZMod.val i < 2 ^ 56 ∧
      cm.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ ∧
      cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind) := by
  obtain ⟨_, rawBytes, cm, _, hhA, haA, hexA, hdeA, _, _, hres⟩ :=
    get_ci_spec hbounded ha ev
  unfold GetCIRawResult at hres
  cases hinfo : cm.info with
  | defn d =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (ok_inj (hld.symm.trans hld_ind)) (defnValShape_ne_induct d _ _ _ _ _ _ _ _ _ _ _)
  | axio _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, rfl, _⟩ := hres
    have heq := ok_inj (hld.symm.trans hld_ind)
    simp at heq
  | quot _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, rfl, _⟩ := hres
    have heq := ok_inj (hld.symm.trans hld_ind)
    simp at heq
  | recr _ =>
    rw [hinfo] at hres
    obtain ⟨_, hld, _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := ok_inj (hld.symm.trans hld_ind)
    simp at heq
  | dPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, d, _, _, _, _, _, _, _, hld, _, _, _, _, rfl, _, _⟩ := hres
    exact absurd (ok_inj (hld.symm.trans hld_ind)) (defnValShape_ne_induct d _ _ _ _ _ _ _ _ _ _ _)
  | cPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hld,
      _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := hres
    have heq := ok_inj (hld.symm.trans hld_ind)
    simp at heq
  | rPrj _ =>
    rw [hinfo] at hres
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hld,
      _, _, _, _, _, _, _, _, _, _, _, _, rfl, _, _⟩ := hres
    have heq := ok_inj (hld.symm.trans hld_ind)
    simp at heq
  | muts _ =>
    rw [hinfo] at hres
    exact False.elim hres
  | iPrj p =>
    rw [hinfo] at hres
    obtain ⟨hidx56, blkBytes, cb, xs, ind, _,
      hhB, haB, hexB, hdeB, hcb, hxs, hld,
      _, _, _, _, _, _, _, b, hb_eq, hb_rep, rfl, _⟩ := hres
    have hv_eq := ok_inj (hld.symm.trans hld_ind)
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv_eq
    rcases hv_eq with ⟨_, _, _, _, _, _, _, _, hblk_eq, hidx_eq⟩
    subst hblk_eq
    let i : F := (p.idx.toNat : F)
    have hval_i : ZMod.val i = p.idx.toNat := val_cast_u56_rec hidx56
    have hu64_i : (ZMod.val i).toUInt64 = p.idx := by
      rw [hval_i]
      exact UInt64.toNat_inj.mp (UInt64.toNat_ofNat_of_lt p.idx.toNat_lt)
    have hp_eq : p = ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ := by
      rcases p with ⟨p_idx, p_blk⟩
      dsimp only at hu64_i hb_eq
      rw [hu64_i, hb_eq]
    have hpow56 : (72057594037927936 : Nat) = 2 ^ 56 := by decide
    refine ⟨rawBytes, blkBytes, cm, cb, xs, ind, b, i,
      hhA, haA, hexA, hdeA, hhB, ?_, hexB, hdeB, hb_rep, hidx_eq.symm,
      by rw [hval_i, ← hpow56]; exact hidx56, ?_, hcb, ?_⟩
    · rw [hb_eq]; exact haB
    · rw [← hp_eq]; exact hinfo
    · rw [hval_i]
      simpa only [Array.getElem?_toList] using hxs

/-- Strengthened `LoadFacts.inductRecord` companion (`Core/Good.lean:134-140` + coordinator ruling):
under `Good c cs`, `EnvDecoded c.E`, and presence of `ixAddr a` and parent block `ixAddr b` in
`c.E.consts`, witnesses BOTH `cm` at `ixAddr a` AND the loaded parent block `cb` at `ixAddr b`
with `cb.info = .muts xs` and `xs[ZMod.val i]? = some (.indc ind)`. -/
theorem inductRecord_of_get_ci_strong {c : Core.Ctx}
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a : Bytes.Address} {nl ty np ni nc u blk idx : SourceValue F}
    (hdec : EnvDecoded c.E)
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (hg : Core.Good c cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld_ind : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]))
    (hmemA : ∀ rawBytes, Hashed cs rawBytes → Address.blake3Pure rawBytes = Core.ixAddr a →
      ∃ lcA, c.E.consts.get? (Core.ixAddr a) = some lcA)
    (hmemB : ∀ (b : Bytes.Address) blkBytes, Hashed cs blkBytes →
      Address.blake3Pure blkBytes = Core.ixAddr b →
      ∃ lcB, c.E.consts.get? (Core.ixAddr b) = some lcB) :
    ∃ (cm cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive)
      (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (Core.ixAddr a) = some cm ∧
      Bytes.RepAddressRef Core.addrTy h' b blk ∧
      idx = .field i ∧
      cm.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ ∧
      Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb ∧
      cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind) := by
  obtain ⟨rawBytes, blkBytes, cm, cb, xs, ind, b, i,
    hhA, haA, hexA, _, hhB, haB, hexB, _, hb_rep, hidx_eq, _, hcm_info, hcb_info, hxs⟩ :=
    inductRecord_raw_of_get_ci ev hg.2 ha hld_ind
  obtain ⟨lcA, hlcA⟩ := hmemA rawBytes hhA haA
  obtain ⟨_, hgetA, hexA₀⟩ := hdec (Core.ixAddr a) lcA hlcA
  have hescA := Core.load_escape hlcA hg.1 rawBytes hhA haA
  rw [hescA, hexA₀] at hexA
  injection hexA with hcm_eq
  rw [hcm_eq] at hgetA
  obtain ⟨lcB, hlcB⟩ := hmemB b blkBytes hhB haB
  obtain ⟨_, hgetB, hexB₀⟩ := hdec (Core.ixAddr b) lcB hlcB
  have hescB := Core.load_escape hlcB hg.1 blkBytes hhB haB
  rw [hescB, hexB₀] at hexB
  injection hexB with hcb_eq
  rw [hcb_eq] at hgetB
  exact ⟨cm, cb, xs, ind, b, i,
    recordAt_of_get? hlcA hgetA, hb_rep, hidx_eq, hcm_info, recordAt_of_get? hlcB hgetB,
    hcb_info, hxs⟩

/-- `LoadFacts.inductRecord` companion (`Core/Good.lean:134-140`). -/
theorem inductRecord_of_get_ci {c : Core.Ctx}
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a : Bytes.Address} {nl ty np ni nc u blk idx : SourceValue F}
    (hdec : EnvDecoded c.E)
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (hg : Core.Good c cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr)
    (hld_ind : loadValue h' ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]))
    (hmemA : ∀ rawBytes, Hashed cs rawBytes → Address.blake3Pure rawBytes = Core.ixAddr a →
      ∃ lcA, c.E.consts.get? (Core.ixAddr a) = some lcA) :
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (Core.ixAddr a) = some cm ∧
      Bytes.RepAddressRef Core.addrTy h' b blk ∧
      idx = .field i ∧
      cm.info = .iPrj ⟨(ZMod.val i).toUInt64, Core.ixAddr b⟩ := by
  obtain ⟨rawBytes, _, cm, _, _, _, b, i,
    hhA, haA, hexA, _, _, _, _, _, hb_rep, hidx_eq, _, hcm_info, _, _⟩ :=
    inductRecord_raw_of_get_ci ev hg.2 ha hld_ind
  obtain ⟨lcA, hlcA⟩ := hmemA rawBytes hhA haA
  obtain ⟨_, hgetA, hexA₀⟩ := hdec (Core.ixAddr a) lcA hlcA
  have hescA := Core.load_escape hlcA hg.1 rawBytes hhA haA
  rw [hescA, hexA₀] at hexA
  injection hexA with hcm_eq
  rw [hcm_eq] at hgetA
  exact ⟨cm, b, i, recordAt_of_get? hlcA hgetA, hb_rep, hidx_eq, hcm_info⟩

/-- An empty-tables `Ixon.Constant` is wire-well-formed iff its `ConstantInfo` payload is. -/
theorem emptyTablesConstant_wireWF {info : Ixon.ConstantInfo} :
    (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF ↔ info.wireWF := by
  have h0 : (#[] : Array Ixon.Expr).size < UInt64.size := by change 0 < UInt64.size; decide
  have h1 : (#[] : Array _root_.Address).size < UInt64.size := by change 0 < UInt64.size; decide
  have h2 : (#[] : Array Ixon.Univ).size < UInt64.size := by change 0 < UInt64.size; decide
  constructor
  · intro hwf; exact hwf.1
  · intro hi
    exact ⟨hi, h0, by simp, h1, by simp, h2, by simp, Ixon.bindersWireWF_empty⟩

/-- Every projection `ConstantInfo` (`iPrj`, `cPrj`, `rPrj`, `dPrj`) over a 32-byte `Core.ixAddr b`
trivially satisfies `(⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF` (covering the sole caller
`DefEq/Rescue.lean:657` of `LoadFacts.canonical` unconditionally). -/
theorem projConstant_wireWF_iPrj (idx : UInt64) (b : Bytes.Address) :
    (⟨.iPrj ⟨idx, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
  rw [emptyTablesConstant_wireWF]
  show (Core.ixAddr b).hash.size = 32
  exact b.size_toArray

theorem projConstant_wireWF_cPrj (idx cidx : UInt64) (b : Bytes.Address) :
    (⟨.cPrj ⟨idx, cidx, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
  rw [emptyTablesConstant_wireWF]
  show (Core.ixAddr b).hash.size = 32
  exact b.size_toArray

theorem projConstant_wireWF_rPrj (idx : UInt64) (b : Bytes.Address) :
    (⟨.rPrj ⟨idx, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
  rw [emptyTablesConstant_wireWF]
  show (Core.ixAddr b).hash.size = 32
  exact b.size_toArray

theorem projConstant_wireWF_dPrj (idx : UInt64) (b : Bytes.Address) :
    (⟨.dPrj ⟨idx, Core.ixAddr b⟩, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF := by
  rw [emptyTablesConstant_wireWF]
  show (Core.ixAddr b).hash.size = 32
  exact b.size_toArray

/-- Core `LoadFacts.canonical` round-trip from `Ixon.Verify.deConstantExact_serConstant`. -/
theorem canonical_of_deConstantExact {lc : Ixon.LazyConstant}
    {info : Ixon.ConstantInfo} {cm : Ixon.Constant}
    (hwf : (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF)
    (hraw : lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩)
    (hdec : Ixon.deConstantExact lc.rawBytes = .ok cm) :
    cm.info = info := by
  have hrt := Ixon.Verify.deConstantExact_serConstant ⟨info, #[], #[], #[], #[]⟩ hwf
  rw [← hraw, hdec] at hrt
  injection hrt with hcm_eq
  rw [hcm_eq]

/-- `LoadFacts.canonical` companion (`Core/Good.lean:302-304`) under `EnvDecoded E` and
`(⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF`. -/
theorem canonical_of_wireWF {E : Ixon.Env} {x : _root_.Address}
    {lc : Ixon.LazyConstant} {info : Ixon.ConstantInfo} {cm : Ixon.Constant}
    (hdec : EnvDecoded E)
    (hwf : (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF)
    (hlc : E.consts.get? x = some lc)
    (hraw : lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩)
    (hget : lc.get? = some cm) :
    cm.info = info := by
  obtain ⟨_, hget', hex'⟩ := hdec x lc hlc
  rw [hget] at hget'
  injection hget' with heq
  subst heq
  exact canonical_of_deConstantExact hwf hraw hex'

/-- `LoadFacts.canonical` companion under `Ix.Cert.Stream.StoredCanonical E order` (`x ∈ order`). -/
theorem canonical_of_wireWF_storedCanonical {E : Ixon.Env} {order : List _root_.Address}
    {x : _root_.Address} {lc : Ixon.LazyConstant} {info : Ixon.ConstantInfo} {cm : Ixon.Constant}
    (hcan : Ix.Cert.Stream.StoredCanonical E order) (hx : x ∈ order)
    (hwf : (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF)
    (hlc : E.consts.get? x = some lc)
    (hraw : lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩)
    (hget : lc.get? = some cm) :
    cm.info = info :=
  canonical_of_deConstantExact hwf hraw (deConstantExact_of_storedCanonical hcan hx hlc hget)

/-- `LoadFacts.canonical` companion for uncached standalone `LazyConstant` entries. -/
theorem canonical_of_wireWF_uncached {lc : Ixon.LazyConstant}
    {info : Ixon.ConstantInfo} {cm : Ixon.Constant}
    (hnone : lc.cache = none) (hoff : lc.off = 0) (hlen : lc.len = lc.buf.size)
    (hwf : (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF)
    (hraw : lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩)
    (hget : lc.get? = some cm) :
    cm.info = info :=
  canonical_of_deConstantExact hwf hraw (deConstantExact_of_uncached hnone hoff hlen hget)

end IxVM.Refinement.L1
