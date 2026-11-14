import IxVMRefinement.Core.Good
import IxVMRefinement.L1.Records
import IxC.Ixon.Verify.Framing
import IxC.Kernel.Model.StoreCompanions
import IxC.Kernel.Model.Open.StoredFacts

/-! # Prefix sentinel store (`sentinelEnv`), `DeclStoreFacts`, and `Core.LoadFacts` assembly

Constructs the prefix sentinel store `sentinelEnv E InstalledAddr` and assembles all 14 fields of
`IxVM.Refinement.Core.LoadFacts` from `L1` (`Records` / `Decode`), the store invariants
(`Ix.Kernel.Open.StoreInv` and `Ix.Kernel.Model.TableBodies`), and a clean declaration-store
interface `DeclStoreFacts`:

1. **`sentinelEnv E InstalledAddr`**:
   keeps `E.consts[a]` at every `a` with `InstalledAddr a` and replaces every uninstalled entry
   `a ∈ E.consts` (`¬ InstalledAddr a`) with `sentinelLazy := L1.mkLazyConst ByteArray.empty dummyConst`.
   Because `Ixon.deConstant ByteArray.empty` and `Ixon.deConstantExact ByteArray.empty` fail and
   `Ixon.serConstant` on any wire-valid constant is non-empty, `Core.Good` (`Core.load_escape`)
   immediately rules out any `Ingress::get_ci` or `Ingress::load_verified_constant` call on an
   uninstalled address in `E.consts`.
2. **`DeclStoreFacts` and `loadFacts_of_declStoreFacts`**:
   reduces `Core.LoadFacts c` (all 14 fields, including `projTables`, `projTablesAt`,
   `projTablesGuard`, `indRecord`, `inductRecord`, `inductBlock`, `recordShape`, and `canonical`)
   to `StoreInv c.env`, `TableBodies c.env`, `decodedOnHashed`, `canonicalAt`, and the crisp
   per-loader / native-structure properties supplied by the declaration and assembly layers.
3. **`loadFacts_withLim` and `DeclStoreFacts` store bridges**:
   supplies `decodedOnHashed` and `canonicalAt` automatically for both `L1.EnvDecoded E` and
   `sentinelEnv E InstalledAddr`, and transports `Core.LoadFacts` across `c.lim` changes when
   `projTablesGuard` is established uniformly across limits. -/

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core (F W)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Section 1: Empty-buffer decode impossibility and `sentinelEnv` -/

/-- Dummy constant cached inside `sentinelLazy` for uninstalled prefix entries. -/
def dummyConst : Ixon.Constant :=
  ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[], #[]⟩

/-- Sentinel `LazyConstant` holding `ByteArray.empty` as `rawBytes`. -/
def sentinelLazy : Ixon.LazyConstant :=
  L1.mkLazyConst ByteArray.empty dummyConst

@[simp] theorem sentinelLazy_get? : sentinelLazy.get? = some dummyConst := rfl

@[simp] theorem sentinelLazy_rawBytes : sentinelLazy.rawBytes = ByteArray.empty :=
  L1.mkLazyConst_rawBytes ByteArray.empty dummyConst

/-- `Ixon.deConstant` never succeeds on `ByteArray.empty`. -/
theorem deConstant_empty_ne_ok (c : Ixon.Constant) :
    Ixon.deConstant ByteArray.empty ≠ .ok c := by
  intro h
  change Except.error "EOF" = Except.ok c at h
  cases h

/-- `Ixon.deConstantExact` never succeeds on `ByteArray.empty`. -/
theorem deConstantExact_empty_ne_ok (c : Ixon.Constant) :
    Ixon.deConstantExact ByteArray.empty ≠ .ok c := by
  intro h
  change Except.error "EOF" = Except.ok c at h
  cases h

/-- Any wire-valid `Ixon.Constant` serializes to a non-empty `ByteArray`. -/
theorem serConstant_ne_empty {c : Ixon.Constant} (hwf : c.wireWF) :
    Ixon.serConstant c ≠ ByteArray.empty := by
  intro hemp
  have hdec := Ixon.Verify.deConstantExact_serConstant c hwf
  rw [hemp] at hdec
  exact deConstantExact_empty_ne_ok c hdec

private theorem hm_get?_empty {α : Type} (k : _root_.Address) :
    ({} : Std.HashMap _root_.Address α).get? k = none := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]

private theorem hm_get?_insert_self {α : Type} (m : Std.HashMap _root_.Address α)
    (k : _root_.Address) (v : α) :
    (m.insert k v).get? k = some v := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]

private theorem hm_get?_insert_ne {α : Type} (m : Std.HashMap _root_.Address α)
    {k q : _root_.Address} (hne : k ≠ q) (v : α) :
    (m.insert k v).get? q = m.get? q := by
  have hbeq : (k == q) = false := by
    cases hb : (k == q)
    · rfl
    · exact absurd (beq_iff_eq.mp hb) hne
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, hbeq,
    ← Std.HashMap.get?_eq_getElem?]
  simp

private theorem hm_mem_keys_iff_isSome {α : Type} (m : Std.HashMap _root_.Address α)
    (a : _root_.Address) :
    a ∈ m.keys ↔ (m.get? a).isSome = true := by
  rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_contains,
    Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.get?_eq_getElem?]

/-- Auxiliary fold building `sentinelConsts` over a list of candidate addresses. -/
noncomputable def sentinelConstsAux (orig : Std.HashMap _root_.Address Ixon.LazyConstant)
    (InstalledAddr : _root_.Address → Prop) :
    List _root_.Address → Std.HashMap _root_.Address Ixon.LazyConstant
  | [] => {}
  | k :: ks =>
    let rest := sentinelConstsAux orig InstalledAddr ks
    match orig.get? k with
    | none => rest
    | some lc =>
      haveI := Classical.propDecidable (InstalledAddr k)
      if InstalledAddr k then rest.insert k lc else rest.insert k sentinelLazy

private theorem sentinelConstsAux_get?_not_mem
    (orig : Std.HashMap _root_.Address Ixon.LazyConstant)
    (InstalledAddr : _root_.Address → Prop) :
    ∀ (ks : List _root_.Address) {a : _root_.Address},
      a ∉ ks → (sentinelConstsAux orig InstalledAddr ks).get? a = none
  | [], _, _ => hm_get?_empty _
  | k :: ks, a, hnot => by
    have hne : k ≠ a := fun h => hnot (List.mem_cons.mpr (Or.inl h.symm))
    have hnot' : a ∉ ks := fun h => hnot (List.mem_cons.mpr (Or.inr h))
    simp only [sentinelConstsAux]
    cases hok : orig.get? k with
    | none => exact sentinelConstsAux_get?_not_mem orig InstalledAddr ks hnot'
    | some lc =>
      dsimp only
      by_cases hi : InstalledAddr k <;>
        simp only [hi, ↓reduceIte, hm_get?_insert_ne _ hne] <;>
        exact sentinelConstsAux_get?_not_mem orig InstalledAddr ks hnot'

private theorem sentinelConstsAux_get?_mem_some
    (orig : Std.HashMap _root_.Address Ixon.LazyConstant)
    (InstalledAddr : _root_.Address → Prop) :
    ∀ (ks : List _root_.Address) {a : _root_.Address} {lc : Ixon.LazyConstant},
      a ∈ ks → orig.get? a = some lc →
      (sentinelConstsAux orig InstalledAddr ks).get? a =
        by classical exact some (if InstalledAddr a then lc else sentinelLazy)
  | [], _, _, hmem, _ => nomatch hmem
  | k :: ks, a, lc, hmem, horig => by
    by_cases hka : k = a
    · subst hka
      simp only [sentinelConstsAux, horig]
      by_cases hi : InstalledAddr k
      · simp [hi, hm_get?_insert_self]
      · simp [hi, hm_get?_insert_self]
    · have hmem' : a ∈ ks := by
        rcases List.mem_cons.mp hmem with rfl | hm
        · exact absurd rfl hka
        · exact hm
      simp only [sentinelConstsAux]
      cases hok : orig.get? k with
      | none => exact sentinelConstsAux_get?_mem_some orig InstalledAddr ks hmem' horig
      | some lc' =>
        dsimp only
        by_cases hi : InstalledAddr k <;>
          simp only [hi, ↓reduceIte, hm_get?_insert_ne _ hka] <;>
          exact sentinelConstsAux_get?_mem_some orig InstalledAddr ks hmem' horig

private theorem sentinelConstsAux_get?_orig_none
    (orig : Std.HashMap _root_.Address Ixon.LazyConstant)
    (InstalledAddr : _root_.Address → Prop) :
    ∀ (ks : List _root_.Address) {a : _root_.Address},
      orig.get? a = none → (sentinelConstsAux orig InstalledAddr ks).get? a = none
  | [], _, _ => hm_get?_empty _
  | k :: ks, a, hnone => by
    by_cases hka : k = a
    · subst hka
      simp only [sentinelConstsAux, hnone]
      exact sentinelConstsAux_get?_orig_none orig InstalledAddr ks hnone
    · simp only [sentinelConstsAux]
      cases hok : orig.get? k with
      | none => exact sentinelConstsAux_get?_orig_none orig InstalledAddr ks hnone
      | some lc' =>
        dsimp only
        by_cases hi : InstalledAddr k <;>
          simp only [hi, ↓reduceIte, hm_get?_insert_ne _ hka] <;>
          exact sentinelConstsAux_get?_orig_none orig InstalledAddr ks hnone

/-- Constant table keeping `orig[a]` at `InstalledAddr a` and storing `sentinelLazy` at every
other key of `orig`. -/
noncomputable def sentinelConsts (orig : Std.HashMap _root_.Address Ixon.LazyConstant)
    (InstalledAddr : _root_.Address → Prop) :
    Std.HashMap _root_.Address Ixon.LazyConstant :=
  sentinelConstsAux orig InstalledAddr orig.keys

/-- **Prefix sentinel store**: keeps `E.consts[a]` where `InstalledAddr a` holds, and populates
every uninstalled `a ∈ E.consts` with `sentinelLazy` (`rawBytes = ByteArray.empty`), while keeping
`E.blobs` (and other `Ixon.Env` fields) unchanged. -/
noncomputable def sentinelEnv (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop) : Ixon.Env :=
  { E with consts := sentinelConsts E.consts InstalledAddr }

@[simp] theorem sentinelEnv_blobs (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop) :
    (sentinelEnv E InstalledAddr).blobs = E.blobs := rfl

theorem sentinelEnv_get?_of_installed (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop)
    {a : _root_.Address} (hi : InstalledAddr a) :
    (sentinelEnv E InstalledAddr).consts.get? a = E.consts.get? a := by
  simp only [sentinelEnv, sentinelConsts]
  cases hget : E.consts.get? a with
  | none => exact sentinelConstsAux_get?_orig_none E.consts InstalledAddr E.consts.keys hget
  | some lc =>
    have hmem : a ∈ E.consts.keys :=
      (hm_mem_keys_iff_isSome E.consts a).mpr (by rw [hget]; rfl)
    rw [sentinelConstsAux_get?_mem_some E.consts InstalledAddr E.consts.keys hmem hget]
    simp [hi]

theorem sentinelEnv_get?_of_not_installed (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop)
    {a : _root_.Address} {lc : Ixon.LazyConstant}
    (hni : ¬ InstalledAddr a) (hget : E.consts.get? a = some lc) :
    (sentinelEnv E InstalledAddr).consts.get? a = some sentinelLazy := by
  simp only [sentinelEnv, sentinelConsts]
  have hmem : a ∈ E.consts.keys :=
    (hm_mem_keys_iff_isSome E.consts a).mpr (by rw [hget]; rfl)
  rw [sentinelConstsAux_get?_mem_some E.consts InstalledAddr E.consts.keys hmem hget]
  simp [hni]

theorem sentinelEnv_get?_none (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop)
    {a : _root_.Address} (hnone : E.consts.get? a = none) :
    (sentinelEnv E InstalledAddr).consts.get? a = none :=
  sentinelConstsAux_get?_orig_none E.consts InstalledAddr E.consts.keys hnone

theorem sentinelEnv_get?_some_inv (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop)
    {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : (sentinelEnv E InstalledAddr).consts.get? a = some lc) :
    (InstalledAddr a ∧ E.consts.get? a = some lc) ∨
      (¬ InstalledAddr a ∧ lc = sentinelLazy ∧ (E.consts.get? a).isSome = true) := by
  cases hget : E.consts.get? a with
  | none =>
    rw [sentinelEnv_get?_none E InstalledAddr hget] at h
    cases h
  | some lc₀ =>
    by_cases hi : InstalledAddr a
    · rw [sentinelEnv_get?_of_installed E InstalledAddr hi, hget] at h
      injection h with heq
      subst heq
      exact Or.inl ⟨hi, rfl⟩
    · rw [sentinelEnv_get?_of_not_installed E InstalledAddr hi hget] at h
      injection h with heq
      exact Or.inr ⟨hi, heq.symm, rfl⟩

theorem sentinelEnv_isSome_iff (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop)
    (a : _root_.Address) :
    ((sentinelEnv E InstalledAddr).consts.get? a).isSome = (E.consts.get? a).isSome := by
  cases hget : E.consts.get? a with
  | none => rw [sentinelEnv_get?_none E InstalledAddr hget]
  | some lc =>
    by_cases hi : InstalledAddr a
    · rw [sentinelEnv_get?_of_installed E InstalledAddr hi, hget]
    · rw [sentinelEnv_get?_of_not_installed E InstalledAddr hi hget]; rfl

theorem recordAt_sentinelEnv_of_installed (E : Ixon.Env) (InstalledAddr : _root_.Address → Prop)
    {a : _root_.Address} (hi : InstalledAddr a) :
    Ix.Cert.recordAt (sentinelEnv E InstalledAddr) a = Ix.Cert.recordAt E a := by
  simp only [Ix.Cert.recordAt, sentinelEnv_get?_of_installed E InstalledAddr hi]

/-! ## Section 2: Sentinel contradiction / `InstalledAddr` forcing under `Core.Good` -/

/-- Under `Core.Good` on `sentinelEnv E InstalledAddr`, any address `x` present in `E.consts`
whose hashed bytes decode via `Ixon.deConstant` MUST satisfy `InstalledAddr x`: otherwise
`sentinelEnv` holds `ByteArray.empty` at `x`, `Core.load_escape` forces `bytes = ByteArray.empty`,
and `deConstant_empty_ne_ok` contradicts decoding. -/
theorem sentinelEnv_installed_of_good_deConstant {E : Ixon.Env}
    {InstalledAddr : _root_.Address → Prop} {c : Core.Ctx} {cs : List (Call F)}
    {x : _root_.Address} {bytes : ByteArray} {cm : Ixon.Constant}
    (hE : c.E = sentinelEnv E InstalledAddr)
    (hmem : (E.consts.get? x).isSome = true)
    (hg : Core.Good c cs)
    (hh : Hashed cs bytes)
    (haddr : _root_.Address.blake3Pure bytes = x)
    (hdec : Ixon.deConstant bytes = .ok cm) :
    InstalledAddr x := by
  by_contra hni
  obtain ⟨lc₀, hlc₀⟩ := Option.isSome_iff_exists.mp hmem
  have hsent : c.E.consts.get? x = some sentinelLazy := by
    rw [hE]
    exact sentinelEnv_get?_of_not_installed E InstalledAddr hni hlc₀
  have hesc := Core.load_escape hsent hg.1 bytes hh haddr
  rw [sentinelLazy_rawBytes] at hesc
  rw [hesc] at hdec
  exact deConstant_empty_ne_ok cm hdec

/-- Exact-decoding variant of `sentinelEnv_installed_of_good_deConstant`. -/
theorem sentinelEnv_installed_of_good_deConstantExact {E : Ixon.Env}
    {InstalledAddr : _root_.Address → Prop} {c : Core.Ctx} {cs : List (Call F)}
    {x : _root_.Address} {bytes : ByteArray} {cm : Ixon.Constant}
    (hE : c.E = sentinelEnv E InstalledAddr)
    (hmem : (E.consts.get? x).isSome = true)
    (hg : Core.Good c cs)
    (hh : Hashed cs bytes)
    (haddr : _root_.Address.blake3Pure bytes = x)
    (hex : Ixon.deConstantExact bytes = .ok cm) :
    InstalledAddr x :=
  sentinelEnv_installed_of_good_deConstant hE hmem hg hh haddr
    (L1.deConstant_of_deConstantExact hex)

/-- Direct `Ingress::get_ci` corollary: any good `get_ci` at an address `a` in `E.consts` against
`sentinelEnv E InstalledAddr` forces `InstalledAddr (Core.ixAddr a)`. -/
theorem sentinelEnv_installed_of_good_get_ci {E : Ixon.Env}
    {InstalledAddr : _root_.Address → Prop} {c : Core.Ctx}
    {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (hE : c.E = sentinelEnv E InstalledAddr)
    (hmem : (E.consts.get? (Core.ixAddr a)).isSome = true)
    (ev : ObsFn W "Ingress::get_ci" [addr] h ptr h' cs)
    (hg : Core.Good c cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a addr) :
    InstalledAddr (Core.ixAddr a) := by
  obtain ⟨_, rawBytes, cm, _, hh, haddr, hex, _, _, _, _⟩ := L1.get_ci_spec hg.2 ha ev
  exact sentinelEnv_installed_of_good_deConstantExact hE hmem hg hh haddr hex

/-- Any entry in `sentinelEnv E InstalledAddr` whose `rawBytes` equal `Ixon.serConstant cst` for a
wire-valid constant `cst` is necessarily an `InstalledAddr` entry inherited from `E.consts`. -/
theorem sentinelEnv_installed_of_serConstant {E : Ixon.Env}
    {InstalledAddr : _root_.Address → Prop} {x : _root_.Address}
    {lc : Ixon.LazyConstant} {cst : Ixon.Constant}
    (hwf : cst.wireWF)
    (hlc : (sentinelEnv E InstalledAddr).consts.get? x = some lc)
    (hraw : lc.rawBytes = Ixon.serConstant cst) :
    InstalledAddr x ∧ E.consts.get? x = some lc := by
  rcases sentinelEnv_get?_some_inv E InstalledAddr hlc with hok | ⟨_, rfl, _⟩
  · exact hok
  · rw [sentinelLazy_rawBytes] at hraw
    exact absurd hraw.symm (serConstant_ne_empty hwf)

/-- Collision lifting from `sentinelEnv E InstalledAddr` to `E` when padding is not replaced by an
uninstalled sentinel (or `blake3Pure ByteArray.empty ≠ padding`) and every `E.consts` address
hashed during `calls` satisfies `InstalledAddr`. -/
theorem hashedCollision_sentinelEnv_to_env {E : Ixon.Env}
    {InstalledAddr : _root_.Address → Prop} {calls : List (Call F)}
    (hpad : E.consts.get? Ix.HostAdmission.Merkle.padding = none ∨
      InstalledAddr Ix.HostAdmission.Merkle.padding ∨
      _root_.Address.blake3Pure ByteArray.empty ≠ Ix.HostAdmission.Merkle.padding)
    (hreach : ∀ x bytes, (E.consts.get? x).isSome = true →
      Hashed calls bytes → _root_.Address.blake3Pure bytes = x → InstalledAddr x)
    (hcol : View.HashedCollision { env := sentinelEnv E InstalledAddr } [] calls) :
    View.HashedCollision { env := E } [] calls := by
  rcases hcol with ⟨x, held, bytes, hsrc, hh, hne, hblk⟩ | ⟨bytes, hsrc, hpad_eq⟩
  · refine .inl ⟨x, held, bytes, ?_, hh, hne, hblk⟩
    rcases hsrc with hpre | ⟨hmem, -⟩ | hh_held
    · rcases hpre with ⟨lc, hget, rfl⟩ | hblob | ⟨rb, hrb, ha1, ha2⟩ | ⟨t, ht, -, -⟩
      · rcases sentinelEnv_get?_some_inv E InstalledAddr hget with ⟨_, hgetE⟩ | ⟨hni, _, his⟩
        · exact .inl (.inl ⟨lc, hgetE, rfl⟩)
        · exact absurd (hreach x bytes his hh hblk) hni
      · exact .inl (.inr (.inl hblob))
      · exact .inl (.inr (.inr (.inl ⟨rb, hrb, ha1, ha2⟩)))
      · cases ht
    · cases hmem
    · exact .inr (.inr hh_held)
  · rcases hsrc with hpre | hh
    · rcases hpre with ⟨lc, hget, rfl⟩ | hblob | ⟨rb, hrb, ha1, ha2⟩ | ⟨t, ht, -, -⟩
      · rcases sentinelEnv_get?_some_inv E InstalledAddr hget with ⟨_, hgetE⟩ | ⟨hni, rfl, _⟩
        · exact .inr ⟨lc.rawBytes, .inl (.inl ⟨lc, hgetE, rfl⟩), hpad_eq⟩
        · rcases hpad with hnone | hi | hne_pad
          · rw [sentinelEnv_get?_none E InstalledAddr hnone] at hget
            cases hget
          · exact absurd hi hni
          · rw [sentinelLazy_rawBytes] at hpad_eq
            exact absurd hpad_eq hne_pad
      · exact .inr ⟨bytes, .inl (.inr (.inl hblob)), hpad_eq⟩
      · exact .inr ⟨bytes, .inl (.inr (.inr (.inl ⟨rb, hrb, ha1, ha2⟩))), hpad_eq⟩
      · cases ht
    · exact .inr ⟨bytes, .inr hh, hpad_eq⟩

theorem good_sentinelEnv_of_good {E : Ixon.Env} {InstalledAddr : _root_.Address → Prop}
    {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {calls : List (Call F)}
    (hpad : E.consts.get? Ix.HostAdmission.Merkle.padding = none ∨
      InstalledAddr Ix.HostAdmission.Merkle.padding ∨
      _root_.Address.blake3Pure ByteArray.empty ≠ Ix.HostAdmission.Merkle.padding)
    (hreach : ∀ x bytes, (E.consts.get? x).isSome = true →
      Hashed calls bytes → _root_.Address.blake3Pure bytes = x → InstalledAddr x)
    (hg : Core.Good ⟨E, env, t, lim⟩ calls) :
    Core.Good ⟨sentinelEnv E InstalledAddr, env, t, lim⟩ calls :=
  ⟨fun hcol => hg.1 (hashedCollision_sentinelEnv_to_env hpad hreach hcol), hg.2⟩

/-! ## Section 3: `DeclStoreFacts` and `loadFacts_of_declStoreFacts` -/

/-- Store-decoded witness on hashed constant preimages: whenever a good derivation hashes `bytes`
at address `x` with `Ixon.deConstantExact bytes = .ok cm`, `c.E.consts` holds an entry at `x`
whose cached value and `rawBytes` decode to `cm`. -/
def DecodedOnHashed (c : Core.Ctx) : Prop :=
  ∀ (cs : List (Call F)) (x : _root_.Address) (bytes : ByteArray) (cm : Ixon.Constant),
    Core.Good c cs →
    Hashed cs bytes →
    _root_.Address.blake3Pure bytes = x →
    Ixon.deConstantExact bytes = .ok cm →
    ∃ lc : Ixon.LazyConstant,
      c.E.consts.get? x = some lc ∧
      lc.get? = some cm ∧
      Ixon.deConstantExact lc.rawBytes = .ok cm ∧
      Ixon.deConstant lc.rawBytes = .ok cm

/-- `CanonicalAt c.E`: any `LazyConstant` in `c.E.consts` whose `rawBytes` serialize a wire-valid
empty-tables `Ixon.Constant` materializes to that constant's `info`. -/
def CanonicalAt (E : Ixon.Env) : Prop :=
  ∀ (x : _root_.Address) (lc : Ixon.LazyConstant) (info : Ixon.ConstantInfo),
    (⟨info, #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF →
    E.consts.get? x = some lc →
    lc.rawBytes = Ixon.serConstant ⟨info, #[], #[], #[], #[]⟩ →
    ∀ cm, lc.get? = some cm → cm.info = info

/-- Declaration-owned projection-table core facts for member `i` of native structure block `b`:
`StoreInv` and `TableBodies` supply `tbl.numParams = nP`, `tbl.numFields = nF`, `findProj?`,
`TowerHead`, `structProjBodies`, and `structProjGuards` automatically! -/
def ProjTableCoreFact (c : Core.Ctx) (b : Bytes.Address) (i : F) : Prop :=
  ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
    c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) =
      some (.ctorInfo cvC nP nF) →
    ∃ tbl : Ix.Kernel.ProjTable .anon,
      c.env.find? (Ix.Kernel.projTableName (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
        some (.projInfo tbl) ∧
      tbl.structName = c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) ∧
      tbl.ctor = c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j) ∧
      tbl.levelParams = cvC.levelParams ∧
      (∀ cb xs ind, Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb → cb.info = .muts xs →
        xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
      ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
        ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort

/-- Crisp interface bundling the store invariants, `L1` decoded-record bridge, loader environment
matches, and `L5` native-inductive store facts required to assemble `Core.LoadFacts c`. -/
structure DeclStoreFacts (c : Core.Ctx) : Prop where
  storeInv : Ix.Kernel.Open.StoreInv c.env
  tableBodies : Ix.Kernel.Model.TableBodies c.env
  decodedOnHashed : DecodedOnHashed c
  canonicalAt : CanonicalAt c.E
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Core.Good c cs →
    Bytes.RepAddressRef Core.addrTy h a addr →
      ∃ ci, c.env.find? (c.κ (Core.ixAddr a)) = some ci ∧ Core.CIPtrRep c.κ h' ptr ci
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs → Core.Good c cs →
    Bytes.RepAddressRef Core.addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) =
        some ci ∧ Core.CIPtrRep c.κ h' ptr ci
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs → Core.Good c cs →
    Bytes.RepAddressRef Core.addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) = some ci ∧
        Core.CIPtrRep c.κ h' ptr ci
  projTablesCore : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs → Core.Good c cs →
    Bytes.RepAddressRef Core.addrTy h b bp → ip = .field i →
    ProjTableCoreFact c b i
  projTablesAtCore : ∀ (bp sap ptr nl ty np u blk : SourceValue F) (h h' h1 h2 : Heap F)
      (cs cs1 : List (Call F)) (b s : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' cs → Core.Good c cs →
    Bytes.RepAddressRef Core.addrTy h b bp →
    ObsFn W "Ingress::get_ci" [sap] h1 ptr h2 cs1 → Core.Good c cs1 →
    Bytes.RepAddressRef Core.addrTy h1 s sap →
    loadValue h2 ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef Core.addrTy h2 b blk →
    ProjTableCoreFact c b i
  projTablesGuard : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs → Core.Good c cs →
    Bytes.RepAddressRef Core.addrTy h b bp → ip = .field i →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat)
      (tbl : Ix.Kernel.ProjTable .anon),
      c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) =
        some (.ctorInfo cvC nP nF) →
      c.env.find? (Ix.Kernel.projTableName (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
        some (.projInfo tbl) →
      Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true ∧
      (Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
        ∀ (f : F) (rc bp' rg : SourceValue F) (hg hg' : Heap F) (csg : List (Call F))
          (g : Core.KLevel) (us : List Core.KLevel),
          ZMod.val f < nF → us.length = tbl.levelParams.length →
          ObsFn W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg →
          Core.Good c csg → Core.RCRep c.t c.lim hg rc →
          Bytes.RepAddressRef Core.addrTy hg b bp' →
          IxVM.Refinement.KernelLevels.RepKLevel hg' g rg →
          (∀ φ, Ix.Kernel.Level.eval φ
            (Ix.Kernel.Level.subst (List.range us.length) us g) = 0) →
          ∀ φ, Ix.Kernel.Level.eval φ
            (Ix.Kernel.Level.subst tbl.levelParams us (tbl.entry (ZMod.val f)).fieldSort) = 0)
  unitLike : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cvC : Ix.Kernel.ConstantVal .anon) (nPc : Nat),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Core.Good c cs →
    Bytes.RepAddressRef Core.addrTy h a ap →
    loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef Core.addrTy h' b blk →
    c.env.find? (c.κ (Core.ixAddr a)) = some (.indInfo cvT caps) →
    Core.FewInductives c (Core.ixAddr b) →
    c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvC nPc 0) →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (c.κ (Core.ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const (c.κ (Core.ixAddr a)) us) = true))
  eta : ∀ (ac b sa : Bytes.Address) (i : F) (j : Nat) (cvc cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List Core.KLevel) (l : Core.KLevel)
      (bp ptr nl ty np u blk idx : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F)),
    c.env.find? (c.κ (Core.ixAddr ac)) = some (.ctorInfo cvc cnP cnF) →
    cvc.name = c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j) → 0 < cnF →
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h1 ptr h2 cs1 → Core.Good c cs1 →
    Bytes.RepAddressRef Core.addrTy h1 b bp →
    loadValue h2 ptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, idx]) →
    c.env.find? (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_modeled" [bq] h3 (.field 0) h4 cs3 ∧ Core.Good c cs3 ∧
        Bytes.RepAddressRef Core.addrTy h3 b bq) →
    Core.piSortAt cnP (Core.posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Core.Good c cs5 ∧
        Bytes.RepAddressRef Core.addrTy h5 sa sp) →
    Core.ixAddr sa = Core.iprjAddr (Core.ixAddr b) (ZMod.val i) →
    caps.eta = true ∧ caps.etaCtor = some (c.κ (Core.ixAddr ac)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cvc.levelParams = cvT.levelParams
  etaIota : ∀ (pp ptr nl ty u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (pa b : Bytes.Address) (i m : F) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List Core.KLevel) (l : Core.KLevel),
    ObsFn W "Ingress::get_ci" [pp] h1 ptr h2 cs1 → Core.Good c cs1 →
    Bytes.RepAddressRef Core.addrTy h1 pa pp →
    loadValue h2 ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, .field m, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef Core.addrTy h2 b blk →
    c.env.find? (c.κ (Core.ixAddr pa)) = some (.indInfo cvT caps) →
    c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) =
      some (.ctorInfo cvc cnP cnF) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧ Core.Good c cs3 ∧
        Bytes.RepAddressRef Core.addrTy h3 b bq) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Core.Good c cs5 ∧
        Bytes.RepAddressRef Core.addrTy h5 pa sp) →
    Core.piSortAt (ZMod.val m) (Core.posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    caps.eta = true ∧
      caps.etaCtor = some (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) ∧
      caps.etaFields = cnF ∧ caps.etaParams = cnP ∧ cnP = ZMod.val m ∧
      cvc.levelParams = cvT.levelParams

/-- Upgrade `ProjTableCoreFact` to the full projection-table conclusion read by `LoadFacts.projTables`
and `LoadFacts.projTablesAt` using `StoreInv` (`ProjOkT`) and `TableBodies`. -/
theorem projTableFull_of_core {c : Core.Ctx} {b : Bytes.Address} {i : F}
    (hS : Ix.Kernel.Open.StoreInv c.env)
    (hTB : Ix.Kernel.Model.TableBodies c.env)
    (hcore : ProjTableCoreFact c b i)
    (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat)
    (hctor : c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) =
      some (.ctorInfo cvC nP nF)) :
    ∃ tbl : Ix.Kernel.ProjTable .anon,
      c.env.find? (Ix.Kernel.projTableName (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
        some (.projInfo tbl) ∧
      tbl.structName = c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) ∧
      tbl.ctor = c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j) ∧
      tbl.numParams = nP ∧
      tbl.numFields = nF ∧
      tbl.levelParams = cvC.levelParams ∧
      (∀ cb xs ind, Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb → cb.info = .muts xs →
        xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
      (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
        Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
      Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
      (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
        tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
      ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
        ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort := by
  obtain ⟨tbl, hfindT, hsn, htc, hlps, hnp_rec, hstrip⟩ := hcore j cvC nP nF hctor
  obtain ⟨cvC', hctor', hbodies, hsorts⟩ := hTB _ tbl hfindT
  rw [htc, hctor] at hctor'
  obtain ⟨rfl, hnp_eq, hnf_eq⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj (Option.some.inj hctor')
  have hnp : tbl.numParams = nP := hnp_eq.symm
  have hnf : tbl.numFields = nF := hnf_eq.symm
  rw [hnp, hnf] at hbodies hsorts
  refine ⟨tbl, hfindT, hsn, htc, hnp, hnf, hlps, hnp_rec, ?_, hbodies, hsorts, hstrip⟩
  intro f hf
  have hf' : f < tbl.numFields := by rw [hnf]; exact hf
  have hfp : c.env.findProj? tbl.structName f = some (tbl.entry f) := by
    unfold Ix.Kernel.Env.findProj?
    rw [hsn, hfindT]
    dsimp only
    simp only [hf', ↓reduceIte]
  exact ⟨hfp, hS.proj_ok _ tbl hfindT f hf'⟩

/-- **Assemble `Core.LoadFacts c`** (all 14 fields) from `DeclStoreFacts c`. -/
theorem loadFacts_of_declStoreFacts {c : Core.Ctx} (hd : DeclStoreFacts c) :
    Core.LoadFacts c where
  getCI := hd.getCI
  getCprj := hd.getCprj
  getIprj := hd.getIprj
  indRecord := by
    intro addr ptr h h' cs a cm cb p xs ind ev hg ha hcm hcm_info hcb hcb_info hxs
    obtain ⟨_, rawBytes, cm', _, hhA, haA, hexA, _, _, _, hres⟩ := L1.get_ci_spec hg.2 ha ev
    obtain ⟨lcA, hlcA, hgetA, hex_lcA, _⟩ :=
      hd.decodedOnHashed cs (Core.ixAddr a) rawBytes cm' hg hhA haA hexA
    have hcm_eq : cm' = cm := by
      unfold Ix.Cert.recordAt at hcm
      rw [hlcA, Option.bind_some, hgetA] at hcm
      exact Option.some.inj hcm
    subst hcm_eq
    simp only [L1.GetCIRawResult, hcm_info] at hres
    obtain ⟨_, blkBytes, cb', _, _, _, hhB, haB, hexB, _, _, _, _, _⟩ := hres
    obtain ⟨lcB, hlcB, hgetB, hex_lcB, _⟩ :=
      hd.decodedOnHashed cs p.block blkBytes cb' hg hhB haB hexB
    have hcb_eq : cb' = cb := by
      unfold Ix.Cert.recordAt at hcb
      rw [hlcB, Option.bind_some, hgetB] at hcb
      exact Option.some.inj hcb
    subst hcb_eq
    refine L1.indRecord_of_deConstantExact ?_ ?_ ev hg ha hcm hcm_info hcb hcb_info hxs
    · intro lc hget
      rw [hlcA] at hget
      injection hget with e
      subst e
      exact hex_lcA
    · intro lc hget
      rw [hlcB] at hget
      injection hget with e
      subst e
      exact hex_lcB
  inductRecord := by
    intro addr ptr h h' cs a nl ty np ni nc u blk idx ev hg ha hld
    obtain ⟨rawBytes, _, cm, _, _, _, b, i,
      hhA, haA, hexA, _, _, _, _, _, hb_rep, hidx_eq, _, hcm_info, _, _⟩ :=
      L1.inductRecord_raw_of_get_ci ev hg.2 ha hld
    obtain ⟨lcA, hlcA, hgetA, _, _⟩ :=
      hd.decodedOnHashed cs (Core.ixAddr a) rawBytes cm hg hhA haA hexA
    refine ⟨cm, b, i, ?_, hb_rep, hidx_eq, hcm_info⟩
    unfold Ix.Cert.recordAt
    rw [hlcA, Option.bind_some]
    exact hgetA
  projTables := fun bp ip ptr h h' cs b i ev hg hb hip j cvC nP nF hctor =>
    projTableFull_of_core hd.storeInv hd.tableBodies
      (hd.projTablesCore bp ip ptr h h' cs b i ev hg hb hip) j cvC nP nF hctor
  projTablesAt := fun bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i
      evM hgM hb evG hgG hs hld hblk j cvC nP nF hctor =>
    projTableFull_of_core hd.storeInv hd.tableBodies
      (hd.projTablesAtCore bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i
        evM hgM hb evG hgG hs hld hblk) j cvC nP nF hctor
  unitLike := hd.unitLike
  eta := hd.eta
  etaIota := hd.etaIota
  recordShape := by
    intro ap r h h' cs a cst ev hg ha hrec
    obtain ⟨_, bytes, c', hh, haddr, hex, _, _, _, _, _, _, cRep⟩ :=
      L1.load_verified_constant_decode ha ev
    have haddr' : _root_.Address.blake3Pure ⟨bytes.toArray⟩ = Core.ixAddr a := haddr
    obtain ⟨lc, hlc, hget, _, _⟩ :=
      hd.decodedOnHashed cs (Core.ixAddr a) ⟨bytes.toArray⟩ c' hg hh haddr' hex
    have hc_eq : c' = cst := by
      unfold Ix.Cert.recordAt at hrec
      rw [hlc, Option.bind_some, hget] at hrec
      exact Option.some.inj hrec
    subst hc_eq
    exact cRep.toConstShapeRep
  inductBlock := by
    intro addr ptr h h' cs a b nl ty np ni nc u blk i ev hg ha hld hblk
    obtain ⟨_, blkBytes, _, cb, xs, ind, b', i',
      _, _, _, _, hhB, haB, hexB, _, hb'_rep, hidx_eq, _, _, hcb_info, hxs⟩ :=
      L1.inductRecord_raw_of_get_ci ev hg.2 ha hld
    have hb_eq : b' = b := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb'_rep hblk
    have hi_eq : i' = i := Value.field.inj hidx_eq.symm
    subst hb_eq hi_eq
    obtain ⟨lcB, hlcB, hgetB, _, _⟩ :=
      hd.decodedOnHashed cs (Core.ixAddr b') blkBytes cb hg hhB haB hexB
    refine ⟨cb, xs, ind, ?_, hcb_info, hxs⟩
    unfold Ix.Cert.recordAt
    rw [hlcB, Option.bind_some]
    exact hgetB
  projTablesGuard := hd.projTablesGuard
  canonical := hd.canonicalAt

/-! ## Section 4: `DecodedOnHashed`, `CanonicalAt`, and `loadFacts_withLim` bridges -/

/-- `L1.EnvDecoded c.E` together with hashed-address coverage yields `DecodedOnHashed c`. -/
theorem decodedOnHashed_of_envDecoded {c : Core.Ctx}
    (hdec : L1.EnvDecoded c.E)
    (hmem : ∀ cs x bytes cm,
      Core.Good c cs → Hashed cs bytes → _root_.Address.blake3Pure bytes = x →
      Ixon.deConstantExact bytes = .ok cm → (c.E.consts.get? x).isSome = true) :
    DecodedOnHashed c := by
  intro cs x bytes cm hg hh haddr hex
  obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (hmem cs x bytes cm hg hh haddr hex)
  obtain ⟨cm₀, hget₀, hex₀⟩ := hdec x lc hlc
  have hesc := Core.load_escape hlc hg.1 bytes hh haddr
  rw [hesc, hex₀] at hex
  injection hex with hcm_eq
  subst hcm_eq
  exact ⟨lc, hlc, hget₀, hex₀, L1.deConstant_of_deConstantExact hex₀⟩

/-- On `sentinelEnv E InstalledAddr`, `L1.EnvDecoded E` and membership in `E.consts` automatically
establish BOTH `InstalledAddr x` AND `DecodedOnHashed c` (via `sentinelEnv_installed_of_good_deConstantExact`). -/
theorem decodedOnHashed_sentinelEnv {E : Ixon.Env} {InstalledAddr : _root_.Address → Prop}
    {c : Core.Ctx}
    (hE : c.E = sentinelEnv E InstalledAddr)
    (hdec : L1.EnvDecoded E)
    (hmem : ∀ cs x bytes cm,
      Core.Good c cs → Hashed cs bytes → _root_.Address.blake3Pure bytes = x →
      Ixon.deConstantExact bytes = .ok cm → (E.consts.get? x).isSome = true) :
    DecodedOnHashed c := by
  intro cs x bytes cm hg hh haddr hex
  have his := hmem cs x bytes cm hg hh haddr hex
  have hi : InstalledAddr x :=
    sentinelEnv_installed_of_good_deConstantExact hE his hg hh haddr hex
  obtain ⟨lc, hlcE⟩ := Option.isSome_iff_exists.mp his
  have hlc : c.E.consts.get? x = some lc := by
    rw [hE, sentinelEnv_get?_of_installed E InstalledAddr hi]
    exact hlcE
  obtain ⟨cm₀, hget₀, hex₀⟩ := hdec x lc hlcE
  have hesc := Core.load_escape hlc hg.1 bytes hh haddr
  rw [hesc, hex₀] at hex
  injection hex with hcm_eq
  subst hcm_eq
  exact ⟨lc, hlc, hget₀, hex₀, L1.deConstant_of_deConstantExact hex₀⟩

/-- `L1.EnvDecoded E` directly implies `CanonicalAt E`. -/
theorem canonicalAt_of_envDecoded {E : Ixon.Env} (hdec : L1.EnvDecoded E) :
    CanonicalAt E :=
  fun _ _ _ hwf hlc hraw _ hget => L1.canonical_of_wireWF hdec hwf hlc hraw hget

/-- `CanonicalAt` holds on `sentinelEnv E InstalledAddr` whenever it holds on `E`: any serialized
wire-valid constant is non-empty, forcing `InstalledAddr x` via `sentinelEnv_installed_of_serConstant`. -/
theorem canonicalAt_sentinelEnv {E : Ixon.Env} {InstalledAddr : _root_.Address → Prop}
    (hcan : CanonicalAt E) :
    CanonicalAt (sentinelEnv E InstalledAddr) := by
  intro x lc info hwf hlc hraw cm hget
  obtain ⟨_, hlcE⟩ := sentinelEnv_installed_of_serConstant hwf hlc hraw
  exact hcan x lc info hwf hlcE hraw cm hget

/-- `CanonicalAt (sentinelEnv E InstalledAddr)` directly from `L1.EnvDecoded E`. -/
theorem canonicalAt_sentinelEnv_of_envDecoded {E : Ixon.Env}
    {InstalledAddr : _root_.Address → Prop} (hdec : L1.EnvDecoded E) :
    CanonicalAt (sentinelEnv E InstalledAddr) :=
  canonicalAt_sentinelEnv (canonicalAt_of_envDecoded hdec)

/-- Transport `Core.LoadFacts` across a change in `c.lim`, given `projTablesGuard` at the new limit
(every other field of `Core.LoadFacts` is independent of `c.lim`). -/
theorem loadFacts_withLim {c : Core.Ctx} (hl : Core.LoadFacts c) (lim' : Option Nat)
    (hguard : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
        (b : Bytes.Address) (i : F),
      ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs →
      Core.Good { c with lim := lim' } cs →
      Bytes.RepAddressRef Core.addrTy h b bp → ip = .field i →
      ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat)
        (tbl : Ix.Kernel.ProjTable .anon),
        c.env.find? (c.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) =
          some (.ctorInfo cvC nP nF) →
        c.env.find? (Ix.Kernel.projTableName (c.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) →
        Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true ∧
        (Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
          ∀ (f : F) (rc bp' rg : SourceValue F) (hg hg' : Heap F) (csg : List (Call F))
            (g : Core.KLevel) (us : List Core.KLevel),
            ZMod.val f < nF → us.length = tbl.levelParams.length →
            ObsFn W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg →
            Core.Good { c with lim := lim' } csg → Core.RCRep c.t lim' hg rc →
            Bytes.RepAddressRef Core.addrTy hg b bp' →
            IxVM.Refinement.KernelLevels.RepKLevel hg' g rg →
            (∀ φ, Ix.Kernel.Level.eval φ
              (Ix.Kernel.Level.subst (List.range us.length) us g) = 0) →
            ∀ φ, Ix.Kernel.Level.eval φ
              (Ix.Kernel.Level.subst tbl.levelParams us (tbl.entry (ZMod.val f)).fieldSort) = 0)) :
    Core.LoadFacts { c with lim := lim' } where
  getCI := hl.getCI
  getCprj := hl.getCprj
  getIprj := hl.getIprj
  indRecord := hl.indRecord
  inductRecord := hl.inductRecord
  projTables := hl.projTables
  projTablesAt := hl.projTablesAt
  unitLike := hl.unitLike
  eta := hl.eta
  etaIota := hl.etaIota
  recordShape := hl.recordShape
  inductBlock := hl.inductBlock
  projTablesGuard := hguard
  canonical := hl.canonical

end IxVM.Refinement.Assembly
