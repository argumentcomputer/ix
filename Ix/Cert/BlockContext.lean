import Ix.Cert.ClosureKeying
import Ix.Cert.BlockRefs
import Ix.Cert.EvidenceTransfer

/-! # A block's compile-side reading context, built from the closure's

The compile-side reading theorems (`RecordReadings`, `DefinitionBlockReads`, `InductiveCompile`)
read a block's compile in a context `cx₁` that keys every name the compile binds
(`BindingsCorrect`), and move the reading to the closure's context `cx` through
`RecordTransfer.RefsLe`: wherever `cx₁` reads one of the block's references, `cx` reads it alike.
This module builds such a `cx₁` from `cx` (`blockCtx`).

**The store.** `cx₁` keeps `cx`'s records at the block's references, at the closure order's
stored records and at those records' blocks (`Kept`); anywhere else it holds an axiom record,
which resolves to itself, so every other address reads as its own key. Keys are computed from
the store (no keys ahead), roles are `cx`'s.

* At a reference, `cx₁` resolves no more than `cx` (`resolveSource_sub`: an axiom record is no
  block), so it reads a key only where `cx` reads it alike (`keyAt_le`, `refsLe`).
* At a stored record of the order, the two stores agree at the record and at its block, so the
  two contexts read one key (`decoded_resolve`, `keyAt_iff`).
* An address the compile binds is a stored record that resolves in the artifact's store
  (`BoundResolve`, the fold's premise); either it is kept, hence a record of the order (a
  reference of the block's record is in the closure), or it holds the axiom record: either way
  `cx₁` keys it (`keyAt_bound`). -/

namespace Ix.Cert.BlockContext

open Ix.Kernel Ix.Kernel.Reader

/-! ## The store -/

/-- The addresses a block's compile-side context keeps from the closure's: the block's
references, the closure order's stored records, and their blocks. -/
def Kept (ixe : Ixon.Env) (order : List Address) (refs : Array Address) (a : Address) : Prop :=
  a ∈ refs ∨ (a ∈ order ∧ (recordAt ixe a).isSome = true) ∨
    ∃ x c, x ∈ order ∧ recordAt ixe x = some c ∧ ownerOf x c = a

open Classical in
/-- **The block's store**: the closure's at kept addresses, an axiom record elsewhere. -/
noncomputable def blockStore (store : Store) (ixe : Ixon.Env) (order : List Address) (refs : Array Address) :
    Store := fun a => if Kept ixe order refs a then store a else some BlockRefs.anyRecord

/-- **The block's compile-side context**: the block's store, the compile's blobs, the closure's
roles, index, hints and reconstruction, no keys computed ahead. -/
noncomputable def blockCtx (cx : Ctx .anon) (ixe : Ixon.Env) (order : List Address) (refs : Array Address)
    (blob : Address → Option ByteArray) : Ctx .anon :=
  { store := blockStore cx.store ixe order refs, blob, roles := cx.roles, index := cx.index, hint := cx.hint,
    reconstruct := cx.reconstruct }

variable {ixe : Ixon.Env} {order : List Address} {refs : Array Address}

theorem blockStore_kept {store : Store} {a : Address} (h : Kept ixe order refs a) :
    blockStore store ixe order refs a = store a := by
  simp [blockStore, h]

theorem blockStore_other {store : Store} {a : Address} (h : ¬ Kept ixe order refs a) :
    blockStore store ixe order refs a = some BlockRefs.anyRecord := by
  simp [blockStore, h]

theorem blockStore_cases (store : Store) (a : Address) :
    blockStore store ixe order refs a = store a ∨ blockStore store ixe order refs a = some BlockRefs.anyRecord := by
  by_cases h : Kept ixe order refs a
  · exact .inl (blockStore_kept h)
  · exact .inr (blockStore_other h)

/-! ## Resolution -/

/-- A store that holds another's records or an axiom record resolves no more than it. -/
theorem resolveSource_sub {s s' : Store} (hs : ∀ x, s' x = s x ∨ s' x = some BlockRefs.anyRecord)
    {a : Address} {c : Ixon.Constant} {q : ConstRef Address} (h : resolveSource s' a c = some q) :
    resolveSource s a c = some q := by
  cases hi : c.info with
  | defn _ | recr _ | axio _ | quot _ => simpa [resolveSource, hi] using h
  | muts _ => simp [resolveSource, hi] at h
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    simp only [resolveSource, hi] at h ⊢
    rcases hs p.block with e | e
    · rw [← e]; exact h
    · simp [e, BlockRefs.anyRecord] at h

/-- A record's resolution reads the store only at its block. -/
theorem resolveSource_of_owner {s s' : Store} {a : Address} {c : Ixon.Constant} {q : ConstRef Address}
    (h : resolveSource s a c = some q) (ho : ∀ cb, s (ownerOf a c) = some cb → s' (ownerOf a c) = some cb) :
    resolveSource s' a c = some q := by
  cases hi : c.info with
  | defn _ | recr _ | axio _ | quot _ => simpa [resolveSource, hi] using h
  | muts _ => simp [resolveSource, hi] at h
  | dPrj p | iPrj p | rPrj p | cPrj p =>
    simp only [ownerOf, hi] at ho
    simp only [resolveSource, hi] at h ⊢
    cases hb : s p.block with
    | none => simp [hb] at h
    | some cb => rw [ho cb hb]; simpa [hb] using h

theorem resolve_sub {s s' : Store} (hs : ∀ x, s' x = s x ∨ s' x = some BlockRefs.anyRecord) {a : Address}
    (ha : s' a = s a) {q : ConstRef Address} (h : resolve s' a = some q) : resolve s a = some q := by
  unfold resolve at h ⊢
  rw [← ha]
  obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
  rw [hc]
  exact resolveSource_sub hs h

theorem keyOfAddress_congr {s s' : Store} {roles : Bindings .anon} {a : Address} (h : resolve s a = resolve s' a) :
    keyOfAddress s roles a = keyOfAddress s' roles a := by
  unfold keyOfAddress
  rw [h]

/-! ## The block's references -/

/-- **The block's context reads a key at a kept address only where the closure's reads it
alike.** -/
theorem keyAt_le {cx : Ctx .anon} {blob : Address → Option ByteArray} {a : Address} (hk : Kept ixe order refs a)
    {k : CName .anon} (h : (blockCtx cx ixe order refs blob).keyAt a = .ok k) : cx.keyAt a = .ok k := by
  rw [Ctx.keyAt_eq_ok] at h ⊢
  change keyOfAddress (blockStore cx.store ixe order refs) cx.roles a = some k at h
  unfold keyOfAddress at h ⊢
  obtain ⟨q, hq, h⟩ := Option.bind_eq_some_iff.mp h
  rw [resolve_sub (blockStore_cases cx.store) (blockStore_kept hk) hq]
  exact h

/-- **The closure's context reads the block's record's references as the block's context
does**, given that it reads alike the blobs the block's context reads there. -/
theorem refsLe {cx : Ctx .anon} {c : Ixon.Constant} {blob : Address → Option ByteArray}
    {after : Ix.CompileM.BlockState}
    (blobs : ∀ a ∈ c.refs, ∀ bytes, (after.blockBlobs.get? a).orElse (fun _ => blob a) = some bytes →
      cx.blob a = some bytes) :
    RecordTransfer.RefsLe c (Ix.CompileCert.ExpressionRead.withBlockBlobs (blockCtx cx ixe order c.refs blob) after) cx where
  keyAt _ ha _ h := keyAt_le (.inl ha) h
  blob _ ha _ h := blobs _ ha _ h

/-! ## The closure order's records -/

/-- A kept address that the artifact stores is a record of the closure order, when the block's
record is. -/
theorem order_of_kept {S : Address → Prop} (corder : ClosureOrder ixe S order) {B : Address} {c : Ixon.Constant}
    (hB : B ∈ order) (hc : recordAt ixe B = some c) {a : Address} (hk : Kept ixe order c.refs a)
    (stored : ixe.consts.contains a = true) : a ∈ order := by
  rcases hk with hr | ⟨ho, -⟩ | ⟨x, cx, hx, hcx, hown⟩
  · exact (corder.complete a).mpr (.step ((corder.complete B).mp hB)
      ⟨c, hc, .inr ⟨Array.contains_iff_mem.mpr hr, stored⟩⟩)
  · exact ho
  · by_cases e : a = x
    · exact e ▸ hx
    · exact (corder.complete a).mpr (.step ((corder.complete x).mp hx) ⟨cx, hcx, .inl ⟨hown, e⟩⟩)

/-- A record of the closure order and its block are kept, and the two stores agree there. -/
theorem decoded_resolve {t : RoleTable} {preA : Prelude .anon} {S : Address → Prop}
    (corder : ClosureOrder ixe S order) {a : Address} {c : Ixon.Constant} (ha : a ∈ order)
    (hc : recordAt ixe a = some c) :
    resolve (blockStore (closureContext ixe t preA order).store ixe order refs) a =
      resolve (closureContext ixe t preA order).store a := by
  have hs : (closureContext ixe t preA order).store a = some c := ClosureKeying.closure_store corder.nodup ha hc
  have hk : Kept ixe order refs a := .inr (.inl ⟨ha, by rw [hc]; rfl⟩)
  have ho : Kept ixe order refs (ownerOf a c) := .inr (.inr ⟨a, c, ha, hc, rfl⟩)
  exact EvidenceTransfer.resolve_congr (by rw [blockStore_kept hk]; exact hs) hs (blockStore_kept ho)

/-- **At a record of the closure order the block's context reads the closure's key.** -/
theorem keyAt_iff {t : RoleTable} {preA : Prelude .anon} {S : Address → Prop} (corder : ClosureOrder ixe S order)
    {blob : Address → Option ByteArray} {a : Address} {c : Ixon.Constant} (ha : a ∈ order)
    (hc : recordAt ixe a = some c) {k : CName .anon} :
    (blockCtx (closureContext ixe t preA order) ixe order refs blob).keyAt a = .ok k ↔
      (closureContext ixe t preA order).keyAt a = .ok k := by
  rw [Ctx.keyAt_eq_ok, Ctx.keyAt_eq_ok]
  change keyOfAddress (blockStore (closureContext ixe t preA order).store ixe order refs)
    (closureContext ixe t preA order).roles a = some k ↔ _
  rw [keyOfAddress_congr (decoded_resolve corder ha hc)]

/-- A stored record that resolves in the artifact's store resolves alike in the closure's, when it
is a record of the closure order. -/
theorem closure_resolve {t : RoleTable} {preA : Prelude .anon} {S : Address → Prop}
    (corder : ClosureOrder ixe S order) {a : Address} {c : Ixon.Constant} (ha : a ∈ order)
    (hc : recordAt ixe a = some c) {q : ConstRef Address} (hq : resolveSource (recordAt ixe) a c = some q) :
    resolve (closureContext ixe t preA order).store a = some q := by
  have hs : (closureContext ixe t preA order).store a = some c := ClosureKeying.closure_store corder.nodup ha hc
  unfold resolve
  rw [hs]
  refine resolveSource_of_owner hq fun cb hcb => ?_
  have hown : ownerOf a c ∈ order := by
    by_cases e : ownerOf a c = a
    · rw [e]; exact ha
    · exact (corder.complete _).mpr (.step ((corder.complete a).mp ha) ⟨c, hc, .inl ⟨rfl, e⟩⟩)
  exact ClosureKeying.closure_store corder.nodup hown hcb

/-- **Every address the compile binds holds a stored record of the artifact that resolves
there.** The fold's premise for a block's compile-side context. -/
def BoundResolve (ixe : Ixon.Env) (cenv : Ix.CompileM.CompileEnv) : Prop :=
  ∀ m a, Ix.CompileCert.ExpressionState.lookupBinding cenv (Ix.CompileCert.ExpressionState.bindingView {}) m = some a →
    ∃ c, recordAt ixe a = some c ∧ (resolveSource (recordAt ixe) a c).isSome = true

/-- **The block's context keys a stored record that resolves in the artifact's store**, when the
block's record is in the closure order. -/
theorem keyAt_stored {t : RoleTable} {preA : Prelude .anon} {S : Address → Prop}
    (corder : ClosureOrder ixe S order) {blob : Address → Option ByteArray} {B : Address} {cB : Ixon.Constant}
    (hB : B ∈ order) (hcB : recordAt ixe B = some cB) {a : Address} {c : Ixon.Constant}
    (hc : recordAt ixe a = some c) (hres : (resolveSource (recordAt ixe) a c).isSome = true) :
    ∃ k, (blockCtx (closureContext ixe t preA order) ixe order cB.refs blob).keyAt a = .ok k := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hres
  have key : ∀ (s : Store) (q' : ConstRef Address), resolve s a = some q' →
      ∃ k, keyOfAddress s (closureContext ixe t preA order).roles a = some k := by
    intro s q' h
    unfold keyOfAddress
    rw [h]
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  by_cases hk : Kept ixe order cB.refs a
  · have ha := order_of_kept corder hB hcB hk (ClosureLayout.recordAt_contains hc)
    have hr : resolve (blockStore (closureContext ixe t preA order).store ixe order cB.refs) a = some q := by
      rw [decoded_resolve (t := t) (preA := preA) corder ha hc]
      exact closure_resolve corder ha hc hq
    obtain ⟨k, hkey⟩ := key _ q hr
    exact ⟨k, Ctx.keyAt_eq_ok.mpr hkey⟩
  · have hr : resolve (blockStore (closureContext ixe t preA order).store ixe order cB.refs) a = some (.member a 0) := by
      unfold resolve
      rw [blockStore_other hk]
      simp [resolveSource, BlockRefs.anyRecord]
    obtain ⟨k, hkey⟩ := key _ _ hr
    exact ⟨k, Ctx.keyAt_eq_ok.mpr hkey⟩

/-! ## The singleton's own key -/

/-- A record that is its own member 0: a definition, recursor, axiom or quotient record. -/
def lone : Ixon.ConstantInfo → Bool
  | .defn _ | .recr _ | .axio _ | .quot _ => true
  | _ => false

/-- In a context with no keys computed ahead, a singleton record's member is keyed as its
address. -/
theorem blockCtx_memberKey {cx : Ctx .anon} {blob : Address → Option ByteArray} {B : Address} {c : Ixon.Constant}
    (hB : (blockCtx cx ixe order refs blob).store B = some c) (single : lone c.info = true) :
    (blockCtx cx ixe order refs blob).memberKey (.member B 0) = (blockCtx cx ixe order refs blob).keyAt B := by
  have hres : resolve (blockCtx cx ixe order refs blob).store B = some (.member B 0) := by
    unfold resolve
    rw [hB]
    cases hi : c.info <;> simp_all [lone, resolveSource]
  have hsing : singletonAt (blockCtx cx ixe order refs blob).store (.member B 0) = some B := by
    cases hi : c.info <;> simp_all [lone, singletonAt]
  unfold Ctx.memberKey Ctx.keyAt
  have hka : (blockCtx cx ixe order refs blob).keys.address[(ConstRef.member B 0 : ConstRef Address)]? = none := by
    simp [blockCtx]
  have hkb : (blockCtx cx ixe order refs blob).keys.byAddress[B]? = none := by
    simp [blockCtx]
  cases hrole : (blockCtx cx ixe order refs blob).roles.names[(ConstRef.member B 0 : ConstRef Address)]? with
  | some k => simp [hres, hrole, hkb]
  | none => simp [Ctx.addressOf, hka, hsing, hres, hrole, hkb, bind, Except.bind, pure, Except.pure, Mode.addressId?]

/-- In the closure's context, a singleton record's member is keyed as its address, on an
authentic store. -/
theorem closure_memberKey {cx : Ctx .anon} (auth : ∀ a c, cx.store a = some c → a = Address.admissionHash (Ixon.serConstant c))
    {B : Address} {c : Ixon.Constant} (hB : cx.store B = some c) (single : lone c.info = true) :
    cx.memberKey (.member B 0) = cx.keyAt B := by
  have hres : resolve cx.store B = some (.member B 0) := by
    unfold resolve
    rw [hB]
    cases hi : c.info <;> simp_all [lone, resolveSource]
  have hsing : singletonAt cx.store (.member B 0) = some B := by
    cases hi : c.info <;> simp_all [lone, singletonAt]
  -- an address keyed for the member resolves to it, so it is `B`
  have haddr : ∀ a, cx.keys.address[(ConstRef.member B 0 : ConstRef Address)]? = some a → a = B := fun a h =>
    ReadingKeys.resolve_inj auth (cx.keys.address_sound _ a h) hres
  cases hrole : cx.roles.names[(ConstRef.member B 0 : ConstRef Address)]? with
  | some k =>
    rw [Ctx.memberKey_of_role hrole]
    symm
    rw [Ctx.keyAt_eq_ok]
    simp [keyOfAddress, hres, hrole]
  | none =>
    have hkey : cx.addressOf (.member B 0) = .ok B := by
      unfold Ctx.addressOf
      cases ha : cx.keys.address[(ConstRef.member B 0 : ConstRef Address)]? with
      | some a => rw [haddr a ha]; rfl
      | none => simp [hsing, pure, Except.pure]
    unfold Ctx.memberKey
    rw [hrole]
    simp only [hkey, bind, Except.bind]
    unfold Ctx.keyAt
    cases hb : cx.keys.byAddress[B]? with
    | some k => rfl
    | none => simp [hres, hrole, Mode.addressId?]

/--
info: 'Ix.Cert.BlockContext.keyAt_stored' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keyAt_stored

end Ix.Cert.BlockContext
