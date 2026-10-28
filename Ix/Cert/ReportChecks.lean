import Ix.Cert.ClosureLayout
import Ix.CompileCert.ReaderIndex

/-! # The meanings of `compileReport`'s artifact checks

Three of `checkReport`'s checks constrain the artifact beyond what its records
say of themselves. Each meaning is stated here with the theorem that
`compileReport`'s result has it:

* **Blobs and records apart** (`BlobsApart`, `blobsApart`): no address holds
  both a stored blob and a stored record (`blobRecordCollision`).
* **Indexed recursors belong to their block's family** (`RecursorsOwned`,
  `recursorsOwned`): every input name published in an inductive block the
  artifact's recursor index attaches recursors to has a family, and each of
  those recursors is a published recursor of it (`unownedRecursor`). The index
  (`Ix.Kernel.Reader.buildIndex`) files a recursor under the block its type's
  first motive carrier names and keeps the first per motive in store order, so
  without the check a recursor record of another family could take the place
  of the block's own.
* **Bound roles' records have their kinds** (`RoleRecordKinds`,
  `roleRecordKinds`): under the default role table, the stored record at a
  bound `Nat` operation's address is a standalone definition and at a bound
  axiom role's address an axiom (`roleRecordKind`).

`RecursorsOwned` is stated over `Ix.Cert.ClosureLayout`'s published records
(`addrOf`, `blockAt`, `nameRecords`), and `ClosureLayout` imports the
statement, so the meanings come after both, here. The recursor check reads the
index over the stored records with a recursor member only
(`storedRecursorRecords`), which is the artifact's index (`recursorIndex_eq`),
and each record's block without its expressions (`recordBlock_eq`). -/

namespace Ix.Cert

open Ix.Cert.ClosureLayout (addrOf blockAt nameRecords)

/-! ## Blobs and records apart -/

/-- **Blobs and records are apart**: no address of `ixe` holds both a stored
blob and a stored record. Blobs and records share `Address.admissionHash`, so
without it a record's blob reference could name a record. -/
def BlobsApart (ixe : Ixon.Env) : Prop :=
  ∀ a, (ixe.blobs.get? a).isSome = true → (ixe.consts.get? a).isSome = true → False

/-- What `blobRecordCollision = none` says: blobs and records are apart. -/
theorem blobRecordCollision_none {ixe : Ixon.Env} (h : blobRecordCollision ixe = none) :
    BlobsApart ixe := by
  intro a hblob hrec
  unfold blobRecordCollision at h
  rw [List.findSome?_eq_none_iff] at h
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hblob
  have hmem : (a, b) ∈ ixe.blobs.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hb
  have found := h (a, b) hmem
  have hcon : ixe.consts.contains a = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?]
    exact hrec
  simp [hcon] at found

/-- **No address holds both a blob and a record**: when `compileReport`
returns, its environment's blobs and records are apart (`checkReport`'s
fourteenth check). -/
theorem blobsApart {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : BlobsApart ixe := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact blobRecordCollision_none (checkReport_ok hc).blobs

/-! ## Indexed recursors belong to their block's family -/

/-- The first inductive of the family of an input inductive, constructor or
recursor: its `all[0]`, its inductive's, or its `all[0]`'s. -/
def FamilyFirst (env : Ix.Environment) (x first : Ix.Name) : Prop :=
  (∃ iv, env.consts.get? x = some (.inductInfo iv) ∧ iv.all[0]? = some first) ∨
  (∃ cv iv, env.consts.get? x = some (.ctorInfo cv) ∧ env.consts.get? cv.induct = some (.inductInfo iv) ∧
    iv.all[0]? = some first) ∨
  (∃ rv i iv, env.consts.get? x = some (.recInfo rv) ∧ rv.all[0]? = some i ∧
    env.consts.get? i = some (.inductInfo iv) ∧ iv.all[0]? = some first)

/-- Every input name published in a block the artifact's recursor index files
recursors under (at the block or a projection of it) has a family, and every
recursor the index files there is a published recursor of that family. A
block's `Muts` entry is published at the block too; it is not an input name. -/
def RecursorsOwned (env : Ix.Environment) (ixe : Ixon.Env) : Prop :=
  ∀ (a : Address) (shape : Ix.Kernel.Reader.BlockShape), (artifactRecIndex ixe).blocks[a]? = some shape →
    ∀ (x : Ix.Name) (p : Address), env.consts.contains x = true → addrOf ixe x = some p → blockAt ixe p = a →
      ∃ first, FamilyFirst env x first ∧ ∀ r ∈ shape.recs, ∃ (rn : Ix.Name) (rv : Ix.RecursorVal),
        env.consts.get? rn = some (.recInfo rv) ∧ rv.all[0]? = some first ∧ r.block ∈ nameRecords ixe rn

/-- `forIn` over a filtered array, when the body keeps its state at every
element the filter drops. -/
theorem forIn_filter_skip {α σ : Type} (xs : Array α) (q : α → Bool) (init : σ)
    (f : α → σ → Id (ForInStep σ)) (hf : ∀ a s, q a = false → f a s = .yield s) :
    forIn (m := Id) (xs.filter q) init f = forIn (m := Id) xs init f := by
  rw [← Array.forIn_toList, ← Array.forIn_toList, Array.toList_filter]
  generalize xs.toList = l
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    cases hq : q a
    · simp only [Bool.false_eq_true, ↓reduceIte, List.forIn_cons, hf a init hq]
      exact ih init
    · simp only [↓reduceIte, List.forIn_cons]
      cases f a init with
      | done s => rfl
      | yield s => exact ih s

/-- The records `storedRecursorRecords` keeps: the stored records with a
recursor member, in order. -/
theorem storedRecursorRecords_eq (ixe : Ixon.Env) :
    storedRecursorRecords ixe =
      (storedRecords ixe).filter fun e => !(Ix.Kernel.Reader.recursorMembers e.2).isEmpty := by
  unfold storedRecursorRecords storedRecords
  rw [parMap_map, Array.filterMap_map, Array.filter_filterMap]
  congr 1
  funext e
  obtain ⟨a, lc⟩ := e
  simp only [Function.comp_apply, id_eq]
  cases lc.get? with
  | none => rfl
  | some c =>
    simp only [Option.map_some, Option.filter_some]
    cases h : (Ix.Kernel.Reader.recursorMembers c).isEmpty <;> simp_all

/-- **The check's recursor index is the artifact's**: `buildIndex` scans a
record only for its recursor members, so over the stored records with one it
builds the index it builds over all of them. -/
theorem recursorIndex_eq (ixe : Ixon.Env) :
    Ix.Kernel.Reader.buildIndex (storedRecord ixe) (storedRecursorRecords ixe) = artifactRecIndex ixe := by
  rw [storedRecursorRecords_eq]
  unfold artifactRecIndex
  rw [← Ix.CompileCert.ReaderIndex.run_eq, ← Ix.CompileCert.ReaderIndex.run_eq]
  unfold Ix.CompileCert.ReaderIndex.run
  rw [forIn_filter_skip]
  · rfl
  · intro e s hq
    have he : Ix.Kernel.Reader.recursorMembers e.2 = #[] := by simpa using hq
    unfold Ix.CompileCert.ReaderIndex.recordStep
    rw [he]
    rfl

/-- The check's block of a record, read without its expressions, is
`ClosureLayout`'s. -/
theorem recordBlock_eq (ixe : Ixon.Env) (a : Address) : recordBlock ixe a = blockAt ixe a := by
  unfold recordBlock blockAt
  rw [RefsRead.storedRefs_eq]
  have hr : recordAt ixe a = storedRecord ixe a := rfl
  rw [hr]
  cases storedRecord ixe a with
  | none => rfl
  | some c => exact Order.refOwner_eq a c

/-- The check's records of a name are `ClosureLayout`'s. -/
theorem publishedRecords_eq (ixe : Ixon.Env) (n : Ix.Name) : publishedRecords ixe n = nameRecords ixe n := by
  unfold publishedRecords nameRecords addrOf
  cases ixe.named.get? n with
  | none => rfl
  | some named => simp only [Option.map_some, recordBlock_eq]

/-- What `familyFirst?` finds is the family's first inductive. -/
theorem familyFirst_of {env : Ix.Environment} {x first : Ix.Name} (h : familyFirst? env x = some first) :
    FamilyFirst env x first := by
  unfold familyFirst? at h
  split at h
  · rename_i iv hx
    exact .inl ⟨iv, hx, h⟩
  · rename_i cv hx
    split at h
    · rename_i iv hi
      exact .inr (.inl ⟨cv, iv, hx, hi, h⟩)
    · cases h
  · rename_i rv hx
    split at h
    · rename_i i hi
      split at h
      · rename_i iv hiv
        exact .inr (.inr ⟨rv, i, iv, hx, hi, hiv, h⟩)
      · cases h
    · cases h
  · cases h

/-- `familyFirst?` reads the input only through its map, so names with one stored
hash agree on it. -/
theorem familyFirst?_congr {env : Ix.Environment} {k x : Ix.Name} (h : (k == x) = true) :
    familyFirst? env k = familyFirst? env x := by
  unfold familyFirst?
  rw [show env.consts.get? k = env.consts.get? x by
    simp only [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_congr h]

/-- A published name's entry, under the key the map stores: a name with its
stored hash. -/
theorem published_entry {ixe : Ixon.Env} {x : Ix.Name} {p : Address} (hp : addrOf ixe x = some p) :
    ∃ k named, (k, named) ∈ ixe.named.toList ∧ (k == x) = true ∧ named.addr = p := by
  unfold addrOf at hp
  obtain ⟨named, hnamed, rfl⟩ := Option.map_eq_some_iff.mp hp
  have hmem : x ∈ ixe.named := Std.HashMap.mem_iff_isSome_getElem?.mpr (by
    simp only [← Std.HashMap.get?_eq_getElem?, hnamed, Option.isSome_some])
  refine ⟨ixe.named.getKey x hmem, named, ?_, Std.HashMap.getKey_beq hmem, rfl⟩
  rw [Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some]
  refine ⟨?_, ?_⟩
  · rw [Std.HashMap.getKey?_congr (Std.HashMap.getKey_beq hmem)]
    exact Std.HashMap.getKey?_eq_some_getKey hmem
  · rw [Std.HashMap.getElem?_congr (Std.HashMap.getKey_beq hmem), ← Std.HashMap.get?_eq_getElem?]
    exact hnamed

/-- The check passed at every published entry. -/
theorem unownedRecursor_entry {env : Ix.Environment} {ixe : Ixon.Env} (h : unownedRecursor env ixe = none)
    {k : Ix.Name} {named : Ixon.Named} (hk : (k, named) ∈ ixe.named.toList) :
    unownedRecursorOf env ixe (Ix.Kernel.Reader.buildIndex (storedRecord ixe) (storedRecursorRecords ixe))
      (familyRecursors env) k named = none := by
  simp only [unownedRecursor, parMap_map, Array.findSome?_map, Array.findSome?_eq_none_iff,
    Function.comp_apply, id_eq, List.mem_toArray] at h
  exact h _ hk

/-- At a published input name in an indexed block, the check finds the name's
family, and each of the block's recursors owned by it. -/
theorem owns_of_entry {env : Ix.Environment} {ixe : Ixon.Env} {cands : Std.HashMap Address (Array Ix.Name)}
    {k : Ix.Name} {named : Ixon.Named} {a : Address} {shape : Ix.Kernel.Reader.BlockShape}
    (h : unownedRecursorOf env ixe (artifactRecIndex ixe) cands k named = none)
    (hk : env.consts.contains k = true) (hb : blockAt ixe named.addr = a)
    (hshape : (artifactRecIndex ixe).blocks[a]? = some shape) :
    ∃ first, familyFirst? env k = some first ∧
      ∀ r ∈ shape.recs, familyOwns env ixe cands first r.block = true := by
  unfold unownedRecursorOf at h
  rw [ite_eq_left hk, recordBlock_eq, hb, hshape] at h
  dsimp only at h
  cases hf : familyFirst? env k with
  | none => rw [hf] at h; cases h
  | some first =>
    rw [hf] at h
    simp only [Option.map_eq_none_iff, Array.find?_eq_none] at h
    exact ⟨first, rfl, fun r hr => by simpa using h r hr⟩

/-- What `familyOwns` finds: a published recursor of the family at the record. -/
theorem owned_of_owns {env : Ix.Environment} {ixe : Ixon.Env} {cands : Std.HashMap Address (Array Ix.Name)}
    {first : Ix.Name} {blk : Address} (h : familyOwns env ixe cands first blk = true) :
    ∃ (rn : Ix.Name) (rv : Ix.RecursorVal), env.consts.get? rn = some (.recInfo rv) ∧
      rv.all[0]? = some first ∧ blk ∈ nameRecords ixe rn := by
  unfold familyOwns at h
  obtain ⟨rn, -, hrn⟩ := Array.any_eq_true'.mp h
  unfold familyRecursorAt at hrn
  split at hrn
  · rename_i rv hget
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hrn
    rw [publishedRecords_eq] at hrn
    exact ⟨rn, rv, hget, hrn.1, hrn.2⟩
  · cases hrn

/-- What `unownedRecursor = none` says: every input name published in an indexed
block has a family, of which every indexed recursor there is a published
recursor. -/
theorem unownedRecursor_none {env : Ix.Environment} {ixe : Ixon.Env}
    (h : unownedRecursor env ixe = none) : RecursorsOwned env ixe := by
  intro a shape hshape x p hx hp hb
  obtain ⟨k, named, hk, hkx, rfl⟩ := published_entry hp
  have hck : env.consts.contains k = true := by
    rw [Std.HashMap.contains_congr hkx]
    exact hx
  have hentry := unownedRecursor_entry h hk
  rw [recursorIndex_eq] at hentry
  obtain ⟨first, hf, howns⟩ := owns_of_entry hentry hck hb hshape
  rw [familyFirst?_congr hkx] at hf
  exact ⟨first, familyFirst_of hf, fun r hr => owned_of_owns (howns r hr)⟩

/-- **Indexed recursors belong to their block's family**: when `compileReport`
returns, every input name published in an inductive block its artifact's
recursor index attaches recursors to has a family, and each of those recursors
is a published recursor of it (`checkReport`'s fifteenth check). -/
theorem recursorsOwned {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : RecursorsOwned env ixe := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact unownedRecursor_none (checkReport_ok hc).recursors

/-! ## Bound roles' records have their kinds -/

/-- **The stored record at a bound role's address has its specification's kind**,
under the default table: at a `Nat` operation's address (an `ops` specification)
a standalone definition, at an axiom role's address (`propext`,
`Classical.choice`, `sorryAx`) an axiom. Every other role, and an address the
artifact stores nothing at, is unconstrained. -/
def RoleRecordKinds (ixe : Ixon.Env) : Prop :=
  ∀ t, Ix.Kernel.Reader.defaultTable = .ok t →
    ∀ (r : Ix.Kernel.Role) (p : Address) (c : Ixon.Constant),
      t.addressOf? r = some p → (ixe.consts.get? p).bind (·.get?) = some c →
        ((Ix.Kernel.Role.spec (md := .anon) r).kind = .ops →
            ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn) ∧
        ((Ix.Kernel.Role.spec (md := .anon) r).kind = .axiom → ∃ ax : Ixon.Axiom, c.info = .axio ax)

/-- A role `addressOf?` binds is among the table's bound entries: it reads the
first bound entry of the role. -/
theorem bound_of_addressOf {t : Ix.Kernel.RoleTable} {r : Ix.Kernel.Role} {p : Address}
    (hp : t.addressOf? r = some p) : (r, p) ∈ t.bound.toList := by
  unfold Ix.Kernel.RoleTable.addressOf? at hp
  obtain ⟨⟨r', p'⟩, hfind, hpp⟩ := Option.map_eq_some_iff.mp hp
  have hr : r' = r := by simpa using Array.find?_some hfind
  have hp' : p' = p := hpp
  subst hr hp'
  exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)

/-- `roleKind` is the kind of the role's specification. -/
theorem roleKind_eq (r : Ix.Kernel.Role) : roleKind r = (Ix.Kernel.Role.spec (md := .anon) r).kind := by
  cases r <;> rfl

/-- The kinds `roleRecordKindOk` accepts. -/
theorem roleRecordKindOk_spec {r : Ix.Kernel.Role} {c : Ixon.Constant} (hok : roleRecordKindOk r c = true) :
    ((Ix.Kernel.Role.spec (md := .anon) r).kind = .ops →
        ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn) ∧
    ((Ix.Kernel.Role.spec (md := .anon) r).kind = .axiom → ∃ ax : Ixon.Axiom, c.info = .axio ax) := by
  unfold roleRecordKindOk at hok
  rw [roleKind_eq] at hok
  refine ⟨fun hops => ?_, fun hax => ?_⟩
  · rw [hops] at hok
    cases hci : c.info with
    | defn d =>
      rw [hci] at hok
      exact ⟨d, rfl, of_decide_eq_true hok⟩
    | _ => rw [hci] at hok; cases hok
  · rw [hax] at hok
    cases hci : c.info with
    | axio ax => exact ⟨ax, rfl⟩
    | _ => rw [hci] at hok; cases hok

/-- The check's bound entries are the decoded default table's. -/
theorem roleTableBound_eq {t : Ix.Kernel.RoleTable} (ht : Ix.Kernel.Reader.defaultTable = .ok t) :
    roleTableBound = t.bound := by
  unfold Ix.Kernel.Reader.defaultTable at ht
  unfold roleTableBound
  generalize Ix.Kernel.Reader.defaultTableBytes = bytes at ht ⊢
  cases bytes with
  | error e => simp [bind, Except.bind] at ht
  | ok bs =>
    simp only [bind, Except.bind] at ht
    show ((Ix.Kernel.RoleTable.ofBytes bs).map (·.bound)).getD #[] = t.bound
    cases hob : Ix.Kernel.RoleTable.ofBytes bs with
    | none =>
      rw [hob] at ht
      simp [throw, throwThe, MonadExceptOf.throw] at ht
    | some t' =>
      rw [hob] at ht
      cases hc : t'.check with
      | error e => simp [hc, Except.mapError] at ht
      | ok u =>
        simp [hc, Except.mapError, pure, Except.pure] at ht
        subst ht
        rfl

/-- The addresses of bound entries hold each entry's address. -/
theorem roleAddrs_of {bound : Array (Ix.Kernel.Role × Address)} {r : Ix.Kernel.Role} {p : Address}
    (hmem : (r, p) ∈ bound.toList) : (roleAddrs bound).contains p = true := by
  unfold roleAddrs
  rw [Std.HashSet.contains_ofList]
  exact List.elem_iff.mpr (List.mem_map.mpr ⟨(r, p), hmem, rfl⟩)

/-- Where `roleRecordKindAt` finds nothing, every role of the entries bound to the
address accepts the record. -/
theorem roleRecordKindAt_none {bound : Array (Ix.Kernel.Role × Address)} {r : Ix.Kernel.Role}
    {p : Address} {c : Ixon.Constant} (hmem : (r, p) ∈ bound.toList)
    (h : roleRecordKindAt bound p c = none) : roleRecordKindOk r c = true := by
  unfold roleRecordKindAt at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  simpa using h (r, p) hmem

/-- The check passed at every stored record at an address the decoded default
table binds. -/
theorem roleRecordKind_entry {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable} (h : roleRecordKind ixe = none)
    (ht : Ix.Kernel.Reader.defaultTable = .ok t) {r : Ix.Kernel.Role} {p : Address} {c : Ixon.Constant}
    (hmem : (r, p) ∈ t.bound.toList) (hc : storedRecord ixe p = some c) : roleRecordKindOk r c = true := by
  obtain ⟨lc, hlc, hget⟩ : ∃ lc, ixe.consts.get? p = some lc ∧ lc.get? = some c := by
    unfold storedRecord at hc
    cases hl : ixe.consts.get? p with
    | none => rw [hl] at hc; cases hc
    | some lc => rw [hl] at hc; exact ⟨lc, rfl, hc⟩
  have hin : (p, lc) ∈ ixe.consts.toList := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hlc
  simp only [roleRecordKind, List.findSome?_eq_none_iff] at h
  have found := h (p, lc) hin
  dsimp only at found
  rw [roleTableBound_eq ht, ite_eq_left (roleAddrs_of hmem), hget] at found
  simp only [Option.map_eq_none_iff] at found
  exact roleRecordKindAt_none hmem found

/-- What `roleRecordKind = none` says: every bound role's stored record has its
specification's kind. -/
theorem roleRecordKind_none {ixe : Ixon.Env} (h : roleRecordKind ixe = none) : RoleRecordKinds ixe :=
  fun _ ht _ _ _ hp hc => roleRecordKindOk_spec (roleRecordKind_entry h ht (bound_of_addressOf hp) hc)

/-- **Bound roles' records have their kinds**: when `compileReport` returns, under
the default role table the stored record at a bound `Nat` operation's address is
a standalone definition and at a bound axiom role's address an axiom
(`checkReport`'s sixteenth check). -/
theorem roleRecordKinds {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : RoleRecordKinds ixe := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact roleRecordKind_none (checkReport_ok hc).roles

end Ix.Cert
