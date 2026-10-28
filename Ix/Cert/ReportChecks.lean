import Ix.Cert.ClosureLayout
import Ix.CompileCert.ReaderIndex
import Ix.RoleEvidence

/-! # The meanings of `compileReport`'s artifact checks

Four of `checkReport`'s checks constrain the artifact beyond what its records
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
* **Literal-support roles are named** (`LiteralRolesNamed`, `literalRolesNamed`):
  under the default role table, a role a stored record's literal is checked
  against (the `Nat` basis, and the string support for a `String` literal) whose
  address the artifact stores a record at is an input constant published at that
  address (`literalRoleUnnamed`).

Six more constrain the input's inductive families to the shapes Lean gives them, so that
quotient Source's reading of a family by its names and the Ixon reader's reading of the
compiled records by their types and positions agree (section "Inductive inputs have Lean's
shapes"): `FamilyNamesStored`, `ConstructorIndices`, `FamilyLevelParams`, `FamilyBlocks`, `RecursorSlotsUnique`
and `RecursorShapes`.

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


/-! ## Literal-support roles are named -/

/-- The input name `literalSupport` gives a literal-support role (`supportNames`'s spelling). -/
def literalRoleName (s : Ix.Kernel.Role) : Ix.Name :=
  Ix.Name.fromLeanName (Ix.RoleEvidence.toLeanName (Ix.Kernel.Key.role s : Ix.Kernel.Key .source))

/-- The check's written-out names are `literalRoleName`'s, on the literal-support roles. -/
theorem literalRoleName_eq {s : Ix.Kernel.Role} (hs : s ∈ literalSupportRoles) :
    literalRoleName s = literalRoleIxName s := by
  simp only [literalSupportRoles, List.mem_cons, List.not_mem_nil, or_false] at hs
  unfold literalRoleName literalRoleIxName
  congr 1
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **A literal's stored support role's record is its name's**, under the default role
table: when a stored record holds a literal and the artifact stores a record at the
address of a role that literal is checked against (`literalRoles`: the `Nat` basis for a
`Nat` literal, with the string support for a `String` literal), that role's name is an
input constant published at that address. A support role no stored literal is checked
against, every other address, and every unbound role are unconstrained: an artifact whose
records hold no literal may store an α-copy of `Nat` at `Nat`'s address. -/
def LiteralRolesNamed (env : Ix.Environment) (ixe : Ixon.Env) : Prop :=
  ∀ t, Ix.Kernel.Reader.defaultTable = .ok t →
    ∀ (a : Address) (c : Ixon.Constant), recordAt ixe a = some c →
      ∀ s ∈ literalRoles c, ∀ b, t.addressOf? s = some b → ixe.consts.contains b = true →
        env.consts.contains (literalRoleName s) = true ∧ addrOf ixe (literalRoleName s) = some b

/-- The check's roles are the literal-support roles of `strLitSupportNames`. -/
theorem keyRoles_strLitSupportNames :
    keyRoles (Ix.Kernel.Reader.strLitSupportNames : List (Ix.Kernel.Key .anon)) = literalSupportRoles :=
  rfl

/-- The check's `Nat` roles are the roles of `natLitSupportNames`. -/
theorem keyRoles_natLitSupportNames :
    keyRoles (Ix.Kernel.Reader.natLitSupportNames : List (Ix.Kernel.Key .anon)) = natLiteralRoles :=
  rfl

/-- A stored record's literal kinds are among the stored records' (`storedLiteralKinds`). -/
theorem storedLiteralKinds_of {ixe : Ixon.Env} {a : Address} {c : Ixon.Constant}
    (hc : recordAt ixe a = some c) :
    ((Ix.Kernel.Reader.literalKinds c).1 = true → (storedLiteralKinds ixe).1 = true) ∧
    ((Ix.Kernel.Reader.literalKinds c).2 = true → (storedLiteralKinds ixe).2 = true) := by
  obtain ⟨lc, hlc, hget⟩ : ∃ lc, ixe.consts.get? a = some lc ∧ lc.get? = some c := by
    unfold recordAt at hc
    cases hl : ixe.consts.get? a with
    | none => rw [hl] at hc; cases hc
    | some lc => rw [hl] at hc; exact ⟨lc, rfl, hc⟩
  have hin : (a, lc) ∈ ixe.consts.toArray := by
    rw [Std.HashMap.mem_toArray_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hlc
  unfold storedLiteralKinds
  simp only [parMap_map, Array.any_map]
  refine ⟨fun h1 => Array.any_eq_true'.mpr ⟨(a, lc), hin, ?_⟩,
    fun h2 => Array.any_eq_true'.mpr ⟨(a, lc), hin, ?_⟩⟩
  · simp only [Function.comp_apply, hget]
    exact h1
  · simp only [Function.comp_apply, hget]
    exact h2

/-- A stored record's literals are checked against roles among `storedLiteralRoles`. -/
theorem literalRoles_stored {ixe : Ixon.Env} {a : Address} {c : Ixon.Constant}
    (hc : recordAt ixe a = some c) {s : Ix.Kernel.Role} (hs : s ∈ literalRoles c) :
    s ∈ storedLiteralRoles ixe := by
  obtain ⟨k1, k2⟩ := storedLiteralKinds_of hc
  unfold literalRoles at hs
  unfold storedLiteralRoles
  dsimp only at hs ⊢
  cases hs2 : (Ix.Kernel.Reader.literalKinds c).2
  · cases hs1 : (Ix.Kernel.Reader.literalKinds c).1
    · simp [hs2, hs1, keyRoles] at hs
    · simp only [hs2, hs1, Bool.false_eq_true, ↓reduceIte, keyRoles_natLitSupportNames] at hs
      rw [k1 hs1]
      cases (storedLiteralKinds ixe).2
      · exact hs
      · simp only [natLiteralRoles, List.mem_cons, List.not_mem_nil, or_false] at hs
        simp only [↓reduceIte, literalSupportRoles, List.mem_cons]
        rcases hs with rfl | rfl | rfl <;> simp
  · simp only [hs2, ↓reduceIte, keyRoles_strLitSupportNames] at hs
    rw [k2 hs2]
    exact hs

/-- A role a stored literal is checked against is a literal-support role. -/
theorem literalRoles_support {c : Ixon.Constant} {s : Ix.Kernel.Role} (hs : s ∈ literalRoles c) :
    s ∈ literalSupportRoles := by
  unfold literalRoles at hs
  dsimp only at hs
  split at hs
  · rwa [keyRoles_strLitSupportNames] at hs
  · split at hs
    · rw [keyRoles_natLitSupportNames] at hs
      simp only [natLiteralRoles, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl <;> simp [literalSupportRoles]
    · simp [keyRoles] at hs

/-- What `literalRoleUnnamed = none` says: every stored support role of a stored literal
is published under the role's name. -/
theorem literalRoleUnnamed_none {env : Ix.Environment} {ixe : Ixon.Env}
    (h : literalRoleUnnamed env ixe = none) : LiteralRolesNamed env ixe := by
  intro t ht a c hc s hs b hb hcb
  have hmem : (s, b) ∈ roleTableBound.toList := by
    rw [roleTableBound_eq ht]
    exact bound_of_addressOf hb
  have hsL := literalRoles_support hs
  have hrole : literalSupportRoles.contains s = true := List.elem_iff.mpr hsL
  rw [literalRoleName_eq hsL]
  by_contra hne
  have hpub : (env.consts.contains (literalRoleIxName s) &&
      (ixe.named.get? (literalRoleIxName s)).map (·.addr) == some b) = false := by
    cases hx : env.consts.contains (literalRoleIxName s)
    · rfl
    · cases hy : ((ixe.named.get? (literalRoleIxName s)).map (·.addr) == some b)
      · rfl
      · exact (hne ⟨hx, beq_iff_eq.mp hy⟩).elim
  have hin : (s, b) ∈ roleTableBound.toList.filter (fun (e : Ix.Kernel.Role × Address) =>
      literalSupportRoles.contains e.1 && ixe.consts.contains e.2 &&
        !(env.consts.contains (literalRoleIxName e.1) &&
          (ixe.named.get? (literalRoleIxName e.1)).map (·.addr) == some e.2)) := by
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    simp only [hrole, hcb, hpub, Bool.not_false, Bool.and_self]
  have hstored : (storedLiteralRoles ixe).contains s = true :=
    List.elem_iff.mpr (literalRoles_stored hc hs)
  unfold literalRoleUnnamed at h
  dsimp only at h
  split at h
  · rename_i hempty
    rw [List.isEmpty_iff] at hempty
    rw [hempty] at hin
    cases hin
  · rw [List.find?_eq_none] at h
    exact absurd hstored (by simpa using h (s, b) hin)

/-- **Literal-support roles are named**: when `compileReport` returns, under the default
role table every support role of a stored literal whose address the artifact stores a
record at is an input constant published at that address (`checkReport`'s seventeenth
check). -/
theorem literalRolesNamed {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : LiteralRolesNamed env ixe := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact literalRoleUnnamed_none (checkReport_ok hc).literals


/-! ## Inductive inputs have Lean's shapes

The compiler copies an inductive family's declarations as Lean gives them, while quotient
Source reads a family by its names and the Ixon reader reads the compiled records by their
types and positions. Six meanings pin the input to the shapes Lean produces, so that the two
readings agree; `checkReport` decides them (`unstoredFamilyName`, `misplacedConstructor`,
`strayLevelParams`, `strayFamilyMember`, `recursorShapeError`) and refuses with one message
prefix ("inductive input check failed"):

* **Family names** (`FamilyNamesStored`): every name an input family lists is an input
  constant's own name. `Ix.Name`'s `==` compares stored hashes only.

* **Constructor indices** (`ConstructorIndices`): the `j`-th constructor of an input inductive
  declares index `j`. The compiler stores the declared index and addresses the constructor by
  its position.
* **Level parameters** (`FamilyLevelParams`): a family's members and constructors have the
  inductive's level-parameter names, and recursors with one `all[0]` have one list, of the
  family's length or one more. The compiler compiles a constructor's type under its
  inductive's names.
* **Family blocks** (`FamilyBlocks`): a block of the compile's condensation that holds a family
  member is exactly that family's types and constructors, or exactly its recursors, each with
  its family's `all`; and a family has fewer than `2 ^ 63` members and auxiliary motives.
* **Recursor slots** (`RecursorSlotsUnique`): every stored recursor member is filed by the
  recursor index, at a slot of its own.
* **Recursor shapes** (`RecursorShapes`): every published input family recursor is filed at
  its family's block and the motive its name gives it, its first carriers the block's members
  in order, its major premise an inductive whose constructors are its rules'. -/

/-- **Every input inductive's `j`-th constructor declares index `j`.** -/
def ConstructorIndices (env : Ix.Environment) : Prop :=
  ∀ (n : Ix.Name) (iv : Ix.InductiveVal), env.consts.get? n = some (.inductInfo iv) →
    ∀ (j : Nat) (hj : j < iv.ctors.size) (cv : Ix.ConstructorVal),
      env.consts.get? iv.ctors[j] = some (.ctorInfo cv) → cv.cidx = j

/-- What `misplacedConstructor = none` says: constructor indices are positions. -/
theorem misplacedConstructor_none {env : Ix.Environment} (h : misplacedConstructor env = none) :
    ConstructorIndices env := by
  intro n iv hn j hj cv hcv
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hn
  obtain ⟨k, -, hmem⟩ := hn
  unfold misplacedConstructor at h
  rw [List.findSome?_eq_none_iff] at h
  have hfind := h (k, .inductInfo iv) hmem
  dsimp only at hfind
  rw [Option.map_eq_none_iff, List.find?_eq_none] at hfind
  have hz : (iv.ctors[j], j) ∈ iv.ctors.toList.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [hj]
  have hj' := hfind _ hz
  dsimp only at hj'
  rw [hcv] at hj'
  simpa using hj'

/-- **Constructor indices are positions**: when `compileReport` returns, every input
inductive's `j`-th constructor declares index `j`. -/
theorem constructorIndices {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : ConstructorIndices env := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact misplacedConstructor_none (checkReport_ok hc).constructorIndices

/-- `namesEq` is equality. -/
theorem namesEq_iff {a b : Array Ix.Name} : namesEq a b = true ↔ a = b :=
  @beq_iff_eq (Array Ix.LeanIngress.TableName) _ _ a b

/-- **A family shares its level-parameter names**: every member an input inductive lists and
every constructor it lists have its names; recursors of one family (one `all[0]`) have one
list, of the family's length or one more. -/
def FamilyLevelParams (env : Ix.Environment) : Prop :=
  (∀ n iv, env.consts.get? n = some (.inductInfo iv) →
    (∀ m ∈ iv.all, ∀ iv', env.consts.get? m = some (.inductInfo iv') →
      iv'.cnst.levelParams = iv.cnst.levelParams) ∧
    (∀ c ∈ iv.ctors, ∀ cv, env.consts.get? c = some (.ctorInfo cv) →
      cv.cnst.levelParams = iv.cnst.levelParams)) ∧
  (∀ x y rx ry first, env.consts.get? x = some (.recInfo rx) → env.consts.get? y = some (.recInfo ry) →
    rx.all[0]? = some first → ry.all[0]? = some first → rx.cnst.levelParams = ry.cnst.levelParams) ∧
  ∀ x rx first iv, env.consts.get? x = some (.recInfo rx) → rx.all[0]? = some first →
    env.consts.get? first = some (.inductInfo iv) →
    rx.cnst.levelParams.size = iv.cnst.levelParams.size ∨ rx.cnst.levelParams.size = iv.cnst.levelParams.size + 1

/-- At an input recursor, the level-parameter check found the first list filed for its
family (`recursorLevelParams`), and it is the recursor's; and the recursor's count is its
family's or one more (`recursorLevelCountOk`). -/
theorem strayLevelParams_recursor {env : Ix.Environment} (h : strayLevelParams env = none)
    {x : Ix.Name} {rx : Ix.RecursorVal} {first : Ix.Name} (hx : env.consts.get? x = some (.recInfo rx))
    (hf : rx.all[0]? = some first) :
    ((recursorLevelParams env).get? first).any (namesEq · rx.cnst.levelParams) = true ∧
      recursorLevelCountOk env first rx = true := by
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hx
  obtain ⟨k, -, hmem⟩ := hx
  unfold strayLevelParams at h
  dsimp only at h
  rw [List.findSome?_eq_none_iff] at h
  have hk := h (k, .recInfo rx) hmem
  dsimp only at hk
  split at hk
  · rename_i first' hf'
    have e : some first = some first' := hf.symm.trans hf'
    cases e
    split at hk
    · rename_i hany
      rw [Bool.and_eq_true] at hany
      exact hany
    · cases hk
  · rename_i hf'
    have e : some first = none := hf.symm.trans hf'
    cases e

/-- What `strayLevelParams = none` says: a family shares its level-parameter names. -/
theorem strayLevelParams_none {env : Ix.Environment} (h : strayLevelParams env = none) :
    FamilyLevelParams env := by
  refine ⟨fun n iv hn => ?_, fun x y rx ry first hx hy hfx hfy => ?_,
    fun x rx first iv hx hf hiv => ?_⟩
  · rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hn
    obtain ⟨k, -, hmem⟩ := hn
    unfold strayLevelParams at h
    dsimp only at h
    rw [List.findSome?_eq_none_iff] at h
    have hk := h (k, .inductInfo iv) hmem
    dsimp only at hk
    split at hk
    · cases hk
    · rename_i hall
      rw [Array.find?_eq_none] at hall hk
      refine ⟨fun m hm iv' hiv' => ?_, fun c hc cv hcv => ?_⟩
      · have := hall m hm
        rw [hiv'] at this
        simpa [namesEq_iff] using this
      · have := hk c hc
        rw [hcv] at this
        simpa [namesEq_iff] using this
  · have h₁ := (strayLevelParams_recursor h hx hfx).1
    have h₂ := (strayLevelParams_recursor h hy hfy).1
    cases hl : (recursorLevelParams env).get? first with
    | none => rw [hl] at h₁; cases h₁
    | some lps =>
      rw [hl] at h₁ h₂
      simp only [Option.any_some, namesEq_iff] at h₁ h₂
      exact h₁.symm.trans h₂
  · have hc := (strayLevelParams_recursor h hx hf).2
    unfold recursorLevelCountOk at hc
    rw [hiv] at hc
    simpa using hc

/-- **A family shares its level-parameter names**: when `compileReport` returns, every member
and constructor an input inductive lists has its level-parameter names, and recursors with one
`all[0]` have one list. -/
theorem familyLevelParams {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : FamilyLevelParams env := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact strayLevelParams_none (checkReport_ok hc).levelParams

/-- **Every name an input family lists is an input constant's own name** (`familyNamesOf`:
an inductive's `all` and constructors, a constructor's inductive, a recursor's `all` and its
rules' constructors). `Ix.Name`'s `==` compares stored hashes only; with this, a lookup by a
family name lands at that exact name. -/
def FamilyNamesStored (env : Ix.Environment) : Prop :=
  ∀ n ci, (n, ci) ∈ env.consts.toList → ∀ a ∈ familyNamesOf ci, ∃ ci', (a, ci') ∈ env.consts.toList

/-- What `unstoredFamilyName = none` says, with the input constants named as they are stored
(`misnamedInput`): family names are input keys exactly. -/
theorem unstoredFamilyName_none {env : Ix.Environment} (h : unstoredFamilyName env = none)
    (named : misnamedInput env = none) : FamilyNamesStored env := by
  intro n ci hmem a ha
  unfold unstoredFamilyName at h
  rw [List.findSome?_eq_none_iff] at h
  have hn := h (n, ci) hmem
  dsimp only at hn
  rw [Option.map_eq_none_iff, List.find?_eq_none] at hn
  have hany : ((env.consts.get? a).any fun ci' => Ix.nameCompareExact ci'.getCnst.name a == .eq) = true := by
    simpa using hn a ha
  obtain ⟨ci', hget, heq⟩ := (Option.any_eq_true _ _).mp hany
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hget
  obtain ⟨k, -, hk⟩ := hget
  have hname : ci'.getCnst.name = k := misnamedInput_none named k ci' hk
  have hexact : ci'.getCnst.name = a := Ix.CompileCert.Canon.nameCompareExact_eq_iff.mp (beq_iff_eq.mp heq)
  rw [← hname, hexact] at hk
  exact ⟨ci', hk⟩

/-- **Family names are input keys**: when `compileReport` returns, every name an input family
lists is an input constant's own name. -/
theorem familyNamesStored {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : FamilyNamesStored env := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact unstoredFamilyName_none (checkReport_ok hc).familyNames (checkReport_ok hc).named

/-- `x` is a type or constructor of the family whose Lean block is `block`: a name the block
lists, or a constructor that an inductive it lists has. -/
def InFamily (env : Ix.Environment) (block : Array Ix.Name) (x : Ix.Name) : Prop :=
  (∃ n ∈ block, (n == x) = true) ∨
    ∃ n ∈ block, ∃ iv, env.consts.get? n = some (.inductInfo iv) ∧ ∃ c ∈ iv.ctors, (c == x) = true

/-- `x` is an input recursor whose block's first member is `first`. -/
def InRecursors (env : Ix.Environment) (first x : Ix.Name) : Prop :=
  ∃ rv, env.consts.get? x = some (.recInfo rv) ∧ rv.all[0]? = some first

/-- **Every block of the compile's condensation that holds a family member is one family's.**
A block that holds an inductive holds exactly its family's types and constructors (its `all`,
and their constructors). So does a block that holds a constructor, for the constructor's
inductive, which must be an input inductive. A block that holds a recursor holds exactly the
input recursors with that recursor's `all[0]`, which must be an input inductive whose `all` is
the recursor's and whose family has fewer than `2 ^ 63` members and auxiliary motives, so its
recursors' positions fit the compiled records' 64-bit fields. -/
def FamilyBlocks (env : Ix.Environment) : Prop :=
  ∀ rep all, (compileBlocks env).blocks.get? rep = some all → ∀ y, all.contains y = true →
    (∀ iv, env.consts.get? y = some (.inductInfo iv) →
      ∀ x, all.contains x = true ↔ InFamily env iv.all x) ∧
    (∀ cv, env.consts.get? y = some (.ctorInfo cv) → ∃ iv, env.consts.get? cv.induct = some (.inductInfo iv) ∧
      ∀ x, all.contains x = true ↔ InFamily env iv.all x) ∧
    (∀ rv, env.consts.get? y = some (.recInfo rv) → ∃ first iv, rv.all[0]? = some first ∧
      env.consts.get? first = some (.inductInfo iv) ∧ rv.all = iv.all ∧
      iv.all.size + iv.numNested < 2 ^ 63 ∧ ∀ x, all.contains x = true ↔ InRecursors env first x)

/-- A name a hash set contains is `==` to one of its listed keys. -/
theorem set_key {s : Ix.Set Ix.Name} {x : Ix.Name} (h : s.contains x = true) :
    ∃ k ∈ s.toList, (x == k) = true := by
  rw [← Std.HashSet.contains_toList] at h
  exact List.contains_iff_exists_mem_beq.mp h

/-- What `sameNames` checks: the set holds exactly the names `==` to one of `names`. -/
theorem sameNames_spec {all : Ix.Set Ix.Name} {names : Array Ix.Name} (h : sameNames all names = true) :
    ∀ x, all.contains x = true ↔ ∃ n ∈ names, (n == x) = true := by
  unfold sameNames at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk, hxk⟩ := set_key hx
    have hset := List.all_eq_true.mp h₁ k hk
    rw [Std.HashSet.contains_ofList] at hset
    obtain ⟨n, hn, hkn⟩ := List.contains_iff_exists_mem_beq.mp hset
    exact ⟨n, Array.mem_toList_iff.mp hn, BEq.symm (BEq.trans hxk hkn)⟩
  · rintro ⟨n, hn, hnx⟩
    have hc := Array.all_eq_true'.mp h₂ n hn
    rwa [Std.HashSet.contains_congr hnx] at hc

/-- The names `familyNames` lists are the family's types and constructors. -/
theorem familyNames_spec (env : Ix.Environment) (block : Array Ix.Name) (x : Ix.Name) :
    (∃ n ∈ familyNames env block, (n == x) = true) ↔ InFamily env block x := by
  unfold familyNames InFamily
  constructor
  · rintro ⟨n, hn, hnx⟩
    rcases Array.mem_append.mp hn with hb | hc
    · exact .inl ⟨n, hb, hnx⟩
    · obtain ⟨m, hm, hnm⟩ := Array.mem_flatMap.mp hc
      split at hnm
      · rename_i iv hiv
        exact .inr ⟨m, hm, iv, hiv, n, hnm, hnx⟩
      · simp at hnm
  · rintro (⟨n, hn, hnx⟩ | ⟨m, hm, iv, hiv, c, hc, hcx⟩)
    · exact ⟨n, Array.mem_append_left _ hn, hnx⟩
    · refine ⟨c, Array.mem_append_right _ (Array.mem_flatMap.mpr ⟨m, hm, ?_⟩), hcx⟩
      rw [hiv]
      exact hc

/-- `familyRecursors`' fold keeps what it has filed. -/
theorem familyRecursors_mono (l : List (Ix.Name × Ix.ConstantInfo))
    (m : Std.HashMap Address (Array Ix.Name)) (key : Address) (x : Ix.Name) (hx : x ∈ m.getD key #[]) :
    x ∈ (l.foldl (fun a b => familyRecursorsStep a b.1 b.2) m).getD key #[] := by
  induction l generalizing m with
  | nil => exact hx
  | cons e l ih =>
    rw [List.foldl_cons]
    apply ih
    obtain ⟨n, ci⟩ := e
    show x ∈ (familyRecursorsStep m n ci).getD key #[]
    unfold familyRecursorsStep
    split
    · split
      · rename_i first _
        rw [Std.HashMap.getD_insert]
        split
        · rename_i hkey
          have hk : first.getHash = key := beq_iff_eq.mp hkey
          subst hk
          exact Array.mem_push_of_mem _ hx
        · exact hx
      · exact hx
    · exact hx

/-- `familyRecursors` files every input recursor under its `all[0]`'s hash. -/
theorem familyRecursors_mem {env : Ix.Environment} {k : Ix.Name} {rv : Ix.RecursorVal} {first : Ix.Name}
    (hk : (k, .recInfo rv) ∈ env.consts.toList) (hf : rv.all[0]? = some first) :
    k ∈ (familyRecursors env).getD first.getHash #[] := by
  unfold familyRecursors
  rw [Std.HashMap.fold_eq_foldl_toList]
  suffices h : ∀ (l : List (Ix.Name × Ix.ConstantInfo)), (k, .recInfo rv) ∈ l →
      ∀ m₀ : Std.HashMap Address (Array Ix.Name),
        k ∈ (l.foldl (fun a b => familyRecursorsStep a b.1 b.2) m₀).getD first.getHash #[] from h _ hk _
  intro l
  induction l with
  | nil => intro hk; cases hk
  | cons e l ih =>
    intro hk m₀
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hk with rfl | hl
    · apply familyRecursors_mono
      show k ∈ (familyRecursorsStep m₀ k (.recInfo rv)).getD first.getHash #[]
      simp [familyRecursorsStep, hf]
    · exact ih hl _

/-- `familyBlockOk` reads its member only through the input's map. -/
theorem familyBlockOk_congr {env : Ix.Environment} {recs : Std.HashMap Address (Array Ix.Name)}
    {all : Ix.Set Ix.Name} {k y : Ix.Name} (h : (k == y) = true) :
    familyBlockOk env recs all k = familyBlockOk env recs all y := by
  unfold familyBlockOk
  rw [show env.consts.get? k = env.consts.get? y by
    simp only [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_congr h]

/-- `familySized` is the size bound. -/
theorem familySized_iff {iv : Ix.InductiveVal} : familySized iv = true ↔ iv.all.size + iv.numNested < 2 ^ 63 := by
  unfold familySized
  exact decide_eq_true_iff

/-- What `familyBlockOk` checks of a member of a block: its family's clause of `FamilyBlocks`. -/
theorem familyBlockOk_spec {env : Ix.Environment} {all : Ix.Set Ix.Name} {y : Ix.Name}
    (h : familyBlockOk env (familyRecursors env) all y = true) :
    (∀ iv, env.consts.get? y = some (.inductInfo iv) →
      ∀ x, all.contains x = true ↔ InFamily env iv.all x) ∧
    (∀ cv, env.consts.get? y = some (.ctorInfo cv) → ∃ iv, env.consts.get? cv.induct = some (.inductInfo iv) ∧
      ∀ x, all.contains x = true ↔ InFamily env iv.all x) ∧
    (∀ rv, env.consts.get? y = some (.recInfo rv) → ∃ first iv, rv.all[0]? = some first ∧
      env.consts.get? first = some (.inductInfo iv) ∧ rv.all = iv.all ∧
      iv.all.size + iv.numNested < 2 ^ 63 ∧ ∀ x, all.contains x = true ↔ InRecursors env first x) := by
  have family : ∀ iv : Ix.InductiveVal, sameNames all (familyNames env iv.all) = true →
      ∀ x, all.contains x = true ↔ InFamily env iv.all x := by
    intro iv hiv x
    rw [sameNames_spec hiv x, familyNames_spec]
  refine ⟨fun iv hiv => ?_, fun cv hcv => ?_, fun rv hrv => ?_⟩
  · unfold familyBlockOk at h
    rw [hiv] at h
    exact family iv h
  · unfold familyBlockOk at h
    rw [hcv] at h
    dsimp only at h
    split at h
    · rename_i iv hiv
      exact ⟨iv, hiv, family iv h⟩
    · cases h
  · unfold familyBlockOk at h
    rw [hrv] at h
    dsimp only at h
    split at h
    · rename_i first hfirst
      split at h
      · rename_i iv hiv
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨hall, hsized⟩, hmembers⟩, hrecs⟩ := h
        refine ⟨first, iv, hfirst, hiv, namesEq_iff.mp hall, familySized_iff.mp hsized, fun x => ⟨fun hx => ?_, ?_⟩⟩
        · unfold InRecursors
          obtain ⟨k, hk, hxk⟩ := set_key hx
          have hm := List.all_eq_true.mp hmembers k hk
          have hget : env.consts.get? x = env.consts.get? k := by
            simp only [Std.HashMap.get?_eq_getElem?]
            exact Std.HashMap.getElem?_congr hxk
          rw [← hget] at hm
          split at hm
          · rename_i rx hrx
            refine ⟨rx, hrx, ?_⟩
            obtain ⟨f, hf, hbeq⟩ := Option.any_eq_true _ _ |>.mp hm
            rw [hf, Ix.Name.beqRaw_iff.mp hbeq]
          · cases hm
        · intro hx
          unfold InRecursors at hx
          obtain ⟨rx, hrx, hfx⟩ := hx
          rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hrx
          obtain ⟨k, hxk, hmem⟩ := hrx
          have hk := familyRecursors_mem hmem hfx
          have hc := Array.all_eq_true'.mp hrecs k hk
          rwa [Std.HashSet.contains_congr (BEq.symm hxk)] at hc
      · cases h
    · cases h

/-- The family check passed at every member of every block of `blocks`. -/
theorem strayFamilyMember_member {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    (h : strayFamilyMember env blocks = none) :
    ∀ rep all, blocks.blocks.get? rep = some all → ∀ y, all.contains y = true →
      familyBlockOk env (familyRecursors env) all y = true := by
  intro rep all hall y hy
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hall
  obtain ⟨rep', -, hmem⟩ := hall
  unfold strayFamilyMember at h
  dsimp only at h
  rw [List.findSome?_eq_none_iff] at h
  have hb := h (rep', all) hmem
  dsimp only at hb
  rw [Option.map_eq_none_iff, List.find?_eq_none] at hb
  obtain ⟨k, hk, hyk⟩ := set_key hy
  have hk' : familyBlockOk env (familyRecursors env) all k = true := by simpa using hb k hk
  rwa [familyBlockOk_congr (BEq.symm hyk)] at hk'

/-- What `strayFamilyMember = none` says over the compile's condensation: family blocks. -/
theorem strayFamilyMember_none {env : Ix.Environment} (h : strayFamilyMember env (compileBlocks env) = none) :
    FamilyBlocks env :=
  fun rep all hall y hy => familyBlockOk_spec (strayFamilyMember_member h rep all hall y hy)

/-- **Family blocks**: when `compileReport` returns, every block of the compile's condensation
that holds a family member is exactly that family's types and constructors, or exactly its
recursors, each with its family's `all`, and the family is of 64-bit size. -/
theorem familyBlocks {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : FamilyBlocks env := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact strayFamilyMember_none (checkReport_ok hc).families

/-! ### Recursor slots and shapes -/

/-- The check's block members are the recursor index's (`ReaderIndex.inductives`). -/
theorem inductiveMembers_eq : inductiveMembers = Ix.CompileCert.ReaderIndex.inductives := rfl

/-- The check's motive order is the recursor index's (`ReaderIndex.orderFor`). -/
theorem motiveOrder_eq : motiveOrder = Ix.CompileCert.ReaderIndex.orderFor := rfl

/-- The check's order guard is the recursor index's (`ReaderIndex.orderValid`). -/
theorem motiveOrderValid_eq : motiveOrderValid = Ix.CompileCert.ReaderIndex.orderValid := rfl

/-- **Every stored recursor member is filed by its analysis, at a slot of its own.** -/
def RecursorSlotsUnique (ixe : Ixon.Env) : Prop :=
  (∀ o c, recordAt ixe o = some c → ∀ j r, (j, r) ∈ Ix.Kernel.Reader.recursorMembers c →
      (recursorSlot? (recordAt ixe) o c r).isSome = true) ∧
  ∀ (o₁ o₂ : Address) (c₁ c₂ : Ixon.Constant) (j₁ j₂ : Nat) (r₁ r₂ : Ixon.Recursor) (slot : Address × Nat),
    recordAt ixe o₁ = some c₁ → recordAt ixe o₂ = some c₂ →
    (j₁, r₁) ∈ Ix.Kernel.Reader.recursorMembers c₁ → (j₂, r₂) ∈ Ix.Kernel.Reader.recursorMembers c₂ →
    recursorSlot? (recordAt ixe) o₁ c₁ r₁ = some slot → recursorSlot? (recordAt ixe) o₂ c₂ r₂ = some slot →
    o₁ = o₂ ∧ j₁ = j₂

/-- **Every published input family recursor is filed by its name**: at its family's block and
the motive its name gives it, its first carriers the block's members in order, its major
premise an inductive whose constructors, in order, are where its rules' constructors are
published (the block's own, or a nested family's container's). -/
def RecursorShapes (env : Ix.Environment) (ixe : Ixon.Env) : Prop :=
  ∀ (n : Ix.Name) (rv : Ix.RecursorVal) (named : Ixon.Named),
    (n, .recInfo rv) ∈ env.consts.toList → ixe.named.get? n = some named →
    ∃ (first : Ix.Name) (fv : Ix.InductiveVal) (m : Nat) (fnamed : Ixon.Named) (owner : Address) (j : Nat)
      (c : Ixon.Constant) (r : Ixon.Recursor) (carriers : Array (Ix.Kernel.ConstRef Address)) (mb : Address)
      (mi : Nat) (ind : Ixon.Inductive),
      rv.all[0]? = some first ∧ env.consts.get? first = some (.inductInfo fv) ∧ namedMotive? fv n = some m ∧
      ixe.named.get? first = some fnamed ∧ publishedRecursor? ixe n = some (owner, j) ∧
      recordAt ixe owner = some c ∧ (j, r) ∈ Ix.Kernel.Reader.recursorMembers c ∧
      recursorAnalysis? (recordAt ixe) owner c r = some (blockAt ixe fnamed.addr, m, carriers, .member mb mi) ∧
      (∀ i < fv.all.size, carriers[i]? = some (.member (blockAt ixe fnamed.addr) i)) ∧
      Ix.Kernel.Reader.inductiveAt (recordAt ixe) (.member mb mi) = some ind ∧ ind.ctors.size = rv.rules.size ∧
      ∀ k (hk : k < rv.rules.size), ∃ cn, ixe.named.get? rv.rules[k].ctor = some cn ∧
        Ix.Kernel.Reader.resolve (recordAt ixe) cn.addr = some (.ctor mb mi k)

/-- A stored record is among the stored records. -/
theorem mem_storedRecords {ixe : Ixon.Env} {o : Address} {c : Ixon.Constant} (hc : recordAt ixe o = some c) :
    (o, c) ∈ storedRecords ixe := by
  obtain ⟨lc, hlc, hget⟩ : ∃ lc, ixe.consts.get? o = some lc ∧ lc.get? = some c := by
    unfold recordAt at hc
    cases hl : ixe.consts.get? o with
    | none => rw [hl] at hc; cases hc
    | some lc => rw [hl] at hc; exact ⟨lc, rfl, hc⟩
  have hin : (o, lc) ∈ ixe.consts.toArray := by
    rw [Std.HashMap.mem_toArray_iff_getElem?_eq_some, ← Std.HashMap.get?_eq_getElem?]
    exact hlc
  unfold storedRecords
  exact Array.mem_filterMap.mpr ⟨(o, lc), hin, by simp [hget]⟩

/-- Every stored recursor member is among `recursorSlots`, with its slot. -/
theorem mem_recursorSlots {ixe : Ixon.Env} {o : Address} {c : Ixon.Constant} {j : Nat} {r : Ixon.Recursor}
    (hc : recordAt ixe o = some c) (hjr : (j, r) ∈ Ix.Kernel.Reader.recursorMembers c) :
    ((o, j), recursorSlot? (recordAt ixe) o c r) ∈ recursorSlots ixe := by
  have hrec : (o, c) ∈ storedRecursorRecords ixe := by
    rw [storedRecursorRecords_eq]
    refine Array.mem_filter.mpr ⟨mem_storedRecords hc, ?_⟩
    have : (Ix.Kernel.Reader.recursorMembers c).isEmpty = false := by
      cases hm : (Ix.Kernel.Reader.recursorMembers c).isEmpty
      · rfl
      · rw [Array.isEmpty_iff] at hm
        rw [hm] at hjr
        simp at hjr
    simp [this]
  unfold recursorSlots
  rw [parMap_map, Array.toList_map, List.mem_flatten]
  refine ⟨_, List.mem_map.mpr ⟨(o, c), Array.mem_toList_iff.mpr hrec, rfl⟩, ?_⟩
  exact List.mem_map.mpr ⟨(j, r), Array.mem_toList_iff.mpr hjr, rfl⟩

/-- What `recursorSlotError = none` says: every stored recursor member is filed, at a slot of
its own. -/
theorem recursorSlotError_none {ixe : Ixon.Env} (h : recursorSlotError ixe = none) :
    RecursorSlotsUnique ixe := by
  unfold recursorSlotError at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hfind
    rw [List.find?_eq_none] at hfind
    refine ⟨fun o c hc j r hjr => ?_, fun o₁ o₂ c₁ c₂ j₁ j₂ r₁ r₂ slot hc₁ hc₂ hm₁ hm₂ hs₁ hs₂ => ?_⟩
    · have := hfind _ (mem_recursorSlots hc hjr)
      exact Option.isSome_iff_ne_none.mpr (by simpa using this)
    · rw [List.findSome?_eq_none_iff] at h
      have e₁ := h (slot, (o₁, j₁)) (List.mem_filterMap.mpr ⟨_, mem_recursorSlots hc₁ hm₁, by simp [hs₁]⟩)
      have e₂ := h (slot, (o₂, j₂)) (List.mem_filterMap.mpr ⟨_, mem_recursorSlots hc₂ hm₂, by simp [hs₂]⟩)
      dsimp only at e₁ e₂
      split at e₁
      · rename_i d₁
        split at e₂
        · rename_i d₂
          rw [of_decide_eq_true d₁] at d₂
          have := Option.some.inj (of_decide_eq_true d₂)
          exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩
        · cases e₂
      · cases e₁

/-- What `rulesAt` checks: each rule's constructor is published where it resolves to the
inductive's constructor at the rule's position. -/
theorem rulesAt_spec {ixe : Ixon.Env} {rv : Ix.RecursorVal} {mb : Address} {mi : Nat}
    (h : rulesAt ixe rv mb mi = true) :
    ∀ k (hk : k < rv.rules.size), ∃ cn, ixe.named.get? rv.rules[k].ctor = some cn ∧
      Ix.Kernel.Reader.resolve (recordAt ixe) cn.addr = some (.ctor mb mi k) := by
  intro k hk
  unfold rulesAt at h
  have hk' := List.all_eq_true.mp h ⟨k, hk⟩ (List.mem_finRange _)
  dsimp only at hk'
  split at hk'
  · rename_i cn hcn
    exact ⟨cn, hcn, beq_iff_eq.mp hk'⟩
  · cases hk'

/-- What `recursorNameError = none` says of a published input recursor: it is filed by its
name. -/
theorem recursorNameError_spec {env : Ix.Environment} {ixe : Ixon.Env} {n : Ix.Name} {rv : Ix.RecursorVal}
    {named : Ixon.Named} (h : recursorNameError env ixe n rv = none) (hn : ixe.named.get? n = some named) :
    ∃ (first : Ix.Name) (fv : Ix.InductiveVal) (m : Nat) (fnamed : Ixon.Named) (owner : Address) (j : Nat)
      (c : Ixon.Constant) (r : Ixon.Recursor) (carriers : Array (Ix.Kernel.ConstRef Address)) (mb : Address)
      (mi : Nat) (ind : Ixon.Inductive),
      rv.all[0]? = some first ∧ env.consts.get? first = some (.inductInfo fv) ∧ namedMotive? fv n = some m ∧
      ixe.named.get? first = some fnamed ∧ publishedRecursor? ixe n = some (owner, j) ∧
      recordAt ixe owner = some c ∧ (j, r) ∈ Ix.Kernel.Reader.recursorMembers c ∧
      recursorAnalysis? (recordAt ixe) owner c r = some (blockAt ixe fnamed.addr, m, carriers, .member mb mi) ∧
      (∀ i < fv.all.size, carriers[i]? = some (.member (blockAt ixe fnamed.addr) i)) ∧
      Ix.Kernel.Reader.inductiveAt (recordAt ixe) (.member mb mi) = some ind ∧ ind.ctors.size = rv.rules.size ∧
      ∀ k (hk : k < rv.rules.size), ∃ cn, ixe.named.get? rv.rules[k].ctor = some cn ∧
        Ix.Kernel.Reader.resolve (recordAt ixe) cn.addr = some (.ctor mb mi k) := by
  unfold recursorNameError at h
  rw [hn] at h
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at h
  cases hfirst : rv.all[0]? with
  | none => rw [hfirst] at h; cases h
  | some first =>
  rw [hfirst] at h
  dsimp only at h
  cases hfv : env.consts.get? first with
  | none => rw [hfv] at h; cases h
  | some ci =>
  rw [hfv] at h
  cases ci with
  | inductInfo fv =>
    dsimp only at h
    cases hm : namedMotive? fv n with
    | none => rw [hm] at h; cases h
    | some m =>
    rw [hm] at h
    dsimp only at h
    cases hfn : ixe.named.get? first with
    | none => rw [hfn] at h; cases h
    | some fnamed =>
    cases hpub : publishedRecursor? ixe n with
    | none => rw [hfn, hpub] at h; cases h
    | some p =>
    obtain ⟨owner, j⟩ := p
    rw [hfn, hpub] at h
    dsimp only at h
    cases hc : storedRecord ixe owner with
    | none => rw [hc] at h; cases h
    | some c =>
    rw [hc] at h
    dsimp only at h
    cases hfind : (Ix.Kernel.Reader.recursorMembers c).find? (·.1 == j) with
    | none => rw [hfind] at h; cases h
    | some e =>
    obtain ⟨j', r⟩ := e
    rw [hfind] at h
    dsimp only at h
    have hjr : (j, r) ∈ Ix.Kernel.Reader.recursorMembers c := by
      have hj : j' = j := by simpa using Array.find?_some hfind
      subst hj
      exact Array.mem_of_find?_eq_some hfind
    cases han : recursorAnalysis? (storedRecord ixe) owner c r with
    | none => rw [han] at h; cases h
    | some a =>
    obtain ⟨b, m', carriers, major⟩ := a
    rw [han] at h
    dsimp only at h
    by_cases hgood : (b == recordBlock ixe fnamed.addr && m' == m &&
        (List.range fv.all.size).all (fun i => carriers[i]? == some (.member b i))) = true
    · simp only [hgood] at h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hgood
      obtain ⟨⟨hb, hm'⟩, hcar⟩ := hgood
      rw [recordBlock_eq] at hb
      subst hb hm'
      cases major with
      | ctor _ _ _ => cases h
      | member mb mi =>
        dsimp only at h
        cases hind : Ix.Kernel.Reader.inductiveAt (storedRecord ixe) (.member mb mi) with
        | none => rw [hind] at h; cases h
        | some ind =>
        rw [hind] at h
        dsimp only at h
        by_cases hr : (ind.ctors.size == rv.rules.size && rulesAt ixe rv mb mi) = true
        · rw [Bool.and_eq_true, beq_iff_eq] at hr
          exact ⟨first, fv, _, fnamed, owner, j, c, r, carriers, mb, mi, ind, rfl, hfv, hm, hfn, rfl,
            hc, hjr, han, hcar, hind, hr.1, rulesAt_spec hr.2⟩
        · simp only [hr] at h
          cases h
    · simp only [hgood] at h
      cases h
  | _ => cases h

/-- What `recursorShapeError = none` says: recursor slots are unique and every published input
family recursor is filed by its name. -/
theorem recursorShapeError_none {env : Ix.Environment} {ixe : Ixon.Env} (h : recursorShapeError env ixe = none) :
    RecursorSlotsUnique ixe ∧ RecursorShapes env ixe := by
  unfold recursorShapeError at h
  split at h
  · cases h
  · rename_i hslots
    refine ⟨recursorSlotError_none hslots, fun n rv named hn hnamed => ?_⟩
    rw [parMap_map, Array.findSome?_eq_none_iff] at h
    have hin : (n, Ix.ConstantInfo.recInfo rv) ∈ env.consts.toArray := by
      rw [← Std.HashMap.toArray_toList]
      exact List.mem_toArray.mpr hn
    have := h _ (Array.mem_map_of_mem hin)
    exact recursorNameError_spec this hnamed

/-- **Recursor slots are unique**: when `compileReport` returns, every stored recursor member is
filed by the recursor index's analysis, and no two at one slot. -/
theorem recursorSlotsUnique {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : RecursorSlotsUnique ixe := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact (recursorShapeError_none (checkReport_ok hc).recursorShapes).1

/-- **Recursors are filed by their names**: when `compileReport` returns, every published input
family recursor is filed at its family's block and the motive its name gives it, with its
rules' constructors its major premise's. -/
theorem recursorShapes {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : RecursorShapes env ixe := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact (recursorShapeError_none (checkReport_ok hc).recursorShapes).2

/-! ### Published definitions have hints -/

/-- **Every published input definition, theorem or opaque has a reducibility hint at its
address** (`Ixon.Env.anonHints`), where the reader (`hintsOf`) and quotient Source
(`fiberHintsMap`) both read it. -/
def DefinitionsHinted (env : Ix.Environment) (ixe : Ixon.Env) : Prop :=
  ∀ n named ci, (n, named) ∈ ixe.named.toList → env.consts.get? n = some ci →
    Ix.LeanIngress.isDefinition ci = true → (ixe.anonHints.get? named.addr).isSome = true

theorem unhintedDefinition_none {env : Ix.Environment} {ixe : Ixon.Env} (h : unhintedDefinition env ixe = none) :
    DefinitionsHinted env ixe := by
  intro n named ci hmem hci hdef
  unfold unhintedDefinition at h
  rw [List.findSome?_eq_none_iff] at h
  have hfind := h (n, named) hmem
  dsimp only at hfind
  rw [hci] at hfind
  rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]
  cases ci
  all_goals first
    | (simp [Ix.LeanIngress.isDefinition] at hdef; done)
    | (simp only at hfind
       split at hfind
       · assumption
       · cases hfind)

/-- **`checkReport`'s hint check**: every published input definition has a hint at its address. -/
theorem definitionsHinted {env : Ix.Environment} {ixe : Ixon.Env} {failures : Failures}
    (h : compileReport env = .ok (ixe, failures)) : DefinitionsHinted env ixe := by
  obtain ⟨cenv, -, hc⟩ := compileReport_ok h
  exact unhintedDefinition_none (checkReport_ok hc).hints

end Ix.Cert
