import IxC.Kernel.Roles
import IxC.Address.Core
import Std.Data.HashSet

/-! # The role table and its binding section

A **role table** binds the checker's roles (`Ix.Kernel.Role`) to the
constants of one environment and carries the evidence of its operations
(IXC-PLAN §8.2). It is input: the checker carries the specifications
(`Role.spec`, `IxC/Kernel/Roles.lean`) and no addresses, and every theorem
holds for every table. The reader renames each bound address to its role key
(`Ix.Kernel.Reader.Bindings`) and resolves each proof entry to its theorem's
value (`Ix.Kernel.Reader.evidenceOf`); the fold validates every bound
constant against its specification.

## The binding section

The table's bytes are a section of their own (owner, 2026-10-14), not
Samuel's `E8 02` profile object. All integers are single bytes:

| bytes | field |
| --- | --- |
| `E8 03` | the section's tag, `N4(0xE, 11)` in the `.ixe`/claim tag space |
| `v` | the specification version (`specVersion`) |
| `n` | the number of bound roles |
| `n × (r, a)` | a role's index in `Role.all` and the 32-byte address bound to it, role indices strictly increasing |
| `m` | the number of evidence entries |
| `m × (r, k, e₁ … e_k)` | a role's index, its evidence count and its evidence, role indices strictly increasing |
| `e` | `00` for `defeq`, `01` and a 32-byte address for `proof` |

The encoding is canonical: a table has one encoding, and the decoder accepts
exactly the encodings of the tables within the format's bounds (`WireWF`),
with no trailing byte (`RoleTable.ofBytes_eq_some_iff`). The admission entry
authenticates the bytes with its `hash` parameter; their hash is the binding
hash a claim commits to.

## Well-formedness

`RoleTable.check` is decidable and runs once, at admission; a failure is a
reject. A table is well formed when its version is `specVersion`, it is
injective in both directions (no role and no address twice), it is closed
under `Role.block` (a block's roles are bound together) and `Role.deps`, and
the evidence is exactly the bound operations': one entry per equation of the
role's `ops` specification, of the kind `Spec.evidenceKinds` fixes, and none
for any other role. This replaces the reader's checks on its committed pin
table (`pinMap`'s `rootComponent` and `derivedShape`, SP3's D6). -/

namespace Ix.Kernel

/-! ## Role indices -/

/-- A role's position in `Role.all`: its index in the binding section. -/
def Role.idx (r : Role) : Nat := Role.all.idxOf r

/-- The role at a binding-section index. -/
def Role.ofIdx? (i : Nat) : Option Role := Role.all[i]?

theorem Role.ofIdx?_idx (r : Role) : Role.ofIdx? r.idx = some r := by
  cases r <;> rfl

theorem Role.idx_lt (r : Role) : r.idx < 64 := by
  cases r <;> decide

/-- Every index below 64 names a role whose index it is (checked). -/
theorem Role.ofIdx?_idx_below :
    ∀ i, i < 64 → (match Role.ofIdx? i with | some r => r.idx == i | none => Bool.false) = Bool.true := by
  decide

theorem Role.idx_ofIdx? {i : Nat} {r : Role} (h : Role.ofIdx? i = some r) : r.idx = i := by
  have hi : i < 64 := by
    rcases Nat.lt_or_ge i 64 with hlt | hge
    · exact hlt
    · have : Role.all.length ≤ i := by simpa [Role.all] using hge
      simp [Role.ofIdx?, List.getElem?_eq_none this] at h
  have hc := Role.ofIdx?_idx_below i hi
  rw [h] at hc
  simpa using hc

theorem Role.idx_inj {r s : Role} (h : r.idx = s.idx) : r = s := by
  have h1 := Role.ofIdx?_idx r
  rw [h, Role.ofIdx?_idx] at h1
  exact (Option.some.inj h1).symm

/-! ## The table -/

/-- **A role table** (IXC-PLAN §8.2): the version of the specification set it
was made for, the bound roles' addresses (by role, ascending), and the
operations' evidence (by role, ascending; one entry per equation). -/
structure RoleTable where
  version : Nat
  bound : Array (Role × Address)
  evidence : Array (Role × Array (Evidence Address))
  deriving Inhabited

/-! ## The binding section -/

namespace RoleTable

/-- Role indices strictly increasing. -/
def Ascending : List Role → Bool
  | a :: b :: rest => decide (a.idx < b.idx) && Ascending (b :: rest)
  | _ => true

/-- An evidence entry's address width. -/
def Evidence.wide : Evidence Address → Bool
  | .defeq => true
  | .proof a => a.hash.size == 32

/-- **The format's domain**: what the binding section can encode, exactly
once. -/
def wireWF (t : RoleTable) : Bool :=
  decide (t.version < 256) && decide (t.bound.size < 256) && decide (t.evidence.size < 256) &&
  t.bound.toList.all (fun p => p.2.hash.size == 32) &&
  t.evidence.toList.all (fun p => decide (p.2.size < 256) && p.2.toList.all Evidence.wide) &&
  Ascending (t.bound.toList.map (·.1)) && Ascending (t.evidence.toList.map (·.1))

/-- The 32 bytes of an address. -/
def encAddr (a : Address) : List UInt8 := a.hash.data.toList

def encBound (p : Role × Address) : List UInt8 := p.1.idx.toUInt8 :: encAddr p.2

def encEvidence : Evidence Address → List UInt8
  | .defeq => [0]
  | .proof a => 1 :: encAddr a

def encEntry (p : Role × Array (Evidence Address)) : List UInt8 :=
  p.1.idx.toUInt8 :: p.2.size.toUInt8 :: p.2.toList.flatMap encEvidence

/-- The section's bytes, as a list. -/
def encode (t : RoleTable) : List UInt8 :=
  0xE8 :: 0x03 :: t.version.toUInt8 :: t.bound.size.toUInt8 ::
    (t.bound.toList.flatMap encBound ++
      (t.evidence.size.toUInt8 :: t.evidence.toList.flatMap encEntry))

/-- **The binding section's bytes.** -/
def toBytes (t : RoleTable) : ByteArray := ⟨t.encode.toArray⟩

def decAddr (bs : List UInt8) : Option (Address × List UInt8) :=
  if 32 ≤ bs.length then some (⟨⟨(bs.take 32).toArray⟩⟩, bs.drop 32) else none

def decBound : Nat → List UInt8 → Option (List (Role × Address) × List UInt8)
  | 0, bs => some ([], bs)
  | _ + 1, [] => none
  | n + 1, b :: bs => do
    let r ← Role.ofIdx? b.toNat
    let (a, bs) ← decAddr bs
    let (rest, bs) ← decBound n bs
    pure ((r, a) :: rest, bs)

def decEvidence : List UInt8 → Option (Evidence Address × List UInt8)
  | 0 :: bs => some (.defeq, bs)
  | 1 :: bs => do
    let (a, bs) ← decAddr bs
    pure (.proof a, bs)
  | _ => none

def decEvidences : Nat → List UInt8 → Option (List (Evidence Address) × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (e, bs) ← decEvidence bs
    let (rest, bs) ← decEvidences n bs
    pure (e :: rest, bs)

def decEntries : Nat → List UInt8 → Option (List (Role × Array (Evidence Address)) × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, b :: k :: bs => do
    let r ← Role.ofIdx? b.toNat
    let (es, bs) ← decEvidences k.toNat bs
    let (rest, bs) ← decEntries n bs
    pure ((r, es.toArray) :: rest, bs)
  | _ + 1, _ => none

/-- Decode a section, exactly: the whole input, within the format's domain. -/
def decode : List UInt8 → Option RoleTable
  | 0xE8 :: 0x03 :: v :: n :: bs =>
    match decBound n.toNat bs with
    | some (bound, m :: bs) =>
      match decEntries m.toNat bs with
      | some (ev, []) =>
        let t : RoleTable := ⟨v.toNat, bound.toArray, ev.toArray⟩
        if t.wireWF then some t else none
      | _ => none
    | _ => none
  | _ => none

/-- **The canonical decoder of the binding section.** -/
def ofBytes (bytes : ByteArray) : Option RoleTable := decode bytes.data.toList

/-! ### The decoder is exact -/

theorem toUInt8_toNat_of_lt {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt h]

theorem toNat_toUInt8 (b : UInt8) : b.toNat.toUInt8 = b := by
  simp [Nat.toUInt8]

theorem idx_toUInt8 (r : Role) : r.idx.toUInt8.toNat = r.idx :=
  toUInt8_toNat_of_lt (Nat.lt_trans (Role.idx_lt r) (by decide))

theorem decAddr_encAddr (a : Address) (h : a.hash.size = 32) (rest : List UInt8) :
    decAddr (encAddr a ++ rest) = some (a, rest) := by
  have hl : (encAddr a).length = 32 := by simpa [encAddr] using h
  unfold decAddr
  rw [if_pos (by simp [hl])]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
  cases a with
  | mk hash => cases hash with
    | mk data => simp [encAddr]

theorem decAddr_inv {bs rest : List UInt8} {a : Address} (h : decAddr bs = some (a, rest)) :
    bs = encAddr a ++ rest ∧ a.hash.size = 32 := by
  unfold decAddr at h
  split at h
  · rename_i hl
    cases h
    refine ⟨?_, ?_⟩
    · simp [encAddr, List.take_append_drop]
    · simp [ByteArray.size, List.length_take]; omega
  · cases h

theorem decBound_enc (rest : List UInt8) :
    ∀ (l : List (Role × Address)), (∀ p ∈ l, p.2.hash.size = 32) →
      decBound l.length (l.flatMap encBound ++ rest) = some (l, rest)
  | [], _ => rfl
  | (r, a) :: l, h => by
    have ha : a.hash.size = 32 := h (r, a) (List.mem_cons_self ..)
    have ih := decBound_enc rest l (fun p hp => h p (List.mem_cons_of_mem _ hp))
    simp only [List.flatMap_cons, List.length_cons, encBound, List.cons_append, List.append_assoc]
    simp only [decBound, idx_toUInt8, Role.ofIdx?_idx, Option.bind_eq_bind, Option.bind_some,
      decAddr_encAddr a ha, ih, Option.pure_def]

theorem decBound_inv :
    ∀ {n : Nat} {bs rest : List UInt8} {l : List (Role × Address)},
      decBound n bs = some (l, rest) →
      bs = l.flatMap encBound ++ rest ∧ l.length = n ∧ ∀ p ∈ l, p.2.hash.size = 32
  | 0, bs, rest, l, h => by
    simp only [decBound, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, [], rest, l, h => by simp [decBound] at h
  | n + 1, b :: bs, rest, l, h => by
    simp only [decBound, Option.bind_eq_bind, Option.pure_def] at h
    cases hr : Role.ofIdx? b.toNat with
    | none => simp [hr] at h
    | some r =>
      cases ha : decAddr bs with
      | none => simp [hr, ha] at h
      | some p =>
        obtain ⟨a, bs'⟩ := p
        cases hd : decBound n bs' with
        | none => simp [hr, ha, hd] at h
        | some q =>
          obtain ⟨l', rest'⟩ := q
          simp only [hr, ha, hd, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hbs, hwide⟩ := decAddr_inv ha
          obtain ⟨hbs', hlen, hw'⟩ := decBound_inv hd
          refine ⟨?_, by simp [hlen], ?_⟩
          · have hb : r.idx.toUInt8 = b := by
              rw [Role.idx_ofIdx? hr, toNat_toUInt8]
            simp [encBound, hb, hbs, hbs']
          · intro p hp
            simp only [List.mem_cons] at hp
            rcases hp with rfl | hp
            · exact hwide
            · exact hw' p hp

theorem decEvidence_enc (e : Evidence Address) (h : Evidence.wide e = true) (rest : List UInt8) :
    decEvidence (encEvidence e ++ rest) = some (e, rest) := by
  cases e with
  | defeq => rfl
  | proof a =>
    have ha : a.hash.size = 32 := by simpa [Evidence.wide] using h
    simp only [encEvidence, List.cons_append, decEvidence, Option.bind_eq_bind,
      decAddr_encAddr a ha, Option.bind_some, Option.pure_def]

theorem decEvidence_inv {bs rest : List UInt8} {e : Evidence Address}
    (h : decEvidence bs = some (e, rest)) :
    bs = encEvidence e ++ rest ∧ Evidence.wide e = true := by
  unfold decEvidence at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · rename_i bs
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    cases ha : decAddr bs with
    | none => simp [ha] at h
    | some p =>
      obtain ⟨a, bs'⟩ := p
      simp only [ha, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hbs, hw⟩ := decAddr_inv ha
      exact ⟨by simp [encEvidence, hbs], by simp [Evidence.wide, hw]⟩
  · cases h

theorem decEvidences_enc (rest : List UInt8) :
    ∀ (l : List (Evidence Address)), (∀ e ∈ l, Evidence.wide e = true) →
      decEvidences l.length (l.flatMap encEvidence ++ rest) = some (l, rest)
  | [], _ => rfl
  | e :: l, h => by
    have he := h e (List.mem_cons_self ..)
    have ih := decEvidences_enc rest l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, List.length_cons, List.append_assoc, decEvidences,
      Option.bind_eq_bind, decEvidence_enc e he, Option.bind_some, ih, Option.pure_def]

theorem decEvidences_inv :
    ∀ {n : Nat} {bs rest : List UInt8} {l : List (Evidence Address)},
      decEvidences n bs = some (l, rest) →
      bs = l.flatMap encEvidence ++ rest ∧ l.length = n ∧ ∀ e ∈ l, Evidence.wide e = true
  | 0, bs, rest, l, h => by
    simp only [decEvidences, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, bs, rest, l, h => by
    simp only [decEvidences, Option.bind_eq_bind, Option.pure_def] at h
    cases he : decEvidence bs with
    | none => simp [he] at h
    | some p =>
      obtain ⟨e, bs'⟩ := p
      cases hd : decEvidences n bs' with
      | none => simp [he, hd] at h
      | some q =>
        obtain ⟨l', rest'⟩ := q
        simp only [he, hd, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hbs, hw⟩ := decEvidence_inv he
        obtain ⟨hbs', hlen, hw'⟩ := decEvidences_inv hd
        refine ⟨by simp [hbs, hbs'], by simp [hlen], ?_⟩
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hw
        · exact hw' x hx

/-- The entries' side conditions: fewer than 256 entries each, wide addresses. -/
def EntryOk (p : Role × Array (Evidence Address)) : Prop :=
  p.2.size < 256 ∧ ∀ e ∈ p.2.toList, Evidence.wide e = true

theorem decEntries_enc (rest : List UInt8) :
    ∀ (l : List (Role × Array (Evidence Address))), (∀ p ∈ l, EntryOk p) →
      decEntries l.length (l.flatMap encEntry ++ rest) = some (l, rest)
  | [], _ => rfl
  | (r, es) :: l, h => by
    obtain ⟨hsz, hw⟩ := h (r, es) (List.mem_cons_self ..)
    have ih := decEntries_enc rest l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hk : es.size.toUInt8.toNat = es.toList.length := by
      rw [toUInt8_toNat_of_lt hsz, Array.length_toList]
    simp only [List.flatMap_cons, List.length_cons, encEntry, List.cons_append, List.append_assoc]
    simp only [decEntries, idx_toUInt8, Role.ofIdx?_idx, Option.bind_eq_bind, Option.bind_some,
      hk, decEvidences_enc _ es.toList hw, ih, Option.pure_def, Array.toArray_toList]

theorem decEntries_inv :
    ∀ {n : Nat} {bs rest : List UInt8} {l : List (Role × Array (Evidence Address))},
      decEntries n bs = some (l, rest) →
      bs = l.flatMap encEntry ++ rest ∧ l.length = n ∧ ∀ p ∈ l, EntryOk p
  | 0, bs, rest, l, h => by
    simp only [decEntries, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, [], rest, l, h => by simp [decEntries] at h
  | n + 1, [_], rest, l, h => by simp [decEntries] at h
  | n + 1, b :: k :: bs, rest, l, h => by
    simp only [decEntries, Option.bind_eq_bind, Option.pure_def] at h
    cases hr : Role.ofIdx? b.toNat with
    | none => simp [hr] at h
    | some r =>
      cases he : decEvidences k.toNat bs with
      | none => simp [hr, he] at h
      | some p =>
        obtain ⟨es, bs'⟩ := p
        cases hd : decEntries n bs' with
        | none => simp [hr, he, hd] at h
        | some q =>
          obtain ⟨l', rest'⟩ := q
          simp only [hr, he, hd, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hbs, hlen, hw⟩ := decEvidences_inv he
          obtain ⟨hbs', hlen', hw'⟩ := decEntries_inv hd
          have hb : r.idx.toUInt8 = b := by rw [Role.idx_ofIdx? hr, toNat_toUInt8]
          have hk : UInt8.ofNat es.length = k := by
            rw [hlen]; exact toNat_toUInt8 k
          refine ⟨?_, by simp [hlen'], ?_⟩
          · simp [encEntry, hb, hk, hbs, hbs']
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · refine ⟨?_, by simpa using hw⟩
              rw [List.size_toArray, hlen]
              exact UInt8.toNat_lt k
            · exact hw' x hx

theorem wireWF_iff (t : RoleTable) :
    t.wireWF = true ↔
      t.version < 256 ∧ t.bound.size < 256 ∧ t.evidence.size < 256 ∧
      (∀ p ∈ t.bound.toList, p.2.hash.size = 32) ∧ (∀ p ∈ t.evidence.toList, EntryOk p) ∧
      Ascending (t.bound.toList.map (·.1)) = true ∧
      Ascending (t.evidence.toList.map (·.1)) = true := by
  simp only [wireWF, EntryOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq, and_assoc]

/-- **The binding section is canonical**: the decoder accepts exactly the
encodings of the tables in the format's domain. -/
theorem decode_eq_some_iff (bs : List UInt8) (t : RoleTable) :
    decode bs = some t ↔ t.wireWF = true ∧ t.encode = bs := by
  constructor
  · intro h
    unfold decode at h
    split at h
    next v n bs =>
      split at h
      next bound m bs' hb =>
        split at h
        next ev he =>
          dsimp only at h
          split at h
          next hwf =>
            cases h
            obtain ⟨hbs, hblen, -⟩ := decBound_inv hb
            obtain ⟨hbs', helen, -⟩ := decEntries_inv he
            refine ⟨hwf, ?_⟩
            have hv : v.toNat.toUInt8 = v := toNat_toUInt8 v
            have hn : bound.toArray.size.toUInt8 = n := by
              rw [List.size_toArray, hblen, toNat_toUInt8]
            have hm : ev.toArray.size.toUInt8 = m := by
              rw [List.size_toArray, helen, toNat_toUInt8]
            simp only [encode, hv, hn, hm, hbs, hbs', List.append_nil]
          next => cases h
        next => cases h
      next => cases h
    next => cases h
  · rintro ⟨hwf, rfl⟩
    obtain ⟨hv, hn, hm, hb, he, -, -⟩ := (wireWF_iff t).mp hwf
    have hdb := decBound_enc (t.evidence.size.toUInt8 :: t.evidence.toList.flatMap encEntry)
      t.bound.toList hb
    have hde := decEntries_enc [] t.evidence.toList he
    rw [List.append_nil] at hde
    rw [Array.length_toList] at hdb hde
    simp only [encode, decode, toUInt8_toNat_of_lt hn, hdb, toUInt8_toNat_of_lt hm, hde,
      toUInt8_toNat_of_lt hv, Array.toArray_toList]
    cases t
    simp only at hwf ⊢
    rw [if_pos hwf]

/-- **`ofBytes` is canonical**: it accepts exactly the binding sections of
the tables in the format's domain, `toBytes`'s. -/
theorem ofBytes_eq_some_iff (bytes : ByteArray) (t : RoleTable) :
    ofBytes bytes = some t ↔ t.wireWF = true ∧ t.toBytes = bytes := by
  unfold ofBytes toBytes
  rw [decode_eq_some_iff]
  constructor
  · rintro ⟨hwf, h⟩
    refine ⟨hwf, ?_⟩
    cases bytes with
    | mk data => simp only at h; simp [h]
  · rintro ⟨hwf, rfl⟩
    exact ⟨hwf, by simp⟩

/-- A table re-encodes to its own section: the encoding round-trips. -/
theorem ofBytes_toBytes (t : RoleTable) (h : t.wireWF = true) : ofBytes t.toBytes = some t :=
  (ofBytes_eq_some_iff _ _).mpr ⟨h, rfl⟩

/-! ## Well-formedness -/

/-- The first address bound twice, if any. -/
def firstRepeat (as : List Address) : Option Address :=
  (as.foldl (fun (acc : Option Address × Std.HashSet Address) a =>
    match acc.1 with
    | some _ => acc
    | none => if acc.2.contains a then (some a, acc.2) else (none, acc.2.insert a))
    (none, {})).1

/-- **Well-formedness**, with the reason a table fails it: the version is
`specVersion`; no role and no address is bound twice; every bound role's
block and dependencies are bound; the evidence is exactly the bound
operations', one entry per equation of the kind the specification fixes. -/
def check (t : RoleTable) : Except String Unit := do
  unless t.version == specVersion do
    throw s!"role table version {t.version}, the specification set is version {specVersion}"
  let roles := t.bound.toList.map (·.1)
  unless roles.Nodup do throw "a role is bound twice"
  if let some a := firstRepeat (t.bound.toList.map (·.2)) then
    throw s!"address {a} is bound to two roles"
  for (r, _) in t.bound do
    for s in r.block do
      unless roles.contains s do throw s!"{repr r} is bound without {repr s}, its block's"
    for d in r.deps do
      unless roles.contains d do throw s!"{repr r} is bound without {repr d}, a dependency"
  let evRoles := t.evidence.toList.map (·.1)
  unless evRoles.Nodup do throw "a role has two evidence entries"
  for (r, es) in t.evidence do
    unless roles.contains r do throw s!"evidence for {repr r}, which is not bound"
    let kinds := (Role.spec r).evidenceKinds
    if kinds.isEmpty then throw s!"evidence for {repr r}, which is not an operation"
    unless es.size == kinds.length && (es.toList.zip kinds).all (fun (e, k) => e.isDefeqKind k) do
      throw s!"the evidence of {repr r} does not match its equations"
  for r in roles do
    unless (Role.spec r).evidenceKinds.isEmpty || evRoles.contains r do
      throw s!"operation {repr r} is bound without evidence"

/-- **A well-formed table** (`check`, decided). -/
def wf (t : RoleTable) : Bool := (check t).isOk

/-- The address bound to a role. -/
def addressOf? (t : RoleTable) (r : Role) : Option Address :=
  (t.bound.find? (·.1 == r)).map (·.2)

/-- A table from its entries in any order: the roles sorted ascending. -/
def ofEntries (version : Nat) (bound : List (Role × Address))
    (evidence : List (Role × Array (Evidence Address))) : RoleTable :=
  { version
    bound := (bound.toArray.qsort fun a b => a.1.idx < b.1.idx)
    evidence := (evidence.toArray.qsort fun a b => a.1.idx < b.1.idx) }

end RoleTable

end Ix.Kernel
