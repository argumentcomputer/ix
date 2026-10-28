import Ix.Cert.ReaderKeys
import Ix.Cert.Stream
import Ix.CompileCert.ReaderIndex

/-! # Cached keys of selected closure rows

These facts concern the actual context built from `Stream.decodedOf`.
`Stream.StoredCanonical` and `closure_decodes` separately connect that list
to raw-byte admission. Coverage of all emitting references, the matching
Source/target trace, and the fixed fallback's closed shape remain open.
-/

namespace Ix.Cert.ReaderClosureKeys

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert

private def recordStep (m : Std.HashMap Address Ixon.Constant)
    (p : Address × Ixon.Constant) : Std.HashMap Address Ixon.Constant :=
  if m.contains p.1 then m else m.insert p.1 p.2

private theorem recordStep_keeps (m : Std.HashMap Address Ixon.Constant)
    (p : Address × Ixon.Constant) {a : Address} {c : Ixon.Constant}
    (h : m[a]? = some c) : (recordStep m p)[a]? = some c := by
  unfold recordStep
  split
  · exact h
  · rename_i hn
    rw [Std.HashMap.getElem?_insert]
    split
    · rename_i he
      have he : p.1 = a := beq_iff_eq.mp he
      rw [he, Std.HashMap.contains_eq_isSome_getElem?, h] at hn
      exact (hn rfl).elim
    · exact h

private theorem recordFold_get (xs : List (Address × Ixon.Constant))
    (m : Std.HashMap Address Ixon.Constant) (a : Address) :
    (xs.foldl recordStep m)[a]? = (m[a]? <|> xs.lookup a) := by
  induction xs generalizing m with
  | nil => simp
  | cons p xs ih =>
    rw [List.foldl_cons, ih, List.lookup_cons]
    cases h : m[a]? with
    | some c => rw [recordStep_keeps m p h]; rfl
    | none =>
      by_cases he : p.1 = a
      · rcases p with ⟨a', c⟩
        dsimp only at he
        subst a'
        simp [recordStep, Std.HashMap.contains_eq_isSome_getElem?, h]
      · have ha : (a == p.1) = false := beq_eq_false_iff_ne.mpr (Ne.symm he)
        have hp : (p.1 == a) = false := beq_eq_false_iff_ne.mpr he
        simp only [recordStep]
        split <;> simp [Std.HashMap.getElem?_insert, hp, ha, h]

theorem recordMap_get (records : Array (Address × Ixon.Constant)) (a : Address) :
    (recordMap records)[a]? = records.toList.lookup a := by
  unfold recordMap
  rw [← Array.foldl_toList]
  exact (recordFold_get records.toList {} a).trans (by simp)

theorem lookup_of_nodup {xs : List (Address × Ixon.Constant)}
    (unique : (xs.map Prod.fst).Nodup) {a : Address} {c : Ixon.Constant}
    (present : (a, c) ∈ xs) : xs.lookup a = some c := by
  induction xs with
  | nil => cases present
  | cons p xs ih =>
    rcases List.nodup_cons.mp unique with ⟨fresh, tailUnique⟩
    rcases List.mem_cons.mp present with he | tailPresent
    · cases he
      exact List.lookup_cons_self
    · have different : a ≠ p.1 := by
        intro same
        exact fresh (same ▸ List.mem_map.mpr ⟨(a, c), tailPresent, rfl⟩)
      cases p with
      | mk b d =>
        rw [List.lookup_cons, beq_eq_false_iff_ne.mpr different]
        exact ih tailUnique tailPresent

theorem recordMap_none_iff (records : Array (Address × Ixon.Constant)) (a : Address) :
    (recordMap records)[a]? = none ↔ a ∉ records.toList.map Prod.fst := by
  rw [recordMap_get, List.lookup_eq_none_iff]
  constructor
  · intro h present
    obtain ⟨p, hp, he⟩ := List.mem_map.mp present
    exact (bne_iff_ne.mp (h p hp)) he.symm
  · intro h p hp
    apply bne_iff_ne.mpr
    intro same
    exact h (List.mem_map.mpr ⟨p, hp, same.symm⟩)

/-- The records `contextOf` computes keys ahead for (`keysOf`); its recursor index scans the
sub-array `indexedRecords`. -/
def scanned (input fallback : Array (Address × Ixon.Constant)) : Array (Address × Ixon.Constant) :=
  let known : Std.HashSet Address := input.foldl (fun s (a, _) => s.insert a) {}
  input ++ fallback.filter (fun (a, _) => !known.contains a)

private theorem known_mem (input : Array (Address × Ixon.Constant)) (a : Address) :
    (input.foldl (fun s (p : Address × Ixon.Constant) => s.insert p.1)
      ({} : Std.HashSet Address)).contains a = true ↔ a ∈ input.toList.map Prod.fst := by
  rw [← Array.foldl_toList]
  suffices h : ∀ (xs : List (Address × Ixon.Constant)) (s : Std.HashSet Address),
      (xs.foldl (fun s p => s.insert p.1) s).contains a = true ↔
        s.contains a = true ∨ a ∈ xs.map Prod.fst by
    simpa using h input.toList {}
  intro xs
  induction xs with
  | nil => intro s; simp
  | cons p xs ih =>
    intro s
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
    rw [Bool.or_eq_true_iff, beq_iff_eq]
    simp only [List.map_cons, List.mem_cons]
    constructor
    · rintro ((same | old) | later)
      · exact .inr (.inl same.symm)
      · exact .inl old
      · exact .inr (.inr later)
    · rintro (old | same | later)
      · exact .inl (.inr old)
      · exact .inl (.inl same.symm)
      · exact .inr later

theorem mem_scanned {input fallback : Array (Address × Ixon.Constant)}
    {a : Address} {c : Ixon.Constant} :
    (a, c) ∈ scanned input fallback ↔ (a, c) ∈ input ∨
      ((a, c) ∈ fallback ∧ a ∉ input.toList.map Prod.fst) := by
  simp only [scanned, Array.mem_append, Array.mem_filter]
  have h := known_mem input a
  cases hc : (input.foldl (fun s p => s.insert p.1) ({} : Std.HashSet Address)).contains a
  · simp only [hc, Bool.not_false, and_true, Bool.false_eq_true, false_iff] at h ⊢
    simp only [h, not_false_eq_true, and_true]
  · simp only [hc, Bool.not_true, Bool.false_eq_true, and_false, or_false, true_iff] at h ⊢
    simp only [h, not_true_eq_false, and_false, or_false]

/-- The index scans a sub-array of the scanned records: the input records it leaves out are
ones filed into a block only the fallback supplies, and the fallback records it leaves out are
ones filed into a block the input supplies (`indexedRecords`). -/
theorem mem_indexed_scanned {store : Store} {input fallback : Array (Address × Ixon.Constant)}
    {a : Address} {c : Ixon.Constant} (h : (a, c) ∈ indexedRecords store input fallback) :
    (a, c) ∈ scanned input fallback := by
  simp only [indexedRecords, scanned, Array.mem_append, Array.mem_filter, Bool.and_eq_true] at h ⊢
  rcases h with ⟨h, -⟩ | ⟨h, known, -⟩
  · exact .inl h
  · exact .inr ⟨h, known⟩

section Context

variable {md : Mode} (t : RoleTable) (input fallback : Array (Address × Ixon.Constant))
    (blobs fallbackBlobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ReducibilityHint)
    (reconstruct : Store → ConstRef Address → Option Address)

local notation "cx" => (contextOf (md := md) t input blobs fallback fallbackBlobs hint reconstruct)

theorem context_input (unique : (input.toList.map Prod.fst).Nodup)
    {a : Address} {c : Ixon.Constant} (present : (a, c) ∈ input) :
    (cx).store a = some c := by
  change ((recordMap input)[a]? <|> ((recordMap fallback)[a]? <|> none)) = some c
  rw [recordMap_get, lookup_of_nodup unique (Array.mem_toList_iff.mpr present)]
  rfl

theorem context_fallback {a : Address} {c : Ixon.Constant}
    (absent : a ∉ input.toList.map Prod.fst) (stored : (recordMap fallback)[a]? = some c) :
    (cx).store a = some c := by
  change ((recordMap input)[a]? <|> ((recordMap fallback)[a]? <|> none)) = some c
  rw [(recordMap_none_iff input a).mpr absent, stored]
  rfl

theorem context_coherent (unique : (input.toList.map Prod.fst).Nodup)
    (fallbackCoherent : ∀ a c, (a, c) ∈ fallback → (recordMap fallback)[a]? = some c) :
    ReaderIndex.Coherent (cx).store (scanned input fallback) := by
  intro a c present
  rcases mem_scanned.mp present with present | ⟨present, absent⟩
  · exact context_input t input fallback blobs fallbackBlobs hint reconstruct unique present
  · exact context_fallback t input fallback blobs fallbackBlobs hint reconstruct absent
      (fallbackCoherent a c present)

theorem context_coherent_of_nodup (unique : (input.toList.map Prod.fst).Nodup)
    (fallbackUnique : (fallback.toList.map Prod.fst).Nodup) :
    ReaderIndex.Coherent (cx).store (scanned input fallback) := by
  apply context_coherent t input fallback blobs fallbackBlobs hint reconstruct unique
  intro a c present
  rw [recordMap_get]
  exact lookup_of_nodup fallbackUnique (Array.mem_toList_iff.mpr present)

theorem scanned_cached {a : Address} {c : Ixon.Constant} {ref : ConstRef Address}
    (present : (a, c) ∈ scanned input fallback) (resolved : resolve (cx).store a = some ref) :
    ∃ b, (cx).keys.address[ref]? = some b :=
  ReaderKeys.keysOf_covers (Array.mem_toList_iff.mpr present) resolved

theorem input_resolved_cached (unique : (input.toList.map Prod.fst).Nodup)
    {a : Address} {c : Ixon.Constant} {ref : ConstRef Address}
    (present : (a, c) ∈ input) (resolved : resolveSource (cx).store a c = some ref) :
    ∃ b, (cx).keys.address[ref]? = some b := by
  apply scanned_cached t input fallback blobs fallbackBlobs hint reconstruct (mem_scanned.mpr (.inl present))
  unfold resolve
  rw [context_input t input fallback blobs fallbackBlobs hint reconstruct unique present]
  exact resolved

/-- Every selected recursor comes from an input row or an unshadowed fallback
row. This does not identify it with an intended Source recursor. -/
theorem selected_origin {block : Address} {shape : BlockShape} {ref : ConstRef Address}
    (found : (cx).index.blocks[block]? = some shape) (selected : ref ∈ shape.recs) :
    ∃ owner c position recursor, ref = .member owner position ∧
      ((owner, c) ∈ input ∨ (owner, c) ∈ fallback ∧ owner ∉ input.toList.map Prod.fst) ∧
      (position, recursor) ∈ recursorMembers c := by
  obtain ⟨_, _, _, owner, c, position, recursor, _, _, _, _, _, _, reference, present, member, _⟩ :=
    ReaderIndex.grouped_entry (cx).store (indexedRecords (cx).store input fallback) block shape found ref selected
  exact ⟨owner, c, position, recursor, reference, mem_scanned.mp (mem_indexed_scanned present), member⟩

/-- A coherent scanned singleton recursor contributes its own cached address. -/
theorem standalone_origin_cached (coherent : ReaderIndex.Coherent (cx).store (scanned input fallback))
    {owner : Address} {c : Ixon.Constant} {position : Nat} {recursor value : Ixon.Recursor}
    (present : (owner, c) ∈ scanned input fallback)
    (member : (position, recursor) ∈ recursorMembers c) (kind : c.info = .recr value) :
    position = 0 ∧ ∃ b, (cx).keys.address[ConstRef.member owner position]? = some b := by
  have source := ReaderIndex.member_source c position recursor member
  rw [kind] at source
  refine ⟨source.1, scanned_cached t input fallback blobs fallbackBlobs hint reconstruct present ?_⟩
  unfold resolve
  rw [coherent owner c present]
  change resolveSource (cx).store owner c = some (.member owner position)
  simp only [resolveSource, kind, source.1]

/-- Under an internal singleton-origin property of fallback recursors, a
selected reference is cached or has an explicit input origin in a mutual
block. The closed fallback data and that remaining input case are separate. -/
theorem selected_cached_or_input_mutual (unique : (input.toList.map Prod.fst).Nodup)
    (fallbackCoherent : ∀ a c, (a, c) ∈ fallback → (recordMap fallback)[a]? = some c)
    (fallbackSingleton : ∀ a c, (a, c) ∈ fallback → ∀ position recursor,
      (position, recursor) ∈ recursorMembers c → ∃ value, c.info = .recr value)
    {block : Address} {shape : BlockShape} {ref : ConstRef Address}
    (found : (cx).index.blocks[block]? = some shape) (selected : ref ∈ shape.recs) :
    (∃ b, (cx).keys.address[ref]? = some b) ∨
      ∃ owner c position recursor members, (owner, c) ∈ input ∧ ref = .member owner position ∧
        c.info = .muts members ∧ members[position]? = some (.recr recursor) := by
  obtain ⟨owner, c, position, recursor, reference, origin, member⟩ :=
    selected_origin t input fallback blobs fallbackBlobs hint reconstruct found selected
  have present := mem_scanned.mpr origin
  have source := ReaderIndex.member_source c position recursor member
  cases kind : c.info with
  | recr value =>
    left
    rw [reference]
    exact (standalone_origin_cached t input fallback blobs fallbackBlobs hint reconstruct
      (context_coherent t input fallback blobs fallbackBlobs hint reconstruct unique fallbackCoherent)
      present member kind).2
  | muts members =>
    rw [kind] at source
    rcases origin with primary | ⟨fallbackRow, _⟩
    · exact .inr ⟨owner, c, position, recursor, members, primary, reference, kind, source⟩
    · obtain ⟨value, singleton⟩ := fallbackSingleton owner c fallbackRow position recursor member
      rw [kind] at singleton
      cases singleton
  | _ => simp only [kind] at source

end Context

/-- A stored seed is one of the selected decoded rows. This uses the lazy
record's `get?`, not a claim that raw-byte admission has already decoded it. -/
theorem seeded_decoded {ixe : Ixon.Env} {sub : Ix.Environment} {order : List Address}
    (closure : ClosureOrder ixe (Seed ixe sub) order) {a : Address} {c : Ixon.Constant}
    (seed : Seed ixe sub a) (stored : recordAt ixe a = some c) :
    (a, c) ∈ Stream.decodedOf ixe order := by
  have existsRecord : ∃ lc, ixe.consts.get? a = some lc := by
    obtain ⟨lc, found, _⟩ := Option.bind_eq_some_iff.mp stored
    exact ⟨lc, found⟩
  have has : ixe.consts.contains a = true := by
    obtain ⟨lc, found⟩ := existsRecord
    rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?, found]
    rfl
  exact List.mem_filterMap.mpr ⟨a, (closure.complete a).mpr (.seed seed has), by simp [stored]⟩

/-- A resolving seed row is cached in the actual context over `decodedOf`.
`StoredCanonical` still supplies the connection to executed byte decoding. -/
theorem seeded_resolved_cached {ixe : Ixon.Env} {sub : Ix.Environment} {order : List Address}
    (closure : ClosureOrder ixe (Seed ixe sub) order)
    (hash : ByteArray → Address) (t : RoleTable) (pre : Prelude .anon)
    (blobs : Ix.Kernel.Ingress.Blobs) (hint : ConstRef Address → Option ReducibilityHint)
    {a : Address} {c : Ixon.Constant} {ref : ConstRef Address}
    (seed : Seed ixe sub a) (stored : recordAt ixe a = some c)
    (resolved : resolveSource
      (Admission.streamContext hash t pre (Stream.decodedOf ixe order) blobs hint).store a c = some ref) :
    ∃ b, (Admission.streamContext hash t pre (Stream.decodedOf ixe order) blobs hint).keys.address[ref]? = some b := by
  exact input_resolved_cached t _ (pre.records ++ pre.evidence) blobs pre.blobs hint
    (Admission.projectionAddress hash)
    (by simpa only [List.toList_toArray] using (Stream.decodedOf_keys ixe order).nodup closure.nodup)
    (by simpa only [List.mem_toArray] using seeded_decoded closure seed stored) resolved

theorem published_resolved_cached {ixe : Ixon.Env} {sub : Ix.Environment} {order : List Address}
    (closure : ClosureOrder ixe (Seed ixe sub) order)
    (hash : ByteArray → Address) (t : RoleTable) (pre : Prelude .anon)
    (blobs : Ix.Kernel.Ingress.Blobs) (hint : ConstRef Address → Option ReducibilityHint)
    {n : Ix.Name} {ci : Ix.ConstantInfo} {named : Ixon.Named} {c : Ixon.Constant} {ref : ConstRef Address}
    (source : sub.consts.get? n = some ci) (published : ixe.named.get? n = some named)
    (stored : recordAt ixe named.addr = some c)
    (resolved : resolveSource
      (Admission.streamContext hash t pre (Stream.decodedOf ixe order) blobs hint).store named.addr c = some ref) :
    ∃ b, (Admission.streamContext hash t pre (Stream.decodedOf ixe order) blobs hint).keys.address[ref]? = some b :=
  seeded_resolved_cached closure hash t pre blobs hint ⟨n, ci, named, source, published, rfl⟩ stored resolved

end Ix.Cert.ReaderClosureKeys
