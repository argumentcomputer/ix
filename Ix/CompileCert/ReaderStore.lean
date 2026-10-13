import Ix.CompileCert.ReaderIndexEntries
import IxC.Kernel.Ixon.Prelude

/-! Coherence of the actual first-record-wins store and reader context.
Equal-address compatibility permits identical aliases; no digest injectivity
or unconditional equality of colliding records is assumed. -/

namespace Ix.CompileCert.ReaderStore

open Ix Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

abbrev Map := Std.HashMap Address Ixon.Constant

def step (map : Map) (row : Address × Ixon.Constant) : Map :=
  if map.contains row.1 then map else map.insert row.1 row.2

def first (records : List (Address × Ixon.Constant)) (key : Address) : Option Ixon.Constant :=
  (records.find? fun row => row.1 == key).map (·.2)

theorem step_lookup (map : Map) (row : Address × Ixon.Constant) (key : Address) :
    (step map row)[key]? = (map[key]? <|> if row.1 == key then some row.2 else none) := by
  by_cases same : row.1 = key
  · subst key
    unfold step
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    cases found : map[row.1]? <;> simp [found]
  · unfold step
    split <;> simp [Std.HashMap.getElem?_insert, beq_iff_eq, same]

theorem fold_lookup (records : List (Address × Ixon.Constant)) (initial : Map) (key : Address) :
    (records.foldl step initial)[key]? = (initial[key]? <|> first records key) := by
  induction records generalizing initial with
  | nil => simp [first]
  | cons row records ih =>
    rw [List.foldl_cons, ih, step_lookup]
    cases found : initial[key]? with
    | some value => simp
    | none =>
      by_cases same : row.1 = key
      · simp [first, same]
      · simp [first, same]

/-- Exact lookup behavior, including duplicate addresses: the first record
is retained independently of any compatibility premise. -/
theorem recordMap_lookup (records : Array (Address × Ixon.Constant)) (key : Address) :
    (recordMap records)[key]? = first records.toList key := by
  unfold recordMap
  change (records.foldl step ({} : Map))[key]? = _
  rw [← Array.foldl_toList, fold_lookup]
  simp

def Consistent (records : Array (Address × Ixon.Constant)) : Prop :=
  ∀ key left right, (key, left) ∈ records → (key, right) ∈ records → left = right

theorem first_present (records : Array (Address × Ixon.Constant)) (consistent : Consistent records)
    (key : Address) (constant : Ixon.Constant) (present : (key, constant) ∈ records) :
    first records.toList key = some constant := by
  unfold first
  cases found : records.toList.find? (fun row => row.1 == key) with
  | none =>
    have absent := List.find?_eq_none.mp found (key, constant) (by simpa using present)
    simp at absent
  | some row =>
    have matched := List.find?_some found
    have same : row.1 = key := beq_iff_eq.mp matched
    have occurs : row ∈ records := by simpa using List.mem_of_find?_eq_some found
    have value : row.2 = constant := consistent key row.2 constant (by simpa only [← same] using occurs) present
    simp [value]

theorem map_present (records : Array (Address × Ixon.Constant)) (consistent : Consistent records)
    (key : Address) (constant : Ixon.Constant) (present : (key, constant) ∈ records) :
    (recordMap records)[key]? = some constant := by
  rw [recordMap_lookup]
  exact first_present records consistent key constant present

theorem map_origin (records : Array (Address × Ixon.Constant)) (key : Address) (constant : Ixon.Constant)
    (found : (recordMap records)[key]? = some constant) : (key, constant) ∈ records := by
  rw [recordMap_lookup, first] at found
  cases picked : records.toList.find? (fun row => row.1 == key) with
  | none => rw [picked] at found; cases found
  | some row =>
    have matched := List.find?_some picked
    have same : row.1 = key := beq_iff_eq.mp matched
    have occurs : row ∈ records := by simpa using List.mem_of_find?_eq_some picked
    simp only [picked, Option.map_some, Option.some.injEq] at found
    simpa only [← same, ← found] using occurs

theorem storeOf_coherent (records : Array (Address × Ixon.Constant)) (fallback : Store)
    (consistent : Consistent records) : ReaderIndexEntries.Coherent (storeOf records fallback) records := by
  intro key constant present
  unfold storeOf
  rw [map_present records consistent key constant present]
  rfl

def known (records : Array (Address × Ixon.Constant)) : Std.HashSet Address :=
  records.foldl (fun keys row => keys.insert row.1) {}

theorem known_fold (records : List (Address × Ixon.Constant)) (initial : Std.HashSet Address) (key : Address) :
    (records.foldl (fun keys row => keys.insert row.1) initial).contains key =
      (initial.contains key || records.any (fun row => row.1 == key)) := by
  induction records generalizing initial with
  | nil => simp
  | cons row records ih =>
    rw [List.foldl_cons, ih, Std.HashSet.contains_insert, List.any_cons]
    cases initial.contains key <;> cases row.1 == key <;> cases records.any (fun row => row.1 == key) <;> rfl

theorem known_contains (records : Array (Address × Ixon.Constant)) (key : Address) :
    (known records).contains key = records.any (fun row => row.1 == key) := by
  unfold known
  rw [← Array.foldl_toList, known_fold]
  simp

theorem known_of_member (records : Array (Address × Ixon.Constant)) (key : Address) (constant : Ixon.Constant)
    (present : (key, constant) ∈ records) : (known records).contains key = true := by
  rw [known_contains, ← Array.any_toList]
  exact List.any_eq_true.mpr ⟨(key, constant), by simpa using present, by simp⟩

theorem map_missing (records : Array (Address × Ixon.Constant)) (key : Address)
    (missing : (known records).contains key = false) : (recordMap records)[key]? = none := by
  cases found : (recordMap records)[key]? with
  | none => rfl
  | some constant =>
    have present := known_of_member records key constant (map_origin records key constant found)
    rw [missing] at present
    cases present

def allRecords (records fallback : Array (Address × Ixon.Constant)) : Array (Address × Ixon.Constant) :=
  records ++ fallback.filter (fun row => !(known records).contains row.1)

theorem context_store (pins : Pins) (records : Array (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (fallback : Array (Address × Ixon.Constant)) (hint : ConstRef Address → Option Kernel.ReducibilityHint) :
    (contextOf pins records blobs fallback hint).store = storeOf records (storeOf fallback) := rfl

theorem context_index (pins : Pins) (records : Array (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (fallback : Array (Address × Ixon.Constant)) (hint : ConstRef Address → Option Kernel.ReducibilityHint) :
    (contextOf pins records blobs fallback hint).index =
      buildIndex (contextOf pins records blobs fallback hint).store pins.names (allRecords records fallback) := rfl

/-- The actual context indexes the supplied records and only unshadowed
fallback records. Each side may contain identical aliases; compatibility
between shadowed supplied/fallback records is not required. -/
theorem context_coherent (pins : Pins) (records : Array (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (fallback : Array (Address × Ixon.Constant)) (hint : ConstRef Address → Option Kernel.ReducibilityHint)
    (primaryConsistent : Consistent records) (fallbackConsistent : Consistent fallback) :
    ReaderIndexEntries.Coherent (contextOf pins records blobs fallback hint).store (allRecords records fallback) := by
  intro key constant present
  rw [context_store]
  rcases Array.mem_append.mp present with primary | extra
  · exact storeOf_coherent records (storeOf fallback) primaryConsistent key constant primary
  · obtain ⟨fallbackPresent, allowed⟩ := Array.mem_filter.mp extra
    have missing : (known records).contains key = false := by simpa using allowed
    unfold storeOf
    rw [map_missing records key missing, map_present fallback fallbackConsistent key constant fallbackPresent]
    rfl

theorem context_primary (pins : Pins) (records : Array (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (fallback : Array (Address × Ixon.Constant)) (hint : ConstRef Address → Option Kernel.ReducibilityHint)
    (consistent : Consistent records) (owner : Address) (constant : Ixon.Constant)
    (present : (owner, constant) ∈ records) :
    (contextOf pins records blobs fallback hint).store owner = some constant := by
  rw [context_store]
  exact storeOf_coherent records (storeOf fallback) consistent owner constant present

theorem consistent_map_entries (map : Map) : Consistent map.toArray := by
  intro key left right first second
  have firstLookup : map[key]? = some left := Std.HashMap.mem_toArray_iff_getElem?_eq_some.mp first
  have secondLookup : map[key]? = some right := Std.HashMap.mem_toArray_iff_getElem?_eq_some.mp second
  exact Option.some.inj (firstLookup.symm.trans secondLookup)

/-- Concrete context construction discharges the earlier store-coherence
premise for every recursor listed by a completed indexed block. -/
theorem context_grouped_lookup (pins : Pins) (records : Array (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (fallback : Array (Address × Ixon.Constant)) (hint : ConstRef Address → Option Kernel.ReducibilityHint)
    (primaryConsistent : Consistent records) (fallbackConsistent : Consistent fallback)
    (block : Address) (shape : BlockShape)
    (shapeFound : (contextOf pins records blobs fallback hint).index.blocks[block]? = some shape)
    (ref : ConstRef Address) (present : ref ∈ shape.recs) :
    ∃ entry owner constant position recursor carriers,
      (contextOf pins records blobs fallback hint).index.recs[ref]? = some entry ∧ entry.block = block ∧
      ref = .member owner position ∧ (contextOf pins records blobs fallback hint).store owner = some constant ∧
      (recursorMembers constant).find? (·.1 == position) = some (position, recursor) ∧
      analyseRecursor (contextOf pins records blobs fallback hint).store owner constant recursor =
        some (entry.motive, carriers, entry.major) := by
  rw [context_index] at shapeFound ⊢
  exact ReaderIndexEntries.grouped_lookup _ pins.names (allRecords records fallback)
    (context_coherent pins records blobs fallback hint primaryConsistent fallbackConsistent) block shape shapeFound ref present

open Ix.CompileM Ix.CompileCert.HeadWriterFrame in
/-- Inclusion of the actual compiler result in a compatible primary record
array discharges its store lookup in the production context. Index existence
remains a separate recursor-discovery obligation. -/
theorem context_compiled_order (source : InductiveVal) (environment : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) environment before = (.ok output, after))
    (pins : Pins) (records : Array (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (fallback : Array (Address × Ixon.Constant)) (hint : ConstRef Address → Option Kernel.ReducibilityHint)
    (consistent : Consistent records) (present : (output.blockAddr, output.block) ∈ records)
    (shape : BlockShape) (indexed : (contextOf pins records blobs fallback hint).index.blocks[output.blockAddr]? = some shape) :
    shape.order = #[0] :=
  ReaderIndex.compiled_order source environment before after output ran (contextOf pins records blobs fallback hint)
    pins.names (allRecords records fallback) shape (context_index pins records blobs fallback hint)
    (context_primary pins records blobs fallback hint consistent output.blockAddr output.block present) indexed

end Ix.CompileCert.ReaderStore
