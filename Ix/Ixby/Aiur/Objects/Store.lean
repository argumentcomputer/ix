module
public import Ix.Ixby.Aiur.Objects.Memory
import all Ix.IndexMap

/-! Preservation under the Lean bytecode evaluator's actual immutable stores.

These proofs use the invariants carried by `IndexMap`; they do not assume
fresh pointers or injective allocation. A content-deduplicating store either
returns an existing cell or appends a new one in its width bucket.

This is a memory-operation theorem, not yet a theorem about every bytecode
transition or about the AIR memory argument. -/

public section
@[expose] section

namespace Ix.Ixby.AiurBackend.Objects.Store

open Objects.Refinement Objects.Memory Aiur.Bytecode.Eval

private theorem index_key_self {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : IndexMap α β) (a : α) (b : β) :
    (m.insert a b).getByKey a = some b := by
  unfold IndexMap.insert
  split <;> simp_all [IndexMap.getByKey]

private theorem index_key_other {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : IndexMap α β) (a c : α) (b : β)
    (different : a ≠ c) : (m.insert a b).getByKey c = m.getByKey c := by
  unfold IndexMap.insert
  split
  · rename_i lookup
    cases old : m.indices[c]? with
    | none => simp [IndexMap.getByKey, Std.HashMap.getElem?_insert, old, different]
    | some index =>
      have bound := (m.validIndices c old).1
      simp [IndexMap.getByKey, Std.HashMap.getElem?_insert, Array.getElem?_push,
        old, different, bound, Nat.ne_of_lt bound]
  · rename_i inserted lookup
    cases old : m.indices[c]? with
    | none => simp [IndexMap.getByKey, old]
    | some index =>
      have bound := (m.validIndices c old).1
      have distinct : inserted ≠ index := by
        intro same
        subst index
        have first := eq_of_beq (m.validIndices a lookup).2
        have second := eq_of_beq (m.validIndices c old).2
        exact different (first.symm.trans second)
      simp [IndexMap.getByKey, old, bound, distinct]

private theorem index_append_old {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : IndexMap α β) (a : α) (b : β)
    (fresh : m.getIdxOf a = none) {index : Nat} {pair : α × β}
    (old : m.getByIdx index = some pair) :
    (m.insert a b).getByIdx index = some pair := by
  have bound : index < m.pairs.size := by
    exact (Array.getElem?_eq_some_iff.mp old).1
  unfold IndexMap.insert
  split
  · simpa [IndexMap.getByIdx, Array.getElem?_push, bound, Nat.ne_of_lt bound] using old
  · rename_i inserted present
    have equal := present.symm.trans fresh
    cases equal

private theorem index_append_new {α β : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : IndexMap α β) (a : α) (b : β)
    (fresh : m.getIdxOf a = none) :
    (m.insert a b).getByIdx m.size = some (a, b) := by
  unfold IndexMap.insert
  split
  · simp [IndexMap.getByIdx, IndexMap.size]
  · rename_i inserted present
    have equal := present.symm.trans fresh
    cases equal

private theorem index_present {α : Type} [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α] (m : IndexMap α Unit) (a : α) {index : Nat}
    (present : m.getIdxOf a = some index) : m.getByIdx index = some (a, ()) := by
  have valid := m.validIndices a present
  rw [IndexMap.getByIdx, Array.getElem?_eq_some_iff]
  refine ⟨valid.1, ?_⟩
  apply Prod.ext
  · exact eq_of_beq valid.2
  · exact Subsingleton.elim _ _

/-- The actual store never changes a previously readable cell, including cells
in its own width bucket. Equal contents may reuse an existing address. -/
theorem mem_store_preserves (st : EvalState) (stored : Array Aiur.G)
    {width pointer : Nat} {flat : Array Aiur.G}
    (loaded : memLoad st width pointer = .ok flat) :
    memLoad (memStore st stored).1 width pointer = .ok flat := by
  unfold memStore
  dsimp only
  split
  · exact loaded
  · rename_i fresh
    unfold memLoad at loaded ⊢
    by_cases same : stored.size = width
    · subst width
      rw [index_key_self]
      cases bucket : st.memory.getByKey stored.size with
      | none => simp [bucket] at loaded
      | some cells =>
        simp only [bucket, Option.getD_some] at fresh ⊢
        have absent : cells.getIdxOf stored = none := by
          cases found : cells.getIdxOf stored with
          | none => rfl
          | some index => exact False.elim (fresh index found)
        cases found : cells.getByIdx pointer with
        | none => simp [bucket, found] at loaded
        | some pair =>
          have kept := index_append_old cells stored () absent found
          simp [kept]
          simpa [bucket, found] using loaded
    · rw [index_key_other _ _ _ _ same]
      exact loaded

/-- The address returned by an actual store reads back exactly the stored
array at its own width, without a fresh-allocation premise. -/
theorem mem_store_load (st : EvalState) (flat : Array Aiur.G) :
    memLoad (memStore st flat).1 flat.size (memStore st flat).2 = .ok flat := by
  unfold memStore
  dsimp only
  split
  · rename_i index present
    unfold memLoad
    cases bucket : st.memory.getByKey flat.size with
    | none => simp [bucket, IndexMap.getIdxOf, default] at present
    | some cells =>
      simp only [bucket, Option.getD_some] at present ⊢
      rw [index_present cells flat present]
  · rename_i fresh
    have absent : ((st.memory.getByKey flat.size).getD default).getIdxOf flat = none := by
      cases found : ((st.memory.getByKey flat.size).getD default).getIdxOf flat with
      | none => rfl
      | some index => exact False.elim (fresh index found)
    unfold memLoad
    rw [index_key_self]
    dsimp only
    rw [index_append_new _ _ _ absent]

/-- Number of allocated cells at one exact width. Content-deduplicated stores
may reuse a cell; they increase this count by at most one. -/
def bucketSize (st : EvalState) (width : Nat) : Nat :=
  ((st.memory.getByKey width).getD default).size

theorem mem_store_bounds (st : EvalState) (flat : Array Aiur.G) :
    (memStore st flat).2 ≤ bucketSize st flat.size ∧
      bucketSize (memStore st flat).1 flat.size ≤ bucketSize st flat.size + 1 := by
  unfold memStore
  dsimp only
  split
  · rename_i index present
    exact ⟨Nat.le_of_lt (((st.memory.getByKey flat.size).getD default).validIndices flat present).1,
      Nat.le_succ _⟩
  · refine ⟨Nat.le_refl _, ?_⟩
    simp only [bucketSize, index_key_self, Option.getD_some]
    unfold IndexMap.size IndexMap.insert
    split <;> simp

theorem mem_store_io (st : EvalState) (flat : Array Aiur.G) :
    (memStore st flat).1.ioBuffer = st.ioBuffer := by
  unfold memStore
  dsimp only
  split <;> rfl

/-- A store cannot allocate in a different width bucket. -/
theorem mem_store_other_bucket (st : EvalState) (flat : Array Aiur.G) (width : Nat)
    (different : flat.size ≠ width) :
    bucketSize (memStore st flat).1 width = bucketSize st width := by
  unfold memStore
  dsimp only
  split
  · rfl
  · simp only [bucketSize, index_key_other _ _ _ _ different]

/-- Extensional preservation of all successfully decoded cells. Unreachable
malformed cells do not have to become well-typed for this relation to hold. -/
def Extends (before after : Heap) : Prop :=
  ∀ pointer cell, before pointer = some cell → after pointer = some cell

theorem store_extends_heap (st : EvalState) (flat : Array Aiur.G) :
    Extends (typedHeap (bytecodeMemory st))
      (typedHeap (bytecodeMemory (memStore st flat).1)) := by
  intro pointer cell old
  obtain ⟨values, loaded, decoded⟩ := (bytecode_heap_load_iff st pointer cell).mp old
  exact bytecode_heap_load _ pointer values cell (mem_store_preserves st flat loaded) decoded

theorem read_fields_extends {before after : Heap} (extension : Extends before after)
    {count pointer : Nat} {fields : List Ref}
    (read : readFields before count pointer = some fields) :
    readFields after count pointer = some fields := by
  induction count generalizing pointer fields with
  | zero =>
    cases loaded : before pointer with
    | none => simp [readFields, loaded] at read
    | some cell =>
      cases cell <;> simp_all [readFields, extension pointer _ loaded]
  | succ count ih =>
    cases loaded : before pointer with
    | none => simp [readFields, loaded] at read
    | some cell =>
      cases cell with
      | nil => simp [readFields, loaded] at read
      | cons value tail =>
        cases rest : readFields before count tail with
        | none => simp [readFields, loaded, rest] at read
        | some values =>
          simp [readFields, loaded, rest] at read
          subst fields
          simp [readFields, extension pointer _ loaded, ih rest]

private theorem all₂_map_mem {α β : Type} {p q : α → β → Prop} {xs : List α} {ys : List β}
    (map : ∀ x ∈ xs, ∀ y, p x y → q x y) (related : All₂ p xs ys) : All₂ q xs ys := by
  induction related with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (map _ (by simp) _ head) (ih (fun x mem y h => map x (by simp [mem]) y h))

theorem represents_extends {before after : Heap} {table : Array CtorDecl}
    (extension : Extends before after) {ref : Ref} {value : Value}
    (represented : Represents before table ref value) : Represents after table ref value := by
  have go : ∀ n ref value, ref.rank = n → Represents before table ref value →
      Represents after table ref value := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro ref value height represented
      cases represented with
      | atom atom => exact .atom atom
      | @ctor index pointer count rank decl fields values declaration arity read ranked children =>
        refine .ctor declaration arity (read_fields_extends extension read) ranked ?_
        apply all₂_map_mem (related := children)
        intro child mem value represented
        have smaller : child.rank < n := by
          have := rank_le_max mem
          simp only [Ref.rank] at height
          omega
        exact ih child.rank smaller child value rfl represented
  exact go ref.rank ref value rfl represented

theorem store_preserves_representation (st : EvalState) (stored : Array Aiur.G)
    {table : Array CtorDecl} {ref : Ref} {value : Value}
    (represented : Represents (typedHeap (bytecodeMemory st)) table ref value) :
    Represents (typedHeap (bytecodeMemory (memStore st stored).1)) table ref value :=
  represents_extends (store_extends_heap st stored) represented

theorem checked_fields_extends {before after : Heap} {table : Array CtorDecl}
    (extension : Extends before after) {index pointer count rank : Nat}
    {decl : CtorDecl} {fields : List Ref}
    (checked : checkedFields before table index pointer count rank = some (decl, fields)) :
    checkedFields after table index pointer count rank = some (decl, fields) := by
  obtain ⟨lookup, arity, read, ranked⟩ := checked_fields_sound checked
  obtain ⟨countBound, positive, rankBound⟩ := checked_fields_bounds checked
  have guard : ¬ (count > objectsProfile.limits.operands ∨ rank = 0 ∨ rank > rankLimit) := by omega
  simp only [checkedFields, if_neg guard, lookup]
  simp [← arity, read_fields_extends extension read, ranked]

private theorem traverse_preserves {f g : Nat → Ref → Option (Value × Nat)}
    (preserve : ∀ budget ref value remaining,
      f budget ref = some (value, remaining) → g budget ref = some (value, remaining))
    {refs : List Ref} {values : List Value} {budget remaining : Nat}
    (decoded : traverseBudget f budget refs = some (values, remaining)) :
    traverseBudget g budget refs = some (values, remaining) := by
  induction refs generalizing budget values with
  | nil => exact decoded
  | cons ref refs ih =>
    simp only [traverseBudget] at decoded
    obtain ⟨⟨value, next⟩, first, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨⟨tail, last⟩, rest, equal⟩ := Option.bind_eq_some_iff.mp decoded
    cases Option.some.inj equal
    simp [traverseBudget, preserve _ _ _ _ first, ih rest]

theorem reconstruct_ref_extends {before after : Heap} {table : Array CtorDecl}
    (extension : Extends before after) {depth budget remaining : Nat} {ref : Ref} {value : Value}
    (decoded : reconstructRef before table depth budget ref = some (value, remaining)) :
    reconstructRef after table depth budget ref = some (value, remaining) := by
  induction depth generalizing budget ref value remaining with
  | zero => simp [reconstructRef] at decoded
  | succ depth ih =>
    cases budget with
    | zero => simp [reconstructRef] at decoded
    | succ budget =>
      cases ref with
      | atom atom => exact decoded
      | ctor index pointer count rank =>
        simp only [reconstructRef] at decoded
        obtain ⟨⟨decl, fields⟩, checked, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨⟨values, rest⟩, children, equal⟩ := Option.bind_eq_some_iff.mp decoded
        cases Option.some.inj equal
        have kept := traverse_preserves (g := reconstructRef after table depth)
          (fun _ _ _ _ h => ih h) children
        simp [reconstructRef, checked_fields_extends extension checked, kept]

theorem store_preserves_reconstruction (st : EvalState) (stored : Array Aiur.G)
    {table : Array CtorDecl} {flat : Array Aiur.G} {nodes remaining : Nat} {value : Value}
    (decoded : reconstruct (bytecodeMemory st) table flat nodes = some (value, remaining)) :
    reconstruct (bytecodeMemory (memStore st stored).1) table flat nodes = some (value, remaining) := by
  unfold reconstruct at decoded ⊢
  obtain ⟨ref, read, decoded⟩ := Option.bind_eq_some_iff.mp decoded
  simp [read, reconstruct_ref_extends (store_extends_heap st stored) decoded]

/-- Exposing a natural memory address as a field requires an explicit bound.
The raw store theorem does not silently assume this conversion is injective. -/
theorem stored_field_pointer (st : EvalState) (flat : Array Aiur.G)
    (bounded : (memStore st flat).2 < goldilocksModulus) :
    memLoad (memStore st flat).1 flat.size (Aiur.G.ofNat (memStore st flat).2).n = .ok flat := by
  rw [field_of_nat_exact _ bounded]
  exact mem_store_load st flat

/-- A newly stored Cons cell extends an existing reversed field spine. -/
theorem stored_cons_fields (st : EvalState) (flat : Array Aiur.G) (width : flat.size = cellWidth)
    {head : Ref} {tail count : Nat} {fields : List Ref}
    (decoded : decodeCell flat = some (.cons head tail))
    (read : readFields (typedHeap (bytecodeMemory st)) count tail = some fields) :
    readFields (typedHeap (bytecodeMemory (memStore st flat).1)) (count + 1) (memStore st flat).2 =
      some (head :: fields) := by
  have loaded := mem_store_load st flat
  rw [width] at loaded
  have cell := bytecode_heap_load _ _ flat (.cons head tail) loaded decoded
  simp [readFields, cell, read_fields_extends (store_extends_heap st flat) read]

/-- Construction from a stored field spine preserves all children's logical
meanings. This is a concrete store contract; connecting the complete compiled
`is_make` call and its field-valued output is a separate obligation. -/
theorem construct_stored_fields (st : EvalState) (flat : Array Aiur.G) (width : flat.size = cellWidth)
    {table : Array CtorDecl} {index count tail : Nat} {decl : CtorDecl}
    {head : Ref} {fields : List Ref} {values : List Value}
    (decoded : decodeCell flat = some (.cons head tail))
    (read : readFields (typedHeap (bytecodeMemory st)) count tail = some fields)
    (lookup : table[index]? = some decl) (arity : count + 1 = decl.fields)
    (children : All₂ (Represents (typedHeap (bytecodeMemory st)) table) (head :: fields) values) :
    Represents (typedHeap (bytecodeMemory (memStore st flat).1)) table
      (makeRef index (memStore st flat).2 (head :: fields)) (.ctor decl.id values.reverse.toArray) := by
  apply construct_represents lookup
  · simpa [read_fields_length read] using arity
  · simpa [read_fields_length read] using stored_cons_fields st flat width decoded read
  · exact all₂_map_mem (fun _ _ _ h => store_preserves_representation st flat h) children

/-- The preservation result applies to an actual successful bytecode Store
instruction, including its register update, not just the memory helper. -/
theorem eval_store_preserves_representation (toplevel : Aiur.Bytecode.Toplevel) (fuel : Nat)
    (indices : Array Aiur.Bytecode.ValIdx) (before after : EvalState)
    {table : Array CtorDecl} {ref : Ref} {value : Value}
    (executed : Aiur.Bytecode.Eval.evalOp toplevel fuel (.store indices) before = .ok after)
    (represented : Represents (typedHeap (bytecodeMemory before)) table ref value) :
    Represents (typedHeap (bytecodeMemory after)) table ref value := by
  cases read : readIdxs before indices with
  | error error => simp [Aiur.Bytecode.Eval.evalOp, read, Bind.bind, Except.bind] at executed
  | ok flat =>
    simp [Aiur.Bytecode.Eval.evalOp, read, Bind.bind, Except.bind] at executed
    cases executed
    exact store_preserves_representation before flat represented

end Ix.Ixby.AiurBackend.Objects.Store
