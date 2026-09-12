module
public import Ix.Ixby.Aiur.Objects.Refinement
public import Ix.Aiur.Semantics.BytecodeEval

/-! Checked reconstruction of the object interpreter's concrete memory.

`ISValue` occupies six fields and `ListNode<ISValue>` eight. This module
decodes those flat layouts, including tags, scalar ranges, and compiler padding,
and reads the actual width-bucketed Lean bytecode evaluator memory.

Reconstruction checks the reachable object graph, rather than assuming a
`ClosedRanked` invariant. It has separate depth and shared node budgets, so
unfolding a shared DAG cannot silently reset the budget for each child.

This is a checked interpretation of memory, NOT a new production verifier or
an AIR soundness theorem. Successful execution still has to be proved to
establish successful reconstruction and the authenticated declaration table.
The proofs below use pure memory operations, not the imported FFI functions.
-/

public section
@[expose] section

namespace Ix.Ixby.AiurBackend.Objects.Memory

open Objects.Refinement

abbrev valueWidth : Nat := 6
abbrev cellWidth : Nat := 8
abbrev rankLimit : Nat := objectsProfile.valueDepth + objectsProfile.maxSteps

/-- No modular reduction or narrowing at the scalar interpretation boundary. -/
def fieldValue (g : Aiur.G) : Goldilocks :=
  ⟨g.n, by
    have modulus : Aiur.gSize.toNat = goldilocksModulus := by decide
    simpa only [UInt64.lt_iff_toNat_lt, modulus] using g.property⟩

def wordValue (a b c d : Aiur.G) : Nat :=
  a.n + 256 * b.n + 65536 * c.n + 16777216 * d.n

theorem word_value_exact (a b c d : Aiur.G)
    (ha : a.n < 256) (hb : b.n < 256) (hc : c.n < 256) (hd : d.n < 256) :
    (wordValue a b c d).toUInt32.toNat = wordValue a b c d := by
  have bounded : wordValue a b c d < 2 ^ 32 := by unfold wordValue; omega
  simp [Nat.mod_eq_of_lt bounded]

/-- `IBValue`: tag plus four payload fields. Applied constructors are zero
padded; a nullary constructor reference repeats its tag (`Lower.toIndex`).
Checking that padding matters for equality with constructor literals. -/
def decodeAtom : List Aiur.G → Option Atom
  | [tag, a, b, c, d] =>
    match tag.n with
    | 0 =>
      if b = 0 ∧ c = 0 ∧ d = 0 then
        if a = 0 then some (.bool false)
        else if a = 1 then some (.bool true) else none
      else none
    | 1 =>
      if a.n < 256 ∧ b.n < 256 ∧ c.n < 256 ∧ d.n < 256 then
        some (.word (wordValue a b c d).toUInt32)
      else none
    | 2 => if b = 0 ∧ c = 0 ∧ d = 0 then some (.field (fieldValue a)) else none
    | 3 => if c = 0 ∧ d = 0 then some (.ext ⟨fieldValue a, fieldValue b⟩) else none
    | 4 => if a = 4 ∧ b = 4 ∧ c = 4 ∧ d = 4 then some .erased else none
    | _ => none
  | _ => none

/-- `ISValue`: Atom has a five-field payload; Ctor has four and one zero pad.
Pointers remain full canonical field naturals, not truncated u32 addresses. -/
def decodeRef : List Aiur.G → Option Ref
  | [tag, a, b, c, d, e] =>
    match tag.n with
    | 0 => Ref.atom <$> decodeAtom [a, b, c, d, e]
    | 1 => if e = 0 then some (.ctor a.n b.n c.n d.n) else none
    | _ => none
  | _ => none

/-- A width-8 cell is either `[Cons, value..., tail]` or a tag-padded Nil.
Other data sharing this width is interpreted only when reached as an ISValues
cell; width alone does not constitute a nominal type check. -/
def decodeCell (flat : Array Aiur.G) : Option Cell :=
  match flat.toList with
  | [tag, a, b, c, d, e, f, tail] =>
    match tag.n with
    | 0 => (Cell.cons · tail.n) <$> decodeRef [a, b, c, d, e, f]
    | 1 =>
      if a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 ∧ e = 1 ∧ f = 1 ∧ tail = 1 then
        some .nil
      else none
    | _ => none
  | _ => none

/-- Width and pointer are distinct coordinates. Arbitrary pointers, duplicate
cells, and unreachable malformed/cyclic entries are permitted. -/
abbrev RawMemory := Nat → Nat → Option (Array Aiur.G)

def typedHeap (memory : RawMemory) : Heap := fun pointer =>
  memory cellWidth pointer >>= decodeCell

def bytecodeMemory (st : Aiur.Bytecode.Eval.EvalState) : RawMemory := fun width pointer =>
  match Aiur.Bytecode.Eval.memLoad st width pointer with
  | .ok flat => some flat
  | .error _ => none

theorem bytecode_heap_load (st : Aiur.Bytecode.Eval.EvalState) (pointer : Nat)
    (flat : Array Aiur.G) (cell : Cell)
    (loaded : Aiur.Bytecode.Eval.memLoad st cellWidth pointer = .ok flat)
    (decoded : decodeCell flat = some cell) :
    typedHeap (bytecodeMemory st) pointer = some cell := by
  simp [typedHeap, bytecodeMemory, loaded, decoded]

theorem bytecode_heap_load_iff (st : Aiur.Bytecode.Eval.EvalState) (pointer : Nat) (cell : Cell) :
    typedHeap (bytecodeMemory st) pointer = some cell ↔
      ∃ flat, Aiur.Bytecode.Eval.memLoad st cellWidth pointer = .ok flat ∧
        decodeCell flat = some cell := by
  cases loaded : Aiur.Bytecode.Eval.memLoad st cellWidth pointer <;>
    simp [typedHeap, bytecodeMemory, loaded]

/-- The checks needed for one constructor. The field bound is checked before
walking the spine, even if malicious metadata supplies a huge field count. -/
def checkedFields (heap : Heap) (table : Array CtorDecl)
    (index pointer count rank : Nat) : Option (CtorDecl × List Ref) := do
  if count > objectsProfile.limits.operands ∨ rank = 0 ∨ rank > rankLimit then none
  else
    let decl ← table[index]?
    if count != decl.fields then none
    else
      let fields ← readFields heap count pointer
      if rank != maxRank fields + 1 then none else some (decl, fields)

theorem checked_fields_sound {heap : Heap} {table : Array CtorDecl}
    {index pointer count rank : Nat} {decl : CtorDecl} {fields : List Ref}
    (checked : checkedFields heap table index pointer count rank = some (decl, fields)) :
    table[index]? = some decl ∧ count = decl.fields ∧
      readFields heap count pointer = some fields ∧ rank = maxRank fields + 1 := by
  unfold checkedFields at checked
  split at checked
  · simp at checked
  · obtain ⟨other, lookup, checked⟩ := Option.bind_eq_some_iff.mp checked
    split at checked
    · simp at checked
    · rename_i arity
      obtain ⟨values, read, checked⟩ := Option.bind_eq_some_iff.mp checked
      split at checked
      · simp at checked
      · rename_i rankEq
        have equal := Option.some.inj checked
        cases equal
        exact ⟨lookup, by simpa using arity, read, by simpa using rankEq⟩

theorem checked_fields_bounds {heap : Heap} {table : Array CtorDecl}
    {index pointer count rank : Nat} {decl : CtorDecl} {fields : List Ref}
    (checked : checkedFields heap table index pointer count rank = some (decl, fields)) :
    count ≤ objectsProfile.limits.operands ∧ 0 < rank ∧ rank ≤ rankLimit := by
  unfold checkedFields at checked
  split at checked
  · simp at checked
  · rename_i bounds
    omega

/-- Left-to-right traversal with one shared remaining-node budget. -/
def traverseBudget (f : Nat → Ref → Option (Value × Nat)) :
    Nat → List Ref → Option (List Value × Nat)
  | budget, [] => some ([], budget)
  | budget, ref :: rest => do
    let (value, remaining) ← f budget ref
    let (values, remaining) ← traverseBudget f remaining rest
    some (value :: values, remaining)

theorem traverse_budget_sound {f : Nat → Ref → Option (Value × Nat)}
    {relation : Ref → Value → Prop}
    (sound : ∀ budget ref value remaining, f budget ref = some (value, remaining) → relation ref value)
    {refs : List Ref} {values : List Value} {budget remaining : Nat}
    (decoded : traverseBudget f budget refs = some (values, remaining)) :
    All₂ relation refs values := by
  induction refs generalizing budget values with
  | nil =>
    simp only [traverseBudget, Option.some.injEq, Prod.mk.injEq] at decoded
    cases decoded.1
    exact .nil
  | cons ref refs ih =>
    simp only [traverseBudget] at decoded
    obtain ⟨⟨value, next⟩, first, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨⟨tail, last⟩, rest, equal⟩ := Option.bind_eq_some_iff.mp decoded
    have eq := Option.some.inj equal
    cases eq
    exact .cons (sound budget ref value next first) (ih rest)

theorem traverse_budget_le {f : Nat → Ref → Option (Value × Nat)}
    (bounded : ∀ budget ref value remaining,
      f budget ref = some (value, remaining) → remaining ≤ budget)
    {refs : List Ref} {values : List Value} {budget remaining : Nat}
    (decoded : traverseBudget f budget refs = some (values, remaining)) : remaining ≤ budget := by
  induction refs generalizing budget values with
  | nil => simp [traverseBudget] at decoded; omega
  | cons ref refs ih =>
    simp only [traverseBudget] at decoded
    obtain ⟨⟨value, next⟩, first, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    obtain ⟨⟨tail, last⟩, rest, equal⟩ := Option.bind_eq_some_iff.mp decoded
    cases Option.some.inj equal
    exact Nat.le_trans (ih rest) (bounded budget ref value next first)

/-- A diagnostic reconstruction, not a new execution rule or I/O profile.
`depth` bounds recursive calls; the shared node budget bounds DAG unfolding.
Each constructor's exact computed-rank rule is checked before its children. -/
def reconstructRef (heap : Heap) (table : Array CtorDecl) :
    Nat → Nat → Ref → Option (Value × Nat)
  | 0, _, _ => none
  | _ + 1, 0, _ => none
  | depth + 1, budget + 1, ref =>
    match ref with
    | .atom atom => some (atom.decode, budget)
    | .ctor index pointer count rank => do
      let (decl, fields) ← checkedFields heap table index pointer count rank
      let (values, remaining) ← traverseBudget (reconstructRef heap table depth) budget fields
      some (.ctor decl.id values.reverse.toArray, remaining)

theorem reconstruct_ref_sound {heap : Heap} {table : Array CtorDecl}
    {depth budget remaining : Nat} {ref : Ref} {value : Value}
    (decoded : reconstructRef heap table depth budget ref = some (value, remaining)) :
    Represents heap table ref value := by
  induction depth generalizing budget ref value remaining with
  | zero => simp [reconstructRef] at decoded
  | succ depth ih =>
    cases budget with
    | zero => simp [reconstructRef] at decoded
    | succ budget =>
      cases ref with
      | atom atom =>
        simp [reconstructRef] at decoded
        cases decoded.1
        exact .atom atom
      | ctor index pointer count rank =>
        simp only [reconstructRef] at decoded
        obtain ⟨⟨decl, fields⟩, checked, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨⟨values, rest⟩, children, equal⟩ := Option.bind_eq_some_iff.mp decoded
        have eq := Option.some.inj equal
        cases eq
        obtain ⟨declaration, arity, read, ranked⟩ := checked_fields_sound checked
        exact .ctor declaration arity read ranked
          (traverse_budget_sound (relation := Represents heap table)
            (fun _ _ _ _ h => ih h) children)

/-- Every successful call consumes at least its root node, and traversal passes
the remaining budget between siblings without replenishing it. -/
theorem reconstruct_ref_consumes {heap : Heap} {table : Array CtorDecl}
    {depth budget remaining : Nat} {ref : Ref} {value : Value}
    (decoded : reconstructRef heap table depth budget ref = some (value, remaining)) :
    remaining < budget := by
  induction depth generalizing budget ref value remaining with
  | zero => simp [reconstructRef] at decoded
  | succ depth ih =>
    cases budget with
    | zero => simp [reconstructRef] at decoded
    | succ budget =>
      cases ref with
      | atom atom => simp [reconstructRef] at decoded; omega
      | ctor index pointer count rank =>
        simp only [reconstructRef] at decoded
        obtain ⟨⟨decl, fields⟩, _, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨⟨values, rest⟩, children, equal⟩ := Option.bind_eq_some_iff.mp decoded
        cases Option.some.inj equal
        have bounded := traverse_budget_le
          (f := reconstructRef heap table depth) (fun _ _ _ _ h => Nat.le_of_lt (ih h)) children
        omega

def reconstruct (memory : RawMemory) (table : Array CtorDecl)
    (flat : Array Aiur.G) (nodes : Nat) : Option (Value × Nat) := do
  let ref ← decodeRef flat.toList
  reconstructRef (typedHeap memory) table rankLimit nodes ref

theorem reconstruct_sound {memory : RawMemory} {table : Array CtorDecl}
    {flat : Array Aiur.G} {nodes remaining : Nat} {value : Value}
    (decoded : reconstruct memory table flat nodes = some (value, remaining)) :
    ∃ ref, decodeRef flat.toList = some ref ∧ Represents (typedHeap memory) table ref value := by
  unfold reconstruct at decoded
  obtain ⟨ref, read, result⟩ := Option.bind_eq_some_iff.mp decoded
  exact ⟨ref, read, reconstruct_ref_sound result⟩

end Ix.Ixby.AiurBackend.Objects.Memory
