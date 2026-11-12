module

/-!
# Ixon resource modes

The modes a record gives its binders, its `let`s, its constructors' fields and
its definitions. Each type is exactly its legal set: no combination of fields
is excluded by a side condition. Each has a wire code, a bijection between the
type and its legal codes (`ofCode? (toCode m) = some m`; every other code
decodes to `none`), with the default at code 0. Every binder of Lean source has
the default mode, so a plain Lean record writes only zero codes.

Where the codes go on the wire:
* a `lam` or `all` binder's mode: the high five bits of the binder's node in the
  record's binder-data section (`AllMode`: the bound variable's mode and the
  mode of the result of the binder's own arrow, for a `lam` as for an `all`);
* a `let`'s mode: its header's TagN value, `nonDep + 2 · LetMode.toCode`
  (`LetMode.header`);
* a constructor's field modes: a flag bit in its first byte, then one byte per
  field (`FieldModes`);
* a definition's assertions: the high nibble of its kind and safety byte
  (`DefAsserts`; the default on a theorem).

Modes are data of the record, hashed into its address. Kernel terms carry none.
-/

@[expose] public section

namespace Ixon

/-- A binder's usage: any number of times (the default), at most once (a
function called at most once), or never at run time. -/
inductive Usage where
  | many
  | once
  | erased
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- The mode of a bound variable: a `lam` or `all` binder's input, a value
`let`'s. Usage `many` with any ownership and locality, usage `once` (shared)
with any locality, or `erased`: seven values. `many` (shared and unrestricted)
is the default.

Code: bit 0 borrowed, bit 1 unique or erased, bit 2 once or erased, so 0 to 6
in the order of the constructors; 7 (an erased binder that is borrowed) is no
mode. -/
inductive BinderMode where
  /-- Usage `many`, shared, unrestricted: the default (code 0). -/
  | many
  /-- Usage `many`, shared, lent for the binder's scope (code 1). -/
  | borrowed
  /-- Usage `many`, unaliased (code 2). -/
  | unique
  /-- Usage `many`, unaliased and lent (code 3). -/
  | uniqueBorrowed
  /-- Usage at most once, shared (code 4). -/
  | once
  /-- Usage at most once, shared and lent (code 5). -/
  | onceBorrowed
  /-- Absent at run time (code 6). -/
  | erased
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace BinderMode

def usage : BinderMode → Usage
  | .many | .borrowed | .unique | .uniqueBorrowed => .many
  | .once | .onceBorrowed => .once
  | .erased => .erased

def isUnique : BinderMode → Bool
  | .unique | .uniqueBorrowed => true
  | _ => false

def isBorrowed : BinderMode → Bool
  | .borrowed | .uniqueBorrowed | .onceBorrowed => true
  | _ => false

def toCode : BinderMode → UInt8
  | .many => 0
  | .borrowed => 1
  | .unique => 2
  | .uniqueBorrowed => 3
  | .once => 4
  | .onceBorrowed => 5
  | .erased => 6

def ofCode? : UInt8 → Option BinderMode
  | 0 => some .many
  | 1 => some .borrowed
  | 2 => some .unique
  | 3 => some .uniqueBorrowed
  | 4 => some .once
  | 5 => some .onceBorrowed
  | 6 => some .erased
  | _ => none

@[simp] theorem ofCode?_toCode (m : BinderMode) : ofCode? m.toCode = some m := by
  cases m <;> rfl

theorem toCode_lt (m : BinderMode) : m.toCode < 7 := by
  cases m <;> decide

end BinderMode

/-- The mode of a binder's result (the result of its arrow: an `all`'s
codomain, a `lam`'s body): its ownership and locality. `shared` (and
unrestricted) is the default. Code: bit 0 borrowed, bit 1 unique, as the low
two bits of a `BinderMode` of usage `many`. -/
inductive ResultMode where
  /-- Shared, unrestricted: the default (code 0). -/
  | shared
  /-- Shared, lent (code 1). -/
  | borrowed
  /-- Unaliased (code 2). -/
  | unique
  /-- Unaliased and lent (code 3). -/
  | uniqueBorrowed
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace ResultMode

def isUnique : ResultMode → Bool
  | .unique | .uniqueBorrowed => true
  | _ => false

def isBorrowed : ResultMode → Bool
  | .borrowed | .uniqueBorrowed => true
  | _ => false

def toCode : ResultMode → UInt8
  | .shared => 0
  | .borrowed => 1
  | .unique => 2
  | .uniqueBorrowed => 3

def ofCode? : UInt8 → Option ResultMode
  | 0 => some .shared
  | 1 => some .borrowed
  | 2 => some .unique
  | 3 => some .uniqueBorrowed
  | _ => none

@[simp] theorem ofCode?_toCode (m : ResultMode) : ofCode? m.toCode = some m := by
  cases m <;> rfl

theorem toCode_lt (m : ResultMode) : m.toCode < 4 := by
  cases m <;> decide

end ResultMode

/-- The mode of a `lam` or `all` binder: its bound variable's (`input`) and its
arrow's result's (`result`), 7 × 4 = 28 values. A `lam`'s result is the result
mode of its own arrow, so a definition's `lam` telescope agrees with its type's
`all` telescope node for node. Code (five bits): the input's code, plus 8 times
the result's; the codes whose low three bits are 7 are no mode. -/
structure AllMode where
  input : BinderMode := .many
  result : ResultMode := .shared
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace AllMode

def toCode (m : AllMode) : UInt8 :=
  m.input.toCode ||| (m.result.toCode <<< 3)

def ofCode? (c : UInt8) : Option AllMode :=
  if c ≥ 32 then none else do
    let input ← BinderMode.ofCode? (c &&& 7)
    let result ← ResultMode.ofCode? (c >>> 3)
    return ⟨input, result⟩

@[simp] theorem ofCode?_toCode (m : AllMode) : ofCode? m.toCode = some m := by
  rcases m with ⟨input, result⟩
  cases input <;> cases result <;> rfl

theorem toCode_lt (m : AllMode) : m.toCode < 32 := by
  rcases m with ⟨input, result⟩
  cases input <;> cases result <;> decide

/-- Whether `m` is the default mode (code 0). -/
def isDefault (m : AllMode) : Bool := m == {}

end AllMode

/-- The mode of a `let`: a value `let` binds its variable at a `BinderMode`,
and a `borrow` lends a shared value for the `let`'s body (its variable is
`borrowed`). Eight values, all legal codes 0 to 7: a value `let`'s code is its
mode's, a `borrow`'s is 7. `value .many` is the default. -/
inductive LetMode where
  | value (mode : BinderMode)
  | borrow
  deriving DecidableEq, Repr, Hashable

instance : Inhabited LetMode := ⟨.value .many⟩

namespace LetMode

/-- The mode of the bound variable. -/
def binderMode : LetMode → BinderMode
  | .value m => m
  | .borrow => .borrowed

def toCode : LetMode → UInt8
  | .value m => m.toCode
  | .borrow => 7

def ofCode? (c : UInt8) : Option LetMode :=
  if c == 7 then some .borrow else LetMode.value <$> BinderMode.ofCode? c

@[simp] theorem ofCode?_toCode (m : LetMode) : ofCode? m.toCode = some m := by
  rcases m with m | _
  · cases m <;> rfl
  · rfl

/-- The `let` header's TagN value: `nonDep` in bit 0, the mode's code above
it, so below 16; a default `let`'s is 0 or 1 and its header one byte. -/
def header (nonDep : Bool) (m : LetMode) : UInt64 :=
  (if nonDep then (1 : UInt64) else 0) ||| (m.toCode.toUInt64 <<< 1)

def ofHeader? (h : UInt64) : Option (Bool × LetMode) :=
  if h ≥ 16 then none else do
    let m ← ofCode? (h >>> 1).toUInt8
    return (h &&& 1 == 1, m)

@[simp] theorem ofHeader?_header (nonDep : Bool) (m : LetMode) :
    ofHeader? (header nonDep m) = some (nonDep, m) := by
  rcases m with m | _
  · cases nonDep <;> cases m <;> first | rfl | decide
  · cases nonDep <;> first | rfl | decide

end LetMode

/-- The mode of a constructor's field: `inherited` (the default: owned or lent
with its container) or `shared` (an ordinary counted reference, excused from
its container's uniqueness). An erased field is erased by its binder's mode in
the constructor's type, and has no field mode of its own. -/
inductive FieldMode where
  | inherited
  | shared
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace FieldMode

def toCode : FieldMode → UInt8
  | .inherited => 0
  | .shared => 1

def ofCode? : UInt8 → Option FieldMode
  | 0 => some .inherited
  | 1 => some .shared
  | _ => none

@[simp] theorem ofCode?_toCode (m : FieldMode) : ofCode? m.toCode = some m := by
  cases m <;> rfl

end FieldMode

/-- The field modes of a constructor with `n` fields: every field `inherited`
(the default, no bytes on the wire), or exactly `n` modes of which at least one
is `shared` (the constructor's flag bit set, then one byte per field). -/
inductive FieldModes (n : Nat) where
  | inherited
  | listed (modes : Vector FieldMode n) (someShared : modes.toArray.any (· == .shared) = true)

namespace FieldModes

variable {n : Nat}

instance : Inhabited (FieldModes n) := ⟨.inherited⟩

/-- The listed modes; none for `inherited`. -/
def toArray : FieldModes n → Array FieldMode
  | .inherited => #[]
  | .listed modes _ => modes.toArray

/-- The mode of field `i` (`inherited` past the last field). -/
def get (m : FieldModes n) (i : Nat) : FieldMode :=
  m.toArray.getD i .inherited

/-- Whether every field is `inherited` (the flag bit clear). -/
def isInherited : FieldModes n → Bool
  | .inherited => true
  | .listed .. => false

/-- `modes` as the field modes of a constructor with `n` fields: `listed` when
there are `n` of them and one is `shared`. -/
def listed? (modes : Array FieldMode) : Option (FieldModes n) :=
  if h : modes.size = n then
    if hs : modes.any (· == .shared) = true then some (.listed ⟨modes, h⟩ hs) else none
  else none

/-- `modes` as field modes: `listed` when there are `n` of them and one is
`shared`, otherwise `inherited`. -/
def ofArray (modes : Array FieldMode) : FieldModes n :=
  (listed? modes).getD .inherited

/-- Listed modes read back from their array. -/
theorem listed?_toArray (modes : FieldModes n) (h : modes.isInherited = false) :
    listed? modes.toArray = some modes := by
  cases modes with
  | inherited => cases h
  | listed v hs =>
    show listed? v.toArray = some (.listed v hs)
    unfold listed?
    split
    · split
      · rfl
      · rename_i hs'; exact absurd hs hs'
    · rename_i h; exact absurd v.size_toArray h

instance : BEq (FieldModes n) where
  beq a b := a.toArray == b.toArray

instance : Repr (FieldModes n) where
  reprPrec m _ := match m with
    | .inherited => Std.Format.text "FieldModes.inherited"
    | .listed modes _ => Std.Format.text "FieldModes.listed " ++ repr modes.toArray

end FieldModes

/-- What a definition asserts about its allocation: nothing (the default), no
reference-count operation, or no allocation at all (which implies no
reference-count operation). -/
inductive AllocAssert where
  | unrestricted
  | noRc
  | noAlloc
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace AllocAssert

def toCode : AllocAssert → UInt8
  | .unrestricted => 0
  | .noRc => 1
  | .noAlloc => 2

def ofCode? : UInt8 → Option AllocAssert
  | 0 => some .unrestricted
  | 1 => some .noRc
  | 2 => some .noAlloc
  | _ => none

@[simp] theorem ofCode?_toCode (a : AllocAssert) : ofCode? a.toCode = some a := by
  cases a <;> rfl

end AllocAssert

/-- A definition's assertions: its allocation, and whether its call graph has
bounded stack depth. Six values; the default asserts nothing. Code (four bits):
the allocation's code, plus 4 for a bounded stack; a code of 8 or more, or an
allocation code of 3, is no `DefAsserts`. A theorem asserts nothing. -/
structure DefAsserts where
  alloc : AllocAssert := .unrestricted
  boundedStack : Bool := false
  deriving DecidableEq, Repr, Inhabited, Hashable

namespace DefAsserts

def toCode (a : DefAsserts) : UInt8 :=
  a.alloc.toCode ||| (if a.boundedStack then 4 else 0)

def ofCode? (c : UInt8) : Option DefAsserts :=
  if c ≥ 8 then none else do
    let alloc ← AllocAssert.ofCode? (c &&& 3)
    return ⟨alloc, c &&& 4 == 4⟩

@[simp] theorem ofCode?_toCode (a : DefAsserts) : ofCode? a.toCode = some a := by
  rcases a with ⟨alloc, boundedStack⟩
  cases alloc <;> cases boundedStack <;> rfl

theorem toCode_lt (a : DefAsserts) : a.toCode < 8 := by
  rcases a with ⟨alloc, boundedStack⟩
  cases alloc <;> cases boundedStack <;> decide

end DefAsserts

end Ixon

end
