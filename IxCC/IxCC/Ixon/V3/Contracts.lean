import IxC.Ixon.Types.Modes
import IxCC.Ixon.Uses

/-! # Ixon v5 resource modes and binder-data types

Re-exports upstream `IxC.Ixon.Types.Modes` (`Usage`, `BinderMode`, `ResultMode`,
`AllMode`, `LetMode`, `FieldMode`, `FieldModes`, `AllocAssert`, `DefAsserts`)
under `IxCC.Ixon.V3` with unified mode accessors (`usage`, `isUnique`,
`isBorrowed`, `isErased`, `isDefault`, `binderMode`, `isBorrow`), and defines
IxCC's private copy of the binder-data section types (`BinderNode`,
`BinderBlock`, `BinderPos`) so `IxC.Address.Core`'s `_root_.Address` never
leaks into `Src` or downstream IRs. -/

namespace Ixon.BinderMode

def isErased (m : BinderMode) : Bool := m == .erased
def isDefault (m : BinderMode) : Bool := m == .many

@[simp] theorem isDefault_many : BinderMode.many.isDefault = true := rfl

end Ixon.BinderMode

namespace Ixon.ResultMode

def isDefault (r : ResultMode) : Bool := r == .shared

@[simp] theorem isDefault_shared : ResultMode.shared.isDefault = true := rfl

end Ixon.ResultMode

namespace Ixon.AllMode

def many : AllMode := {}
def erased : AllMode := { input := .erased }
def once : AllMode := { input := .once }
def unique : AllMode := { input := .unique }
def borrowed : AllMode := { input := .borrowed }

def usage (m : AllMode) : Usage := m.input.usage
def isUnique (m : AllMode) : Bool := m.input.isUnique
def isBorrowed (m : AllMode) : Bool := m.input.isBorrowed
def isErased (m : AllMode) : Bool := m.input.isErased

@[simp] theorem isDefault_many : AllMode.many.isDefault = true := rfl

end Ixon.AllMode

namespace Ixon.LetMode

def isBorrow : LetMode → Bool
  | .borrow => true
  | .value _ => false

def usage (m : LetMode) : Usage := m.binderMode.usage
def isUnique (m : LetMode) : Bool := m.binderMode.isUnique
def isBorrowed (m : LetMode) : Bool := m.binderMode.isBorrowed
def isErased (m : LetMode) : Bool := m.binderMode.isErased
def isDefault (m : LetMode) : Bool := m == .value .many

@[simp] theorem isDefault_value_many : (LetMode.value .many).isDefault = true := rfl

end Ixon.LetMode

namespace IxCC.Ixon.V3

abbrev Usage := _root_.Ixon.Usage
abbrev BinderMode := _root_.Ixon.BinderMode
abbrev ResultMode := _root_.Ixon.ResultMode
abbrev AllMode := _root_.Ixon.AllMode
abbrev LetMode := _root_.Ixon.LetMode
abbrev FieldMode := _root_.Ixon.FieldMode
abbrev FieldModes := _root_.Ixon.FieldModes
abbrev AllocAssert := _root_.Ixon.AllocAssert
abbrev DefAsserts := _root_.Ixon.DefAsserts

namespace BinderMode
export _root_.Ixon.BinderMode (many borrowed unique uniqueBorrowed once onceBorrowed erased
  ofCode? ofCode?_toCode toCode_lt isDefault_many)
end BinderMode

namespace ResultMode
export _root_.Ixon.ResultMode (shared borrowed unique uniqueBorrowed
  ofCode? ofCode?_toCode toCode_lt isDefault_shared)
end ResultMode

namespace AllMode
export _root_.Ixon.AllMode (many erased once unique borrowed
  ofCode? ofCode?_toCode toCode_lt isDefault_many)
end AllMode

namespace LetMode
export _root_.Ixon.LetMode (value borrow
  ofCode? header ofHeader? ofCode?_toCode ofHeader?_header isDefault_value_many)
end LetMode

namespace FieldMode
export _root_.Ixon.FieldMode (inherited shared ofCode? ofCode?_toCode)
end FieldMode

namespace FieldModes
export _root_.Ixon.FieldModes (inherited listed listed? ofArray listed?_toArray)
end FieldModes

namespace AllocAssert
export _root_.Ixon.AllocAssert (unrestricted noRc noAlloc ofCode? ofCode?_toCode)
end AllocAssert

namespace DefAsserts
export _root_.Ixon.DefAsserts (ofCode? ofCode?_toCode toCode_lt)
end DefAsserts

/-- One numbered node of a record's binder-data block (mirrors
`IxC.Ixon.BinderNode`). A binder's node carries both its zero-ness datum and
its `AllMode`; a share node names the sharing entry's variant. -/
inductive BinderNode where
  | never (mode : AllMode) : BinderNode
  | zero (mode : AllMode) : BinderNode
  | ifAllZero (params : Array UInt64) (mode : AllMode) : BinderNode
  | share : UInt64 → BinderNode
  | undecided (mode : AllMode) : BinderNode
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

namespace BinderNode

def TAG_NEVER : UInt8 := 0
def TAG_ZERO : UInt8 := 1
def TAG_IF_ALL_ZERO : UInt8 := 2
def TAG_SHARE : UInt8 := 3
def TAG_UNDECIDED : UInt8 := 4

/-- The node's mode: `none` at a share node. -/
def mode? : BinderNode → Option AllMode
  | .never m | .zero m | .ifAllZero _ m | .undecided m => some m
  | .share _ => none

/-- Whether the node is an undecided binder (tag 4). -/
def isUndecided : BinderNode → Bool
  | .undecided _ => true
  | _ => false

end BinderNode

/-- The binder data of one expression of a record (mirrors
`IxC.Ixon.BinderBlock`). -/
structure BinderBlock where
  shared : Bool
  index : UInt64
  variant : UInt64
  nodes : Array BinderNode
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

/-- A binder's position in a record's binder-data section (mirrors
`IxC.Ixon.BinderPos`). -/
structure BinderPos where
  shared : Bool
  index : UInt64
  variant : UInt64
  ordinal : Nat
  deriving BEq, DecidableEq, Repr, Inhabited, Hashable

end IxCC.Ixon.V3
