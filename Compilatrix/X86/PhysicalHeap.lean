import Compilatrix.X86.PhysicalScalar

/-! Syntax and slot selection for the bounded leaf-constructor CFG fragment.
Values and credits use separate fixed ranges in the existing 32-word frame.
The last twelve slots stage simultaneous block-edge copies. Constructor
fields are exact Word Nats; owning constructor values may cross direct calls.
The selector never admits a retain of a constructor or a borrowed parameter.
-/

namespace Compilatrix.X86.PhysicalHeap
open Compilatrix.Ixon (Address Owned)

def maxValues : Nat := 16
def maxCredits : Nat := 4
def maxEdge : Nat := 12
def creditBase : Nat := 16
def scratchBase : Nat := 20
def maxConstructors : Nat := 32

inductive Kind where
  | scalar
  | node
  | erased
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Kind.owners : Kind → Nat | .node => 1 | _ => 0

structure Scope where
  values : Array (Option Kind) := #[]
  credits : Array (Option IxIR2.LayoutId) := #[]
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Scope.initial (parameters : Array Kind) : Scope := ⟨parameters.map some, #[]⟩

def Scope.finished (scope : Scope) : Bool :=
  scope.values.all (· != some .node) && scope.credits.all Option.isNone

def Scope.bounded (scope : Scope) : Bool := scope.values.size ≤ maxValues && scope.credits.size ≤ maxCredits

def Scope.peek (scope : Scope) : IxIR2.Atom → Except String (Kind × Scalar.Atom)
  | .reg index => do
      let some (some kind) := scope.values[index]? | throw "heap CFG operand is unavailable"
      return (kind, .var index)
  | .lit (.nat number) => do
      let some word := ExactNat.encode number | throw "heap CFG Nat literal exceeds Word"
      return (.scalar, .constant word)
  | .erased => .ok (.erased, .constant 0)
  | _ => throw "heap CFG operand is outside the Nat/constructor fragment"

def Scope.take (scope : Scope) (source : IxIR2.Atom) : Except String (Kind × Scalar.Atom × Scope) := do
  let (kind, operand) ← scope.peek source
  match kind, source with
  | .node, .reg index => return (kind, operand, { scope with values := scope.values.setIfInBounds index none })
  | _, _ => return (kind, operand, scope)

def Scope.scalar (scope : Scope) (source : IxIR2.Atom) : Except String Scalar.Atom := do
  let (.scalar, operand) ← scope.peek source | throw "heap CFG constructor field or scalar operation has a heap operand"
  return operand

def Scope.node (scope : Scope) (source : IxIR2.Atom) : Except String Scalar.Atom := do
  let (.node, operand) ← scope.peek source | throw "heap CFG constructor operation has a scalar operand"
  return operand

def Scope.pushValue (scope : Scope) (kind : Kind) : Except String Scope :=
  if scope.values.size < maxValues then .ok { scope with values := scope.values.push (some kind) }
  else .error "heap CFG value slots exceed 16"

def Scope.pushFields (scope : Scope) (count : Nat) : Except String Scope :=
  if scope.values.size + count ≤ maxValues then
    .ok { scope with values := scope.values ++ Array.replicate count (some .scalar) }
  else .error "heap CFG destructuring exceeds the value slots"

def Scope.pushCredit (scope : Scope) (layout : IxIR2.LayoutId) : Except String Scope :=
  if scope.credits.size < maxCredits then .ok { scope with credits := scope.credits.push (some layout) }
  else .error "heap CFG credit slots exceed four"

def Scope.takeCredit (scope : Scope) (index : Nat) : Except String (IxIR2.LayoutId × Scope) := do
  let some (some layout) := scope.credits[index]? | throw "heap CFG credit is unavailable"
  return (layout, { scope with credits := scope.credits.setIfInBounds index none })

structure Constructor where
  cid : IxIR2.CtorId
  schema : IxIR2.CtorSchema
  tag : Word
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

abbrev Schemas := Owned → IxIR2.CtorId → Option IxIR2.CtorSchema

def constructor (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (world : Owned) (cid : IxIR2.CtorId) : Except String Constructor := do
  let some schema := schemas world cid | throw "heap CFG constructor schema is missing"
  if schema.fields.size > 2 then throw "heap CFG constructor has more than two fields"
  let some index := constructors.findIdx? (· == cid) | throw "heap CFG constructor tag is missing"
  if index >= maxConstructors then throw "heap CFG constructor tags exceed 32"
  return { cid, schema, tag := UInt64.ofNat (index + 2) }

/-- Operations name actual stack slots. A reservation writes its fields into
the appended value slots and its pointer into the separate credit range. -/
inductive Primitive where
  | nop
  | move (destination : Nat) (source : Scalar.Atom)
  | alloc (world : Owned) (ctor : Constructor) (fields : Array Scalar.Atom) (destination : Nat)
  | fetch (source : Scalar.Atom) (field destination : Nat)
  | reserve (world : Owned) (ctor : Constructor) (source : Scalar.Atom) (fields credit : Nat)
  | reuse (world : Owned) (ctor : Constructor) (credit : Nat) (fields : Array Scalar.Atom) (destination : Nat)
  | release (world : Owned) (source : Scalar.Atom)
  | discard (credit : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Primitive.allocations : Primitive → Nat | .alloc .. => 1 | _ => 0


inductive CopySource where
  | atom (source : Scalar.Atom)
  | predecessor (source : Scalar.Atom)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Copy where
  source : CopySource
  destination : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Transfer where
  copies : Array Copy
  scope : Scope
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def capAccepts (cap : IxIR2.ValueCap) (kind : Kind) : Bool :=
  match cap with
  | .scalar => kind != .node
  | .owned _ => true
  | .borrowed .. => false

def creditAccepts (cap : IxIR2.CreditCap) (layout : IxIR2.LayoutId) : Bool :=
  match cap with
  | .required actual | .optional actual => actual == layout

end Compilatrix.X86.PhysicalHeap
