module
public import Std
public import Ix.Ixby.Goldilocks

/-!
# IxBy functional bytecode: logical instruction set

An unfrozen semantic model, not a byte encoding or a proving circuit. Function,
block, and local indices are mathematical naturals, not machine words. Calls
and immutable values are explicit; native ownership, mutable RAM, and physical
pointer identity are absent. See docs/Ixby.md and the local implementation plan.
-/

public section
@[expose] section

namespace Ix.Ixby

abbrev FunctionId := Nat
abbrev BlockId := Nat
abbrev Local := Nat
abbrev Constructor := Nat

/-- Logical constructor identity: declaration/block digest, inductive member,
and constructor tag. This fixed-width name does not compute or authenticate a
hash and commits to no byte order. Its source correspondence is a compiler
obligation, not an assumption made by the evaluator. -/
structure CtorId where
  block : Fin (2 ^ 256)
  member : Nat := 0
  tag : Nat := 0
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Scalars have distinct tags. Nats are unbounded mathematical naturals;
Bool is a target scalar representation, not an implicit source constructor
equivalence. Word/field arithmetic uses separate tags and explicit conversions;
it never changes the meaning of Nat operations. Bytes are not UTF-8 strings.
Word32 is a scalar value, not an address, mutable register, or a requirement
to lower functional control and objects into a word machine. -/
inductive Scalar where
  | nat (value : Nat)
  | str (value : String)
  | bool (value : Bool)
  | word32 (value : UInt32)
  | field (value : Goldilocks)
  | extField (value : ExtGoldilocks)
  | bytes (value : Array UInt8)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Constructor fields and partially applied function captures are immutable.
A PAP names a function in this program and supplies strictly fewer arguments
than its arity. Input validation and construction check these invariants.
Object equality/pointer identity is not a guest instruction. -/
inductive Value where
  | scalar (value : Scalar)
  | ctor (id : CtorId) (fields : Array Value)
  | pap (function : FunctionId) (captured : Array Value)
  | erased
  deriving BEq, Repr, Inhabited

inductive Operand where
  /-- Absolute slot in the current immutable local frame. Binding appends a
  slot; it never renumbers or overwrites an existing local. -/
  | local (slot : Local)
  | literal (value : Scalar)
  | erased
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Closed reference primitives. Comparisons produce Bool scalars; Nat
subtraction truncates at zero, n / 0 = 0, and n % 0 = n. String length counts Unicode
scalar values, not UTF-8 bytes. These are semantic operations, not claims of
constant proving cost. Hashing means unkeyed BLAKE3 with 32 output bytes.
Field inverses map zero to zero; byte/field decoding is strict, not modular. -/
inductive Primitive where
  | natAdd | natSub | natMul | natDiv | natMod | natEq | natLt
  | strAppend | strLength | strEq
  | word32Add | word32Sub | word32Mul | word32And | word32Or | word32Xor
  | word32Shl | word32Shr | word32Rotr | word32Eq | word32Lt
  | word32ToBytes | bytesToWord32 | word32ToField
  | fieldAdd | fieldSub | fieldMul | fieldInverse | fieldEq
  | fieldToBytes | bytesToField
  | extAdd | extSub | extMul | extInverse | extEq | extPack | extFst | extSnd
  | bytesLength | bytesGet | bytesAppend | bytesSlice | bytesEq | blake3
  deriving BEq, DecidableEq, Repr, Inhabited

def Primitive.arity : Primitive → Nat
  | .strLength | .word32ToBytes | .bytesToWord32 | .word32ToField
  | .fieldInverse | .fieldToBytes | .bytesToField | .extInverse | .extFst | .extSnd
  | .bytesLength | .blake3 => 1
  | .bytesSlice => 3
  | _ => 2

inductive Op where
  | copy (value : Operand)
  | primitive (op : Primitive) (args : List Operand)
  | construct (ctor : Constructor) (fields : List Operand)
  | project (value : Operand) (field : Nat)
  | closure (function : FunctionId) (captured : List Operand)
  /-- Direct calls are exactly saturated. -/
  | call (function : FunctionId) (args : List Operand)
  | callSelf (args : List Operand)
  /-- General application handles under-, exact-, and over-saturation. An
  empty argument list is identity; erased values absorb application. -/
  | apply (function : Operand) (args : List Operand)
  deriving BEq, DecidableEq, Repr, Inhabited

structure Alternative where
  ctor : Constructor
  target : BlockId
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One logical block transition. Branches keep current locals and constructor
branches append fields in declaration order. Nat successor branches append the
predecessor. Only return through an empty continuation terminates execution. -/
inductive Instr where
  | letOp (op : Op) (next : BlockId)
  | ret (value : Operand)
  | tailCall (function : FunctionId) (args : List Operand)
  | tailCallSelf (args : List Operand)
  | tailApply (function : Operand) (args : List Operand)
  | caseCtor (value : Operand) (alternatives : List Alternative)
  | caseNat (value : Operand) (ifZero ifSucc : BlockId)
  | branch (condition : Operand) (ifTrue ifFalse : BlockId)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The exact incoming frame size is part of the block contract. Whole-image
admission checks every operand and successor, including unreachable blocks. -/
structure Block where
  locals : Nat
  instruction : Instr
  deriving BEq, DecidableEq, Repr, Inhabited

structure Function where
  arity : Nat
  entry : BlockId := 0
  blocks : Array Block
  deriving BEq, Repr, Inhabited

structure CtorDecl where
  id : CtorId
  fields : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Entire closed image, not a canonical codec. The future commitment includes
all declarations and code, the entry point, primitive profile, and ABI. Local
function IDs permit mutual calls without asking for content-address fixpoints. -/
structure Program where
  entry : FunctionId := 0
  functions : Array Function
  constructors : Array CtorDecl := #[]
  deriving BEq, Repr, Inhabited

inductive Resource where
  | functions | constructors | blocks | locals | operands | continuations
  | inputNodes | natBits | stringBytes | byteArrayBytes
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Reference admission/execution capacities, NOT a prover RAM model. Blocks
are bounded per function, inputNodes counts the complete input value forest,
and scalar limits apply to literals, inputs, and primitive results. Fuel counts
machine transitions separately. These bounds are explicit semantic parameters.
They are not a permanent address width or production capacity recommendation. -/
structure Limits where
  functions : Nat := 4096
  constructors : Nat := 4096
  blocks : Nat := 65536
  locals : Nat := 4096
  operands : Nat := 256
  continuations : Nat := 65536
  inputNodes : Nat := 65536
  natBits : Nat := 4096
  stringBytes : Nat := 65536
  byteArrayBytes : Nat := 65536
  deriving BEq, Repr, Inhabited

inductive Error where
  | limit (resource : Resource)
  | invalidFunction (function : FunctionId)
  | invalidBlock (function : FunctionId) (block : BlockId)
  | invalidInstruction (function : FunctionId) (block : BlockId)
  | invalidLocal (slot : Local)
  | invalidConstructor (ctor : Constructor)
  | duplicateConstructor (id : CtorId)
  | frameSize (expected actual : Nat)
  | arityMismatch (expected actual : Nat)
  | invalidValue
  | invalidClosure (function : FunctionId)
  | invalidProjection (field : Nat)
  | missingCase (id : CtorId)
  | notConstructor | notNat | notBool | notFunction
  | primitiveType (primitive : Primitive)
  | primitiveValue (primitive : Primitive)
  | outOfFuel
  deriving BEq, DecidableEq, Repr, Inhabited

structure Frame where
  function : FunctionId
  block : BlockId
  locals : Array Value
  deriving BEq, Repr, Inhabited

inductive Control where
  | eval (frame : Frame)
  | apply (function : Value) (args : Array Value)
  | ret (value : Value)
  deriving BEq, Repr, Inhabited

inductive Continuation where
  /-- Resume at this block after appending the returned value to saved locals. -/
  | resume (frame : Frame)
  /-- Over-application first calls the saturated function, then applies its
  result to these arguments before resuming the original caller. -/
  | apply (args : Array Value)
  deriving BEq, Repr, Inhabited

structure State where
  control : Control
  continuation : Array Continuation := #[]
  deriving BEq, Repr, Inhabited

inductive Transition where
  | next (state : State)
  | halted (value : Value)
  deriving BEq, Repr, Inhabited

end Ix.Ixby
