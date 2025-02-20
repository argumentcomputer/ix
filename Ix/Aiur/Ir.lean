/-
The `TopLevel` is an abstraction that allows executing arbitrary Aiur program.
Roughly it works as following: user instantiates the `TopLevel` object using one or
more functions (of type `Function`) that express one or more finite computations.
The `TopLevel` implementation defines an execution algorithm which takes a tuple
(`FuncIdx`, `Array Value`) as input and returns `QueryRecord` as output. The input
provides information about what exact function to invoke (`FuncIdx`) as well as what
data (`Array Value`) to use for this function. The output (`QueryRecord`) contains
result of the provided function execution over provided data.
-/

/-- `Prim` defines primitive data types currently supported by Aiur language -/
inductive Prim
  | u64 : UInt64 → Prim
  | bool : Bool → Prim
deriving Inhabited, BEq, Repr

/--
`ValIdx` is a pointer to a particular value stored in the inner stack of the
`TopLevel` execution algorithm
-/
structure ValIdx where
  val : Nat
deriving Inhabited, BEq, Repr

def ValIdx.toNat (self : ValIdx) : Nat := self.val

/--
`FuncIdx` is a pointer to a function that needs to be executed by a `TopLevel` execution
algorithm
-/
structure FuncIdx where
  val : Nat
deriving Inhabited, BEq, Repr, Hashable

def FuncIdx.toNat (self : FuncIdx) : Nat := self.val

/-- `Op` enumerates operations currently supported by Aiur -/
inductive Op
  | prim : Prim → Op
  | add : ValIdx → ValIdx → Op
  | sub : ValIdx → ValIdx → Op
  | mul : ValIdx → ValIdx → Op
  | lt : ValIdx → ValIdx → Op
  | and : ValIdx → ValIdx → Op
  | xor : ValIdx → ValIdx → Op
  /-- A call operation takes 3 elements, function index, arguments, and output size -/
  | call : FuncIdx → Array ValIdx → Nat → Op
deriving Inhabited, Repr

/--
`SelIdx` serves as a selector of the particular code branch that is executed and
requires constraining for the proving system
-/
structure SelIdx where
  val : Nat
deriving Inhabited, BEq, Repr

def SelIdx.toNat (self : SelIdx) : Nat := self.val

mutual
/-- `Ctrl` expresses the control flows of the program -/
inductive Ctrl
  | if : ValIdx → Block → Block → Ctrl
  | return : SelIdx → Array ValIdx → Ctrl
deriving Inhabited, Repr

/--
`Block` serves as a body of the user-defined Aiur program / computation. May reference inner
blocks via `Ctrl`
-/
structure Block where
  ops : Array Op
  ctrl : Ctrl
  returnIdents : Array SelIdx
deriving Inhabited, Repr
end

/-- `Function` is an abstraction that expresses some finite computation -/
structure Function where
  inputSize : Nat
  outputSize : Nat
  body : Block
deriving Inhabited

structure Toplevel where
  functions : Array Function

def Toplevel.getFunction (self : Toplevel) (f : FuncIdx) : Function :=
  self.functions[f.toNat]!
