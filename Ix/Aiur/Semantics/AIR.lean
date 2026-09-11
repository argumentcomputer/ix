/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

module
public import Ix.Aiur.Stages.Bytecode

/-!
Relational bytecode semantics for AIR extraction.

Each local execution records its constrained call requests. Advice is chosen
at each operation, including I/O reads and unconstrained calls. I/O writes,
key insertion and debugging impose no relation, as in the native constraint
emitter. Memory is a shared relation between width, pointer and contents;
its functionality is a separate memory-table obligation.

`Execution` closes local executions into finite call derivations. It neither
replays the runtime cache nor identifies advice with native hint results.
Proving that arbitrary native AIR rows have these local semantics, and that
the selected certified program checks the advice it needs, remain obligations.
-/

public section
@[expose] section

namespace Aiur.Bytecode.AIR

/-- Immutable memory facts supplied by the memory tables. -/
abbrev Memory := Nat → G → Array G → Prop

/-- A full function lookup, before channel encoding or compression. -/
structure Call where
  function : FunIdx
  inputs : Array G
  outputs : Array G
  rank : G
  deriving DecidableEq

/-- Read all indexed values, rejecting an invalid index. -/
def readValues (values : Array G) (indices : Array ValIdx) : Option (Array G) :=
  indices.mapM fun index => values[index]?

/-- Little-endian packing as field arithmetic. The caller checks length four. -/
def packWord (bytes : Array G) : G :=
  bytes.toList.zipIdx.foldl (fun value (byte, index) =>
    value + byte * G.ofNat (256 ^ index)) 0

def adviceOfSize (size : Nat) (advice : Array G) : Option (Array G) :=
  if advice.size = size then some advice else none

def unaryByte (values : Array G) (index : ValIdx)
    (compute : G → Array G) : Option (Array G) := do
  let value ← values[index]?
  if value.n < 256 then some (compute value) else none

def binaryByte (values : Array G) (left right : ValIdx)
    (compute : G → G → Array G) : Option (Array G) := do
  let x ← values[left]?
  let y ← values[right]?
  if x.n < 256 ∧ y.n < 256 then some (compute x y) else none

def pairValues (pair : G × G) : Array G := #[pair.1, pair.2]

def readWord (values : Array G) (indices : Array ValIdx) : Option G := do
  if indices.size ≠ 4 then none else do
    let bytes ← readValues values indices
    some (packWord bytes)

/-- Local operation outputs. Calls constrained by function lookups and
memory operations have separate `Step` constructors. All other constructors
are covered here, including the virtual carry of an unconstrained u32 sum.
Byte gadgets require their table input ranges; advice bytes do not. -/
def primitive (op : Op) (values advice : Array G) : Option (Array G) :=
  match op with
  | .const value => some #[value]
  | .add a b => do return #[(← values[a]?) + (← values[b]?)]
  | .sub a b => do return #[(← values[a]?) - (← values[b]?)]
  | .mul a b => do return #[(← values[a]?) * (← values[b]?)]
  | .eqZero a => do return #[G.eqZero (← values[a]?)]
  | .call _ _ outputSize true => adviceOfSize outputSize advice
  | .call _ _ _ false | .store _ | .load _ _ => none
  | .assertEq xs ys _ => do
    let left ← readValues values xs
    let right ← readValues values ys
    if left = right then some #[] else none
  | .ioGetInfo _ _ => adviceOfSize 2 advice
  | .ioRead _ _ size => adviceOfSize size advice
  | .ioSetInfo _ _ _ _ | .ioWrite _ _ | .debug _ _ => some #[]
  | .u8BitDecomposition a => unaryByte values a (Array.ofFn ∘ G.u8BitDecomposition)
  | .u8ShiftLeft a => unaryByte values a fun x => #[G.u8ShiftLeft x]
  | .u8ShiftRight a => unaryByte values a fun x => #[G.u8ShiftRight x]
  | .u8Xor a b => binaryByte values a b fun x y => #[G.u8Xor x y]
  | .u8Add a b => binaryByte values a b fun x y => pairValues (G.u8Add x y)
  | .u8Mul a b => binaryByte values a b fun x y => pairValues (G.u8Mul x y)
  | .u8Sub a b => binaryByte values a b fun x y => pairValues (G.u8Sub x y)
  | .u8And a b => binaryByte values a b fun x y => #[G.u8And x y]
  | .u8Or a b => binaryByte values a b fun x y => #[G.u8Or x y]
  | .u8LessThan a b => binaryByte values a b fun x y => #[G.u8LessThan x y]
  | .u8XorSplit7 a b => binaryByte values a b fun x y =>
      let z := x.n ^^^ y.n
      #[G.ofNat (z / 128), G.ofNat ((z * 2) % 256)]
  | .u8XorSplit4 a b => binaryByte values a b fun x y =>
      let z := x.n ^^^ y.n
      #[G.ofNat (z / 16), G.ofNat ((z * 16) % 256)]
  | .u8RangeCheck a b => binaryByte values a b fun _ _ => #[]
  | .u32LessThan a b => do
    let x ← values[a]?
    let y ← values[b]?
    if x.n < 2 ^ 32 ∧ y.n < 2 ^ 32 then some #[G.u32LessThan x y] else none
  | .unconstrainedBigUintDivMod _ _ => adviceOfSize 2 advice
  | .unconstrainedGToBytes _ => adviceOfSize 8 advice
  | .unconstrainedGInverse _ => adviceOfSize 1 advice
  | .unconstrainedU32Add a b => do
    let x ← readWord values a
    let y ← readWord values b
    let bytes ← adviceOfSize 4 advice
    return bytes.push ((x + y - packWord bytes) * 0xfffffffe00000002)
  | .unconstrainedU32Add3 a b c => do
    let x ← readWord values a
    let y ← readWord values b
    let z ← readWord values c
    let bytes ← adviceOfSize 4 advice
    return bytes.push ((x + y + z - packWord bytes) * 0xfffffffe00000002)
  | .u32ToField bytes => do return #[← readWord values bytes]

/-- One operation, with the constrained calls it requests. Advice is local
to this occurrence, even when the same operation appears in another row. -/
inductive Step (memory : Memory) : Op → Array G → Array G → List Call → Prop
  | primitive (evaluated : primitive op values advice = some outputs) :
      Step memory op values (values ++ outputs) []
  | call (arguments : readValues values indices = some request.inputs)
      (outputSize : request.outputs.size = size) :
      Step memory (.call request.function indices size false) values
        (values ++ request.outputs) [request]
  | store (arguments : readValues values indices = some contents)
      (stored : memory contents.size pointer contents) :
      Step memory (.store indices) values (values.push pointer) []
  | load (address : values[index]? = some pointer)
      (width : contents.size = size) (loaded : memory size pointer contents) :
      Step memory (.load size index) values (values ++ contents) []

inductive RunOps (memory : Memory) : List Op → Array G → Array G → List Call → Prop
  | nil : RunOps memory [] values values []
  | cons (first : Step memory op values intermediate firstCalls)
      (rest : RunOps memory ops intermediate finalValues restCalls) :
      RunOps memory (op :: ops) values finalValues (firstCalls ++ restCalls)

/-- Returns escape the function; yields enter the nearest continuation. -/
inductive Outcome where
  | returned : Array G → Outcome
  | yielded : Array G → Outcome

/-- A matching branch, or the default when no discriminant matches.
Duplicate case keys remain nondeterministic here, as permitted by the
selector equations; compiler uniqueness is a separate obligation. -/
inductive SelectArm (scrutinee : G) (cases : Array (G × Block))
    (fallback : Option Block) : Block → Prop
  | case (member : (scrutinee, block) ∈ cases.toList) :
      SelectArm scrutinee cases fallback block
  | fallback (selected : fallback = some block)
      (unmatched : ∀ pair ∈ cases.toList, pair.1 ≠ scrutinee) :
      SelectArm scrutinee cases fallback block

mutual

inductive RunBlock (memory : Memory) : Block → Array G → Outcome → List Call → Prop
  | block (operations : RunOps memory block.ops.toList values intermediate opCalls)
      (control : RunCtrl memory block.ctrl intermediate outcome ctrlCalls) :
      RunBlock memory block values outcome (opCalls ++ ctrlCalls)

inductive RunCtrl (memory : Memory) : Ctrl → Array G → Outcome → List Call → Prop
  | returned (result : readValues values indices = some outputs) :
      RunCtrl memory (.return selector indices) values (.returned outputs) []
  | yielded (result : readValues values indices = some outputs) :
      RunCtrl memory (.yield selector indices) values (.yielded outputs) []
  | match (value : values[index]? = some scrutinee)
      (selected : SelectArm scrutinee cases fallback arm)
      (branch : RunBlock memory arm values outcome calls) :
      RunCtrl memory (.match index cases fallback) values outcome calls
  | matchContinueReturn (value : values[index]? = some scrutinee)
      (selected : SelectArm scrutinee cases fallback arm)
      (branch : RunBlock memory arm values (.returned outputs) calls) :
      RunCtrl memory (.matchContinue index cases fallback size aux lookups continuation)
        values (.returned outputs) calls
  | matchContinueYield (value : values[index]? = some scrutinee)
      (selected : SelectArm scrutinee cases fallback arm)
      (branch : RunBlock memory arm values (.yielded yielded) branchCalls)
      (outputSize : yielded.size = size)
      (continued : RunBlock memory continuation (values ++ yielded) outcome contCalls) :
      RunCtrl memory (.matchContinue index cases fallback size aux lookups continuation)
        values outcome (branchCalls ++ contCalls)

end

/-- Local meaning of one function row, before resolving its call requests. -/
inductive RunFunction (program : Toplevel) (memory : Memory) : Call → List Call → Prop
  | function (selected : program.functions[request.function]? = some function)
      (arity : function.layout.inputSize = request.inputs.size)
      (body : RunBlock memory function.body request.inputs (.returned request.outputs) calls) :
      RunFunction program memory request calls

/-- A finite derivation: every constrained call has its own finite derivation.
Rows may be reused by several callers. Advice and immutable memory facts are
retained by the local relations, without asserting sequential cache effects. -/
inductive Execution (program : Toplevel) (memory : Memory) : Call → Prop
  | function (row : RunFunction program memory request calls)
      (children : ∀ child ∈ calls, Execution program memory child) :
      Execution program memory request

end Aiur.Bytecode.AIR

end
end
