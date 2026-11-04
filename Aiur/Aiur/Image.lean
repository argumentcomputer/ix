import Aiur.Execution.Encode
import Aiur.Optimized.Basic

/-!
The runtime image: the certified compiler's output as explicit data that a
runtime reads directly. It carries the execution bytecode (functions, enum
layouts, fixed tables, maps and entry interfaces) and the trace artifact
(population plans, physical circuits and function groups).

The shapes mirror the runtime's representation one to one; nothing is
optimized in transit. Identifiers and register lists are naturals below
`2^63`. Field elements are canonical `UInt64`s. A polynomial is a buffer of
post-order nodes, three little-endian 64-bit words each (tag, a, b): tag 0
is the constant `a`, 1 the variable `a`, and 2, 3 and 4 the sum, difference
and product of the earlier nodes `a` and `b`; the last node is the root.
Every node but the root is an operand exactly once, so a reader can rebuild
the tree without recursion.

`Image.toJson` renders the diagnostic JSON artifact from an image.
-/

namespace Aiur.Image
open Lean

/-- Post-order polynomial nodes; see the module documentation. -/
abbrev Poly := ByteArray

inductive Ty where
  | field
  | tuple (items : Array Ty)
  | ptr (target : Ty)
  | enum (name : String)
  deriving Inhabited, BEq

inductive IOType where
  | field
  | tuple (items : Array IOType)
  | array (element : IOType) (length : Nat)
  | record (name : String) (fields : Array (String × IOType))
  | enum (name : String) (constructors : Array (String × Array IOType))
  deriving Inhabited, BEq

/-- Guard and branch tests: registers and canonical values, pairwise. -/
structure Tests where
  registers : Array Nat
  values : Array UInt64
  deriving Inhabited, BEq

inductive Instruction where
  | literal (dest : Nat) (value : UInt64)
  | copy (dest source : Array Nat)
  | neg (dest source : Nat)
  /-- `op`: 0 add, 1 sub, 2 mul, 3 div. -/
  | binary (dest left right : Nat) (op : UInt8)
  | guard (tests : Tests) (message : String)
  | branch (tests : Tests) (otherwise : Nat)
  | jump (target : Nat)
  | call (function : Nat) (args dest : Array Nat)
  | store (type : Ty) (value : Array Nat) (dest : Nat)
  | load (type : Ty) (pointer : Nat) (dest : Array Nat)
  | hint (channel : String) (type keyType : Ty) (key dest : Array Nat)
  | assertEq (left right : Array Nat) (message : Option String) (runtimeCheck : Bool)
  | ret (value : Array Nat)
  | fail (message : String)
  deriving Inhabited, BEq

structure Function where
  name : String
  params : Array Ty
  result : Ty
  registers : Nat
  code : Array Instruction
  deriving Inhabited, BEq

structure Enum where
  name : String
  constructors : Array (String × Array Ty)
  deriving Inhabited, BEq

structure Table where
  name : String
  type : Ty
  rows : Array (Array UInt64)
  deriving Inhabited, BEq

structure Map where
  name : String
  params : Array Ty
  result : Ty
  input : Nat
  output : Nat
  deriving Inhabited, BEq

structure Entry where
  name : String
  function : Nat
  inputs : Array IOType
  output : Option IOType
  deriving Inhabited, BEq

structure Program where
  version : Nat
  functions : Array Function
  enums : Array Enum
  tables : Array Table
  maps : Array Map
  entries : Array Entry
  modulus : UInt64
  deriving Inhabited, BEq

inductive Action where
  | assign (dest : Array Nat) (values : Array Poly)
  | inverse (dest : Nat) (value : Poly)
  | choose (dest : Array Nat) (tests : Array (Array Poly))
  | failure (dest : Array Nat) (differences : Array Poly)
  | call (name : String) (args : Array Poly) (dest : Array Nat)
  | store (type : Ty) (values : Array Poly) (dest : Nat)
  | load (type : Ty) (address : Poly) (dest : Array Nat)
  | hint (channel : String) (instruction : Nat) (type keyType : Ty) (key : Array Poly)
      (dest : Array Nat)
  deriving Inhabited, BEq

structure Step where
  guard : Poly
  action : Action
  deriving Inhabited, BEq

structure ColumnWrite where
  column : Nat
  source : Nat
  guard : Poly
  deriving Inhabited, BEq

structure FunctionPlan where
  name : String
  chip : String
  witnesses : Nat
  inputs : Array Nat
  output : Array Nat
  steps : Array Step
  writes : Array ColumnWrite
  deriving Inhabited, BEq

structure Send where
  channel : String
  args : Array Poly
  result : Array Nat
  enable : Poly
  deriving Inhabited, BEq

structure MemoryLookup where
  type : Ty
  address : Poly
  values : Array Poly
  enable : Poly
  deriving Inhabited, BEq

structure Chip where
  name : String
  width : Nat
  activation : Nat
  inputs : Array Nat
  output : Array Poly
  constraints : Array Poly
  sends : Array Send
  memory : Array MemoryLookup
  deriving Inhabited, BEq

structure GroupLookup where
  enable : Poly
  args : Array Poly
  deriving Inhabited, BEq

structure GroupWrite where
  column : Nat
  value : Poly
  deriving Inhabited, BEq

structure GroupMember where
  name : String
  columns : Array Nat
  selector : Nat
  writes : Array GroupWrite
  deriving Inhabited, BEq

structure Group where
  name : String
  width : Nat
  activation : Poly
  constraints : Array Poly
  receive : Array Poly
  sends : Array GroupLookup
  members : Array GroupMember
  deriving Inhabited, BEq

structure Trace where
  version : Nat
  functions : Array FunctionPlan
  chips : Array Chip
  groups : Array Group
  modulus : UInt64
  deriving Inhabited, BEq

/-- A compiled program with its trace artifact. -/
structure RuntimeImage where
  program : Program
  trace : Trace
  deriving Inhabited

/-! ## Construction -/

def word (n : Nat) : Except String UInt64 :=
  if n < 2 ^ 64 then pure n.toUInt64 else throw s!"value {n} exceeds 64 bits"

private def pushWord (bytes : ByteArray) (n : UInt64) : ByteArray := Id.run do
  let mut bytes := bytes
  for i in [0:8] do
    bytes := bytes.push (n >>> (8 * i).toUInt64).toUInt8
  return bytes

private def pushNode (bytes : ByteArray) (tag a b : UInt64) : ByteArray :=
  pushWord (pushWord (pushWord bytes tag) a) b

/-- Append `p`'s post-order nodes, numbering them from `next`; returns the
buffer and the root's index. -/
def polyNodes (encode : F → Nat) (bytes : ByteArray) (next : Nat) :
    Optimized.Polynomial F → Except String (ByteArray × Nat)
  | .const x => do return (pushNode bytes 0 (← word (encode x)) 0, next)
  | .var x => do return (pushNode bytes 1 (← word x) 0, next)
  | .add a b => do
    let (bytes, ia) ← polyNodes encode bytes next a
    let (bytes, ib) ← polyNodes encode bytes (ia + 1) b
    return (pushNode bytes 2 ia.toUInt64 ib.toUInt64, ib + 1)
  | .sub a b => do
    let (bytes, ia) ← polyNodes encode bytes next a
    let (bytes, ib) ← polyNodes encode bytes (ia + 1) b
    return (pushNode bytes 3 ia.toUInt64 ib.toUInt64, ib + 1)
  | .mul a b => do
    let (bytes, ia) ← polyNodes encode bytes next a
    let (bytes, ib) ← polyNodes encode bytes (ia + 1) b
    return (pushNode bytes 4 ia.toUInt64 ib.toUInt64, ib + 1)

def poly (encode : F → Nat) (p : Optimized.Polynomial F) : Except String Poly :=
  return (← polyNodes encode .empty 0 p).1

def ty : Aiur.Ty → Ty
  | .field => .field
  | .ptr type => .ptr (ty type)
  | .tuple types => .tuple (types.map ty).toArray
  | .enum name => .enum name
termination_by type => sizeOf type

def ioType : Execution.IOType → IOType
  | .field => .field
  | .tuple items => .tuple (items.map ioType).toArray
  | .array element length => .array (ioType element) length
  | .record name fields => .record name (fields.map fun entry => (entry.1, ioType entry.2)).toArray
  | .enum name constructors =>
      .enum name (constructors.map fun entry => (entry.1, (entry.2.map ioType).toArray)).toArray
termination_by type => sizeOf type
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      cases ‹String × Execution.IOType›
      simp_all only [Prod.mk.sizeOf_spec]
      omega
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      have hp : sizeOf entry < sizeOf constructors := List.sizeOf_lt_of_mem (by assumption)
      cases entry
      simp_all only [Prod.mk.sizeOf_spec]
      omega

def tests (encode : F → Nat) (tests : List (Execution.Register × F)) : Except String Tests := do
  return { registers := (tests.map (·.1)).toArray,
           values := ← (tests.map (·.2)).toArray.mapM fun v => word (encode v) }

def binOp : BinOp → UInt8
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3

def opName : UInt8 → String
  | 0 => "add" | 1 => "sub" | 2 => "mul" | _ => "div"

def instruction (encode : F → Nat) : Execution.Instruction F → Except String Instruction
  | .literal dest value => return .literal dest (← word (encode value))
  | .copy dest source => return .copy dest.toArray source.toArray
  | .neg dest source => return .neg dest source
  | .binary dest op left right => return .binary dest left right (binOp op)
  | .guard ts message => return .guard (← tests encode ts) message
  | .branch ts target => return .branch (← tests encode ts) target
  | .jump target => return .jump target
  | .call function args dest => return .call function args.toArray dest.toArray
  | .store type value dest => return .store (ty type) value.toArray dest
  | .load type pointer dest => return .load (ty type) pointer dest.toArray
  | .hint type keyType key dest channel =>
      return .hint channel (ty type) (ty keyType) key.toArray dest.toArray
  | .assertEq left right assertion =>
      return .assertEq left.toArray right.toArray assertion.message assertion.runtimeCheck
  | .ret value => return .ret value.toArray
  | .fail message => return .fail message

/-- The execution bytecode of `exported`, as `Execution.Export.toJson`
encodes it. -/
def program (exported : Execution.Export F) (modulus : Nat) (encode : F → Nat) :
    Except String Program := do
  if modulus < 2 || modulus ≥ 2^64 then throw "execution requires a prime modulus fitting UInt64"
  let code := exported.bytecode
  let entries ← code.entries.toArray.mapM fun (name, function) => do
    let some interface := exported.interfaces.find? (·.name == name)
      | throw s!"missing entry IO interface {name}"
    return { name, function, inputs := (interface.inputs.map ioType).toArray,
             output := interface.output.map ioType : Entry }
  let functions ← code.functions.toArray.mapM fun fn => do
    return { name := fn.name, params := (fn.params.map ty).toArray, result := ty fn.result
             registers := fn.registers, code := ← fn.code.mapM (instruction encode) : Function }
  let tables ← code.tables.toArray.mapM fun table => do
    return { name := table.name, type := ty table.type
             rows := ← table.rows.toArray.mapM fun row => row.toArray.mapM (word ∘ encode) : Table }
  return {
    version := 2, modulus := modulus.toUInt64, functions, tables, entries
    enums := code.enums.toArray.map fun decl =>
      { name := decl.name, constructors := (decl.constructors.map fun c =>
          (c.name, (c.fields.map ty).toArray)).toArray }
    maps := code.maps.toArray.map fun map =>
      { name := map.name, params := (map.params.map ty).toArray, result := ty map.result
        input := map.input, output := map.output } }

/-! ## Diagnostic JSON -/

private def obj (fields : List (String × Json)) := Json.mkObj fields
private def js {α : Type} [ToJson α] (value : α) : Json := Lean.toJson value

private def tagged (key tag : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj ((key, js tag) :: fields)

private def readWord (bytes : ByteArray) (offset : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [0:8] do
    n := n + (bytes.get! (offset + i)).toNat * 256 ^ i
  return n

/-- The polynomial tree of a node buffer, as nested JSON. -/
def polyJson (p : Poly) : Except String Json := do
  let count := p.size / 24
  unless count * 24 == p.size && count > 0 do throw "malformed polynomial nodes"
  let mut nodes : Array Json := #[]
  for i in [0:count] do
    let tag := readWord p (24 * i)
    let a := readWord p (24 * i + 8)
    let b := readWord p (24 * i + 16)
    let node ← match tag with
      | 0 => pure (obj [("const", js a)])
      | 1 => pure (obj [("var", js a)])
      | _ =>
        let some x := nodes[a]? | throw "polynomial operand out of order"
        let some y := nodes[b]? | throw "polynomial operand out of order"
        match tag with
        | 2 => pure (obj [("add", js [x, y])])
        | 3 => pure (obj [("sub", js [x, y])])
        | 4 => pure (obj [("mul", js [x, y])])
        | _ => throw "invalid polynomial node"
    nodes := nodes.push node
  return nodes.back!

def polysJson (ps : Array Poly) : Except String Json := return js (← ps.mapM polyJson)

partial def Ty.toJson : Ty → Json
  | .field => tagged "kind" "field"
  | .ptr type => tagged "kind" "ptr" [("target", type.toJson)]
  | .tuple types => tagged "kind" "tuple" [("items", js (types.map Ty.toJson))]
  | .enum name => tagged "kind" "enum" [("name", js name)]

partial def IOType.toJson : IOType → Json
  | .field => tagged "kind" "field"
  | .tuple items => tagged "kind" "tuple" [("items", js (items.map IOType.toJson))]
  | .array element length => tagged "kind" "array" [("element", element.toJson), ("length", js length)]
  | .record name fields => tagged "kind" "struct" [("name", js name),
      ("fields", js (fields.map fun entry => js [js entry.1, entry.2.toJson]))]
  | .enum name constructors => tagged "kind" "enum" [("name", js name),
      ("constructors", js (constructors.map fun entry => js [js entry.1, js (entry.2.map IOType.toJson)]))]

private def testsJson (t : Tests) : Json :=
  js ((t.registers.zip t.values).map fun (r, v) => js [r, v.toNat])

def Instruction.toJson : Instruction → Json
  | .literal dest value => tagged "op" "literal" [("dest", js dest), ("value", js value.toNat)]
  | .copy dest source => tagged "op" "copy" [("dest", js dest), ("source", js source)]
  | .neg dest source => tagged "op" "neg" [("dest", js dest), ("source", js source)]
  | .binary dest left right op => tagged "op" "binary" [("dest", js dest),
      ("operator", js (opName op)),
      ("left", js left), ("right", js right)]
  | .guard t message => tagged "op" "guard" [("tests", testsJson t), ("message", js message)]
  | .branch t target => tagged "op" "branch" [("tests", testsJson t), ("otherwise", js target)]
  | .jump target => tagged "op" "jump" [("target", js target)]
  | .call function args dest => tagged "op" "call"
      [("function", js function), ("args", js args), ("dest", js dest)]
  | .store type value dest => tagged "op" "store"
      [("type", type.toJson), ("value", js value), ("dest", js dest)]
  | .load type pointer dest => tagged "op" "load"
      [("type", type.toJson), ("pointer", js pointer), ("dest", js dest)]
  | .hint channel type keyType key dest => tagged "op" "hint"
      [("channel", js channel), ("type", type.toJson), ("key_type", keyType.toJson),
       ("key", js key), ("dest", js dest)]
  | .assertEq left right message runtimeCheck => tagged "op" "assert_eq"
      [("left", js left), ("right", js right), ("message", js message),
       ("runtime_check", js runtimeCheck)]
  | .ret value => tagged "op" "ret" [("value", js value)]
  | .fail message => tagged "op" "fail" [("message", js message)]

def Program.toJson (p : Program) : Json :=
  obj [("version", js p.version), ("modulus", js p.modulus.toNat),
    ("functions", js (p.functions.map fun fn => obj [("name", js fn.name),
      ("params", js (fn.params.map Ty.toJson)), ("result", fn.result.toJson),
      ("registers", js fn.registers), ("code", js (fn.code.map Instruction.toJson))])),
    ("enums", js (p.enums.map fun decl => obj [("name", js decl.name),
      ("constructors", js (decl.constructors.map fun (name, fields) =>
        obj [("name", js name), ("fields", js (fields.map Ty.toJson))]))])),
    ("tables", js (p.tables.map fun table => obj [("name", js table.name),
      ("type", table.type.toJson), ("rows", js (table.rows.map (·.map UInt64.toNat)))])),
    ("maps", js (p.maps.map fun map => obj [("name", js map.name),
      ("params", js (map.params.map Ty.toJson)), ("result", map.result.toJson),
      ("input", js map.input), ("output", js map.output)])),
    ("entries", js (p.entries.map fun entry => obj [("name", js entry.name),
      ("function", js entry.function), ("inputs", js (entry.inputs.map IOType.toJson)),
      ("output", (entry.output.map IOType.toJson).getD Json.null)]))]

def Action.toJson : Action → Except String Json
  | .assign dest values => do return tagged "op" "assign" [("dest", js dest), ("values", ← polysJson values)]
  | .inverse dest value => do return tagged "op" "inverse" [("dest", js dest), ("value", ← polyJson value)]
  | .choose dest tests => do return tagged "op" "choose" [("dest", js dest),
      ("tests", js (← tests.mapM polysJson))]
  | .failure dest differences => do return tagged "op" "failure" [("dest", js dest),
      ("differences", ← polysJson differences)]
  | .call name args dest => do return tagged "op" "call" [("name", js name), ("dest", js dest),
      ("args", ← polysJson args)]
  | .store type values dest => do return tagged "op" "store" [("type", type.toJson),
      ("values", ← polysJson values), ("dest", js dest)]
  | .load type address dest => do return tagged "op" "load" [("type", type.toJson),
      ("address", ← polyJson address), ("dest", js dest)]
  | .hint channel instruction type keyType key dest => do
    return tagged "op" "hint" [("channel", js channel), ("instruction", js instruction), ("type", type.toJson),
       ("key_type", keyType.toJson), ("key", ← polysJson key), ("dest", js dest)]

def FunctionPlan.toJson (f : FunctionPlan) : Except String Json := do
  let steps ← f.steps.mapM fun step => do
    return obj [("guard", ← polyJson step.guard), ("action", ← step.action.toJson)]
  let writes ← f.writes.mapM fun w => do
    return obj [("column", js w.column), ("source", js w.source), ("guard", ← polyJson w.guard)]
  return obj [("name", js f.name), ("chip", js f.chip), ("witnesses", js f.witnesses),
    ("inputs", js f.inputs), ("output", js f.output), ("steps", js steps), ("writes", js writes)]

def Chip.toJson (c : Chip) : Except String Json := do
  let sends ← c.sends.mapM fun s => do
    return obj [("channel", js s.channel), ("args", ← polysJson s.args), ("result", js s.result),
      ("enable", ← polyJson s.enable)]
  let memory ← c.memory.mapM fun m => do
    return obj [("type", m.type.toJson), ("address", ← polyJson m.address),
      ("values", ← polysJson m.values), ("enable", ← polyJson m.enable)]
  return obj [("name", js c.name), ("width", js c.width), ("activation", js c.activation),
    ("inputs", js c.inputs), ("output", ← polysJson c.output),
    ("constraints", ← polysJson c.constraints), ("sends", js sends), ("memory", js memory)]

def Group.toJson (g : Group) : Except String Json := do
  let sends ← g.sends.mapM fun s => do
    return obj [("enable", ← polyJson s.enable), ("args", ← polysJson s.args)]
  let members ← g.members.mapM fun m => do
    let writes ← m.writes.mapM fun w => do
      return obj [("column", js w.column), ("value", ← polyJson w.value)]
    return obj [("name", js m.name), ("columns", js m.columns), ("selector", js m.selector),
      ("writes", js writes)]
  return obj [("name", js g.name), ("width", js g.width), ("activation", ← polyJson g.activation),
    ("constraints", ← polysJson g.constraints), ("receive", ← polysJson g.receive),
    ("sends", js sends), ("members", js members)]

def Trace.toJson (t : Trace) : Except String Json := do
  return obj [("version", js t.version), ("modulus", js t.modulus.toNat),
    ("functions", js (← t.functions.mapM FunctionPlan.toJson)),
    ("chips", js (← t.chips.mapM Chip.toJson)), ("groups", js (← t.groups.mapM Group.toJson))]

/-- The diagnostic JSON package `{"program", "trace"}`. -/
def RuntimeImage.toJson (image : RuntimeImage) : Except String Json := do
  return obj [("program", image.program.toJson), ("trace", ← image.trace.toJson)]

end Aiur.Image
