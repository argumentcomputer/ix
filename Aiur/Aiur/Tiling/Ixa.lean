import Aiur.Tiling.Bridge
import Aiur.Execution.Encode
import Aiur.Ixon.Field
import Aiur.Artifact

/-!
# Reading the lowered chips from a compiled artifact

A package (`Aiur.Artifact.package`, grammar in the Rust reader
`aiur::artifact`) carries in its trace section every activated depth chip of
`Depth.system cfg prepared.system`, as `Trace.putChip` writes it: the chip
`Activation.compile c` with its wire values flattened to words, together with
`c.numVars`. That is exactly the data `Bridge.lower idOf c` reads, so the
lookup circuits the tiling theorems are about can be built from the file:

* `IChip` is the written form of one chip and `IChip.ofChip c` the form
  `putChip` writes for `c`;
* `IChip.lower` is `Bridge.lower` on that form, and `IChip.lower_ofChip`
  proves `(IChip.ofChip c).lower idOf = Bridge.lower idOf c`;
* `decodePackage` reads a version 2 (UInt64 scalars) or version 3 (wide
  scalars) package: the callable names (functions, then maps, the numbering of
  `idOf`), the map claim tuples and the chips, with every polynomial expanded
  from the node pool.

The decoder is not proved inverse to the writer. Exports use
`decodeChecked` (`IxaTrace.lean`), which re-encodes the decoded trace section
and compares it with the file byte for byte. The decoder rejects unknown tags,
out-of-range node references, constants not below the modulus and trailing
bytes.
-/

namespace Aiur.Tiling.Ixa

open Aiur.Ixon Aiur.Circuit

/-! ## The written form of a chip -/

structure ISend (F : Type) where
  channel : String
  args : List (ArithExpr F)
  result : List Nat
  enable : ArithExpr F

structure IMemory (F : Type) where
  type : Ty
  address : ArithExpr F
  values : List (ArithExpr F)
  enable : ArithExpr F

/-- One chip of a trace section: the activated chip (`width` columns) of a
source chip with `activation` columns, whose selector is column `activation`. -/
structure IChip (F : Type) where
  name : String
  width : Nat
  activation : Nat
  inputs : List Nat
  output : List (ArithExpr F)
  constraints : List (ArithExpr F)
  sends : List (ISend F)
  memory : List (IMemory F)

instance {F : Type} : Inhabited (IChip F) := ⟨⟨"", 0, 0, [], [], [], [], []⟩⟩

section Lower

variable {F : Type} [Field F] [DecidableEq F]

/-- The data `Trace.putChip` writes for the source chip `c`. -/
def IChip.ofChip (c : Chip F) : IChip F :=
  let a := Optimized.Activation.compile c
  { name := a.name
    width := a.numVars
    activation := c.numVars
    inputs := a.inputs.flatMap WireValue.words
    output := a.output.words
    constraints := a.constraints
    sends := a.sends.map fun s => ⟨s.channel, s.args.flatMap WireValue.words, s.result.words, s.enable⟩
    memory := a.memory.map fun m => ⟨m.value.type, m.address, m.value.words, m.enable⟩ }

/-- `Bridge.lower` on the written form: selector `activation`, receive
multiplicity `activation + 1`. -/
def IChip.lower (idOf : String → Nat) (x : IChip F) : Tiling.Circuit F where
  width := x.activation + 2
  constraints := x.constraints ++
    [.mul (.sub (.const 1) (.var x.activation)) (.var (x.activation + 1))]
  lookups := ⟨.sub (.const 0) (.var (x.activation + 1)),
      .const (Bridge.CALL : F) :: .const (idOf x.name : F) :: (x.inputs.map .var ++ x.output)⟩ ::
    (x.sends.map (fun s => ⟨s.enable,
        .const (Bridge.CALL : F) :: .const (idOf s.channel : F) :: (s.args ++ s.result.map .var)⟩) ++
      x.memory.map fun m => ⟨m.enable,
        .const (Bridge.ROM : F) :: .const (m.values.length : F) :: m.address :: m.values⟩)

theorem IChip.lower_ofChip (idOf : String → Nat) (c : Chip F) :
    (IChip.ofChip c).lower idOf = Bridge.lower idOf c := by
  simp only [IChip.lower, IChip.ofChip, Bridge.lower, Bridge.receiveLookup, List.map_map, Function.comp_def, List.map_flatMap]
  rfl

theorem lower_map_ofChip (idOf : String → Nat) (cs : List (Chip F)) :
    (cs.map IChip.ofChip).map (IChip.lower idOf) = cs.map (Bridge.lower idOf) := by
  simp [Function.comp_def, IChip.lower_ofChip]

/-- `Bridge.checkEnables` on the written form. -/
def IChip.checkEnables (bound : Nat) (x : IChip F) : Bool :=
  x.sends.all (fun s => Bridge.boolCertAt x.constraints bound x.activation s.enable) &&
    x.memory.all (fun m => Bridge.boolCertAt x.constraints bound x.activation m.enable)

theorem IChip.checkEnables_ofChip (bound : Nat) (c : Chip F) :
    (IChip.ofChip c).checkEnables bound = Bridge.checkEnables bound c := by
  simp only [IChip.checkEnables, IChip.ofChip, Bridge.checkEnables, List.all_map, Function.comp_def]

end Lower

/-! ## Decoding -/

/-! ## The decoded trace section -/

/-- One population step's operation, as `Trace.putOperation` writes it. -/
inductive IOp (F : Type) where
  | assign (dest : List Nat) (values : List (ArithExpr F))
  | inverse (dest : Nat) (value : ArithExpr F)
  | choose (dest : List Nat) (tests : List (List (ArithExpr F)))
  | failure (dest : List Nat) (differences : List (ArithExpr F))
  | call (name : String) (args : List (ArithExpr F)) (dest : List Nat)
  | store (type : Ty) (values : List (ArithExpr F)) (dest : Nat)
  | load (type : Ty) (address : ArithExpr F) (dest : List Nat)
  | hint (channel : String) (pc : Nat) (type keyType : Ty) (key : List (ArithExpr F)) (dest : List Nat)

/-- A function's population plan, as `Trace.putFunctionOf` writes it. -/
structure IPlan (F : Type) where
  name : String
  representative : String
  roles : Nat
  inputs : List Nat
  outputs : List Nat
  steps : List (ArithExpr F × IOp F)
  writes : List (Nat × Nat × ArithExpr F)

/-- A chip's depth metadata, as `Trace.putDepth` writes it: slot kinds `0 … 3`,
with a column for kinds `2` and `3`. -/
structure IDepth where
  column : Option Nat
  rank : Nat
  slots : List (Nat × Option Nat)

structure IMember (F : Type) where
  name : String
  columns : Array Nat
  selector : Nat
  writes : List (Nat × ArithExpr F)

/-- A checked function group, as `Trace.putGroup` writes it. -/
structure IGroup (F : Type) where
  name : String
  width : Nat
  activation : ArithExpr F
  constraints : List (ArithExpr F)
  receive : List (ArithExpr F)
  sends : List (ArithExpr F × List (ArithExpr F))
  members : List (IMember F)

structure ITrace (F : Type) where
  wide : Bool
  modulus : Nat
  limbs : List Nat
  plans : List (IPlan F)
  chips : List (IChip F × IDepth)
  groups : List (IGroup F)

/-- A decoded package: what an export needs from it. -/
structure Package (F : Type) where
  modulus : Nat
  /-- Version 3 (wide scalars). -/
  wide : Bool
  /-- Function names, then map names: the callable numbering. -/
  callables : Array String
  functions : Nat
  /-- Per map: its callable index and its claim payloads (input row ++ output row). -/
  maps : Array (Nat × Array (List F))
  entries : Array (String × Nat)
  limbs : List Nat
  chips : Array (IChip F)
  /-- Per checked function group: its name and its members' names. -/
  groups : Array (String × List String)
  /-- The whole program section, decoded. -/
  program : Execution.Export F
  /-- The whole trace section, decoded. -/
  trace : ITrace F
  /-- The byte offset of the trace section in the file. -/
  traceStart : Nat

/-- The index of `name` among the callables (`Snapshot`'s `idOf`). -/
def Package.idOf {F : Type} (p : Package F) (name : String) : Nat :=
  p.callables.toList.idxOf name

/-- The tuple `[CALL, id, payload…]` of every claim of the maps in `called`,
map by map in program order, rows in table order. -/
def Package.claims {F : Type} [NatCast F] (p : Package F) (called : String → Bool) : List (List F) :=
  p.maps.toList.flatMap fun (callable, rows) =>
    if called (p.callables.getD callable "") then
      rows.toList.map fun r => (Bridge.CALL : F) :: (callable : F) :: r
    else []

section Decode

variable {F : Type} [NatCast F]

@[specialize] def getList (item : GetM α) : GetM (List α) := return (← getArray item).toList

def getNats : GetM (List Nat) := getList getNat

/-- A field integer in the package's scalar encoding. -/
def getScalar (wide : Bool) : GetM Nat := if wide then getWideNat else getNat

/-- The node pool: every node expanded to its polynomial. Operands point
back by `1 ≤ back ≤ i`. -/
def getNodes (wide : Bool) (modulus : Nat) : GetM (Array (ArithExpr F)) := do
  let n ← getCount
  let mut out : Array (ArithExpr F) := Array.mkEmpty n
  for i in [0:n] do
    let tag ← getTag "node" 5
    if tag == 0 then
      let v ← getScalar wide
      unless v < modulus do fail s!"constant {v} is not below the modulus"
      out := out.push (.const (v : F))
    else if tag == 1 then
      out := out.push (.var (← getNat))
    else
      let a ← getNat
      let b ← getNat
      unless 1 ≤ a && a ≤ i && 1 ≤ b && b ≤ i do fail s!"node {i} refers outside the pool"
      let x := out.getD (i - a) (.var 0)
      let y := out.getD (i - b) (.var 0)
      out := out.push (match tag with
        | 2 => .add x y
        | 3 => .sub x y
        | _ => .mul x y)
  return out

def getPoly (pool : Array (ArithExpr F)) : GetM (ArithExpr F) := do
  let i ← getNat
  let some p := pool[i]? | fail s!"polynomial root {i} is outside the pool"
  return p

def getPolys (pool : Array (ArithExpr F)) : GetM (List (ArithExpr F)) := getList (getPoly pool)

/-- The chip record of `Trace.putChip`. -/
def getChipRecord (pool : Array (ArithExpr F)) : GetM (IChip F) := do
  let name ← getString
  let width ← getNat
  let activation ← getNat
  unless width == activation + 1 do fail s!"chip {name}: activated width {width} is not {activation} + 1"
  let inputs ← getNats
  let output ← getPolys pool
  let constraints ← getPolys pool
  let sends ← getList do
    let channel ← getString
    let args ← getPolys pool
    let result ← getNats
    let enable ← getPoly pool
    return (⟨channel, args, result, enable⟩ : ISend F)
  let memory ← getList do
    let type ← Execution.getTy
    let address ← getPoly pool
    let values ← getPolys pool
    let enable ← getPoly pool
    return (⟨type, address, values, enable⟩ : IMemory F)
  return { name, width, activation, inputs, output, constraints, sends, memory }

def getIOp (pool : Array (ArithExpr F)) : GetM (IOp F) := do
  match ← getTag "action" 8 with
  | 0 => return .assign (← getNats) (← getPolys pool)
  | 1 => return .inverse (← getNat) (← getPoly pool)
  | 2 => return .choose (← getNats) (← getList (getPolys pool))
  | 3 => return .failure (← getNats) (← getPolys pool)
  | 4 => return .call (← getString) (← getPolys pool) (← getNats)
  | 5 => return .store (← Execution.getTy) (← getPolys pool) (← getNat)
  | 6 => return .load (← Execution.getTy) (← getPoly pool) (← getNats)
  | _ => return .hint (← getString) (← getNat) (← Execution.getTy) (← Execution.getTy) (← getPolys pool) (← getNats)

def getIPlan (pool : Array (ArithExpr F)) : GetM (IPlan F) := do
  let name ← getString
  let representative ← getString
  let roles ← getNat
  let inputs ← getNats
  let outputs ← getNats
  let steps ← getList do return (← getPoly pool, ← getIOp pool)
  let writes ← getList do return (← getNat, ← getNat, ← getPoly pool)
  return { name, representative, roles, inputs, outputs, steps, writes }

def getIDepth : GetM IDepth := do
  let column ← getOption getNat
  let rank ← getNat
  let slots ← getList do
    let kind ← getTag "depth slot" 4
    if 2 ≤ kind then return (kind, some (← getNat)) else return (kind, none)
  return { column, rank, slots }

def getIGroup (pool : Array (ArithExpr F)) : GetM (IGroup F) := do
  let name ← getString
  let width ← getNat
  let activation ← getPoly pool
  let constraints ← getPolys pool
  let receive ← getPolys pool
  let sends ← getList do return (← getPoly pool, ← getPolys pool)
  let members ← getList do
    let name ← getString
    let columns ← getArray getNat
    let selector ← getNat
    let writes ← getList do return (← getNat, ← getPoly pool)
    return ({ name, columns, selector, writes } : IMember F)
  return { name, width, activation, constraints, receive, sends, members }

/-- A complete trace section (everything after the program section's trace
option byte). -/
def getTrace (wide : Bool) (modulus : Nat) : GetM (ITrace F) := do
  let pv ← getNat
  unless pv == 3 do fail s!"unsupported trace plan version {pv}"
  let tm ← getScalar wide
  unless tm == modulus do fail s!"trace modulus {tm} is not {modulus}"
  let limbs ← getNats
  let pool ← getNodes (F := F) wide modulus
  let plans ← getList (getIPlan pool)
  let chips ← getList do return (← getChipRecord pool, ← getIDepth)
  let groups ← getList (getIGroup pool)
  return { wide, modulus, limbs, plans, chips, groups }


/-- `getIOType` with a bound on the nesting depth. -/
def getIOTypeAux : Nat → GetM Execution.IOType
  | 0 => fail "io type nesting exceeds the input"
  | fuel + 1 => do
      match ← getTag "io type" 5 with
      | 0 => return .field
      | 1 => return .tuple (← getList (getIOTypeAux fuel))
      | 2 => return .array (← getIOTypeAux fuel) (← getNat)
      | 3 => return .record (← getString) (← getList (return (← getString, ← getIOTypeAux fuel)))
      | _ => return .enum (← getString) (← getList (return (← getString, ← getList (getIOTypeAux fuel))))

/-- Every nesting level reads a tag byte, so this bound never binds. -/
def getIOType : GetM Execution.IOType := do getIOTypeAux ((← remaining) + 1)

def getTests (wide : Bool) : GetM (List (Nat × F)) :=
  getList (return (← getNat, ((← getScalar wide : Nat) : F)))

def getInstruction (wide : Bool) : GetM (Execution.Instruction F) := do
  match ← getTag "instruction" 15 with
  | 0 => return .literal (← getNat) ((← getScalar wide : Nat) : F)
  | 1 => return .copy (← getNats) (← getNats)
  | 2 => return .neg (← getNat) (← getNat)
  | 3 => do
      let dest ← getNat
      let op : BinOp := match ← getTag "binary op" 4 with
        | 0 => .add | 1 => .sub | 2 => .mul | _ => .div
      return .binary dest op (← getNat) (← getNat)
  | 4 => return .guard (← getTests wide) (← getString)
  | 5 => return .branch (← getTests wide) (← getNat)
  | 6 => return .jump (← getNat)
  | 7 => return .call (← getNat) (← getNats) (← getNats)
  | 8 => return .store (← Execution.getTy) (← getNats) (← getNat)
  | 9 => return .load (← Execution.getTy) (← getNat) (← getNats)
  | 10 => do
      let channel ← getString
      return .hint (← Execution.getTy) (← Execution.getTy) (← getNats) (← getNats) channel
  | 11 => return .assertEq (← getNats) (← getNats) ⟨← getOption getString, ← getBool⟩
  | 12 => return .ret (← getNats)
  | 13 => return .fail (← getString)
  | _ => return .ptrEq (← getNat) (← getNat) (← getNat)

/-- The program section `Export.putProgramWithEncoding` writes, from the
bytecode version on. Entry IO interfaces become `interfaces`, in entry order. -/
def getProgram (wide : Bool) (modulus : Nat) : GetM (Execution.Export F) := do
  let bv ← getNat
  unless bv == Execution.bytecodeVersion do fail s!"unsupported bytecode version {bv}"
  let m ← getScalar wide
  unless m == modulus do fail s!"program modulus {m} is not {modulus}"
  let functions ← getList do
    let name ← getString
    let params ← getList Execution.getTy
    let result ← Execution.getTy
    let registers ← getNat
    let code ← getArray (getInstruction wide)
    return ({ name, params, result, registers, code } : Execution.Function F)
  let enums ← getList do
    let name ← getString
    let constructors ← getList (return ({ name := ← getString, fields := ← getList Execution.getTy } : ConstructorDecl))
    return ({ name, constructors } : EnumDecl)
  let rows ← getArray (getList (getScalar wide))
  for r in rows do
    unless r.all (· < modulus) do fail "a table value is not below the modulus"
  let tables ← getList do
    let name ← getString
    let type ← Execution.getTy
    let refs ← getNats
    let rs ← refs.mapM fun i => match rows[i]? with
      | some r => pure (r.map fun v => (v : F))
      | none => fail s!"table row {i} is outside the row pool"
    return ({ name, type, rows := rs } : Execution.Table F)
  let maps ← getList do
    let name ← getString
    let params ← getList Execution.getTy
    let result ← Execution.getTy
    let input ← getNat
    let output ← getNat
    return ({ name, params, result, input, output } : Execution.Map)
  let entries ← getList do
    let name ← getString
    let function ← getNat
    let inputs ← getList getIOType
    let output ← getOption getIOType
    return ((name, function), ({ name, inputs, output } : Execution.Interface))
  return { bytecode := { functions, enums, tables, maps, entries := entries.map (·.1) },
           interfaces := entries.map (·.2) }

/-- A package file whose program and trace sections use the modulus
`modulus`. -/
def getPackage (modulus : Nat) : GetM (Package F) := do
  let magic ← getRaw 8
  unless magic.data == Aiur.Artifact.packageMagic.data do fail "not an Aiur package"
  let version ← getNat
  unless version == 2 || version == 3 do fail s!"unsupported package version {version}"
  let wide := version == 3
  let program ← getProgram (F := F) wide modulus
  let code := program.bytecode
  let functions := code.functions.map (·.name)
  let tables := code.tables.toArray.map (·.rows)
  let maps := code.maps.map fun m => (m.name, m.input, m.output)
  let entries := code.entries.toArray
  let some () ← getOption (pure ()) | fail "the package has no trace section"
  let traceStart := (← get).pos
  let trace ← getTrace (F := F) wide modulus
  let limbs := trace.limbs
  let chips := (trace.chips.map (·.1)).toArray
  let groups := (trace.groups.map fun g => (g.name, g.members.map (·.name))).toArray
  let callables := (functions ++ maps.map (·.1)).toArray
  let mut mapClaims : Array (Nat × Array (List F)) := #[]
  for ((_, input, output), k) in maps.zipIdx do
    let some ins := tables[input]? | fail s!"map input table {input} is missing"
    let some outs := tables[output]? | fail s!"map output table {output} is missing"
    unless ins.length == outs.length do fail "a map's input and output tables differ in length"
    mapClaims := mapClaims.push (functions.length + k,
      ((ins.zip outs).map fun (a, b) => a ++ b).toArray)
  return { modulus, wide, callables, functions := functions.length, maps := mapClaims,
           entries, limbs, chips, groups, program, trace, traceStart }

/-- Decode a complete package file. -/
def decodePackage (modulus : Nat) (bytes : ByteArray) : Except String (Package F) :=
  Ixon.decode (getPackage modulus) bytes

end Decode

end Aiur.Tiling.Ixa
