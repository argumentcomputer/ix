import Ix.Compiler.X86.PhysicalScalar

namespace Ix.Compiler.X86.PhysicalScalar

def maxDepth : Nat := 128
def maxWork : Nat := 4096

private abbrev Build := StateT Nat (Except String)

private def tick : Build Unit := do
  match ← get with
  | 0 => throw "physical scalar CFG expansion exceeds its work limit"
  | remaining + 1 => set remaining

private def atom (bindings : Array Scalar.Atom) (source : IxIR2.Atom) :
    Build { target : Scalar.Atom // lowerAtom bindings source = some target } :=
  match _found : lowerAtom bindings source with
  | none => throw "physical scalar operand is not an in-scope register or exact Word Nat"
  | some target => pure ⟨target, rfl⟩

private def atoms (bindings : Array Scalar.Atom) (source : Array IxIR2.Atom) :
    Build { target : Array Scalar.Atom // lowerAtoms bindings source = some target } :=
  match _found : lowerAtoms bindings source with
  | none => throw "physical scalar arguments contain an unsupported operand"
  | some target => pure ⟨target, rfl⟩

private def edge (definition : IxIR2.Function) (source : IxIR2.Edge)
    (arguments : Array Scalar.Atom) (implicitCount : Nat) :
    Build (PLift (EdgeReady definition source arguments implicitCount)) := do
  match found : definition.blocks[source.target]? with
  | none => throw "physical scalar edge targets a missing block"
  | some target =>
    if arity : implicitCount + arguments.size = target.valueParams.size then
      if credits : source.credits = #[] then
        if targetCredits : target.creditParams = #[] then
          return ⟨.mk target found arity credits targetCredits⟩
        else throw "physical scalar edge requires reuse credits"
      else throw "physical scalar edge transfers reuse credits"
    else throw "physical scalar edge has the wrong value arity"

private def callee (entries : Entries) (current : Nat) (address : Ixon.Address)
    (arguments : Array Scalar.Atom) :
    Build { index : Nat // ∃ definition, entries[index]? = some (address, definition) ∧
      index < current ∧ arguments.size = definition.signature.params.size } := do
  let some index := entries.findIdx? (·.1 == address) | throw "physical scalar direct callee is missing"
  match found : entries[index]? with
  | none => throw "physical scalar callee index is missing"
  | some (actual, definition) =>
    if same : actual = address then
      if earlier : index < current then
        if arity : arguments.size = definition.signature.params.size then
          return ⟨index, definition, by simpa [same] using found, earlier, arity⟩
        else throw "physical scalar call has the wrong argument arity"
      else throw "physical scalar calls must target earlier nonrecursive functions"
    else throw "physical scalar callee address disagrees"

private def lowerCode (entries : Entries) (current : Nat) (definition : IxIR2.Function) :
    Nat → (block pc : Nat) → (bindings : Array Scalar.Atom) → (locals : Nat) →
      Build { expression : Scalar.Expr // Code entries current definition block pc bindings locals expression }
  | 0, _, _, _, _ => throw "physical scalar CFG is cyclic or exceeds the depth limit"
  | fuel + 1, block, pc, bindings, locals => do
    tick
    if locals > Scalar.maxLocals then throw "physical scalar path exceeds its local slot limit"
    match blockAt : definition.blocks[block]? with
    | none => throw "physical scalar current block is missing"
    | some body =>
      match instruction : body.instructions[pc]? with
      | some (.move source) =>
        let target ← atom bindings source
        let rest ← lowerCode entries current definition fuel block (pc + 1) (bindings.push target.val) locals
        return ⟨rest.val, .move blockAt instruction target.property rest.property⟩
      | some (.retainShared source) =>
        let target ← atom bindings source
        let rest ← lowerCode entries current definition fuel block (pc + 1) (bindings.push target.val) locals
        return ⟨rest.val, .retain blockAt instruction target.property rest.property⟩
      | some (.releaseShared source) =>
        let target ← atom bindings source
        let rest ← lowerCode entries current definition fuel block (pc + 1) bindings locals
        return ⟨rest.val, .release blockAt instruction target.property rest.property⟩
      | some (.dropUnique source) =>
        let target ← atom bindings source
        let rest ← lowerCode entries current definition fuel block (pc + 1) bindings locals
        return ⟨rest.val, .drop blockAt instruction target.property rest.property⟩
      | some (.call address source) =>
        let arguments ← atoms bindings source
        let called ← callee entries current address arguments.val
        let rest ← lowerCode entries current definition fuel block (pc + 1) (bindings.push (.var locals)) (locals + 1)
        return ⟨.letE (.call called.val arguments.val) rest.val, by
          obtain ⟨definition, found, earlier, arity⟩ := called.property
          exact .call blockAt instruction arguments.property found earlier arity rest.property⟩
      | some _ => throw "physical scalar instruction is outside the admitted fragment"
      | none =>
        if endAt : pc = body.instructions.size then
          match term : body.terminator with
          | .ret source =>
            let target ← atom bindings source
            return ⟨.atom target.val, .ret blockAt endAt term target.property⟩
          | .jump source =>
            let arguments ← atoms bindings source.values
            let ready ← edge definition source arguments.val 0
            let rest ← lowerCode entries current definition fuel source.target 0 arguments.val locals
            return ⟨rest.val, .jump blockAt endAt term arguments.property ready.down rest.property⟩
          | .switchValue source constructors (some peel) =>
            if empty : constructors = #[] then
              let target ← atom bindings source
              let zeroArgs ← atoms bindings peel.zero.values
              let succArgs ← atoms bindings peel.succ.values
              let zeroReady ← edge definition peel.zero zeroArgs.val 0
              let succReady ← edge definition peel.succ succArgs.val 1
              let zero ← lowerCode entries current definition fuel peel.zero.target 0 zeroArgs.val locals
              let successor ← lowerCode entries current definition fuel peel.succ.target 0
                (#[.var locals] ++ succArgs.val) (locals + 1)
              return ⟨.branch target.val zero.val (.letE (.sub target.val (.constant 1)) successor.val),
                .branch blockAt endAt (by simpa [empty] using term) target.property zeroArgs.property succArgs.property
                  zeroReady.down succReady.down zero.property successor.property⟩
            else throw "physical scalar switch has constructor alternatives"
          | .tailCall address source =>
            let arguments ← atoms bindings source
            let called ← callee entries current address arguments.val
            return ⟨.call called.val arguments.val, by
              obtain ⟨definition, found, earlier, arity⟩ := called.property
              exact .tailCall blockAt endAt term arguments.property found earlier arity⟩
          | _ => throw "physical scalar terminator is outside the admitted fragment"
        else throw "physical scalar instruction position passed the terminator"

private def dependencies (definition : IxIR2.Function) : List Ixon.Address :=
  definition.blocks.toList.flatMap fun block =>
    block.instructions.toList.filterMap (fun | .call address _ => some address | _ => none) ++
      match block.terminator with | .tailCall address _ => [address] | _ => []

private def discover (program : IxIR2.Program) : Nat → Entries → Ixon.Address → Except String Entries
  | 0, _, _ => throw "physical scalar call graph is recursive or exceeds its depth limit"
  | fuel + 1, entries, address => do
    if entries.any (·.1 == address) then return entries
    let some (.fn definition) := lookup program address | throw "physical scalar entry/callee is not a declared function"
    if definition.blocks.size > maxDepth || definition.blocks.any (·.instructions.size > maxDepth) then
      throw "physical scalar function exceeds its block or instruction limit"
    let mut entries := entries
    for dependency in dependencies definition do
      entries ← discover program fuel entries dependency
    if entries.size >= Scalar.maxFunctions then throw "physical scalar call graph exceeds its function limit"
    return entries.push (address, definition)

structure Row (entries : Entries) where
  index : Nat
  address : Ixon.Address
  definition : IxIR2.Function
  target : Scalar.Function
  arity : target.parameters = definition.signature.params.size
  nonempty : definition.blocks.isEmpty = false
  code : Code entries index definition 0 0 (parameters target.parameters) target.parameters target.body

private def lowerFunction (entries : Entries) (index : Nat) (address : Ixon.Address) (definition : IxIR2.Function) :
    Except String (Row entries) := do
  let count := definition.signature.params.size
  if count > 2 then throw "physical scalar function has more than two parameters"
  if nonempty : definition.blocks.isEmpty = false then
    let (body, _) ← (lowerCode entries index definition maxDepth 0 0 (parameters count) count).run maxWork
    return { index, address, definition, target := ⟨count, body.val⟩, arity := rfl, nonempty, code := body.property }
  else throw "physical scalar function has no entry block"

structure Selected (program : IxIR2.Program) (root : Ixon.Address) where
  entries : Entries
  rows : Array (Row entries)
  declared : entries.all (fun (address, definition) => lookup program address == some (.fn definition)) = true
  indexed : (rows.toList.zipIdx).all (fun (row, index) => row.index == index && entries[index]? == some (row.address, row.definition)) = true
  complete : rows.size = entries.size
  scalar : Scalar.Checked
  functions : scalar.program.functions = rows.map (·.target)
  rootFound : (entries[scalar.program.entry]?).map (·.1) = some root

/-- Select an actual physical function from a checked source artifact or an
explicit CFG input. The certificates are independent of runtime arguments. -/
def select (program : IxIR2.Program) (root : Ixon.Address) : Except String (Selected program root) := do
  let entries ← discover program Scalar.maxFunctions #[] root
  let mut rows := #[]
  for index in [:entries.size] do
    let (address, definition) := entries[index]!
    rows := rows.push (← lowerFunction entries index address definition)
  let target : Scalar.Program := { functions := rows.map (·.target), entry := entries.size - 1 }
  let some scalar := Scalar.check target | throw "physical scalar output exceeds native scope, call, or size limits"
  if declared : entries.all (fun (address, definition) => lookup program address == some (.fn definition)) = true then
    if indexed : (rows.toList.zipIdx).all (fun (row, index) => row.index == index && entries[index]? == some (row.address, row.definition)) = true then
      if complete : rows.size = entries.size then
        if functions : scalar.program.functions = rows.map (·.target) then
          if rootFound : (entries[scalar.program.entry]?).map (·.1) = some root then
            return { entries, rows, declared, indexed, complete, scalar, functions, rootFound }
          else throw "physical scalar selected root disagrees"
        else throw "physical scalar native functions disagree"
      else throw "physical scalar function table is incomplete"
    else throw "physical scalar function table indices disagree"
  else throw "physical scalar declaration lookup disagrees"

end Ix.Compiler.X86.PhysicalScalar
