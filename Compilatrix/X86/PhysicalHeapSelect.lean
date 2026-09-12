import Compilatrix.X86.PhysicalHeapCode

namespace Compilatrix.X86.PhysicalHeap

def maxDepth : Nat := 128
def maxWork : Nat := 4096
def maxFunctions : Nat := 32
def maxAllocations : Nat := 64
def maxControls : Nat := 1048576

private abbrev Build := StateT Nat (Except String)

private def tick : Build Unit := do
  match ← get with
  | 0 => throw "heap CFG expansion exceeds 4096 visited points"
  | remaining + 1 => set remaining

private def witnessed {α : Type} (value : Except String α) :
    Except String { result : α // value = .ok result } :=
  match _found : value with
  | .error message => .error message
  | .ok result => .ok ⟨result, rfl⟩

private def callee (entries : Interfaces) (current : Nat) (address : Ixon.Address) (kinds : Array Kind) :
    Except String { index : Nat // ∃ target, entries[index]? = some target ∧ index < current ∧
      target.address = address ∧ target.parameters = kinds } := do
  let some index := entries.findIdx? (fun entry => entry.address == address && entry.parameters == kinds)
    | throw "heap CFG callee has no earlier interface for these argument kinds"
  match found : entries[index]? with
  | none => throw "heap CFG callee index is missing"
  | some target =>
    if earlier : index < current then
      if addressed : target.address = address then
        if parameters : target.parameters = kinds then
          return ⟨index, target, found, earlier, addressed, parameters⟩
        else throw "heap CFG callee parameter kinds disagree"
      else throw "heap CFG callee address disagrees"
    else throw "heap CFG call is not earlier in the nonrecursive order"

private def lowerCode (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) :
    Nat → (block pc : Nat) → (scope : Scope) →
      Build { tree : Tree // Code schemas constructors entries current definition block pc scope tree }
  | 0, _, _, _ => throw "heap CFG is cyclic or exceeds the depth limit"
  | fuel + 1, block, pc, scope => do
    tick
    match blockAt : definition.blocks[block]? with
    | none => throw "heap CFG block is missing"
    | some body =>
      match instructionAt : body.instructions[pc]? with
      | some (.call address arguments) =>
        let selected ← selectArgumentsChecked scope arguments
        let kinds := selected.kinds
        let operands := selected.operands
        let consumed := selected.next
        let called ← callee entries current address kinds
        match found : entries[called.val]? with
        | none => throw "heap CFG callee vanished"
        | some target =>
          let pushed ← witnessed (consumed.pushValue target.result)
          let rest ← lowerCode schemas constructors entries current definition fuel block (pc + 1) pushed.val
          return ⟨.call called.val operands scope.values.size rest.val, by
            obtain ⟨actual, actualAt, earlier, addressed, parameters⟩ := called.property
            have equal := Option.some.inj (actualAt.symm.trans found)
            subst actual
            exact .call blockAt instructionAt selected.code found earlier addressed parameters pushed.property rest.property⟩
      | some instruction =>
        let selected ← selectPrimitiveChecked schemas constructors scope instruction
        let rest ← lowerCode schemas constructors entries current definition fuel block (pc + 1) selected.next
        return ⟨.primitive selected.operation rest.val, .primitive blockAt instructionAt selected.code rest.property⟩
      | none =>
        if endAt : pc = body.instructions.size then
          match term : body.terminator with
          | .ret source =>
            let taken ← witnessed (scope.take source)
            let kind := taken.val.1
            let value := taken.val.2.1
            let next := taken.val.2.2
            if finished : next.finished = true then
              return ⟨.ret kind value, .ret blockAt endAt term taken.property finished⟩
            else throw "heap CFG return leaves an owning value or credit behind"
          | .jump edge =>
            let selected ← selectTransferChecked definition scope edge
            let rest ← lowerCode schemas constructors entries current definition fuel edge.target 0 selected.transfer.scope
            return ⟨.jump selected.transfer rest.val, .jump blockAt endAt term selected.code rest.property⟩
          | .switchValue source alternatives peel =>
            match scalar : scope.scalar source with
            | .ok value =>
              match peeled : peel with
              | none => throw "heap CFG scalar switch has no Nat peel"
              | some peel =>
                let zeroSelected ← selectTransferChecked definition scope peel.zero
                let succSelected ← selectTransferChecked definition scope peel.succ (some value)
                let zero ← lowerCode schemas constructors entries current definition fuel peel.zero.target 0 zeroSelected.transfer.scope
                let successor ← lowerCode schemas constructors entries current definition fuel peel.succ.target 0 succSelected.transfer.scope
                if sameResult : zero.val.result = successor.val.result then
                  return ⟨.branch value zeroSelected.transfer zero.val succSelected.transfer successor.val,
                    .branch blockAt endAt (by simpa only [peeled] using term) scalar zeroSelected.code
                      succSelected.code sameResult zero.property successor.property⟩
                else throw "heap CFG Nat branches return different value kinds"
            | .error _ =>
              let node ← witnessed (scope.node source)
              let some alternative := alternatives[0]? | throw "heap CFG constructor switch is empty"
              if single : alternatives = #[alternative] then
                let selected ← selectTransferChecked definition scope alternative.edge
                let rest ← lowerCode schemas constructors entries current definition fuel alternative.edge.target 0 selected.transfer.scope
                return ⟨.jump selected.transfer rest.val,
                  .constructor (peel := peel) blockAt endAt (by simpa only [single] using term) node.property selected.code rest.property⟩
              else throw "heap CFG constructor switch requires a single constructor alternative"
          | .branchCredit credit yes no =>
            match active : scope.credits[credit]? with
            | some (some layout) =>
              let selected ← selectTransferChecked definition scope yes
              let rest ← lowerCode schemas constructors entries current definition fuel yes.target 0 selected.transfer.scope
              return ⟨.jump selected.transfer rest.val, .present blockAt endAt term active selected.code rest.property⟩
            | _ => throw "heap CFG credit branch has no live reservation"
          | .tailCall address arguments =>
            let selected ← selectArgumentsChecked scope arguments
            let kinds := selected.kinds
            let operands := selected.operands
            let consumed := selected.next
            if finished : consumed.finished = true then
              let called ← callee entries current address kinds
              match found : entries[called.val]? with
              | none => throw "heap CFG tail callee vanished"
              | some target =>
                return ⟨.tailCall target.result called.val operands, by
                  obtain ⟨actual, actualAt, earlier, addressed, parameters⟩ := called.property
                  have equal := Option.some.inj (actualAt.symm.trans found)
                  subst actual
                  exact .tailCall blockAt endAt term selected.code finished found earlier addressed parameters⟩
            else throw "heap CFG tail call leaves an owning value or credit behind"
          | _ => throw "heap CFG terminator is outside the nonrecursive fragment"
        else throw "heap CFG instruction position passed the terminator"

private def dependencies (definition : IxIR2.Function) : List Ixon.Address :=
  definition.blocks.toList.flatMap fun block =>
    block.instructions.toList.filterMap (fun | .call address _ => some address | _ => none) ++
      match block.terminator with | .tailCall address _ => [address] | _ => []

private def discover (program : IxIR2.Program) : Nat → PhysicalScalar.Entries → Ixon.Address → Except String PhysicalScalar.Entries
  | 0, _, _ => throw "heap CFG call graph is recursive or exceeds 32 functions"
  | fuel + 1, entries, address => do
    if entries.any (·.1 == address) then return entries
    let some (.fn definition) := PhysicalScalar.lookup program address | throw "heap CFG entry/callee is not a function"
    if definition.blocks.size > maxDepth || definition.blocks.any (·.instructions.size > maxDepth) then
      throw "heap CFG source function exceeds the block/instruction limits"
    let mut entries := entries
    for dependency in dependencies definition do
      entries ← discover program fuel entries dependency
    if entries.size >= maxFunctions then throw "heap CFG declaration graph exceeds 32 functions"
    return entries.push (address, definition)

private def instructionConstructors : IxIR2.Instr → List IxIR2.CtorId
  | .alloc _ cid _ | .allocWith _ _ cid _ | .takeUnique _ cid | .resetShared _ cid |
    .freeUnique _ cid | .fetch _ cid _ => [cid]
  | _ => []

private def collectConstructors (entries : PhysicalScalar.Entries) : Except String (Array IxIR2.CtorId) := do
  let mut constructors := #[]
  for (_, definition) in entries do
    for block in definition.blocks do
      for instruction in block.instructions do
        for cid in instructionConstructors instruction do
          if !constructors.contains cid then
            if constructors.size >= maxConstructors then throw "heap CFG constructor registry exceeds 32 identities"
            constructors := constructors.push cid
  return constructors

/-- At most nine parameter profiles exist for a two-argument helper.
Profiles are checked once in dependency order; unsupported profiles are
discarded. Calls select the exact scalar/node profile, independently of data.
-/
def profiles : Nat → Array (Array Kind)
  | 0 => #[#[]]
  | 1 => #[#[.scalar], #[.node], #[.erased]]
  | 2 => #[#[.scalar, .scalar], #[.scalar, .node], #[.scalar, .erased],
      #[.node, .scalar], #[.node, .node], #[.node, .erased],
      #[.erased, .scalar], #[.erased, .node], #[.erased, .erased]]
  | _ => #[]

structure PendingRow (schemas : Schemas) (constructors : Array IxIR2.CtorId) where
  prior : Interfaces
  interface : Interface
  source : FunctionCode schemas constructors prior prior.size interface

private def lowerFunction (schemas : Schemas) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (address : Ixon.Address) (definition : IxIR2.Function) (parameters : Array Kind) :
    Except String (PendingRow schemas constructors) := do
  if arity : parameters.size = definition.signature.params.size then
    if small : parameters.size ≤ 2 then
      if owned : definition.signature.params.all (·.passing == .owned) = true then
        if nonempty : definition.blocks.isEmpty = false then
          let (tree, _) ← (lowerCode schemas constructors entries entries.size definition maxDepth 0 0 (Scope.initial parameters)).run maxWork
          let allocations := tree.val.allocations (entries.map (·.allocations))
          if allocations > maxAllocations then throw "heap CFG allocation demand exceeds 64 cells"
          let controls := tree.val.controls (entries.map (·.controls))
          if controls > maxControls then throw "heap CFG execution bound exceeds 1048576 physical control steps"
          let interface : Interface := {
            address, definition, parameters, result := tree.val.result, allocations, controls }
          return { prior := entries, interface, source := {
            tree := tree.val, arity, small, owned, nonempty, result := rfl, allocations := rfl, controls := rfl, code := tree.property } }
        else throw "heap CFG function has no entry block"
      else throw "heap CFG borrowed function parameters are unsupported"
    else throw "heap CFG function has more than two parameters"
  else throw "heap CFG function profile has the wrong arity"

structure Row (schemas : Schemas) (constructors : Array IxIR2.CtorId) (entries : Interfaces) where
  index : Nat
  interface : Interface
  found : entries[index]? = some interface
  source : FunctionCode schemas constructors entries index interface

private def finishRow (schemas : Schemas) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (pending : PendingRow schemas constructors) : Except String (Row schemas constructors entries) := do
  if found : entries[pending.prior.size]? = some pending.interface then
    if accepted : pending.prior.toList.zipIdx.all (fun (entry, index) => entries[index]? == some entry) = true then
      let same : ∀ (index : Nat) (callee : Interface), pending.prior[index]? = some callee → entries[index]? = some callee := by
        intro index callee present
        have member : (callee, index) ∈ pending.prior.toList.zipIdx :=
          List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa only [Array.getElem?_toList] using present)
        exact beq_iff_eq.mp (List.all_eq_true.mp accepted (callee, index) member)
      return { index := pending.prior.size, interface := pending.interface, found, source := pending.source.weaken same }
    else throw "heap CFG earlier interfaces changed during selection"
  else throw "heap CFG interface order changed during selection"

structure Selected (schemas : Schemas) (program : IxIR2.Program) (root : Ixon.Address) where
  constructors : Array IxIR2.CtorId
  entries : Interfaces
  rows : Array (Row schemas constructors entries)
  declared : entries.all (fun entry => PhysicalScalar.lookup program entry.address == some (.fn entry.definition)) = true
  indexed : rows.toList.zipIdx.all (fun (row, index) => row.index == index) = true
  complete : rows.size = entries.size
  entry : Nat
  entryInterface : Interface
  entryFound : entries[entry]? = some entryInterface
  entryAddress : entryInterface.address = root
  entryParameters : entryInterface.parameters.all (· == .scalar) = true
  entryResult : entryInterface.result = .scalar
  functionsBound : entries.size ≤ maxFunctions
  allocationBound : entryInterface.allocations ≤ maxAllocations
  controlBound : entryInterface.controls ≤ maxControls

def select (schemas : Schemas) (program : IxIR2.Program) (root : Ixon.Address) :
    Except String (Selected schemas program root) := do
  let declarations ← discover program maxFunctions #[] root
  let constructors ← collectConstructors declarations
  let mut entries : Interfaces := #[]
  let mut pending : Array (PendingRow schemas constructors) := #[]
  for (address, definition) in declarations do
    for parameters in profiles definition.signature.params.size do
      match lowerFunction schemas constructors entries address definition parameters with
      | .error _ => pure ()
      | .ok row =>
        if entries.size >= maxFunctions then throw "heap CFG accepted interfaces exceed 32 functions"
        entries := entries.push row.interface
        pending := pending.push row
  let rows ← pending.mapM (finishRow schemas constructors entries)
  let some entry := entries.findIdx? (fun entry => entry.address == root && entry.parameters.all (· == .scalar))
    | throw "heap CFG entry has no admitted scalar-argument interface"
  match entryFound : entries[entry]? with
  | none => throw "heap CFG selected entry is missing"
  | some entryInterface =>
    if declared : entries.all (fun entry => PhysicalScalar.lookup program entry.address == some (.fn entry.definition)) = true then
      if indexed : rows.toList.zipIdx.all (fun (row, index) => row.index == index) = true then
        if complete : rows.size = entries.size then
          if entryAddress : entryInterface.address = root then
            if entryParameters : entryInterface.parameters.all (· == .scalar) = true then
              if entryResult : entryInterface.result = .scalar then
                if functionsBound : entries.size ≤ maxFunctions then
                  if allocationBound : entryInterface.allocations ≤ maxAllocations then
                    if controlBound : entryInterface.controls ≤ maxControls then
                      return {
                        constructors, entries, rows, declared, indexed, complete, entry, entryInterface, entryFound
                        entryAddress, entryParameters, entryResult, functionsBound, allocationBound, controlBound }
                    else throw "heap CFG entry control bound exceeds the finite execution budget"
                  else throw "heap CFG entry allocation demand exceeds the arena"
                else throw "heap CFG native function bound changed"
              else throw "heap CFG entry must consume its constructors and return a scalar"
            else throw "heap CFG entry argument profile changed"
          else throw "heap CFG entry address changed"
        else throw "heap CFG function coverage is incomplete"
      else throw "heap CFG function indices disagree"
    else throw "heap CFG declaration lookup changed"

end Compilatrix.X86.PhysicalHeap
