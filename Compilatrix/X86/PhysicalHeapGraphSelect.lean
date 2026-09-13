import Compilatrix.X86.PhysicalHeapSelect
import Compilatrix.X86.PhysicalHeapGraphBuild

namespace Compilatrix.X86.PhysicalHeap.Graph

structure Pending {schemas : Schemas} {constructors : Array IxIR2.CtorId} where
  row : PendingRow schemas constructors
  graph : Root row.source.tree

/-- Check a function graph, including its exact initial profile and the
existing physical allocation/control bounds. No recursive tree query runs. -/
def checkFunction (schemas : Schemas) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (address : Ixon.Address) (definition : IxIR2.Function) (parameters : Array Kind)
    (candidate : Candidate) (limits : Limits := {}) : Except String (Pending (schemas := schemas) (constructors := constructors)) := do
  if arity : parameters.size = definition.signature.params.size then
    if small : parameters.size ≤ 2 then
      if owned : definition.signature.params.all (·.passing == .owned) = true then
        if nonempty : definition.blocks.isEmpty = false then
          let checked ← checkBody schemas constructors entries entries.size definition candidate limits
          match found : checked.body.cells[candidate.entry]? with
          | none => throw "heap graph entry is missing"
          | some root =>
            if initial : root.node.point = ⟨0, 0, Scope.initial parameters⟩ then
              let summary := root.summary
              if summary.allocations > maxAllocations then throw "heap graph allocation demand exceeds 64 cells"
              if summary.controls > maxControls then throw "heap graph execution bound exceeds 1048576 physical control steps"
              let member := Array.mem_of_getElem? found
              let resources := checked.summaries root member
              let interface : Interface := {
                address, definition, parameters, result := summary.result,
                allocations := summary.allocations, controls := summary.controls }
              let source : FunctionCode schemas constructors entries entries.size interface := {
                tree := root.tree, arity, small, owned, nonempty,
                result := resources.1, allocations := resources.2.1, controls := resources.2.2
                code := by
                  have code := checked.typed root member
                  rw [initial] at code
                  exact code }
              return {
                row := { prior := entries, interface, source }
                graph := ⟨checked.body, candidate.entry, root, found, rfl⟩ }
            else throw "heap graph entry has the wrong source point or initial profile"
        else throw "heap graph function has no entry block"
      else throw "heap graph borrowed function parameters are unsupported"
    else throw "heap graph function has more than two parameters"
  else throw "heap graph function profile has the wrong arity"

def lowerFunction (schemas : Schemas) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (address : Ixon.Address) (definition : IxIR2.Function) (parameters : Array Kind)
    (limits : Limits := {}) : Except String (Pending (schemas := schemas) (constructors := constructors)) := do
  let candidate ← propose schemas constructors entries entries.size definition ⟨0, 0, Scope.initial parameters⟩ limits
  checkFunction schemas constructors entries address definition parameters candidate limits

structure Row (schemas : Schemas) (constructors : Array IxIR2.CtorId) (entries : Interfaces) where
  row : PhysicalHeap.Row schemas constructors entries
  graph : Root row.source.tree

def finish (schemas : Schemas) (constructors : Array IxIR2.CtorId) (entries : Interfaces)
    (pending : Pending (schemas := schemas) (constructors := constructors)) : Except String (Row schemas constructors entries) := do
  let row ← checkedExcept (finishRow schemas constructors entries pending.row)
  return {
    row := row.val
    graph := by
      rw [finishRow_tree row.property]
      exact pending.graph }

structure Selected (schemas : Schemas) (program : IxIR2.Program) (root : Ixon.Address) where
  selected : PhysicalHeap.Selected schemas program root
  graphs : Array (Row schemas selected.constructors selected.entries)
  same : graphs.map (·.row) = selected.rows

def select (schemas : Schemas) (program : IxIR2.Program) (root : Ixon.Address)
    (limits : Limits := {}) : Except String (Selected schemas program root) := do
  let declarations ← discover program maxFunctions #[] root
  let constructors ← collectConstructors declarations
  let mut entries : Interfaces := #[]
  let mut pending : Array (Pending (schemas := schemas) (constructors := constructors)) := #[]
  for (address, definition) in declarations do
    for parameters in profiles definition.signature.params.size do
      match lowerFunction schemas constructors entries address definition parameters limits with
      | .error _ => pure ()
      | .ok row =>
        if entries.size >= maxFunctions then throw "heap graph accepted interfaces exceed 32 functions"
        entries := entries.push row.row.interface
        pending := pending.push row
  let graphs ← pending.mapM (finish schemas constructors entries)
  let rows := graphs.map (·.row)
  let some entry := entries.findIdx? (fun entry => entry.address == root && entry.parameters.all (· == .scalar))
    | throw "heap graph entry has no admitted scalar-argument interface"
  match entryFound : entries[entry]? with
  | none => throw "heap graph selected entry is missing"
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
                        selected := {
                          constructors, entries, rows, declared, indexed, complete, entry, entryInterface, entryFound
                          entryAddress, entryParameters, entryResult, functionsBound, allocationBound, controlBound }
                        graphs, same := rfl }
                    else throw "heap graph entry control bound exceeds the finite execution budget"
                  else throw "heap graph entry allocation demand exceeds the arena"
                else throw "heap graph native function bound changed"
              else throw "heap graph entry must consume its constructors and return a scalar"
            else throw "heap graph entry argument profile changed"
          else throw "heap graph entry address changed"
        else throw "heap graph function coverage is incomplete"
      else throw "heap graph function indices disagree"
    else throw "heap graph declaration lookup changed"

end Compilatrix.X86.PhysicalHeap.Graph
