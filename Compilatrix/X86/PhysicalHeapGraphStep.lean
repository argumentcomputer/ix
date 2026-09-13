import Compilatrix.X86.PhysicalHeapGraph

namespace Compilatrix.X86.PhysicalHeap.Graph

abbrev CodeAt (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) (point : Point) (tree : Tree) : Prop :=
  Code schemas constructors entries current definition point.block point.pc point.scope tree

structure Step (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) (point : Point) where
  shape : Shape Point
  sound : ∀ tree, Realizes (CodeAt schemas constructors entries current definition) shape tree →
    CodeAt schemas constructors entries current definition point tree

private structure Callee (entries : Interfaces) (current : Nat) (address : Ixon.Address) (kinds : Array Kind) where
  index : Nat
  target : Interface
  found : entries[index]? = some target
  earlier : index < current
  addressed : target.address = address
  parameters : target.parameters = kinds

private def callee (entries : Interfaces) (current : Nat) (address : Ixon.Address) (kinds : Array Kind) :
    Except String (Callee entries current address kinds) := do
  let some index := entries.findIdx? (fun row => row.address == address && row.parameters == kinds)
    | throw "heap graph callee has no earlier interface for these argument kinds"
  match found : entries[index]? with
  | none => throw "heap graph callee index is missing"
  | some target =>
    if earlier : index < current then
      if addressed : target.address = address then
        if parameters : target.parameters = kinds then return ⟨index, target, found, earlier, addressed, parameters⟩
        else throw "heap graph callee parameter kinds disagree"
      else throw "heap graph callee address disagrees"
    else throw "heap graph call is not earlier in the nonrecursive order"

/-- Select one point, checking its actual syntax and complete ownership scope.
Child selection is separate, so repeated continuations can be referenced. -/
def selectStep (schemas : Schemas) (constructors : Array IxIR2.CtorId)
    (entries : Interfaces) (current : Nat) (definition : IxIR2.Function) (point : Point) :
    Except String (Step schemas constructors entries current definition point) := do
  let block := point.block
  let pc := point.pc
  let scope := point.scope
  match blockAt : definition.blocks[block]? with
  | none => throw "heap graph block is missing"
  | some body =>
    match instructionAt : body.instructions[pc]? with
    | some (.call address arguments) =>
      let selected ← selectArgumentsChecked scope arguments
      let called ← callee entries current address selected.kinds
      let pushed ← checkedExcept (selected.next.pushValue called.target.result)
      return {
        shape := .call called.index selected.operands scope.values.size ⟨block, pc + 1, pushed.val⟩
        sound := by
          intro tree realized
          cases realized with
          | call rest =>
            exact .call blockAt instructionAt selected.code called.found called.earlier
              called.addressed called.parameters pushed.property rest }
    | some instruction =>
      let selected ← selectPrimitiveChecked schemas constructors scope instruction
      return {
        shape := .primitive selected.operation ⟨block, pc + 1, selected.next⟩
        sound := by
          intro tree realized
          cases realized with
          | primitive rest => exact .primitive blockAt instructionAt selected.code rest }
    | none =>
      if endAt : pc = body.instructions.size then
        match term : body.terminator with
        | .ret source =>
          let taken ← checkedExcept (scope.take source)
          if finished : taken.val.2.2.finished = true then
            return {
              shape := .ret taken.val.1 taken.val.2.1
              sound := by
                intro tree realized
                cases realized
                exact .ret blockAt endAt term taken.property finished }
          else throw "heap graph return leaves an owning value or credit behind"
        | .jump edge =>
          let selected ← selectTransferChecked definition scope edge
          return {
            shape := .jump selected.transfer ⟨edge.target, 0, selected.transfer.scope⟩
            sound := by
              intro tree realized
              cases realized with
              | jump rest => exact .jump blockAt endAt term selected.code rest }
        | .switchValue source alternatives peel =>
          match scalar : scope.scalar source with
          | .ok value =>
            match peeled : peel with
            | none => throw "heap graph scalar switch has no Nat peel"
            | some peel =>
              let zero ← selectTransferChecked definition scope peel.zero
              let succ ← selectTransferChecked definition scope peel.succ (some value)
              return {
                shape := .branch value zero.transfer ⟨peel.zero.target, 0, zero.transfer.scope⟩
                  succ.transfer ⟨peel.succ.target, 0, succ.transfer.scope⟩
                sound := by
                  intro tree realized
                  cases realized with
                  | branch same left right =>
                    exact .branch blockAt endAt (by simpa only [peeled] using term) scalar
                      zero.code succ.code same left right }
          | .error _ =>
            let node ← checkedExcept (scope.node source)
            let some alternative := alternatives[0]? | throw "heap graph constructor switch is empty"
            if single : alternatives = #[alternative] then
              let selected ← selectTransferChecked definition scope alternative.edge
              return {
                shape := .jump selected.transfer ⟨alternative.edge.target, 0, selected.transfer.scope⟩
                sound := by
                  intro tree realized
                  cases realized with
                  | jump rest =>
                    exact .constructor (peel := peel) blockAt endAt
                      (by simpa only [single] using term) node.property selected.code rest }
            else throw "heap graph constructor switch requires a single constructor alternative"
        | .branchCredit credit yes no =>
          match active : scope.credits[credit]? with
          | some (some layout) =>
            let selected ← selectTransferChecked definition scope yes
            return {
              shape := .jump selected.transfer ⟨yes.target, 0, selected.transfer.scope⟩
              sound := by
                intro tree realized
                cases realized with
                | jump rest => exact .present blockAt endAt term active selected.code rest }
          | _ => throw "heap graph credit branch has no live reservation"
        | .tailCall address arguments =>
          let selected ← selectArgumentsChecked scope arguments
          if finished : selected.next.finished = true then
            let called ← callee entries current address selected.kinds
            return {
              shape := .tailCall called.target.result called.index selected.operands
              sound := by
                intro tree realized
                cases realized
                exact .tailCall blockAt endAt term selected.code finished called.found called.earlier
                  called.addressed called.parameters }
          else throw "heap graph tail call leaves an owning value or credit behind"
        | _ => throw "heap graph terminator is outside the nonrecursive fragment"
      else throw "heap graph instruction position passed the terminator"

end Compilatrix.X86.PhysicalHeap.Graph
