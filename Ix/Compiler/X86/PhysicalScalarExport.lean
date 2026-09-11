import Ix.Compiler.X86.PhysicalScalarObject

namespace Ix.Compiler.X86.PhysicalScalar
open IxIR2.Eval

def papBlock (address : Ixon.Address) : IxIR2.Block :=
  { valueParams := #[], creditParams := #[], instructions := #[.papp address #[]], terminator := .ret (.reg 0) }

def tailBlock (address : Ixon.Address) : IxIR2.Block :=
  { valueParams := #[], creditParams := #[], instructions := #[], terminator := .tailCall address #[] }

/-- The module's exported value must be an uncaptured function closure.
Nullary tail aliases may lead to that closure; runtime CFG selection starts
at its declared target. This adapter is separate from instruction selection. -/
inductive ExportPath (program : IxIR2.Program) (address : Ixon.Address) (target : IxIR2.Function) : IxIR2.Function → Prop where
  | closure {definition}
      (nullary : definition.signature.params.size = 0) (shared : definition.signature.result = .shared)
      (blocks : definition.blocks = #[papBlock address])
      (declared : lookup program address = some (.fn target))
      (papSafe : target.signature.papSafe = true) (positive : 0 < target.signature.params.size) :
      ExportPath program address target definition
  | tail {definition alias callee}
      (nullary : definition.signature.params.size = 0) (blocks : definition.blocks = #[tailBlock alias])
      (declared : lookup program alias = some (.fn callee))
      (rest : ExportPath program address target callee) : ExportPath program address target definition

theorem ExportPath.nullary {program address target definition} (path : ExportPath program address target definition) :
    definition.signature.params.size = 0 := by cases path <;> assumption

theorem ExportPath.nonempty {program address target definition} (path : ExportPath program address target definition) :
    definition.blocks.isEmpty = false := by cases path <;> simp_all

theorem ExportPath.declared {program address target definition} (path : ExportPath program address target definition) :
    lookup program address = some (.fn target) := by
  induction path with
  | closure _ _ _ declared _ _ => exact declared
  | tail _ _ _ _ ih => exact ih

theorem ExportPath.papSafe {program address target definition} (path : ExportPath program address target definition) :
    target.signature.papSafe = true := by
  induction path with
  | closure _ _ _ _ safe _ => exact safe
  | tail _ _ _ _ ih => exact ih

theorem ExportPath.positive {program address target definition} (path : ExportPath program address target definition) :
    0 < target.signature.params.size := by
  induction path with
  | closure _ _ _ _ _ positive => exact positive
  | tail _ _ _ _ ih => exact ih

def closureStore (address : Ixon.Address) (target : IxIR2.Function) : Store :=
  (({} : Store).allocNode .shared (.papN address target.signature.params.size #[])).1

theorem closureStore.view (address : Ixon.Address) (target : IxIR2.Function) :
    (closureStore address target).get? 0 = some ⟨.shared, 1, .papN address target.signature.params.size #[]⟩ := rfl

/-- The checked module entry really returns the closure selected for the
runtime ABI. No runtime scalar input is evaluated during this check. -/
theorem ExportPath.steps {program address target definition} (path : ExportPath program address target definition)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema)
    (oracle : Ixon.Address → List RVal → Option RVal) :
    ∃ count, IxIR2.Eval.Steps (Context.ofProgram program schemas oracle) .physical count
      (initialMachine definition #[] 0)
      { store := closureStore address target, heapFuel := 0, control := .halted (.loc 0) } := by
  induction path with
  | @closure definition nullary shared blocks declared papSafe positive =>
    let context := Context.ofProgram program schemas oracle
    let start := initialMachine definition #[] 0
    let middle : IxIR2.Eval.Machine := {
      store := closureStore address target, heapFuel := 0
      control := .running { definition, pc := 1, values := #[.loc 0] } [] }
    have allocated := Step.pappFn (context := context) (interpretation := .physical) (machine := start)
      (frame := { definition, values := #[] }) (block := papBlock address)
      rfl (by simp [blocks]) (by simp [papBlock]) rfl rfl declared papSafe rfl positive
    have allocated : Step context .physical start middle := allocated
    have returned : Step context .physical middle
        { store := closureStore address target, heapFuel := 0, control := .halted (.loc 0) } :=
      Step.retHalt (machine := middle) (block := papBlock address)
        rfl (by simp [blocks]) rfl rfl rfl rfl (by rw [shared]; rfl)
    exact ⟨2, (allocated.toSteps rfl).trans (returned.toSteps rfl)⟩
  | @tail definition alias callee nullary blocks declared rest ih =>
    obtain ⟨count, executed⟩ := ih
    have entered := Step.tailCallFn (context := Context.ofProgram program schemas oracle) (interpretation := .physical)
      (machine := initialMachine definition #[] 0) (frame := { definition, values := #[] }) (block := tailBlock alias)
      rfl (by simp [blocks]) rfl rfl rfl rfl declared rest.nullary.symm rest.nonempty
    refine ⟨count + 1, ?_⟩
    exact .cons rfl entered executed

theorem ExportPath.runMain {program address target} (path : ExportPath program address target program.main)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema)
    (oracle : Ixon.Address → List RVal → Option RVal) :
    ∃ count, runMain (Context.ofProgram program schemas oracle) .physical program count 0 =
      .ok { store := closureStore address target, value := .loc 0, controlRemaining := 0, heapRemaining := 0 } := by
  obtain ⟨count, steps⟩ := path.steps schemas oracle
  exact ⟨count, (runMain_eq_runMachine path.nullary path.nonempty).trans steps.runMachine_halted⟩

structure ExportedFrom (program : IxIR2.Program) (definition : IxIR2.Function) where
  address : Ixon.Address
  target : IxIR2.Function
  path : ExportPath program address target definition

private def resolveFrom (program : IxIR2.Program) : Nat → (definition : IxIR2.Function) → Except String (ExportedFrom program definition)
  | 0, _ => throw "physical scalar export aliases are cyclic or exceed the depth limit"
  | fuel + 1, definition => do
    if nullary : definition.signature.params.size = 0 then
      match _bodyAt : definition.blocks[0]? with
      | none => throw "physical scalar module export is missing"
      | some body =>
        match body.instructions.toList, body.terminator with
        | [.papp address #[]], .ret (.reg 0) =>
          if blocks : definition.blocks = #[papBlock address] then
            if shared : definition.signature.result = .shared then
              match declared : lookup program address with
              | some (.fn target) =>
                if papSafe : target.signature.papSafe = true then
                  if positive : 0 < target.signature.params.size then
                    return ⟨address, target, .closure nullary shared blocks declared papSafe positive⟩
                  else throw "physical scalar exported closure is saturated"
                else throw "physical scalar exported function is not PAP-safe"
              | _ => throw "physical scalar exported closure target is missing"
            else throw "physical scalar exported closure has the wrong ownership world"
          else throw "physical scalar exported closure wrapper has unsupported blocks"
        | [], .tailCall address #[] =>
          if blocks : definition.blocks = #[tailBlock address] then
            match declared : lookup program address with
            | some (.fn callee) =>
              let rest ← resolveFrom program fuel callee
              return ⟨rest.address, rest.target, .tail nullary blocks declared rest.path⟩
            | _ => throw "physical scalar export alias is missing"
          else throw "physical scalar export alias has unsupported blocks"
        | _, _ => throw "physical scalar module must export an uncaptured function closure"
    else throw "physical scalar module export wrapper is not nullary"

def resolveExport (program : IxIR2.Program) : Except String (ExportedFrom program program.main) :=
  resolveFrom program 32 program.main

structure Exported (program : IxIR2.Program) (provenance : ELF.Provenance) where
  source : ExportedFrom program program.main
  compiled : Compiled program source.address provenance
  same : compiled.definition = source.target

def compileExport (program : IxIR2.Program) (provenance : ELF.Provenance)
    (name : String := "compilatrix_physical_scalar") : Except String (Exported program provenance) := do
  let source ← resolveExport program
  let compiled ← compile program source.address provenance name
  if same : compiled.definition = source.target then return { source, compiled, same }
  else throw "physical scalar exported target differs from its selected definition"

def compileSourceExport {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (name : String := "compilatrix_physical_scalar") :
    Except String (Exported attached.target.artifact.program (sourceProvenance attached)) :=
  compileExport attached.target.artifact.program (sourceProvenance attached) name

end Ix.Compiler.X86.PhysicalScalar
