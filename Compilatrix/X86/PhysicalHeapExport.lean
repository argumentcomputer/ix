import Compilatrix.X86.PhysicalHeapObject
import Compilatrix.X86.PhysicalExportSourceApply

namespace Compilatrix.X86.PhysicalHeap

structure Exported (schemas : Schemas) (program : IxIR2.Program) (provenance : ELF.Provenance) where
  source : PhysicalScalar.ExportedFrom program program.main
  compiled : Compiled schemas program source.address true provenance
  same : compiled.selected.entryInterface.definition = source.target

def compileExport (schemas : Schemas) (program : IxIR2.Program) (provenance : ELF.Provenance)
    (name : String := "compilatrix_heap_cfg") : Except String (Exported schemas program provenance) := do
  let source ← PhysicalScalar.resolveExport program
  let compiled ← compile schemas program source.address true provenance name
  if same : compiled.selected.entryInterface.definition = source.target then return { source, compiled, same }
  else throw "heap CFG export differs from the selected function"

def compileSnapshotExport (artifact : IxIR2.Wire.Artifact) {limits : IxIR2.Validate.Limits}
    (_checked : IxIR2.Wire.Checked limits artifact) (name : String := "compilatrix_heap_cfg") :
    Except String (Exported artifact.context.schemas artifact.program (.ixir2 artifact.address)) :=
  compileExport artifact.context.schemas artifact.program (.ixir2 artifact.address) name

def compileSourceExport {constants root config world eraseFuel lowerFuel}
    (attached : IxIR2.Pipeline.Attached constants root config world eraseFuel lowerFuel)
    (name : String := "compilatrix_heap_cfg") :
    Except String (Exported attached.target.artifact.validationContext.schemas attached.target.artifact.program (sourceProvenance attached)) :=
  compileExport attached.target.artifact.validationContext.schemas attached.target.artifact.program (sourceProvenance attached) name

end Compilatrix.X86.PhysicalHeap
