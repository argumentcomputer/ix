import Compilatrix.X86.PhysicalScalarSources
import Compilatrix.X86.PhysicalScalarExamples
import Compilatrix.X86.ScalarNat
import Compilatrix.Coverage.Snapshot
import Compilatrix.Tools.Check

open Lean Compilatrix Compilatrix.X86 Compilatrix.Tools.Check
namespace PhysicalGate

def inputs : List (Nat × Nat) :=
  let m := UInt64.size - 1
  [(0,0), (0,1), (1,0), (1,1), (2,3), (3,2), (7,7), (7,19), (19,7),
    (0,m), (m,0), (m,1), (1,m), (m,m), (m-1,1), (m-1,2), (2,m-1), (m,m-1), (m-1,m)]

def expected (name : String) (a b : Nat) : Nat := match name with
  | "project" | "swap" => a
  | "tag" => if a == 0 then 11 else 22
  | "pred" => a - 1
  | "choose" | "diamond" => if a == 0 then b else a - 1
  | "helpers" => if a ≤ 1 then 11 else 22
  | "nested" => if a ≤ 2 then b else a - 3
  | "permuted" => if a == 0 then b else a
  | "constant" => UInt64.size - 1
  | _ => 0

def core (depth a b : Nat) : Core :=
  let low : Word := 0x10000
  let top := low + (272 * depth - 8).toUInt64
  let allowed := fun address : Word => decide (low ≤ address ∧ address < top + 8)
  let memory : Memory := { bytes := fun address => (address ^^^ 0xa7).toUInt8, readable := allowed, writable := allowed }
  let registers : Registers := fun register => 0x1020304050607080 + (SysV.calleeSaved.toList.idxOf register + 1).toUInt64
  { registers := ((registers.set .rsp top).set .rdi a.toUInt64).set .rsi b.toUInt64
    memory := memory.write64 top 0x12345678 }

def native (target : X86.Checked) (text : ByteArray) (entry : Nat) (initial : Core) (wanted : Nat) : IO Nat := do
  let typed := X86.runFrom Runtime.rejecting target 1000 initial
  need (typed.status == .halted wanted.toUInt64 && typed.core.readReg .rax == wanted.toUInt64 && typed.core.readReg .rdx == 0)
    "physical scalar typed native result disagrees"
  need (typed.core.readReg .rsp == initial.readReg .rsp && typed.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "physical scalar typed stack/register restoration failed"
  let base : Word := 0x400000
  let mut state : ByteEval.State := ⟨initial, base + entry.toUInt64, {}⟩
  let mut count := 0
  for _ in [:1000] do
    if state.rip == 0x12345678 then break
    state ← checked ((ByteEval.step text base state).mapError reprStr)
    count := count + 1
  need (state.rip == 0x12345678 && state.core.readReg .rax == wanted.toUInt64 && state.core.readReg .rdx == 0)
    "physical scalar byte result/status/return address disagrees"
  need (state.core.readReg .rsp == initial.readReg .rsp + 8 && state.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "physical scalar byte stack/register restoration failed"
  for address in [(0xffff : Word), 0xfff8, initial.readReg .rsp + 8, initial.readReg .rsp + 16] do
    need (state.core.memory.bytes address == initial.memory.bytes address) "physical scalar outside canary changed"
  return count

def observePhysical (program : IxIR2.Program) (definition : IxIR2.Function)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema) (a b wanted : Nat) : IO (Nat × Nat) := do
  let ctx := IxIR2.Eval.Context.ofProgram program schemas
  let mut costs := (0, 0)
  for mode in [IxIR2.Eval.Interpretation.logical, .physical] do
    let result ← checked ((IxIR2.Eval.runFunction ctx mode definition #[.lit (.nat a), .lit (.nat b)] 1000 1000).mapError reprStr)
    need (result.value == .lit (.nat wanted)) "physical scalar CFG result disagrees"
    need (result.store.counters == ({} : IxIR2.Eval.Counters) && result.store.live == 0)
      "physical scalar CFG changed the heap or allocation/reference counters"
    costs := (1000 - result.controlRemaining, 1000 - result.heapRemaining)
  return costs

def admission : IO (Array String) := do
  let mut rejected := #[]
  for (name, program) in PhysicalScalar.Examples.rejections do
    match PhysicalScalar.select program PhysicalScalar.Examples.root with
    | .ok _ => throw (IO.userError s!"physical scalar accepted invalid CFG: {name}")
    | .error error =>
      if name == "expansion-budget" then need (error.contains "work limit") "CFG expansion was not bounded before native emission"
      rejected := rejected.push name
  for values in [#[UInt64.size, 0], #[0, UInt64.size], #[UInt64.size * 2, 1]] do
    need ((Scalar.encodeArguments values).isNone) "physical scalar argument conversion silently wrapped"
  need (Scalar.encodeArguments #[UInt64.size - 1, 0] == some #[0xffffffffffffffff, 0]) "physical scalar maximum input rejected"
  return rejected

def rawCFGs : IO (Array Json) := do
  let mut rows := #[]
  for (name, program) in PhysicalScalar.Examples.cfgs do
    let selected ← checked (PhysicalScalar.select program PhysicalScalar.Examples.root)
    let nativeCode ← checked (Scalar.compile selected.scalar)
    let stream ← checked ((Stream.encode nativeCode.target).mapError reprStr)
    let (_, definition) ← present selected.entries[selected.scalar.program.entry]? "raw CFG entry is missing"
    let depth := selected.scalar.program.entry + 1
    for (a, b) in inputs do
      let wanted := expected name a b
      let _ ← observePhysical program definition (fun _ _ => none) a b wanted
      let _ ← native nativeCode.target stream.output.text
        (stream.output.blockOffsets[nativeCode.target.program.entry.toNat]?.getD 0) (core depth a b) wanted
    rows := rows.push (Json.mkObj [("name", toJson name), ("physical_blocks", toJson definition.blocks.size),
      ("functions", toJson selected.scalar.program.functions.size), ("inputs", toJson inputs.length)])
  return rows

def exportRejections {program provenance} (exported : PhysicalScalar.Exported program provenance) : IO Unit := do
  let replace := fun definition => { program with declarations := program.declarations.map fun (address, old) =>
    (address, if address == exported.source.address then .fn definition else old) }
  let captured := { program with main := PhysicalScalar.Examples.function 0 #[PhysicalScalar.Examples.block 0
    #[.papp exported.source.address #[.lit (.nat 0)]] (.ret (.reg 0))] }
  let missing := { program with main := PhysicalScalar.Examples.function 0 #[PhysicalScalar.papBlock (Ixon.Address.replicate 0xee)] }
  let saturated := replace { exported.source.target with signature := { exported.source.target.signature with params := #[] } }
  let unsafeTarget := replace { exported.source.target with signature := { exported.source.target.signature with papSafe := false } }
  let cyclic := { program with
    main := PhysicalScalar.Examples.function 0 #[PhysicalScalar.tailBlock exported.source.address]
    declarations := [(exported.source.address, .fn (PhysicalScalar.Examples.function 0 #[PhysicalScalar.tailBlock exported.source.address]))] }
  for changed in [captured, missing, saturated, unsafeTarget, cyclic] do
    match PhysicalScalar.resolveExport changed with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "physical scalar accepted invalid module export")

def stackRejections {program root provenance} (compiled : PhysicalScalar.Compiled program root provenance) : IO Nat := do
  let depth := compiled.selected.scalar.program.entry + 1
  let initial := core depth 2 3
  let inaccessible := { initial with memory := { initial.memory with writable := fun _ => false } }
  match (X86.runFrom Runtime.rejecting compiled.native.target 1000 inaccessible).status with
  | .trapped (.memoryFault _) => pure ()
  | _ => throw (IO.userError "physical scalar unwritable stack did not trap")
  if depth > 1 then
    let floor := initial.readReg .rsp - 264
    let short := { initial with memory := { initial.memory with
      readable := fun address => decide (floor ≤ address ∧ address < initial.readReg .rsp + 8)
      writable := fun address => decide (floor ≤ address ∧ address < initial.readReg .rsp + 8) } }
    match (X86.runFrom Runtime.rejecting compiled.native.target 1000 short).status with
    | .trapped (.memoryFault _) => return 2
    | _ => throw (IO.userError "physical scalar insufficient call stack did not trap")
  return 1

end PhysicalGate

def main (args : List String) : IO UInt32 := cli "source-native-physical-scalar" do
  let [directory] := args | throw (IO.userError "usage: source-native-physical-scalar <new-output-directory>")
  let directory : System.FilePath := directory
  need (!(← directory.pathExists)) "physical scalar producer requires a fresh output directory"
  let rejected ← PhysicalGate.admission
  let cfgs ← PhysicalGate.rawCFGs
  IO.FS.createDirAll directory
  let mut rows : Array Json := #[]
  let mut stackRejections := 0
  for name in ["project", "tag", "pred", "choose", "helpers", "nested"] do
    let source ← checked (PhysicalScalar.Examples.source name)
    let attached ← checked (source.compile.mapError reprStr)
    let exported ← checked (PhysicalScalar.compileSourceExport attached "compilatrix_scalar")
    let compiled := exported.compiled
    PhysicalGate.exportRejections exported
    stackRejections := stackRejections + (← PhysicalGate.stackRejections compiled)
    let program := attached.target.artifact.program
    let schemas := attached.target.artifact.validationContext.schemas
    let physicalContext := IxIR2.Eval.Context.ofProgram program schemas
    let mainResult ← checked ((IxIR2.Eval.runMain physicalContext .physical program 100 100).mapError reprStr)
    let .loc location := mainResult.value | throw (IO.userError "physical module main did not return a closure")
    let some box := mainResult.store.get? location | throw (IO.userError "physical module closure is missing")
    need (box.node == .papN exported.source.address 2 #[] && box.world == .shared && box.rc == 1)
      "physical module export differs from the selected uncaptured binary function"
    let ctx := Pipeline.validatedEvalCtx source.constants source.config
    let function ← checked ((Ixon.Eval.eval ctx 2000 (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError reprStr)
    let rawCtx : IxIR0.Ctx := { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
    let rawFunction ← checked ((IxIR0.eval rawCtx 2000 [] (.ref source.root)).mapError reprStr)
    let depth := compiled.selected.scalar.program.entry + 1
    let text ← present (ELFRead.text? compiled.object.bytes) "physical scalar actual ELF text missing"
    let offset ← present (ELF.entry? compiled.object.bytes compiled.input.exportName) "physical scalar actual ELF export missing"
    let mut observations : Array Json := #[]
    for (a, b) in PhysicalGate.inputs do
      let wanted := PhysicalGate.expected name a b
      let first ← checked ((Ixon.Eval.apply ctx 20000 function (.litV (.natL a))).mapError reprStr)
      let result ← checked ((Ixon.Eval.apply ctx 20000 first (.litV (.natL b))).mapError reprStr)
      need (match result with | .litV (.natL n) => n == wanted | _ => false) s!"{name}({a},{b}): source Nat result disagrees"
      let firstRaw ← checked ((IxIR0.apply rawCtx 20000 rawFunction (.lit (.nat a))).mapError reprStr)
      let resultRaw ← checked ((IxIR0.apply rawCtx 20000 firstRaw (.lit (.nat b))).mapError reprStr)
      need (match resultRaw with | .lit (.nat n) => n == wanted | _ => false) "physical scalar raw IxIR0 result disagrees"
      let (ir1Store, ir1Value) ← checked ((IxIR1.invoke { decls := attached.source.artifact.targetDeclEnv }
        1000 exported.source.address [.lit (.nat a), .lit (.nat b)] {}).mapError reprStr)
      need (ir1Value == .lit (.nat wanted) && ir1Store.allocs == 0 && ir1Store.frees == 0 && ir1Store.rcops == 0 && ir1Store.live == 0)
        "physical scalar addressed IxIR1 result or heap disagrees"
      let (controlCost, heapCost) ← PhysicalGate.observePhysical program compiled.definition schemas a b wanted
      let initial := PhysicalGate.core depth a b
      let count ← PhysicalGate.native compiled.native.target text offset initial wanted
      let finalState ← checked ((ObjectEval.run compiled.object.bytes compiled.input.exportName 0x400000 count initial).mapError reprStr)
      need (finalState.rip == 0x12345678 && finalState.core.readReg .rax == wanted.toUInt64 && finalState.core.readReg .rdx == 0)
        "physical scalar complete ObjectEval result disagrees"
      observations := observations.push (Json.mkObj [("left", toJson a), ("right", toJson b), ("value", toJson wanted),
        ("status", toJson (0 : Nat)), ("byte_steps", toJson count), ("physical_control", toJson controlCost),
        ("physical_heap_fuel", toJson heapCost), ("source_evaluated", toJson true)])
    let physicalBlocks := compiled.selected.entries.foldl (fun total entry => total + entry.2.blocks.size) 0
    let row := Json.mkObj [("name", toJson name), ("source_root", toJson source.root),
      ("ir1_root", toJson compiled.input.provenance.root), ("physical_entry", toJson exported.source.address),
      ("functions", toJson compiled.selected.scalar.program.functions.size), ("physical_blocks", toJson physicalBlocks),
      ("native_blocks", toJson compiled.native.target.program.blocks.size), ("stack_depth", toJson depth),
      ("stack_bytes", toJson (272 * depth)), ("below_entry_bytes", toJson (272 * depth - 8)),
      ("text_bytes", toJson text.size), ("text_hash", toJson (Coverage.hex (Blake3.Rust.hash text).val)),
      ("object_bytes", toJson compiled.object.bytes.size), ("snapshot", toJson s!"{name}.json"), ("object", toJson s!"{name}.o")]
    let snapshot := Json.mkObj [("format", toJson "compilatrix/source-native-physical-scalar/1"), ("policy", toJson PhysicalScalar.policy),
      ("row", row), ("text", toJson (Coverage.hex text)), ("provenance", toJson (Coverage.hex compiled.input.provenance.bytes)),
      ("entry_offset", toJson offset), ("selected_entries", toJson (compiled.selected.entries.map (·.1))),
      ("observations", toJson observations), ("source_compilation", source.compilationSnapshot attached)]
    IO.FS.writeBinFile (directory / s!"{name}.o") compiled.object.bytes
    IO.FS.writeFile (directory / s!"{name}.json") (snapshot.pretty 100 ++ "\n")
    rows := rows.push row
  let report := Json.mkObj [("format", toJson "compilatrix/source-native-physical-scalar-report/1"), ("policy", toJson PhysicalScalar.policy),
    ("runtime_arguments", toJson (2 : Nat)), ("source_evaluations", toJson (114 : Nat)), ("object_executions", toJson (114 : Nat)),
    ("cfg_stream_executions", toJson (76 : Nat)), ("cfg_cases", toJson cfgs), ("admission_rejections", toJson rejected),
    ("export_rejections", toJson (30 : Nat)), ("conversion_rejections", toJson (3 : Nat)),
    ("capacity_rejections", toJson stackRejections), ("cases", toJson rows)]
  IO.FS.writeFile (directory / "report.json") (report.pretty 100 ++ "\n")
  IO.println "source-native-physical-scalar ok: six source exports, 114 source/IR/object runs, 76 CFG stream runs, admission/export/capacity checks"
