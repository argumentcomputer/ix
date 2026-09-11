import Ix.Compiler.X86.PhysicalScalarSources
import Ix.Compiler.X86.PhysicalScalarCapturedSourceObject
import Ix.Compiler.X86.PhysicalScalarExamples
import Ix.Compiler.X86.ScalarNat
import Ix.Compiler.Coverage.Snapshot
import Ix.Compiler.Tools.Check

open Lean Ix.Compiler Ix.Compiler.X86 Ix.Compiler.Tools.Check
namespace CapturedGate
open PhysicalScalar.Captured

def families : List String := ["capture-project", "capture-choice", "capture-nested"]
def captures : List (String × Nat) := [("zero", 0), ("seven", 7), ("max", UInt64.size - 1)]

def inputs : List (Nat × Nat) :=
  let m := UInt64.size - 1
  [(0,0), (0,1), (1,0), (1,1), (2,3), (3,2), (7,7), (7,19), (19,7),
    (0,m), (m,0), (m,1), (1,m), (m,m), (m-1,1), (m-1,2), (2,m-1), (m,m-1), (m-1,m)]

def expected (name : String) (capture argument : Nat) : Nat := match name with
  | "capture-project" => capture
  | "capture-choice" => if argument == 0 then capture else argument - 1
  | _ => if argument ≤ 2 then capture else argument - 3

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
    "captured scalar typed native result disagrees"
  need (typed.core.readReg .rsp == initial.readReg .rsp && typed.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "captured scalar typed stack/register restoration failed"
  let base : Word := 0x400000
  let mut state : ByteEval.State := ⟨initial, base + entry.toUInt64, {}⟩
  let mut count := 0
  for _ in [:1000] do
    if state.rip == 0x12345678 then break
    state ← checked ((ByteEval.step text base state).mapError reprStr)
    count := count + 1
  need (state.rip == 0x12345678 && state.core.readReg .rax == wanted.toUInt64 && state.core.readReg .rdx == 0)
    "captured scalar byte result/status/return address disagrees"
  need (state.core.readReg .rsp == initial.readReg .rsp + 8 && state.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "captured scalar byte stack/register restoration failed"
  for address in [(0xffff : Word), 0xfff8, initial.readReg .rsp + 8, initial.readReg .rsp + 16] do
    need (state.core.memory.bytes address == initial.memory.bytes address) "captured scalar outside canary changed"
  return count

def observePhysical (program : IxIR2.Program) (definition : IxIR2.Function)
    (schemas : Ixon.Owned → IxIR2.CtorId → Option IxIR2.CtorSchema) (values : Array Word) (wanted : Nat)
    (initial : IxIR2.Eval.Store := {}) : IO (Nat × Nat) := do
  let ctx := IxIR2.Eval.Context.ofProgram program schemas
  let mut costs := (0, 0)
  for mode in [IxIR2.Eval.Interpretation.logical, .physical] do
    let result ← checked ((IxIR2.Eval.runFunction ctx mode definition (values.map PhysicalScalar.rval) 1000 1000 initial).mapError reprStr)
    need (result.value == .lit (.nat wanted)) "captured scalar CFG result disagrees"
    need (result.store.counters == initial.counters && result.store.live == 0 &&
      result.store.heap.nodes.size == initial.heap.nodes.size && result.store.heap.nodes.all Option.isNone)
      "captured scalar CFG changed the heap or allocation/reference counters"
    costs := (1000 - result.controlRemaining, 1000 - result.heapRemaining)
  return costs

def heapJSON (store : IxIR1.Store) : Json := Json.mkObj [
  ("allocs", toJson store.allocs), ("frees", toJson store.frees), ("rcops", toJson store.rcops),
  ("reuses", toJson store.reuses), ("slots", toJson store.nodes.size), ("live", toJson store.live)]

def sameHeap (left right : IxIR1.Store) : Bool :=
  heapJSON left == heapJSON right && (left.nodes.zip right.nodes).all fun (a, b) =>
    match a, b with
    | none, none => true
    | some a, some b => a.world == b.world && a.rc == b.rc && a.node == b.node
    | _, _ => false

def rejected {α : Type} (name : String) (result : Except String α) : IO Unit := do
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"captured scalar accepted {name}")

def initializerRejections {program schemas limits provenance}
    (compiled : Compiled program schemas limits provenance) : IO (Array String) := do
  let source := compiled.source
  let main := fun instructions terminator => PhysicalScalar.Examples.function 0
    #[PhysicalScalar.Examples.block 0 instructions terminator]
  let pap := IxIR2.Instr.papp source.address #[.lit (.nat source.capture.toNat)]
  let replace := fun definition => { program with declarations := program.declarations.map fun (address, old) =>
    (address, if address == source.address then .fn definition else old) }
  let malformed : List (String × IxIR2.Program) := [
    ("non-nullary", { program with main := { program.main with signature := { program.main.signature with
      params := #[⟨.shared, .owned⟩] } } }),
    ("empty-main", { program with main := { program.main with blocks := #[] } }),
    ("non-closure", { program with main := main #[] (.ret (.lit (.nat 0))) }),
    ("zero-captures", { program with main := main #[.papp source.address #[]] (.ret (.reg 0)) }),
    ("non-word-capture", { program with main := main #[.papp source.address #[.erased]] (.ret (.reg 0)) }),
    ("capture-overflow", { program with main := main #[.papp source.address #[.lit (.nat UInt64.size)]] (.ret (.reg 0)) }),
    ("extra-live-closure", { program with main := main #[pap, pap] (.ret (.reg 1)) }),
    ("shared-rc-two", { program with main := main #[pap, .retainShared (.reg 0)] (.ret (.reg 1)) }),
    ("missing-target", { program with declarations := program.declarations.filter (fun pair => pair.1 != source.address) }),
    ("unsafe-target", replace { source.target with signature := { source.target.signature with papSafe := false } }),
    ("target-arity", replace { source.target with signature := { source.target.signature with params := #[] } }),
    ("multiple-captures", { (replace { source.target with signature := { source.target.signature with
      params := Array.replicate 3 ⟨.shared, .owned⟩ } }) with
      main := main #[.papp source.address #[.lit (.nat 0), .lit (.nat 1)]] (.ret (.reg 0)) })]
  for (name, changed) in malformed do
    rejected name (checkInitializer changed schemas)
  for (name, limits) in [("control-limit", { control := 0 : Limits }), ("heap-limit", { heap := 0 : Limits }),
      ("slot-limit", { slots := 1 : Limits })] do
    rejected name (checkInitializer program schemas limits)
  return malformed.toArray.map (·.1) ++ #["control-limit", "heap-limit", "slot-limit"]

def stackRejections (target : X86.Checked) (depth : Nat) : IO Unit := do
  let initial := core depth 2 3
  let inaccessible := { initial with memory := { initial.memory with writable := fun _ => false } }
  let .trapped (.memoryFault _) := (X86.runFrom Runtime.rejecting target 1000 inaccessible).status
    | throw (IO.userError "captured scalar unwritable stack did not trap")
  let floor := initial.readReg .rsp - 264
  let short := { initial with memory := { initial.memory with
    readable := fun address => decide (floor ≤ address ∧ address < initial.readReg .rsp + 8)
    writable := fun address => decide (floor ≤ address ∧ address < initial.readReg .rsp + 8) } }
  let .trapped (.memoryFault _) := (X86.runFrom Runtime.rejecting target 1000 short).status
    | throw (IO.userError "captured scalar insufficient nested-call stack did not trap")

def admission : IO Unit := do
  for values in [#[UInt64.size], #[UInt64.size * 2]] do
    need ((Scalar.encodeArguments values).isNone) "captured scalar argument conversion wrapped"
  need (Scalar.encodeArguments #[UInt64.size - 1] == some #[0xffffffffffffffff]) "maximum exact argument rejected"
  let full ← present (Scalar.check { functions := Array.replicate 32 ⟨2, .atom (.var 0)⟩, entry := 31 })
    "32-function boundary fixture is invalid"
  rejected "33-function wrapper" (Scalar.bind full 7)
  let unary ← present (Scalar.check { functions := #[⟨1, .atom (.var 0)⟩], entry := 0 }) "unary fixture is invalid"
  rejected "unary underlying target" (Scalar.bind unary 7)
  let tooLarge ← checked (PhysicalScalar.Examples.source "capture-project" (some UInt64.size))
  let attached ← checked (tooLarge.compile.mapError reprStr)
  rejected "actual source capture overflow" (compileSource attached)

end CapturedGate

def main (args : List String) : IO UInt32 := cli "source-native-captured-scalar" do
  let [directory] := args | throw (IO.userError "usage: source-native-captured-scalar <new-output-directory>")
  let directory : System.FilePath := directory
  need (!(← directory.pathExists)) "captured scalar producer requires a fresh output directory"
  CapturedGate.admission
  IO.FS.createDirAll directory
  let mut rows : Array Json := #[]
  let mut rejected : Array String := #[]
  for family in CapturedGate.families do
    for (tag, capture) in CapturedGate.captures do
      let name := s!"{family}-{tag}"
      let source ← checked (PhysicalScalar.Examples.source family (some capture))
      let attached ← checked (source.compile.mapError reprStr)
      let compiled ← checked (PhysicalScalar.Captured.compileSource attached "compilatrix_scalar")
      need (compiled.source.capture.toNat == capture && compiled.source.target.signature.params.size == 2 &&
        compiled.bound.checked.program.functions[compiled.bound.checked.program.entry]?.map (·.parameters) == some 1)
        "captured scalar capture or ABI changed"
      let failures ← CapturedGate.initializerRejections compiled
      if rejected.isEmpty then rejected := failures else need (rejected == failures) "initializer rejection inventory differs"
      let depth := compiled.bound.checked.program.entry + 1
      CapturedGate.stackRejections compiled.native.target depth
      let program := attached.target.artifact.program
      let schemas := attached.target.artifact.validationContext.schemas
      let physicalContext := IxIR2.Eval.Context.ofProgram program schemas
      let initialized := compiled.source.result
      let location := compiled.source.heap.location
      need (location == 1 && initialized.store.heap.nodes.size == 2 && initialized.store.heap.allocs == 2 &&
        initialized.store.heap.frees == 1 && initialized.store.heap.rcops == 1 && initialized.store.heap.reuses == 0 &&
        initialized.store.live == 1 && initialized.store.peakLiveNodes == 1)
        "captured scalar initializer allocation/capture layout changed"
      let ir1Context := attached.compiled.simulationSourceContext
      let (moduleStore, moduleValue) ← checked ((IxIR1.runMain ir1Context attached.source.artifact.main 1000).mapError reprStr)
      need (moduleValue == initialized.value && CapturedGate.sameHeap moduleStore initialized.store.heap)
        "IxIR1 and physical captured initializer disagree"
      let spent := compiled.source.heap.spent
      need (spent.nodes.all Option.isNone && spent.allocs == 2 && spent.frees == 2 && spent.rcops == 2 && spent.reuses == 0)
        "captured scalar closure reclamation disagrees"
      let ctx := Pipeline.validatedEvalCtx source.constants source.config
      let function ← checked ((Ixon.Eval.eval ctx 2000 (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError reprStr)
      let rawCtx : IxIR0.Ctx := { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
      let rawFunction ← checked ((IxIR0.eval rawCtx 2000 [] (.ref source.root)).mapError reprStr)
      let .error (.stuck _) := Ixon.Eval.applyMany ctx 20000 function [.litV (.natL 2), .litV (.natL 3)]
        | throw (IO.userError "captured source overapplication accepted")
      let .error (.stuck _) := IxIR1.applyGo ir1Context 1000 moduleStore moduleValue [.lit (.nat 2), .lit (.nat 3)]
        | throw (IO.userError "captured IxIR1 overapplication accepted")
      for badArgs in [#[.lit (.nat 2)], #[.lit (.nat capture), .lit (.nat 2), .lit (.nat 3)]] do
        let .error (.stuck message) := IxIR2.Eval.runFunction physicalContext .physical compiled.source.target badArgs 1000 1000
          | throw (IO.userError "captured physical invocation accepted wrong arity")
        need (message == "function argument arity mismatch") "captured physical invocation rejected for the wrong reason"
      let text ← present (ELFRead.text? compiled.object.bytes) "captured scalar ELF text missing"
      let offset ← present (ELF.entry? compiled.object.bytes compiled.input.exportName) "captured scalar ELF export missing"
      let mut observations : Array Json := #[]
      for (a, b) in CapturedGate.inputs do
        let wanted := CapturedGate.expected family capture a
        let values : Array Word := #[a.toUInt64]
        let result ← checked ((Ixon.Eval.applyMany ctx 20000 function (PhysicalScalar.sourceArguments values)).mapError reprStr)
        need (match result with | .litV (.natL n) => n == wanted | _ => false) s!"{name}({a}): source Nat result disagrees"
        let resultRaw ← checked ((IxIR0.apply rawCtx 20000 rawFunction (.lit (.nat a))).mapError reprStr)
        need (match resultRaw with | .lit (.nat n) => n == wanted | _ => false) "captured scalar raw IxIR0 result disagrees"
        let (ir1Store, ir1Value) ← checked ((IxIR1.applyGo ir1Context 1000 moduleStore moduleValue
          [.lit (.nat a)]).mapError reprStr)
        need (ir1Value == .lit (.nat wanted) && CapturedGate.sameHeap ir1Store spent)
          "captured scalar IxIR1 application disagrees or leaked"
        let fullValues : Array Word := #[capture.toUInt64, a.toUInt64]
        let (invokedStore, invokedValue) ← checked ((IxIR1.invoke ir1Context 1000 compiled.source.address
          (fullValues.map PhysicalScalar.rval).toList spent).mapError reprStr)
        need (invokedValue == ir1Value && CapturedGate.sameHeap invokedStore spent)
          "captured scalar addressed invocation changed capture order or heap"
        let (controlCost, heapCost) ← CapturedGate.observePhysical program compiled.source.target schemas fullValues wanted { heap := spent }
        let initial := CapturedGate.core depth a b
        let count ← CapturedGate.native compiled.native.target text offset initial wanted
        let finalState ← checked ((ObjectEval.run compiled.object.bytes compiled.input.exportName 0x400000 count initial).mapError reprStr)
        need (finalState.rip == 0x12345678 && finalState.core.readReg .rax == wanted.toUInt64 && finalState.core.readReg .rdx == 0)
          "captured scalar complete ObjectEval disagrees"
        observations := observations.push (Json.mkObj [("argument", toJson a), ("unused_rsi", toJson b), ("value", toJson wanted),
          ("status", toJson (0 : Nat)), ("byte_steps", toJson count), ("physical_control", toJson controlCost),
          ("physical_heap_fuel", toJson heapCost), ("source_evaluated", toJson true),
          ("source_arguments", toJson (values.map UInt64.toNat)), ("physical_arguments", toJson (fullValues.map UInt64.toNat)),
          ("application_heap", CapturedGate.heapJSON ir1Store)])
      let physicalBlocks := compiled.selected.entries.foldl (fun total entry => total + entry.2.blocks.size) 0
      let row := Json.mkObj [("name", toJson name), ("family", toJson family), ("capture", toJson capture),
        ("source_root", toJson source.root), ("ir1_root", toJson compiled.input.provenance.root),
        ("physical_entry", toJson compiled.source.address), ("runtime_parameters", toJson (1 : Nat)),
        ("physical_parameters", toJson (2 : Nat)), ("selected_functions", toJson compiled.selected.scalar.program.functions.size),
        ("functions", toJson compiled.bound.checked.program.functions.size), ("physical_blocks", toJson physicalBlocks),
        ("native_blocks", toJson compiled.native.target.program.blocks.size), ("stack_depth", toJson depth),
        ("stack_bytes", toJson (272 * depth)), ("below_entry_bytes", toJson (272 * depth - 8)),
        ("text_bytes", toJson text.size), ("text_hash", toJson (Coverage.hex (Blake3.Rust.hash text).val)),
        ("object_bytes", toJson compiled.object.bytes.size), ("snapshot", toJson s!"{name}.json"), ("object", toJson s!"{name}.o")]
      let snapshot := Json.mkObj [("format", toJson "compilatrix/source-native-captured-scalar/1"),
        ("policy", toJson PhysicalScalar.Captured.policy), ("row", row), ("text", toJson (Coverage.hex text)),
        ("provenance", toJson (Coverage.hex compiled.input.provenance.bytes)), ("entry_offset", toJson offset),
        ("selected_entries", toJson (compiled.selected.entries.map (·.1))),
        ("initializer", Json.mkObj [("location", toJson location), ("capture", toJson capture),
          ("heap", CapturedGate.heapJSON initialized.store.heap), ("peak_live", toJson initialized.store.peakLiveNodes),
          ("control_steps", toJson (4096 - initialized.controlRemaining)), ("heap_fuel", toJson (16384 - initialized.heapRemaining))]),
        ("observations", toJson observations), ("source_compilation", source.compilationSnapshot attached)]
      IO.FS.writeBinFile (directory / s!"{name}.o") compiled.object.bytes
      IO.FS.writeFile (directory / s!"{name}.json") (snapshot.pretty 100 ++ "\n")
      rows := rows.push row
  let runs := rows.size * CapturedGate.inputs.length
  let report := Json.mkObj [("format", toJson "compilatrix/source-native-captured-scalar-report/1"),
    ("policy", toJson PhysicalScalar.Captured.policy), ("runtime_parameters", toJson (1 : Nat)),
    ("source_evaluations", toJson runs), ("object_executions", toJson runs),
    ("initializer_rejections", toJson rejected), ("initializer_rejection_runs", toJson (rejected.size * rows.size)),
    ("application_boundary_checks", toJson (4 * rows.size)), ("wrapper_rejections", toJson (2 : Nat)),
    ("conversion_rejections", toJson (3 : Nat)), ("capacity_rejections", toJson (2 * rows.size)), ("cases", toJson rows)]
  IO.FS.writeFile (directory / "report.json") (report.pretty 100 ++ "\n")
  IO.println "source-native-captured-scalar ok: nine captured source exports, 171 source/application/object runs, initializer/wrapper/conversion/capacity checks"
