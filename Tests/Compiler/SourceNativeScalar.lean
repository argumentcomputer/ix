import Ix.Compiler.X86.ScalarSources
import Ix.Compiler.X86.ScalarSourceObject
import Ix.Compiler.Coverage.Snapshot
import Ix.Compiler.Tools.Check

open Lean Ix.Compiler Ix.Compiler.X86 Ix.Compiler.Tools.Check

private def inputs : List (Nat × Nat) :=
  let m := UInt64.size - 1
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (3, 2), (7, 7), (7, 19), (19, 7),
    (0, m), (m, 0), (m, 1), (1, m), (m, m), (m - 1, 1), (m - 1, 2),
    (2, m - 1), (m, m - 1), (m - 1, m)]

private def expected (name : String) (a b : Nat) : Option Nat :=
  match name with
  | "sub" => some (a - b)
  | "nested" => if a == 0 then some 7 else if a > b then some (a - b)
      else if a + b < UInt64.size then some (a + b) else none
  | "add" => if a + b < UInt64.size then some (a + b) else none
  | _ => if a + b < UInt64.size then some (a + b - 1) else none

private def sourceNat : Nat → Ixon.Address → Ixon.Eval.Value → Option Nat
  | 0, _, _ => none
  | _ + 1, _, .litV (.natL number) => some number
  | fuel + 1, block, .ctorV found 0 1 [tail] =>
      if found == block then (sourceNat fuel block tail).map (· + 1) else none
  | _, _, _ => none

private def rawNat : Nat → Ixon.Address → IxIR0.Value → Option Nat
  | 0, _, _ => none
  | _ + 1, _, .lit (.nat number) => some number
  | fuel + 1, successor, .ctor found 1 [tail] =>
      if found == successor then (rawNat fuel successor tail).map (· + 1) else none
  | _, _, _ => none

private def core (depth a b : Nat) : Core :=
  let low : Word := 0x10000
  let top := low + (272 * depth - 8).toUInt64
  let allowed := fun address : Word => decide (low ≤ address ∧ address < top + 8)
  let memory : Memory := {
    bytes := fun address => (address ^^^ 0xa7).toUInt8
    readable := allowed, writable := allowed }
  let registers : Registers := fun register => 0x1020304050607080 + (SysV.calleeSaved.toList.idxOf register + 1).toUInt64
  { registers := ((registers.set .rsp top).set .rdi a.toUInt64).set .rsi b.toUInt64
    memory := memory.write64 top 0x12345678 }

private def nativeObservation {source : Coverage.Source} {attached : source.Attached}
    (compiled : Scalar.Source.Compiled attached.source) (a b : Nat) (wanted : Option Nat) : IO Json := do
  let initial := core (compiled.selected.scalar.program.entry + 1) a b
  let typed := X86.runFrom Runtime.rejecting compiled.native.target 1000 initial
  let value := (wanted.getD 0).toUInt64
  let tag : Word := if wanted.isSome then 0 else 1
  need (typed.status == .halted value && typed.core.readReg .rax == value && typed.core.readReg .rdx == tag)
    "typed native value/status disagrees with independent Nat arithmetic"
  need (typed.core.readReg .rsp == initial.readReg .rsp && typed.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "typed native stack/register restoration failed"
  let text ← present (ELFRead.text? compiled.object.bytes) "actual ELF text missing"
  let offset ← present (ELF.entry? compiled.object.bytes compiled.input.exportName) "actual ELF export missing"
  let base : Word := 0x400000
  let mut state : ByteEval.State := ⟨initial, base + offset.toUInt64, {}⟩
  let mut count := 0
  for _ in [:1000] do
    if state.rip == 0x12345678 then break
    state ← checked ((ByteEval.step text base state).mapError reprStr)
    count := count + 1
  need (state.rip == 0x12345678 && state.core.readReg .rax == value && state.core.readReg .rdx == tag)
    "actual object byte execution returned the wrong value/status/address"
  need (state.core.readReg .rsp == initial.readReg .rsp + 8 && state.core.calleeSavedMatch initial.calleeSavedSnapshot)
    "actual object byte execution changed stack/saved registers"
  for address in [(0xffff : Word), 0xfff8, initial.readReg .rsp + 8, initial.readReg .rsp + 16] do
    need (state.core.memory.bytes address == initial.memory.bytes address) "native execution changed an outside canary"
  let finalState ← checked ((ObjectEval.run compiled.object.bytes compiled.input.exportName base count initial).mapError reprStr)
  need (finalState.rip == state.rip && finalState.core.readReg .rax == value && finalState.core.readReg .rdx == tag)
    "complete ObjectEval entry/run disagrees"
  return Json.mkObj [("left", toJson a), ("right", toJson b), ("value", toJson value.toNat),
    ("status", toJson tag.toNat), ("byte_steps", toJson count), ("source_evaluated", toJson (a < 32 && b < 32))]

private def rejectSelection (declarations : List (Ixon.Address × IxIR0.Decl)) (root : Ixon.Address) : IO Unit := do
  match Scalar.Source.select declarations root with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed scalar source unexpectedly selected")

private def rejections {source : Coverage.Source} (attached : source.Attached)
    (compiled : Scalar.Source.Compiled attached.source) : IO Unit := do
  let declarations := attached.source.erasure.result.raw
  let replace := fun address replacement => declarations.map fun (found, declaration) =>
    (found, if found == address then replacement else declaration)
  let binary := fun body => IxIR0.Decl.defn .shared (.lam .many (.lam .many body))
  rejectSelection (replace source.root (binary .erased)) source.root
  rejectSelection (replace source.root (binary (.app (.app (.ref source.root) (.var 1)) (.var 0)))) source.root
  rejectSelection (replace source.root (binary (.ref (Ixon.Address.replicate 0x99)))) source.root
  rejectSelection (replace source.root (.defn .shared (.lam .many (.var 0)))) source.root
  rejectSelection (replace source.root (binary (IxIR0.NatArithmetic.sharedLiteral UInt64.size))) source.root
  rejectSelection (replace compiled.selected.primitives.arithmetic.successor (.ctor 0 1)) source.root
  rejectSelection (replace source.root (binary (.var 2))) source.root
  let initial := core (compiled.selected.scalar.program.entry + 1) 2 3
  let inaccessible := { initial with memory := { initial.memory with writable := fun _ => false } }
  match (X86.runFrom Runtime.rejecting compiled.native.target 1000 inaccessible).status with
  | .trapped (.memoryFault _) => pure ()
  | _ => throw (IO.userError "unwritable native stack did not trap in the model")
  if compiled.selected.scalar.program.entry > 0 then
    let floor := initial.readReg .rsp - 264
    let short := { initial with memory := { initial.memory with
      readable := fun address => decide (floor ≤ address ∧ address < initial.readReg .rsp + 8)
      writable := fun address => decide (floor ≤ address ∧ address < initial.readReg .rsp + 8) } }
    match (X86.runFrom Runtime.rejecting compiled.native.target 1000 short).status with
    | .trapped (.memoryFault _) => pure ()
    | _ => throw (IO.userError "insufficient nested-call stack did not trap in the model")

private def admissionChecks : IO Unit := do
  for program in [
    { functions := #[⟨3, .atom (.var 0)⟩], entry := 0 : Scalar.Program },
    { functions := #[⟨2, .atom (.var 2)⟩], entry := 0 },
    { functions := #[⟨2, .call 0 #[.var 0, .var 1]⟩], entry := 0 },
    { functions := Array.replicate 33 ⟨2, .atom (.var 0)⟩, entry := 0 },
    { functions := #[⟨2, (List.range 31).foldl (fun body _ => .letE (.atom (.constant 0)) body) (.atom (.var 0))⟩], entry := 0 }
  ] do
    need (Scalar.check program |>.isNone) "invalid scalar scope/arity/graph/capacity accepted"
  for values in [#[UInt64.size, 0], #[0, UInt64.size], #[UInt64.size * 2, 1]] do
    need ((Scalar.encodeArguments values).isNone) "oversized source Nat converted by wrapping"
  need (Scalar.encodeArguments #[UInt64.size - 1, 0] == some #[0xffffffffffffffff, 0]) "largest exact input rejected"

def main (args : List String) : IO UInt32 := cli "source-native-scalar" do
  let [directory] := args | throw (IO.userError "usage: source-native-scalar <new-output-directory>")
  let directory : System.FilePath := directory
  need (!(← directory.pathExists)) "source-native-scalar requires a fresh output directory"
  admissionChecks
  IO.FS.createDirAll directory
  let mut rows : Array Json := #[]
  for (name, program) in Scalar.Examples.families do
    let source ← checked (Scalar.Examples.source name program)
    let attached ← checked (source.compile.mapError reprStr)
    let compiled ← checked (Scalar.Source.compile attached.source "compilatrix_scalar")
    rejections attached compiled
    let ctx := Pipeline.validatedEvalCtx source.constants source.config
    let function ← checked ((Ixon.Eval.eval ctx 2000 (Pipeline.validatedMainFrame source.root) [] Pipeline.validatedMainSource).mapError reprStr)
    let rawCtx : IxIR0.Ctx := { env := IxIR0.Env.ofList attached.source.erasure.result.raw }
    let rawFunction ← checked ((IxIR0.eval rawCtx 2000 [] (.ref source.root)).mapError reprStr)
    let mut observations : Array Json := #[]
    for (a, b) in inputs do
      let wanted := expected name a b
      if a < 32 && b < 32 then
        let first ← checked ((Ixon.Eval.apply ctx 20000 function (.litV (.natL a))).mapError reprStr)
        let result ← checked ((Ixon.Eval.apply ctx 20000 first (.litV (.natL b))).mapError reprStr)
        let firstRaw ← checked ((IxIR0.apply rawCtx 20000 rawFunction (.lit (.nat a))).mapError reprStr)
        let resultRaw ← checked ((IxIR0.apply rawCtx 20000 firstRaw (.lit (.nat b))).mapError reprStr)
        let natBlock ← present source.natBlock "source Nat block missing"
        need (sourceNat 1000 natBlock result == wanted && rawNat 1000 compiled.selected.primitives.arithmetic.successor resultRaw == wanted)
          s!"{name}({a},{b}): Ixon/raw IxIR0 disagree with exact Nat arithmetic"
      observations := observations.push (← nativeObservation compiled a b wanted)
    let depth := compiled.selected.scalar.program.entry + 1
    let text := compiled.stream.output.text
    let row := Json.mkObj [("name", toJson name), ("source_root", toJson source.root),
      ("ir1_root", toJson compiled.input.provenance.root), ("functions", toJson compiled.selected.scalar.program.functions.size),
      ("blocks", toJson compiled.native.target.program.blocks.size), ("stack_depth", toJson depth),
      ("stack_bytes", toJson (272 * depth)), ("below_entry_bytes", toJson (272 * depth - 8)),
      ("text_bytes", toJson text.size), ("text_hash", toJson (Coverage.hex (Blake3.Rust.hash text).val)),
      ("object_bytes", toJson compiled.object.bytes.size),
      ("snapshot", toJson s!"{name}.json"), ("object", toJson s!"{name}.o")]
    let snapshot := Json.mkObj [("format", toJson "compilatrix/source-native-scalar/1"), ("policy", toJson Scalar.Source.policy),
      ("row", row), ("text", toJson (Coverage.hex text)), ("provenance", toJson (Coverage.hex compiled.input.provenance.bytes)),
      ("entry_offset", toJson (compiled.stream.output.blockOffsets[compiled.input.entryBlock.toNat]?.getD 0)),
      ("observations", toJson observations), ("source_compilation", source.compilationSnapshot attached)]
    IO.FS.writeBinFile (directory / s!"{name}.o") compiled.object.bytes
    IO.FS.writeFile (directory / s!"{name}.json") (snapshot.pretty 100 ++ "\n")
    rows := rows.push row
  let report := Json.mkObj [("format", toJson "compilatrix/source-native-scalar-report/1"), ("policy", toJson Scalar.Source.policy),
    ("runtime_arguments", toJson (2 : Nat)), ("source_evaluations", toJson (45 : Nat)),
    ("object_executions", toJson (95 : Nat)), ("source_rejections", toJson (35 : Nat)),
    ("admission_rejections", toJson (5 : Nat)), ("conversion_rejections", toJson (3 : Nat)),
    ("capacity_rejections", toJson (7 : Nat)), ("cases", toJson rows)]
  IO.FS.writeFile (directory / "report.json") (report.pretty 100 ++ "\n")
  IO.println "source-native-scalar ok: five source functions, 45 source evaluations, 95 runtime object executions, exact arithmetic and admission/capacity checks"
