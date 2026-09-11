import Ix.Compiler.Tools.UniqueCheck
import Ix.Compiler.Tools.X86Check

/-! Independent inspection of the residual expression, its complete machine
text, source/physical observations, and native ABI results. No compiler,
selector, encoder, ELF writer, or machine evaluator is imported. -/
namespace Ix.Compiler.Tools.UpstreamNativeCheck
open Lean System Check UniqueCheck X86Check

def little (count value : Nat) : ByteArray :=
  ByteArray.mk ((List.range count).toArray.map fun index => (value / 2^(8 * index) % 256).toUInt8)

def expressionLength : Nat → Json → IO Nat
  | 0, _ => throw (IO.userError "residual expression exceeds checker budget")
  | fuel + 1, expression => do
    match ← strField expression "op" with
    | "argument" => return 3
    | "constant" =>
        need ((← number expression "value") < UInt64.size) "residual constant exceeds Word"
        return 10
    | "successor" => return (← expressionLength fuel (← field expression "value")) + 7
    | "call" => return (← expressionLength fuel (← field expression "value")) + 10
    | _ => throw (IO.userError "unknown residual operation")

def expressionBytes (offsets : Array Nat) (current : Nat) : Nat → Json → Nat → IO ByteArray
  | 0, _, _ => throw (IO.userError "residual expression exceeds checker budget")
  | fuel + 1, expression, position => do
    match ← strField expression "op" with
    | "argument" => return ← checked (unhex "48 89 f8")
    | "constant" =>
        let value ← number expression "value"
        need (value < UInt64.size) "residual constant exceeds Word"
        return (← checked (unhex "48 b8")) ++ little 8 value
    | "successor" => return (← expressionBytes offsets current fuel (← field expression "value") position) ++
        (← checked (unhex "48 81 c0 01 00 00 00"))
    | "call" =>
        let callee ← number expression "function"
        need (callee < current && callee < offsets.size) "residual call is recursive or out of range"
        let headBytes ← expressionBytes offsets current fuel (← field expression "value") position
        let delta : Int := (offsets[callee]! : Int) - (position + headBytes.size + 9 : Nat)
        need (-(2^31 : Int) ≤ delta && delta < 2^31) "residual call displacement out of range"
        return headBytes ++ (← checked (unhex "48 89 c7 55 e8")) ++ little 4 (delta % (2^32)).toNat ++ (← checked (unhex "5d"))
    | _ => throw (IO.userError "unknown residual operation")

def expressionValue (functions : Array Json) : Nat → Json → Nat → IO Nat
  | 0, _, _ => throw (IO.userError "residual evaluation exceeds checker budget")
  | fuel + 1, expression, argument => do
    let result ← match ← strField expression "op" with
      | "argument" => pure argument
      | "constant" => number expression "value"
      | "successor" => return (← expressionValue functions fuel (← field expression "value") argument) + 1
      | "call" => do
          let target ← number expression "function"
          need (target < functions.size) "residual evaluation call out of range"
          expressionValue functions fuel (← field functions[target]! "body")
            (← expressionValue functions fuel (← field expression "value") argument)
      | _ => throw (IO.userError "unknown residual operation")
    need (result < UInt64.size) "residual arithmetic overflows Word"
    return result

/-- Executed instruction/call counts and maximum simultaneous call depth.
Successors can run more than once, so these cannot be inferred from the result. -/
def expressionCost (functions : Array Json) : Nat → Json → IO (Nat × Nat × Nat)
  | 0, _ => throw (IO.userError "residual cost exceeds checker budget")
  | fuel + 1, expression => do
    match ← strField expression "op" with
    | "argument" | "constant" => return (1, 0, 0)
    | "successor" =>
        let (steps, calls, depth) ← expressionCost functions fuel (← field expression "value")
        return (steps + 1, calls, depth)
    | "call" =>
        let target ← number expression "function"
        need (target < functions.size) "residual cost call out of range"
        let (inputSteps, inputCalls, inputDepth) ← expressionCost functions fuel (← field expression "value")
        let (bodySteps, bodyCalls, bodyDepth) ← expressionCost functions fuel (← field functions[target]! "body")
        return (inputSteps + 4 + bodySteps + 1, inputCalls + 1 + bodyCalls, max inputDepth (bodyDepth + 1))
    | _ => throw (IO.userError "unknown residual operation")

def policyProvenance (root : String) (version : Nat := 4) : IO ByteArray := do
  return "compilatrix/x86-object-provenance/1".toUTF8 ++
    (← checked (unhex ("00 00 " ++ root))) ++ little 4 version ++ little 4 1

def readLE (bytes : ByteArray) (offset count : Nat) : IO Nat := do
  need (offset + count ≤ bytes.size) "upstream ELF field out of bounds"
  return (List.range count).foldl (fun value index => value + bytes[offset + index]!.toNat * 2^(8 * index)) 0

def slice (bytes : ByteArray) (offset size : Nat) : IO ByteArray := do
  need (offset + size ≤ bytes.size) "upstream ELF section out of bounds"
  return bytes.extract offset (offset + size)

def inspectELFBytes (bytes text : ByteArray) (entry : Nat) (root : String) (version : Nat := 4) : IO Unit := do
  need (bytes.size ≥ 64 && bytes.extract 0 7 == (← checked (unhex "7f 45 4c 46 02 01 01"))) "upstream ELF header disagrees"
  need ((← readLE bytes 16 2) == 1 && (← readLE bytes 18 2) == 62 && (← readLE bytes 20 4) == 1 &&
    (← readLE bytes 24 8) == 0 && (← readLE bytes 32 8) == 0 && (← readLE bytes 52 2) == 64 &&
    (← readLE bytes 56 2) == 0 && (← readLE bytes 58 2) == 64 && (← readLE bytes 60 2) == 8 &&
    (← readLE bytes 62 2) == 7) "upstream ELF structural header disagrees"
  let table ← readLE bytes 40 8
  need (table + 8 * 64 == bytes.size) "upstream ELF section table bounds disagree"
  let sectionOffset := fun index => table + 64 * index
  let payload (index : Nat) : IO ByteArray := do
    slice bytes (← readLE bytes (sectionOffset index + 24) 8) (← readLE bytes (sectionOffset index + 32) 8)
  let names ← payload 7
  let stringAt := fun (strings : ByteArray) offset => do
    need (offset < strings.size) "upstream ELF string out of bounds"
    let tail := strings.extract offset strings.size
    let length := tail.data.toList.takeWhile (· != 0) |>.length
    need (length < tail.size) "upstream ELF string is unterminated"
    present (String.fromUTF8? (tail.extract 0 length)) "upstream ELF string is not UTF-8"
  for (index, name) in [(1, ".text"), (2, ".rela.text"), (3, ".note.compilatrix"), (4, ".symtab"),
      (5, ".strtab"), (6, ".note.GNU-stack"), (7, ".shstrtab")] do
    need ((← stringAt names (← readLE bytes (sectionOffset index) 4)) == name) "upstream ELF section name disagrees"
  need ((← payload 1) == text && (← readLE bytes (sectionOffset 1 + 4) 4) == 1 &&
    (← readLE bytes (sectionOffset 1 + 8) 8) == 6) "upstream ELF executable text disagrees"
  need ((← payload 2).isEmpty && (← payload 6).isEmpty && (← readLE bytes (sectionOffset 6 + 8) 8) == 0)
    "upstream ELF relocations or stack policy disagree"
  let symbols ← payload 4
  let strings ← payload 5
  need (symbols.size == 72 && (← readLE bytes (sectionOffset 4 + 56) 8) == 24 &&
    (← readLE bytes (sectionOffset 4 + 40) 4) == 5) "upstream ELF symbol table disagrees"
  need ((← stringAt strings (← readLE symbols 48 4)) == "compilatrix_main" &&
    (← readLE symbols 52 1) == 18 && (← readLE symbols 53 1) == 0 && (← readLE symbols 54 2) == 1 &&
    (← readLE symbols 56 8) == entry && (← readLE symbols 64 8) == text.size - entry)
    "upstream ELF exported entry disagrees"
  let note ← payload 3
  need (containsBytes note (← policyProvenance root version)) "upstream ELF provenance disagrees"

private def register (index : Nat) : Json :=
  Json.mkObj [("reg", Json.mkObj [("id", toJson index)])]

private def operation (name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj [(name, Json.mkObj fields)]

private def physicalBlock (program : Json) (origin : String) (arity : Nat) : IO Json := do
  let declarations ← arrField program "declarations"
  let matching ← declarations.filterM fun declaration => do return (← array declaration)[0]? == some (toJson origin)
  need (matching.size == 1) "capture transport declaration identity disagrees"
  let declaration ← array matching[0]!
  let definition ← field (← field declaration[1]! "fn") "definition"
  let signature ← field definition "signature"
  let owned := Json.mkObj [("world", toJson "shared"), ("passing", toJson "owned")]
  need ((← field signature "params") == toJson (Array.replicate arity owned) &&
      (← strField signature "result") == "shared" && (← field signature "papSafe") == toJson true)
    "capture transport physical signature disagrees"
  let blocks ← arrField definition "blocks"
  need (blocks.size == 1 && (← arrField blocks[0]! "creditParams").isEmpty &&
      (← field blocks[0]! "valueParams") == toJson (Array.replicate arity
        (operation "owned" [("world", toJson "shared")]))) "capture transport physical block disagrees"
  return blocks[0]!

/-- Independently tie this upstream fixture's residual capture to the actual
physical initializer, PAP target, application order, and returned parameter.
The selector accepts a wider fragment; this oracle checks the reviewed fixture. -/
def inspectCapture (snapshot : Json) (functions : Array Json) : IO Unit := do
  let native ← field snapshot "native"
  let schema ← field native "schema"
  let program ← field (← field (← field snapshot "compilation") "ixir2_diagnostic") "program"
  let capturedOrigin ← strField functions[0]! "origin"
  let twiceOrigin ← strField functions[1]! "origin"
  let initializerOrigin ← strField functions[2]! "origin"
  let captured ← physicalBlock program capturedOrigin 2
  let twice ← physicalBlock program twiceOrigin 2
  let initializer ← physicalBlock program initializerOrigin 0
  let call := fun function args => operation "tailCall" [("function", toJson function), ("args", toJson args)]
  let ret := fun index => operation "ret" [("value", register index)]
  need ((← field captured "instructions") == toJson #[operation "releaseShared" [("target", register 1)]] &&
      (← field captured "terminator") == ret 0) "capture transport physical parameter order disagrees"
  let apply := fun closure argument => operation "apply" [("function", register closure), ("args", toJson #[register argument])]
  need ((← field twice "instructions") == toJson #[operation "retainShared" [("target", register 0)], apply 0 1, apply 2 3] &&
      (← field twice "terminator") == ret 4) "capture transport physical applications disagree"
  let alloc := fun cid args => operation "alloc" [("world", toJson "shared"), ("cid", cid), ("args", toJson args)]
  need ((← field initializer "instructions") == toJson #[
      alloc (← field schema "zero") (#[] : Array Json),
      alloc (← field schema "succ") #[register 0], alloc (← field schema "succ") #[register 1],
      operation "papp" [("function", toJson capturedOrigin), ("args", toJson #[register 2])],
      alloc (← field schema "zero") (#[] : Array Json)] &&
      (← field initializer "terminator") == call twiceOrigin #[register 3, register 4])
    "capture transport physical initializer disagrees"
  let main ← field program "main"
  let mainBlocks ← arrField main "blocks"
  need (mainBlocks.size == 1 && (← arrField mainBlocks[0]! "instructions").isEmpty &&
      (← field mainBlocks[0]! "terminator") == call initializerOrigin (#[] : Array Json))
    "capture transport physical main disagrees"
  let zero := Json.mkObj [("op", toJson "constant"), ("value", toJson (0 : Nat))]
  let successor := fun value => Json.mkObj [("op", toJson "successor"), ("value", value)]
  let capture := successor (successor zero)
  let natParam := Json.mkObj [("kind", toJson "nat")]
  let staticParam := Json.mkObj [("kind", toJson "static-nat"), ("value", capture)]
  let closureParam := Json.mkObj [("kind", toJson "known-static-capture-pap"),
    ("function", toJson capturedOrigin), ("capture", capture)]
  need ((← field functions[0]! "parameters") == toJson #[staticParam, natParam] &&
      (← field functions[1]! "parameters") == toJson #[closureParam, natParam] &&
      (← arrField functions[2]! "parameters").isEmpty)
    "capture transport residual parameters disagree"
  let residualCall := fun (index : Nat) value =>
    Json.mkObj [("op", toJson "call"), ("function", toJson index), ("value", value)]
  need ((← field functions[0]! "body") == capture &&
      (← field functions[1]! "body") == residualCall 0 (residualCall 0 (Json.mkObj [("op", toJson "argument")])) &&
      (← field functions[2]! "body") == residualCall 1 zero &&
      (← field functions[3]! "body") == residualCall 2 zero) "capture transport residual expressions disagree"

def inspect (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  let native ← field snapshot "native"
  let selector ← strField native "selector"
  let captured := selector == "closed-static-capture-nat-calls/1"
  let version := if captured then 8 else 4
  need ((← strField native "format") == "compilatrix/upstream-native/1" &&
    (captured || selector == "closed-unary-nat-calls/1") &&
    (← number native "runtime_arguments") == 0 && (← field native "word_exact") == toJson true)
    "upstream native selection domain disagrees"
  need ((← number native "lowering_version") == version && (← number native "pass_policy_version") == 1 &&
    (← strField native "symbol") == "compilatrix_main" &&
    (← strField row "optimization_policy") == "baseline-ixir2; " ++ selector) "upstream native policy disagrees"
  let expected ← number (← field row "observation") "nat"
  need ((← number native "value") == expected) "upstream native source value disagrees"
  let residual ← field native "residual"
  let functions ← arrField residual "functions"
  let entry ← number residual "entry"
  need (functions.size == 4 && entry == 3) "upstream native function inventory disagrees"
  if captured then inspectCapture snapshot functions
  let mut offsets := #[]
  let mut position := 0
  for function in functions do
    offsets := offsets.push position
    position := position + (← expressionLength 1024 (← field function "body")) + 1
  let mut text := ByteArray.empty
  for index in [:functions.size] do
    let function := functions[index]!
    let parameters ← arrField function "parameters"
    if !captured then
      for parameter in parameters do
        need (["nat", "known-capture-free-pap", "erased"].contains (← strField parameter "kind"))
          "capture-free parameter domain disagrees"
    need ((parameters.filter fun parameter => (parameter.getObjValAs? String "kind").toOption == some "nat").size ≤ 1)
      "upstream native residual has multiple Nat arguments"
    if index == entry then
      need ((← field function "origin") == Json.null && parameters.isEmpty) "upstream native main is open"
    else
      need (isHex 64 (← strField function "origin")) "upstream native origin is missing"
    text := text ++ (← expressionBytes offsets index 1024 (← field function "body") offsets[index]!) ++ little 1 0xc3
  need ((← field native "block_offsets") == toJson offsets && (← number native "text_bytes") == text.size &&
    (← byteField native "text") == text) "upstream native complete text or CALL layout disagrees"
  need ((← expressionValue functions 1024 (← field functions[entry]! "body") 0) == expected)
    "upstream residual result disagrees"
  need ((← byteField native "object") == bytes && (← number native "object_bytes") == bytes.size &&
    (← strField native "object_identity") == digest bytes) "upstream native object bytes disagree"
  inspectELFBytes bytes text offsets[entry]! (← strField row "ir1_root") version
  let physical ← field (← field snapshot "observations") "physical_ixir2"
  need ((← field native "physical_store") == (← field physical "store") &&
    (← field native "physical_value") == (← field physical "value") &&
    (← field native "reclaimed_store") == (← field physical "reclaimed")) "upstream native physical certificate disagrees"
  let reclaimed ← field (← field native "reclaimed_store") "heap"
  need ((← arrField reclaimed "nodes").all (· == Json.null) &&
    (← field reclaimed "allocs") == (← field reclaimed "frees")) "upstream native baseline reclamation disagrees"
  let heap ← field native "native_heap"
  for counter in ["allocs", "frees", "rcops"] do need ((← number heap counter) == 0) "unboxed native kernel allocated"
  need ((← number heap "result_bytes") == 8) "native Word result size disagrees"
  let executions ← arrField native "executions"
  need (executions.size == 4) "upstream native execution inventory disagrees"
  let (steps, calls, depth) ← expressionCost functions 1024 (← field functions[entry]! "body")
  for execution in executions do
    need ((← number execution "value") == expected && (← number execution "direct_calls") == calls &&
      (← number execution "stack_written_bytes") == 16 * depth && (← number execution "stack_capacity_bytes") == 64 &&
      (← number execution "typed_steps") == steps + 1 && (← number execution "byte_steps") == steps + 1)
      "upstream native computation or stack observation disagrees"
    for flag in ["saved_registers_preserved", "stack_restored_before_ret", "call_trace_certified", "object_entry_certified"] do
      need ((← field execution flag) == toJson true) s!"upstream native {flag} failed"
  let fallbacks ← arrField native "fallbacks_and_rejections"
  let budgetNames := #["zero-depth", "zero-functions", "zero-instructions"] ++
    (if captured then #["zero-capture-fuel"] else #[])
  let baselineNames := budgetNames ++ (if captured then #["capture-free-policy"] else #[])
  need ((← fallbacks.mapM (strField · "name")) == baselineNames ++ #["misaligned-stack", "insufficient-stack"])
    "upstream native fallback inventory disagrees"
  for index in [:fallbacks.size] do
    let path := if index < baselineNames.size then "checked-baseline-ixir2" else "no-native-execution-certificate"
    let reason := if index < budgetNames.size then "budget" else if index < baselineNames.size then "capturedPap" else "execution-condition"
    need ((← strField fallbacks[index]! "path") == path && (← strField fallbacks[index]! "reason") == reason)
      "native fallback path or reason disagrees"

def regressions (row snapshot : Json) (bytes : ByteArray) : IO Unit := do
  for (name, path, replacement, fragment) in [
      ("Word bound", ["native", "word_exact"], toJson false, "selection domain"),
      ("policy", ["native", "lowering_version"], toJson (1 : Nat), "native policy"),
      ("source value", ["native", "value"], toJson (99 : Nat), "source value"),
      ("text", ["native", "text"], toJson "c3", "complete text"),
      ("entry", ["native", "residual", "entry"], toJson (0 : Nat), "function inventory"),
      ("calls", ["native", "block_offsets"], toJson [0, 0, 0, 0], "CALL layout"),
      ("object", ["native", "object"], toJson "00", "object bytes"),
      ("reclamation", ["native", "reclaimed_store"], Json.null, "physical certificate"),
      ("fallbacks", ["native", "fallbacks_and_rejections"], toJson ([] : List Json), "fallback inventory")] do
    rejects name fragment (inspect row (← replaceAt snapshot path replacement) bytes)
  rejects "truncated object" "object bytes" (inspect row snapshot (bytes.extract 0 (bytes.size - 1)))
  let native ← field snapshot "native"
  let executions ← arrField native "executions"
  let badSteps ← replaceAt executions[0]! ["typed_steps"] (toJson (28 : Nat))
  rejects "executed capture cost" "computation or stack" (inspect row
    (← replaceAt snapshot ["native", "executions"] (toJson (executions.set! 0 badSteps))) bytes)
  if (← strField native "selector") != "closed-static-capture-nat-calls/1" then return
  let functions ← arrField (← field native "residual") "functions"
  let staticParams ← arrField functions[0]! "parameters"
  let closureParams ← arrField functions[1]! "parameters"
  let constant := Json.mkObj [("op", toJson "constant"), ("value", toJson (2 : Nat))]
  let wrongCapture ← replaceAt staticParams[0]! ["value"] constant
  let wrongClosure ← replaceAt closureParams[0]! ["capture"] constant
  let wrongTarget ← replaceAt closureParams[0]! ["function"] (← field functions[1]! "origin")
  for (name, index, path, replacement, fragment) in [
      ("capture expression", 0, ["parameters"], toJson (staticParams.set! 0 wrongCapture), "residual parameters"),
      ("capture parameter order", 0, ["parameters"], toJson #[staticParams[1]!, staticParams[0]!], "residual parameters"),
      ("closure capture key", 1, ["parameters"], toJson (closureParams.set! 0 wrongClosure), "residual parameters"),
      ("closure target", 1, ["parameters"], toJson (closureParams.set! 0 wrongTarget), "residual parameters"),
      ("folded capture body", 0, ["body"], constant, "residual expressions")] do
    let function ← replaceAt functions[index]! path replacement
    let changed ← replaceAt snapshot ["native", "residual", "functions"] (toJson (functions.set! index function))
    rejects name fragment (inspect row changed bytes)
  let program ← field (← field (← field snapshot "compilation") "ixir2_diagnostic") "program"
  let declarations ← arrField program "declarations"
  let initializer ← physicalBlock program (← strField functions[2]! "origin") 0
  let instructions ← arrField initializer "instructions"
  let wrongPap ← replaceAt instructions[3]! ["papp", "args"] (toJson #[register 1])
  for (name, origin, blockPath, replacement, fragment) in [
      ("physical capture return", 0, ["terminator", "ret", "value"], register 1, "physical parameter order"),
      ("physical capture initializer", 2, ["instructions"], toJson ([] : List Json), "physical initializer"),
      ("physical PAP capture", 2, ["instructions"], toJson (instructions.set! 3 wrongPap), "physical initializer"),
      ("physical PAP safety", 0, [], Json.null, "physical signature")] do
    let target ← field functions[origin]! "origin"
    let mut changedDeclarations := declarations
    for index in [:declarations.size] do
      let declaration ← array declarations[index]!
      if declaration[0]! != target then continue
      let definition ← field (← field declaration[1]! "fn") "definition"
      let changedDefinition ← if blockPath.isEmpty then replaceAt definition ["signature", "papSafe"] (toJson false)
        else do
          let blocks ← arrField definition "blocks"
          let block ← replaceAt blocks[0]! blockPath replacement
          replaceAt definition ["blocks"] (toJson (blocks.set! 0 block))
      let changed ← replaceAt declaration[1]! ["fn", "definition"] changedDefinition
      changedDeclarations := changedDeclarations.set! index (toJson (declaration.set! 1 changed))
    let changed ← replaceAt snapshot ["compilation", "ixir2_diagnostic", "program", "declarations"] (toJson changedDeclarations)
    rejects name fragment (inspect row changed bytes)

end Ix.Compiler.Tools.UpstreamNativeCheck
