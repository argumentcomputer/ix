import Ix.Compiler.CallReuse.Observations

/-! Independent policy and rejection witnesses. These hand-built boundary
tests supplement the source-produced map matrix; they are not compiler input
fixtures for the source theorem or its artifact gate. -/

namespace Ix.Compiler.CallReuse.PolicyExamples

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2
open Lean

private def layout : Address := Address.replicate 0x91
private def node : CtorId := { block := Address.replicate 0x92, indIdx := 0, cidx := 0 }
private def other : CtorId := { node with cidx := 1 }
private def leafAddress : Address := Address.replicate 0x93
private def childAddress : Address := Address.replicate 0x94

private def schemas (world : Owned) (ctor : CtorId) : Option CtorSchema :=
  if ctor == node then some { layout, fields := #[world] }
  else if ctor == other then some { layout := Address.replicate 0x95, fields := #[world] }
  else none

private def validation : Validate.Context := { schemas }
private def signature (world : Owned := .shared) : Signature :=
  { params := #[], result := world, papSafe := world == .shared }
private def block (instructions : Array Instr) (terminator : Terminator) : Block :=
  { valueParams := #[], creditParams := #[], instructions, terminator }
private def leaf : Function :=
  { signature := signature, blocks := #[block #[] (.ret (.lit (.nat 23)))] }

private def prefixInstructions (world : Owned := .shared) : Array Instr :=
  #[.alloc world node #[.lit (.nat 7)],
    match world with | .shared => .resetShared (.reg 0) node | .unique => .takeUnique (.reg 0) node]

private def reuseBody (world : Owned := .shared) (callee : Address := leafAddress) : Function :=
  { signature := signature world
    blocks := #[block (prefixInstructions world ++
      #[.call callee #[], .releaseShared (.reg 2), .allocWith 0 world node #[.reg 1]]) (.ret (.reg 3))] }

private def reuseProgram (world : Owned := .shared) : Program :=
  { declarations := [(leafAddress, .fn leaf)], main := reuseBody world }

private def discardProgram (world : Owned := .shared) : Program :=
  { declarations := [(leafAddress, .fn leaf)]
    main := {
      signature := signature
      blocks := #[block (prefixInstructions world ++ #[.call leafAddress #[], .discardCredit 0,
        match world with | .shared => .releaseShared (.reg 1) | .unique => .dropUnique (.reg 1)])
        (.ret (.reg 2))] } }

private def coldProgram : Program :=
  { declarations := [(leafAddress, .fn leaf)]
    main := {
      signature := signature
      blocks := #[block #[.alloc .shared node #[.lit (.nat 7)], .retainShared (.reg 0),
        .resetShared (.reg 0) node, .call leafAddress #[], .releaseShared (.reg 3),
        .allocWith 0 .shared node #[.reg 2], .releaseShared (.reg 1)] (.ret (.reg 4))] } }

private def nestedProgram : Program :=
  { declarations := [(leafAddress, .fn leaf), (childAddress, .fn (reuseBody))]
    main := reuseBody .shared childAddress }

private def edgeProgram (credits : Array Nat) (targetCredits : Array CreditCap)
    (targetInstructions : Array Instr) : Program :=
  { declarations := [(leafAddress, .fn leaf)]
    main := {
      signature := signature
      blocks := #[
        block (prefixInstructions ++ #[.call leafAddress #[], .releaseShared (.reg 1), .releaseShared (.reg 2)])
          (.jump { target := 1, values := #[], credits }),
        { valueParams := #[], creditParams := targetCredits, instructions := targetInstructions
          terminator := .ret (.lit (.nat 9)) }] } }

private def need (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def accepted (program : Program) : Except String Unit := do
  let _ ← (Validate.validateWithPolicy .suspendedCallsV1 Validate.defaultLimits validation program).mapError
    (fun error => s!"v1 rejected: {repr error}")
  match Validate.validate validation program with
  | .ok _ => throw "v0 accepted a live call credit"
  | .error (.invalid _ .credit _) => pure ()
  | .error error => throw s!"v0 rejected at the wrong boundary: {repr error}"

private def rejected (name : String) (program : Program) (violation : Validate.Violation := .credit) :
    Except String String := do
  match Validate.validateWithPolicy .suspendedCallsV1 Validate.defaultLimits validation program with
  | .ok _ => throw s!"{name}: v1 unexpectedly accepted"
  | .error (.invalid _ actual _) => need (actual == violation) s!"{name}: rejected for {repr actual}"
  | .error error => throw s!"{name}: wrong rejection {repr error}"
  return name

private def run (program : Program) (mode : Eval.Interpretation) : Except String Eval.Result :=
  (Eval.Policy.runMain .suspendedCallsV1 (Eval.Context.ofProgram program schemas)
    mode program 10000 10000).mapError reprStr

private def releaseResult (program : Program) (result : Eval.Result) : Except String Eval.Store := do
  let (released, _) ← (match program.main.signature.result with
    | .shared => Eval.releaseShared 10000 result.store result.value
    | .unique => Eval.dropUniqueWork 10000 result.store [result.value]).mapError reprStr
  need (released.live == 0 && released.heap.allocs == released.heap.frees) "policy result did not reclaim fully"
  return released

private def execution (name : String) (program : Program) (expectedReuses expectedCredits : Nat) :
    Except String String := do
  accepted program
  let logical ← run program .logical
  let physical ← run program .physical
  let (_, maximum, _) ← Examples.prefixObservations validation program .suspendedCallsV1 physical physical
  need (physical.store.heap.reuses == expectedReuses && maximum == expectedCredits) s!"{name}: credit/reuse counts"
  need (logical.store.heap.allocs == physical.store.heap.allocs + physical.store.heap.reuses &&
    logical.store.heap.frees == physical.store.heap.frees + physical.store.heap.reuses &&
    logical.store.heap.rcops == physical.store.heap.rcops) s!"{name}: logical/physical counters"
  let _ ← releaseResult program logical
  let _ ← releaseResult program physical
  match Eval.runMain (Eval.Context.ofProgram program schemas) .physical program 10000 10000 with
  | .ok _ => throw s!"{name}: original evaluator crossed a live call credit"
  | .error (.mem detail) => need (detail.contains "credit") s!"{name}: wrong original error"
  | .error error => throw s!"{name}: wrong original rejection {repr error}"
  return name

private def withSuffix (instructions : Array Instr) (terminator : Terminator) : Program :=
  { declarations := [(leafAddress, .fn leaf)]
    main := { signature := signature, blocks := #[block (prefixInstructions ++ instructions) terminator] } }

/-- Policy v1 permits only direct non-tail calls at a live-credit boundary;
linear consumption, frame isolation, and every other boundary remain checked. -/
def checks : Except String (List String) := do
  let mut names := []
  for (name, program, reuses, maximum) in [
      ("optional-hot-call", reuseProgram, 1, 1),
      ("optional-cold-call", coldProgram, 0, 1),
      ("required-call", reuseProgram .unique, 1, 1),
      ("optional-discard-after-return", discardProgram, 0, 1),
      ("required-discard-after-return", discardProgram .unique, 0, 1),
      ("nested-independent-callers", nestedProgram, 2, 2),
      ("edge-transfer-after-return", edgeProgram #[0] #[.optional layout] #[.discardCredit 0], 0, 1)] do
    names := names ++ [← (execution name program reuses maximum).mapError (fun message => s!"{name}: {message}")]
  let self := withSuffix #[.callSelf #[], .releaseShared (.reg 2), .allocWith 0 .shared node #[.reg 1]] (.ret (.reg 3))
  accepted self
  names := names ++ ["callSelf-policy-boundary"]
  let malformed := [
    ("double-consumption", withSuffix #[.call leafAddress #[], .discardCredit 0, .discardCredit 0] (.ret (.reg 2)), Validate.Violation.credit),
    ("unconsumed-return", withSuffix #[.call leafAddress #[], .releaseShared (.reg 1)] (.ret (.reg 2)), .resources),
    ("tail-call-live-credit", withSuffix #[] (.tailCall leafAddress #[]), .credit),
    ("tail-self-live-credit", withSuffix #[] (.tailCallSelf #[]), .credit),
    ("papp-live-credit", withSuffix #[.papp leafAddress #[]] (.ret (.reg 2)), .credit),
    ("apply-live-credit", withSuffix #[.apply (.lit (.nat 0)) #[]] (.ret (.reg 2)), .credit),
    ("extern-live-credit", withSuffix #[.extern leafAddress #[]] (.ret (.reg 2)), .credit),
    ("layout-mismatch-after-return", withSuffix #[.call leafAddress #[], .releaseShared (.reg 2),
      .allocWith 0 .shared other #[.reg 1]] (.ret (.reg 3)), .credit),
    ("duplicate-edge-credit", edgeProgram #[0, 0] #[.optional layout, .optional layout]
      #[.discardCredit 0, .discardCredit 1], .credit),
    ("omitted-edge-credit", edgeProgram #[] #[] #[], .resources)]
  for (name, program, violation) in malformed do names := names ++ [← rejected name program violation]
  let thief := { reuseProgram with
    declarations := [(leafAddress, .fn { leaf with blocks := #[block #[.discardCredit 0] (.ret (.lit (.nat 0)))] })] }
  names := names ++ [← rejected "callee-cannot-consume-ancestor-credit" thief .register]
  match run thief .physical with
  | .ok _ => throw "callee accessed its ancestor's credit register"
  | .error message => need (message.contains "credit") "callee failed for unrelated reason"
  let fallback : Program := {
    declarations := []
    main := {
      signature := signature .unique
      blocks := #[block (prefixInstructions .unique ++ #[.allocWith 0 .unique node #[.reg 1]]) (.ret (.reg 2))] } }
  match sourceAccepted : Validate.validateWith Validate.defaultLimits validation fallback with
  | .error error => throw s!"fallback baseline invalid: {repr error}"
  | .ok stats =>
      let selected := CallReuse.selectChecked Validate.defaultLimits validation fallback ⟨stats, sourceAccepted⟩
      match selected with
      | .optimized .. => throw "credit-bearing source escaped the source-ready check"
      | .baseline _ (.unsupportedSource) _ =>
          need (selected.target == fallback && selected.policy == .callLocalV0) "fallback changed its program or policy"
          let actual ← (Eval.Policy.runMain selected.policy (Eval.Context.ofProgram selected.target schemas)
            .physical selected.target 10000 10000).mapError reprStr
          let original ← (Eval.runMain (Eval.Context.ofProgram fallback schemas)
            .physical fallback 10000 10000).mapError reprStr
          need (toJson actual.store == toJson original.store && actual.value == original.value)
            "checked fallback changed execution"
      | .baseline _ error _ => throw s!"unexpected fallback reason {repr error}"
  names := names ++ ["checked-baseline-fallback"]
  let shape : CallReuse.Shape := {
    valueParams := #[.owned .shared], source := 0, sourceConstructor := node, fieldCount := 1
    calls := #[.call leafAddress #[]], allocationConstructor := node
    allocationArguments := #[.reg 2], result := .reg 4 }
  need ((CallReuse.inspect Validate.defaultLimits validation shape.baseline).isSome) "canonical site was not recognized"
  for (name, changed) in [
      ("site-indirect-call", { shape with calls := #[.papp leafAddress #[]] }),
      ("site-no-call", { shape with calls := #[] }),
      ("site-live-owner", { shape with calls := #[.call leafAddress #[.reg 0]] }),
      ("site-layout-mismatch", { shape with allocationConstructor := other })] do
    need ((CallReuse.inspect Validate.defaultLimits validation changed.baseline).isNone &&
      CallReuse.rewriteBlock Validate.defaultLimits validation changed.baseline == changed.baseline)
      s!"{name}: unsupported site was rewritten"
    names := names ++ [name]
  return names

end Ix.Compiler.CallReuse.PolicyExamples
