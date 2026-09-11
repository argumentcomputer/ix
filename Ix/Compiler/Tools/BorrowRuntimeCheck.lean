import Ix.Compiler.Tools.BorrowExecution

/-! Independent structural reconstruction and runtime-input replay for B2.
This module imports no compiler, optimizer, ownership checker, evaluator,
source generator, or semantic certificate. -/

namespace Ix.Compiler.Tools.BorrowRuntimeCheck

open Lean Ix.Compiler.Tools.Check Ix.Compiler.Tools.BorrowCheck

def atomNat (n : Nat) : Json := tagged "lit" [("literal", tagged "nat" [("n", toJson n)])]

def signature (borrow : Bool) : Json := obj [
  ("params", toJson #[obj [("world", toJson "shared"), ("passing", toJson (if borrow then "borrowed" else "owned"))]]),
  ("result", toJson "shared"), ("papSafe", toJson (!borrow))]

def block (borrow : Bool) (instructions : Array Json) (terminator : Json) : Json := obj [
  ("valueParams", toJson #[if borrow then borrowed else owned]), ("creditParams", toJson (#[] : Array Json)),
  ("instructions", toJson instructions), ("terminator", terminator)]

def ret (value : Json) : Json := tagged "ret" [("value", value)]
def call (tag address : String) (args : Array Json) : Json := tagged tag [("function", toJson address), ("args", toJson args)]

def forward (borrow : Bool) (address : String) : Json := obj [
  ("signature", signature borrow), ("blocks", toJson #[block borrow #[] (call "tailCall" address #[reg 0])])]

def twice (borrow : Bool) (address : String) : Json := obj [
  ("signature", signature borrow), ("blocks", toJson #[block borrow #[
    if borrow then tagged "move" [("value", reg 0)] else tagged "retainShared" [("target", reg 0)],
    call "call" address #[reg 1], tagged "releaseShared" [("target", reg 2)]] (call "tailCall" address #[reg 0])])]

def reader (schema : Json) (borrow : Bool) : IO Json := do
  let zero ← field schema "zero"
  let succ ← field schema "succ"
  let releases := if borrow then #[] else #[tagged "releaseShared" [("target", reg 0)]]
  let edge := fun (target : Nat) => obj [("target", toJson target), ("values", toJson #[reg 0]), ("credits", toJson (#[] : Array Json))]
  let switch := tagged "switchValue" [("scrutinee", reg 0), ("natPeel", Json.null),
    ("constructors", toJson #[obj [("cid", zero), ("edge", edge 1)], obj [("cid", succ), ("edge", edge 2)]])]
  return obj [("signature", signature borrow), ("blocks", toJson #[
    block borrow #[] switch,
    block borrow releases (ret (atomNat (← number schema "zeroResult"))),
    block borrow (#[tagged "fetch" [("target", reg 0), ("cid", succ), ("field", toJson (0 : Nat))]] ++ releases)
      (ret (atomNat (← number schema "succResult")))])]

def nullary (papSafe : Bool) (instructions : Array Json) (terminator : Json) : Json := obj [
  ("signature", obj [("params", toJson (#[] : Array Json)), ("result", toJson "shared"), ("papSafe", toJson papSafe)]),
  ("blocks", toJson #[obj [("valueParams", toJson (#[] : Array Json)), ("creditParams", toJson (#[] : Array Json)),
    ("instructions", toJson instructions), ("terminator", terminator)]])]

def callerAddress : String := String.join (List.replicate 32 "f0")

def dynamicCaller (entry : String) : Json := obj [
  ("signature", obj [("params", toJson #[obj [("world", toJson "shared"), ("passing", toJson "owned")]]),
    ("result", toJson "shared"), ("papSafe", toJson false)]),
  ("blocks", toJson #[block false #[call "papp" entry #[], tagged "apply" [("function", reg 1), ("args", toJson #[reg 0])]] (ret (reg 2))])]

def withCaller (program : Json) (entry : String) : IO Json := do
  let declarations ← arrField program "declarations"
  for declaration in declarations do
    need ((← BorrowCheck.entry declaration).1 != callerAddress) "caller adapter label collision"
  replace program "declarations" (toJson (declarations.push (toJson #[toJson callerAddress,
    tagged "fn" [("definition", dynamicCaller entry)]])))

private def callee (definition : Json) : IO String := do
  let blocks ← arrField definition "blocks"
  let block ← present blocks[0]? "missing reader entry block"
  let (tag, term) ← constructor (← field block "terminator")
  need (tag == "tailCall") "expected a direct call-chain link"
  strField term "function"

def inspectGraph (row baseline rewritten : Json) : IO Unit := do
  let depth ← number row "depth"
  let schema ← field row "schema"
  need ((← number schema "zeroResult") == 11 && (← number schema "succResult") == 22 &&
    (← number (← field schema "zero") "cidx") == 0 && (← number (← field schema "succ") "cidx") == 1 &&
    (← number (← field schema "zero") "indIdx") == 0 && (← number (← field schema "succ") "indIdx") == 0)
    "runtime reader schema changed"
  let entry ← strField row "entry"
  let borrowedEntry ← strField row "borrowed_entry"
  let factory ← strField row "factory"
  let summaries ← arrField (← field row "inference") "summaries"
  inspectRewrite baseline rewritten summaries
  need ((← target summaries entry) == borrowedEntry && borrowedEntry != entry) "owned/borrowed export mapping mismatch"
  let factoryDefinition := nullary true #[call "papp" entry #[]] (ret (reg 0))
  let main := nullary false #[] (call "tailCall" factory #[])
  need ((← function baseline factory) == factoryDefinition && (← function rewritten factory) == factoryDefinition &&
    (← field baseline "main") == main && (← field rewritten "main") == main) "runtime owned PAP export changed"
  let entryDefinition ← function baseline entry
  let mut address ← callee entryDefinition
  need (entryDefinition == twice false address) "runtime entry does not read its argument twice"
  let expectedReader ← reader schema false
  let mut covered := #[entry]
  let mut links := 0
  let mut finished := false
  for _ in [:33] do
    need (!covered.contains address) "cyclic borrowed dependency"
    covered := covered.push address
    let definition ← function baseline address
    if definition == expectedReader then
      finished := true
      break
    let next ← callee definition
    need (definition == forward false next) "non-reader body in the runtime call chain"
    address := next
    links := links + 1
  need (finished && links == depth && covered.size == depth + 2) "runtime chain depth mismatch"
  let owners ← summaries.mapM (strField · "owner")
  need (owners.size == covered.size && owners.all covered.contains && covered.all owners.contains)
    "unproved or omitted borrowed summary"
  let mut extras := 0
  for declaration in ← arrField baseline "declarations" do
    let (owner, definition) ← BorrowCheck.entry declaration
    if !covered.contains owner && owner != factory then
      need (definition == nullary true #[] (ret (toJson "erased"))) "unexpected source function outside the checked chain"
      extras := extras + 1
  need (extras == 1) "runtime source erased declaration inventory mismatch"
  need ((← field row "baseline_size") == (← programSize baseline) &&
    (← field row "borrowed_size") == (← programSize rewritten)) "runtime code growth report mismatch"
  for (key, declarations, blocks, instructions) in [
      ("baseline_size", depth + 4, depth + 7, 7),
      ("borrowed_size", 2 * depth + 6, 2 * depth + 9, 2 * depth + 9)] do
    let size ← field row key
    need ((← number size "declarations") == declarations && (← number size "blocks") == blocks &&
      (← number size "instructions") == instructions) "runtime wrapper/code-size formula changed"

def scalarTree (value : Nat) : Json := tagged "scalar" [("value", toJson value)]
def succTree (tail : Json) : Json := tagged "succ" [("tail", tail)]
def nested : Nat → Json → Json
  | 0, value => value
  | count + 1, value => succTree (nested count value)
def succArgument (payload : Json) : Json := tagged "succ" [("payload", payload)]

def expectedInputs : Array (String × Json) := #[
  ("zero", toJson "zero"), ("succ-0", succArgument (scalarTree 0)),
  ("succ-1", succArgument (scalarTree 1)), ("succ-wide", succArgument (scalarTree (2 ^ 256 + 19))),
  ("nested-zero-1", succArgument (toJson "zero")),
  ("nested-zero-8", succArgument (nested 7 (toJson "zero"))),
  ("nested-zero-32", succArgument (nested 31 (toJson "zero"))),
  ("nested-scalar-17", succArgument (nested 16 (scalarTree 4096)))]

structure Built where
  memory : Memory
  value : Json
  scalarLeaves : Nat

def appendCtor (memory : Memory) (cid : Json) (fields : Array Json) : Memory × Json :=
  let index := memory.nodes.size
  ({ memory with
      nodes := memory.nodes.push (obj [("world", toJson "shared"), ("rc", toJson (1 : Nat)),
        ("node", tagged "ctorN" [("cid", cid), ("fields", toJson fields)])])
      allocs := memory.allocs + 1, peak := memory.allocs + 1 }, tagged "loc" [("l", toJson index)])

def makeTree (schema : Json) : Nat → Json → IO Built
  | 0, _ => throw (IO.userError "runtime input tree bound exceeded")
  | fuel + 1, tree => do
      if tree == toJson "zero" then
        let (memory, value) := appendCtor {} (← field schema "zero") #[]
        return ⟨memory, value, 0⟩
      let (tag, data) ← constructor tree
      if tag == "scalar" then return ⟨{}, scalar (← number data "value"), 1⟩
      need (tag == "succ") "unknown runtime input tree"
      let child ← makeTree schema fuel (← field data "tail")
      let (memory, value) := appendCtor child.memory (← field schema "succ") #[child.value]
      return ⟨memory, value, child.scalarLeaves⟩

def makeArgument (schema argument : Json) : IO Built := do
  if argument == toJson "zero" then makeTree schema 64 argument else do
    let (tag, data) ← constructor argument
    need (tag == "succ") "runtime root must be a constructor"
    makeTree schema 64 (succTree (← field data "payload"))

def inspectInput (row baseline rewritten observation : Json) (name : String) (argument : Json) : IO Unit := do
  let schema ← field row "schema"
  let built ← makeArgument schema argument
  let nodes := built.memory.allocs
  let successorCase := argument != toJson "zero"
  let expected := if successorCase then 22 else 11
  need ((← strField observation "name") == name && (← field observation "argument") == argument &&
    (← field observation "input_store") == built.memory.json && (← field observation "input_value") == built.value &&
    (← number observation "nodes") == nodes && (← number observation "number") == expected &&
    (← number observation "ixon") == expected && (← number observation "raw_ixir0") == expected)
    "runtime argument or source observation mismatch"
  let paths ← arrField observation "paths"
  need (paths.size == 2) "missing direct/PAP runtime comparison"
  let depth ← number row "depth"
  let entry ← strField row "entry"
  for index in [:2] do
    let dynamic := index == 1
    let path := paths[index]!
    need ((← strField path "kind") == (if dynamic then "dynamic" else "direct")) "runtime invocation kind changed"
    let initial : Machine := { memory := built.memory, frame := { owner := if dynamic then callerAddress else entry, values := #[built.value] } }
    for (label, program, extraRC, extraSteps, extraWork) in [
        ("baseline", baseline, 2, 0, 2), ("borrowed", rewritten, 0, 1, 1)] do
      let program ← if dynamic then withCaller program entry else pure program
      let result ← field path label
      inspectExecutionFrom program (← field path s!"{label}_prefixes") result expected initial
      let store ← field result "store"
      let heap ← field store "heap"
      let allocations := nodes + (if dynamic then 1 else 0)
      let steps := 2 * depth + 10 + (if successorCase then 2 else 0) + (if dynamic then 3 else 0) + extraSteps
      let work := nodes + built.scalarLeaves + extraWork + (if dynamic then 1 else 0)
      need ((← number heap "allocs") == allocations && (← number heap "frees") == allocations &&
        (← number heap "rcops") == nodes + extraRC + (if dynamic then 1 else 0) &&
        (← number store "peakLiveNodes") == allocations &&
        (← number result "control_remaining") + steps == 1000 &&
        (← number result "heap_remaining") + work == 1000) "runtime RC/heap/control contract drifted"

def inspectLender (row rewritten lender : Json) : IO Unit := do
  let argument := succArgument (nested 7 (toJson "zero"))
  let built ← makeArgument (← field row "schema") argument
  let (_, locationData) ← constructor built.value
  let location ← number locationData "l"
  let node ← built.memory.get location
  let memory := { built.memory with nodes := built.memory.nodes.set! location (← replace node "rc" (toJson (3 : Nat))), rcops := 2 }
  need ((← field lender "argument") == argument && (← number lender "owners") == 3 &&
    (← field lender "input_store") == memory.json && (← field lender "input_value") == built.value)
    "aliased caller input mismatch"
  let result ← field lender "execution"
  let prefixes ← field lender "prefixes"
  inspectExecutionFrom rewritten prefixes result 22
    { memory, frame := { owner := ← strField row "borrowed_entry", values := #[built.value] } } false
  need ((← field result "store") == memory.json) "borrowed entry consumed its lender"
  for row in ← array prefixes do need ((← field row "store") == memory.json) "borrowed prefix changed lender heap"
  need ((← number result "control_remaining") + 2 * (← number row "depth") + 10 == 1000 &&
    (← number result "heap_remaining") == 999) "borrowed entry execution cost changed"
  let cleaned ← reclaimCopies { memory with remaining := 999 } built.value 3
  need ((← field lender "cleanup_store") == cleaned.json && (← number lender "cleanup_remaining") == cleaned.remaining &&
    cleaned.nodes.all (· == Json.null) && cleaned.frees == cleaned.allocs) "caller failed to reclaim its returned lender"

end Ix.Compiler.Tools.BorrowRuntimeCheck
