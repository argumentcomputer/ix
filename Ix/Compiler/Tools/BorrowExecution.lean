import Ix.Compiler.Tools.BorrowCheck

/-! A separate interpreter for the small shared-heap instruction slice used
by the source-borrow fixtures. It checks every exported control state, frame
value, heap slot, RC update, release work item, and continuation transition.
It imports neither the compiler evaluator nor the borrowed-call pass. -/

namespace Ix.Compiler.Tools.BorrowCheck

open Lean Ix.Compiler.Tools.Check

structure Memory where
  nodes : Array Json := #[]
  allocs : Nat := 0
  frees : Nat := 0
  rcops : Nat := 0
  peak : Nat := 0
  remaining : Nat := 1000

def Memory.json (memory : Memory) : Json :=
  obj [("heap", obj [("nodes", toJson memory.nodes), ("allocs", toJson memory.allocs),
    ("frees", toJson memory.frees), ("rcops", toJson memory.rcops), ("reuses", toJson (0 : Nat))]),
    ("peakLiveNodes", toJson memory.peak), ("resetAttempts", toJson (0 : Nat)),
    ("hotResets", toJson (0 : Nat)), ("coldResets", toJson (0 : Nat)),
    ("reusedPayloadUnits", toJson (0 : Nat))]

private def location (value : Json) : IO (Option Nat) := do
  if value == toJson "erased" then return none
  let (tag, info) ← constructor value
  if tag == "loc" then return some (← number info "l")
  need (tag == "lit") "malformed runtime value"
  return none

def Memory.get (memory : Memory) (index : Nat) : IO Json := do
  let some node := memory.nodes[index]? | throw (IO.userError "heap location out of bounds")
  need (node != Json.null && (← strField node "world") == "shared" && (← number node "rc") > 0)
    "dead or invalid shared heap location"
  return node

private def retain (memory : Memory) (value : Json) : IO Memory := do
  let some index ← location value | return memory
  let node ← memory.get index
  let node ← replace node "rc" (toJson ((← number node "rc") + 1))
  return { memory with nodes := memory.nodes.set! index node, rcops := memory.rcops + 1 }

private def release (initial : Memory) (value : Json) : IO Memory := do
  let mut memory := initial
  let mut todo := [value]
  for _ in [:1001] do
    let head :: rest := todo | return memory
    todo := rest
    need (memory.remaining > 0) "independent release budget exhausted"
    memory := { memory with remaining := memory.remaining - 1 }
    if let some index ← location head then
      let box ← memory.get index
      let rc ← number box "rc"
      memory := { memory with rcops := memory.rcops + 1 }
      if rc > 1 then
        memory := { memory with nodes := memory.nodes.set! index (← replace box "rc" (toJson (rc - 1))) }
      else
        let (tag, node) ← constructor (← field box "node")
        let children ← arrField node (if tag == "ctorN" then "fields" else "args")
        need (tag == "ctorN" || tag == "papN") "invalid heap node tag"
        todo := children.toList ++ todo
        memory := { memory with nodes := memory.nodes.set! index Json.null, frees := memory.frees + 1 }
  throw (IO.userError "independent release work exceeded its bound")

private def allocate (memory : Memory) (node : Json) : Memory × Json :=
  let index := memory.nodes.size
  let nodes := memory.nodes.push (obj [("world", toJson "shared"), ("rc", toJson (1 : Nat)), ("node", node)])
  ({ memory with
      nodes, allocs := memory.allocs + 1
      peak := max memory.peak (nodes.countP (· != Json.null)) }, tagged "loc" [("l", toJson index)])

structure Frame where
  owner : String := "main"
  block : Nat := 0
  pc : Nat := 0
  values : Array Json := #[]

structure Machine where
  memory : Memory := {}
  frame : Frame := {}
  stack : List Frame := []
  halted : Option Json := none

def Machine.control (machine : Machine) : Json :=
  match machine.halted with
  | some value => obj [("halted", value)]
  | none => obj [("owner", toJson machine.frame.owner), ("block", toJson machine.frame.block),
      ("pc", toJson machine.frame.pc), ("values", toJson machine.frame.values),
      ("stack_depth", toJson machine.stack.length)]

private def resolve (frame : Frame) (atom : Json) : IO Json := do
  if atom == toJson "erased" then return atom
  let (tag, info) ← constructor atom
  match tag with
  | "reg" =>
      present frame.values[← number info "id"]? "unbound operand register"
  | "lit" => return tagged "lit" [("l", ← field info "literal")]
  | _ => throw (IO.userError "unknown block atom")

private def arguments (frame : Frame) (args : Json) : IO (Array Json) := do
  (← array args).mapM (resolve frame)

private def enter (program : Json) (owner : String) (values : Array Json) : IO Frame := do
  let definition ← function program owner
  let signature ← field definition "signature"
  need ((← arrField signature "params").size == values.size && !(← arrField definition "blocks").isEmpty)
    "independent call entry mismatch"
  return { owner, values }

private def papArity (program : Json) (owner : String) : IO Nat := do
  let signature ← field (← function program owner) "signature"
  need ((← field signature "papSafe") == toJson true && (← strField signature "result") == "shared")
    "dynamic entry reached a borrowed or non-shared signature"
  let params ← arrField signature "params"
  for param in params do
    need ((← strField param "world") == "shared" && (← strField param "passing") == "owned")
      "dynamic argument is not owned"
  return params.size

private def transfer (machine : Machine) (edge : Json) : IO Machine := do
  need ((← arrField edge "credits").isEmpty) "unexpected edge credit"
  let values ← arguments machine.frame (← field edge "values")
  return { machine with frame := { machine.frame with block := ← number edge "target", pc := 0, values } }

def step (program : Json) (machine : Machine) : IO Machine := do
  need machine.halted.isNone "extra transition after halt"
  let definition ← function program machine.frame.owner
  let blocks ← arrField definition "blocks"
  let block ← present blocks[machine.frame.block]? "missing execution block"
  need ((← arrField block "creditParams").isEmpty) "unexpected execution credit"
  let instructions ← arrField block "instructions"
  let frame := machine.frame
  let next := { frame with pc := frame.pc + 1 }
  if frame.pc < instructions.size then
    let (tag, args) ← constructor instructions[frame.pc]!
    match tag with
    | "move" =>
        return { machine with frame := { next with values := next.values.push (← resolve frame (← field args "value")) } }
    | "retainShared" =>
        let value ← resolve frame (← field args "target")
        return { machine with
          memory := ← retain machine.memory value
          frame := { next with values := next.values.push value } }
    | "releaseShared" =>
        return { machine with memory := ← release machine.memory (← resolve frame (← field args "target")), frame := next }
    | "alloc" =>
        need ((← strField args "world") == "shared") "unexpected allocation world"
        let values ← arguments frame (← field args "args")
        let (memory, value) := allocate machine.memory (tagged "ctorN" [("cid", ← field args "cid"), ("fields", toJson values)])
        return { machine with memory, frame := { next with values := next.values.push value } }
    | "fetch" =>
        let some index ← location (← resolve frame (← field args "target"))
          | throw (IO.userError "fetch target is not a location")
        let node ← field (← field (← machine.memory.get index) "node") "ctorN"
        need ((← field node "cid") == (← field args "cid")) "fetch constructor mismatch"
        let fields ← arrField node "fields"
        let value ← present fields[← number args "field"]? "fetch field missing"
        return { machine with frame := { next with values := next.values.push value } }
    | "call" =>
        let callee ← enter program (← strField args "function") (← arguments frame (← field args "args"))
        return { machine with frame := callee, stack := next :: machine.stack }
    | "papp" =>
        let owner ← strField args "function"
        let arity ← papArity program owner
        let values ← arguments frame (← field args "args")
        need (values.size < arity) "saturated papp instruction"
        let (memory, value) := allocate machine.memory
          (tagged "papN" [("f", toJson owner), ("arity", toJson arity), ("args", toJson values)])
        return { machine with memory, frame := { next with values := next.values.push value } }
    | "apply" =>
        let value ← resolve frame (← field args "function")
        let some index ← location value | throw (IO.userError "fixture apply is not a PAP")
        let pap ← field (← field (← machine.memory.get index) "node") "papN"
        let owner ← strField pap "f"
        let arity ← papArity program owner
        need ((← number pap "arity") == arity) "PAP arity mismatch"
        let captured ← arrField pap "args"
        let values := captured ++ (← arguments frame (← field args "args"))
        need (captured.size < arity && values.size == arity) "fixture application left the exact-saturation slice"
        let mut memory := machine.memory
        for value in captured do memory ← retain memory value
        memory ← release memory value
        return { machine with memory, frame := ← enter program owner values, stack := next :: machine.stack }
    | _ => throw (IO.userError s!"unsupported independent instruction {tag}")
  else
    need (frame.pc == instructions.size) "execution pc passed terminator"
    let (tag, args) ← constructor (← field block "terminator")
    match tag with
    | "ret" =>
        let value ← resolve frame (← field args "value")
        match machine.stack with
        | [] => return { machine with halted := some value }
        | caller :: rest =>
            return { machine with
              stack := rest, frame := { caller with values := caller.values.push value } }
    | "tailCall" =>
        let callee ← enter program (← strField args "function") (← arguments frame (← field args "args"))
        return { machine with frame := callee }
    | "jump" => transfer machine (← field args "edge")
    | "switchValue" =>
        let some index ← location (← resolve frame (← field args "scrutinee"))
          | throw (IO.userError "fixture switch is not a heap constructor")
        let ctor ← field (← field (← machine.memory.get index) "node") "ctorN"
        let alternatives ← arrField args "constructors"
        for alternative in alternatives do
          if (← field alternative "cid") == (← field ctor "cid") then
            return ← transfer machine (← field alternative "edge")
        throw (IO.userError "missing independent switch alternative")
    | _ => throw (IO.userError s!"unsupported independent terminator {tag}")

def inspectExecutionFrom (program prefixes result : Json) (expected : Nat)
    (initial : Machine) (requireReclamation : Bool := true) : IO Unit := do
  let prefixes ← array prefixes
  need (!prefixes.isEmpty && prefixes.size ≤ 1001) "invalid execution-prefix count"
  let mut machine := initial
  for index in [:prefixes.size] do
    let row := prefixes[index]!
    need ((← number row "step") == index && (← field row "store") == machine.memory.json &&
      (← number row "heap_remaining") == machine.memory.remaining &&
      (← field row "control") == machine.control) s!"independent execution mismatch at step {index}"
    if index + 1 < prefixes.size then machine ← step program machine
  need (machine.halted == some (scalar expected)) "independent result mismatch"
  if requireReclamation then
    need (machine.memory.nodes.all (· == Json.null) && machine.memory.allocs == machine.memory.frees)
      "independent reclamation mismatch"
  need ((← field result "value") == scalar expected && (← field result "store") == machine.memory.json &&
    (← number result "control_remaining") + prefixes.size - 1 == 1000 &&
    (← number result "heap_remaining") == machine.memory.remaining) "replay result differs from independent execution"

def inspectExecution (program prefixes result : Json) (expected : Nat) : IO Unit :=
  inspectExecutionFrom program prefixes result expected {}

def reclaimCopies (initial : Memory) (value : Json) (count : Nat) : IO Memory := do
  need (count ≤ 32) "caller release count exceeded its bound"
  let mut memory := initial
  for _ in [:count] do memory ← release memory value
  return memory

end Ix.Compiler.Tools.BorrowCheck
