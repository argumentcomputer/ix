import Compilatrix.Ixby.Runtime.Run
import Compilatrix.Tools.Check

/-! An observer around the unchanged reference `Ix.Ixby.step`. This reports
native execution evidence, not a proof. Scalar maxima inspect primitive
operands, newly bound locals, returns and applications; they are not a
traversal of every value reachable from the complete heap. -/

open Ix.Ixby Compilatrix.Ixby Lean

structure Stats where
  blocks : Array Nat
  controls : Array Nat := #[0, 0, 0]
  maxLocals : Nat := 0
  maxContinuations : Nat := 0
  maxApplyArgs : Nat := 0
  maxNatBits : Nat := 0
  maxBytes : Nat := 0
  maxCtorFields : Nat := 0
  maxCaptured : Nat := 0
  deriving Inhabited

def Stats.value (s : Stats) : Value → Stats
  | .scalar (.nat n) => { s with maxNatBits := max s.maxNatBits (if n == 0 then 0 else n.log2 + 1) }
  | .scalar (.bytes bs) => { s with maxBytes := max s.maxBytes bs.size }
  | .ctor _ fs => { s with maxCtorFields := max s.maxCtorFields fs.size }
  | .pap _ fs => { s with maxCaptured := max s.maxCaptured fs.size }
  | _ => s

def Stats.operand (s : Stats) (frame : Frame) : Operand → Stats
  | .local i => match frame.locals[i]? with | some v => s.value v | none => s
  | .literal v => s.value (.scalar v)
  | .erased => s

def inspect (bases : Array Nat) (program : Program) (s : Stats) (state : State) : Stats := Id.run do
  let mut s := { s with maxContinuations := max s.maxContinuations state.continuation.size }
  match state.control with
  | .eval frame =>
    s := { s with controls := s.controls.modify 0 (· + 1), blocks := s.blocks.modify (bases[frame.function]! + frame.block) (· + 1), maxLocals := max s.maxLocals frame.locals.size }
    if let some v := frame.locals.back? then s := s.value v
    if let .letOp (.primitive _ args) _ := program.functions[frame.function]!.blocks[frame.block]!.instruction then
      s := args.foldl (fun stats op => stats.operand frame op) s
  | .ret v =>
    s := s.value v
    s := { s with controls := s.controls.modify 1 (· + 1) }
  | .apply v args =>
    s := s.value v
    s := { s with controls := s.controls.modify 2 (· + 1), maxApplyArgs := max s.maxApplyArgs args.size }
    s := args.foldl Stats.value s
  return s

def runChunk (limits : Limits) (program : Program) (bases : Array Nat) :
    Nat → State → Stats → Except Error (Sum Value State × Stats × Nat)
  | 0, state, stats => .ok (.inr state, stats, 0)
  | n + 1, state, stats => do
    let stats := inspect bases program stats state
    match ← step limits program state with
    | .halted value => return (.inl value, stats, n)
    | .next state => runChunk limits program bases n state stats

def checked {ε : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

def main (args : List String) : IO UInt32 := do
  let [programPath, inputPath, expectedPath, reportPath, maximum] := args
    | throw (IO.userError "usage: ExecutionProfile program input expected report maxsteps")
  let artifact ← checked (Binary.decode (← IO.FS.readBinFile programPath).data)
  let input ← checked (Binary.decodeInput artifact.value (← IO.FS.readBinFile inputPath).data)
  let artifact := artifact.value
  let mut state ← checked (initialState artifact.limits artifact.program input.value)
  let mut bases := #[]
  let mut total := 0
  for function in artifact.program.functions do
    bases := bases.push total
    total := total + function.blocks.size
  let mut stats : Stats := { blocks := Array.replicate total 0 }
  let mut count := 0
  let mut complete := false
  let cap := min artifact.maxSteps maximum.toNat!
  while count < cap do
    let fuel := min 1000000 (cap - count)
    let (result, nextStats, remaining) ← checked (runChunk artifact.limits artifact.program bases fuel state stats)
    stats := nextStats
    count := count + fuel - remaining
    match result with
    | .inl value =>
      let bytes ← checked (Binary.encodeOutput artifact value)
      unless bytes == (← IO.FS.readBinFile expectedPath).data do
        throw (IO.userError "profiled execution output mismatch")
      complete := true
      break
    | .inr next => state := next
    if count % 100000000 == 0 then
      IO.println s!"transitions={count}, max_locals={stats.maxLocals}, max_continuations={stats.maxContinuations}, max_nat_bits={stats.maxNatBits}"
      (← IO.getStdout).flush
  let blocks := artifact.program.functions.foldl (fun (out : Array Json) f =>
    f.blocks.foldl (fun out b => out.push (toJson (reprStr b.instruction))) out) #[]
  let report := Json.mkObj [
    ("completed", toJson complete), ("reference_transitions", toJson count),
    ("control_counts_eval_ret_apply", toJson stats.controls),
    ("max_locals", toJson stats.maxLocals), ("max_continuations", toJson stats.maxContinuations),
    ("max_apply_arguments", toJson stats.maxApplyArgs), ("max_observed_nat_bits", toJson stats.maxNatBits),
    ("max_observed_bytes", toJson stats.maxBytes), ("max_observed_constructor_fields", toJson stats.maxCtorFields),
    ("max_observed_pap_captures", toJson stats.maxCaptured),
    ("function_block_bases", toJson bases), ("block_counts", toJson stats.blocks), ("instructions", Json.arr blocks)]
  IO.FS.writeFile reportPath (report.compress ++ "\n")
  IO.println s!"profile completed={complete}, transitions={count}"
  return 0
