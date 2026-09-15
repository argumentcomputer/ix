module
import Tests.Ixby.Common
import Ix.Ixby.Flock.Trace

namespace Tests.Ixby.Flock.Control

open Ix.Ixby
open Ix.Ixby.FlockBackend.ControlModel

private def profile : Profile := {
  limits := {
    functions := 2
    constructors := 0
    blocks := 2
    locals := 3
    operands := 2
    continuations := 2
    inputNodes := 8
    natBits := 0
    stringBytes := 0
    byteArrayBytes := 0 }
  programBytes := 256
  valueBytes := 64
  valueDepth := 1
  maxSteps := 8 }

private def word (value : Nat) : Value := .scalar (.word32 value.toUInt32)

private def program : Program := { functions := #[
  { arity := 1, blocks := #[
    ⟨1, .letOp (.call 1 [.local 0]) 1⟩,
    ⟨2, .ret (.local 1)⟩] },
  { arity := 1, blocks := #[
    ⟨1, .letOp (.primitive .word32Add [.local 0, .literal (.word32 1)]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }] }

private def caller : Frame := ⟨0, 0, #[word 41]⟩
private def saved : Frame := { caller with block := 1 }
private def callee : Frame := ⟨1, 0, #[word 41]⟩
private def bound : Frame := append callee 1 (word 42)
private def resumed : Frame := append saved 1 (word 42)

private def entry : Entry profile.limits program 1 #[word 41] := {
  function := { arity := 1, blocks := #[
    ⟨1, .letOp (.primitive .word32Add [.local 0, .literal (.word32 1)]) 1⟩,
    ⟨2, .ret (.local 1)⟩] }
  found := rfl
  arity := rfl
  block := ⟨1, .letOp (.primitive .word32Add [.local 0, .literal (.word32 1)]) 1⟩
  checked := rfl }

private theorem call_step : Step profile.limits program ⟨.eval caller, #[]⟩
    (.next ⟨.eval callee, #[saved]⟩) :=
  .call (op := .call 1 [.local 0]) (declared := 1) rfl (.call rfl) entry (by decide)

private theorem bind_step : Step profile.limits program ⟨.eval callee, #[saved]⟩
    (.next ⟨.eval bound, #[saved]⟩) :=
  .bind (op := .primitive .word32Add [.local 0, .literal (.word32 1)])
    (declared := 1) (next := ⟨2, .ret (.local 1)⟩) rfl
    (.primitive (args := [word 41, word 1]) rfl rfl) rfl

private theorem callee_ret_step : Step profile.limits program ⟨.eval bound, #[saved]⟩
    (.next ⟨.ret (word 42), #[saved]⟩) :=
  .ret (operand := .local 1) (declared := 2) rfl rfl

private theorem resume_step : Step profile.limits program ⟨.ret (word 42), #[saved]⟩
    (.next ⟨.eval resumed, #[]⟩) :=
  .resume (saved := saved) (rest := #[]) (value := word 42)
    (next := ⟨2, .ret (.local 1)⟩) rfl

private theorem caller_ret_step : Step profile.limits program ⟨.eval resumed, #[]⟩
    (.next ⟨.ret (word 42), #[]⟩) :=
  .ret (operand := .local 1) (declared := 2) rfl rfl

private theorem six_steps : Trace profile.limits program 6
    (.active 6 ⟨.eval caller, #[]⟩) (.halted 0 (word 42)) :=
  .cons (.next call_step)
    (.cons (.next bind_step)
      (.cons (.next callee_ret_step)
        (.cons (.next resume_step)
          (.cons (.next caller_ret_step)
            (.cons (.halt (.halt (word 42))) (.nil _))))))

-- A proved trace of actual instructions, not a premise asserting that a
-- native execution was sound. Both the returned value and exact fuel matter.
example : run profile.limits program 6 (Machine.mk (.eval caller) #[]).decode =
    .ok (word 42) := six_steps.reference_run

example : Ix.Ixby.execute profile.limits program #[word 41] 6 = .ok (word 42) :=
  six_steps.reference_execution (by
    simp only [Machine.decode, ActiveControl.decode, Array.map_empty]
    rfl)

example : ¬ TimedStep profile.limits program (.active 0 ⟨.ret (word 42), #[]⟩)
    (.halted 0 (word 42)) := TimedStep.zero_fuel_rejects

example (after : Snapshot)
    (transition : TimedStep profile.limits program (.halted 2 (word 42)) after) :
    after = .halted 2 (word 42) := transition.halted_freezes

-- A forged resolved return cannot inhabit the decoded relation for the real
-- return instruction. This also exercises the whole Step.reference theorem.
example (value : Value)
    (forged : Step profile.limits program ⟨.eval resumed, #[]⟩
      (.next ⟨.ret value, #[]⟩)) : value = word 42 := by
  have same := Except.ok.inj (caller_ret_step.reference.symm.trans forged.reference)
  exact (Ix.Ixby.Control.ret.inj (congrArg State.control (Transition.next.inj same))).symm

private def bytesRun : Except String Bool := do
  let code ← (Codec.encodeProgram profile program).mapError (fun e => reprStr e)
  let input ← (Codec.encodeInput profile program #[word 41]).mapError (fun e => reprStr e)
  let output ← (Codec.encodeOutput profile program (word 42)).mapError (fun e => reprStr e)
  let actual ← (Codec.execute profile code input 6).mapError (fun e => reprStr e)
  return actual.outputBytes == output

private def checks : IO (List Check) := do
  let start := (Machine.mk (.eval caller) #[]).decode
  let sameResult {ε α : Type} [BEq ε] [BEq α] (a b : Except ε α) :=
    match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false
  return [
    ("ordered continuation bank decodes oldest first",
      (Machine.mk (.ret (word 42)) #[caller, callee]).decode.continuation ==
        #[.resume caller, .resume callee]),
    ("append preserves old locals and target", resumed == ⟨0, 1, #[word 41, word 42]⟩),
    ("call then primitive then both returns uses six transitions",
      sameResult (Ix.Ixby.execute profile.limits program #[word 41] 6) (.ok (word 42))),
    ("five transitions exhaust before terminal return",
      sameResult (run profile.limits program 5 start) (.error .outOfFuel)),
    ("active zero fuel is not a terminal result",
      sameResult ((Snapshot.active 0 ⟨.ret (word 42), #[]⟩).result profile.limits program)
        (.error .outOfFuel)),
    ("halting padding retains its returned value",
      sameResult ((Snapshot.halted 0 (word 42)).result profile.limits program) (.ok (word 42))),
    ("extra admitted fuel preserves the reference result",
      sameResult (profile.execute program #[word 41] 8) (.ok (word 42))),
    ("fuel beyond the profile is rejected",
      sameResult (profile.execute program #[word 41] 9) (.error .steps)),
    ("canonical byte execution agrees with the proved control example", bytesRun.toOption == some true)
  ]

public def suite : IO UInt32 := runChecks "ixby-flock-control" checks

end Tests.Ixby.Flock.Control
