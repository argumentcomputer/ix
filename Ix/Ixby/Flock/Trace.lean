module
public import Ix.Ixby.Flock.Control
public import Ix.Ixby.Codec

/-!
# Finite control traces, exact fuel and byte execution

Every active transition, including empty-stack return, consumes one fuel.
Only a genuine terminal result can enter absorbing, fuel-preserving padding.
Finite traces of the decoded control rules therefore imply the reference run
and, with exact admitted codec endpoints, `Codec.Evaluates`.

This is NOT a claim that the Rust Flock tables already enforce all the rules.
The native constraint-to-decoded-rule theorem is still required, as are the
constrained codec and initial-state connections. No native evaluator or
proof-acceptance bit is assumed in these theorems.
-/

public section
@[expose] section

namespace Ix.Ixby.FlockBackend.ControlModel

private theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem except_map_ok {ε α β : Type} (a : α) (f : α → β) :
    f <$> (Except.ok a : Except ε α) = .ok (f a) := rfl

attribute [local simp] except_bind_ok except_map_ok

inductive Snapshot where
  | active (remaining : Nat) (machine : Machine)
  | halted (remaining : Nat) (value : Value)
  deriving BEq, Repr, Inhabited

def Snapshot.remaining : Snapshot → Nat
  | .active remaining _ | .halted remaining _ => remaining

def Snapshot.result (limits : Limits) (program : Program) : Snapshot → Except Error Value
  | .active remaining machine => run limits program remaining machine.decode
  | .halted _ value => .ok value

inductive TimedStep (limits : Limits) (program : Program) : Snapshot → Snapshot → Prop where
  | next {remaining : Nat} {before after : Machine}
      (transition : Step limits program before (.next after)) :
      TimedStep limits program (.active (remaining + 1) before) (.active remaining after)
  | halt {remaining : Nat} {before : Machine} {value : Value}
      (transition : Step limits program before (.halted value)) :
      TimedStep limits program (.active (remaining + 1) before) (.halted remaining value)
  | pad (remaining : Nat) (value : Value) :
      TimedStep limits program (.halted remaining value) (.halted remaining value)

theorem TimedStep.result {limits : Limits} {program : Program} {before after : Snapshot}
    (transition : TimedStep limits program before after) :
    before.result limits program = after.result limits program := by
  cases transition with
  | next transition => simp [Snapshot.result, run, transition.reference, Outcome.decode]
  | halt transition => simp [Snapshot.result, run, transition.reference, Outcome.decode]
  | pad => rfl

theorem TimedStep.active_consumes_one {limits : Limits} {program : Program}
    {remaining : Nat} {machine : Machine} {after : Snapshot}
    (transition : TimedStep limits program (.active remaining machine) after) :
    remaining = after.remaining + 1 := by
  cases transition <;> rfl

theorem TimedStep.zero_fuel_rejects {limits : Limits} {program : Program}
    {machine : Machine} {after : Snapshot} :
    ¬ TimedStep limits program (.active 0 machine) after := by
  intro transition
  have := transition.active_consumes_one
  omega

theorem TimedStep.halted_freezes {limits : Limits} {program : Program}
    {remaining : Nat} {value : Value} {after : Snapshot}
    (transition : TimedStep limits program (.halted remaining value) after) :
    after = .halted remaining value := by
  cases transition
  rfl

/-- Exactly the fixed unrolled row count; padding rows count here even though
they consume no logical fuel. The empty trace cannot turn an active state
into a halted state. -/
inductive Trace (limits : Limits) (program : Program) : Nat → Snapshot → Snapshot → Prop where
  | nil (state : Snapshot) : Trace limits program 0 state state
  | cons {rows : Nat} {first second last : Snapshot}
      (transition : TimedStep limits program first second)
      (rest : Trace limits program rows second last) :
      Trace limits program (rows + 1) first last

theorem Trace.result {limits : Limits} {program : Program} {rows : Nat}
    {before after : Snapshot} (trace : Trace limits program rows before after) :
    before.result limits program = after.result limits program := by
  induction trace with
  | nil => rfl
  | cons transition _ ih => exact transition.result.trans ih

theorem Trace.reference_run {limits : Limits} {program : Program} {rows fuel remaining : Nat}
    {machine : Machine} {value : Value}
    (trace : Trace limits program rows (.active fuel machine) (.halted remaining value)) :
    run limits program fuel machine.decode = .ok value := trace.result

theorem Trace.reference_execution {limits : Limits} {program : Program}
    {input : Array Value} {rows fuel remaining : Nat} {machine : Machine} {value : Value}
    (initial : initialState limits program input = .ok machine.decode)
    (trace : Trace limits program rows (.active fuel machine) (.halted remaining value)) :
    Ix.Ixby.execute limits program input fuel = .ok value := by
  simpa [Ix.Ixby.execute, initial] using trace.reference_run

private theorem input_admission {profile : Profile} {program : Program} {input : Array Value}
    {bytes : Codec.Bytes} (encoded : Codec.encodeInput profile program input = .ok bytes) :
    profile.validateValues program input = .ok () := by
  unfold Codec.encodeInput Codec.validateInput at encoded
  simp only [Bind.bind, Except.bind, Except.mapError] at encoded
  cases hp : profile.validateProgram program with
  | error e => simp [hp] at encoded
  | ok _ =>
    cases hf : program.getFunction program.entry with
    | error e => simp [hp, hf] at encoded
    | ok function =>
      by_cases ha : input.size != function.arity
      · simp [hp, hf, ha] at encoded
      · cases hv : profile.validateValues program input with
        | error e => simp [hp, hf, ha, hv] at encoded
        | ok result => cases result; rfl

private theorem output_admission {profile : Profile} {program : Program} {value : Value}
    {bytes : Codec.Bytes} (encoded : Codec.encodeOutput profile program value = .ok bytes) :
    profile.validateProgram program = .ok () ∧
      profile.validateValues program #[value] = .ok () := by
  unfold Codec.encodeOutput at encoded
  simp only [Bind.bind, Except.bind, Except.mapError] at encoded
  cases hp : profile.validateProgram program with
  | error e => simp [hp] at encoded
  | ok result =>
    cases result
    cases hv : profile.validateValues program #[value] with
    | error e => simp [hp, hv] at encoded
    | ok result => cases result; exact ⟨rfl, rfl⟩

/-- Exact canonical byte endpoints plus a finite admitted control trace imply
the existing byte execution proposition. Decoder equations concern the entire
image/input, not just visited instructions. Output admission is recovered
from the encoder equation, and fuel must obey the semantic profile. -/
theorem Trace.byte_execution {profile : Profile} {programBytes inputBytes outputBytes : Codec.Bytes}
    {program : Codec.Decoded (Codec.encodeProgram profile) programBytes}
    {input : Codec.Decoded (Codec.encodeInput profile program.value) inputBytes}
    {rows fuel remaining : Nat} {machine : Machine} {value : Value}
    (decodedProgram : Codec.decodeProgram profile programBytes = .ok program)
    (decodedInput : Codec.decodeInput profile program.value inputBytes = .ok input)
    (initial : initialState profile.limits program.value input.value = .ok machine.decode)
    (trace : Trace profile.limits program.value rows (.active fuel machine) (.halted remaining value))
    (fuelBound : fuel ≤ profile.maxSteps)
    (encodedOutput : Codec.encodeOutput profile program.value value = .ok outputBytes) :
    Codec.Evaluates profile programBytes inputBytes outputBytes := by
  have hInput := input_admission input.canonical
  obtain ⟨hProgram, hOutput⟩ := output_admission encodedOutput
  have hRun := trace.reference_execution initial
  have hProfile : profile.execute program.value input.value fuel = .ok value := by
    simp [Profile.execute, hProgram, hInput, Nat.not_lt.mpr fuelBound, hRun,
      hOutput, Except.mapError]
  refine ⟨fuel, ?_⟩
  simp only [Codec.execute, decodedProgram, except_bind_ok, decodedInput]
  split
  · rename_i error rejected
    rw [hProfile] at rejected
    contradiction
  · rename_i output evaluated
    have same : output = value := Except.ok.inj (evaluated.symm.trans hProfile)
    subst output
    split
    · rename_i error rejected
      rw [encodedOutput] at rejected
      contradiction
    · rename_i bytes encoded
      have same : bytes = outputBytes := Except.ok.inj (encoded.symm.trans encodedOutput)
      subst bytes
      rfl

end Ix.Ixby.FlockBackend.ControlModel
