module
public import Ix.Ixby.Eval

/-! The current IXBF execution profile. All logical primitives and scalar
representations belong to one language revision. Loader byte/depth budgets
restrict admission and are not part of the committed semantic parameters. -/

public section
@[expose] section

namespace Ix.Ixby

structure Profile where
  limits : Limits := {}
  programBytes : Nat := 67108864
  valueBytes : Nat := 67108864
  valueDepth : Nat := 1024
  maxSteps : Nat := 1000000
  deriving BEq, Repr, Inhabited

inductive ProfileError where
  | reference (error : Error)
  | configuration
  | steps
  | depth
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The ten semantic capacities in their canonical IXBF/IXFP order. -/
def Profile.parameters (profile : Profile) : Array Nat :=
  let l := profile.limits
  #[l.functions, l.constructors, l.blocks, l.locals, l.operands, l.continuations,
    l.inputNodes, l.natBits, l.stringBytes, l.byteArrayBytes]

def Profile.validate (profile : Profile) : Except ProfileError Unit := do
  unless profile.parameters.all (· < 2 ^ 128) && profile.maxSteps < 2 ^ 64 do
    throw .configuration

def Profile.validateProgram (profile : Profile) (program : Program) :
    Except ProfileError Unit := do
  profile.validate
  Ix.Ixby.validateProgram profile.limits program |>.mapError .reference

/-- A shared work list carries each node's remaining depth. Neither the node
budget nor the depth budget resets when traversing siblings. -/
def Profile.valuesSupported (profile : Profile) : Nat → List (Value × Nat) → Except ProfileError Unit
  | _, [] => .ok ()
  | 0, _ :: _ => .error (.reference (.limit .inputNodes))
  | fuel + 1, (value, depth) :: rest => do
    let nextDepth ← match depth with
      | 0 => throw .depth
      | d + 1 => pure d
    let children ← match value with
      | .scalar _ | .byteBuilder _ => pure #[]
      | .ctor _ fields | .pap _ fields | .array fields => pure fields
      | .erased => pure #[]
    profile.valuesSupported fuel ((children.toList.map (·, nextDepth)) ++ rest)

def Profile.validateValues (profile : Profile) (program : Program) (values : Array Value) :
    Except ProfileError Unit := do
  profile.validate
  validateInputValues profile.limits program profile.limits.inputNodes values.toList
    |>.mapError .reference
  profile.valuesSupported profile.limits.inputNodes (values.toList.map (·, profile.valueDepth))

/-- The profiled reference boundary additionally admits the output value.
Wire byte-size limits are enforced by the codecs; this is not byte execution. -/
def Profile.execute (profile : Profile) (program : Program) (input : Array Value) (fuel : Nat) :
    Except ProfileError Value := do
  profile.validateProgram program
  profile.validateValues program input
  if fuel > profile.maxSteps then throw .steps
  let output ← Ix.Ixby.execute profile.limits program input fuel |>.mapError .reference
  profile.validateValues program #[output]
  return output

/-- Profile admission only restricts execution; it does not replace the
functional machine's successful-execution meaning. -/
theorem Profile.execute_refines {profile : Profile} {program : Program}
    {input : Array Value} {fuel : Nat} {output : Value}
    (success : profile.execute program input fuel = .ok output) :
    Ix.Ixby.execute profile.limits program input fuel = .ok output := by
  unfold Profile.execute at success
  simp only [Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure] at success
  cases admitted : profile.validateProgram program with
  | error error => simp [admitted] at success
  | ok _ =>
    cases inputs : profile.validateValues program input with
    | error error => simp [admitted, inputs] at success
    | ok _ =>
      by_cases steps : fuel > profile.maxSteps
      · simp [admitted, inputs, steps] at success
      · cases evaluated : Ix.Ixby.execute profile.limits program input fuel with
        | error error => simp [admitted, inputs, steps, evaluated] at success
        | ok value =>
          cases outputs : profile.validateValues program #[value] with
          | error error => simp [admitted, inputs, steps, evaluated, outputs] at success
          | ok _ =>
            simp [admitted, inputs, steps, evaluated, outputs] at success
            exact congrArg Except.ok success

end Ix.Ixby
