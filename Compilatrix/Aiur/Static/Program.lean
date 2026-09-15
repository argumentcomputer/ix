import Compilatrix.Aiur.Wire.ComponentCheck
import Compilatrix.Aiur.Static.Counter

/-! Bind static row assignments to the exact checked bytecode metadata.
Counter inference chooses an observation and direction. Its semantic edge
equations are checked on the supplied trace; no analyzer theorem is assumed. -/

namespace Compilatrix.Aiur.Static

open _root_.Aiur (G)
open _root_.Aiur.Bytecode

inductive ProgramError where
  | functionLimit
  | components (reason : String)
  | missingComponent (function : Nat)
  | counterStep (function : Nat)
  deriving DecidableEq, Repr

structure FunctionPlan where
  component : CallComponent
  constrained : Bool
  inputSize : Nat
  counter : Option UnitCounter.Certificate
  deriving Repr

/-- An order number may be reused across ranked and counter functions by
the pinned checker. Separate the two kinds before choosing a global mode. -/
def FunctionPlan.order (plan : FunctionPlan) : Nat :=
  2 * plan.component.order + if plan.component.ranked then 2 else 1

def FunctionPlan.counterValue (plan : FunctionPlan) (inputs outputs : List G) : G :=
  match plan.counter with
  | none => 0
  | some candidate => normalizedCounter candidate inputs outputs

def FunctionPlan.counterBound (plan : FunctionPlan) (inputs outputs : List G) : Bool :=
  match plan.counter with
  | none => true
  | some candidate => (counterObservation candidate inputs outputs).isSome

/-- Only recursive unranked functions need another analyzer invocation.
The component preflight bounds these analyses, including their allocations. -/
def inferPlans (toplevel : Toplevel) : Except ProgramError (Array FunctionPlan) :=
  toplevel.functions.mapIdxM fun index function => do
    let component ← if toplevel.callComponents.isEmpty then
        pure ({ order := 0, ranked := true } : CallComponent)
      else match toplevel.callComponents[index]? with
        | some component => pure component
        | none => throw (.missingComponent index)
    let counter := if !component.ranked && function.constrained &&
        function.body.collectConstrainedCallees.contains index then
      UnitCounter.find? index function
      else none
    if let some candidate := counter then
      if candidate.step != 1 && candidate.step != (0 : G) - 1 then
        throw (.counterStep index)
    return ⟨component, function.constrained, function.layout.inputSize, counter⟩

structure Program (toplevel : Toplevel) : Type where
  limits : Wire.CheckLimits
  components : Wire.ComponentChecked limits toplevel
  functionBound : toplevel.functions.size ≤ limits.maxFunctions
  plans : Array FunctionPlan
  inferred : inferPlans toplevel = .ok plans

def prepareChecked (limits : Wire.CheckLimits) (toplevel : Toplevel)
    (components : Wire.ComponentChecked limits toplevel) : Except ProgramError (Program toplevel) :=
  if bounded : toplevel.functions.size ≤ limits.maxFunctions then
    match inferred : inferPlans toplevel with
    | .error error => .error error
    | .ok plans => .ok ⟨limits, components, bounded, plans, inferred⟩
  else .error .functionLimit

theorem prepareChecked_ok (limits : Wire.CheckLimits) (toplevel : Toplevel)
    (components : Wire.ComponentChecked limits toplevel)
    (bounded : toplevel.functions.size ≤ limits.maxFunctions)
    (plans : Array FunctionPlan) (inferred : inferPlans toplevel = .ok plans) :
    prepareChecked limits toplevel components =
      .ok ⟨limits, components, bounded, plans, inferred⟩ := by
  simp only [prepareChecked, dif_pos bounded]
  split
  next h => rw [inferred] at h; contradiction
  next ps h => cases inferred.symm.trans h; rfl

def prepare (limits : Wire.CheckLimits) (toplevel : Toplevel) :
    Except ProgramError (Program toplevel) := do
  if toplevel.functions.size > limits.maxFunctions then throw .functionLimit
  match Wire.checkComponents limits toplevel with
  | .error reason => throw (.components reason)
  | .ok checked => prepareChecked limits toplevel checked

theorem Program.accepted {toplevel : Toplevel} (program : Program toplevel) :
    Wire.componentsValid toplevel = true := program.components.accepted

end Compilatrix.Aiur.Static
