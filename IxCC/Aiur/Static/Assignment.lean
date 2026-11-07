import IxCC.Aiur.Static.Program
import IxCC.Aiur.Check
import IxCC.Aiur.WellFounded

/-! Check a static assignment on every exact provider dependency.
Ranks are ordinary witness data. Counter observations and modes are fixed
by the checked program; no per-edge counter or mode choice is accepted. -/

namespace IxCC.Aiur.Static

open _root_.Aiur.Bytecode (Toplevel)

structure AssignmentLimits where
  maxPairs : Nat := 65536
  maxRank : Nat := 2 ^ 48 - 1
  deriving Repr

inductive AssignmentError where
  | traceLimit
  | dependencyLimit
  | rankCount
  | rankLimit
  | providerBinding
  | dependencies
  deriving DecidableEq, Repr

def rankedOrder (order : Nat) : Bool := order % 2 == 0

/-- Zero-weight parents have no execution premise and cannot be children in
`Requires`. Assign them order zero, below every admitted nonzero provider. -/
def facts (plans : Array FunctionPlan) (rank : Nat) (row : Row) : RowFacts :=
  if row.multiplicity = 0 then ⟨0, 0, 0⟩
  else match row.provides with
    | .function function inputs outputs =>
        match plans[function]? with
        | some plan => ⟨plan.order, plan.counterValue inputs outputs, rank⟩
        | none => ⟨0, 0, 0⟩
    | .memory .. | .gadget .. => ⟨2 * plans.size + 1, 0, 0⟩

def traceFacts (plans : Array FunctionPlan) (ranks : Array Nat) (trace : Trace) :
    trace.RowId → RowFacts :=
  fun id => facts plans (ranks[id.val]?.getD 0) (trace.row id)

/-- Constrained providers bind to the actual function's arity and metadata.
Missing plans cannot be licensed by the total fallback in `facts`. -/
def providerBound (plans : Array FunctionPlan) (row : Row) : Bool :=
  if row.active = true ∧ row.multiplicity ≠ 0 then
    match row.provides with
    | .function function inputs outputs =>
        match plans[function]? with
        | some plan => plan.constrained && inputs.length == plan.inputSize &&
            plan.component.order < plans.size && plan.counterBound inputs outputs
        | none => false
    | .memory .. | .gadget .. => row.demands.isEmpty
  else true

def Advances (parent child : RowFacts) : Prop :=
  parent.order < child.order ∨
    (parent.order = child.order ∧
      if rankedOrder parent.order then parent.rank < child.rank
      else child.counter = parent.counter + 1)

instance (parent child : RowFacts) : Decidable (Advances parent child) :=
  inferInstanceAs (Decidable (_ ∨ _))

def checkDependencies (trace : Trace) (assignment : trace.RowId → RowFacts) : Bool :=
  (List.finRange trace.rows.length).all fun parent =>
    (List.finRange trace.rows.length).all fun child =>
      decide (trace.Requires child parent → Advances (assignment parent) (assignment child))

theorem checkDependencies_sound (trace : Trace) (assignment : trace.RowId → RowFacts)
    (checked : checkDependencies trace assignment = true) :
    ∀ child parent, trace.Requires child parent → Advances (assignment parent) (assignment child) := by
  intro child parent required
  have parents := List.all_eq_true.mp checked parent (by simp)
  exact of_decide_eq_true (List.all_eq_true.mp parents child (by simp)) required

structure Assignment {toplevel : Toplevel} (program : Program toplevel) (trace : Trace) : Type where
  ranks : Array Nat
  rankCount : ranks.size = trace.rows.length
  bindings : trace.rows.all (providerBound program.plans) = true
  dependencies : checkDependencies trace (traceFacts program.plans ranks trace) = true

def Assignment.certificate {toplevel : Toplevel} {program : Program toplevel} {trace : Trace}
    (assignment : Assignment program trace) : StaticCertificate trace.RowId trace.Requires where
  facts := traceFacts program.plans assignment.ranks trace
  ranked := rankedOrder
  edge := checkDependencies_sound trace _ assignment.dependencies

/-- Structural and matrix budgets are checked before enumerating pairs.
No missing rank, guessed column, or unbound function is silently accepted. -/
def checkAssignment {toplevel : Toplevel} (program : Program toplevel) (trace : Trace)
    (traceLimits : Trace.Limits) (limits : AssignmentLimits) (ranks : Array Nat) :
    Except AssignmentError (Assignment program trace) :=
  if !trace.withinLimits traceLimits then .error .traceLimit
  else if trace.rows.length * trace.rows.length > limits.maxPairs then .error .dependencyLimit
  else if count : ranks.size = trace.rows.length then
    if !(ranks.all (fun rank => rank ≤ limits.maxRank)) then .error .rankLimit
    else if bindings : trace.rows.all (providerBound program.plans) = true then
      if dependencies : checkDependencies trace (traceFacts program.plans ranks trace) = true then
        .ok ⟨ranks, count, bindings, dependencies⟩
      else .error .dependencies
    else .error .providerBinding
  else .error .rankCount

theorem Assignment.wellFounded {toplevel : Toplevel} {program : Program toplevel} {trace : Trace}
    (assignment : Assignment program trace) (bound : trace.WithinCharacteristic) :
    WellFounded trace.Requires := trace.static_wellFounded bound assignment.certificate

end IxCC.Aiur.Static
