import Compilatrix.Aiur.Balance
import Compilatrix.Aiur.Memory

/-! Bounded executable checking of logical trace facts. This checks a supplied
logical trace, not a STARK proof or its AIR extraction. Acyclicity is a
separate certificate consumed by the derivation interface. -/

namespace Compilatrix.Aiur.Trace

open _root_.Aiur (G gSize)

def mentioned (trace : Trace) : List Message :=
  trace.requirements ++ trace.rows.map Row.provides

def checkActivity (trace : Trace) : Bool :=
  trace.rows.all fun row => decide (row.multiplicity = 0 ∨ row.active = true)

def checkBalance (trace : Trace) : Bool :=
  trace.mentioned.all fun message =>
    decide (G.ofNat (trace.demandCount message) = providerSum message trace.rows)

theorem checkActivity_sound (trace : Trace) (checked : trace.checkActivity = true) :
    trace.Activity := by
  intro row member nonzero
  have h := List.all_eq_true.mp checked row member
  have h : row.multiplicity = 0 ∨ row.active = true := of_decide_eq_true h
  exact h.resolve_left nonzero

theorem checkBalance_sound (trace : Trace) (checked : trace.checkBalance = true) :
    trace.Balanced := by
  intro message
  by_cases member : message ∈ trace.mentioned
  · exact of_decide_eq_true (List.all_eq_true.mp checked message member)
  · have absent : message ∉ trace.requirements :=
      fun h => member (List.mem_append_left _ h)
    have providers : providerSum message trace.rows = 0 := by
      apply providerSum_zero
      intro row rowMember equal
      exact False.elim (member (List.mem_append_right _ (List.mem_map.mpr ⟨row, rowMember, equal⟩)))
    have count : trace.demandCount message = 0 := List.count_eq_zero_of_not_mem absent
    rw [count, providers]
    rfl

structure Limits where
  maxRows : Nat := 256
  maxUnitSlots : Nat := 1024
  maxMessageFields : Nat := 64
  deriving Repr

def messageFields : Message → Nat
  | .function _ inputs outputs => inputs.length + outputs.length
  | .memory _ _ values => values.length + 1
  | .gadget _ values => values.length

def withinLimits (trace : Trace) (limits : Limits) : Bool :=
  trace.rows.length ≤ limits.maxRows &&
  trace.rows.length + trace.publicClaims.length +
    (trace.rows.map (fun row => row.demands.length)).sum ≤ limits.maxUnitSlots &&
  trace.mentioned.all (fun message => messageFields message ≤ limits.maxMessageFields) &&
  trace.rows.all (fun row => row.demands.all (fun message => messageFields message ≤ limits.maxMessageFields))

inductive Error where
  | resourceLimit
  | characteristicBound
  | inactiveProvider
  | unbalanced
  | inconsistentMemory
  deriving DecidableEq, Repr

structure Validated (trace : Trace) : Type where
  activity : trace.Activity
  balanced : trace.Balanced
  bound : trace.WithinCharacteristic
  memory : Memory.Coherent (Memory.cells trace)

def validate (trace : Trace) (limits : Limits := {}) : Except Error (Validated trace) := do
  if !trace.withinLimits limits then throw .resourceLimit
  if bound : trace.WithinCharacteristic then
    if activity : trace.checkActivity = true then
      if balance : trace.checkBalance = true then
        if memory : Memory.check trace = true then
          return ⟨trace.checkActivity_sound activity, trace.checkBalance_sound balance, bound,
            Memory.check_sound trace memory⟩
        else throw .inconsistentMemory
      else throw .unbalanced
    else throw .inactiveProvider
  else throw .characteristicBound

end Compilatrix.Aiur.Trace
