import Compilatrix.Aiur.CounterAnalysis.Registers

namespace Compilatrix.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode
open OracleEval (Values)

def InputCalls (self column : Nat) (step : G) (inputs : Array G) (demands : List Call) : Prop :=
  ∀ call ∈ demands, call.function = self →
    ∃ parent child, inputs[column]? = some parent ∧ call.inputs[column]? = some child ∧ child = parent + step

def OutputCalls (self column : Nat) (marker : Option Nat) (values : Array G) (demands : List Call) : Prop :=
  match marker with
  | none => ∀ call ∈ demands, call.function ≠ self
  | some index => ∃ value, values[index]? = some value ∧
      ∀ call ∈ demands, call.function = self → call.outputs[column]? = some value

def CallInvariant (self : Nat) (candidate : UnitCounter.Certificate) (inputs : Array G)
    (marker : Option Nat) (values : Array G) (demands : List Call) : Prop :=
  match candidate.mode with
  | .input => InputCalls self candidate.column candidate.step inputs demands
  | .output => OutputCalls self candidate.column marker values demands

structure Invariant (function : Nat) (candidate : UnitCounter.Certificate) (inputs : Array G)
    (abstractState : UnitCounter.State) (state : OracleEval.State) : Prop where
  registers : Registers abstractState.values state.values
  inputsPreserved : Extends inputs state.values
  callsSound : CallInvariant function candidate inputs abstractState.recursiveOutput state.values (calls state.demandsRev)

theorem CallInvariant.extend {self : Nat} {candidate : UnitCounter.Certificate} {inputs before after : Array G}
    {marker : Option Nat} {demands : List Call} (preserves : Extends before after)
    (sound : CallInvariant self candidate inputs marker before demands) :
    CallInvariant self candidate inputs marker after demands := by
  cases candidate with | mk mode column step =>
    cases mode with
    | input => exact sound
    | output =>
      cases marker with
      | none => exact sound
      | some index =>
        obtain ⟨value, read, allCalls⟩ := sound
        exact ⟨value, preserves _ _ read, allCalls⟩

theorem CallInvariant.nonself {self : Nat} {candidate : UnitCounter.Certificate} {inputs values : Array G}
    {marker : Option Nat} {demands : List Call} {call : Call} (different : call.function ≠ self)
    (sound : CallInvariant self candidate inputs marker values demands) :
    CallInvariant self candidate inputs marker values (call :: demands) := by
  cases candidate with | mk mode column step =>
    cases mode with
    | input =>
      intro current member same
      rcases List.mem_cons.mp member with rfl | member
      · exact False.elim (different same)
      · exact sound current member same
    | output =>
      cases marker with
      | none =>
        intro current member
        rcases List.mem_cons.mp member with rfl | member
        · exact different
        · exact sound current member
      | some index =>
        obtain ⟨value, read, allCalls⟩ := sound
        refine ⟨value, read, ?_⟩
        intro current member same
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (different same)
        · exact allCalls current member same

theorem Invariant.preserve {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore abstractAfter : UnitCounter.State} {before after : OracleEval.State}
    (sound : Invariant self candidate inputs abstractBefore before)
    (registers : Registers abstractAfter.values after.values) (preserves : Extends before.values after.values)
    (marker : abstractAfter.recursiveOutput = abstractBefore.recursiveOutput)
    (sameCalls : calls after.demandsRev = calls before.demandsRev) :
    Invariant self candidate inputs abstractAfter after := by
  refine ⟨registers, sound.inputsPreserved.trans preserves, ?_⟩
  rw [marker, sameCalls]
  exact sound.callsSound.extend preserves

theorem Invariant.push {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore : UnitCounter.State} {before after : OracleEval.State}
    (sound : Invariant self candidate inputs abstractBefore before) (expression : Option UnitCounter.Affine) (value : G)
    (meaning : ValueSound before.values expression value)
    (values : after.values = before.values ++ #[value])
    (sameCalls : calls after.demandsRev = calls before.demandsRev) :
    Invariant self candidate inputs { abstractBefore with values := abstractBefore.values.push expression } after := by
  refine sound.preserve ?_ ?_ rfl sameCalls
  · simpa only [values, Array.push_eq_append] using sound.registers.push expression value meaning
  · rw [values]; exact extends_append _ _

theorem Invariant.unknown {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore : UnitCounter.State} {before after : OracleEval.State}
    (sound : Invariant self candidate inputs abstractBefore before) (outputs : Values) (count : Nat)
    (size : outputs.length = count) (values : after.values = before.values ++ outputs.toArray)
    (sameCalls : calls after.demandsRev = calls before.demandsRev) :
    Invariant self candidate inputs
      { abstractBefore with values := abstractBefore.values ++ Array.replicate count none } after := by
  refine sound.preserve ?_ ?_ rfl sameCalls
  · simpa [values, size] using sound.registers.unknown (outputs := outputs.toArray)
  · rw [values]; exact extends_append _ _

theorem Invariant.initial (self : Nat) (candidate : UnitCounter.Certificate) (inputs : Values)
    (replies : List Values) (remainingFields : Nat) :
    Invariant self candidate inputs.toArray
      { values := (Array.range inputs.length).map (some ∘ UnitCounter.affVar) }
      { values := inputs.toArray, replies, remainingFields } := by
  refine ⟨by simpa using Registers.initial inputs.toArray, Extends.refl _, ?_⟩
  cases candidate with | mk mode column step =>
    cases mode <;> simp [CallInvariant, InputCalls, OutputCalls, calls]

end Compilatrix.Aiur.CounterAnalysis
