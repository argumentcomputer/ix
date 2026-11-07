import IxCC.Aiur.CounterAnalysis.Invariant

namespace IxCC.Aiur.CounterAnalysis

open _root_.IxCC.Vendor.Aiur (G)
open _root_.IxCC.Vendor.Aiur.Bytecode
open OracleEval (Values)

theorem Invariant.nonselfCall {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore : UnitCounter.State} {before after : OracleEval.State}
    (sound : Invariant self candidate inputs abstractBefore before) (function : Nat) (arguments outputs : Values) (count : Nat)
    (different : function ≠ self) (size : outputs.length = count)
    (values : after.values = before.values ++ outputs.toArray)
    (newCall : calls after.demandsRev = ⟨function, arguments, outputs⟩ :: calls before.demandsRev) :
    Invariant self candidate inputs
      { abstractBefore with values := abstractBefore.values ++ Array.replicate count none } after := by
  have preserves : Extends before.values after.values := by rw [values]; exact extends_append _ _
  refine ⟨by simpa [values, size] using sound.registers.unknown (outputs := outputs.toArray),
    sound.inputsPreserved.trans preserves, ?_⟩
  rw [newCall]
  exact (sound.callsSound.extend preserves).nonself different

theorem Invariant.inputCall {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore : UnitCounter.State} {before after : OracleEval.State}
    (sound : Invariant self candidate inputs abstractBefore before)
    (mode : candidate.mode = .input) (columnBound : candidate.column < inputs.size)
    (indices : Array Nat) (arguments outputs : Values) (count argument : Nat)
    (selected : indices[candidate.column]? = some argument)
    (known : (abstractBefore.values[argument]?).getD none = some ⟨some candidate.column, candidate.step⟩)
    (reads : Reads before.values indices arguments) (size : outputs.length = count)
    (values : after.values = before.values ++ outputs.toArray)
    (newCall : calls after.demandsRev = ⟨self, arguments, outputs⟩ :: calls before.demandsRev) :
    Invariant self candidate inputs
      { abstractBefore with values := abstractBefore.values ++ Array.replicate count none } after := by
  obtain ⟨child, argumentRead, registerRead⟩ := reads.get selected
  obtain ⟨parent, parentRead, equation⟩ := sound.registers.get registerRead _ known
  have initialRead := Array.getElem?_eq_getElem columnBound
  have preserved := sound.inputsPreserved _ _ initialRead
  have equal : parent = inputs[candidate.column] := Option.some.inj (parentRead.symm.trans preserved)
  have preserves : Extends before.values after.values := by rw [values]; exact extends_append _ _
  refine ⟨by simpa [values, size] using sound.registers.unknown (outputs := outputs.toArray),
    sound.inputsPreserved.trans preserves, ?_⟩
  change CallInvariant self candidate inputs abstractBefore.recursiveOutput after.values (calls after.demandsRev)
  rw [CallInvariant, mode, newCall]
  intro call member same
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨inputs[candidate.column], child, initialRead, argumentRead, equal ▸ equation⟩
  · have old := sound.callsSound
    rw [CallInvariant, mode] at old
    exact old call member same

theorem Invariant.outputCall {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore : UnitCounter.State} {before after : OracleEval.State}
    (sound : Invariant self candidate inputs abstractBefore before)
    (mode : candidate.mode = .output) (noMarker : abstractBefore.recursiveOutput = none)
    (arguments outputs : Values) (count : Nat) (columnBound : candidate.column < count)
    (size : outputs.length = count) (values : after.values = before.values ++ outputs.toArray)
    (newCall : calls after.demandsRev = ⟨self, arguments, outputs⟩ :: calls before.demandsRev) :
    Invariant self candidate inputs
      { values := abstractBefore.values ++ (Array.range count).map (fun index =>
          if index == candidate.column then some (UnitCounter.affVar (abstractBefore.values.size + candidate.column)) else none)
        recursiveOutput := some (abstractBefore.values.size + candidate.column) } after := by
  have preserves : Extends before.values after.values := by rw [values]; exact extends_append _ _
  have bound : candidate.column < outputs.toArray.size := by simpa [size] using columnBound
  have outputRead := Array.getElem?_eq_getElem bound
  have markerRead : after.values[abstractBefore.values.size + candidate.column]? = some outputs.toArray[candidate.column] := by
    rw [values, sound.registers.1, Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact outputRead
  refine ⟨by simpa [values, size] using sound.registers.marker (outputs := outputs.toArray) candidate.column,
    sound.inputsPreserved.trans preserves, ?_⟩
  change CallInvariant self candidate inputs (some _) after.values (calls after.demandsRev)
  rw [CallInvariant, mode, newCall]
  refine ⟨outputs.toArray[candidate.column], markerRead, ?_⟩
  intro call member same
  rcases List.mem_cons.mp member with rfl | member
  · simpa only [List.getElem?_toArray] using outputRead
  · have old := sound.callsSound
    rw [CallInvariant, mode, noMarker] at old
    exact False.elim (old call member same)

end IxCC.Aiur.CounterAnalysis
