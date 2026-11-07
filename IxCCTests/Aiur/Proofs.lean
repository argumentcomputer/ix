import IxCCTests.Aiur.Fixtures

namespace IxCCTests.Aiur

open IxCC.Aiur

def accepted (trace : Trace) (success : trace.validate.isOk = true) : Trace.Validated trace :=
  match result : trace.validate with
  | .ok checked => checked
  | .error _ => by simp [result, Except.isOk, Except.toBool] at success

theorem mixed_derives : mixed.Derivation (mixedMessage 0) :=
  (accepted mixed (by decide)).public_derivation mixedStatic (by decide)

theorem memory_derives : witnessMemory.Derivation (memoryMessage 1 7 42) := by
  have checked := accepted witnessMemory (by decide)
  have result := witnessMemory.row_derivation checked.activity checked.balanced checked.bound
    (witnessMemory.static_wellFounded checked.bound memoryStatic) ⟨1, by decide⟩ (by decide) (by decide)
  exact result

theorem memory_at_seven : Memory.heap (Memory.cells witnessMemory) 1 7 = some [42] :=
  (accepted witnessMemory (by decide)).memory_agrees memory_derives

/-- The attack passes balance/activity/heap checks but cannot obtain any
static certificate, regardless of the proposed component, counter, or rank. -/
theorem selfCall_no_static (certificate : StaticCertificate selfCall.RowId selfCall.Requires) : False :=
  certificate.noShortCycle (fun _ => ⟨0, by decide⟩) 1 (by decide) (by decide)
    ⟨fun _ _ => by dsimp only; decide, rfl⟩

theorem mutualCall_no_static (certificate : StaticCertificate mutualCall.RowId mutualCall.Requires) : False := by
  let walk : Nat → mutualCall.RowId := fun index => ⟨index % 2, Nat.mod_lt _ (by decide)⟩
  apply certificate.noShortCycle walk 2 (by decide) (by decide)
  constructor
  · intro index bounded
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> decide
  · decide

end IxCCTests.Aiur
