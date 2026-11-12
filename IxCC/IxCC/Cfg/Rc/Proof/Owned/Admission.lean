import IxCC.Cfg.Rc.Proof.Owned.Activation
import IxCC.Own.Plain.Proof.Owned.Program

/-! # What the program gate says about the ownership code (heap stage 2)

From the program gate: the source domain, the Boolean pins, and for every numbered function a
body in the map that erases to the source body and that the ownership checker accepts from the
function's parameters. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc

/-- The checker's parts, read from the program gate. -/
theorem checkScopedProgram_ownedParts {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : checkScopedProgram F bodies P = true) :
    Own.Plain.programDomain F = true ∧ Own.Plain.checkBoolPins F = true ∧
      Own.Plain.BodiesChecked F bodies := by
  have owned := checkScopedProgram_checkOwned h
  simp only [Own.Plain.checkOwned, Bool.and_eq_true] at owned
  exact ⟨owned.1.1, owned.1.2, Own.Plain.checkMapE_ok (Own.Plain.except_isOk owned.2)⟩

end IxCC.Cfg.Rc
