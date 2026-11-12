import IxCC.Cfg.Rc.Proof.Check
import IxCC.Cfg.Rc.Proof.Scoped
import IxCC.Own.Plain.Proof.Owned.Program
import IxCC.Own.Plain.Proof.OwnedAccepts

/-! # What the program gate says about the ownership code (heap stage 2)

The gate runs the ownership checker (`Cfg.Rc.checkProgram`'s Boolean is `Own.Plain.checkOwned`):
the source domain, the Boolean pins, and for every numbered function a body in the map that
erases to the source body and that the checker accepts from the function's parameters. -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc

/-- The program gate admits only maps the ownership checker accepts. -/
theorem checkScopedProgram_checkOwned {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : checkScopedProgram F bodies P = true) : Own.Plain.checkOwned F bodies = true :=
  (checkProgram_parts (checkScopedProgram_parts h).1).1

/-- The checker's parts, read from the program gate. -/
theorem checkScopedProgram_ownedParts {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program} (h : checkScopedProgram F bodies P = true) :
    Own.Plain.programDomain F = true ∧ Own.Plain.checkBoolPins F = true ∧
      Own.Plain.BodiesChecked F bodies := by
  have owned := checkScopedProgram_checkOwned h
  simp only [Own.Plain.checkOwned, Bool.and_eq_true] at owned
  exact ⟨owned.1.1, owned.1.2, Own.Plain.checkMapE_ok (Own.Plain.except_isOk owned.2)⟩

/-- **Nothing the program gate admitted before heap stage 2 is refused now.** Before, the gate's
Boolean was `Own.Plain.checkPlainMap` (the canonical placement, recomputed and compared) where
`checkProgram` now runs the ownership checker; the hypothesis is that gate, word for word with the
checker replaced. Proved from canonical acceptance (`checkPlainMap_checkOwned`). -/
theorem checkScopedProgram_owned {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {P : Program}
    (h : (Own.Plain.checkPlainMap F bodies &&
      (match generate F bodies with
        | none => false
        | some expected => programEq expected P) &&
      programNames F bodies && sourceDense F) = true) :
    checkScopedProgram F bodies P = true := by
  simp only [checkScopedProgram, checkProgram, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨plain, gen⟩, names⟩, dense⟩ := h
  refine ⟨⟨⟨Own.Plain.checkPlainMap_checkOwned plain, ?_⟩, names⟩, dense⟩
  revert gen
  cases generate F bodies <;> exact id

end IxCC.Cfg.Rc
