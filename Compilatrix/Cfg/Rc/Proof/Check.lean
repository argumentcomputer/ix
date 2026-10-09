import Compilatrix.Cfg.Rc.Check
import Compilatrix.Cfg.Rc.Proof.Bounds
import Compilatrix.Cfg.Rc.Proof.Coverage

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc


theorem mapEq_iff {α : Type} (eq : α → α → Bool)
    (sound : ∀ a b, eq a b = true ↔ a = b) (a b : Src.NatMap α) :
    mapEq eq a b = true ↔ a = b := by
  induction a generalizing b with
  | leaf => cases b <;> simp [mapEq]
  | node v l r il ir =>
    cases b with
    | leaf => simp [mapEq]
    | node w l' r' => cases v <;> cases w <;> simp [mapEq, sound, il, ir, and_assoc]

theorem funEq_iff (a b : Cfg.Fun) : funEq a b = true ↔ a = b := by
  cases a; cases b; simp [funEq, and_assoc]

theorem programEq_iff (a b : Program) : programEq a b = true ↔ a = b := by
  rcases a with ⟨⟨af, az, ae, ac, ⟨an, as, ab, atrue⟩⟩, aa⟩
  rcases b with ⟨⟨bf, bz, be, bc, ⟨bn, bs, bb, btrue⟩⟩, ba⟩
  simp [programEq, mapEq_iff _ funEq_iff, mapEq_iff _ tableEq_iff, and_assoc]

theorem checkProgram_parts {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {candidate : Program} (h : checkProgram F bodies candidate = true) :
    Own.Plain.checkPlainMap F bodies = true ∧ generate F bodies = some candidate := by
  simp only [checkProgram, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  cases hg : generate F bodies with
  | none => simp [hg] at h
  | some expected =>
    have eq : expected = candidate := (programEq_iff ..).mp (by simpa [hg] using h.2)
    simpa [eq]

end Compilatrix.Cfg.Rc
