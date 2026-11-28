import IxCC.Cfg.Rc.Check
import IxCC.Cfg.Rc.Proof.Bounds
import IxCC.Cfg.Rc.Proof.Coverage

set_option autoImplicit false
namespace IxCC.Cfg.Rc


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

theorem rawEq_iff (a b : RawLayout) : rawEq a b = true ↔ a = b := by
  rcases a with ⟨av, ar⟩
  rcases b with ⟨bv, br⟩
  simp only [rawEq, Bool.and_eq_true, mapEq_iff (fun x y : List Nat => decide (x = y))
    (fun x y => decide_eq_true_iff) av bv, decide_eq_true_eq, RawLayout.mk.injEq]

theorem programEq_iff (a b : Program) : programEq a b = true ↔ a = b := by
  rcases a with ⟨⟨af, az, ae, ac, ⟨an, as, ab, atrue⟩⟩, aa, ar⟩
  rcases b with ⟨⟨bf, bz, be, bc, ⟨bn, bs, bb, btrue⟩⟩, ba, br⟩
  simp [programEq, mapEq_iff _ funEq_iff, mapEq_iff _ tableEq_iff, rawEq_iff, and_assoc]

/-- The generated program carries the layout it was given. -/
theorem generate_raw {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {raw : RawLayout}
    {P : Program} (h : generate F bodies raw = some P) : P.raw = raw := by
  unfold generate at h
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h
    rw [← h]

/-- The candidate at another raw layout is the same candidate with that layout. -/
theorem generate_withRaw {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {raw : RawLayout}
    {P : Program} (h : generate F bodies raw = some P) (raw' : RawLayout) :
    generate F bodies raw' = some { P with raw := raw' } := by
  unfold generate at h ⊢
  cases he : entries F bodies (List.range F.size) with
  | none => simp [he] at h
  | some es =>
    simp only [he, bind, Option.bind, Option.some.injEq] at h ⊢
    rw [← h]

theorem checkProgram_parts {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code}
    {candidate : Program} {borrows : Own.Plain.BorrowSigs} {uniqs : Own.Plain.UniqSigs}
    (h : checkProgram F bodies candidate borrows uniqs = true) :
    Own.Plain.checkOwned F bodies borrows uniqs = true ∧
      generate F bodies candidate.raw = some candidate := by
  simp only [checkProgram, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  cases hg : generate F bodies candidate.raw with
  | none => simp [hg] at h
  | some expected =>
    have eq : expected = candidate := (programEq_iff ..).mp (by simpa [hg] using h.2)
    simpa [eq]

end IxCC.Cfg.Rc
