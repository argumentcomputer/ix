import Aiur.Plonk.Msg

/-!
# What a checked gate cone gives

`Template.Checked.constraints_hold` concludes about `T.wide val`, which reads
`0` on columns without a slot. `coversVars T W C` adds that every variable of
every constraint's normal form is a column below `W` with a slot; then the
constraints hold at any row `x` that agrees with the column slots
(`holds_of_cover`).

* `constraint_of_cone`: a checked, covering cone of `rowConstraint a r j`
  whose column slots carry row `r` of `main` gives constraint `j` of the Air
  at `a.assign main r`.
* `message_of_cone`: a checked, covering cone of `msgCircuit a r k` whose
  column slots carry row `r`, `γ`, `β`, `q`, `s` and `s'` gives
  `q · fp γ β tuple = multiplicity` and `s' = s + q` for lookup `k` at
  `a.assign main r`.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Poly Template)
open Aiur.Tiling.WideStage (Air)
open Aiur.Scalar.Circuit (ArithExpr)
open Lower (Fr)

theorem holds_of_cover {T : Template Fr} {C : Tiling.Circuit Fr} {W : Nat} (ok : T.check C = true)
    (cover : coversVars T W C = true) {val : Nat → Fr} (holds : T.RelationsHold val) (x : Nat → Fr)
    (agree : ∀ v < W, ∀ s, T.colSlot v = some s → val s = x v) : C.Holds x := by
  intro e he
  have h := Template.Checked.constraints_hold (Template.checked_of_check T ok) holds e he
  rw [← Poly.denote_ofExpr, ← Poly.denote_norm] at h ⊢
  have hcov := List.all_eq_true.mp cover e he
  rw [Poly.denote_congr (g := T.wide val) _ ?_]
  · exact h
  intro t ht v hv
  have hv' := List.all_eq_true.mp (List.all_eq_true.mp hcov t ht) v hv
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hv'
  obtain ⟨hW, s, hs⟩ := hv'
  simp [Template.wide, hs, agree v hW s hs]

namespace AirIn

theorem fixRow_denote_of_agree (a : Air Fr) (main : Nat → Nat → Fr) (r : Nat) (x : Nat → Fr)
    (agree : ∀ v < a.circuit.width, x v = main r v) (e : ArithExpr Fr) :
    (fixRow a r e).denote x = e.denote (a.assign main r) := by
  induction e with
  | const v => rfl
  | var v =>
      by_cases h : v < a.circuit.width <;>
        simp [fixRow, h, ArithExpr.denote, Air.assign, agree]
  | add x y hx hy => simp [fixRow, ArithExpr.denote, hx, hy]
  | sub x y hx hy => simp [fixRow, ArithExpr.denote, hx, hy]
  | mul x y hx hy => simp [fixRow, ArithExpr.denote, hx, hy]

theorem constraint_of_cone {a : Air Fr} {main : Nat → Nat → Fr} {r j : Nat} {T : Template Fr}
    (ok : T.check (rowConstraint a r j) = true)
    (cover : coversVars T a.circuit.width (rowConstraint a r j) = true)
    {val : Nat → Fr} (holds : T.RelationsHold val)
    (cols : ∀ v < a.circuit.width, ∀ s, T.colSlot v = some s → val s = main r v)
    (hj : j < a.circuit.constraints.length) :
    a.circuit.constraints[j].denote (a.assign main r) = 0 := by
  refine (rowConstraint_holds_iff a main r j hj).mp (holds_of_cover ok cover holds _ ?_)
  intro v hv s hs
  simp [cols v hv s hs, Air.assign, hv]

/-- A message row: main columns of row `r`, then `γ`, `β`, `q`, `s`, `s'`;
`z` on every other column (the unused `sumIn` reference). -/
def msgView (a : Air Fr) (main : Nat → Nat → Fr) (r : Nat) (γ β q s s' z : Fr) (v : Nat) : Fr :=
  if v < a.circuit.width then main r v
  else if v = gammaCol a then γ
  else if v = betaCol a then β
  else if v = qCol a then q
  else if v = sInCol a then s
  else if v = sOutCol a then s'
  else z

theorem message_of_cone {a : Air Fr} {main : Nat → Nat → Fr} {r k : Nat} {count : Bool} {T : Template Fr}
    (ok : T.check (msgCircuit a r k count) = true)
    (cover : coversVars T (a.circuit.width + 6) (msgCircuit a r k count) = true)
    {val : Nat → Fr} (holds : T.RelationsHold val) {γ β q s s' z : Fr}
    (cols : ∀ v < a.circuit.width + 6, ∀ t, T.colSlot v = some t → val t = msgView a main r γ β q s s' z v) :
    q * fp γ β ((lookupAt a k).tuple (a.assign main r)) =
        (lookupAt a k).multiplicity.denote (a.assign main r) ∧ s' = s + q := by
  have H := holds_of_cover ok cover holds (msgView a main r γ β q s s' z) cols
  have agree : ∀ v < a.circuit.width, msgView a main r γ β q s s' z v = main r v := by
    intro v hv; simp [msgView, hv]
  have W1 : ¬ a.circuit.width < a.circuit.width := Nat.lt_irrefl _
  have hq := H (qConstraint a r k) (by simp [msgCircuit])
  have hs := H (sumConstraint a) (by simp [msgCircuit])
  simp only [qConstraint, sumConstraint, normExpr_denote, ArithExpr.denote, fpExpr_denote] at hq hs
  simp only [multExpr, argExprs, fixRow_denote_of_agree a main r _ agree, List.map_map] at hq
  have e1 : msgView a main r γ β q s s' z (qCol a) = q := by simp [msgView, qCol, gammaCol, betaCol]
  have e2 : msgView a main r γ β q s s' z (gammaCol a) = γ := by simp [msgView, gammaCol]
  have e3 : msgView a main r γ β q s s' z (betaCol a) = β := by simp [msgView, gammaCol, betaCol]
  have e4 : msgView a main r γ β q s s' z (sInCol a) = s := by
    simp [msgView, gammaCol, betaCol, qCol, sInCol]
  have e5 : msgView a main r γ β q s s' z (sOutCol a) = s' := by
    simp [msgView, gammaCol, betaCol, qCol, sInCol, sOutCol]
  rw [e1, e2, e3] at hq
  rw [e1, e4, e5] at hs
  refine ⟨?_, ?_⟩
  · have : (List.map ((fun e => ArithExpr.denote (msgView a main r γ β q s s' z) e) ∘ fixRow a r)
        (lookupAt a k).args) = (lookupAt a k).tuple (a.assign main r) := by
      simp only [Tiling.Lookup.tuple]
      apply List.map_congr_left
      intro e _
      exact fixRow_denote_of_agree a main r _ agree e
    rw [this] at hq
    exact sub_eq_zero.mp hq
  · exact (sub_eq_zero.mp hs).symm

end AirIn

end Aiur.Plonk
