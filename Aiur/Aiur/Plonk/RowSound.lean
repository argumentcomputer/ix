import Aiur.Plonk.Emit

/-!
# A row's constraints from its emitted gates

`rowOkR a r` extends `rowOk` with two checks per constraint cone, both
independent of any wire map:

* `realisedB T sr gs`: every template row is a constraint gate of the row
  with slot `s` read as reference `sr s` (`sr` from `slotRefs`, untrusted);
* `colsB T sr`: every column slot `.column c` reads the cell reference of
  main column `c` (`8c`).

`constraints_of_gates`: if a wire assignment satisfies the row's gates
instantiated through any `wireOf` that sends cell reference `x` to
`cellWire (x / 8)`, then the Air's constraints hold at row `r` of the trace
`main` with `main r v = w (cellWire v)`.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Template SlotDef)
open Aiur.Tiling.WideStage (Air)
open Lower (Fr LGate Ref)

namespace Lower

/-- The reference of each slot `toTemplate` creates: the sorted cell
references, then the output of each defining gate. -/
def slotRefs (gates : Array LGate) : Array Ref := Id.run do
  let gs := gates.filter (·.tag == .constraint)
  let isCell (r : Ref) := r % 4 == 0
  let cells := (gs.toList.flatMap fun g => [g.a, g.b, g.c].filter isCell).eraseDups.mergeSort (· ≤ ·)
  let mut out := cells.toArray
  for g in gs do
    if g.root.isNone then out := out.push g.c
  return out

end Lower

def colsB (T : Template Fr) (sr : Nat → Ref) : Bool :=
  T.slots.zipIdx.all fun (d, s) =>
    match d with
    | .column c => sr s % 4 == 0 && sr s / 8 == c
    | _ => true

namespace AirIn

def coneOkR (gs : Array LGate) (W : Nat) (C : Nat → Tiling.Circuit Fr) (j : Nat) : Bool :=
  match Lower.coneTemplate gs airCol j with
  | .ok T =>
      let roots := (Array.range gs.size).filter fun i => gs[i]!.root == some j
      let sr := match roots.toList with
        | [i] => Lower.slotRefs ((Lower.cone gs i).map fun (g : LGate) => if g.root.isSome then { g with root := some 0 } else g)
        | _ => #[]
      let srf (s : Nat) : Ref := sr.getD s 0
      T.check (C j) && coversVars T W (C j) && realisedB T srf gs.toList && colsB T srf
  | .error _ => false

theorem coneOkR_spec {gs : Array LGate} {W : Nat} {C : Nat → Tiling.Circuit Fr} {j : Nat}
    (h : coneOkR gs W C j = true) :
    ∃ T sr, T.check (C j) = true ∧ coversVars T W (C j) = true ∧ realisedB T sr gs.toList = true ∧
      colsB T sr = true := by
  unfold coneOkR at h
  split at h
  · rename_i T _
    simp only [Bool.and_eq_true] at h
    exact ⟨T, _, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · exact absurd h (by simp)

def rowOkR (a : Air Fr) (r : Nat) : Bool :=
  let gs := rowGates a r
  (List.range a.circuit.constraints.length).all (coneOkR gs a.circuit.width (rowConstraint a r))

theorem colSlot_column {T : Template Fr} {v s : Nat} (h : T.colSlot v = some s) :
    T.slots[s]? = some (.column v) := by
  unfold Template.colSlot at h
  obtain ⟨hs, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  simp only [beq_iff_eq] at hp
  simp [hs, hp]

theorem constraints_of_gates {a : Air Fr} {r : Nat} (ok : rowOkR a r = true)
    (wireOf : Ref → Nat) (cellWire : Nat → Nat) (hcell : ∀ x, x % 4 = 0 → wireOf x = cellWire (x / 8))
    (w : Nat → Fr) (hold : ∀ g ∈ (rowGates a r).toList.map (Lower.LGate.inst wireOf), g.Holds w)
    (main : Nat → Nat → Fr) (hmain : ∀ v, main r v = w (cellWire v)) :
    a.circuit.Holds (a.assign main r) := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨T, sr, hcheck, hcover, hreal, hcols⟩ :=
    coneOkR_spec (List.all_eq_true.mp ok j (List.mem_range.mpr hj))
  have holds := relationsHold_of_realised (realised_of_realisedB hreal wireOf) hold
  refine constraint_of_cone hcheck hcover holds ?_ hj
  intro v _ s hs
  have hslot := colSlot_column hs
  have hc' := List.all_eq_true.mp hcols (SlotDef.column v, s)
    (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hslot))
  simp only [Bool.and_eq_true, beq_iff_eq] at hc'
  simp [Function.comp, hcell _ hc'.1, hc'.2, hmain]

/-- `checkConstraints` with `rowOkR`. -/
def checkConstraintsR (name : String) (a : Air Fr) : Except String Unit := do
  if a.circuit.constraints.isEmpty then return
  let rows := if readsMainOnly a then 1 else a.rows
  for r in [0:rows] do
    unless rowOkR a r do
      let gs := rowGates a r
      for j in [0:a.circuit.constraints.length] do
        unless coneOkR gs a.circuit.width (rowConstraint a r) j do
          throw s!"{name} row {r}: constraint {j} is not realised by its gates"

end AirIn

end Aiur.Plonk
