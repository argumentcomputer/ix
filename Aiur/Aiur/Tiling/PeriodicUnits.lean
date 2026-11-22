import Aiur.Tiling.Tables
import Aiur.Tiling.PeriodicUnroll

/-!
# Lowered chips, possibly unrolled

A *unit* is a chip with an optional unrolling. Its circuit is the lowered
chip, or the unrolled lowered chip; an instance of it gives one row of the
lowered chip, or one per body. Under `unitOk` (`Unroll.check` of the
unrolling), the unit's constraints give every body row the chip's
constraints and its ledger is the sum of the body rows' ledgers, so a system
of units and table rows has the same wide ledger as the chip instances
`instancesU` plus the tables (`System.wideLedger_units`).
-/

namespace Aiur.Tiling

open Aiur.Circuit
open Aiur.Optimized


variable {F : Type} [Field F] [DecidableEq F]

namespace Bridge

def unitCircuit (idOf : String → Nat) : Chip F × Option (Unroll F) → Tiling.Circuit F
  | (c, none) => lower idOf c
  | (c, some U) => U.circuit (lower idOf c)

/-- The chip rows of one instance of a unit with row `w`. -/
def unitRows (idOf : String → Nat) : Chip F × Option (Unroll F) → (Circuit.Var → F) → List (Circuit.Var → F)
  | (_, none), w => [w]
  | (c, some U), w => (List.range U.bodies.length).map fun b => U.row (lower idOf c) b w

def unitOk (idOf : String → Nat) : Chip F × Option (Unroll F) → Bool
  | (_, none) => true
  | (c, some U) => U.check (lower idOf c)

def unitBodies : Chip F × Option (Unroll F) → Nat
  | (_, none) => 1
  | (_, some U) => U.bodies.length

theorem length_unitRows (idOf : String → Nat) (u : Chip F × Option (Unroll F)) (w : Circuit.Var → F) :
    (unitRows idOf u w).length = unitBodies u := by
  rcases u with ⟨c, _ | U⟩ <;> simp [unitRows, unitBodies]

theorem unit_holds {idOf : String → Nat} {u : Chip F × Option (Unroll F)} {w : Circuit.Var → F}
    (h : (unitCircuit idOf u).Holds w) : ∀ r ∈ unitRows idOf u w, (lower idOf u.1).Holds r := by
  rcases u with ⟨c, _ | U⟩
  · simpa [unitRows, unitCircuit] using h
  · intro r hr
    simp only [unitRows, List.mem_map, List.mem_range] at hr
    obtain ⟨b, hb, rfl⟩ := hr
    exact U.holds _ h hb

theorem unit_ledger {idOf : String → Nat} {u : Chip F × Option (Unroll F)} (ok : unitOk idOf u = true)
    (w : Circuit.Var → F) :
    (unitCircuit idOf u).rowLedger w = ((unitRows idOf u w).map (lower idOf u.1).rowLedger).sum := by
  rcases u with ⟨c, _ | U⟩
  · simp [unitRows, unitCircuit]
  · simp only [unitCircuit, unitRows, List.map_map, Function.comp_def]
    exact Unroll.rowLedger_circuit ok w

/-- The chip rows of all instances of the units. -/
def instancesU (idOf : String → Nat) (units : List (Chip F × Option (Unroll F))) (sys : System F)
    (main : Nat → Nat → F) : List (Chip F × (Circuit.Var → F)) :=
  (List.range units.length).flatMap fun f =>
    match units[f]? with
    | some u => (List.range (sys.cap f)).flatMap fun i =>
        (unitRows idOf u (sys.wideRow main f i)).map fun r => (u.1, r)
    | none => []

def capacityRowsU (units : List (Chip F × Option (Unroll F))) (sys : System F) : Nat :=
  ((List.range units.length).map fun f =>
    match units[f]? with
    | some u => sys.cap f * unitBodies u
    | none => 0).sum

def capacityLookupsU (units : List (Chip F × Option (Unroll F))) (sys : System F) : Nat :=
  ((List.range units.length).map fun f =>
    match units[f]? with
    | some u => sys.cap f * unitBodies u * (u.1.sends.length + u.1.memory.length)
    | none => 0).sum + 1

theorem mem_instancesU {idOf : String → Nat} {units : List (Chip F × Option (Unroll F))} {sys : System F}
    {main : Nat → Nat → F} {p : Chip F × (Circuit.Var → F)} (hp : p ∈ instancesU idOf units sys main) :
    ∃ f, ∃ hf : f < units.length, ∃ i < sys.cap f,
      p.1 = units[f].1 ∧ p.2 ∈ unitRows idOf units[f] (sys.wideRow main f i) := by
  simp only [instancesU, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨f, hf, hp⟩ := hp
  rw [List.getElem?_eq_getElem hf] at hp
  simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hp
  obtain ⟨i, hi, r, hr, rfl⟩ := hp
  exact ⟨f, hf, i, hi, rfl, hr⟩

theorem sum_const_length {α M : Type} [AddCommMonoid M] (l : List α) (m : M) :
    (l.map fun _ => m).sum = l.length • m := by
  simp [List.map_const', List.sum_replicate]

theorem lookupCount_instancesU (idOf : String → Nat) (units : List (Chip F × Option (Unroll F)))
    (sys : System F) (main : Nat → Nat → F) :
    lookupCount (instancesU idOf units sys main) = capacityLookupsU units sys := by
  simp only [lookupCount, capacityLookupsU, instancesU, System.sum_map_flatMap]
  congr 2
  apply List.map_congr_left
  intro f _
  cases units[f]? with
  | none => simp
  | some u =>
    simp only [System.sum_map_flatMap, List.map_map, Function.comp_def]
    have inner : ∀ a, ((unitRows idOf u (sys.wideRow main f a)).map
        fun _ => u.1.sends.length + u.1.memory.length).sum =
        unitBodies u * (u.1.sends.length + u.1.memory.length) := by
      intro a; rw [sum_const_length, length_unitRows, smul_eq_mul]
    simp only [inner, sum_const_length, List.length_range, smul_eq_mul]
    ring

theorem length_instancesU (idOf : String → Nat) (units : List (Chip F × Option (Unroll F))) (sys : System F)
    (main : Nat → Nat → F) : (instancesU idOf units sys main).length = capacityRowsU units sys := by
  simp only [instancesU, capacityRowsU, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro f _
  cases units[f]? with
  | none => simp
  | some u =>
    simp only [List.length_flatMap, List.length_map, length_unitRows, List.map_map, Function.comp_def]
    rw [sum_const_length]
    simp [mul_comm]

end Bridge

open Bridge

/-- The wide ledger of a system of units and table rows is the chips' ledger
over `instancesU` plus a ledger supported on the table rows. -/
theorem System.wideLedger_units {units : List (Chip F × Option (Unroll F))} {idOf : String → Nat}
    {fixed : List (List F)} (sys : System F)
    (circuits : sys.circuits = units.map (unitCircuit idOf) ++ fixed.map tableCircuit)
    (ok : ∀ u ∈ units, unitOk idOf u = true) (main : Nat → Nat → F) :
    ∃ tables : Ledger F, (∀ t, tables t ≠ 0 → t ∈ fixed) ∧
      sys.wideLedger (sys.wideRow main) =
        ((instancesU idOf units sys main).map fun p => (Bridge.lower idOf p.1).rowLedger p.2).sum + tables := by
  let G : Nat → Ledger F := fun f => ((List.range (sys.cap f)).map fun i =>
      ((sys.circuits[f]?.map fun C => C.rowLedger (sys.wideRow main f i)).getD 0)).sum
  have len : sys.circuits.length = units.length + fixed.length := by simp [circuits]
  refine ⟨((List.range fixed.length).map fun j => G (units.length + j)).sum, ?_, ?_⟩
  · intro t ht
    by_contra nt
    apply ht
    apply ledger_sum_off (S := (· ∈ fixed)) _ t nt
    intro x hx u hu
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hj := List.mem_range.mp hj
    apply ledger_sum_off (S := (· ∈ fixed)) _ u hu
    intro y hy v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
    have at_j : sys.circuits[units.length + j]? = some (tableCircuit fixed[j]) := by
      rw [circuits, List.getElem?_append_right (by simp)]
      simp [hj]
    simp only [at_j, Option.map_some, Option.getD_some, tableCircuit_rowLedger, Finsupp.single_apply]
    rw [if_neg]
    rintro rfl
    exact hv (List.getElem_mem hj)
  · unfold System.wideLedger
    rw [len, List.range_add, List.map_append, List.sum_append]
    congr 1
    · simp only [instancesU, System.sum_map_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro f hf
      have hf := List.mem_range.mp hf
      have at_f : sys.circuits[f]? = some (unitCircuit idOf units[f]) := by
        rw [circuits, List.getElem?_append_left (by simpa using hf)]
        simp [hf]
      simp only [at_f, List.getElem?_eq_getElem hf, Option.map_some, Option.getD_some,
        System.sum_map_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro i _
      rw [unit_ledger (ok _ (List.getElem_mem hf)), List.map_map]
      rfl
    · simp only [List.map_map, Function.comp_def, G]

end Aiur.Tiling
