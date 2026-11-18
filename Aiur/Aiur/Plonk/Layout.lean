import Aiur.Plonk.StageSound

/-!
# A concrete wire layout

`Layout` numbers the wires: cell `(t, r, c)` is `cellBase t + r·rowWidth t + c`,
pool reference `4k + 2` is `poolBase + k`, row-local reference `4k + 1` of row
`i` is `locBase i + k`, the row's `sumIn` is `sumIn i`, and every other
reference is `spare`. `cell_eq` and `pool_eq` hold by construction; the
running-sum link is decided by `linkOk` (`linkedB` over `instances`), and
`Layout.wiring` packages a layout that passes it as a `Wiring`.
-/

namespace Aiur.Plonk

open Aiur.Tiling.WideStage (Air)
open Lower (Fr Ref)

structure Layout where
  cellBase : Nat → Nat
  rowWidth : Nat → Nat
  poolBase : Nat
  locBase : Nat × Nat → Nat
  sumIn : Nat × Nat → Nat
  spare : Nat

namespace Layout

def cellWire (L : Layout) (i : Nat × Nat) (c : Nat) : Nat := L.cellBase i.1 + i.2 * L.rowWidth i.1 + c

def poolWire (L : Layout) (x : Ref) : Nat := L.poolBase + x / 4

def wireOf (L : Layout) (i : Nat × Nat) (x : Ref) : Nat :=
  if x % 4 = 0 then L.cellWire i (x / 8)
  else if x % 4 = 2 then L.poolWire x
  else if x % 4 = 1 then L.locBase i + x / 4
  else if x = Lower.sumIn then L.sumIn i
  else L.spare

/-- `fr` is every row's final-sum reference; for a uniform table it is
checked once (`lowerRowState_uniform`). -/
def finalOk (airs : List (Air Fr)) (P : Lower.Pool) (fr : Nat × Nat → Ref) : Bool :=
  airs.zipIdx.all fun x =>
    if AirIn.uniformB x.1 then
      fr (x.2, 0) == (AirIn.lowerRowState x.1 0 P).sum && (List.range x.1.rows).all fun r => fr (x.2, r) == fr (x.2, 0)
    else (List.range x.1.rows).all fun r => fr (x.2, r) == (AirIn.lowerRowState x.1 r P).sum

theorem finalOk_spec {airs : List (Air Fr)} {P : Lower.Pool} {fr : Nat × Nat → Ref} (h : finalOk airs P fr = true)
    {i : Nat × Nat} (hi : i ∈ instances airs) : fr i = (rowState airs P i).sum := by
  obtain ⟨x, hx, hix, hr, hat⟩ := mem_instances hi
  have hx' := List.all_eq_true.mp h x hx
  rw [hix, rowState, hat]
  simp only at hx' ⊢
  split at hx'
  · rename_i hu
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hx'
    rw [hx'.2 _ hr, hx'.1, AirIn.lowerRowState_uniform hu i.2]
  · simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hx'
    exact hx' _ hr

theorem Linked.congr_out {ι α : Type} {fin fout fout' : ι → α} :
    ∀ {x : α} {l : List ι} {y : α}, (∀ i ∈ l, fout' i = fout i) → Linked fin fout' x l y → Linked fin fout x l y
  | _, [], _, _, h => h
  | _, i :: _, _, he, h => by
      refine ⟨h.1, ?_⟩
      rw [← he i List.mem_cons_self]
      exact Linked.congr_out (fun j hj => he j (List.mem_cons_of_mem _ hj)) h.2

def linkOk (L : Layout) (airs : List (Air Fr)) (P : Lower.Pool) (init last : Nat) : Bool :=
  linkedB (fun i => L.wireOf i Lower.sumIn) (fun i => L.wireOf i (rowState airs P i).sum) init (instances airs) last

/-- `linkOk` with the final-sum references given by `fr`. -/
def linkOkF (L : Layout) (airs : List (Air Fr)) (fr : Nat × Nat → Ref) (init last : Nat) : Bool :=
  linkedB (fun i => L.wireOf i Lower.sumIn) (fun i => L.wireOf i (fr i)) init (instances airs) last

def wiringF (L : Layout) {airs : List (Air Fr)} {P : Lower.Pool} (fr : Nat × Nat → Ref) (init last : Nat)
    (hf : finalOk airs P fr = true) (h : L.linkOkF airs fr init last = true) : Wiring airs P where
  wireOf := L.wireOf
  cellWire := L.cellWire
  poolWire := L.poolWire
  init := init
  last := last
  cell_eq := fun i x hx => by simp [wireOf, hx]
  pool_eq := fun i x hx => by simp [wireOf, hx]
  linked := Linked.congr_out (fun i hi => by rw [finalOk_spec hf hi]) (linked_of_linkedB h)

def wiring (L : Layout) {airs : List (Air Fr)} {P : Lower.Pool} (init last : Nat)
    (h : L.linkOk airs P init last = true) : Wiring airs P where
  wireOf := L.wireOf
  cellWire := L.cellWire
  poolWire := L.poolWire
  init := init
  last := last
  cell_eq := fun i x hx => by simp [wireOf, hx]
  pool_eq := fun i x hx => by simp [wireOf, hx]
  linked := linked_of_linkedB h

end Layout

end Aiur.Plonk
