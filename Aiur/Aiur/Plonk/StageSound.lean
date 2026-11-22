import Aiur.Plonk.Chain

/-!
# The emitted constraint system of a stage, and what satisfying it gives

The stage's tables `airs` are lowered row by row against one global pool
`P`; `rowState airs P (t, r)` is row `r` of table `t`. The emitted gates
(`emitGates`) are

* the boundary gates `w(last) = 0` and `w(init) = 0`;
* every pool gate, its references through `poolWire`;
* every row's gates, through the row's wire map `wireOf (t, r)`.

A `Wiring` fixes the wire maps: cell references go to the cell wires
`cellWire (t, r) c`, pool references to `poolWire` in every row, and the
running sum is linked across rows in `instances` order (`Linked`: each row's
`sumIn` wire is the previous row's final-sum wire; the first is `init`, the
last row's final sum is `last`). Soundness needs no injectivity of the wire
maps: identifying wires only adds constraints.

`stageOk airs P poolIdx` checks every table: `poolClosed P` (pool gates read
only pool references), then `rowCheck` on row 0 of a uniform table
(`rowCheck_uniform`) and on every row of the others.

`stage_sound`: if `w` satisfies the emitted gates, the trace
`W.main w t r c = w (cellWire (t, r) c)` satisfies `StageHolds airs`, and if
no message tuple has a zero fingerprint,
`logupEval γ β (stageLedger airs main) = − w(init)`.

`ChallengeGood γ β T L`: the ledger is zero whenever its LogUp sum
vanishes, and no message tuple has a zero fingerprint (`stage_balanced` in
`WideSound.lean` uses it with the root table appended). `ChallengeGood` is the crypto-layer event: `(γ, β)` drawn after the binding
commitment to the message cells (Fiat–Shamir), and bounded by the
fingerprint-injectivity and Schwartz–Zippel counts of `Logup.lean`.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Ledger)
open Aiur.Tiling.WideStage (Air StageHolds stageLedger)
open Lower (Fr LGate Ref)

/-- `x` threads through `l`: each element's input is the previous output,
the first input is `x`, the last output is `y`. -/
def Linked {ι α : Type} (fin fout : ι → α) : α → List ι → α → Prop
  | x, [], y => x = y
  | x, i :: is, y => fin i = x ∧ Linked fin fout (fout i) is y

theorem Linked.map {ι α β : Type} {fin fout : ι → α} (f : α → β) :
    ∀ {x : α} {l : List ι} {y : α}, Linked fin fout x l y → Linked (f ∘ fin) (f ∘ fout) (f x) l (f y)
  | _, [], _, h => congrArg f h
  | _, _ :: _, _, h => ⟨by simp [Function.comp, h.1], Linked.map f h.2⟩

theorem Linked.telescope {ι : Type} {fin fout : ι → Fr} :
    ∀ {x : Fr} {l : List ι} {y : Fr}, Linked fin fout x l y → y - x = (l.map fun i => fout i - fin i).sum
  | _, [], _, h => by simp only [Linked] at h; simp [h]
  | _, _ :: _, _, h => by
      rw [List.map_cons, List.sum_cons, ← Linked.telescope h.2, h.1]
      ring

/-- `Linked` as a decision procedure on wires. -/
def linkedB {ι : Type} (fin fout : ι → Nat) : Nat → List ι → Nat → Bool
  | x, [], y => x == y
  | x, i :: is, y => fin i == x && linkedB fin fout (fout i) is y

theorem linked_of_linkedB {ι : Type} {fin fout : ι → Nat} :
    ∀ {x : Nat} {l : List ι} {y : Nat}, linkedB fin fout x l y = true → Linked fin fout x l y
  | _, [], _, h => by simp only [linkedB, beq_iff_eq] at h; exact h
  | _, _ :: _, _, h => by
      simp only [linkedB, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨h.1, linked_of_linkedB h.2⟩

def defaultAir : Air Fr := ⟨⟨0, 0, [], []⟩, 0, fun _ _ => 0⟩

def airAt (airs : List (Air Fr)) (t : Nat) : Air Fr := airs.getD t defaultAir

/-- Every row `(t, r)` of the stage, table by table. -/
def instances (airs : List (Air Fr)) : List (Nat × Nat) :=
  airs.zipIdx.flatMap fun x => (List.range x.1.rows).map fun r => (x.2, r)

def rowState (airs : List (Air Fr)) (P : Lower.Pool) (i : Nat × Nat) : Lower.St :=
  AirIn.lowerRowState (airAt airs i.1) i.2 P

structure Wiring (airs : List (Air Fr)) (P : Lower.Pool) where
  wireOf : Nat × Nat → Ref → Nat
  cellWire : Nat × Nat → Nat → Nat
  poolWire : Ref → Nat
  init : Nat
  last : Nat
  cell_eq : ∀ i x, x % 4 = 0 → wireOf i x = cellWire i (x / 8)
  pool_eq : ∀ i x, x % 4 = 2 → wireOf i x = poolWire x
  linked : Linked (fun i => wireOf i Lower.sumIn) (fun i => wireOf i (rowState airs P i).sum) init
    (instances airs) last

def Wiring.main {airs : List (Air Fr)} {P : Lower.Pool} (W : Wiring airs P) (w : Nat → Fr) (t r c : Nat) : Fr :=
  w (W.cellWire (t, r) c)

def emitGates (airs : List (Air Fr)) (P : Lower.Pool) (W : Wiring airs P) : List (Gate Fr) :=
  [⟨W.last, W.last, W.last, 1, 0, 0, 0, 0⟩, ⟨W.init, W.init, W.init, 1, 0, 0, 0, 0⟩] ++ P.gates.toList.map (·.inst W.poolWire) ++
    (instances airs).flatMap fun i => (rowState airs P i).gates.toList.map (·.inst (W.wireOf i))

def poolClosed (P : Lower.Pool) : Bool :=
  P.gates.all fun g => g.a % 4 == 2 && g.b % 4 == 2 && g.c % 4 == 2

def stageOk (airs : List (Air Fr)) (P : Lower.Pool) (poolIdx : Ref → Option Nat) : Bool :=
  poolClosed P && airs.all fun a =>
    if AirIn.uniformB a then AirIn.rowCheck a 0 P poolIdx
    else (List.range a.rows).all fun r => AirIn.rowCheck a r P poolIdx

/-- The message tuples of the stage under trace `main`. -/
def MsgTuple (airs : List (Air Fr)) (main : Nat → Nat → Nat → Fr) (u : List Fr) : Prop :=
  ∃ x ∈ airs.zipIdx, ∃ r < x.1.rows, ∃ l ∈ x.1.circuit.lookups, u = l.tuple (x.1.assign (main x.2) r)

theorem mem_instances {airs : List (Air Fr)} {i : Nat × Nat} (h : i ∈ instances airs) :
    ∃ x ∈ airs.zipIdx, i = (x.2, i.2) ∧ i.2 < x.1.rows ∧ airAt airs x.2 = x.1 := by
  simp only [instances, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨x, hx, r, hr, rfl⟩ := h
  refine ⟨x, hx, rfl, hr, ?_⟩
  have := List.mem_zipIdx_iff_getElem?.mp hx
  simp [airAt, List.getD_eq_getElem?_getD, this]

theorem rowCheck_of_stageOk {airs : List (Air Fr)} {P : Lower.Pool} {poolIdx : Ref → Option Nat}
    (ok : stageOk airs P poolIdx = true) {a : Air Fr} (ha : a ∈ airs) {r : Nat} (hr : r < a.rows) :
    AirIn.rowCheck a r P poolIdx = true := by
  simp only [stageOk, Bool.and_eq_true, List.all_eq_true] at ok
  have h := ok.2 a ha
  split at h
  · rename_i hu; rw [AirIn.rowCheck_uniform hu]; exact h
  · exact List.all_eq_true.mp h r (List.mem_range.mpr hr)

theorem gate_inst_pool {P : Lower.Pool} (closed : poolClosed P = true) {wireOf poolWire : Ref → Nat}
    (heq : ∀ x, x % 4 = 2 → wireOf x = poolWire x) {g : LGate} (hg : g ∈ P.gates) :
    g.inst wireOf = g.inst poolWire := by
  have h := Array.all_eq_true_iff_forall_mem.mp closed g hg
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp [Lower.LGate.inst, heq _ h.1.1, heq _ h.1.2, heq _ h.2]

theorem sum_flatMap' {α : Type} (l : List α) (g : α → List Fr) :
    (l.flatMap g).sum = (l.map fun a => (g a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_instances (airs : List (Air Fr)) (f : Nat × Nat → Fr) (F : Air Fr → Nat → Nat → Fr)
    (hf : ∀ x ∈ airs.zipIdx, ∀ r < x.1.rows, f (x.2, r) = F x.1 x.2 r) :
    ((instances airs).map f).sum =
      (airs.zipIdx.map fun x => ((List.range x.1.rows).map fun r => F x.1 x.2 r).sum).sum := by
  rw [instances, List.map_flatMap, sum_flatMap']
  apply congrArg List.sum
  apply List.map_congr_left
  intro x hx
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  exact hf x hx r (List.mem_range.mp hr)

theorem stage_sound {airs : List (Air Fr)} {P : Lower.Pool} {poolIdx : Ref → Option Nat}
    (ok : stageOk airs P poolIdx = true) (W : Wiring airs P) (w : Nat → Fr)
    (sat : ∀ g ∈ emitGates airs P W, g.Holds w) :
    StageHolds airs (W.main w) ∧
      ((∀ u, MsgTuple airs (W.main w) u → fp (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef)) u ≠ 0) →
        logupEval (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef)) (stageLedger airs (W.main w)) =
          - w W.init) := by
  have closed : poolClosed P = true := by
    simp only [stageOk, Bool.and_eq_true] at ok; exact ok.1
  have hlast : w W.last = 0 := by
    have := sat _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl List.mem_cons_self))))
    simpa [Gate.Holds] using this
  have hpoolW : ∀ g ∈ P.gates, (g.inst W.poolWire).Holds w := fun g hg =>
    sat _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
      (List.mem_map.mpr ⟨g, Array.mem_toList_iff.mpr hg, rfl⟩)))))
  -- every row: constraints and the row's LogUp equation
  have row : ∀ x ∈ airs.zipIdx, ∀ r < x.1.rows,
      x.1.circuit.Holds (x.1.assign (W.main w x.2) r) ∧
        ((∀ l ∈ x.1.circuit.lookups, fp (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
            (l.tuple (x.1.assign (W.main w x.2) r)) ≠ 0) →
          w (W.wireOf (x.2, r) (rowState airs P (x.2, r)).sum) - w (W.wireOf (x.2, r) Lower.sumIn) =
            logupEval (w (W.poolWire Lower.gammaRef)) (w (W.poolWire Lower.betaRef))
              (x.1.circuit.rowLedger (x.1.assign (W.main w x.2) r))) := by
    intro x hx r hr
    have hat : airAt airs x.2 = x.1 := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simp [airAt, List.getD_eq_getElem?_getD, this]
    have hin : (x.2, r) ∈ instances airs := by
      simp only [instances, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨x, hx, r, hr, rfl⟩
    have hst : rowState airs P (x.2, r) = AirIn.lowerRowState x.1 r P := by simp [rowState, hat]
    have hmem : x.1 ∈ airs := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      exact List.mem_of_getElem? this
    have hγ := W.pool_eq (x.2, r) Lower.gammaRef (by decide)
    have hβ := W.pool_eq (x.2, r) Lower.betaRef (by decide)
    have := AirIn.rowCheck_sound (rowCheck_of_stageOk ok hmem hr) (W.wireOf (x.2, r)) (W.cellWire (x.2, r))
      (W.cell_eq (x.2, r)) w
      (fun g hg => sat _ (List.mem_append.mpr (.inr (List.mem_flatMap.mpr ⟨(x.2, r), hin,
        List.mem_map.mpr ⟨g, by rw [hst]; exact Array.mem_toList_iff.mpr hg, rfl⟩⟩))))
      (fun g hg => by rw [gate_inst_pool closed (W.pool_eq (x.2, r)) hg]; exact hpoolW g hg)
      (W.main w x.2) (fun v => rfl)
    rw [hγ, hβ, ← hst] at this
    exact this
  refine ⟨fun x hx r hr => (row x hx r hr).1, fun hfp => ?_⟩
  have tele := (W.linked.map w).telescope
  rw [hlast, zero_sub] at tele
  rw [tele, sum_instances airs _ (fun a t r => logupEval (w (W.poolWire Lower.gammaRef))
      (w (W.poolWire Lower.betaRef)) (a.circuit.rowLedger (a.assign (W.main w t) r)))]
  · rw [stageLedger, map_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _
    simp [Air.ledger, map_list_sum, List.map_map, Function.comp_def]
  · intro x hx r hr
    exact (row x hx r hr).2 fun l hl => hfp _ ⟨x, hx, r, hr, l, hl, rfl⟩

/-- The crypto-layer event for challenges `(γ, β)` and ledger `L` over the
message tuples `tuples`: no tuple has a zero fingerprint, and the LogUp sum of
`L` vanishes only if `L` is zero. -/
def ChallengeGood (γ β : Fr) (tuples : List Fr → Prop) (L : Ledger Fr) : Prop :=
  (∀ u, tuples u → fp γ β u ≠ 0) ∧ (logupEval γ β L = 0 → L = 0)

theorem init_zero {airs : List (Air Fr)} {P : Lower.Pool} (W : Wiring airs P) {w : Nat → Fr}
    (sat : ∀ g ∈ emitGates airs P W, g.Holds w) : w W.init = 0 := by
  have := sat ⟨W.init, W.init, W.init, 1, 0, 0, 0, 0⟩
    (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_cons_of_mem _ List.mem_cons_self)))))
  simpa [Gate.Holds] using this

end Aiur.Plonk
