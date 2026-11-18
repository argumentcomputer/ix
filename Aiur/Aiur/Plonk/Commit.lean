import Aiur.Plonk.StageSound

/-!
# The commitment list: exactly the cells messages read

BSB22 binds the values of the committed wires before the challenge `γ` is
drawn (`Scs.Satisfied`: `w γ = H (committed.map w)`). For the LogUp argument
the committed values must determine every message: its tuple and its
multiplicity. `msgCols a` is the set of main columns read by some lookup of
`a` (the variables of each multiplicity and argument below the main width;
the variables above it are fixed columns, i.e. constants of the table).
`commitList airs cellWire` is the cell wire of every such column in every
row of every table, in `instances` order.

`committed_binds`: two assignments that agree on the committed wires have
the same stage ledger and the same message tuples. So the ledger and the
tuple set that `ChallengeGood` quantifies over are functions of the
committed values (`ledgerOf`, `tuplesOf`, `ledgerOf_spec`), fixed before `γ`.
Cells outside every message are not committed: they enter no message, and
the constraints are checked on the final assignment.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Ledger)
open Aiur.Tiling.WideStage (Air StageHolds stageLedger)
open Aiur.Scalar.Circuit (ArithExpr)
open Lower (Fr Ref)

def exprVars : ArithExpr Fr → List Nat
  | .const _ => []
  | .var v => [v]
  | .add x y | .sub x y | .mul x y => exprVars x ++ exprVars y

theorem denote_congr {x y : Nat → Fr} : ∀ e : ArithExpr Fr, (∀ v ∈ exprVars e, x v = y v) →
    e.denote x = e.denote y
  | .const _, _ => rfl
  | .var v, h => h v (by simp [exprVars])
  | .add a b, h | .sub a b, h | .mul a b, h => by
      simp only [ArithExpr.denote]
      rw [denote_congr a fun v hv => h v (by simp [exprVars, hv]),
        denote_congr b fun v hv => h v (by simp [exprVars, hv])]

def lookupVars (l : Tiling.Lookup Fr) : List Nat := exprVars l.multiplicity ++ l.args.flatMap exprVars

/-- The main columns some lookup of `a` reads. -/
def msgCols (a : Air Fr) : List Nat :=
  ((a.circuit.lookups.flatMap lookupVars).filter (· < a.circuit.width)).eraseDups

/-- The committed wires: the message cells of every row of every table. -/
def commitList (airs : List (Air Fr)) (cellWire : Nat × Nat → Nat → Nat) : List Nat :=
  (instances airs).flatMap fun i => (msgCols (airAt airs i.1)).map (cellWire i)

theorem mem_msgCols {a : Air Fr} {l : Tiling.Lookup Fr} (hl : l ∈ a.circuit.lookups) {v : Nat}
    (hv : v ∈ lookupVars l) (hw : v < a.circuit.width) : v ∈ msgCols a := by
  simp only [msgCols, List.mem_eraseDups, List.mem_filter, List.mem_flatMap, decide_eq_true_eq]
  exact ⟨⟨l, hl, hv⟩, hw⟩

/-- A lookup's tuple and multiplicity depend only on the row's message cells. -/
theorem lookup_congr (a : Air Fr) {m m' : Nat → Nat → Fr} {r : Nat}
    (h : ∀ c ∈ msgCols a, m r c = m' r c) {l : Tiling.Lookup Fr} (hl : l ∈ a.circuit.lookups) :
    l.tuple (a.assign m r) = l.tuple (a.assign m' r) ∧
      l.multiplicity.denote (a.assign m r) = l.multiplicity.denote (a.assign m' r) := by
  have hv : ∀ v ∈ lookupVars l, a.assign m r v = a.assign m' r v := by
    intro v hv
    simp only [Air.assign_apply]
    split
    · rename_i hw; exact h v (mem_msgCols hl hv hw)
    · rfl
  refine ⟨?_, denote_congr _ fun v hv' => hv v (by simp [lookupVars, hv'])⟩
  simp only [Tiling.Lookup.tuple]
  apply List.map_congr_left
  intro e he
  exact denote_congr e fun v hv' => hv v (by simp only [lookupVars, List.mem_append, List.mem_flatMap]; exact .inr ⟨e, he, hv'⟩)

theorem rowLedger_congr (a : Air Fr) {m m' : Nat → Nat → Fr} {r : Nat}
    (h : ∀ c ∈ msgCols a, m r c = m' r c) :
    a.circuit.rowLedger (a.assign m r) = a.circuit.rowLedger (a.assign m' r) := by
  simp only [Tiling.Circuit.rowLedger]
  congr 1
  apply List.map_congr_left
  intro l hl
  obtain ⟨ht, hm⟩ := lookup_congr a h hl
  simp only [Tiling.Lookup.entry, ht, hm]

theorem committed_binds {airs : List (Air Fr)} {P : Lower.Pool} (W : Wiring airs P) {w w' : Nat → Fr}
    (h : ∀ x ∈ commitList airs W.cellWire, w x = w' x) :
    stageLedger airs (W.main w) = stageLedger airs (W.main w') ∧
      ∀ u, MsgTuple airs (W.main w) u ↔ MsgTuple airs (W.main w') u := by
  have cells : ∀ x ∈ airs.zipIdx, ∀ r < x.1.rows, ∀ c ∈ msgCols x.1, W.main w x.2 r c = W.main w' x.2 r c := by
    intro x hx r hr c hc
    have hat : airAt airs x.2 = x.1 := by
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simp [airAt, List.getD_eq_getElem?_getD, this]
    apply h
    simp only [commitList, List.mem_flatMap, List.mem_map]
    refine ⟨(x.2, r), ?_, c, by rw [hat]; exact hc, rfl⟩
    simp only [instances, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨x, hx, r, hr, rfl⟩
  refine ⟨?_, fun u => ?_⟩
  · simp only [stageLedger]
    congr 1
    apply List.map_congr_left
    intro x hx
    simp only [Air.ledger]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact rowLedger_congr x.1 (cells x hx r (List.mem_range.mp hr))
  · constructor
    · rintro ⟨x, hx, r, hr, l, hl, rfl⟩
      exact ⟨x, hx, r, hr, l, hl, (lookup_congr x.1 (cells x hx r hr) hl).1⟩
    · rintro ⟨x, hx, r, hr, l, hl, rfl⟩
      exact ⟨x, hx, r, hr, l, hl, (lookup_congr x.1 (cells x hx r hr) hl).1.symm⟩

/-- The ledger as a function of the committed values. -/
noncomputable def ledgerOf {airs : List (Air Fr)} {P : Lower.Pool} (W : Wiring airs P) (c : List Fr) : Ledger Fr :=
  open Classical in
  if h : ∃ w : Nat → Fr, (commitList airs W.cellWire).map w = c then stageLedger airs (W.main h.choose) else 0

/-- The message tuples as a function of the committed values. -/
noncomputable def tuplesOf {airs : List (Air Fr)} {P : Lower.Pool} (W : Wiring airs P) (c : List Fr) (u : List Fr) : Prop :=
  open Classical in
  if h : ∃ w : Nat → Fr, (commitList airs W.cellWire).map w = c then MsgTuple airs (W.main h.choose) u else False

theorem ledgerOf_spec {airs : List (Air Fr)} {P : Lower.Pool} (W : Wiring airs P) (w : Nat → Fr) :
    ledgerOf W ((commitList airs W.cellWire).map w) = stageLedger airs (W.main w) ∧
      tuplesOf W ((commitList airs W.cellWire).map w) = MsgTuple airs (W.main w) := by
  have ex : ∃ w' : Nat → Fr, (commitList airs W.cellWire).map w' = (commitList airs W.cellWire).map w := ⟨w, rfl⟩
  have agree : ∀ x ∈ commitList airs W.cellWire, ex.choose x = w x := List.map_inj_left.mp ex.choose_spec
  have b := committed_binds W agree
  refine ⟨?_, ?_⟩
  · simp only [ledgerOf, dif_pos ex]; exact b.1
  · funext u; simp only [tuplesOf, dif_pos ex]; exact propext (b.2 u)

end Aiur.Plonk
