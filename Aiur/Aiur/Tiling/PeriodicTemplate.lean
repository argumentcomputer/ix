import Aiur.Tiling.Periodic
import Aiur.Tiling.KeyedLedger

/-!
# Templates and fixed columns of the periodic-shard layout (v2)

A v2 template (`Template2`) is a layout certificate over physical rows of `W`
cells (`L = W/4` lanes):

* a **gate row** holds lanes that are gate lanes, lane messages or empty, and
  a list of **spans** `(start, len, role)`: each span is one relation, the sum
  of its lanes, with a product only in its first lane;
* a **row message** holds one logical message row, in `W` cells. On the rows
  of a chunked call receive (`key`), cell 1 is constrained to zero and the
  fixed key column carries the instance's invocation id.

Messages are listed once, as v1 message rows (`messages`), in lookup order;
physical lanes and rows reference them by index. Their bus coordinate is the
packed code `ts` of `(tag, sub)` from the system's bus table.

The checker validates a v2 template through two templates derived from it:

* `logical`: a v1 `Template` with one joined gate row per span (its lanes
  padded with zero lanes), one pin row per invocation slot, and the message
  rows. `System.checkKeyed` of the system of logical templates validates every
  relation, slot and message group, as in v1.
* `shadow`: a v1 `Template` whose rows carry the physical cells. The copy
  labels and multiplicities of a shard come from the shadow system, so the v1
  copy argument applies to each shard.

`checkPhysical` adds what ties the physical rows to the logical template: spans
fit their row and have distinct starts, continuation lanes have no product,
gate lanes have no invocation-id term, physical cells hold no invocation slot,
every message is placed once, lane messages fit three cells, and the bus
table's placement flag matches.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

inductive LaneUse (F : Type) where
  | empty
  | gate (lane : Lane F)
  /-- A lane message: logical message `m`, whose payload fits three cells. -/
  | message (m : Nat)
  deriving Repr

structure Span where
  start : Nat
  len : Nat
  role : Role
  deriving Repr, DecidableEq

inductive Row2 (F : Type) where
  | gate (lanes : List (LaneUse F)) (spans : List Span)
  /-- A row message: logical message `m`; `key` on a chunked call receive's rows. -/
  | message (m : Nat) (key : Bool)
  deriving Repr

/-- A logical message row `(sel, tag, sub, cells)`, as in v1. -/
abbrev Message (F : Type) := F × F × F × List (Option Nat)

structure Template2 (F : Type) where
  width : Nat
  slots : List (SlotDef F)
  messages : List (Message F)
  rows : List (Row2 F)
  /-- Slots without physical cells that carry a message multiplicity
  `mk + mc·x` (`Template2.physMult`). -/
  virtual : List Nat := []
  /-- Virtual slots constrained boolean by a logical-only row (`boolRows`),
  each certified by `checkBool`. -/
  booleans : List Nat := []
  deriving Repr

/-! ## The logical template -/

section Logical

variable [Zero F] [One F] [Neg F]

def LaneUse.lane : LaneUse F → Lane F
  | .gate lane => lane
  | _ => Lane.zero

/-- The lanes of span `sp`, padded with zero lanes to a full row. -/
def spanLanes (W : Nat) (ls : List (LaneUse F)) (sp : Span) : List (Lane F) :=
  ((ls.drop sp.start).take sp.len).map LaneUse.lane ++ List.replicate (lanes W - sp.len) Lane.zero

/-- `X_s − X_id`: pins invocation slot `s` to the instance's id. -/
def pinLane (s : Nat) : Lane F := { (Lane.zero : Lane F) with q0 := 1, c0 := some s, qid := -1 }

def pinRow (W s : Nat) : Row F := .gate (pinLane s :: List.replicate (lanes W - 1) Lane.zero) true [.pin s]

def Row2.logical (W : Nat) : Row2 F → List (Row F)
  | .gate ls spans => spans.map fun sp => .gate (spanLanes W ls sp) true [sp.role]
  | .message .. => []

def Template2.pins [DecidableEq F] (T : Template2 F) : List (Row F) :=
  T.slots.zipIdx.filterMap fun (d, s) => if d = .invocation then some (pinRow T.width s) else none

/-- The defining lane of virtual slot `s`: `c·X_x + k − X_s` for `s := k + c·x`,
`k − X_s` for `s := k`. -/
def virtualLane (s : Nat) : SlotDef F → Lane F
  | .sum [.linear c x] k => { (Lane.zero : Lane F) with q0 := c, c0 := some x, q1 := -1, c1 := some s, qc := k }
  | .sum _ k => { (Lane.zero : Lane F) with q0 := -1, c0 := some s, qc := k }
  | _ => Lane.zero

def virtualRow (W s : Nat) (d : SlotDef F) : Row F :=
  .gate (virtualLane s d :: List.replicate (lanes W - 1) Lane.zero) true [.defines s]

def Template2.virtualRows (T : Template2 F) : List (Row F) :=
  T.virtual.map fun s => virtualRow T.width s ((T.slots[s]?).getD (.key 0))

/-- `X_v² − X_v`. -/
def boolLane (v : Nat) : Lane F := { (Lane.zero : Lane F) with qm := 1, q0 := -1, c0 := some v, c1 := some v }

def boolRow (W v : Nat) : Row F := .gate (boolLane v :: List.replicate (lanes W - 1) Lane.zero) true [.boolean v]

def Template2.boolRows (T : Template2 F) : List (Row F) := T.booleans.map (boolRow T.width)

def Template2.messageRows (T : Template2 F) : List (Row F) :=
  T.messages.map fun (sel, tag, sub, cells) => .message sel tag sub cells

def Template2.logical [DecidableEq F] (T : Template2 F) : Template F where
  width := T.width
  slots := T.slots
  rows := T.rows.flatMap (Row2.logical T.width) ++ T.pins ++ T.virtualRows ++ T.boolRows ++ T.messageRows

end Logical

/-! ## Physical cells -/

def Template2.msgCells (T : Template2 F) (m : Nat) : List (Option Nat) :=
  (T.messages[m]?.map (·.2.2.2)).getD []

/-- The physical multiplicity `(mk, mc, cell 0)` of message `m`. A virtual
multiplicity slot defined as `mk + mc·x` puts `x` in cell 0, and a constant one
`mk` leaves it empty; any other message has `mk = 0`, `mc = sel` and its
multiplicity slot in cell 0. -/
def Template2.physMult [Zero F] (T : Template2 F) (m : Nat) : F × F × Option Nat :=
  match T.messages[m]? with
  | some (sel, _, _, some v :: _) =>
      if v ∈ T.virtual then
        match T.slots[v]? with
        | some (.sum [.linear c x] k) => (k, c, some x)
        | some (.sum [] k) => (k, 0, none)
        | _ => (0, sel, some v)
      else (0, sel, some v)
  | some (sel, _, _, _) => (0, sel, none)
  | none => (0, 0, none)

def Template2.laneCells [Zero F] (T : Template2 F) : LaneUse F → List (Option Nat)
  | .empty => [none, none, none, none]
  | .gate lane => lane.cells
  | .message m => (List.range 4).map fun j => if j = 0 then (T.physMult m).2.2 else ((T.msgCells m)[j]?).getD none

def Template2.rowCells [Zero F] (T : Template2 F) : Row2 F → List (Option Nat)
  | .gate ls _ => ls.flatMap T.laneCells
  | .message m key => (List.range T.width).map fun j =>
      if key = true ∧ j = 1 then none else if j = 0 then (T.physMult m).2.2 else ((T.msgCells m)[j]?).getD none

/-- The value of virtual slot `s` given the values `v` of physical slots. -/
def Template2.virtualValue [Zero F] [Add F] [Mul F] (T : Template2 F) (v : Nat → F) (s : Nat) : F :=
  match T.slots[s]? with
  | some (.sum [.linear c x] k) => k + c * v x
  | some (.sum [] k) => k
  | _ => 0

/-- The physical cells as a v1 template: the input of the copy argument. -/
def Template2.shadow [Zero F] (T : Template2 F) : Template F where
  width := T.width
  slots := T.slots
  rows := T.rows.map fun r => .message 0 0 0 (T.rowCells r)

def Row2.refs : Row2 F → List Nat
  | .gate ls _ => ls.filterMap fun
      | .message m => some m
      | _ => none
  | .message m _ => [m]

/-- The message indices the physical rows place, in row order. -/
def Template2.refs (T : Template2 F) : List Nat := T.rows.flatMap Row2.refs

/-! ## Bus codes -/

/-- `(tag, sub) ↦ (code, lane)`: the packed bus coordinate of a message
channel and whether its messages are lane messages. -/
abbrev Buses (F : Type) := List ((F × F) × Nat × Bool)

def codeOf [DecidableEq F] [NatCast F] [Zero F] (buses : Buses F) (key : F × F) : F :=
  ((buses.lookup key).map fun e => ((e.1 : Nat) : F)).getD 0

/-! ## The physical checker -/

section Check

variable [DecidableEq F] [Zero F]

def Template2.laneMessageOk (T : Template2 F) (buses : Buses F) (m : Nat) : Bool :=
  match T.messages[m]? with
  | some (_, tag, sub, cells) =>
      (cells.drop 4).all (· == none) &&
        match buses.lookup (tag, sub) with
        | some (_, lane) => lane
        | none => false
  | none => false

def Template2.rowMessageOk (T : Template2 F) (buses : Buses F) (m : Nat) (key : Bool) : Bool :=
  (match T.messages[m]? with
    | some (_, tag, sub, _) =>
        match buses.lookup (tag, sub) with
        | some (_, lane) => !lane
        | none => false
    | none => false) &&
  (!key || match (T.msgCells m)[1]? with
    | some (some k) => T.slots[k]? == some .invocation
    | _ => false)

def Template2.checkSpan (ls : List (LaneUse F)) (L : Nat) (sp : Span) : Bool :=
  1 ≤ sp.len && sp.start + sp.len ≤ L &&
    (List.range' (sp.start + 1) (sp.len - 1)).all fun l =>
      match ls[l]? with
      | some (.gate lane) => lane.qm == 0
      | _ => true

def Template2.checkRow (T : Template2 F) (buses : Buses F) : Row2 F → Bool
  | .gate ls spans =>
      ls.length == lanes T.width &&
        ls.all (fun
          | .gate lane => lane.qid == 0
          | .message m => T.laneMessageOk buses m
          | .empty => true) &&
        spans.all (Template2.checkSpan ls (lanes T.width)) &&
        decide (spans.map (·.start)).Nodup
  | .message m key => T.rowMessageOk buses m key

/-- Virtual slot `v` is `k + c·x` for a physical slot `x`, or a constant `k`. -/
def Template2.virtualOk (T : Template2 F) (v : Nat) : Bool :=
  match T.slots[v]? with
  | some (.sum [.linear _ x] _) => x < T.slots.length && T.slots[x]? != some .invocation && !T.virtual.contains x
  | some (.sum [] _) => true
  | _ => false

/-- The physical conditions of a v2 template; the logical template is checked
by `System.checkKeyed` of the logical system. -/
def Template2.checkPhysical (T : Template2 F) (buses : Buses F) : Bool :=
  T.rows.all (fun r => (T.rowCells r).all fun c => c.all fun s =>
    s < T.slots.length && T.slots[s]? != some .invocation) &&
  T.rows.all (T.checkRow buses) &&
  decide T.refs.Nodup && T.refs.length == T.messages.length && T.refs.all (· < T.messages.length)

/-- Virtual slots: no physical cell holds one, each is `k + c·x` for a physical
slot `x` or a constant, and a message whose multiplicity is virtual has
`sel = 1`. -/
def Template2.checkVirtual [One F] (T : Template2 F) : Bool :=
  T.rows.all (fun r => (T.rowCells r).all fun c => c.all fun s => !T.virtual.contains s) &&
  T.virtual.all T.virtualOk &&
  T.messages.all fun (sel, _, _, cells) => match cells with
    | some v :: _ => !T.virtual.contains v || sel == (1 : F)
    | _ => true

end Check

section Booleans

variable [CommRing F] [DecidableEq F]

/-- `(k + c·X_x)² − (k + c·X_x)`. -/
def virtualBoolPoly (c : F) (x : Nat) (k : F) : Poly F :=
  let d : Poly F := [([x], c), ([], k)]
  Poly.sub (Poly.mul d d) d

/-- The relation of span `sp` of a gate row with lanes `ls`, as its logical row states it. -/
def Template2.spanPoly (T : Template2 F) (ls : List (LaneUse F)) (sp : Span) : Poly F :=
  (spanLanes T.width ls sp).flatMap (Lane.poly T.slots.length)

/-- Virtual slot `v` is boolean on every instance: a constant `k` with
`k² = k`, or `k + c·x` with a span whose relation is identical to
`(k + c·x)² − (k + c·x)`. -/
def Template2.boolOk (T : Template2 F) (v : Nat) : Bool :=
  T.virtual.contains v &&
    match T.slots[v]? with
    | some (.sum [.linear c x] k) => T.rows.any fun
        | .gate ls spans => spans.any fun sp => Poly.Identical (T.spanPoly ls sp) (virtualBoolPoly c x k)
        | .message .. => false
    | some (.sum [] k) => k * k == k
    | _ => false

def Template2.checkBool (T : Template2 F) : Bool := T.booleans.all T.boolOk

end Booleans

/-! ## Fixed columns of one physical row -/

section Fixed

variable [Zero F] [One F] [NatCast F] [DecidableEq F]

def _root_.Aiur.Tiling.Lane.gateCoef (lane : Lane F) : Nat → F
  | 0 => lane.qm
  | 1 => lane.q0
  | 2 => lane.q1
  | 3 => lane.q2
  | 4 => lane.q3
  | 5 => lane.qc
  | _ => 0

/-- Gate coefficient `m` of lane `l`. A key row's lane 0 is the span `x1 = 0`. -/
def Row2.gateCoef : Row2 F → Nat → Nat → F
  | .gate ls _, l, m =>
      match ls[l]? with
      | some (.gate lane) => lane.gateCoef m
      | _ => 0
  | .message _ key, l, m => if key = true ∧ l = 0 ∧ m = 2 then 1 else 0

/-- Span flag `M_{l,l'}`. -/
def Row2.flag : Row2 F → Nat → Nat → F
  | .gate _ spans, l, l' => if spans.any (fun sp => sp.start == l && decide (l' < sp.start + sp.len)) then 1 else 0
  | .message _ key, l, l' => if key = true ∧ l = 0 ∧ l' = 0 then 1 else 0

/-- Lane message column `k` (`ts, mk, mc`) of lane `l`. -/
def Row2.laneMsg (T : Template2 F) (buses : Buses F) : Row2 F → Nat → Nat → F
  | .gate ls _, l, k =>
      match ls[l]? with
      | some (.message m) =>
          match T.messages[m]? with
          | some (_, tag, sub, _) => [codeOf buses (tag, sub), (T.physMult m).1, (T.physMult m).2.1].getD k 0
          | none => 0
      | _ => 0
  | .message .., _, _ => 0

/-- Row message column `k` (`ts, mk, mc, rkey, kf`), for an instance with local id `id`. -/
def Row2.rowMsg (T : Template2 F) (buses : Buses F) (id : F) : Row2 F → Nat → F
  | .message m key, k =>
      match T.messages[m]? with
      | some (_, tag, sub, _) =>
          [codeOf buses (tag, sub), (T.physMult m).1, (T.physMult m).2.1, if key then id else 0,
            if key then 1 else 0].getD k 0
      | none => 0
  | .gate .., _ => 0

/-- A fixed row in column order: gates, flags, lane messages, row message,
labels, multiplicities. -/
def fixedRow (W : Nat) (gate flag laneMsg : Nat → Nat → F) (rowMsg label mult : Nat → F) : List F :=
  (List.range (lanes W)).flatMap (fun l => (List.range 6).map (gate l)) ++
  (List.range (lanes W)).flatMap (fun l => (List.range (flagBlock W l)).map fun d => flag l (l + d)) ++
  (List.range (lanes W)).flatMap (fun l => (List.range 3).map (laneMsg l)) ++
  (List.range 5).map rowMsg ++ (List.range W).map label ++ (List.range W).map mult

end Fixed

/-! ## Layouts and sharded systems -/

/-- One shard's circuits, templates and instance counts. Shards with equal
layouts have equal fixed matrices. -/
structure Layout (F : Type) where
  circuits : List (Circuit F)
  templates : List (Template2 F)
  caps : List Nat

def Layout.shadow [Zero F] (W : Nat) (L : Layout F) : System F where
  width := W
  circuits := L.circuits
  templates := L.templates.map Template2.shadow
  caps := L.caps

structure Sharded (F : Type) where
  width : Nat
  shards : List (Layout F)
  buses : Buses F

namespace Sharded

variable (S : Sharded F)

/-- The logical system: every shard's logical templates, shard by shard. -/
def system [DecidableEq F] [Zero F] [One F] [Neg F] : System F where
  width := S.width
  circuits := S.shards.flatMap (·.circuits)
  templates := S.shards.flatMap fun L => L.templates.map Template2.logical
  caps := S.shards.flatMap (·.caps)

def shadow [Zero F] (k : Nat) : System F := ((S.shards[k]?).getD ⟨[], [], []⟩).shadow S.width

/-- Copy labels of shard `k` start after those of earlier shards. -/
def labelOffset [Zero F] (k : Nat) : Nat :=
  ((List.range k).map fun k' => (S.shadow k').keys.length + 1).sum

/-- The index of shard `k`'s first circuit in the logical system. -/
def base (k : Nat) : Nat := ((S.shards.take k).map (·.templates.length)).sum

/-- Invocation ids of shard `k` start after those of earlier shards: at the
logical system's id of the shard's first instance. -/
def idOffset [DecidableEq F] [Zero F] [One F] [Neg F] (k : Nat) : Nat := S.system.instId (S.base k) 0

def check [Field F] [DecidableEq F] : Bool :=
  S.system.checkKeyed &&
    S.shards.all (fun L => L.circuits.length == L.templates.length &&
      L.caps.length == L.templates.length &&
      L.templates.all fun T => T.width == S.width && T.checkPhysical S.buses) &&
    decide (S.buses.map (·.1)).Nodup && decide (S.buses.map (·.2.1)).Nodup &&
    (S.buses.all fun e => e.2.1 % 4 == 1 || e.2.1 % 4 == 2) &&
    S.shards.all fun L => L.templates.all fun T => T.checkVirtual && T.checkBool

variable [Field F] [DecidableEq F]

/-- Fixed column `c` of physical row `p` of layout `L`: the same for every
shard of that layout. -/
def fixedAt (L : Layout F) (p c : Nat) : F :=
  let sh := L.shadow S.width
  match sh.places[p]? with
  | some (f, i, r) =>
      match L.templates[f]? with
      | some T =>
          match T.rows[r]? with
          | some row =>
              ((fixedRow S.width row.gateCoef row.flag (row.laneMsg T S.buses)
                (row.rowMsg T S.buses (sh.instId f i : F)) (sh.labelAt p) (sh.multAt p))[c]?).getD 0
          | none => 0
      | none => 0
  | none => 0

def layout (k : Nat) : Layout F := (S.shards[k]?).getD ⟨[], [], []⟩

/-- Main row `p` of shard `k` with the layout's fixed columns. -/
def assign (k : Nat) (main : Nat → Nat → F) (p : Nat) (v : Var) : F :=
  if v < S.width then main p v else S.fixedAt (S.layout k) p (v - S.width)

/-- The circuit of shard `k`. -/
def circuit (k : Nat) : Circuit F := narrowCircuit S.width (S.labelOffset k) (S.idOffset k)

/-- All lookups of all shards; shard `k` has `H k` rows. -/
noncomputable def ledger (H : Nat → Nat) (main : Nat → Nat → Nat → F) : Ledger F :=
  ∑ k ∈ Finset.range S.shards.length, ∑ p ∈ Finset.range (H k),
    (S.circuit k).rowLedger (S.assign k (main k) p)

end Sharded

end Aiur.Tiling.Periodic
