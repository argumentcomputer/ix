import Aiur.Tiling.Basic
import Aiur.Tiling.Poly

/-!
# Templates

A template is one wide circuit's row laid out as a fixed sequence of narrow
rows. Every value it needs is a *slot*: a wide main column, or a sum of
linear and product terms over earlier slots. A narrow row's cells name the
slots they hold; copy constraints make every cell of a slot carry one value.

Gate rows hold four-cell lanes
`qm·x0·x1 + q0·x0 + q1·x1 + q2·x2 + q3·x3 + qc`. An unjoined row requires
every lane to vanish; a joined row requires their sum to vanish. Each
resulting relation is labelled with a `Role` that the checker validates: it
defines a sum slot, it is a wide constraint, or it is padding.

A message row holds one wide lookup: multiplicity `sel·x0` and tuple
`[tag, sub, x1, …, x(W-1)]`, where the cells after the payload are unused.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Constraint Satisfies)

inductive Term (F : Type) where
  | linear (c : F) (s : Nat)
  | product (c : F) (s t : Nat)
  deriving Repr, DecidableEq

inductive SlotDef (F : Type) where
  | column (c : Nat)
  | sum (terms : List (Term F)) (k : F)
  /-- The instance's invocation id, the receive key of a chunked call. -/
  | invocation
  /-- A free key (callee id, table row or ROM address) of chunked message `message`. -/
  | key (message : Nat)
  deriving Repr, DecidableEq

structure Lane (F : Type) where
  qm : F
  q0 : F
  q1 : F
  q2 : F
  q3 : F
  qc : F
  c0 : Option Nat
  c1 : Option Nat
  c2 : Option Nat
  c3 : Option Nat
  /-- Coefficient of the instance's invocation id, folded into `qc` per instance. -/
  qid : F
  deriving Repr, DecidableEq

inductive Role where
  | pad
  | defines (s : Nat)
  | root (j : Nat)
  /-- Pins an invocation slot to the instance's id. -/
  | pin (s : Nat)
  /-- Booleanity of the multiplicity of a chunked send. -/
  | boolean (s : Nat)
  deriving Repr, DecidableEq

inductive Row (F : Type) where
  | gate (lanes : List (Lane F)) (join : Bool) (roles : List Role)
  | message (sel tag sub : F) (cells : List (Option Nat))
  deriving Repr

structure Template (F : Type) where
  width : Nat
  slots : List (SlotDef F)
  rows : List (Row F)
  deriving Repr

variable {F : Type}

def Lane.zero [Zero F] : Lane F := ⟨0, 0, 0, 0, 0, 0, none, none, none, none, 0⟩

def Lane.cells (lane : Lane F) : List (Option Nat) := [lane.c0, lane.c1, lane.c2, lane.c3]

def Row.cells : Row F → List (Option Nat)
  | .gate lanes _ _ => lanes.flatMap Lane.cells
  | .message _ _ _ cells => cells

def Template.cell (T : Template F) (r j : Nat) : Option Nat :=
  match T.rows[r]? with
  | some row => (row.cells[j]?).getD none
  | none => none

/-! ## Relations as polynomials over slots -/

section Polys

variable [CommRing F]

def cellPoly (cell : Option Nat) (q : F) : Poly F :=
  match cell with
  | some s => [([s], q)]
  | none => []

/-- The lane's relation over slots. Variable `idv` stands for the instance's
invocation id, which the fixed `qc` column carries scaled by `qid`. -/
def Lane.poly [DecidableEq F] (idv : Nat) (lane : Lane F) : Poly F :=
  (match lane.c0, lane.c1 with
    | some a, some b => [(Mono.insert a [b], lane.qm)]
    | _, _ => []) ++
  cellPoly lane.c0 lane.q0 ++ cellPoly lane.c1 lane.q1 ++ cellPoly lane.c2 lane.q2 ++
    cellPoly lane.c3 lane.q3 ++ [([], lane.qc)] ++
    (if lane.qid = 0 then [] else [([idv], lane.qid)])

def Row.relations [DecidableEq F] (idv : Nat) : Row F → List (Role × Poly F)
  | .gate lanes true roles => [(roles.headD .pad, lanes.flatMap (Lane.poly idv))]
  | .gate lanes false roles => roles.zip (lanes.map (Lane.poly idv))
  | .message .. => []

def Term.poly : Term F → Poly F
  | .linear c s => [([s], c)]
  | .product c s t => [(Mono.insert s [t], c)]

/-- `Σ terms + k - slot`: the relation that defines a sum slot. -/
def defPoly (s : Nat) (terms : List (Term F)) (k : F) : Poly F :=
  Poly.const k ++ terms.flatMap Term.poly ++ [([s], -1)]

def Term.subst (f : Nat → Poly F) : Term F → Poly F
  | .linear c u => Poly.scale c (f u)
  | .product c u v => Poly.scale c (Poly.mul (f u) (f v))

def substTerms (f : Nat → Poly F) (terms : List (Term F)) : Poly F :=
  terms.flatMap (Term.subst f)

/-- The value of a slot as a polynomial over wide columns. -/
def Template.meaning (T : Template F) (s : Nat) : Poly F :=
  match T.slots[s]? with
  | some (.column c) => Poly.var c
  | some (.sum terms k) =>
      Poly.const k ++ substTerms (fun u => if _h : u < s then T.meaning u else []) terms
  | _ => []
termination_by s

/-- Slot `t` as a polynomial over slots, with every sum slot above `s`
replaced by its definition. A relation that defines `s` may be split across
rows linked by carry slots, which are created after `s`. -/
def Template.expandAbove (T : Template F) (s t : Nat) : Poly F :=
  match T.slots[t]? with
  | some (.sum terms k) =>
      if s < t then
        Poly.const k ++ substTerms (fun u => if _h : u < t then T.expandAbove s u else []) terms
      else Poly.var t
  | _ => Poly.var t
termination_by t

end Polys

/-! ## The checker -/

section Check

variable [CommRing F] [DecidableEq F]

def Term.slotsBelow (s : Nat) : Term F → Bool
  | .linear _ u => u < s
  | .product _ u v => u < s && v < s

def Template.colSlot (T : Template F) (c : Nat) : Option Nat :=
  T.slots.findIdx? (· == .column c)

def Lane.wellFormed (lane : Lane F) : Bool :=
  (lane.c0.isSome && lane.c1.isSome || lane.qm == 0) &&
    (lane.c0.isSome || lane.q0 == 0) && (lane.c1.isSome || lane.q1 == 0) &&
    (lane.c2.isSome || lane.q2 == 0) && (lane.c3.isSome || lane.q3 == 0)

def Row.wellFormed (width : Nat) : Row F → Bool
  | .gate lanes join roles =>
      lanes.length == width / 4 && lanes.all Lane.wellFormed &&
        (if join then roles.length == 1 else roles.length == lanes.length)
  | .message _ _ _ cells => cells.length == width

def Poly.slotsBelow (n : Nat) (p : Poly F) : Bool := p.all fun t => t.1.all (· < n)

/-- The expected cells of a message row for a lookup with `payload` slots. -/
def messageCells (width mult : Nat) (payload : List Nat) : List (Option Nat) :=
  some mult :: payload.map some ++ List.replicate (width - 1 - payload.length) none

/-- The variable of the invocation id in relations: one past the last slot. -/
def Template.idVar (T : Template F) : Nat := T.slots.length

def Template.relations (T : Template F) : List (Role × Poly F) :=
  T.rows.flatMap (Row.relations T.idVar)

/-- A slot that denotes a polynomial over the wide row. -/
def Template.wideSlot (T : Template F) (s : Nat) : Bool :=
  match T.slots[s]? with
  | some (.column _) | some (.sum _ _) => true
  | _ => false

def Template.wideTerm (T : Template F) : Term F → Bool
  | .linear _ u => T.wideSlot u
  | .product _ u v => T.wideSlot u && T.wideSlot v

def Template.widePoly (T : Template F) (p : Poly F) : Bool := p.all fun t => t.1.all T.wideSlot

def Template.checkSlot (T : Template F) (s : Nat) : SlotDef F → Bool
  | .column c => T.colSlot c == some s
  | .sum terms _ => terms.all (Term.slotsBelow s) && terms.all T.wideTerm &&
      T.relations.any fun rel => rel.1 == .defines s
  | .invocation => T.relations.any fun rel => rel.1 == .pin s
  | .key _ => true

def Template.checkRelation (T : Template F) (circuit : Circuit F) : Role × Poly F → Bool
  | (.pad, p) => (Poly.norm p).isEmpty
  | (.defines s, p) =>
      match T.slots[s]? with
      | some (.sum terms k) => Poly.Identical (Poly.subst (T.expandAbove s) p) (defPoly s terms k)
      | _ => false
  | (.root j, p) =>
      match circuit.constraints[j]? with
      | some constraint =>
          T.widePoly p && Poly.Identical (Poly.subst T.meaning p) (Poly.ofExpr constraint)
      | none => false
  | (.pin s, p) =>
      T.slots[s]? == some .invocation && Poly.Identical p (Poly.sub (Poly.var s) (Poly.var T.idVar))
  | (.boolean _, _) => true

def Template.checkConstraint (T : Template F) (j : Nat) (constraint : ArithExpr F) : Bool :=
  (Poly.norm (Poly.ofExpr constraint)).isEmpty || T.relations.any fun rel => rel.1 == .root j

def Template.messages (T : Template F) : List (F × F × F × List (Option Nat)) :=
  T.rows.filterMap fun
    | .message sel tag sub cells => some (sel, tag, sub, cells)
    | .gate .. => none

def allPairs (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && allPairs f as bs
  | _, _ => false

def Template.checkMessage (T : Template F) (message : F × F × F × List (Option Nat))
    (lookup : Lookup F) : Bool :=
  let (sel, tag, sub, cells) := message
  match lookup.args, cells with
  | tagExpr :: subExpr :: payload, some mult :: rest =>
      let slots := (rest.take payload.length).filterMap id
      Poly.Identical (Poly.ofExpr tagExpr) (Poly.const tag) &&
        Poly.Identical (Poly.ofExpr subExpr) (Poly.const sub) &&
        payload.length + 1 ≤ T.width &&
        cells == messageCells T.width mult slots &&
        T.wideSlot mult &&
        Poly.Identical (Poly.scale sel (T.meaning mult)) (Poly.ofExpr lookup.multiplicity) &&
        allPairs (fun s expr => T.wideSlot s && Poly.Identical (T.meaning s) (Poly.ofExpr expr))
          slots payload
  | _, _ => false

/-! ### Keyed chunks

A lookup whose payload does not fit one row travels as a group of `J ≥ 2`
message rows `[mult, key, chunk_c, …]` with `sub_c = sub + offset c`. A ROM
lookup is keyed by its address (the first payload entry) and chunks the rest;
a ROM receive's address must be a constant, so that the system checker can
compare the keys of all ROM receivers. A call receive is keyed by the
instance's invocation slot; any other send by a free key slot. A send's multiplicity is constrained boolean by a relation
of role `boolean mult`. -/

/-- Message rows of a lookup with `n` payload entries. -/
def groupSize (W n : Nat) (rom : Bool) : Nat :=
  if n + 1 ≤ W then 1
  else if rom then (n - 1 + (W - 2) - 1) / (W - 2) else (n + (W - 2) - 1) / (W - 2)

def chunkStride : Nat := 2 ^ 32

/-- The `sub` of chunk `c`: ROM chunks start at offset 0, call chunks at 1. -/
def chunkSub (rom : Bool) (sub : F) (c : Nat) : F :=
  sub + ((if rom then c else c + 1 : Nat) : F) * (chunkStride : F)

def keyedCells (W mult key : Nat) (chunk : List Nat) : List (Option Nat) :=
  some mult :: some key :: chunk.map some ++ List.replicate (W - 2 - chunk.length) none

def Template.messageRom (m : F × F × F × List (Option Nat)) : Bool := m.2.1 == 2

/-- Consecutive message rows, one group per lookup. -/
def Template.splitGroups (W : Nat) :
    List (F × F × F × List (Option Nat)) → List (Lookup F) → List (List (F × F × F × List (Option Nat)))
  | _, [] => []
  | ms, l :: ls =>
      let J := groupSize W (l.args.length - 2) ((ms.head?.map Template.messageRom).getD false)
      ms.take J :: Template.splitGroups W (ms.drop J) ls

/-- `(sel·X_m)² − sel·X_m`. -/
def boolPoly (sel : F) (m : Nat) : Poly F := [([m, m], sel * sel), ([m], -sel)]

def Template.chunkCells (m : F × F × F × List (Option Nat)) : List Nat := (m.2.2.2.drop 2).filterMap id

def Template.checkChunked (T : Template F) (receive : Bool) (group : List (F × F × F × List (Option Nat)))
    (lookup : Lookup F) : Bool :=
  match lookup.args, group with
  | tagExpr :: subExpr :: payload, (sel, tag, sub0, some mult :: some key :: _) :: _ =>
      let rom := tag == 2
      let sub := sub0 - chunkSub rom 0 0
      let values := if rom then payload.drop 1 else payload
      2 ≤ group.length &&
        Poly.Identical (Poly.ofExpr tagExpr) (Poly.const tag) &&
        Poly.Identical (Poly.ofExpr subExpr) (Poly.const sub) &&
        group.zipIdx.all (fun (m, c) => m.1 == sel && m.2.1 == tag && m.2.2.1 == chunkSub rom sub c &&
          (Template.chunkCells m).length + 2 ≤ T.width &&
          m.2.2.2 == keyedCells T.width mult key (Template.chunkCells m)) &&
        T.wideSlot mult &&
        Poly.Identical (Poly.scale sel (T.meaning mult)) (Poly.ofExpr lookup.multiplicity) &&
        allPairs (fun s expr => T.wideSlot s && Poly.Identical (T.meaning s) (Poly.ofExpr expr))
          (group.flatMap Template.chunkCells) values &&
        (if rom then
            T.wideSlot key &&
              (match payload with
                | a :: _ => Poly.Identical (T.meaning key) (Poly.ofExpr a)
                | [] => false)
          else if receive then T.slots[key]? == some .invocation
          else key < T.slots.length) &&
        (if receive then
          (if rom then (match payload with | .const _ :: _ => true | _ => false) else true)
        else T.relations.any fun rel => rel.1 == .boolean mult && Poly.Identical rel.2 (boolPoly sel mult))
  | _, _ => false

def Template.checkGroup (T : Template F) (receive : Bool) (group : List (F × F × F × List (Option Nat)))
    (lookup : Lookup F) : Bool :=
  match group with
  | [m] => T.checkMessage m lookup
  | _ => T.checkChunked receive group lookup

def Template.checkGroups (T : Template F) (circuit : Circuit F) : Bool :=
  let groups := Template.splitGroups T.width T.messages circuit.lookups
  groups.flatten == T.messages &&
    allPairs (fun (g, l) lookup => T.checkGroup (l == 0) g lookup) groups.zipIdx circuit.lookups

/-- One message row per lookup: no chunked group. -/
def Template.checkUnchunked (T : Template F) (circuit : Circuit F) : Bool :=
  T.messages.length == circuit.lookups.length &&
    (T.messages.zip circuit.lookups).all fun (m, l) => T.checkMessage m l

/-- Validation of a template against the wide circuit it tiles. -/
def Template.check (T : Template F) (circuit : Circuit F) : Bool :=
  4 ≤ T.width && T.width % 4 == 0 &&
    T.rows.all (Row.wellFormed T.width) &&
    T.rows.all (fun row => row.cells.all fun cell => cell.all (· < T.slots.length)) &&
    T.slots.zipIdx.all (fun (d, s) => T.checkSlot s d) &&
    T.relations.all (T.checkRelation circuit) &&
    circuit.constraints.zipIdx.all (fun (p, j) => T.checkConstraint j p) &&
    (T.checkUnchunked circuit || T.checkGroups circuit)

end Check

end Aiur.Tiling
