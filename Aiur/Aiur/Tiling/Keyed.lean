import Aiur.Tiling.Refinement

/-!
# Systems with keyed chunks

`System.checkKeyed` is `System.check` without the unchunked restriction: every
template is validated group by group (`Template.checkGroups`), and every row
key `(tag, sub_row)` of the narrow message bus has one *role*: the `sub` of
the wide channel it belongs to, and, for a chunk row, its chunk index, the
group's chunk count and whether the channel is a ROM read. A functional role
table makes chunk tuples of different chunks or channels distinct, and keeps
unchunked rows off chunk tuples, without any bound on the field's
characteristic.
-/

namespace Aiur.Tiling

variable {F : Type} [CommRing F] [DecidableEq F]

/-- Role of a message row: wide `sub`, and `(chunk, count, rom)` for a chunk row. -/
abbrev RowRole (F : Type) := F × Option (Nat × Nat × Bool)

/-- Row keys and roles of one message group. -/
def groupRoles (g : List (F × F × F × List (Option Nat))) : List ((F × F) × RowRole F) :=
  match g with
  | [m] => [((m.2.1, m.2.2.1), (m.2.2.1, none))]
  | m :: _ =>
      let rom := Template.messageRom m
      let sub := m.2.2.1 - chunkSub rom 0 0
      g.zipIdx.map fun (m', c) => ((m'.2.1, m'.2.2.1), (sub, some (c, g.length, rom)))
  | [] => []

namespace System

variable (sys : System F)

def groups (T : Template F) (C : Circuit F) : List (List (F × F × F × List (Option Nat))) :=
  Template.splitGroups T.width T.messages C.lookups

def roles : List ((F × F) × RowRole F) :=
  (sys.templates.zip sys.circuits).flatMap fun (T, C) => (groups T C).flatMap groupRoles

/-- The constant address of a ROM receive: argument 2 of lookup 0. -/
def romAddress (C : Circuit F) : Option F :=
  match C.lookups with
  | L :: _ =>
      match L.args with
      | _ :: _ :: .const k :: _ => some k
      | _ => none
  | [] => none

/-- Chunked ROM receivers: circuit, channel `(tag, sub)` and constant address. -/
def romReceivers : List (Nat × (F × F) × F) :=
  ((sys.templates.zip sys.circuits).zipIdx).filterMap fun ((T, C), f) =>
    match groups T C, romAddress C with
    | (m :: _ :: _) :: _, some k =>
        if Template.messageRom m then some (f, (m.2.1, m.2.2.1 - chunkSub true 0 0), k) else none
    | _, _ => none

/-- `System.check` for layouts with keyed chunks. Chunked ROM receivers are
keyed by their constant address, so each has one instance and the addresses
of one channel are distinct. -/
def checkKeyed : Bool :=
  4 ≤ sys.width && sys.width % 4 == 0 &&
  sys.circuits.length == sys.templates.length && sys.caps.length == sys.templates.length &&
    (sys.templates.zip sys.circuits).all (fun (T, C) =>
      T.width == sys.width && T.check C && T.checkGroups C) &&
    sys.arities.all (fun (key, n) => sys.arities.lookup key == some n) &&
    sys.arities.all (fun (key, _) => key.1 != (COPY : F)) &&
    sys.roles.all (fun (key, r) => sys.roles.lookup key == some r) &&
    decide (sys.romReceivers.map (·.2)).Nodup &&
    sys.romReceivers.all fun x => sys.cap x.1 ≤ 1

end System

/-- Lower and lay out given circuits, validated by `System.checkKeyed`. -/
def tileKeyed (width : Nat) (circuits : List (Circuit F)) (caps : List Nat) :
    Except String (System F) := do
  let templates ← circuits.mapM fun C => lower (Graph.ofCircuit C) width
  let sys : System F := { width, circuits, templates, caps }
  unless sys.checkKeyed do throw "tiled system failed keyed validation"
  return sys

section Sound

variable {F : Type} [Field F] [DecidableEq F]

theorem System.valid_of_checkKeyed {sys : System F} (ok : sys.checkKeyed = true) : sys.Valid := by
  simp only [System.checkKeyed, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨w4, wmod⟩, len1⟩, len2⟩, temps⟩, ar⟩, tg⟩, _⟩, _⟩, _⟩ := ok
  refine ⟨⟨of_decide_eq_true w4, wmod⟩, ⟨len1, len2⟩, ?_,
    fun e he => by simpa using ar e he, fun e he => by simpa using tg e he⟩
  intro f h hc
  have mem : (sys.templates[f], sys.circuits[f]) ∈ sys.templates.zip sys.circuits := by
    rw [List.mem_iff_getElem]
    exact ⟨f, by simp [h, hc], by simp⟩
  have := temps _ mem
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, Template.checked_of_check _ this.1.2⟩

/-- **Constraints of a keyed layout.** A narrow trace of a system accepted by
`checkKeyed`, whose copy bus balances, reconstructs wide rows that satisfy
their circuits; chunked templates included. -/
theorem System.keyed_holds {sys : System F} (ok : sys.checkKeyed = true)
    (small : SmallCast F sys.bound) {N : Nat} (tall : sys.places.length ≤ N) {main : Nat → Nat → F}
    (rows : ∀ p < N, Scalar.Circuit.Satisfies (narrowCircuit (F := F) sys.width).constraints
      (sys.assign main p))
    {ext : Ledger F} (extCopy : ∀ L v, ext [(COPY : F), L, v] = 0)
    (balanced : sys.narrowLedger N main + ext = 0) :
    ∀ f (hf : f < sys.circuits.length), ∀ i < sys.cap f,
      sys.circuits[f].Holds (sys.wideRow main f i) := by
  have valid := sys.valid_of_checkKeyed ok
  obtain ⟨_, _, copies⟩ := System.copy_balance valid valid.width.1 extCopy balanced
  have trace : sys.Trace N main := ⟨valid, small, tall, rows, copies⟩
  exact fun f hf i hi => trace.wide_holds hf hi

end Sound

end Aiur.Tiling
