import IxCC.Aiur.Field

/-! Exact messages and field-weighted balance for an extracted Aiur trace.

Rows here are the logical projection of a satisfying assignment. Establishing
that projection from the keyed AIR remains a separate theorem. Provider
multiplicities are field elements, including negative values; unit demands
are counted in Nat and embedded only when expressing lookup balance.
-/

namespace IxCC.Aiur

open _root_.IxCC.Vendor.Aiur (G gSize)

inductive Message where
  | function (function : Nat) (inputs outputs : List G)
  | memory (bucket : Nat) (pointer : G) (values : List G)
  | gadget (channel : Nat) (values : List G)
  deriving DecidableEq, Repr

structure Row where
  active : Bool
  provides : Message
  multiplicity : G
  demands : List Message
  deriving DecidableEq, Repr

structure Trace where
  rows : List Row
  publicClaims : List Message
  deriving DecidableEq, Repr

namespace Trace

abbrev RowId (trace : Trace) := Fin trace.rows.length

def row (trace : Trace) (id : trace.RowId) : Row := trace.rows[id.val]

/-- Inactive rows do not create demands. Duplicate messages count repeatedly. -/
def requirements (trace : Trace) : List Message :=
  trace.publicClaims ++ trace.rows.flatMap fun row => if row.active then row.demands else []

def demandCount (trace : Trace) (message : Message) : Nat :=
  trace.requirements.count message

def providerSum (message : Message) : List Row → G
  | [] => 0
  | row :: rows =>
    (if row.provides = message then row.multiplicity else 0) + providerSum message rows

/-- The free activity constraint extracted from function/memory/gadget AIR. -/
def Activity (trace : Trace) : Prop :=
  ∀ row ∈ trace.rows, row.multiplicity ≠ 0 → row.active = true

def Balanced (trace : Trace) : Prop :=
  ∀ message, G.ofNat (trace.demandCount message) = providerSum message trace.rows

/-- One provider slot per row, plus active unit demands and public claims.
The AIR adapter must bound this by the verifier's checked slot budget; the
Rust budget also counts provider slots and inactive padding rows. -/
def unitSlots (trace : Trace) : Nat := trace.rows.length + trace.requirements.length

def WithinCharacteristic (trace : Trace) : Prop := trace.unitSlots < gSize.toNat

instance (trace : Trace) : Decidable trace.WithinCharacteristic :=
  inferInstanceAs (Decidable (trace.unitSlots < gSize.toNat))

/-- `child` provides one active unit demand of `parent`, with nonzero weight.
The same message may have multiple providers; no choice is baked into the relation. -/
def Requires (trace : Trace) (child parent : trace.RowId) : Prop :=
  (trace.row parent).active = true ∧
  (trace.row child).active = true ∧
  (trace.row child).multiplicity ≠ 0 ∧
  (trace.row child).provides ∈ (trace.row parent).demands

instance (trace : Trace) : DecidableRel trace.Requires := fun _ _ => by
  unfold Requires
  infer_instance

theorem row_mem (trace : Trace) (id : trace.RowId) : trace.row id ∈ trace.rows := by
  exact List.getElem_mem _

theorem rows_lt (trace : Trace) (bound : trace.WithinCharacteristic) :
    trace.rows.length < gSize.toNat := by
  unfold WithinCharacteristic unitSlots at bound
  omega

end Trace
end IxCC.Aiur
