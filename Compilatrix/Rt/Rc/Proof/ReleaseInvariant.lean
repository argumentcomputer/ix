import Compilatrix.Rt.Rc.Proof.Cursor
import Compilatrix.Rt.Rc.Proof.FreeList
import Compilatrix.Rt.Rc.Proof.PendingBalance

/-! Concrete release cutpoint invariant. This is data about heap cells,
bytes, permissions, slot coverage, linked free lists, and pending tokens.
No field assumes a machine simulation or successful release. -/
namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Proof

structure CursorFrame where
  location : Nat
  address : Word
  original : Own.Body
  before : X86.Memory
  visited : Nat

def CursorFrame.suffix (frame : CursorFrame) : List RVal :=
  frame.original.fields.drop frame.visited
def cursorHead (frames : List CursorFrame) : Word :=
  match frames with | [] => 0 | frame :: _ => frame.address
def cursorTokens (frames : List CursorFrame) : List RVal :=
  flattenPending (frames.map CursorFrame.suffix)

def CursorChain (addresses : AddressMap) (heap : Heap) (mem : X86.Memory) :
    List CursorFrame → Prop
  | [] => True
  | frame :: tail =>
    heap.cell? frame.location = some .dead ∧
    PendingCursor addresses frame.before mem frame.address (cursorHead tail)
      frame.original frame.visited ∧
    frame.address.toNat + cellBytes frame.original.fields.length < 2^63 ∧
    CursorChain addresses heap mem tail

structure ReleaseInvariant (heap : Heap) (addresses : AddressMap) (mem : X86.Memory)
    (external : Nat → Nat) (current : Option RVal) (frames : List CursorFrame)
    (context base bump limit : Word) (slots : List Slot) (freeLists : Nat → List Word) : Prop where
  balance : Balance heap external (current.toList ++ cursorTokens frames)
  live : HeapLive heap addresses mem
  partition : ArenaPartition heap addresses base bump limit slots
  cursors : CursorChain addresses heap mem frames
  cursor_distinct : (frames.map CursorFrame.address).Nodup
  cursor_nonzero : ∀ frame ∈ frames, frame.address ≠ 0
  cursor_access : ∀ frame ∈ frames, ∀ j < cellBytes frame.original.fields.length,
    mem.readable (frame.address+UInt64.ofNat j) = true ∧
      mem.writable (frame.address+UInt64.ofNat j) = true
  cursor_class : ∀ frame ∈ frames,
    mem.bytes (frame.address+1) = (UInt64.ofNat (smallClass frame.original.fields.length)).toUInt8
  cursors_placed : ∀ earlier frame tail, frames = earlier ++ frame :: tail →
    ∃ slot ∈ slots, slot.address = frame.address ∧
      slot.cls = smallClass frame.original.fields.length ∧
      slot.kind = .pending frame.location frame.suffix (cursorHead tail)
  pending_exact : ∀ slot ∈ slots, ∀ location suffix predecessor,
    slot.kind = .pending location suffix predecessor ↔
      ∃ earlier frame tail, frames = earlier ++ frame :: tail ∧
        frame.location = location ∧ frame.address = slot.address ∧
        slot.cls = smallClass frame.original.fields.length ∧
        frame.suffix = suffix ∧ predecessor = cursorHead tail
  free_exact : ∀ slot ∈ slots,
    slot.kind = .free ↔ slot.address ∈ freeLists slot.cls
  free_distinct : ∀ cls, (freeLists cls).Nodup
  free_placed : ∀ cls address, address ∈ freeLists cls →
    ∃ slot ∈ slots, slot.address = address ∧ slot.cls = cls ∧ slot.kind = .free
  free_chains : ∀ cls, FreeChain mem (freeLists cls)
  free_heads : ∀ cls, 1 ≤ cls → cls ≤ 32 →
    WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) ((freeLists cls).headD 0)
  head_writable : ∀ cls, 1 ≤ cls → cls ≤ 32 → ∀ j < 8,
    mem.writable (freeHeadAddress context (UInt64.ofNat cls)+UInt64.ofNat j) = true
  head_fit : ∀ cls, 1 ≤ cls → cls ≤ 32 →
    (freeHeadAddress context (UInt64.ofNat cls)).toNat+8 ≤ 2^64
  context_fit : context.toNat+8*33 < 2^63
  head_disjoint : ∀ cls, 1 ≤ cls → cls ≤ 32 → ∀ slot ∈ slots,
    (freeHeadAddress context (UInt64.ofNat cls)).toNat+8 ≤ slot.address.toNat ∨
      slot.address.toNat+8*slot.cls ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat

/-- Every logical pending location is live before it is visited. This follows
from numeric balance, including duplicate tokens, rather than a caller's
promise that all traversal loads are safe. Physical placement follows from
the independent HeapLive component. -/
theorem balance_pending_live {heap : Heap} {external : Nat → Nat} {pending : List RVal}
    (hb : Balance heap external pending) {location : Nat} (hm : RVal.loc location ∈ pending) :
    ∃ refs body, heap.cell? location = some (.live refs .dyn body) ∧ 0 < refs := by
  have hp := refsIn_pos hm
  have he := hb location
  cases hc : heap.cell? location with
  | none => simp [dynCount, hc] at he; omega
  | some cell =>
    cases cell with
    | dead => simp [dynCount, hc] at he; omega
    | live refs mode body =>
      cases mode with
      | static => simp [dynCount, hc] at he; omega
      | dyn =>
        refine ⟨refs, body, rfl, ?_⟩
        simp only [dynCount, hc] at he
        omega


end Compilatrix.Rt.Rc.Procs
