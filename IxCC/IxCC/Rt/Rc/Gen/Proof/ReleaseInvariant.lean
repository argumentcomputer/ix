import IxCC.Rt.Rc.Gen.Proof.Cursor
import IxCC.Rt.Rc.Proof.ReleaseInvariant

/-! The release cutpoint invariant for cells of any layout: `Procs.ReleaseInvariant` with the
general live cells, partition and cursors, sizes from `classWords`, every slot's class at most
`cmax`, and the free-list heads of all 71 classes. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof

def CursorChain (addresses : AddressMap) (heap : Heap) (mem : X86.Memory) :
    List CursorFrame → Prop
  | [] => True
  | frame :: tail =>
    heap.cell? frame.location = some .dead ∧
    PendingCursor addresses frame.before mem frame.address (cursorHead tail)
      frame.original frame.visited ∧
    frame.address.toNat + cellBytesOf frame.original.ctor < 2^63 ∧
    CursorChain addresses heap mem tail

structure ReleaseInvariant (cmax : Nat) (heap : Heap) (addresses : AddressMap) (mem : X86.Memory)
    (external : Nat → Nat) (current : Option RVal) (frames : List CursorFrame)
    (context base bump limit : Word) (slots : List Slot) (freeLists : Nat → List Word) : Prop where
  balance : Balance heap external (current.toList ++ cursorTokens frames)
  live : HeapLive heap addresses mem
  partition : ArenaPartition cmax heap addresses base bump limit slots
  cursors : CursorChain addresses heap mem frames
  cursor_distinct : (frames.map CursorFrame.address).Nodup
  cursor_nonzero : ∀ frame ∈ frames, frame.address ≠ 0
  cursor_layout : ∀ frame ∈ frames, (layoutOf frame.original.ctor).ok = true
  cursor_access : ∀ frame ∈ frames, ∀ j < cellBytesOf frame.original.ctor,
    mem.readable (frame.address+UInt64.ofNat j) = true ∧
      mem.writable (frame.address+UInt64.ofNat j) = true
  cursor_class : ∀ frame ∈ frames,
    mem.bytes (frame.address+1) = (UInt64.ofNat (classOf frame.original.ctor)).toUInt8
  cursor_scan : ∀ frame ∈ frames,
    mem.bytes frame.address = (UInt64.ofNat frame.original.ctor.nobj).toUInt8
  cursors_placed : ∀ earlier frame tail, frames = earlier ++ frame :: tail →
    ∃ slot ∈ slots, slot.address = frame.address ∧
      slot.cls = classOf frame.original.ctor ∧
      slot.kind = .pending frame.location frame.suffix (cursorHead tail)
  pending_exact : ∀ slot ∈ slots, ∀ location suffix predecessor,
    slot.kind = .pending location suffix predecessor ↔
      ∃ earlier frame tail, frames = earlier ++ frame :: tail ∧
        frame.location = location ∧ frame.address = slot.address ∧
        slot.cls = classOf frame.original.ctor ∧
        frame.suffix = suffix ∧ predecessor = cursorHead tail
  free_exact : ∀ slot ∈ slots,
    slot.kind = .free ↔ slot.address ∈ freeLists slot.cls
  free_distinct : ∀ cls, (freeLists cls).Nodup
  free_placed : ∀ cls address, address ∈ freeLists cls →
    ∃ slot ∈ slots, slot.address = address ∧ slot.cls = cls ∧ slot.kind = .free
  free_chains : ∀ cls, FreeChain mem (freeLists cls)
  free_heads : ∀ cls, 1 ≤ cls → cls ≤ maxClass →
    WordAt mem (freeHeadAddress context (UInt64.ofNat cls)) ((freeLists cls).headD 0)
  head_writable : ∀ cls, 1 ≤ cls → cls ≤ maxClass → ∀ j < 8,
    mem.writable (freeHeadAddress context (UInt64.ofNat cls)+UInt64.ofNat j) = true
  head_fit : ∀ cls, 1 ≤ cls → cls ≤ maxClass →
    (freeHeadAddress context (UInt64.ofNat cls)).toNat+8 ≤ 2^64
  context_fit : context.toNat+8*(maxClass+1) < 2^63
  head_disjoint : ∀ cls, 1 ≤ cls → cls ≤ maxClass → ∀ slot ∈ slots,
    (freeHeadAddress context (UInt64.ofNat cls)).toNat+8 ≤ slot.address.toNat ∨
      slot.address.toNat+8*classWords slot.cls ≤ (freeHeadAddress context (UInt64.ofNat cls)).toNat

/-- Tokens that are scalar literals: the abstract release consumes them without effect. -/
def ScalarTokens (tokens : List RVal) : Prop := ∀ token ∈ tokens, ∃ n, token = .lit (.nat n)

theorem noScalars : ScalarTokens [] := by simp [ScalarTokens]

theorem refsIn_scalars {lits : List RVal} (hl : ScalarTokens lits) (k : Nat) (rest : List RVal) :
    refsIn k (lits ++ rest) = refsIn k rest := by
  induction lits with
  | nil => rfl
  | cons token tail ih =>
    obtain ⟨n, rfl⟩ := hl token (by simp)
    simpa [refsIn] using ih (fun t ht => hl t (by simp [ht]))

theorem Balance.drop_scalars {heap : Heap} {external : Nat → Nat} {lits rest : List RVal}
    (hb : Balance heap external (lits ++ rest)) (hl : ScalarTokens lits) :
    Balance heap external rest := by
  intro k
  have := hb k
  rwa [refsIn_scalars hl] at this

theorem dropAll_scalars {heap : Heap} {lits : List RVal} (hl : ScalarTokens lits) (rest : List RVal) :
    dropAll heap (lits ++ rest) = dropAll heap rest := by
  induction lits with
  | nil => rfl
  | cons token tail ih =>
    obtain ⟨n, rfl⟩ := hl token (by simp)
    rw [List.cons_append, dropAll]
    simp only [releaseOne]
    exact ih (fun t ht => hl t (by simp [ht]))

/-- A finished cursor's suffix is its cell's scalar words. -/
theorem PendingCursor.suffix_scalars {addresses before mem address predecessor original visited}
    (h : PendingCursor addresses before mem address predecessor original visited)
    (hv : visited = original.ctor.nobj) : ScalarTokens (original.fields.drop visited) := by
  intro token hm
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hm
  rw [List.getElem_drop] at he
  have hlen : visited + j < original.fields.length := by simp at hj; omega
  exact h.scalars (visited + j) token (by rw [List.getElem?_eq_getElem hlen]; exact congrArg some he)
    (by omega)

theorem pending_ne_free {slot : Slot} {location suffix predecessor}
    (hk : slot.kind = .pending location suffix predecessor) : slot.kind ≠ .free := by
  rw [hk]; intro h; cases h

theorem live_ne_free {slot : Slot} {location} (hk : slot.kind = .live location) :
    slot.kind ≠ .free := by
  rw [hk]; intro h; cases h

theorem ReleaseInvariant.cursor_bytes
    {cmax heap addresses mem external current frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external current frames context base bump limit slots lists)
    {frame : CursorFrame} (hm : frame ∈ frames) :
    16 ≤ cellBytesOf frame.original.ctor ∧
      8 * (1 + frame.original.ctor.nobj + frame.original.ctor.nscalar) ≤ cellBytesOf frame.original.ctor :=
  cellBytesOf_le (h.cursor_layout frame hm) |>.imp_right fun h => h.1

end IxCC.Rt.Rc.Gen
