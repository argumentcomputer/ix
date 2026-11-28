import IxCC.Rt.Rc.Gen.Proof.ProtectedOps
import IxCC.Rt.Rc.Gen.Proof.ReleasePoint
import IxCC.Rt.Rc.Gen.Proof.UniqueStep
import IxCC.Rt.Rc.Gen.Proof.RecycleDetailed

/-! The last reference to a cell without scanned fields: block 11 recycles it at once onto its
class's list. Abstractly the cell dies and its fields, all scalar literals, become tokens the
release consumes without effect; physically only its header word and its class's head change. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

theorem recycle_advance (target : Word) (location : Nat) (suffix : List RVal) (predecessor : Word)
    (slots : List Slot) :
    recycleSlots target (advanceSlots target location suffix predecessor slots) =
      recycleSlots target slots := by
  simp only [recycleSlots, advanceSlots, List.map_map]
  apply List.map_congr_left
  intro slot _
  by_cases he : slot.address = target <;> simp [he]

/-- A unique live cell's slot becomes free and the cell dead: the partition is kept. -/
theorem ArenaPartition.kill_free {heap addresses base bump limit slots}
    (h : ArenaPartition cmax heap addresses base bump limit slots)
    {parent : Slot} (hp : parent ∈ slots) {location body}
    (hk : parent.kind = .live location)
    (hcell : heap.cell? location = some (.live 1 .dyn body)) :
    ArenaPartition cmax (setCell heap location .dead) addresses base bump limit
      (recycleSlots parent.address slots) := by
  have hd := h.detach_pending hp hk hcell [] 0
  have hm : {parent with kind := .pending location [] 0} ∈
      advanceSlots parent.address location [] 0 slots :=
    List.mem_map.mpr ⟨parent, hp, by simp⟩
  have hr := hd.recycle_pending hm (location := location) (suffix := []) (predecessor := 0) rfl
  simpa only [recycle_advance] using hr

/-- The complete invariant after block 11. -/
theorem ReleaseInvariant.scalar_complete
    {heap addresses mem external location frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external (some (.loc location)) frames
      context base bump limit slots lists)
    {body} (hcell : heap.cell? location = some (.live 1 .dyn body))
    (hz : body.ctor.nobj = 0) :
    ∃ parent ∈ slots, addresses location = some parent.address ∧ parent.cls = classOf body.ctor ∧
      ReleaseInvariant cmax (setCell heap location .dead) addresses
        (recycleParent mem context (UInt64.ofNat parent.cls) parent.address ((lists parent.cls).headD 0))
        external none frames context base bump limit (recycleSlots parent.address slots)
        (pushFree lists parent.cls parent.address) ∧
      ScalarTokens body.fields := by
  obtain ⟨_, address, haddress, cell⟩ := h.live.cell location 1 .dyn body hcell
  obtain ⟨parent, hp, hk⟩ := h.partition.placed location 1 body hcell
  obtain ⟨r, b, hc, had, hcls⟩ := h.partition.live parent hp location hk
  rw [hcell] at hc
  have heq : r = 1 ∧ b = body := by simpa using hc.symm
  obtain ⟨hr, hb⟩ := heq
  subst r; subst b
  have hpa : parent.address = address := by
    rw [haddress] at had; exact (Option.some.inj had).symm
  have hscal : ScalarTokens body.fields := by
    intro token hm
    obtain ⟨j, hj, he⟩ := List.getElem_of_mem hm
    exact cell.scalar_values j token (by rw [List.getElem?_eq_getElem hj]; exact congrArg some he)
      (by omega)
  have hbal : Balance heap external (.loc location :: cursorTokens frames) := by simpa using h.balance
  have hedges := (unique_has_no_survivor hcell hbal).2.2
  have vp := h.partition.valid parent hp
  have hbytes := cell.bytes
  have hnf := live_ne_free hk
  have hr : ∀ j < 8, mem.readable (parent.address+UInt64.ofNat j) = true := by
    intro j hj; rw [hpa]; exact cell.readable j (by omega)
  let oldHead := (lists parent.cls).headD 0
  let after := recycleParent mem context (UInt64.ofNat parent.cls) parent.address oldHead
  -- every other occupied slot keeps its bytes
  have hother : ∀ slot ∈ slots, slot ≠ parent →
      ObjectFrame mem after slot.address (8*classWords slot.cls) :=
    fun slot hs hne => h.recycle_slot_frame hp hs hne oldHead
  have hframeSlot : ∀ frame ∈ frames, ∃ slot ∈ slots, slot.address = frame.address ∧
      slot.cls = classOf frame.original.ctor ∧ slot ≠ parent := by
    intro frame hm
    obtain ⟨earlier, later, he⟩ := List.mem_iff_append.mp hm
    obtain ⟨slot, hs, ha, hc, hpend⟩ := h.cursors_placed earlier frame later he
    refine ⟨slot, hs, ha, hc, ?_⟩
    intro eq; subst slot; rw [hk] at hpend; cases hpend
  have hframes : ∀ frame ∈ frames,
      ObjectFrame mem after frame.address (cellBytesOf frame.original.ctor) := by
    intro frame hm
    obtain ⟨slot, hs, ha, hc, hne⟩ := hframeSlot frame hm
    simpa only [ha, hc, cellBytesOf] using hother slot hs hne
  refine ⟨parent, hp, by rw [hpa]; exact haddress, hcls, ?_, hscal⟩
  refine {
    balance := ?_
    live := ?_
    partition := h.partition.kill_free hp hk hcell
    cursors := (h.cursors.free_cell hcell).frame hframes
    cursor_distinct := h.cursor_distinct
    cursor_nonzero := h.cursor_nonzero
    cursor_layout := h.cursor_layout
    cursor_access := ?_
    cursor_class := ?_
    cursor_scan := ?_
    cursors_placed := ?_
    pending_exact := ?_
    free_exact := h.recycle_free_exact hp
    free_distinct := h.recycle_distinct hp hnf
    free_placed := fun _ _ hm => h.recycle_free_placed hp hnf hm
    free_chains := h.recycle_chains hp hnf hr
    free_heads := fun _ hl hu => h.recycle_heads hp oldHead hl hu
    head_writable := ?_
    head_fit := h.head_fit
    context_fit := h.context_fit
    head_disjoint := ?_ }
  · have hb' := balance_free hcell hbal
    simpa using Balance.drop_scalars hb' hscal
  · apply h.live.kill hcell hedges
    intro loc r b a hne hold hmapping
    obtain ⟨slot, hs, hks⟩ := h.partition.placed loc r b hold
    obtain ⟨r', b', hc', had', hcls'⟩ := h.partition.live slot hs loc hks
    rw [hold] at hc'
    have hbb : b' = b := by cases hc'; rfl
    subst b'
    have hsa : slot.address = a := by rw [hmapping] at had'; exact (Option.some.inj had').symm
    have hne' : slot ≠ parent := by
      intro eq; subst slot; rw [hk] at hks; cases hks; exact hne rfl
    simpa only [hsa, hcls', cellBytesOf] using hother slot hs hne'
  · intro frame hm j hj
    simpa [after, recycleParent, X86.Memory.write] using h.cursor_access frame hm j hj
  · intro frame hm
    have hb := (hframes frame hm).bytes_eq 1 (by have := h.cursor_bytes hm; omega)
    have he : after.bytes (frame.address+1) = mem.bytes (frame.address+1) := by simpa using hb
    exact he.trans (h.cursor_class frame hm)
  · intro frame hm
    have hb := (hframes frame hm).bytes_eq 0 (by have := h.cursor_bytes hm; omega)
    have he : after.bytes frame.address = mem.bytes frame.address := by simpa using hb
    exact he.trans (h.cursor_scan frame hm)
  · intro earlier frame later he
    obtain ⟨slot, hs, ha, hc, hpend⟩ := h.cursors_placed earlier frame later he
    have hne : slot.address ≠ parent.address := by
      intro hsa
      have := h.partition.address_unique hs hp hsa
      subst slot; rw [hk] at hpend; cases hpend
    exact ⟨slot, List.mem_map.mpr ⟨slot, hs, by simp [hne]⟩, ha, hc, hpend⟩
  · intro slot hm loc suffix pred
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    by_cases he : old.address = parent.address
    · simp only [he, ite_true]
      constructor
      · intro hx; cases hx
      · rintro ⟨earlier, frame, later, hfr, hloc, hadd, -, -, -⟩
        obtain ⟨slot, hs, ha, -, hpend⟩ := h.cursors_placed earlier frame later hfr
        have := h.partition.address_unique hs hp (by rw [ha, ← hadd])
        subst slot; rw [hk] at hpend; cases hpend
    · simpa only [he, ite_false] using h.pending_exact old hold loc suffix pred
  · intro cls hl hu j hj
    simpa [after, recycleParent, X86.Memory.write] using h.head_writable cls hl hu j hj
  · intro cls hl hu slot hm
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hm
    have hs := h.head_disjoint cls hl hu old hold
    by_cases he : old.address = parent.address <;> simpa [he] using hs

theorem ReleasePoint.scalar_move_frame {p : ReleasePoint} {addresses external context base bump limit}
    (hp : p.Valid cmax addresses external context base bump limit) {location body}
    (hc : p.current = some (.loc location))
    (hcell : p.heap.cell? location = some (.live 1 .dyn body)) (hz : body.ctor.nobj = 0) :
    ∃ next, p.Move cmax addresses external context base bump limit next ∧
      ProtectedFrame p.mem next.mem context base bump := by
  obtain ⟨hi, hr⟩ := hp
  have hr' : ∃ word, valueWord addresses (.loc location) = some word ∧
      p.env[1]? = some word ∧ p.env[2]? = some (cursorHead p.frames) := by
    simpa only [hc] using hr
  obtain ⟨address, ha, h1, h2⟩ := hr'
  have hi' : ReleaseInvariant cmax p.heap addresses p.mem external (some (.loc location)) p.frames
      context base bump limit p.slots p.lists := by simpa only [hc] using hi
  obtain ⟨_, a, ham, cell⟩ := hi'.live.cell location 1 .dyn body hcell
  have hae : a = address := by
    change addresses location = some address at ha
    rw [ha] at ham; exact (Option.some.inj ham).symm
  subst a
  obtain ⟨parent, hm, hpa, hcls, hiNext, hscal⟩ := hi'.scalar_complete hcell hz
  have hpa' : parent.address = address := by
    change addresses location = some address at ha
    rw [ha] at hpa; exact (Option.some.inj hpa).symm
  have vp := hi'.partition.valid parent hm
  let oldHead := (p.lists parent.cls).headD 0
  have hhead := hi'.free_heads parent.cls vp.1 vp.2.1
  have hload : loadWord p.mem .w64 .zero (freeHeadAddress context (UInt64.ofNat parent.cls)) =
      some oldHead := by simp only [loadWord, hhead.read64]; rfl
  have hbytes := cell.bytes
  have hrun := scalar_recycle p.mem context address (cursorHead p.frames) (UInt64.ofNat parent.cls)
    oldHead (p.env.insert 3 0) (by simp only [Std.HashMap.getElem?_insert]; exact h1)
    (by simp only [Std.HashMap.getElem?_insert]; exact h2)
    (by simpa [hz] using cell.scan_load) (by simpa [hcls] using cell.class_load) hload
    (fun j hj => cell.writable j (by omega)) (hi'.head_writable parent.cls vp.1 vp.2.1)
  let next : ReleasePoint := {p with
    heap := setCell p.heap location .dead
    mem := recycleParent p.mem context (UInt64.ofNat parent.cls) address oldHead
    current := none
    slots := recycleSlots parent.address p.slots
    lists := pushFree p.lists parent.cls parent.address
    env := ((((p.env.insert 3 0).insert 5 0).insert 17 (UInt64.ofNat parent.cls)).insert 18 oldHead).insert 8
      (cursorHead p.frames)}
  have hrelease : releaseOne p.heap (.loc location) (cursorTokens p.frames) =
      some (next.heap, body.fields ++ next.current.toList ++ cursorTokens next.frames) := by
    simp [releaseOne, hcell, next]
  refine ⟨next, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨by simpa only [next, hpa'] using hiNext, ?_⟩
    simp only [next, Std.HashMap.getElem?_insert]; rfl
  · change ReleaseLess (cutpointRank next.heap none next.frames) (cutpointRank p.heap p.current p.frames)
    rw [hc]
    apply Prod.Lex.left
    exact mass_free_lt hcell
  · refine ⟨1, ?_⟩
    have hs := (cell.unique_dispatch context p.env h1).trans hrun
    simpa only [ReleasePoint.state, hc, next, Option.isSome_some, ite_true, Option.isSome_none,
      Bool.false_eq_true, ite_false] using hs
  · exact ⟨body.fields, hscal, by simpa only [hc] using hrelease⟩
  · simpa only [next, hpa'] using hi'.recycle_protected hm oldHead

end IxCC.Rt.Rc.Gen
