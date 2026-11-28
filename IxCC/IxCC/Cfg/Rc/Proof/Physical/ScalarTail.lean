import IxCC.Cfg.Rc.Proof.Physical.PublicationFree
import IxCC.Cfg.Rc.Proof.Physical.PublicationKinds
import IxCC.Cfg.Rc.Proof.Physical.PublicationTokens
import IxCC.Cfg.Rc.Proof.Physical.PublicationLive
import IxCC.Cfg.Rc.Proof.Physical.ReservedHeader
import IxCC.Cfg.Rc.Proof.Physical.AllocSteps
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FailureTransport
import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorInvariant
import IxCC.Rt.Rc.Gen.Proof.ReserveFree
import IxCC.Rt.Rc.Gen.Proof.ReserveBump
import IxCC.Rt.Rc.Gen.Proof.AllocFailure
import IxCC.Rt.Rc.Gen.Proof.AllocatorMetadata
import IxCC.Rt.Rc.Gen.Proof.AllocatorAccess
import IxCC.Rt.Rc.Gen.Proof.ProtectedMetadata
import IxCC.Rt.Rc.Gen.Proof.ReadyOperations
import IxCC.Rt.Rc.Gen.Proof.InPlace
import IxCC.Rt.Rc.Proof.Readback.Header
import IxCC.Rt.Rc.Proof.SuccessTransport

/-! # General Scalar-Tail Constructor Readiness (`CtorInfo.nscalar ≥ 0`)

Generalizes physical allocation, payload publication, constructor-table invariants (`ScalarHeapCtorOk`),
release (`Gen.dec`), `@unique` in-place reuse (`Gen.inPlace_ready`), and header/word readback to
arbitrary `Rt.Rc.CellLayout`s with `nscalar ≥ 0`, including:
* 1-scalar-word boxed `UInt64` cells (`⟨nobj := 0, nscalar := 1, tag := 0⟩`, `word-w2`'s `wordBoxCtor`),
* mixed object+scalar-tail cells (`nobj > 0, nscalar > 0`), and
* Phase 1 fully scanned cells (`nscalar = 0`, recovered as a special case via `HeapCtorOk.toScalar`). -/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Proof IxCC.Rt.Rc.Procs
open IxCC.Cfg.Rc.Proof.Physical.Bridge

/-! ## General-layout reserved storage and publication (`nscalar ≥ 0`) -/

/-- Reserved allocator storage for any valid constructor layout (`nobj` scanned object fields
followed by `nscalar` raw 64-bit scalar words). -/
structure ScalarReservedCell (mem : X86.Memory) (address : Word) (body : Own.Body) : Prop where
  layout : (Gen.layoutOf body.ctor).ok = true
  arity : body.fields.length = body.ctor.nobj + body.ctor.nscalar
  shared : body.ctor.fieldKinds = List.replicate body.ctor.nobj .shared
  nonzero : address ≠ 0
  aligned : address.toNat % 8 = 0
  fit : address.toNat + Gen.cellBytesOf body.ctor < 2 ^ 63
  readable : ∀ j < Gen.cellBytesOf body.ctor, mem.readable (address + UInt64.ofNat j) = true
  writable : ∀ j < Gen.cellBytesOf body.ctor, mem.writable (address + UInt64.ofNat j) = true
  header : mem.read .w32 address =
    UInt64.ofNat (headerLow body.ctor.nobj (Gen.classOf body.ctor) body.ctor.tag)
  count : mem.read .w32 (address + 4) = 0

/-- A unique dynamic header for any valid `CellLayout` splits into its low 32-bit `(scan, cls, tag)`
word and high 32-bit zero count word. -/
theorem unique_header_reads_gen {mem : X86.Memory} {address : Word} {L : CellLayout} {cls : Nat}
    (hL : L.ok = true) (hcl : L.cls? = some cls)
    (represented : WordAt mem address (dynamicHeader L.nobj cls L.tag 1)) :
    mem.read .w32 address = UInt64.ofNat (headerLow L.nobj cls L.tag) ∧
      mem.read .w32 (address + 4) = 0 := by
  have headerEq : dynamicHeader L.nobj cls L.tag 1 = UInt64.ofNat (headerLow L.nobj cls L.tag) := by
    simp [dynamicHeader, header]
  rw [headerEq] at represented
  have hb := CellLayout.ok_bounds hL
  have hc := (CellLayout.cls_spec hL hcl).2.1
  have bound : headerLow L.nobj cls L.tag < 2 ^ 32 := by
    simp only [headerLow, maxTag, maxFields, maxClass] at *
    omega
  have wordBound : (UInt64.ofNat (headerLow L.nobj cls L.tag)).toNat < 2 ^ 32 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    exact bound
  exact ⟨(wordAt_read32_low represented).trans (truncate32_small wordBound),
    wordAt_read32_high_zero represented wordBound⟩

/-- Publishing all `nobj + nscalar` words (object words at `j < nobj`, raw 64-bit scalar words at
`nobj ≤ j < nobj + nscalar`) establishes `Gen.LiveCell`. -/
theorem ScalarReservedCell.publish {mem : X86.Memory} {address : Word} {body : Own.Body}
    (reserved : ScalarReservedCell mem address body) (addresses : AddressMap) (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value →
      Gen.fieldWord addresses body.ctor j value = some (words j)) :
    Gen.LiveCell addresses
      (publishFields mem address words (List.range body.fields.length)) address 1 body := by
  have hbytes := (Gen.cellBytesOf_le reserved.layout).2.1
  have fit : address.toNat + 8 * (body.fields.length + 1) < 2 ^ 63 := by
    have := reserved.fit; have := reserved.arity; omega
  have frame := publishFields_headerFrame fit words mem
  refine {
    positive := by decide
    bounded := by decide
    layout := reserved.layout
    arity := reserved.arity
    shared := reserved.shared
    nonzero := reserved.nonzero
    aligned := reserved.aligned
    fit := reserved.fit
    readable := fun j hj => by rw [frame.readable]; exact reserved.readable j hj
    writable := fun j hj => by rw [frame.writable]; exact reserved.writable j hj
    header := ?_
    count := ?_
    fields := ?_ }
  · rw [← reserved.header]
    apply X86.Memory.readLittle_congr
    intro j hj
    apply frame.bytes_eq
    simp only [X86.Width.bytes] at hj; omega
  · change (publishFields mem address words (List.range body.fields.length)).read .w32 (address + 4) = 0
    rw [← reserved.count]
    apply X86.Memory.readLittle_congr
    intro j hj
    rw [cell_offset4]
    apply frame.bytes_eq
    simp only [X86.Width.bytes] at hj; omega
  · intro j value lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    refine ⟨words j, values j value lookup, ?_⟩
    have published := publishFields_word (List.range body.fields.length) address words fit
      (fun idx hi => List.mem_range.mp hi) List.nodup_range (List.mem_range.mpr bound)
      (mem := mem) (fun byte hb => by
        rw [fieldAddress_byte]
        apply reserved.readable
        have := reserved.arity; omega)
    simpa only [fieldAddress, show 8 * (j + 1) = 8 + 8 * j by omega] using published

theorem scalar_reserved_from_ready {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem external context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (body : Own.Body)
    (sizeClass : chosen.cls = Gen.classOf body.ctor)
    (hlayout : (Gen.layoutOf body.ctor).ok = true)
    (arity : body.fields.length = body.ctor.nobj + body.ctor.nscalar)
    (shared : body.ctor.fieldKinds = List.replicate body.ctor.nobj .shared)
    (header : WordAt mem chosen.address
      (dynamicHeader body.ctor.nobj (Gen.classOf body.ctor) body.ctor.tag 1)) :
    ScalarReservedCell mem chosen.address body := by
  have valid := ready.idle.partition.valid chosen member
  have bounds := ready.idle.partition.bounds
  have byteSize : Gen.cellBytesOf body.ctor = 8 * classWords chosen.cls := by
    rw [sizeClass]; rfl
  have reads := unique_header_reads_gen hlayout (Gen.layoutOf_cls hlayout) header
  refine {
    layout := hlayout
    arity
    shared
    nonzero := ready.slot_nonzero member
    aligned := valid.2.2.1
    fit := by rw [byteSize]; omega
    readable := fun j hj => (ready.slot_access member (by rwa [byteSize] at hj)).1
    writable := fun j hj => (ready.slot_access member (by rwa [byteSize] at hj)).2
    header := reads.1
    count := reads.2 }

private theorem scalar_slot_frame {heap : Own.Heap} {addresses : AddressMap}
    {base bump limit : Word} {slots : List Slot}
    (partition : Gen.ArenaPartition maxClass heap addresses base bump limit slots)
    {chosen other : Slot} (hm : chosen ∈ slots) (hn : other ∈ slots)
    (different : other.address ≠ chosen.address) {fields : Nat}
    (hfit8 : 8 * (fields + 1) ≤ 8 * classWords chosen.cls) (words : Nat → Word) (mem : X86.Memory) :
    ObjectFrame mem (publishFields mem chosen.address words (List.range fields))
      other.address (8 * classWords other.cls) := by
  have chosenBounds := partition.valid chosen hm
  have otherBounds := partition.valid other hn
  have arena := partition.bounds
  have disjoint := partition_intervals partition hn hm different
  have fieldFit : chosen.address.toNat + 8 * (fields + 1) < 2 ^ 63 := by omega
  apply publishFields_objectFrame (List.range fields) chosen.address words (by omega)
    (fun idx hi => fieldAddress_fit fieldFit (List.mem_range.mp hi)) (fun idx hi => ?_) mem
  rw [fieldAddress_nat fieldFit (List.mem_range.mp hi)]
  have bound := List.mem_range.mp hi
  rcases disjoint with left | right
  · left; omega
  · right; omega

private theorem scalar_old_live {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : Gen.ReleaseInvariant maxClass heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    {fields : Nat} (hfit8 : 8 * (fields + 1) ≤ 8 * classWords chosen.cls) (words : Nat → Word) :
    Gen.HeapLive heap addresses (publishFields mem chosen.address words (List.range fields)) := by
  refine { cell := ?_, fields_live := idle.live.fields_live, disjoint := idle.live.disjoint }
  intro location refs mode body cell
  obtain ⟨dynamic, address, mapped, represented⟩ := idle.live.cell location refs mode body cell
  subst mode
  obtain ⟨slot, slotMember, kind⟩ := idle.partition.placed location refs body cell
  obtain ⟨_, otherBody, otherCell, otherMap, otherClass⟩ := idle.partition.live slot slotMember location kind
  have bodyEqual : otherBody = body :=
    (Own.Cell.live.inj (Option.some.inj (otherCell.symm.trans cell))).2.2
  subst otherBody
  have addressEqual : slot.address = address := Option.some.inj (otherMap.symm.trans mapped)
  subst address
  have different : slot.address ≠ chosen.address := by
    intro same
    have equal := partition_address_unique idle.partition slotMember member same
    subst slot; rw [reserved] at kind; cases kind
  refine ⟨rfl, slot.address, mapped, represented.frame ?_⟩
  simpa only [otherClass, Gen.cellBytesOf] using
    scalar_slot_frame idle.partition member slotMember different hfit8 words mem

private theorem scalar_free_chains {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : Gen.ReleaseInvariant maxClass heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    {fields : Nat} (hfit8 : 8 * (fields + 1) ≤ 8 * classWords chosen.cls) (words : Nat → Word) (cls : Nat) :
    FreeChain (publishFields mem chosen.address words (List.range fields)) (lists cls) := by
  apply freeChain_words (idle.free_chains cls)
  intro address present word represented
  obtain ⟨slot, slotMember, addressEq, _, freeKind⟩ := idle.free_placed cls address present
  subst address
  have different : slot.address ≠ chosen.address := by
    intro same
    have equal := partition_address_unique idle.partition slotMember member same
    subst slot; rw [reserved] at freeKind; cases freeKind
  have frame := scalar_slot_frame idle.partition member slotMember different hfit8 words mem
  have positive := idle.partition.valid slot slotMember
  have oldWord : WordAt mem (slot.address + UInt64.ofNat 0) word := by simpa using represented
  simpa using frame.word (offset := 0) (by omega) oldWord

private theorem scalar_head_frame {heap : Own.Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (idle : Gen.ReleaseInvariant maxClass heap addresses mem external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) {fields : Nat}
    (hfit8 : 8 * (fields + 1) ≤ 8 * classWords chosen.cls) (words : Nat → Word)
    {cls : Nat} (lower : 1 ≤ cls) (upper : cls ≤ maxClass) :
    ObjectFrame mem (publishFields mem chosen.address words (List.range fields))
      (freeHeadAddress context (UInt64.ofNat cls)) 8 := by
  have chosenBounds := idle.partition.valid chosen member
  have arena := idle.partition.bounds
  have fieldFit : chosen.address.toNat + 8 * (fields + 1) < 2 ^ 63 := by omega
  have separate := idle.head_disjoint cls lower upper chosen member
  apply publishFields_objectFrame (List.range fields) chosen.address words
    (idle.head_fit cls lower upper)
    (fun idx hi => fieldAddress_fit fieldFit (List.mem_range.mp hi)) (fun idx hi => ?_) mem
  rw [fieldAddress_nat fieldFit (List.mem_range.mp hi)]
  have bound := List.mem_range.mp hi
  rcases separate with left | right
  · left; omega
  · right; omega

private theorem scalar_protected {heap : Own.Heap} {addresses : AddressMap}
    {original : X86.Memory} {external : Nat → Nat} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (idle : Gen.ReleaseInvariant maxClass heap addresses original external none [] context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) {fields : Nat}
    (hfit8 : 8 * (fields + 1) ≤ 8 * classWords chosen.cls) (words : Nat → Word)
    (indices : List Nat) (bounded : ∀ idx ∈ indices, idx < fields) (mem : X86.Memory) :
    Gen.ProtectedFrame mem (publishFields mem chosen.address words indices) context base bump := by
  induction indices generalizing mem with
  | nil => exact Gen.ProtectedFrame.refl _ _ _ _
  | cons idx indices ih =>
    have first := idle.object_store_frame member mem (8 * (idx + 1)) .w64 (words idx) (by
      have hi := bounded idx (by simp)
      simp only [X86.Width.bytes]; omega)
    exact first.trans (ih (fun j hj => bounded j (by simp [hj])) _)

/-- General-layout publication into `Gen.AllocatorReady`, valid for ANY `nscalar ≥ 0`
(including `nobj = 0, nscalar = 1` boxed `UInt64` cells and mixed `nobj > 0, nscalar > 0` cells). -/
theorem scalar_publication_ready {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    {chosen : Slot} (member : chosen ∈ slots) (reserved : chosen.kind = .reserved)
    (sizeClass : chosen.cls = Gen.classOf body.ctor)
    (storage : ScalarReservedCell mem chosen.address body) (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value →
      Gen.fieldWord addresses body.ctor j value = some (words j)) :
    Gen.AllocatorReady maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size chosen.address)
      (publishFields mem chosen.address words (List.range body.fields.length))
      (fun location => external location + refsIn location [(heap.alloc .rc body).1])
      context base bump limit (publishSlots heap.size chosen.address slots) lists := by
  have hfit8 : 8 * (body.fields.length + 1) ≤ 8 * classWords chosen.cls := by
    have hc := (Gen.cellBytesOf_le storage.layout).2.1
    rw [sizeClass]; unfold Gen.cellBytesOf at hc; have := storage.arity; omega
  have fields := idle_field_tokens ready.idle
  have bounded := publication_fields_bounded fields
  have oldLive := heapLive_placeFresh (scalar_old_live ready.idle member reserved hfit8 words) chosen.address
  have freshLive := storage.publish (placeFresh addresses heap.size chosen.address) words (by
    intro j value lookup
    unfold Gen.fieldWord
    split
    · rw [placeFresh_old (bounded value (List.mem_of_getElem? lookup))]
      have hv := values j value lookup
      simp only [Gen.fieldWord, *, ite_true] at hv
      exact hv
    · have hv := values j value lookup
      simp only [Gen.fieldWord, *, ite_false] at hv
      exact hv)
  have hlive : Gen.HeapLive (heap.alloc .rc body).2 (placeFresh addresses heap.size chosen.address)
      (publishFields mem chosen.address words (List.range body.fields.length)) := by
    apply heapLive_append oldLive (by simp [placeFresh]) freshLive (publication_children fields)
    intro location refs other address cell mapped
    have locationBound : location < heap.size := (Array.getElem?_eq_some_iff.mp cell).1
    have oldMap : addresses location = some address := by
      simpa [placeFresh, Nat.ne_of_lt locationBound] using mapped
    obtain ⟨slot, slotMember, kind⟩ := ready.idle.partition.placed location refs other cell
    obtain ⟨_, oldBody, oldCell, slotMap, slotClass⟩ :=
      ready.idle.partition.live slot slotMember location kind
    have bodyEqual : oldBody = other :=
      (Own.Cell.live.inj (Option.some.inj (oldCell.symm.trans cell))).2.2
    subst oldBody
    have addressEqual : slot.address = address := Option.some.inj (slotMap.symm.trans oldMap)
    subst address
    have different : chosen.address ≠ slot.address := by
      intro same
      have equal := partition_address_unique ready.idle.partition member slotMember same
      subst slot; rw [reserved] at kind; cases kind
    have disjoint := partition_intervals ready.idle.partition member slotMember different
    rw [sizeClass, slotClass] at disjoint
    simpa only [Gen.cellBytesOf] using disjoint
  have hidle : Gen.ReleaseInvariant maxClass (heap.alloc .rc body).2
      (placeFresh addresses heap.size chosen.address)
      (publishFields mem chosen.address words (List.range body.fields.length))
      (fun location => external location + refsIn location [(heap.alloc .rc body).1]) none []
      context base bump limit (publishSlots heap.size chosen.address slots) lists := {
    balance := by simpa [cursorTokens, flattenPending] using publication_balance fields
    live := hlive
    partition := partition_publish ready.idle.partition member reserved body sizeClass
    cursors := trivial
    cursor_distinct := by simp
    cursor_nonzero := by simp
    cursor_layout := by simp
    cursor_access := by simp
    cursor_class := by simp
    cursor_scan := by simp
    cursors_placed := fun _ _ _ h => by have := congrArg List.length h; simp at this
    pending_exact := fun slot present location suffix predecessor => by
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
      rw [publishSlot_pending ready.idle.partition member reserved oldMember heap.size location suffix predecessor]
      simpa using ready.idle.pending_exact old oldMember location suffix predecessor
    free_exact := publication_free_exact ready.idle member reserved heap.size
    free_distinct := ready.idle.free_distinct
    free_placed := publication_free_placed ready.idle member reserved heap.size
    free_chains := scalar_free_chains ready.idle member reserved hfit8 words
    free_heads := fun cls lo hi => by
      have frame := scalar_head_frame ready.idle member hfit8 words lo hi
      have oldWord : WordAt mem (freeHeadAddress context (UInt64.ofNat cls) + UInt64.ofNat 0)
          ((lists cls).headD 0) := by simpa using ready.idle.free_heads cls lo hi
      simpa using frame.word (offset := 0) (by decide) oldWord
    head_writable := fun cls lo hi j bound => by
      rw [(scalar_head_frame ready.idle member hfit8 words lo hi).writable]
      exact ready.idle.head_writable cls lo hi j bound
    head_fit := ready.idle.head_fit
    context_fit := ready.idle.context_fit
    head_disjoint := fun cls lo hi slot present => by
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp present
      simpa using ready.idle.head_disjoint cls lo hi old oldMember }
  exact ready.after_protected
    (scalar_protected ready.idle member hfit8 words (List.range body.fields.length)
      (fun _ h => List.mem_range.mp h) mem) hidle

/-! ## General-layout wrapper execution (`allocationWrapper` + `Rt.Rc.Gen.alloc L`) -/

theorem scalar_allocator_call_free (L : CellLayout) : CallFree (Gen.alloc L) := by
  unfold Gen.alloc
  split
  · simp [CallFree, Gen.declined]
  · split <;> simp [CallFree, Gen.allocFunc, Gen.declined]

theorem scalar_allocator_caller {L : CellLayout} {cls : Nat}
    (hL : L.ok = true) (hcl : L.cls? = some cls)
    {mem after : X86.Memory} {context address : Word}
    (execution : Lir.eval (Gen.allocProgram L) 0 [] mem context = .ok ([address], after))
    {P : Lir.Program} {procedure destination : Nat}
    (function : P.funcs[procedure]? = some (Gen.alloc L))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    Sem.Star (Lir.semStep P)
      { mem, ctx := context, stack := { fn := procedure, label := 0, pos := 0, env := {} } :: caller :: callers } 0
      { mem := after, ctx := context,
        stack := { caller with env := caller.env.insert destination address, dsts := [] } :: callers } := by
  have reaches := (Lir.runs_eval (Gen.alloc_free_initial mem context L cls hL hcl)) 0
  dsimp only at reaches
  rw [execution] at reaches
  let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := {} }
  have localRun : Sem.Reaches (Lir.semStep (localProgram (Gen.alloc L)))
      (localState mem context frame) 0 (.ok ([address], after)) := by
    simpa only [localProgram, Gen.allocProgram, localState, allocState, frame] using reaches
  obtain ⟨charges, bound, trace⟩ := local_success_transport (Gen.alloc L)
    (scalar_allocator_call_free L) P procedure function mem context frame rfl caller callers
    (env := caller.env.insert destination address) localRun (by simp [dest, Lir.bindParams])
  have zero : charges = 0 := by omega
  subst charges
  simpa only [ambientState, frame] using trace

theorem scalar_allocation_wrapper_success {L : CellLayout} {cls : Nat}
    (hL : L.ok = true) (hcl : L.cls? = some cls)
    {fields : Nat} {mem reserved : X86.Memory} {context address : Word}
    (execution : Lir.eval (Gen.allocProgram L) 0 [] mem context = .ok ([address], reserved))
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} {words : Nat → Word}
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure fields))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc L))
    (values : ∀ idx < fields, env[idx]? = some (words idx))
    (writable : ∀ idx < fields, ∀ byte < 8,
      reserved.writable (fieldAddress address idx + UInt64.ofNat byte) = true)
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    Sem.Star (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers } 1
      { mem := publishFields reserved address words (List.range fields), ctx := context,
        stack := { caller with env := caller.env.insert destination address, dsts := [] } :: callers } := by
  have enter : Lir.enter P procedure [] = some { fn := procedure, label := 0, pos := 0, env := {} } := by
    simp [Lir.enter, procedureLookup, Gen.alloc_eq hL hcl, Gen.allocFunc, Lir.bindParams]
  have callStep := allocation_call (env := env) (rest := caller :: callers)
    (mem := mem) (ctx := context) wrapperLookup enter
  let continuation : Lir.Frame := { fn := wrapper, label := 0, pos := 1, env, dsts := [fields] }
  have procedureTrace := scalar_allocator_caller hL hcl execution procedureLookup
    continuation (caller :: callers) rfl
  have stores := allocation_publish (rest := caller :: callers) (ctx := context)
    wrapperLookup values writable
  have returnStep := allocation_return (env := env.insert fields address) (address := address)
    (caller := caller) (rest := callers)
    (mem := publishFields reserved address words (List.range fields)) (ctx := context)
    wrapperLookup (by simp) dest
  have combined := (Sem.Star.single (Lir.semStep_next.mpr callStep)).trans
    (procedureTrace.trans (stores.trans (Sem.Star.single (Lir.semStep_next.mpr returnStep))))
  simpa [continuation] using combined

/-- Total LIR allocation + payload publication for ANY valid constructor layout (`nscalar ≥ 0`),
including `wordBoxCtor` (`nobj = 0, nscalar = 1, tag = 0`) and mixed scalar-tail constructors:
either allocates (free-list or bump), publishes all object and raw scalar words, and restores
`Gen.AllocatorReady`, or cleanly hits `.resource .heap` when the arena is exhausted. -/
theorem scalar_allocation_total {heap : Heap} {addresses : AddressMap} {mem : X86.Memory}
    {external : Nat → Nat} {body : Own.Body} {context base bump limit : Word}
    {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass heap addresses mem
      (fun location => external location + refsIn location body.fields)
      context base bump limit slots lists)
    (hlayout : (Gen.layoutOf body.ctor).ok = true)
    (arity : body.fields.length = body.ctor.nobj + body.ctor.nscalar)
    (shared : body.ctor.fieldKinds = List.replicate body.ctor.nobj .shared)
    {P : Lir.Program} {wrapper procedure destination : Nat} {env : Lir.Env} (words : Nat → Word)
    (wrapperLookup : P.funcs[wrapper]? = some (allocationWrapper procedure body.fields.length))
    (procedureLookup : P.funcs[procedure]? = some (Gen.alloc (Gen.layoutOf body.ctor)))
    (registers : ∀ idx < body.fields.length, env[idx]? = some (words idx))
    (values : ∀ j value, body.fields[j]? = some value →
      Gen.fieldWord addresses body.ctor j value = some (words j))
    (caller : Lir.Frame) (callers : List Lir.Frame) (dest : caller.dsts = [destination]) :
    (∃ address next finalMem finalSlots finalLists,
      Gen.AllocatorReady maxClass (heap.alloc .rc body).2 (placeFresh addresses heap.size address)
        finalMem (fun location => external location + refsIn location [(heap.alloc .rc body).1])
        context base next limit finalSlots finalLists ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers } 1
        { mem := finalMem, ctx := context,
          stack := { caller with env := caller.env.insert destination address, dsts := [] } :: callers }) ∨
    Sem.Reaches (Lir.semStep P)
      { mem, ctx := context, stack := { fn := wrapper, label := 0, pos := 0, env } :: caller :: callers }
      1 (.resource .heap) := by
  have hcl := Gen.layoutOf_cls hlayout
  have hclsLe : Gen.classOf body.ctor ≤ maxClass := (Gen.classOf_spec hlayout).2.1
  have hbytesLe : 8 * (1 + body.ctor.nobj + body.ctor.nscalar) ≤ classBytes (Gen.classOf body.ctor) :=
    (Gen.cellBytesOf_le hlayout).2.1
  cases head : lists (Gen.classOf body.ctor) with
  | nil =>
    by_cases space : bump.toNat + classBytes (Gen.classOf body.ctor) ≤ limit.toNat
    · obtain ⟨execution, reserved, hdrWord⟩ := ready.reserve_bump hlayout hcl hclsLe head space 0
      have member : Gen.bumpSlot bump (Gen.classOf body.ctor) ∈
          Gen.bumpSlot bump (Gen.classOf body.ctor) :: slots := by simp
      have storage := scalar_reserved_from_ready reserved member body rfl hlayout arity shared hdrWord
      have finalReady := scalar_publication_ready reserved member rfl rfl storage words values
      have bounds := ready.idle.partition.bounds
      have htrace := scalar_allocation_wrapper_success hlayout hcl execution wrapperLookup
        procedureLookup registers (fun idx hi byte hb => by
          have offsetBound : 8 * (idx + 1) + byte < classBytes (Gen.classOf body.ctor) := by omega
          have addressNat : (bump + UInt64.ofNat (8 * (idx + 1) + byte)).toNat =
              bump.toNat + (8 * (idx + 1) + byte) := Rt.Proof.addr_toNat (by omega)
          have access := ready.arena_access (bump + UInt64.ofNat (8 * (idx + 1) + byte))
            (by rw [addressNat]; omega) (by rw [addressNat]; omega)
          simpa [Gen.reserveBump, X86.Memory.write, fieldAddress_byte] using access.2)
        caller callers dest
      exact .inl ⟨bump, _, _, _, _, finalReady, htrace⟩
    · have failure := ready.reserve_short hlayout hcl head (by omega) 0
      have enter : Lir.enter P procedure [] = some { fn := procedure, label := 0, pos := 0, env := {} } := by
        simp [Lir.enter, procedureLookup, Gen.alloc_eq hlayout hcl, Gen.allocFunc, Lir.bindParams]
      have callStep := allocation_call (env := env) (rest := caller :: callers)
        (mem := mem) (ctx := context) wrapperLookup enter
      let continuation : Lir.Frame :=
        { fn := wrapper, label := 0, pos := 1, env, dsts := [body.fields.length] }
      let frame : Lir.Frame := { fn := 0, label := 0, pos := 0, env := {} }
      have reaches := (Lir.runs_eval (Gen.alloc_free_initial mem context _ _ hlayout hcl)) 0
      dsimp only at reaches; rw [failure] at reaches
      have localRun : Sem.Reaches (Lir.semStep (localProgram (Gen.alloc (Gen.layoutOf body.ctor))))
          (localState mem context frame) 0 (.resource .heap) := by
        simpa only [localProgram, Gen.allocProgram, localState, allocState, frame] using reaches
      have failed := local_resource_transport (Gen.alloc (Gen.layoutOf body.ctor))
        (scalar_allocator_call_free _) P procedure procedureLookup mem context frame rfl
        (continuation :: caller :: callers) localRun
      exact .inr (by simpa [frame, continuation, ambientState] using
        Sem.Reaches.star (Sem.Star.single (Lir.semStep_next.mpr callStep)) failed)
  | cons address tail =>
    have present : address ∈ lists (Gen.classOf body.ctor) := by simp [head]
    obtain ⟨target, member, targetAddress, targetClass, _⟩ :=
      ready.idle.free_placed (Gen.classOf body.ctor) address present
    have selected : lists target.cls = target.address :: tail := by rw [targetClass, targetAddress, head]
    obtain ⟨execution, reserved, placed, hdrWord⟩ :=
      ready.reserve_free member selected targetClass hlayout hcl 0
    have storage := scalar_reserved_from_ready reserved placed body targetClass hlayout arity shared hdrWord
    have finalReady := scalar_publication_ready reserved placed rfl targetClass storage words values
    have htrace := scalar_allocation_wrapper_success hlayout hcl execution wrapperLookup
      procedureLookup registers (fun idx hi byte hb => by
        have access := ready.slot_access member (j := 8 * (idx + 1) + byte) (by
          rw [targetClass]; unfold classBytes at hbytesLe; omega)
        simpa [Gen.reserveFree, X86.Memory.write, fieldAddress_byte] using access.2)
      caller callers dest
    exact .inl ⟨target.address, bump, _, _, _, finalReady, htrace⟩

/-! ## Scalar-tail constructor-table invariant (`ScalarHeapCtorOk`) -/

/-- Constructor table compatibility generalized to `nscalar ≥ 0`: the constructor matches its
`Lam.CtorInfo` table row by `(key, tag, arity = nobj + nscalar)`, has `nobj` shared object field
kinds, is not a tagged-`Nat` constructor, and satisfies `(Gen.layoutOf c).ok` when non-fieldless. -/
structure ScalarCtorOk (tables : Rt.Lower.Tables) (c : Fir.CtorInfo) : Prop where
  row : ∃ r, tables.ctors.find? (·.key == c.key) = some r ∧
    r.key = c.key ∧ r.tag = c.tag ∧ r.arity = c.arity
  notNat : Rt.Lower.isNatKey tables c.key = false
  tagBound : c.tag ≤ Rt.maxTag
  shared : c.fieldKinds = List.replicate c.nobj .shared
  layoutOk : c.fieldless = false → (Gen.layoutOf c).ok = true

def ScalarValueCtorOk (tables : Rt.Lower.Tables) : RVal → Prop
  | .ctor0 c => ScalarCtorOk tables c ∧ c.fieldless = true
  | _ => True

def ScalarBodyCtorOk (tables : Rt.Lower.Tables) (body : Body) : Prop :=
  ScalarCtorOk tables body.ctor ∧ body.ctor.fieldless = false ∧
    body.fields.length = body.ctor.arity ∧
    ∀ value ∈ body.fields, ScalarValueCtorOk tables value

def ScalarHeapCtorOk (tables : Rt.Lower.Tables) (heap : Heap) : Prop :=
  ∀ location refs mode body, heap.cell? location = some (.live refs mode body) →
    ScalarBodyCtorOk tables body

theorem CtorOk.toScalar {tables : Rt.Lower.Tables} {c : Fir.CtorInfo} (h : CtorOk tables c)
    (hok : c.fieldless = false → (Gen.layoutOf c).ok = true) :
    ScalarCtorOk tables c := by
  have ht := h.table
  unfold Fir.CtorInfo.ofKey at ht
  cases hf : tables.ctors.find? (·.key == c.key) with
  | none => simp [hf] at ht
  | some r =>
    simp only [hf, Option.map_some, Option.some.injEq] at ht
    have hkeyB := List.find?_some hf
    have hkey : r.key = c.key := beq_iff_eq.mp hkeyB
    have htag : r.tag = c.tag := by rw [← ht]
    have harity : r.arity = c.arity := by rw [← ht]; simp [Fir.CtorInfo.arity]
    have hsh : c.fieldKinds = List.replicate c.nobj .shared := by rw [← ht]
    exact ⟨⟨r, hf, hkey, htag, harity⟩, h.notNat, h.tag, hsh, hok⟩

theorem ValueCtorOk.toScalar {tables : Rt.Lower.Tables} {v : RVal} (h : ValueCtorOk tables v) :
    ScalarValueCtorOk tables v := by
  cases v with
  | ctor0 c =>
    exact ⟨CtorOk.toScalar h.1 (fun hf => by rw [h.2] at hf; cases hf), h.2⟩
  | loc _ | lit _ | erased => trivial

theorem HeapCtorOk.toScalar {tables : Rt.Lower.Tables} {H : Heap}
    (h : HeapCtorOk tables H)
    (hlive : ∀ l rc m b, H.cell? l = some (.live rc m b) →
      (Gen.layoutOf b.ctor).ok = true ∧ b.fields.length = b.ctor.arity) :
    ScalarHeapCtorOk tables H := by
  intro l rc m b hc
  obtain ⟨hcok, hnf, hfields⟩ := h l rc m b hc
  obtain ⟨hl, hlen⟩ := hlive l rc m b hc
  exact ⟨CtorOk.toScalar hcok (fun _ => hl), hnf, hlen,
    fun u hu => ValueCtorOk.toScalar (hfields u hu)⟩

theorem ScalarHeapCtorOk.alloc {tables : Rt.Lower.Tables} {H : Heap} {body : Body}
    (before : ScalarHeapCtorOk tables H) (compatible : ScalarBodyCtorOk tables body) :
    ScalarHeapCtorOk tables (H.alloc .rc body).2 := by
  intro l refs mode b cell
  have bound := Own.Proof.cell?_some cell
  have size := Own.Proof.alloc_size .rc H body
  by_cases old : l < H.size
  · rw [(Own.Proof.Ext.alloc .rc H body).2 l old] at cell
    exact before l refs mode b cell
  · have equal : l = H.size := by omega
    subst l
    rw [Own.Proof.alloc_cell] at cell
    simp only [AllocPol.mode, Option.some.injEq, Cell.live.injEq] at cell
    rcases cell with ⟨rfl, rfl, rfl⟩
    exact compatible

theorem ScalarHeapCtorOk.sameBodies {tables : Rt.Lower.Tables} {H H' : Heap}
    (before : ScalarHeapCtorOk tables H) (same : SameBodies H H') : ScalarHeapCtorOk tables H' := by
  intro l rc m b cell
  have equal := same.2 l
  rw [cell] at equal
  cases old : H.cell? l with
  | none => simp [old, body?] at equal
  | some c =>
    cases c with
    | dead => simp [old, body?] at equal
    | live refs mode body =>
      simp only [old, Option.bind_some, body?, Option.some.injEq] at equal
      subst body
      exact before l refs mode b old

theorem ScalarHeapCtorOk.free {tables : Rt.Lower.Tables} {H : Heap}
    (before : ScalarHeapCtorOk tables H) {l : Nat} (bound : l < H.size) :
    ScalarHeapCtorOk tables (setCell H l .dead) := by
  intro k refs mode body cell
  rw [setCell_cell H l _ bound k] at cell
  by_cases equal : l = k
  · simp [equal] at cell
  · rw [ite_eq_right (fun h => absurd h equal)] at cell
    exact before k refs mode body cell

theorem ScalarHeapCtorOk.releaseOne {tables : Rt.Lower.Tables} {H H' : Heap}
    {value : RVal} {pending pending' : List RVal} (before : ScalarHeapCtorOk tables H)
    (effect : Own.Rc.releaseOne H value pending = some (H', pending')) :
    ScalarHeapCtorOk tables H' := by
  cases value with
  | loc l =>
    cases cell : H.cell? l with
    | none => simp [Own.Rc.releaseOne, cell] at effect
    | some c =>
      cases c with
      | dead => simp [Own.Rc.releaseOne, cell] at effect
      | live refs mode body =>
        cases mode with
        | static =>
          simp only [Own.Rc.releaseOne, cell, Option.some.injEq, Prod.mk.injEq] at effect
          rcases effect with ⟨rfl, rfl⟩; exact before
        | dyn =>
          cases refs with
          | zero => simp [Own.Rc.releaseOne, cell] at effect
          | succ refs =>
            cases refs with
            | zero =>
              simp only [Own.Rc.releaseOne, cell, Option.some.injEq, Prod.mk.injEq] at effect
              rcases effect with ⟨rfl, rfl⟩
              exact before.free (Own.Proof.cell?_some cell)
            | succ refs =>
              simp only [Own.Rc.releaseOne, cell, Option.some.injEq, Prod.mk.injEq] at effect
              rcases effect with ⟨rfl, rfl⟩
              exact before.sameBodies (sameBodies_set cell)
  | lit _ | ctor0 _ | erased =>
    simp only [Own.Rc.releaseOne, Option.some.injEq, Prod.mk.injEq] at effect
    rcases effect with ⟨rfl, rfl⟩; exact before

theorem ScalarHeapCtorOk.dropAll {tables : Rt.Lower.Tables} (H : Heap) (pending : List RVal)
    {H' : Heap} (before : ScalarHeapCtorOk tables H)
    (effect : Own.Rc.dropAll H pending = some H') : ScalarHeapCtorOk tables H' := by
  match pending with
  | [] =>
    simp only [Own.Rc.dropAll, Option.some.injEq] at effect
    subst H'; exact before
  | value :: tail =>
    cases step : Own.Rc.releaseOne H value tail with
    | none => rw [Own.Rc.dropAll, step] at effect; cases effect
    | some result =>
      rcases result with ⟨next, rest⟩
      rw [Own.Rc.dropAll, step] at effect
      exact ScalarHeapCtorOk.dropAll next rest (before.releaseOne step) effect
termination_by (mass H, pending.length)
decreasing_by exact releaseOne_decreases step

theorem ScalarHeapCtorOk.reuseCell {tables : Rt.Lower.Tables} {H : Heap}
    (before : ScalarHeapCtorOk tables H) {l : Nat} (hl : l < H.size) {b' : Body}
    (hb' : ScalarBodyCtorOk tables b') : ScalarHeapCtorOk tables (reusedHeap H l b') := by
  intro k refs mode body hcell
  rw [Own.Rc.reusedHeap_cell hl] at hcell
  by_cases hfresh : k = H.size
  · rw [ite_eq_left hfresh] at hcell
    cases hcell
    exact hb'
  · rw [ite_eq_right hfresh] at hcell
    by_cases hlk : l = k
    · rw [ite_eq_left hlk] at hcell; cases hcell
    · rw [ite_eq_right hlk] at hcell
      exact before k refs mode body hcell

/-! ## Release, `@unique` in-place reuse, and `word-w2` readback compatibility -/

/-- Releasing a live scalar-tail cell via `Rt.Rc.Gen.dec` executes completely, recycles it onto
its class free list without scanning any scalar tail word, and preserves both `Gen.AllocatorReady`
and `ScalarHeapCtorOk`. -/
theorem scalar_cell_release_ready {tables : Rt.Lower.Tables}
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory} {external : Nat → Nat}
    {value : RVal} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (fun location => external location + refsIn location [value])
      context base bump limit slots lists)
    (hcok : ScalarHeapCtorOk tables H)
    {word : Word} (hw : valueWord addresses value = some word)
    (P : Lir.Program) (decProc : Nat) (hdec : P.funcs[decProc]? = some Gen.dec)
    (caller : Lir.Frame) (callers : List Lir.Frame) (hdsts : caller.dsts = []) :
    ∃ H' mem' slots' lists' charges,
      dropAll H [value] = some H' ∧
      ScalarHeapCtorOk tables H' ∧
      Gen.AllocatorReady maxClass H' addresses mem' external context base bump limit slots' lists' ∧
      Sem.Star (Lir.semStep P)
        { mem, ctx := context, stack := { fn := decProc, label := 0, pos := 0, env := Gen.decEnv word } :: caller :: callers }
        charges { mem := mem', ctx := context, stack := caller :: callers } := by
  obtain ⟨H', mem', slots', lists', charges, hdrop, hready', htrace⟩ :=
    ready.release_caller_ready word hw P decProc hdec caller callers hdsts
  exact ⟨H', mem', slots', lists', charges, hdrop, hcok.dropAll H [value] hdrop, hready', htrace⟩

/-- Static `@unique` in-place `Gen.writeCell` reuse for general scalar-tail constructors (`nscalar ≥ 0`,
including boxed `UInt64` updates and mixed object+scalar FBIP rewrites) preserves both
`Gen.AllocatorReady` and `ScalarHeapCtorOk`. -/
theorem scalar_inPlace_reuse_ready {tables : Rt.Lower.Tables}
    {H : Heap} {addresses : AddressMap} {mem : X86.Memory} {external : Nat → Nat}
    {rest kept : List RVal} {context base bump limit : Word} {slots : List Slot} {lists : Nat → List Word}
    {l : Nat} {a : Word} {b b' : Body}
    (ready : Gen.AllocatorReady maxClass H addresses mem
      (fun k => external k + refsIn k (.loc l :: rest)) context base bump limit slots lists)
    (hcok : ScalarHeapCtorOk tables H)
    (hc : H.cell? l = some (.live 1 .dyn b))
    (ha : addresses l = some a)
    (hb' : ScalarBodyCtorOk tables b')
    (hclass : Gen.classOf b'.ctor = Gen.classOf b.ctor)
    (hmass : ∀ k, refsIn k (b.fields ++ rest) = refsIn k (b'.fields ++ kept))
    (hwords : ∀ j u, b'.fields[j]? = some u → (Gen.fieldWord addresses b'.ctor j u).isSome = true) :
    ∃ (H' : Heap) (slots' : List Slot),
      reuseCell H l b' = some (.loc H.size, H') ∧
      ScalarHeapCtorOk tables H' ∧
      Gen.AllocatorReady maxClass H'
        (fun k => if k = H.size then some a else addresses k)
        (Gen.writeCell mem addresses a b' (Gen.classOf b.ctor))
        (fun k => external k + refsIn k (.loc H.size :: kept))
        context base bump limit slots' lists := by
  have hl : l < H.size := Own.Proof.cell?_some hc
  have hlayout := hb'.1.layoutOk hb'.2.1
  have harity : b'.fields.length = b'.ctor.nobj + b'.ctor.nscalar := hb'.2.2.1
  obtain ⟨H', slots', hrc, hready'⟩ :=
    Gen.inPlace_ready ready hc ha hlayout harity hb'.1.shared hclass hmass hwords
  have hH' : H' = reusedHeap H l b' := by
    rw [Own.Rc.reuseCell_some hc] at hrc
    exact (Prod.mk.inj (Option.some.inj hrc)).2.symm
  exact ⟨H', slots', hrc, hH' ▸ hcok.reuseCell hl hb', hready'⟩

/-- Physical header and payload readback bridge for any `Gen.LiveCell` with `nscalar ≥ 0`:
exposes the exact 64-bit header (`scan = body.ctor.nobj`, `tag = body.ctor.tag`), every object field
word at `address + 8 + 8*j` (`j < nobj`), and every raw 64-bit scalar word `UInt64.ofNat n` at
`address + 8 + 8*(nobj + k)` (`k < nscalar`), matching `word-w2`'s `Rt.readbackWord` contract. -/
theorem scalar_liveCell_readback_words {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs : Nat} {body : Own.Body}
    (h : Gen.LiveCell addresses mem address refs body) :
    address &&& 1 ≠ 1 ∧
    (∃ hdr : Word, mem.read64? address = .ok hdr ∧
      (hdr &&& 0xFF).toNat = body.ctor.nobj ∧
      ((hdr >>> 16) &&& 0xFFFF).toNat = body.ctor.tag) ∧
    (∀ j value, j < body.ctor.nobj → body.fields[j]? = some value →
      ∃ w, valueWord addresses value = some w ∧
        mem.read64? (address + UInt64.ofNat (8 + 8 * j)) = .ok w) ∧
    (∀ k value, k < body.ctor.nscalar → body.fields[body.ctor.nobj + k]? = some value →
      ∃ n, value = .lit (.nat n) ∧ n < 2 ^ 64 ∧
        mem.read64? (address + UInt64.ofNat (8 + 8 * (body.ctor.nobj + k))) = .ok (UInt64.ofNat n)) := by
  have heven : address &&& 1 ≠ 1 := by
    intro hodd
    have hmod : address.toNat % 2 = 1 := by
      have := congrArg UInt64.toNat hodd
      rw [UInt64.toNat_and] at this
      simpa [Nat.and_one_is_mod] using this
    have hal := h.aligned; omega
  obtain ⟨hcls, hn, ht⟩ := Gen.classOf_lt h.layout
  have hrc : refs - 1 < 2 ^ 32 := by have := h.bounded; unfold maxCount at this; omega
  have hhdr := Readback.live_header h
  refine ⟨heven, ⟨dynamicHeader body.ctor.nobj (Gen.classOf body.ctor) body.ctor.tag refs,
    hhdr, header_scan hn hcls ht hrc, header_tag hn hcls ht hrc⟩, ?_, ?_⟩
  · intro j value hj lookup
    obtain ⟨w, hfw, hwa⟩ := h.fields j value lookup
    simp only [Gen.fieldWord, hj, ite_true] at hfw
    exact ⟨w, hfw, hwa.read64⟩
  · intro k value hk lookup
    obtain ⟨w, hfw, hwa⟩ := h.fields (body.ctor.nobj + k) value lookup
    have hge : ¬ body.ctor.nobj + k < body.ctor.nobj := by omega
    simp only [Gen.fieldWord, hge, ite_false] at hfw
    cases value with
    | lit lit =>
      cases lit with
      | nat n =>
        simp only [Gen.scalarWord] at hfw
        by_cases hlt : n < 2 ^ 64
        · simp only [hlt, ite_true, Option.some.injEq] at hfw
          subst hfw
          exact ⟨n, rfl, hlt, hwa.read64⟩
        · simp only [hlt, ite_false] at hfw; cases hfw
      | str _ => simp [Gen.scalarWord] at hfw
    | loc _ | ctor0 _ | erased => simp [Gen.scalarWord] at hfw

/-- Specialized readback bridge for `word-w2`'s 1-scalar-word boxed `UInt64` cell
(`nobj = 0, nscalar = 1, tag = 0`): `address` is even, header has `scan = 0, tag = 0`, and
`address + 8` holds the exact raw 64-bit payload `UInt64.ofNat n`. -/
theorem boxedWord64_liveCell_readback_words {addresses : AddressMap} {mem : X86.Memory}
    {address : Word} {refs n : Nat} {key : Key.CtorKey}
    (h : Gen.LiveCell addresses mem address refs
      { ctor := { key, tag := 0, nobj := 0, nscalar := 1, fieldKinds := [] },
        fields := [.lit (.nat n)] }) :
    address &&& 1 ≠ 1 ∧
    (∃ hdr : Word, mem.read64? address = .ok hdr ∧
      (hdr &&& 0xFF).toNat = 0 ∧ ((hdr >>> 16) &&& 0xFFFF).toNat = 0) ∧
    n < 2 ^ 64 ∧ mem.read64? (address + 8) = .ok (UInt64.ofNat n) := by
  obtain ⟨heven, hhdr, _, hsc⟩ := scalar_liveCell_readback_words h
  obtain ⟨n', hval, hlt, hread⟩ := hsc 0 (.lit (.nat n)) Nat.zero_lt_one rfl
  cases hval
  exact ⟨heven, hhdr, hlt, by simpa using hread⟩

end IxCC.Cfg.Rc.Native
