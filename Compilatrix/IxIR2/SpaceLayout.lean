import Compilatrix.IxIR2.SpaceHeap

/-!
# A versioned finite-storage model for the explicit machine

`ixir2-fixed-slot-space/1` assigns bytes to a bounded Word-valued heap and
to explicit control frames. It is a resource semantics, not a native ABI or
a claim about the Lean interpreter's host allocations. Immutable code,
recursive destruction workspaces and future native register spills are not
represented here. Native unique-list arenas retain their separate ABI.

Values use two words (tag and Word payload). A cell has an 80-byte header:
kind, ownership, RC, full 32-byte identity, two identity/arity words, and field
count. The chosen field bound determines its fixed payload capacity. Empty
slots retain this entire capacity. The 96-byte descriptor accounts for the
cursor, capacity, nine evaluator counters, and reservation count.

Frames use 64 bytes for a full code identity, block, PC and array lengths;
all value entries and credit entries, including consumed entries, are charged.
A credit uses 48 bytes for its full layout identity, tag and location. Saved
continuations add a 16-byte tag/length header plus any pending arguments.
-/

namespace Compilatrix.IxIR2.Eval.Space

def policyTag : String := "ixir2-fixed-slot-space/1"
def descriptorBytes : Nat := 96
def valueBytes : Nat := 16
def cellHeaderBytes : Nat := 80
def frameHeaderBytes : Nat := 64
def creditBytes : Nat := 48
def continuationHeaderBytes : Nat := 16

structure Layout where
  fields : Nat := 2
  deriving BEq, Repr, Inhabited

def Layout.cellBytes (layout : Layout) : Nat := cellHeaderBytes + valueBytes * layout.fields

def wordFits (value : Nat) : Bool := value < UInt64.size

def valueFits : RVal → Bool
  | .loc location | .lit (.nat location) => wordFits location
  | .erased => true
  | .lit (.str _) => false

def Layout.nodeFits (layout : Layout) (box : NodeBox) : Bool :=
  wordFits box.rc && match box.node with
    | .ctorN identity fields =>
        wordFits identity.indIdx && wordFits identity.cidx &&
          fields.size ≤ layout.fields && fields.all valueFits
    | .papN _ arity arguments =>
        wordFits arity && arguments.size ≤ layout.fields && arguments.all valueFits

def creditFits : Option Credit → Bool
  | none => true
  | some { presence := .present (some location), .. } => wordFits location
  | some _ => true

def frameFits (frame : Frame) : Bool :=
  wordFits frame.block && wordFits frame.pc && wordFits frame.values.size &&
    wordFits frame.credits.size && frame.values.all valueFits && frame.credits.all creditFits

def continuationFits : Continuation → Bool
  | .resume frame => frameFits frame
  | .applyMore arguments frame =>
      frameFits frame && wordFits arguments.size && arguments.all valueFits

def frameBytes (frame : Frame) : Nat :=
  frameHeaderBytes + valueBytes * frame.values.size + creditBytes * frame.credits.size

def continuationBytes : Continuation → Nat
  | .resume frame => continuationHeaderBytes + frameBytes frame
  | .applyMore arguments frame =>
      continuationHeaderBytes + frameBytes frame + valueBytes * arguments.size

def controlBytes (machine : Machine) : Nat :=
  match machine.control with
  | .halted _ => valueBytes
  | .running frame stack => frameBytes frame + (stack.map continuationBytes).sum

def Layout.machineFits (layout : Layout) (machine : Machine) : Bool :=
  wordFits layout.fields && wordFits (descriptorBytes + layout.cellBytes * machine.store.slots) &&
    wordFits (controlBytes machine) &&
    ([machine.store.heap.allocs, machine.store.heap.reuses, machine.store.heap.frees,
      machine.store.heap.rcops, machine.store.resetAttempts, machine.store.hotResets,
      machine.store.coldResets, machine.store.reusedPayloadUnits, machine.store.peakLiveNodes,
      machine.presentCredits].all wordFits) &&
    machine.store.heap.nodes.all (fun slot => slot.all layout.nodeFits) &&
    match machine.control with
    | .halted value => valueFits value
    | .running frame stack => frameFits frame && stack.all continuationFits

def Layout.liveBytes (layout : Layout) (machine : Machine) : Nat :=
  layout.cellBytes * machine.store.live

def Layout.reservedBytes (layout : Layout) (machine : Machine) : Nat :=
  layout.cellBytes * machine.presentCredits

def Layout.occupiedBytes (layout : Layout) (machine : Machine) : Nat :=
  layout.liveBytes machine + layout.reservedBytes machine

def Layout.retainedFreeBytes (layout : Layout) (machine : Machine) : Nat :=
  layout.cellBytes * machine.store.heap.frees

def Layout.committedBytes (layout : Layout) (store : Store) : Nat :=
  descriptorBytes + layout.cellBytes * store.slots

structure Demand where
  heap : Nat
  control : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

abbrev Capacity := Demand

def Demand.within (needed available : Demand) : Bool :=
  needed.heap ≤ available.heap && needed.control ≤ available.control

def Demand.join (left right : Demand) : Demand :=
  ⟨max left.heap right.heap, max left.control right.control⟩

@[simp] theorem Demand.join_within (left right capacity : Demand) :
    (left.join right).within capacity = true ↔
      left.within capacity = true ∧ right.within capacity = true := by
  simp only [Demand.join, Demand.within, Bool.and_eq_true, decide_eq_true_eq, Nat.max_le]
  omega

def Layout.demand (layout : Layout) (machine : Machine) : Demand :=
  ⟨layout.committedBytes machine.store, controlBytes machine⟩

theorem Layout.committed_partition (layout : Layout) {policy : CreditPolicy} {context : Context}
    {count : Nat} {definition : Function} {arguments : Array RVal} {heapFuel : Nat}
    {machine : Machine}
    (steps : Policy.Steps policy context .physical count
      (initialMachine definition arguments heapFuel) machine) :
    layout.committedBytes machine.store = descriptorBytes +
      layout.occupiedBytes machine + layout.retainedFreeBytes machine := by
  rw [Layout.committedBytes, steps.slot_partition.2]
  simp [Layout.occupiedBytes, Layout.liveBytes, Layout.reservedBytes,
    Layout.retainedFreeBytes, Nat.mul_add, Nat.add_assoc]

theorem Layout.prefix_capacity (layout : Layout) {policy : CreditPolicy} {context : Context}
    {fuel prefixCount : Nat} {initial middle : Machine} {result : Result}
    (run : Policy.runMachine policy context .physical fuel initial = .ok result)
    (prefixSteps : Policy.Steps policy context .physical prefixCount initial middle) :
    layout.committedBytes middle.store ≤ layout.committedBytes result.store := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Policy.runMachine_prefix_slots run prefixSteps)) _

/-- Suspending a call keeps the caller's entire frame and all its reserved
heap capacity. It adds the new callee frame and a continuation header. -/
theorem suspendCall_bytes (layout : Layout) {context : Context} {before after : Machine}
    {frame : Frame} {stack : List Continuation} {call : Policy.DirectCall}
    (running : before.control = .running frame stack)
    (called : Policy.suspendCall context before frame stack call = .ok after) :
    layout.committedBytes after.store = layout.committedBytes before.store ∧
      layout.reservedBytes after = layout.reservedBytes before ∧
      ∃ arguments, resolveAtoms frame.values call.arguments = .ok arguments ∧
        controlBytes after = controlBytes before + frameHeaderBytes +
          continuationHeaderBytes + valueBytes * arguments.size := by
  have resources := Policy.suspendCall_resources running called
  refine ⟨congrArg layout.committedBytes resources.1, ?_, ?_⟩
  · simp only [Layout.reservedBytes, resources.2.2]
  · obtain ⟨arguments, definition, resolved, _, _, _, rfl⟩ := Policy.suspendCall_iff.mp called
    refine ⟨arguments, resolved, ?_⟩
    simp [controlBytes, running, continuationBytes, frameBytes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Compilatrix.IxIR2.Eval.Space
