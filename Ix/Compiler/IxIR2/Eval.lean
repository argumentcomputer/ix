import Ix.Compiler.IxIR1.Eval
import Ix.Compiler.IxIR2.Validate

/-!
# Logical and physical execution for IxIR₂

The two interpretations share one small-step control machine.  Logical
execution frees a consumed constructor immediately and allocates freshly at
`allocWith`; physical execution reserves the slot and either reuses or
releases it.  Calls are represented by an explicit continuation stack, so the
total runner spends exactly one control unit per IxIR₂ instruction or
terminator.  Recursive heap traversal has an independent budget.
-/

namespace Ix.Compiler.IxIR2.Eval

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR2

abbrev RVal := IxIR1.RVal
abbrev Node := IxIR1.Node
abbrev NodeBox := IxIR1.NodeBox

inductive Interpretation where
  | logical
  | physical
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

inductive Error where
  | controlFuel
  | heapFuel
  | stuck (detail : String)
  | mem (detail : String)
  | unknownRef (address : Address)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Counters shared by the logical and physical observations. -/
structure Counters where
  allocs : Nat := 0
  reuses : Nat := 0
  frees : Nat := 0
  rcops : Nat := 0
  resetAttempts : Nat := 0
  hotResets : Nat := 0
  coldResets : Nat := 0
  reusedPayloadUnits : Nat := 0
  peakLiveNodes : Nat := 0
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The IxIR₁ heap representation is reused deliberately.  IxIR₂ adds reset
observations while preserving the existing constructor/PAP runtime boundary. -/
structure Store where
  heap : IxIR1.Store := {}
  resetAttempts : Nat := 0
  hotResets : Nat := 0
  coldResets : Nat := 0
  reusedPayloadUnits : Nat := 0
  peakLiveNodes : Nat := 0
  deriving Repr, Inhabited

def Store.get? (store : Store) (location : Nat) : Option NodeBox :=
  store.heap.get? location

def Store.live (store : Store) : Nat := store.heap.live

def Store.counters (store : Store) : Counters :=
  { allocs := store.heap.allocs
    reuses := store.heap.reuses
    frees := store.heap.frees
    rcops := store.heap.rcops
    resetAttempts := store.resetAttempts
    hotResets := store.hotResets
    coldResets := store.coldResets
    reusedPayloadUnits := store.reusedPayloadUnits
    peakLiveNodes := store.peakLiveNodes }

private def Store.withPeak (store : Store) : Store :=
  { store with peakLiveNodes := max store.peakLiveNodes store.live }

@[simp] theorem Store.withPeak_heap (store : Store) :
    store.withPeak.heap = store.heap := by
  rfl

def Store.allocNode (store : Store) (world : Owned) (node : Node) :
    Store × Nat :=
  let (heap, location) := store.heap.allocNode world node
  ({ store with heap }.withPeak, location)

@[simp] theorem Store.allocNode_heap (store : Store) (world : Owned)
    (node : Node) :
    (store.allocNode world node).1.heap =
      (store.heap.allocNode world node).1 := by
  rfl

@[simp] theorem Store.allocNode_location (store : Store) (world : Owned)
    (node : Node) :
    (store.allocNode world node).2 =
      (store.heap.allocNode world node).2 := by
  rfl

def Store.setBox (store : Store) (location : Nat) (box : NodeBox) : Store :=
  { store with heap := store.heap.setBox location box }

@[simp] theorem Store.setBox_heap (store : Store) (location : Nat)
    (box : NodeBox) :
    (store.setBox location box).heap = store.heap.setBox location box := by
  rfl

def Store.kill (store : Store) (location : Nat) : Store :=
  { store with heap := store.heap.kill location }

@[simp] theorem Store.kill_heap (store : Store) (location : Nat) :
    (store.kill location).heap = store.heap.kill location := by
  rfl

def Store.rcTick (store : Store) : Store :=
  { store with heap := store.heap.rcTick }

@[simp] theorem Store.rcTick_heap (store : Store) :
    store.rcTick.heap = store.heap.rcTick := by
  rfl

/-- Remove a live node without counting a free.  The physical credit becomes
the sole authority for this empty slot. -/
def Store.reserve (store : Store) (location : Nat) : Store :=
  { store with
    heap := { store.heap with
      nodes := store.heap.nodes.setIfInBounds location none } }

def Store.releaseReservation (store : Store) (location : Nat) :
    Except Error Store :=
  match (store.heap.nodes)[location]? with
  | some none =>
      .ok { store with heap := { store.heap with frees := store.heap.frees + 1 } }
  | _ => .error (.mem "release of a non-reserved physical slot")

def Store.reuseReservation (store : Store) (location : Nat) (world : Owned)
    (node : Node) (payloadUnits : Nat) : Except Error Store :=
  match (store.heap.nodes)[location]? with
  | some none =>
      let box : NodeBox := { world, rc := 1, node }
      let heap :=
        { store.heap with
          nodes := store.heap.nodes.setIfInBounds location (some box)
          reuses := store.heap.reuses + 1 }
      .ok ({ store with
        heap
        reusedPayloadUnits := store.reusedPayloadUnits + payloadUnits }).withPeak
  | _ => .error (.mem "reuse of a non-reserved physical slot")

def Store.tickResetAttempt (store : Store) : Store :=
  { store with resetAttempts := store.resetAttempts + 1 }

def Store.tickHotReset (store : Store) : Store :=
  { store with hotResets := store.hotResets + 1 }

def Store.tickColdReset (store : Store) : Store :=
  { store with coldResets := store.coldResets + 1 }

inductive CreditPresence where
  | absent
  /-- `none` in the logical interpretation, the reserved slot in physical. -/
  | present (reservation : Option Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

structure Credit where
  layout : LayoutId
  presence : CreditPresence
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

def Credit.isPresent : Credit → Bool
  | { presence := .present _, .. } => true
  | { presence := .absent, .. } => false

private def Credit.presentFor (interpretation : Interpretation)
    (layout : LayoutId) (location : Nat) : Credit :=
  match interpretation with
  | .logical => { layout, presence := .present none }
  | .physical => { layout, presence := .present (some location) }

structure Context where
  declarations : Address → Option Decl := fun _ => none
  schemas : Owned → CtorId → Option CtorSchema := fun _ _ => none
  oracle : Address → List RVal → Option RVal := fun _ _ => none

def Context.ofProgram (program : Program)
    (schemas : Owned → CtorId → Option CtorSchema)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) : Context :=
  { declarations := fun address =>
      (program.declarations.find? fun entry => entry.1 == address).map (·.2)
    schemas
    oracle }

def RVal.isScalar : RVal → Bool
  | .loc _ => false
  | .lit _ | .erased => true

def RVal.hasWorld (store : Store) (world : Owned) : RVal → Bool
  | .loc location =>
      match store.get? location with
      | some box => box.world == world
      | none => false
  | .lit _ | .erased => true

def resolveAtom (values : Array RVal) : Atom → Except Error RVal
  | .reg id =>
      match (values)[id]? with
      | some value => .ok value
      | none => .error (.stuck s!"unknown value register {id}")
  | .lit literal => .ok (.lit literal)
  | .erased => .ok .erased

def resolveAtoms (values : Array RVal) (atoms : Array Atom) :
    Except Error (Array RVal) :=
  atoms.foldlM (fun output atom => do
    return output.push (← resolveAtom values atom)) #[]

private def lookupSchema (context : Context) (world : Owned) (cid : CtorId) :
    Except Error CtorSchema :=
  match context.schemas world cid with
  | some schema => .ok schema
  | none => .error (.stuck "missing constructor schema")

private def requireCtor (store : Store) (location : Nat) (world : Owned)
    (cid : CtorId) : Except Error (NodeBox × Array RVal) := do
  let box ← match store.get? location with
    | some box => pure box
    | none => .error (.mem s!"dead constructor location {location}")
  if box.world != world then
    .error (.mem "constructor ownership-world mismatch")
  else
    match box.node with
    | .ctorN actual fields =>
        if actual == cid then return (box, fields)
        else .error (.stuck "constructor identity mismatch")
    | .papN .. => .error (.stuck "constructor operation on a PAP")

/-! ## Heap-only recursive primitives -/

/-- Increment one shared reference, leaving scalar values unchanged. -/
def retainShared (store : Store) (value : RVal) : Except Error Store :=
  match value with
  | .lit _ | .erased => .ok store
  | .loc location =>
      match store.get? location with
      | none => .error (.mem s!"retain of dead location {location}")
      | some box =>
          if box.world != .shared then
            .error (.mem "retain of a unique node")
          else
            .ok ((store.setBox location { box with rc := box.rc + 1 }).rcTick)

private def retainSharedMany (store : Store) (values : Array RVal) :
    Except Error Store :=
  values.foldlM retainShared store

/-- Deep shared release.  Every work-list item, including a scalar leaf,
consumes one heap-traversal unit; control fuel is not visible here. -/
def releaseSharedWork : Nat → Store → List RVal → Except Error (Store × Nat)
  | fuel, store, [] => .ok (store, fuel)
  | 0, _, _ :: _ => .error .heapFuel
  | fuel + 1, store, value :: rest =>
      match value with
      | .lit _ | .erased => releaseSharedWork fuel store rest
      | .loc location =>
          match store.get? location with
          | none => .error (.mem s!"release of dead location {location}")
          | some box =>
              if box.world != .shared then
                .error (.mem "release of a unique node")
              else
                let store := store.rcTick
                if box.rc == 0 then
                  .error (.mem "shared node has zero refcount")
                else if box.rc == 1 then
                  let children := match box.node with
                    | .ctorN _ fields => fields.toList
                    | .papN _ _ arguments => arguments.toList
                  releaseSharedWork fuel (store.kill location) (children ++ rest)
                else
                  releaseSharedWork fuel
                    (store.setBox location { box with rc := box.rc - 1 }) rest

def releaseShared (heapFuel : Nat) (store : Store) (value : RVal) :
    Except Error (Store × Nat) :=
  releaseSharedWork heapFuel store [value]

/-- Deep unique destruction with a separate work-list budget. -/
def dropUniqueWork : Nat → Store → List RVal → Except Error (Store × Nat)
  | fuel, store, [] => .ok (store, fuel)
  | 0, _, _ :: _ => .error .heapFuel
  | fuel + 1, store, value :: rest =>
      match value with
      | .lit _ | .erased => dropUniqueWork fuel store rest
      | .loc location =>
          match store.get? location with
          | none => .error (.mem s!"dropUnique of dead location {location}")
          | some box =>
              if box.world != .unique then
                .error (.mem "dropUnique of a shared node")
              else
                match box.node with
                | .papN .. => .error (.mem "dropUnique of a PAP")
                | .ctorN _ fields =>
                    dropUniqueWork fuel (store.kill location)
                      (fields.toList ++ rest)

def dropUnique (heapFuel : Nat) (store : Store) (value : RVal) :
    Except Error (Store × Nat) :=
  dropUniqueWork heapFuel store [value]

/-! ## Small-step control machine -/

structure Frame where
  definition : Function
  block : BlockId := 0
  pc : Nat := 0
  values : Array RVal := #[]
  credits : Array (Option Credit) := #[]
  deriving Repr, Inhabited

inductive Continuation where
  | resume (frame : Frame)
  | applyMore (arguments : Array RVal) (frame : Frame)
  deriving Repr, Inhabited

inductive Control where
  | running (frame : Frame) (stack : List Continuation)
  | halted (value : RVal)
  deriving Repr, Inhabited

structure Machine where
  store : Store := {}
  heapFuel : Nat := 0
  control : Control
  deriving Repr, Inhabited

structure Result where
  store : Store
  value : RVal
  controlRemaining : Nat
  heapRemaining : Nat
  deriving Repr, Inhabited

def creditPresentCount (credits : Array (Option Credit)) : Nat :=
  credits.foldl (fun total credit =>
    match credit with
    | some credit => if credit.isPresent then total + 1 else total
    | none => total) 0

def Frame.presentCredits (frame : Frame) : Nat :=
  creditPresentCount frame.credits

def Continuation.presentCredits : Continuation → Nat
  | .resume frame | .applyMore _ frame => frame.presentCredits

def Machine.presentCredits (machine : Machine) : Nat :=
  match machine.control with
  | .halted _ => 0
  | .running frame stack =>
      frame.presentCredits +
        stack.foldl (fun total continuation =>
          total + continuation.presentCredits) 0

private def Frame.advance (frame : Frame) : Frame :=
  { frame with pc := frame.pc + 1 }

private def Frame.pushValue (frame : Frame) (value : RVal) : Frame :=
  { frame with values := frame.values.push value }

private def Frame.pushValues (frame : Frame) (values : Array RVal) : Frame :=
  { frame with values := frame.values ++ values }

private def Frame.pushCredit (frame : Frame) (credit : Credit) : Frame :=
  { frame with credits := frame.credits.push (some credit) }

private def Frame.hasCredits (frame : Frame) : Bool :=
  frame.credits.any Option.isSome

private def currentBlock (frame : Frame) : Except Error Block :=
  match (frame.definition.blocks)[frame.block]? with
  | some block => .ok block
  | none => .error (.stuck s!"missing current block {frame.block}")

/-- Shared entry check for both versioned credit policies. Every callee starts
with an empty credit register file; caller credits stay in its continuation. -/
def enterFunction (definition : Function) (arguments : Array RVal) :
    Except Error Frame :=
  if arguments.size != definition.signature.params.size then
    .error (.stuck "function argument arity mismatch")
  else if definition.blocks.isEmpty then
    .error (.stuck "function has no entry block")
  else
    .ok { definition, values := arguments }

private def creditAt (frame : Frame) (id : CreditId) : Except Error Credit :=
  match (frame.credits)[id]? with
  | some (some credit) => .ok credit
  | some none => .error (.mem s!"credit {id} was already consumed")
  | none => .error (.stuck s!"unknown credit register {id}")

private def takeCredit (frame : Frame) (id : CreditId) :
    Except Error (Frame × Credit) := do
  let credit ← creditAt frame id
  return ({ frame with credits := frame.credits.setIfInBounds id none }, credit)

private def takeCredits (frame : Frame) (ids : Array CreditId) :
    Except Error (Frame × Array Credit) :=
  ids.foldlM (fun state id => do
    let (frame, credit) ← takeCredit state.1 id
    return (frame, state.2.push credit)) (frame, #[])

private def checkFieldWorlds (store : Store) (schema : CtorSchema)
    (values : Array RVal) : Except Error Unit := do
  if values.size != schema.fields.size then
    .error (.stuck "constructor field-count mismatch")
  else
    for pair in values.toList.zip schema.fields.toList do
      if !pair.1.hasWorld store pair.2 then
        .error (.mem "constructor field ownership-world mismatch")

/-- Public semantic premise used by allocation reduction and simulation
lemmas.  Its executable witness remains shared with the evaluator. -/
def FieldWorlds (store : Store) (schema : CtorSchema)
    (values : Array RVal) : Prop :=
  checkFieldWorlds store schema values = .ok ()

/-- The executable field check certifies the actual runtime payload arity. -/
theorem FieldWorlds.size {store : Store} {schema : CtorSchema} {values : Array RVal}
    (checked : FieldWorlds store schema values) : values.size = schema.fields.size := by
  by_cases same : values.size = schema.fields.size
  · exact same
  · simp [FieldWorlds, checkFieldWorlds, same] at checked

/-- A uniform constructor schema accepts an equally sized value vector when
every value inhabits that world.  Baseline pipeline schemas have exactly this
form, so semantic simulation can discharge the evaluator's executable field
check from source ownership evidence. -/
theorem FieldWorlds.of_replicate {store : Store} {schema : CtorSchema}
    {values : Array RVal} {world : Owned} {count : Nat}
    (schemaFields : schema.fields = Array.replicate count world)
    (valueCount : values.size = count)
    (worlds : ∀ value ∈ values.toList,
      RVal.hasWorld store world value = true) :
    FieldWorlds store schema values := by
  have loop : ∀ entries : List RVal,
      (∀ value ∈ entries, RVal.hasWorld store world value = true) →
      (for pair in entries.zip (List.replicate entries.length world) do
          if !RVal.hasWorld store pair.2 pair.1 then
            Except.error
              (Error.mem "constructor field ownership-world mismatch")) =
        Except.ok PUnit.unit := by
    intro entries entryWorlds
    induction entries with
    | nil => rfl
    | cons value rest ih =>
        have head := entryWorlds value (by simp)
        have tail : ∀ candidate ∈ rest,
            RVal.hasWorld store world candidate = true := by
          intro candidate member
          exact entryWorlds candidate (by simp [member])
        simp only [List.length_cons, List.replicate_succ,
          List.zip_cons_cons, List.forIn_cons]
        have headFalse :
            (!RVal.hasWorld store world value) = false := by
          simp [head]
        rw [headFalse]
        simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
          pure, Except.pure]
        exact ih tail
  unfold FieldWorlds checkFieldWorlds
  rw [schemaFields]
  have sizes :
      (values.size != (Array.replicate count world).size) = false := by
    simp [valueCount]
  rw [sizes]
  simp only [Bool.false_eq_true, ↓reduceIte, Array.toList_replicate]
  have lengthEq : values.toList.length = count := by
    simpa using valueCount
  rw [← lengthEq]
  rw [loop values.toList worlds]

/-- Inversion of `of_replicate`: a successful uniform-schema check exposes
both the exact field count and the dynamic world of every field. -/
theorem FieldWorlds.to_replicate {store : Store} {schema : CtorSchema}
    {values : Array RVal} {world : Owned} {count : Nat}
    (schemaFields : schema.fields = Array.replicate count world)
    (worlds : FieldWorlds store schema values) :
    values.size = count ∧
      ∀ value ∈ values.toList,
        RVal.hasWorld store world value = true := by
  have loop : ∀ entries : List RVal,
      (for pair in entries.zip (List.replicate entries.length world) do
          if !RVal.hasWorld store pair.2 pair.1 then
            Except.error
              (Error.mem "constructor field ownership-world mismatch")) =
        Except.ok PUnit.unit →
      ∀ value ∈ entries,
        RVal.hasWorld store world value = true := by
    intro entries
    induction entries with
    | nil => simp
    | cons head tail ih =>
        intro run value member
        simp only [List.length_cons, List.replicate_succ,
          List.zip_cons_cons, List.forIn_cons] at run
        have headWorld : RVal.hasWorld store world head = true := by
          cases found : RVal.hasWorld store world head with
          | false =>
              simp only [found, Bool.not_false, ↓reduceIte, bind,
                Except.bind] at run
              cases run
          | true => rfl
        have tailRun :
            (for pair in tail.zip (List.replicate tail.length world) do
                if !RVal.hasWorld store pair.2 pair.1 then
                  Except.error
                    (Error.mem
                      "constructor field ownership-world mismatch")) =
              Except.ok PUnit.unit := by
          simpa [headWorld] using run
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact headWorld
        · exact ih tailRun value member
  unfold FieldWorlds checkFieldWorlds at worlds
  rw [schemaFields] at worlds
  by_cases valueCount : values.size = count
  · have sizes :
        (values.size != (Array.replicate count world).size) = false := by
      simp [valueCount]
    rw [sizes] at worlds
    simp only [Bool.false_eq_true, ↓reduceIte,
      Array.toList_replicate] at worlds
    have lengthEq : values.toList.length = count := by
      simpa using valueCount
    rw [← lengthEq] at worlds
    exact ⟨valueCount, loop values.toList worlds⟩
  · have sizes :
        (values.size != (Array.replicate count world).size) = true := by
      simp [valueCount]
    rw [sizes] at worlds
    simp at worlds

/-- Constructor-field validation depends on a store only through the dynamic
world observed for each field value.  This congruence theorem lets semantic
simulations transport `FieldWorlds` across a heap relation without unfolding
the evaluator's private checker. -/
theorem FieldWorlds.congrStore {left right : Store} {schema : CtorSchema}
    {values : Array RVal}
    (sameWorlds : ∀ world value,
      RVal.hasWorld left world value = RVal.hasWorld right world value)
    (worlds : FieldWorlds left schema values) :
    FieldWorlds right schema values := by
  unfold FieldWorlds checkFieldWorlds at worlds ⊢
  simpa only [← sameWorlds] using worlds

/-- Pointwise value relation used by the public field-check transport seam. -/
inductive FieldValuesWorldEq (left right : Store) :
    List RVal → List RVal → Prop where
  | nil : FieldValuesWorldEq left right [] []
  | cons {leftValue rightValue : RVal} {lefts rights : List RVal}
      (head : ∀ world,
        RVal.hasWorld left world leftValue =
          RVal.hasWorld right world rightValue)
      (tail : FieldValuesWorldEq left right lefts rights) :
      FieldValuesWorldEq left right (leftValue :: lefts)
        (rightValue :: rights)

theorem FieldValuesWorldEq.length_eq {left right : Store} :
    ∀ {lefts rights : List RVal},
      FieldValuesWorldEq left right lefts rights →
      lefts.length = rights.length
  | _, _, .nil => rfl
  | _, _, .cons _ tail => by simp [tail.length_eq]

/-- Constructor-field validation transports across pointwise values that make
the same dynamic ownership observation.  This is the allocation-facing
equivariance interface: clients need not unfold the private checker or require
the two value vectors to use identical concrete heap locations. -/
theorem FieldWorlds.transport {left right : Store} {schema : CtorSchema}
    {leftValues rightValues : Array RVal}
    (related : FieldValuesWorldEq left right
      leftValues.toList rightValues.toList)
    (worlds : FieldWorlds left schema leftValues) :
    FieldWorlds right schema rightValues := by
  have sizes : leftValues.size = rightValues.size := by
    simpa using related.length_eq
  have loop : ∀ {lefts rights : List RVal},
      FieldValuesWorldEq left right lefts rights →
      ∀ schemaFields : List Owned,
        ((for pair in lefts.zip schemaFields do
            if !pair.1.hasWorld left pair.2 then
              Except.error
                (Error.mem "constructor field ownership-world mismatch")) :
            Except Error Unit) =
          ((for pair in rights.zip schemaFields do
            if !pair.1.hasWorld right pair.2 then
              Except.error
                (Error.mem "constructor field ownership-world mismatch")) :
            Except Error Unit) := by
    intro lefts rights valuesRelated
    induction valuesRelated with
    | nil => intro schemaFields; simp
    | cons valueRelated tailRelated ih =>
        intro schemaFields
        cases schemaFields with
        | nil => rfl
        | cons world rest =>
            simp only [List.zip_cons_cons, List.forIn_cons]
            rw [valueRelated world]
            split <;> simp only [bind, Except.bind, pure, Except.pure]
            exact ih rest
  unfold FieldWorlds checkFieldWorlds at worlds ⊢
  rw [← sizes]
  rw [← loop related schema.fields.toList]
  exact worlds

/-- Pointwise preservation of successful world observations. Dead historical
registers need not have the same observations after physical reuse. -/
inductive FieldValuesWorldForward (left right : Store) : List RVal → List RVal → Prop where
  | nil : FieldValuesWorldForward left right [] []
  | cons {leftValue rightValue : RVal} {lefts rights : List RVal}
      (head : ∀ world, RVal.hasWorld left world leftValue = true →
        RVal.hasWorld right world rightValue = true)
      (tail : FieldValuesWorldForward left right lefts rights) :
      FieldValuesWorldForward left right (leftValue :: lefts) (rightValue :: rights)

theorem FieldValuesWorldForward.length_eq {left right : Store} :
    ∀ {lefts rights : List RVal}, FieldValuesWorldForward left right lefts rights →
      lefts.length = rights.length
  | _, _, .nil => rfl
  | _, _, .cons _ tail => by simp [tail.length_eq]

theorem FieldWorlds.forward {left right : Store} {schema : CtorSchema}
    {leftValues rightValues : Array RVal}
    (related : FieldValuesWorldForward left right leftValues.toList rightValues.toList)
    (worlds : FieldWorlds left schema leftValues) : FieldWorlds right schema rightValues := by
  have sizes : leftValues.size = rightValues.size := by simpa using related.length_eq
  have loop : ∀ {lefts rights : List RVal},
      FieldValuesWorldForward left right lefts rights → ∀ schemaFields : List Owned,
        ((for pair in lefts.zip schemaFields do
            if !pair.1.hasWorld left pair.2 then
              Except.error (Error.mem "constructor field ownership-world mismatch")) :
            Except Error Unit) = .ok () →
        ((for pair in rights.zip schemaFields do
            if !pair.1.hasWorld right pair.2 then
              Except.error (Error.mem "constructor field ownership-world mismatch")) :
            Except Error Unit) = .ok () := by
    intro lefts rights related
    induction related with
    | nil => intro schemaFields checked; simpa using checked
    | @cons leftValue rightValue lefts rights head tail ih =>
        intro schemaFields checked
        cases schemaFields with
        | nil => rfl
        | cons world rest =>
            simp only [List.zip_cons_cons, List.forIn_cons] at checked ⊢
            cases observed : RVal.hasWorld left world leftValue with
            | false => simp [observed, bind, Except.bind] at checked
            | true =>
                have rightObserved := head world observed
                simp [observed, bind, Except.bind, pure, Except.pure] at checked
                simpa [rightObserved, bind, Except.bind, pure, Except.pure] using
                  ih rest (by simpa [bind, Except.bind, pure, Except.pure] using checked)
  have arity := worlds.size
  unfold FieldWorlds checkFieldWorlds at worlds ⊢
  simp only [← sizes, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at worlds ⊢
  exact loop related schema.fields.toList worlds

private def callScalarOracle (context : Context) (address : Address)
    (arguments : Array RVal) : Except Error RVal :=
  if !arguments.all RVal.isScalar then
    .error (.mem "extern heap arguments require an ownership policy")
  else
    match context.oracle address arguments.toList with
    | none => .error (.unknownRef address)
    | some value =>
        if value.isScalar then .ok value
        else .error (.mem "extern heap results require an ownership policy")

private def declarationArity : Decl → Nat
  | .fn definition => definition.signature.params.size
  | .extern arity => arity

private def declarationPapSafe : Decl → Bool
  | .fn definition => definition.signature.papSafe
  | .extern _ => true

private def ensureCallBoundary (frame : Frame) : Except Error Unit :=
  if frame.hasCredits then
    .error (.mem "reuse credit crossed a call boundary")
  else
    return ()

private def resumeImmediate (store : Store) (heapFuel : Nat) (value : RVal)
    (frame : Frame) (stack : List Continuation) : Machine :=
  { store := store
    heapFuel := heapFuel
    control := .running (frame.pushValue value) stack }

private def beginApply (context : Context) (_interpretation : Interpretation)
    (store : Store) (heapFuel : Nat) (function : RVal)
    (arguments : Array RVal) (resume : Frame) (stack : List Continuation) :
    Except Error Machine := do
  match function with
  | .lit _ => .error (.stuck "apply of a scalar literal")
  | .erased =>
      let (store, heapFuel) ←
        releaseSharedWork heapFuel store arguments.toList
      return resumeImmediate store heapFuel .erased resume stack
  | .loc location =>
      let box ← match store.get? location with
        | some box => pure box
        | none => .error (.mem s!"apply of dead location {location}")
      if box.world != .shared then
        .error (.mem "apply of a unique node")
      else
        match box.node with
        | .ctorN .. => .error (.stuck "apply of a constructor node")
        | .papN address arity captured =>
            if captured.size >= arity then
              .error (.stuck "malformed saturated PAP")
            else
              let store ← retainSharedMany store captured
              let (store, heapFuel) ←
                releaseSharedWork heapFuel store [.loc location]
              let total := captured ++ arguments
              if total.size < arity then
                let (store, location) :=
                  store.allocNode .shared (.papN address arity total)
                return resumeImmediate store heapFuel (.loc location) resume stack
              else
                let declaration ← match context.declarations address with
                  | some declaration => pure declaration
                  | none => .error (.unknownRef address)
                if !declarationPapSafe declaration then
                  .error (.stuck "shared PAP targets a non-pap-safe function")
                else
                  let supplied := total.extract 0 arity
                  let rest := total.extract arity total.size
                  match declaration with
                  | .fn definition =>
                      let callee ← enterFunction definition supplied
                      let continuation : Continuation :=
                        if rest.isEmpty then Continuation.resume resume
                        else Continuation.applyMore rest resume
                      let nextMachine : Machine :=
                        { store := store
                          heapFuel := heapFuel
                          control := .running callee (continuation :: stack) }
                      return nextMachine
                  | .extern expectedArity =>
                      if supplied.size != expectedArity then
                        .error (.stuck "extern PAP arity mismatch")
                      else if !rest.isEmpty then
                        .error (.stuck "over-application of a scalar extern result")
                      else
                        let value ← callScalarOracle context address supplied
                        return resumeImmediate store heapFuel value resume stack

private def transferEdge (frame : Frame) (edge : Edge)
    (implicitValues : Array RVal := #[]) : Except Error Frame := do
  let values ← resolveAtoms frame.values edge.values
  let (frame, credits) ← takeCredits frame edge.credits
  if frame.hasCredits then
    .error (.mem "edge abandoned a live reuse credit")
  else
    let target ← match (frame.definition.blocks)[edge.target]? with
      | some block => pure block
      | none => .error (.stuck s!"edge targets missing block {edge.target}")
    let values := implicitValues ++ values
    if values.size != target.valueParams.size then
      .error (.stuck "edge value arity mismatch")
    else if credits.size != target.creditParams.size then
      .error (.stuck "edge credit arity mismatch")
    else
      return { frame with
        block := edge.target
        pc := 0
        values
        credits := credits.map some }

private def runInstruction (context : Context)
    (interpretation : Interpretation) (machine : Machine) (frame : Frame)
    (stack : List Continuation) (instruction : Instr) : Except Error Machine := do
  let next := frame.advance
  match instruction with
  | .move atom =>
      let value ← resolveAtom frame.values atom
      return { machine with control := .running (next.pushValue value) stack }
  | .alloc world cid arguments =>
      let schema ← lookupSchema context world cid
      let values ← resolveAtoms frame.values arguments
      checkFieldWorlds machine.store schema values
      let (store, location) := machine.store.allocNode world (.ctorN cid values)
      return { machine with
        store
        control := .running (next.pushValue (.loc location)) stack }
  | .allocWith creditId world cid arguments =>
      let schema ← lookupSchema context world cid
      let values ← resolveAtoms frame.values arguments
      checkFieldWorlds machine.store schema values
      let (next, credit) ← takeCredit next creditId
      if credit.layout != schema.layout then
        .error (.mem "allocWith credit layout mismatch")
      else
        match interpretation, credit.presence with
        | _, .absent =>
            let (store, location) :=
              machine.store.allocNode world (.ctorN cid values)
            return { machine with
              store
              control := .running (next.pushValue (.loc location)) stack }
        | .logical, .present none =>
            let (store, location) :=
              machine.store.allocNode world (.ctorN cid values)
            return { machine with
              store
              control := .running (next.pushValue (.loc location)) stack }
        | .physical, .present (some location) =>
            let store ← machine.store.reuseReservation location world
              (.ctorN cid values) schema.fields.size
            return { machine with
              store
              control := .running (next.pushValue (.loc location)) stack }
        | _, .present _ =>
            .error (.mem "credit reservation belongs to the other interpretation")
  | .discardCredit creditId =>
      let (next, credit) ← takeCredit next creditId
      let store ← match interpretation, credit.presence with
        | _, .absent => pure machine.store
        | .logical, .present none => pure machine.store
        | .physical, .present (some location) =>
            machine.store.releaseReservation location
        | _, .present _ =>
            .error (.mem "credit reservation belongs to the other interpretation")
      return { machine with store, control := .running next stack }
  | .takeUnique target cid =>
      let schema ← lookupSchema context .unique cid
      match ← resolveAtom frame.values target with
      | .loc location =>
          let (box, fields) ← requireCtor machine.store location .unique cid
          if box.rc != 1 then
            .error (.mem "unique constructor has a non-unit refcount")
          else
            let store := match interpretation with
              | .logical => machine.store.kill location
              | .physical => machine.store.reserve location
            let credit := Credit.presentFor interpretation schema.layout location
            let next := (next.pushValues fields).pushCredit credit
            return { machine with store, control := .running next stack }
      | _ => .error (.mem "takeUnique requires a constructor location")
  | .resetShared target cid =>
      let schema ← lookupSchema context .shared cid
      match ← resolveAtom frame.values target with
      | .loc location =>
          let (box, fields) ← requireCtor machine.store location .shared cid
          let store := machine.store.tickResetAttempt
          if box.rc == 0 then
            .error (.mem "shared constructor has zero refcount")
          else if box.rc == 1 then
            let store := (match interpretation with
              | .logical => store.kill location
              | .physical => store.reserve location).tickHotReset
            let credit := Credit.presentFor interpretation schema.layout location
            let next := (next.pushValues fields).pushCredit credit
            return { machine with store, control := .running next stack }
          else
            let store :=
              ((store.setBox location { box with rc := box.rc - 1 }).rcTick).tickColdReset
            let store ← retainSharedMany store fields
            let credit : Credit := { layout := schema.layout, presence := .absent }
            let next := (next.pushValues fields).pushCredit credit
            return { machine with store, control := .running next stack }
      | _ => .error (.mem "resetShared requires a constructor location")
  | .retainShared target =>
      let value ← resolveAtom frame.values target
      let store ← retainShared machine.store value
      return { machine with
        store
        control := .running (next.pushValue value) stack }
  | .releaseShared target =>
      let value ← resolveAtom frame.values target
      let (store, heapFuel) ← releaseShared machine.heapFuel machine.store value
      return { store, heapFuel, control := .running next stack }
  | .dropUnique target =>
      let value ← resolveAtom frame.values target
      let (store, heapFuel) ← dropUnique machine.heapFuel machine.store value
      return { store, heapFuel, control := .running next stack }
  | .freeUnique target cid =>
      match ← resolveAtom frame.values target with
      | .loc location =>
          let (_, fields) ← requireCtor machine.store location .unique cid
          if !fields.all RVal.isScalar then
            .error (.mem "freeUnique requires an all-scalar constructor")
          else
            return { machine with
              store := machine.store.kill location
              control := .running next stack }
      | _ => .error (.mem "freeUnique requires a constructor location")
  | .fetch target cid field =>
      match ← resolveAtom frame.values target with
      | .loc location =>
          let box ← match machine.store.get? location with
            | some box => pure box
            | none => .error (.mem s!"fetch from dead location {location}")
          match box.node with
          | .papN .. => .error (.stuck "fetch from a PAP")
          | .ctorN actual fields =>
              if actual != cid then
                .error (.stuck "fetch constructor identity mismatch")
              else
                match (fields)[field]? with
                | some value =>
                    return { machine with
                      control := .running (next.pushValue value) stack }
                | none => .error (.stuck s!"fetch field {field} out of range")
      | _ => .error (.stuck "fetch from a non-location")
  | .call address arguments =>
      ensureCallBoundary frame
      let values ← resolveAtoms frame.values arguments
      match context.declarations address with
      | some (.fn definition) =>
          let callee ← enterFunction definition values
          return { machine with
            control := .running callee (.resume next :: stack) }
      | some (.extern _) => .error (.stuck "call must not target an extern")
      | none => .error (.unknownRef address)
  | .callSelf arguments =>
      ensureCallBoundary frame
      let values ← resolveAtoms frame.values arguments
      let callee ← enterFunction frame.definition values
      return { machine with control := .running callee (.resume next :: stack) }
  | .papp address arguments =>
      ensureCallBoundary frame
      let values ← resolveAtoms frame.values arguments
      let declaration ← match context.declarations address with
        | some declaration => pure declaration
        | none => .error (.unknownRef address)
      let arity := declarationArity declaration
      if !declarationPapSafe declaration then
        .error (.stuck "PAP target is not papSafe")
      else if values.size >= arity then
        .error (.stuck "papp must be strictly under-saturated")
      else
        let (store, location) :=
          machine.store.allocNode .shared (.papN address arity values)
        return { machine with
          store
          control := .running (next.pushValue (.loc location)) stack }
  | .apply function arguments =>
      ensureCallBoundary frame
      let function ← resolveAtom frame.values function
      let arguments ← resolveAtoms frame.values arguments
      beginApply context interpretation machine.store machine.heapFuel function
        arguments next stack
  | .extern address arguments =>
      ensureCallBoundary frame
      let values ← resolveAtoms frame.values arguments
      match context.declarations address with
      | some (.extern arity) =>
          if values.size != arity then
            .error (.stuck "extern arity mismatch")
          else
            let value ← callScalarOracle context address values
            return { machine with control := .running (next.pushValue value) stack }
      | some (.fn _) => .error (.stuck "extern instruction targets a function")
      | none => .error (.unknownRef address)

private def finishReturn (context : Context)
    (interpretation : Interpretation) (machine : Machine) (frame : Frame)
    (stack : List Continuation) (value : RVal) : Except Error Machine := do
  if frame.hasCredits then
    .error (.mem "function returned with a live reuse credit")
  else if !value.hasWorld machine.store frame.definition.signature.result then
    .error (.mem "function result ownership-world mismatch")
  else
    match stack with
    | [] => return { machine with control := .halted value }
    | .resume caller :: rest =>
        return { machine with control := .running (caller.pushValue value) rest }
    | .applyMore arguments caller :: rest =>
        beginApply context interpretation machine.store machine.heapFuel value
          arguments caller rest

private def runTerminator (context : Context)
    (interpretation : Interpretation) (machine : Machine) (frame : Frame)
    (stack : List Continuation) (terminator : Terminator) : Except Error Machine := do
  match terminator with
  | .jump edge =>
      let frame ← transferEdge frame edge
      return { machine with control := .running frame stack }
  | .switchValue scrutinee constructors natPeel =>
      match ← resolveAtom frame.values scrutinee with
      | .loc location =>
          let box ← match machine.store.get? location with
            | some box => pure box
            | none => .error (.mem s!"switch on dead location {location}")
          match box.node with
          | .papN .. => .error (.stuck "switch on a PAP")
          | .ctorN cid _ =>
              match constructors.find? fun alternative => alternative.cid == cid with
              | none => .error (.stuck "missing constructor alternative")
              | some alternative =>
                  let frame ← transferEdge frame alternative.edge
                  return { machine with control := .running frame stack }
      | .lit (.nat number) =>
          match natPeel with
          | none => .error (.stuck "Nat switch without literal peeling")
          | some peel =>
              match number with
              | 0 =>
                  let frame ← transferEdge frame peel.zero
                  return { machine with control := .running frame stack }
              | predecessor + 1 =>
                  let frame ← transferEdge frame peel.succ #[.lit (.nat predecessor)]
                  return { machine with control := .running frame stack }
      | .lit (.str _) | .erased => .error (.stuck "switch on a non-Nat scalar")
  | .branchCredit credit someEdge noneEdge =>
      let credit ← creditAt frame credit
      let edge := if credit.isPresent then someEdge else noneEdge
      let frame ← transferEdge frame edge
      return { machine with control := .running frame stack }
  | .ret atom =>
      let value ← resolveAtom frame.values atom
      finishReturn context interpretation machine frame stack value
  | .tailCall address arguments =>
      ensureCallBoundary frame
      let values ← resolveAtoms frame.values arguments
      match context.declarations address with
      | some (.fn definition) =>
          let frame ← enterFunction definition values
          return { machine with control := .running frame stack }
      | some (.extern _) => .error (.stuck "tailCall must not target an extern")
      | none => .error (.unknownRef address)
  | .tailCallSelf arguments =>
      ensureCallBoundary frame
      let values ← resolveAtoms frame.values arguments
      let frame ← enterFunction frame.definition values
      return { machine with control := .running frame stack }

/-- One control transition: exactly one IxIR₂ instruction or terminator. -/
def step (context : Context) (interpretation : Interpretation)
    (machine : Machine) : Except Error Machine := do
  match machine.control with
  | .halted _ => return machine
  | .running frame stack =>
      let block ← currentBlock frame
      if h : frame.pc < block.instructions.size then
        runInstruction context interpretation machine frame stack
          block.instructions[frame.pc]
      else if frame.pc == block.instructions.size then
        runTerminator context interpretation machine frame stack block.terminator
      else
        .error (.stuck "program counter passed the block terminator")

/-- Unfueled small-step relation underlying the total runner. -/
def Step (context : Context) (interpretation : Interpretation)
    (before after : Machine) : Prop :=
  step context interpretation before = .ok after

/-- Public proof interface for one checked CFG-edge transfer. It exposes the
resulting frame without making simulation clients unfold the evaluator's
private dispatcher. -/
def EdgeTransfer (frame : Frame) (edge : Edge)
    (implicitValues : Array RVal) (target : Frame) : Prop :=
  transferEdge frame edge implicitValues = .ok target

/-- Public proof interface for one dynamic-application dispatch.  Both an
`apply` instruction and an `applyMore` return continuation enter the same
private executable worker; exposing its exact successful equation here keeps
their semantic proofs on one control boundary. -/
def ApplyTransfer (context : Context) (interpretation : Interpretation)
    (store : Store) (heapFuel : Nat) (function : RVal)
    (arguments : Array RVal) (resume : Frame)
    (stack : List Continuation) (target : Machine) : Prop :=
  beginApply context interpretation store heapFuel function arguments resume
    stack = .ok target

/-- Public equation for one scalar-only external call. -/
def ScalarOracleCall (context : Context) (address : Address)
    (arguments : Array RVal) (value : RVal) : Prop :=
  callScalarOracle context address arguments = .ok value

theorem ScalarOracleCall.congrOracle {left right : Context}
    {address : Address} {arguments : Array RVal} {value : RVal}
    (oracles : left.oracle = right.oracle)
    (called : ScalarOracleCall left address arguments value) :
    ScalarOracleCall right address arguments value := by
  unfold ScalarOracleCall callScalarOracle at called ⊢
  rw [← oracles]
  exact called

/-- A successful scalar oracle boundary certifies that both its full argument
vector and returned value are scalar. -/
theorem ScalarOracleCall.scalar {context : Context} {address : Address}
    {arguments : Array RVal} {value : RVal}
    (called : ScalarOracleCall context address arguments value) :
    arguments.all RVal.isScalar = true ∧ value.isScalar = true := by
  by_cases argumentsScalar : arguments.all RVal.isScalar = true
  · refine ⟨argumentsScalar, ?_⟩
    cases oracleAt : context.oracle address arguments.toList with
    | none =>
        simp [ScalarOracleCall, callScalarOracle, argumentsScalar,
          oracleAt] at called
    | some result =>
        by_cases resultScalar : result.isScalar = true
        · simp [ScalarOracleCall, callScalarOracle, argumentsScalar,
            oracleAt, resultScalar] at called
          cases called
          exact resultScalar
        · simp [ScalarOracleCall, callScalarOracle, argumentsScalar,
            oracleAt, resultScalar] at called
  · simp [ScalarOracleCall, callScalarOracle, argumentsScalar] at called

/-- Public equation for the shared-value retain loop used while opening a
PAP.  The implementation remains centralized in the evaluator while
simulation clients can relate it to IxIR₁'s `dupVals`. -/
def RetainSharedMany (store : Store) (values : Array RVal)
    (target : Store) : Prop :=
  retainSharedMany store values = .ok target

/-- Public equation for looking up a live credit without consuming it.  This
is the semantic premise used by `branchCredit`. -/
def CreditLookup (frame : Frame) (id : CreditId) (credit : Credit) : Prop :=
  creditAt frame id = .ok credit

/-- Public equation for consuming one linear credit from a frame.  Allocation
and discard rules use the returned frame directly, keeping the private slot
update centralized in the evaluator. -/
def CreditTake (frame : Frame) (id : CreditId) (target : Frame)
    (credit : Credit) : Prop :=
  takeCredit frame id = .ok (target, credit)

/-- Public equation for transferring a vector of linear credits across a CFG
edge. -/
def CreditTakeMany (frame : Frame) (ids : Array CreditId) (target : Frame)
    (credits : Array Credit) : Prop :=
  takeCredits frame ids = .ok (target, credits)

/-- A structural view of batch credit consumption.  It exposes the sequence
of successful single-credit takes without exposing the evaluator's private
fold implementation. -/
inductive CreditTakeSequence :
    Frame → List CreditId → Frame → List Credit → Prop where
  | nil (frame : Frame) : CreditTakeSequence frame [] frame []
  | cons {frame middle target : Frame} {id : CreditId}
      {ids : List CreditId} {credit : Credit} {credits : List Credit}
      (head : CreditTake frame id middle credit)
      (tail : CreditTakeSequence middle ids target credits) :
      CreditTakeSequence frame (id :: ids) target (credit :: credits)

private theorem takeCredit_changeDefinition (frame : Frame) (id : CreditId)
    (definition : Function) :
    takeCredit { frame with definition } id =
      (takeCredit frame id).map (fun output =>
        ({ output.1 with definition }, output.2)) := by
  unfold takeCredit creditAt
  cases found : frame.credits[id]? with
  | none =>
      simp [bind, Except.bind, Except.map]
  | some slot =>
      cases slot with
      | none =>
          simp [bind, Except.bind, Except.map]
      | some credit =>
          simp [bind, Except.bind, pure, Except.pure, Except.map]

theorem CreditLookup.congrDefinition {frame : Frame} {id : CreditId}
    {credit : Credit} (definition : Function)
    (lookedUp : CreditLookup frame id credit) :
    CreditLookup { frame with definition } id credit := by
  unfold CreditLookup creditAt at lookedUp ⊢
  simpa using lookedUp

theorem CreditTake.congrDefinition {frame target : Frame} {id : CreditId}
    {credit : Credit} (definition : Function)
    (taken : CreditTake frame id target credit) :
    CreditTake { frame with definition } id
      { target with definition } credit := by
  unfold CreditTake at taken ⊢
  rw [takeCredit_changeDefinition, taken]
  rfl

/-- Successful single-credit consumption exposes the exact frame update and
the live slot that was removed. -/
theorem CreditTake.target_eq {frame target : Frame} {id : CreditId}
    {credit : Credit} (taken : CreditTake frame id target credit) :
    target = { frame with
      credits := frame.credits.setIfInBounds id none } ∧
      frame.credits[id]? = some (some credit) := by
  unfold CreditTake takeCredit creditAt at taken
  cases found : frame.credits[id]? with
  | none =>
      simp [found, bind, Except.bind] at taken
  | some slot =>
      cases slot with
      | none =>
          simp [found, bind, Except.bind] at taken
      | some foundCredit =>
          simp [found, bind, Except.bind, pure, Except.pure] at taken
          obtain ⟨rfl, rfl⟩ := taken
          exact ⟨rfl, rfl⟩

private theorem takeCredits_changeDefinition (frame : Frame)
    (ids : Array CreditId) (definition : Function) :
    takeCredits { frame with definition } ids =
      (takeCredits frame ids).map (fun output =>
        ({ output.1 with definition }, output.2)) := by
  unfold takeCredits
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  let transform : Frame × Array Credit → Frame × Array Credit :=
    fun state => ({ state.1 with definition }, state.2)
  let takeStep : Frame × Array Credit → CreditId →
      Except Error (Frame × Array Credit) :=
    fun state id => do
      let (next, credit) ← takeCredit state.1 id
      return (next, state.2.push credit)
  have one : ∀ (state : Frame × Array Credit) (id : CreditId),
      takeStep (transform state) id =
        (takeStep state id).map transform := by
    intro state id
    simp only [takeStep, transform]
    rw [takeCredit_changeDefinition]
    cases taken : takeCredit state.1 id with
    | error error =>
        simp [bind, Except.bind, Except.map]
    | ok output =>
        obtain ⟨next, credit⟩ := output
        simp [bind, Except.bind, pure, Except.pure, Except.map]
  have loop : ∀ (remaining : List CreditId)
      (state : Frame × Array Credit),
      List.foldlM takeStep (transform state) remaining =
        (List.foldlM takeStep state remaining).map transform := by
    intro remaining
    induction remaining with
    | nil => intro state; rfl
    | cons id tail ih =>
        intro state
        simp only [List.foldlM_cons]
        cases taken : takeStep state id with
        | error error =>
            have transformed := one state id
            rw [taken] at transformed
            simp only [Except.map] at transformed
            rw [transformed]
            simp [bind, Except.bind, Except.map]
        | ok next =>
            have transformed := one state id
            rw [taken] at transformed
            simp only [Except.map] at transformed
            rw [transformed]
            simpa [bind, Except.bind, Except.map] using ih next
  exact loop ids.toList (frame, #[])

/-- Consuming credits changes only the credit file of a frame. -/
theorem CreditTakeMany.definition {frame target : Frame}
    {ids : Array CreditId} {credits : Array Credit}
    (taken : CreditTakeMany frame ids target credits) :
    target.definition = frame.definition := by
  unfold CreditTakeMany at taken
  have preserved :=
    takeCredits_changeDefinition frame ids frame.definition
  have inputEq : { frame with definition := frame.definition } = frame := by
    cases frame
    rfl
  rw [inputEq, taken] at preserved
  simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at preserved
  have definitions := congrArg Frame.definition preserved.1
  simpa using definitions

/-- Successful batch consumption decomposes into the corresponding sequence
of successful single-credit takes. -/
theorem CreditTakeMany.sequence {frame target : Frame}
    {ids : Array CreditId} {credits : Array Credit}
    (taken : CreditTakeMany frame ids target credits) :
    CreditTakeSequence frame ids.toList target credits.toList := by
  let takeStep : Frame × Array Credit → CreditId →
      Except Error (Frame × Array Credit) :=
    fun state id => do
      let (next, credit) ← takeCredit state.1 id
      return (next, state.2.push credit)
  have loop : ∀ (remaining : List CreditId) (current : Frame)
      (initial : Array Credit) {final : Frame} {output : Array Credit},
      List.foldlM takeStep (current, initial) remaining =
        .ok (final, output) →
      ∃ suffix : List Credit,
        CreditTakeSequence current remaining final suffix ∧
          output.toList = initial.toList ++ suffix := by
    intro remaining
    induction remaining with
    | nil =>
        intro current initial final output run
        simp only [List.foldlM_nil] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨[], .nil current, by simp⟩
    | cons id rest ih =>
        intro current initial final output run
        rw [List.foldlM_cons] at run
        cases headRun : takeCredit current id with
        | error error =>
            simp [takeStep, headRun, bind, Except.bind] at run
        | ok result =>
            obtain ⟨middle, credit⟩ := result
            simp only [takeStep, headRun, bind, Except.bind, pure,
              Except.pure] at run
            obtain ⟨suffix, tail, outputEq⟩ :=
              ih middle (initial.push credit) run
            refine ⟨credit :: suffix, .cons ?_ tail, ?_⟩
            · exact headRun
            · simp [outputEq, List.append_assoc]
  unfold CreditTakeMany takeCredits at taken
  rw [← Array.foldlM_toList] at taken
  change List.foldlM takeStep (frame, #[]) ids.toList =
    .ok (target, credits) at taken
  obtain ⟨suffix, sequence, outputEq⟩ := loop ids.toList frame #[] taken
  have suffixEq : credits.toList = suffix := by simpa using outputEq
  subst suffix
  exact sequence

/-- A sequence of successful single-credit takes reconstructs the evaluator's
batch operation. -/
theorem CreditTakeSequence.toMany {frame target : Frame}
    {ids : List CreditId} {credits : List Credit}
    (sequence : CreditTakeSequence frame ids target credits) :
    CreditTakeMany frame ids.toArray target credits.toArray := by
  let takeStep : Frame × Array Credit → CreditId →
      Except Error (Frame × Array Credit) :=
    fun state id => do
      let (next, credit) ← takeCredit state.1 id
      return (next, state.2.push credit)
  have loop : ∀ {current final : Frame} {remaining : List CreditId}
      {output : List Credit},
      CreditTakeSequence current remaining final output →
      ∀ initial : Array Credit,
        List.foldlM takeStep (current, initial) remaining =
          .ok (final, initial ++ output.toArray) := by
    intro current final remaining output sequence
    induction sequence with
    | nil current =>
        intro initial
        rfl
    | @cons current middle final id remaining credit output head tail ih =>
        intro initial
        rw [List.foldlM_cons]
        unfold CreditTake at head
        have headStep : takeStep (current, initial) id =
            .ok (middle, initial.push credit) := by
          dsimp only [takeStep]
          rw [head]
          rfl
        rw [headStep]
        simp only [bind, Except.bind]
        rw [ih (initial.push credit)]
        congr 2
        apply Array.toList_inj.mp
        simp
  unfold CreditTakeMany takeCredits
  rw [← Array.foldlM_toList]
  change List.foldlM takeStep (frame, #[]) ids =
    .ok (target, credits.toArray)
  simpa using loop sequence #[]

/-- No unconsumed credit remains in this frame. -/
def NoLiveCredits (frame : Frame) : Prop :=
  frame.credits.any Option.isSome = false

/-- Public equation for the ownership- and identity-checked constructor view
used by destructive operations. -/
def ConstructorView (store : Store) (location : Nat) (world : Owned)
    (cid : CtorId) (box : NodeBox) (fields : Array RVal) : Prop :=
  requireCtor store location world cid = .ok (box, fields)

/-- Constructor inspection is extensional in the selected heap lookup. -/
theorem ConstructorView.congrStore {left right : Store} {location : Nat}
    {world : Owned} {cid : CtorId} {box : NodeBox}
    {fields : Array RVal}
    (same : left.get? location = right.get? location)
    (viewed : ConstructorView left location world cid box fields) :
    ConstructorView right location world cid box fields := by
  unfold ConstructorView requireCtor at viewed ⊢
  rw [← same]
  exact viewed

/-- A successful checked constructor view exposes the exact live box,
ownership world, and constructor payload that justified it. -/
theorem ConstructorView.parts {store : Store} {location : Nat}
    {world : Owned} {cid : CtorId} {box : NodeBox}
    {fields : Array RVal}
    (viewed : ConstructorView store location world cid box fields) :
    store.get? location = some box ∧
      box.world = world ∧ box.node = .ctorN cid fields := by
  unfold ConstructorView requireCtor at viewed
  cases boxAt : store.get? location with
  | none =>
      simp [boxAt, bind, Except.bind] at viewed
  | some foundBox =>
      simp only [boxAt, bind, Except.bind, pure, Except.pure] at viewed
      by_cases worldEq : foundBox.world = world
      · simp [worldEq] at viewed
        cases node : foundBox.node with
        | papN address arity arguments => simp [node] at viewed
        | ctorN actual actualFields =>
            simp only [node] at viewed
            by_cases cidEq : actual = cid
            · subst actual
              simp at viewed
              obtain ⟨rfl, rfl⟩ := viewed
              exact ⟨rfl, worldEq, node⟩
            · simp [cidEq] at viewed
      · simp [worldEq] at viewed

theorem CreditLookup.of_getElem {frame : Frame} {id : CreditId}
    {credit : Credit}
    (found : frame.credits[id]? = some (some credit)) :
    CreditLookup frame id credit := by
  unfold CreditLookup creditAt
  rw [found]

theorem CreditTake.of_lookup {frame : Frame} {id : CreditId}
    {credit : Credit} (found : CreditLookup frame id credit) :
    CreditTake frame id
      { frame with credits := frame.credits.setIfInBounds id none }
      credit := by
  unfold CreditTake takeCredit
  unfold CreditLookup at found
  rw [found]
  rfl

theorem CreditTakeMany.single {frame target : Frame} {id : CreditId}
    {credit : Credit} (taken : CreditTake frame id target credit) :
    CreditTakeMany frame #[id] target #[credit] := by
  unfold CreditTakeMany takeCredits
  unfold CreditTake at taken
  simp [taken]
  rfl

theorem ConstructorView.of_box {store : Store} {location : Nat}
    {world : Owned} {cid : CtorId} {box : NodeBox}
    {fields : Array RVal}
    (boxAt : store.get? location = some box)
    (boxWorld : box.world = world)
    (node : box.node = .ctorN cid fields) :
    ConstructorView store location world cid box fields := by
  unfold ConstructorView requireCtor
  rw [boxAt]
  simp [boxWorld, node]
  rfl

theorem RetainSharedMany.empty (store : Store) :
    RetainSharedMany store #[] store := by
  rfl

theorem RetainSharedMany.cons {store middle target : Store}
    {value : RVal} {values : List RVal}
    (head : retainShared store value = .ok middle)
    (tail : RetainSharedMany middle values.toArray target) :
    RetainSharedMany store (value :: values).toArray target := by
  unfold RetainSharedMany retainSharedMany at tail ⊢
  rw [← Array.foldlM_toList] at tail ⊢
  change List.foldlM retainShared middle values = .ok target at tail
  change (do
    let next ← retainShared store value
    List.foldlM retainShared next values) = .ok target
  rw [head]
  exact tail

/-- Invert a successful nonempty batch retain into its first retain and the
remaining batch.  This is the elimination counterpart of
`RetainSharedMany.cons`; clients can reason inductively without unfolding the
private executable fold. -/
theorem RetainSharedMany.cons_inv {store target : Store}
    {value : RVal} {values : List RVal}
    (run : RetainSharedMany store (value :: values).toArray target) :
    ∃ middle,
      retainShared store value = .ok middle ∧
      RetainSharedMany middle values.toArray target := by
  unfold RetainSharedMany retainSharedMany at run
  rw [← Array.foldlM_toList] at run
  change (do
    let middle ← retainShared store value
    List.foldlM retainShared middle values) = .ok target at run
  cases head : retainShared store value with
  | error error =>
      rw [head] at run
      contradiction
  | ok middle =>
      refine ⟨middle, rfl, ?_⟩
      unfold RetainSharedMany retainSharedMany
      rw [← Array.foldlM_toList]
      simpa only [head, bind, Except.bind] using run

/-- Applying an erased function releases the supplied shared arguments and
resumes the caller immediately with the erased value. -/
theorem ApplyTransfer.erased {context : Context}
    {interpretation : Interpretation} {store outStore : Store}
    {heapFuel outHeapFuel : Nat} {arguments : Array RVal}
    {resume : Frame} {stack : List Continuation}
    (released : releaseSharedWork heapFuel store arguments.toList =
      .ok (outStore, outHeapFuel)) :
    ApplyTransfer context interpretation store heapFuel .erased arguments
      resume stack
      { store := outStore
        heapFuel := outHeapFuel
        control := .running
          { resume with values := resume.values.push .erased } stack } := by
  unfold ApplyTransfer beginApply resumeImmediate Frame.pushValue
  rw [released]
  rfl

/-- Opening an under-saturated PAP retains its captured arguments, consumes
the old PAP owner, allocates the longer PAP, and resumes the caller in the
same control step. -/
theorem ApplyTransfer.papUnder {context : Context}
    {interpretation : Interpretation} {store retainedStore releasedStore : Store}
    {heapFuel outHeapFuel : Nat} {location : Nat} {box : NodeBox}
    {address : Address} {arity : Nat} {captured arguments : Array RVal}
    {resume : Frame} {stack : List Continuation}
    (boxAt : store.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (retained : RetainSharedMany store captured retainedStore)
    (released : releaseSharedWork heapFuel retainedStore [.loc location] =
      .ok (releasedStore, outHeapFuel))
    (totalUnder : (captured ++ arguments).size < arity) :
    let allocation := releasedStore.allocNode .shared
      (.papN address arity (captured ++ arguments))
    ApplyTransfer context interpretation store heapFuel (.loc location)
      arguments resume stack
      { store := allocation.1
        heapFuel := outHeapFuel
        control := .running
          { resume with values := resume.values.push (.loc allocation.2) }
          stack } := by
  dsimp only
  unfold RetainSharedMany at retained
  unfold ApplyTransfer beginApply
  simp only
  rw [boxAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [shared]
  rw [if_neg (by decide)]
  rw [node]
  simp only
  rw [if_neg (by omega)]
  rw [retained]
  simp only
  rw [released]
  simp only
  rw [if_pos totalUnder]
  rfl

/-- Opening a saturated or over-saturated PAP enters its checked function
target.  Remaining arguments are represented by the evaluator's explicit
`applyMore` continuation; exact saturation uses an ordinary resume. -/
theorem ApplyTransfer.papFn {context : Context}
    {interpretation : Interpretation} {store retainedStore releasedStore : Store}
    {heapFuel outHeapFuel : Nat} {location : Nat} {box : NodeBox}
    {address : Address} {arity : Nat} {captured arguments : Array RVal}
    {definition : Function} {resume : Frame} {stack : List Continuation}
    (boxAt : store.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (retained : RetainSharedMany store captured retainedStore)
    (released : releaseSharedWork heapFuel retainedStore [.loc location] =
      .ok (releasedStore, outHeapFuel))
    (totalEnough : arity ≤ (captured ++ arguments).size)
    (declaration : context.declarations address = some (.fn definition))
    (papSafe : definition.signature.papSafe = true)
    (suppliedArity :
      ((captured ++ arguments).extract 0 arity).size =
        definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    let total := captured ++ arguments
    let supplied := total.extract 0 arity
    let remaining := total.extract arity total.size
    let callee : Frame := { definition, values := supplied }
    let continuation : Continuation :=
      if remaining.isEmpty then .resume resume
      else .applyMore remaining resume
    ApplyTransfer context interpretation store heapFuel (.loc location)
      arguments resume stack
      { store := releasedStore
        heapFuel := outHeapFuel
        control := .running callee (continuation :: stack) } := by
  dsimp only
  unfold RetainSharedMany at retained
  unfold ApplyTransfer beginApply
  simp only
  rw [boxAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [shared]
  rw [if_neg (by decide)]
  rw [node]
  simp only
  rw [if_neg (by omega)]
  rw [retained]
  simp only
  rw [released]
  simp only
  rw [if_neg (Nat.not_lt.mpr totalEnough)]
  rw [declaration]
  simp only
  simp only [declarationPapSafe, papSafe, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  have arityGuard : ¬
      ((((captured ++ arguments).extract 0 arity).size !=
        definition.signature.params.size) = true) := by
    intro unequal
    exact (bne_iff_ne.mp unequal) suppliedArity
  have blockGuard : ¬ (definition.blocks.isEmpty = true) := by
    simp [nonempty]
  unfold enterFunction
  rw [if_neg arityGuard, if_neg blockGuard]

/-- A PAP may also target a scalar extern declaration.  Successful extern
application is necessarily exactly saturated because a scalar result cannot
be fed through `applyMore`; it resumes the suspended frame immediately. -/
theorem ApplyTransfer.papExtern {context : Context}
    {interpretation : Interpretation} {store retainedStore releasedStore : Store}
    {heapFuel outHeapFuel : Nat} {location : Nat} {box : NodeBox}
    {address : Address} {arity expectedArity : Nat}
    {captured arguments : Array RVal} {value : RVal}
    {resume : Frame} {stack : List Continuation}
    (boxAt : store.get? location = some box)
    (shared : box.world = .shared)
    (node : box.node = .papN address arity captured)
    (capturedUnder : captured.size < arity)
    (retained : RetainSharedMany store captured retainedStore)
    (released : releaseSharedWork heapFuel retainedStore [.loc location] =
      .ok (releasedStore, outHeapFuel))
    (totalEnough : arity ≤ (captured ++ arguments).size)
    (declaration : context.declarations address =
      some (.extern expectedArity))
    (suppliedArity :
      ((captured ++ arguments).extract 0 arity).size = expectedArity)
    (remainingEmpty :
      ((captured ++ arguments).extract arity
        (captured ++ arguments).size).isEmpty = true)
    (called : ScalarOracleCall context address
      ((captured ++ arguments).extract 0 arity) value) :
    ApplyTransfer context interpretation store heapFuel (.loc location)
      arguments resume stack
      { store := releasedStore
        heapFuel := outHeapFuel
        control := .running
          { resume with values := resume.values.push value } stack } := by
  unfold RetainSharedMany at retained
  unfold ApplyTransfer beginApply resumeImmediate Frame.pushValue
  simp only
  rw [boxAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [shared]
  rw [if_neg (by decide)]
  rw [node]
  simp only
  rw [if_neg (by omega)]
  rw [retained]
  simp only
  rw [released]
  simp only
  rw [if_neg (Nat.not_lt.mpr totalEnough)]
  rw [declaration]
  simp only [declarationPapSafe, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  have arityGuard : ¬
      ((((captured ++ arguments).extract 0 arity).size != expectedArity) =
        true) := by
    intro unequal
    exact (bne_iff_ne.mp unequal) suppliedArity
  rw [if_neg arityGuard]
  rw [remainingEmpty]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold ScalarOracleCall at called
  rw [called]

/-- Exhaustive successful shapes of the dynamic-application worker.  This
indexed relation records the runtime evidence hidden by `beginApply` while
fixing its exact output machine, so clients can eliminate an arbitrary
`ApplyTransfer` without unfolding the private dispatcher. -/
inductive ApplyTransferCase (context : Context)
    (interpretation : Interpretation) (store : Store) (heapFuel : Nat)
    (arguments : Array RVal) (resume : Frame) (stack : List Continuation) :
    RVal → Machine → Prop where
  | erased {outStore : Store} {outHeapFuel : Nat}
      (released : releaseSharedWork heapFuel store arguments.toList =
        .ok (outStore, outHeapFuel)) :
      ApplyTransferCase context interpretation store heapFuel arguments
        resume stack .erased
        { store := outStore
          heapFuel := outHeapFuel
          control := .running
            { resume with values := resume.values.push .erased } stack }
  | papUnder {location : Nat} {box : NodeBox} {address : Address}
      {arity : Nat} {captured : Array RVal}
      {retainedStore releasedStore : Store} {outHeapFuel : Nat}
      (boxAt : store.get? location = some box)
      (shared : box.world = .shared)
      (node : box.node = .papN address arity captured)
      (capturedUnder : captured.size < arity)
      (retained : RetainSharedMany store captured retainedStore)
      (released : releaseSharedWork heapFuel retainedStore [.loc location] =
        .ok (releasedStore, outHeapFuel))
      (totalUnder : (captured ++ arguments).size < arity) :
      ApplyTransferCase context interpretation store heapFuel arguments
        resume stack (.loc location)
        (let allocation := releasedStore.allocNode .shared
          (.papN address arity (captured ++ arguments))
        { store := allocation.1
          heapFuel := outHeapFuel
          control := .running
            { resume with
              values := resume.values.push (.loc allocation.2) } stack })
  | papFn {location : Nat} {box : NodeBox} {address : Address}
      {arity : Nat} {captured : Array RVal}
      {retainedStore releasedStore : Store} {outHeapFuel : Nat}
      {definition : Function}
      (boxAt : store.get? location = some box)
      (shared : box.world = .shared)
      (node : box.node = .papN address arity captured)
      (capturedUnder : captured.size < arity)
      (retained : RetainSharedMany store captured retainedStore)
      (released : releaseSharedWork heapFuel retainedStore [.loc location] =
        .ok (releasedStore, outHeapFuel))
      (totalEnough : arity ≤ (captured ++ arguments).size)
      (declaration : context.declarations address = some (.fn definition))
      (papSafe : definition.signature.papSafe = true)
      (suppliedArity :
        ((captured ++ arguments).extract 0 arity).size =
          definition.signature.params.size)
      (nonempty : definition.blocks.isEmpty = false) :
      ApplyTransferCase context interpretation store heapFuel arguments
        resume stack (.loc location)
        (let total := captured ++ arguments
        let supplied := total.extract 0 arity
        let remaining := total.extract arity total.size
        let callee : Frame := { definition, values := supplied }
        let continuation : Continuation :=
          if remaining.isEmpty then .resume resume
          else .applyMore remaining resume
        { store := releasedStore
          heapFuel := outHeapFuel
          control := .running callee (continuation :: stack) })
  | papExtern {location : Nat} {box : NodeBox} {address : Address}
      {arity expectedArity : Nat} {captured : Array RVal}
      {retainedStore releasedStore : Store} {outHeapFuel : Nat}
      {value : RVal}
      (boxAt : store.get? location = some box)
      (shared : box.world = .shared)
      (node : box.node = .papN address arity captured)
      (capturedUnder : captured.size < arity)
      (retained : RetainSharedMany store captured retainedStore)
      (released : releaseSharedWork heapFuel retainedStore [.loc location] =
        .ok (releasedStore, outHeapFuel))
      (totalEnough : arity ≤ (captured ++ arguments).size)
      (declaration : context.declarations address =
        some (.extern expectedArity))
      (suppliedArity :
        ((captured ++ arguments).extract 0 arity).size = expectedArity)
      (remainingEmpty :
        ((captured ++ arguments).extract arity
          (captured ++ arguments).size).isEmpty = true)
      (called : ScalarOracleCall context address
        ((captured ++ arguments).extract 0 arity) value) :
      ApplyTransferCase context interpretation store heapFuel arguments
        resume stack (.loc location)
        { store := releasedStore
          heapFuel := outHeapFuel
          control := .running
            { resume with values := resume.values.push value } stack }

/-- Every explicit successful application shape reconstructs the public
transfer equation. -/
theorem ApplyTransferCase.transfer {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {function : RVal} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {target : Machine}
    (classified : ApplyTransferCase context interpretation store heapFuel
      arguments resume stack function target) :
    ApplyTransfer context interpretation store heapFuel function arguments
      resume stack target := by
  cases classified with
  | erased released => exact ApplyTransfer.erased released
  | papUnder boxAt shared node capturedUnder retained released totalUnder =>
      exact ApplyTransfer.papUnder boxAt shared node capturedUnder retained
        released totalUnder
  | papFn boxAt shared node capturedUnder retained released totalEnough
      declaration papSafe suppliedArity nonempty =>
      exact ApplyTransfer.papFn boxAt shared node capturedUnder retained
        released totalEnough declaration papSafe suppliedArity nonempty
  | papExtern boxAt shared node capturedUnder retained released totalEnough
      declaration suppliedArity remainingEmpty called =>
      exact ApplyTransfer.papExtern boxAt shared node capturedUnder retained
        released totalEnough declaration suppliedArity remainingEmpty called

/-- Invert an arbitrary successful dynamic dispatch into exactly one of the
four public runtime shapes. -/
theorem ApplyTransfer.classify {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {function : RVal} {arguments : Array RVal} {resume : Frame}
    {stack : List Continuation} {target : Machine}
    (transferred : ApplyTransfer context interpretation store heapFuel
      function arguments resume stack target) :
    ApplyTransferCase context interpretation store heapFuel arguments
      resume stack function target := by
  unfold ApplyTransfer beginApply at transferred
  simp only [bind, Except.bind, pure, Except.pure] at transferred
  cases function with
  | lit literal =>
      simp at transferred
  | erased =>
      cases released : releaseSharedWork heapFuel store arguments.toList with
      | error error =>
          simp [released] at transferred
      | ok output =>
          obtain ⟨outStore, outHeapFuel⟩ := output
          simp [released, resumeImmediate, Frame.pushValue] at transferred
          subst target
          exact .erased released
  | loc location =>
      cases boxAt : store.get? location with
      | none =>
          simp [boxAt] at transferred
      | some box =>
          cases box with
          | mk world rc node =>
              cases world with
              | unique =>
                  simp [boxAt] at transferred
              | shared =>
                  cases node with
                  | ctorN cid fields =>
                      simp [boxAt] at transferred
                  | papN address arity captured =>
                      have sharedEq :
                          (Owned.shared != Owned.shared) = false := by decide
                      simp only [boxAt, sharedEq, Bool.false_eq_true, if_false]
                        at transferred
                      by_cases capturedUnder : captured.size < arity
                      · have capturedNotEnough : ¬arity ≤ captured.size :=
                          Nat.not_le_of_gt capturedUnder
                        simp only [capturedNotEnough, ↓reduceIte]
                          at transferred
                        cases retainedRun : retainSharedMany store captured with
                        | error error =>
                            simp only [retainedRun] at transferred
                            cases transferred
                        | ok retainedStore =>
                            simp only [retainedRun] at transferred
                            cases releasedRun : releaseSharedWork heapFuel
                                retainedStore [.loc location] with
                            | error error =>
                                simp only [releasedRun] at transferred
                                cases transferred
                            | ok output =>
                                simp only [releasedRun] at transferred
                                obtain ⟨releasedStore, outHeapFuel⟩ := output
                                by_cases totalUnder :
                                    (captured ++ arguments).size < arity
                                · simp only [if_pos totalUnder] at transferred
                                  injection transferred with targetEq
                                  subst target
                                  exact .papUnder boxAt rfl rfl capturedUnder
                                    retainedRun releasedRun totalUnder
                                · have totalEnough :
                                      arity ≤ (captured ++ arguments).size :=
                                    Nat.le_of_not_gt totalUnder
                                  simp only [if_neg totalUnder] at transferred
                                  cases declarationAt :
                                      context.declarations address with
                                  | none =>
                                      simp only [declarationAt] at transferred
                                      cases transferred
                                  | some declaration =>
                                      simp only [declarationAt] at transferred
                                      cases declaration with
                                      | fn definition =>
                                          cases papSafe :
                                              definition.signature.papSafe with
                                          | false =>
                                              simp only [declarationPapSafe,
                                                papSafe, Bool.not_false,
                                                if_true]
                                                at transferred
                                              cases transferred
                                          | true =>
                                              simp only [declarationPapSafe,
                                                papSafe, Bool.not_true,
                                                Bool.false_eq_true, if_false]
                                                at transferred
                                              by_cases suppliedArity :
                                                  ((captured ++ arguments).extract
                                                    0 arity).size =
                                                  definition.signature.params.size
                                              · have arityMatch :
                                                    (((captured ++ arguments).extract
                                                      0 arity).size !=
                                                      definition.signature.params.size) =
                                                    false := by
                                                  exact Bool.eq_false_iff.mpr
                                                    (fun mismatch =>
                                                      (bne_iff_ne.mp mismatch)
                                                        suppliedArity)
                                                cases blockEmpty :
                                                    definition.blocks.isEmpty with
                                                | true =>
                                                    simp only [enterFunction,
                                                      arityMatch,
                                                      Bool.false_eq_true,
                                                      if_false, blockEmpty,
                                                      if_true]
                                                      at transferred
                                                    cases transferred
                                                | false =>
                                                    simp only [enterFunction,
                                                      arityMatch,
                                                      Bool.false_eq_true,
                                                      if_false, blockEmpty]
                                                      at transferred
                                                    injection transferred with
                                                      targetEq
                                                    subst target
                                                    exact .papFn boxAt rfl rfl
                                                      capturedUnder retainedRun
                                                      releasedRun totalEnough
                                                      declarationAt papSafe
                                                      suppliedArity blockEmpty
                                              · have arityMismatch :
                                                    (((captured ++ arguments).extract
                                                      0 arity).size !=
                                                      definition.signature.params.size) =
                                                    true := by
                                                  exact bne_iff_ne.mpr
                                                    suppliedArity
                                                simp only [enterFunction,
                                                  arityMismatch, if_true]
                                                  at transferred
                                                cases transferred
                                      | extern expectedArity =>
                                          simp only [declarationPapSafe,
                                            Bool.not_true,
                                            Bool.false_eq_true, ↓reduceIte]
                                            at transferred
                                          by_cases suppliedArity :
                                              ((captured ++ arguments).extract
                                                0 arity).size = expectedArity
                                          · have arityMatch :
                                                (((captured ++ arguments).extract
                                                  0 arity).size !=
                                                  expectedArity) = false := by
                                              exact Bool.eq_false_iff.mpr
                                                (fun mismatch =>
                                                  (bne_iff_ne.mp mismatch)
                                                    suppliedArity)
                                            simp only [arityMatch,
                                              Bool.false_eq_true, if_false]
                                              at transferred
                                            cases remainingEmpty :
                                                ((captured ++ arguments).extract
                                                  arity
                                                  (captured ++ arguments).size).isEmpty
                                              with
                                            | false =>
                                                simp only [remainingEmpty,
                                                  Bool.not_false, if_true]
                                                  at transferred
                                                cases transferred
                                            | true =>
                                                simp only [remainingEmpty,
                                                  Bool.not_true,
                                                  Bool.false_eq_true, if_false]
                                                  at transferred
                                                cases called : callScalarOracle
                                                    context address
                                                    ((captured ++ arguments).extract
                                                      0 arity) with
                                                | error error =>
                                                    simp only [called]
                                                      at transferred
                                                    cases transferred
                                                | ok value =>
                                                    simp only [called]
                                                      at transferred
                                                    injection transferred with
                                                      targetEq
                                                    subst target
                                                    exact .papExtern boxAt rfl rfl
                                                      capturedUnder retainedRun
                                                      releasedRun totalEnough
                                                      declarationAt suppliedArity
                                                      remainingEmpty called
                                          · have arityMismatch :
                                                (((captured ++ arguments).extract
                                                  0 arity).size !=
                                                  expectedArity) = true := by
                                              exact bne_iff_ne.mpr
                                                suppliedArity
                                            simp only [arityMismatch, if_true]
                                              at transferred
                                            cases transferred
                      · have capturedEnough : arity ≤ captured.size :=
                          Nat.le_of_not_gt capturedUnder
                        simp only [capturedEnough, ↓reduceIte] at transferred
                        cases transferred

/-- General checked edge transfer from public value-resolution and linear
credit premises.  This is the proof seam used by optional-credit branches. -/
theorem EdgeTransfer.of_parts {frame after : Frame} {edge : Edge}
    {implicitValues values : Array RVal} {credits : Array Credit}
    {block : Block}
    (resolved : resolveAtoms frame.values edge.values = .ok values)
    (taken : CreditTakeMany frame edge.credits after credits)
    (cleared : NoLiveCredits after)
    (blockAt : after.definition.blocks[edge.target]? = some block)
    (valueArity : (implicitValues ++ values).size = block.valueParams.size)
    (creditArity : credits.size = block.creditParams.size) :
    EdgeTransfer frame edge implicitValues
      { after with
        block := edge.target
        pc := 0
        values := implicitValues ++ values
        credits := credits.map some } := by
  unfold EdgeTransfer transferEdge
  rw [resolved]
  simp only [bind, Except.bind]
  unfold CreditTakeMany at taken
  rw [taken]
  simp only
  have noLive : after.hasCredits = false := by
    unfold Frame.hasCredits
    exact cleared
  rw [noLive]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [blockAt]
  simp [pure, Except.pure, valueArity, creditArity]

/-- Invert a successful edge transfer into its value resolution, linear
credit consumption, target lookup, ABI checks, and exact successor frame. -/
theorem EdgeTransfer.parts {frame target : Frame} {edge : Edge}
    {implicitValues : Array RVal}
    (transferred : EdgeTransfer frame edge implicitValues target) :
    ∃ values credits after block,
      resolveAtoms frame.values edge.values = .ok values ∧
        CreditTakeMany frame edge.credits after credits ∧
        NoLiveCredits after ∧
        after.definition.blocks[edge.target]? = some block ∧
        (implicitValues ++ values).size = block.valueParams.size ∧
        credits.size = block.creditParams.size ∧
        target = { after with
          block := edge.target
          pc := 0
          values := implicitValues ++ values
          credits := credits.map some } := by
  unfold EdgeTransfer transferEdge at transferred
  cases resolved : resolveAtoms frame.values edge.values with
  | error error =>
      rw [resolved] at transferred
      contradiction
  | ok values =>
      rw [resolved] at transferred
      simp only [bind, Except.bind] at transferred
      cases taken : takeCredits frame edge.credits with
      | error error =>
          rw [taken] at transferred
          contradiction
      | ok output =>
          obtain ⟨after, credits⟩ := output
          rw [taken] at transferred
          simp only at transferred
          cases live : after.hasCredits with
          | true =>
              rw [live] at transferred
              simp at transferred
          | false =>
              rw [live] at transferred
              simp only [Bool.false_eq_true, ↓reduceIte] at transferred
              cases blockAt : after.definition.blocks[edge.target]? with
              | none =>
                  rw [blockAt] at transferred
                  contradiction
              | some block =>
                  rw [blockAt] at transferred
                  simp only [pure, Except.pure] at transferred
                  cases valueMismatch :
                      ((implicitValues ++ values).size !=
                        block.valueParams.size) with
                  | true =>
                      rw [valueMismatch] at transferred
                      simp at transferred
                  | false =>
                      rw [valueMismatch] at transferred
                      simp only [Bool.false_eq_true, ↓reduceIte] at transferred
                      cases creditMismatch :
                          (credits.size != block.creditParams.size) with
                      | true =>
                          rw [creditMismatch] at transferred
                          simp at transferred
                      | false =>
                          rw [creditMismatch] at transferred
                          simp only [Bool.false_eq_true, ↓reduceIte] at transferred
                          have valueArity : (implicitValues ++ values).size =
                              block.valueParams.size := by
                            simpa using valueMismatch
                          have creditArity : credits.size =
                              block.creditParams.size := by
                            simpa using creditMismatch
                          have targetEq := Except.ok.inj transferred
                          refine ⟨values, credits, after, block, rfl, ?_, ?_,
                            ?_, valueArity, creditArity, targetEq.symm⟩
                          · exact taken
                          · unfold NoLiveCredits
                            exact live
                          · exact blockAt

/-- Baseline lowering carries no credits. Resolving its explicit edge values,
finding the target block, and matching the two target arities therefore
determines the exact successor frame. -/
theorem EdgeTransfer.baseline {frame : Frame} {edge : Edge}
    {implicitValues values : Array RVal} {block : Block}
    (resolved : resolveAtoms frame.values edge.values = .ok values)
    (frameCredits : frame.credits = #[])
    (edgeCredits : edge.credits = #[])
    (blockAt : frame.definition.blocks[edge.target]? = some block)
    (valueArity : (implicitValues ++ values).size = block.valueParams.size)
    (blockCredits : block.creditParams = #[]) :
    EdgeTransfer frame edge implicitValues
      { frame with
        block := edge.target
        pc := 0
        values := implicitValues ++ values
        credits := #[] } := by
  have noLive : frame.hasCredits = false := by
    simp [Frame.hasCredits, frameCredits]
  have taken : takeCredits frame edge.credits = .ok (frame, #[]) := by
    rw [edgeCredits]
    rfl
  unfold EdgeTransfer transferEdge
  rw [resolved]
  simp only [bind, Except.bind]
  rw [taken]
  simp only
  rw [noLive]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [blockAt]
  simp [pure, Except.pure, valueArity, blockCredits]

/-- A successful edge transfer is insensitive to replacing the enclosing
function definition when the selected target block keeps the same incoming
value and credit ABI.  The resulting frame changes only its definition. -/
theorem EdgeTransfer.congrDefinition {frame target : Frame} {edge : Edge}
    {implicitValues : Array RVal} {definition : Function}
    {sourceBlock rewrittenBlock : Block}
    (sourceAt : frame.definition.blocks[edge.target]? = some sourceBlock)
    (rewrittenAt : definition.blocks[edge.target]? = some rewrittenBlock)
    (valueParams : rewrittenBlock.valueParams = sourceBlock.valueParams)
    (creditParams : rewrittenBlock.creditParams = sourceBlock.creditParams)
    (transferred : EdgeTransfer frame edge implicitValues target) :
    EdgeTransfer { frame with definition } edge implicitValues
      { target with definition } := by
  unfold EdgeTransfer transferEdge at transferred ⊢
  cases resolved : resolveAtoms frame.values edge.values with
  | error error =>
      rw [resolved] at transferred
      contradiction
  | ok values =>
      rw [resolved] at transferred
      simp only [bind, Except.bind] at transferred ⊢
      cases taken : takeCredits frame edge.credits with
      | error error =>
          rw [taken] at transferred
          contradiction
      | ok output =>
          obtain ⟨after, credits⟩ := output
          rw [taken] at transferred
          simp only at transferred
          have afterDefinition : after.definition = frame.definition :=
            CreditTakeMany.definition taken
          have rewrittenTaken :=
            takeCredits_changeDefinition frame edge.credits definition
          rw [taken] at rewrittenTaken
          simp only [Except.map] at rewrittenTaken
          rw [rewrittenTaken]
          simp only
          have rewrittenLive :
              ({ after with definition }).hasCredits = after.hasCredits := rfl
          cases live : after.hasCredits with
          | true =>
              rw [live] at transferred
              simp only [↓reduceIte] at transferred
              simp at transferred
          | false =>
              rw [live] at transferred
              simp only [Bool.false_eq_true, ↓reduceIte] at transferred
              rw [rewrittenLive, live]
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [afterDefinition, sourceAt] at transferred
              simp only [pure, Except.pure] at transferred
              rw [rewrittenAt]
              simp only [pure, Except.pure]
              cases valueArity :
                  ((implicitValues ++ values).size !=
                    sourceBlock.valueParams.size) with
              | true =>
                  rw [valueArity] at transferred
                  simp only [↓reduceIte] at transferred
                  simp at transferred
              | false =>
                  rw [valueArity] at transferred
                  simp only [Bool.false_eq_true, ↓reduceIte] at transferred
                  rw [valueParams, valueArity]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  cases creditArity :
                      (credits.size != sourceBlock.creditParams.size) with
                  | true =>
                      rw [creditArity] at transferred
                      simp only [↓reduceIte] at transferred
                      simp at transferred
                  | false =>
                      rw [creditArity] at transferred
                      simp only [Bool.false_eq_true, ↓reduceIte] at transferred
                      rw [creditParams, creditArity]
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      cases transferred
                      rfl

/-- Every successful transfer selected a concrete block at its edge target. -/
theorem EdgeTransfer.targetBlock {frame target : Frame} {edge : Edge}
    {implicitValues : Array RVal}
    (transferred : EdgeTransfer frame edge implicitValues target) :
    ∃ block, frame.definition.blocks[edge.target]? = some block := by
  unfold EdgeTransfer transferEdge at transferred
  cases resolved : resolveAtoms frame.values edge.values with
  | error error =>
      rw [resolved] at transferred
      contradiction
  | ok values =>
      rw [resolved] at transferred
      simp only [bind, Except.bind] at transferred
      cases taken : takeCredits frame edge.credits with
      | error error =>
          rw [taken] at transferred
          contradiction
      | ok output =>
          obtain ⟨after, credits⟩ := output
          rw [taken] at transferred
          simp only at transferred
          have afterDefinition : after.definition = frame.definition :=
            CreditTakeMany.definition taken
          cases live : after.hasCredits with
          | true =>
              rw [live] at transferred
              simp at transferred
          | false =>
              rw [live] at transferred
              simp only [Bool.false_eq_true, ↓reduceIte] at transferred
              cases found : after.definition.blocks[edge.target]? with
              | none =>
                  rw [found] at transferred
                  contradiction
              | some block =>
                  exact ⟨block, by simpa [afterDefinition] using found⟩

/-- An edge transfer retains its enclosing function definition. -/
theorem EdgeTransfer.definition {frame target : Frame} {edge : Edge}
    {implicitValues : Array RVal}
    (transferred : EdgeTransfer frame edge implicitValues target) :
    target.definition = frame.definition := by
  obtain ⟨block, blockAt⟩ := transferred.targetBlock
  have changed := transferred.congrDefinition
    (definition := frame.definition) blockAt blockAt rfl rfl
  have inputEq : { frame with definition := frame.definition } = frame := by
    cases frame
    rfl
  rw [inputEq] at changed
  unfold EdgeTransfer at transferred changed
  have targetEq : target = { target with definition := frame.definition } :=
    Except.ok.inj (transferred.symm.trans changed)
  have definitions := congrArg Frame.definition targetEq
  simpa using definitions

/-- Reduction rule for the present arm of an optional-credit branch.  The
credit is transferred by the selected edge, rather than consumed by the
terminator itself. -/
theorem Step.branchCreditPresent {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame target : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit} {someEdge noneEdge : Edge}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .branchCredit creditId someEdge noneEdge)
    (lookedUp : CreditLookup frame creditId credit)
    (present : credit.isPresent = true)
    (transferred : EdgeTransfer frame someEdge #[] target) :
    Step context interpretation machine
      { machine with control := .running target stack } := by
  unfold Step step currentBlock runTerminator
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp only
  unfold CreditLookup at lookedUp
  rw [lookedUp]
  simp only
  rw [present]
  unfold EdgeTransfer at transferred
  simp [transferred]

/-- Reduction rule for the absent arm of an optional-credit branch. -/
theorem Step.branchCreditAbsent {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame target : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit} {someEdge noneEdge : Edge}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .branchCredit creditId someEdge noneEdge)
    (lookedUp : CreditLookup frame creditId credit)
    (absent : credit.isPresent = false)
    (transferred : EdgeTransfer frame noneEdge #[] target) :
    Step context interpretation machine
      { machine with control := .running target stack } := by
  unfold Step step currentBlock runTerminator
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp only
  unfold CreditLookup at lookedUp
  rw [lookedUp]
  simp only
  rw [absent]
  unfold EdgeTransfer at transferred
  simp [transferred]

/-- Reduction rule for an ordinary block jump. -/
theorem Step.jump {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame target : Frame}
    {stack : List Continuation} {block : Block} {edge : Edge}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .jump edge)
    (transferred : EdgeTransfer frame edge #[] target) :
    Step context interpretation machine
      { machine with control := .running target stack } := by
  unfold Step step currentBlock runTerminator
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  unfold EdgeTransfer at transferred
  simp [transferred]

/-- Reduction rule for constructor dispatch through an exact alternative. -/
theorem Step.switchCtor {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame target : Frame} {stack : List Continuation} {block : Block}
    {scrutinee : Atom} {constructors : Array CtorAlt}
    {natPeel : Option NatPeel} {location : Nat} {box : NodeBox}
    {cid : CtorId} {fields : Array RVal} {alternative : CtorAlt}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors natPeel)
    (resolved : resolveAtom frame.values scrutinee = .ok (.loc location))
    (boxAt : machine.store.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (alternativeAt : constructors.find? (fun candidate =>
      candidate.cid == cid) = some alternative)
    (transferred : EdgeTransfer frame alternative.edge #[] target) :
    Step context interpretation machine
      { machine with control := .running target stack } := by
  unfold Step step currentBlock runTerminator
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp only
  rw [resolved]
  simp only
  rw [boxAt]
  simp only
  rw [node]
  simp only
  rw [alternativeAt]
  unfold EdgeTransfer at transferred
  simp [transferred]

/-- Reduction rule for the zero branch of a literal-Nat switch. -/
theorem Step.switchNatZero {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame target : Frame} {stack : List Continuation} {block : Block}
    {scrutinee : Atom} {constructors : Array CtorAlt} {peel : NatPeel}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors (some peel))
    (resolved : resolveAtom frame.values scrutinee = .ok (.lit (.nat 0)))
    (transferred : EdgeTransfer frame peel.zero #[] target) :
    Step context interpretation machine
      { machine with control := .running target stack } := by
  unfold Step step currentBlock runTerminator
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp only
  rw [resolved]
  unfold EdgeTransfer at transferred
  simp [transferred]

/-- Reduction rule for the successor branch of a literal-Nat switch. The
predecessor is the branch's one implicit leading value. -/
theorem Step.switchNatSucc {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame target : Frame} {stack : List Continuation} {block : Block}
    {scrutinee : Atom} {constructors : Array CtorAlt} {peel : NatPeel}
    {predecessor : Nat}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator =
      .switchValue scrutinee constructors (some peel))
    (resolved : resolveAtom frame.values scrutinee =
      .ok (.lit (.nat (predecessor + 1))))
    (transferred : EdgeTransfer frame peel.succ
      #[.lit (.nat predecessor)] target) :
    Step context interpretation machine
      { machine with control := .running target stack } := by
  unfold Step step currentBlock runTerminator
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp only
  rw [resolved]
  unfold EdgeTransfer at transferred
  simp [transferred]

/-- Reduction rule for returning a value to an ordinary suspended caller. -/
theorem Step.retResume {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame caller : Frame}
    {rest : List Continuation} {block : Block}
    {atom : Atom} {value : RVal}
    (control : machine.control =
      .running frame (.resume caller :: rest))
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (noCredits : frame.credits = #[])
    (world : value.hasWorld machine.store
      frame.definition.signature.result = true) :
    Step context interpretation machine
      { machine with
        control := .running
          { caller with values := caller.values.push value } rest } := by
  unfold Step step currentBlock runTerminator finishReturn
    Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp [resolved, Frame.hasCredits, noCredits, world]

/-- Reduction rule for a direct tail call to a compiler function. -/
theorem Step.tailCallFn {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {address : Address} {arguments : Array Atom} {values : Array RVal}
    {definition : Function}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCall address arguments)
    (noCredits : frame.credits = #[])
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (declaration : context.declarations address = some (.fn definition))
    (arity : values.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition, values } stack } := by
  unfold Step step currentBlock runTerminator ensureCallBoundary
    Frame.hasCredits enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp [noCredits, resolved, declaration, arity, nonempty]

/-- Reduction rule for a tail-recursive self call. -/
theorem Step.tailCallSelf {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {arguments : Array Atom} {values : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCallSelf arguments)
    (noCredits : frame.credits = #[])
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (arity : values.size = frame.definition.signature.params.size)
    (nonempty : frame.definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition := frame.definition, values }
          stack } := by
  unfold Step step currentBlock runTerminator ensureCallBoundary
    Frame.hasCredits enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp [noCredits, resolved, arity, nonempty]

/-- Tail-recursive self call after all credit slots have been consumed.  In
contrast to the baseline-specialized `tailCallSelf` rule above, this rule
accepts a nonempty credit file containing only `none`; `allocWith` produces
exactly that state after consuming a rewrite credit. -/
theorem Step.tailCallSelfCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {arguments : Array Atom} {values : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCallSelf arguments)
    (noCredits : NoLiveCredits frame)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (arity : values.size = frame.definition.signature.params.size)
    (nonempty : frame.definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition := frame.definition, values }
          stack } := by
  unfold Step step currentBlock runTerminator ensureCallBoundary
    Frame.hasCredits enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  unfold NoLiveCredits at noCredits
  simp [noCredits, resolved, arity, nonempty]

/-- Reduction rule for returning from the outermost frame. -/
theorem Step.retHalt {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {block : Block}
    {atom : Atom} {value : RVal}
    (control : machine.control = .running frame [])
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (noCredits : frame.credits = #[])
    (world : value.hasWorld machine.store
      frame.definition.signature.result = true) :
    Step context interpretation machine
      { machine with control := .halted value } := by
  unfold Step step currentBlock runTerminator finishReturn
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp [resolved, Frame.hasCredits, noCredits, world]

/-- Reduction rule for the public small-step relation at a `move`
instruction.  Simulation proofs can use this rule without depending on the
evaluator's private instruction dispatcher. -/
theorem Step.move {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {stack : List Continuation}
    {block : Block} {atom : Atom} {value : RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .move atom)
    (resolved : resolveAtom frame.values atom = .ok value) :
    Step context interpretation machine
      { machine with
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value }
          stack } := by
  unfold Step step currentBlock runInstruction Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  rw [resolved]

/-- Reduction rule for a checked ordinary allocation. -/
theorem Step.alloc {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {stack : List Continuation}
    {block : Block} {world : Owned} {cid : CtorId}
    {arguments : Array Atom} {schema : CtorSchema}
    {values : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .alloc world cid arguments)
    (schemaAt : context.schemas world cid = some schema)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (fields : FieldWorlds machine.store schema values) :
    let allocation := machine.store.allocNode world (.ctorN cid values)
    Step context interpretation machine
      { machine with
        store := allocation.1
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push (.loc allocation.2) }
          stack } := by
  unfold Step step currentBlock runInstruction Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold FieldWorlds at fields
  rw [fields]

/-- An absent credit is consumed and allocation falls back to a fresh slot in
either interpretation. -/
theorem Step.allocWithAbsent {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame next : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit} {world : Owned} {cid : CtorId}
    {arguments : Array Atom} {schema : CtorSchema} {values : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : context.schemas world cid = some schema)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (fields : FieldWorlds machine.store schema values)
    (taken : CreditTake { frame with pc := frame.pc + 1 }
      creditId next credit)
    (layout : credit.layout = schema.layout)
    (absent : credit.presence = .absent) :
    let allocation := machine.store.allocNode world (.ctorN cid values)
    Step context interpretation machine
      { machine with
        store := allocation.1
        control := .running
          { next with values := next.values.push (.loc allocation.2) }
          stack } := by
  dsimp only
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold FieldWorlds at fields
  rw [fields]
  simp only
  unfold CreditTake at taken
  rw [taken]
  simp [layout, absent, Frame.pushValue]

/-- A present logical credit records the reset opportunity but still allocates
a fresh semantic node. -/
theorem Step.allocWithLogical {context : Context} {machine : Machine}
    {frame next : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit} {world : Owned} {cid : CtorId}
    {arguments : Array Atom} {schema : CtorSchema} {values : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : context.schemas world cid = some schema)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (fields : FieldWorlds machine.store schema values)
    (taken : CreditTake { frame with pc := frame.pc + 1 }
      creditId next credit)
    (layout : credit.layout = schema.layout)
    (present : credit.presence = .present none) :
    let allocation := machine.store.allocNode world (.ctorN cid values)
    Step context .logical machine
      { machine with
        store := allocation.1
        control := .running
          { next with values := next.values.push (.loc allocation.2) }
          stack } := by
  dsimp only
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold FieldWorlds at fields
  rw [fields]
  simp only
  unfold CreditTake at taken
  rw [taken]
  simp [layout, present, Frame.pushValue]

/-- A present physical credit reuses its reserved slot after an exact layout
check. -/
theorem Step.allocWithPhysical {context : Context} {machine : Machine}
    {frame next : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit} {world : Owned} {cid : CtorId}
    {arguments : Array Atom} {schema : CtorSchema} {values : Array RVal}
    {location : Nat} {store : Store}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .allocWith creditId world cid arguments)
    (schemaAt : context.schemas world cid = some schema)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (fields : FieldWorlds machine.store schema values)
    (taken : CreditTake { frame with pc := frame.pc + 1 }
      creditId next credit)
    (layout : credit.layout = schema.layout)
    (present : credit.presence = .present (some location))
    (reused : machine.store.reuseReservation location world
      (.ctorN cid values) schema.fields.size = .ok store) :
    Step context .physical machine
      { machine with
        store
        control := .running
          { next with values := next.values.push (.loc location) }
          stack } := by
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold FieldWorlds at fields
  rw [fields]
  simp only
  unfold CreditTake at taken
  rw [taken]
  simp only
  rw [layout]
  have sameLayout : (schema.layout != schema.layout) = false := by
    simp
  rw [sameLayout]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [present]
  simp only
  rw [reused]
  rfl

/-- Discarding an absent credit changes neither the heap nor the advanced
frame beyond consuming the credit slot. -/
theorem Step.discardCreditAbsent {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame next : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .discardCredit creditId)
    (taken : CreditTake { frame with pc := frame.pc + 1 }
      creditId next credit)
    (absent : credit.presence = .absent) :
    Step context interpretation machine
      { machine with control := .running next stack } := by
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold CreditTake at taken
  rw [taken]
  simp [absent]

/-- Discarding a present logical credit needs no physical heap action. -/
theorem Step.discardCreditLogical {context : Context} {machine : Machine}
    {frame next : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .discardCredit creditId)
    (taken : CreditTake { frame with pc := frame.pc + 1 }
      creditId next credit)
    (present : credit.presence = .present none) :
    Step context .logical machine
      { machine with control := .running next stack } := by
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold CreditTake at taken
  rw [taken]
  simp [present]

/-- Discarding a present physical credit releases its reserved slot. -/
theorem Step.discardCreditPhysical {context : Context} {machine : Machine}
    {frame next : Frame} {stack : List Continuation} {block : Block}
    {creditId : CreditId} {credit : Credit} {location : Nat} {store : Store}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .discardCredit creditId)
    (taken : CreditTake { frame with pc := frame.pc + 1 }
      creditId next credit)
    (present : credit.presence = .present (some location))
    (released : machine.store.releaseReservation location = .ok store) :
    Step context .physical machine
      { machine with store, control := .running next stack } := by
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold CreditTake at taken
  rw [taken]
  simp only
  rw [present]
  simp only
  rw [released]

/-- Logical unique extraction kills the constructor and yields its fields plus
a reservation-free required credit. -/
theorem Step.takeUniqueLogical {context : Context} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {target : Atom} {cid : CtorId} {schema : CtorSchema} {location : Nat}
    {box : NodeBox} {fields : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .takeUnique target cid)
    (schemaAt : context.schemas .unique cid = some schema)
    (resolved : resolveAtom frame.values target = .ok (.loc location))
    (viewed : ConstructorView machine.store location .unique cid box fields)
    (unitRC : box.rc = 1) :
    Step context .logical machine
      { machine with
        store := machine.store.kill location
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values ++ fields
            credits := frame.credits.push (some
              { layout := schema.layout, presence := .present none }) }
          stack } := by
  unfold Step step currentBlock runInstruction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold ConstructorView at viewed
  rw [viewed]
  simp [unitRC, Credit.presentFor, Frame.advance, Frame.pushValues,
    Frame.pushCredit]

/-- Physical unique extraction reserves the constructor slot and records its
location in the required credit. -/
theorem Step.takeUniquePhysical {context : Context} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {target : Atom} {cid : CtorId} {schema : CtorSchema} {location : Nat}
    {box : NodeBox} {fields : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .takeUnique target cid)
    (schemaAt : context.schemas .unique cid = some schema)
    (resolved : resolveAtom frame.values target = .ok (.loc location))
    (viewed : ConstructorView machine.store location .unique cid box fields)
    (unitRC : box.rc = 1) :
    Step context .physical machine
      { machine with
        store := machine.store.reserve location
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values ++ fields
            credits := frame.credits.push (some
              { layout := schema.layout,
                presence := .present (some location) }) }
          stack } := by
  unfold Step step currentBlock runInstruction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold ConstructorView at viewed
  rw [viewed]
  simp [unitRC, Credit.presentFor, Frame.advance, Frame.pushValues,
    Frame.pushCredit]

/-- A unit-refcount logical shared reset takes the hot path, kills the source
node, and exposes a reservation-free present credit. -/
theorem Step.resetSharedLogicalHot {context : Context} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {target : Atom} {cid : CtorId} {schema : CtorSchema} {location : Nat}
    {box : NodeBox} {fields : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .resetShared target cid)
    (schemaAt : context.schemas .shared cid = some schema)
    (resolved : resolveAtom frame.values target = .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared cid box fields)
    (unitRC : box.rc = 1) :
    Step context .logical machine
      { machine with
        store := ((machine.store.tickResetAttempt).kill location).tickHotReset
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values ++ fields
            credits := frame.credits.push (some
              { layout := schema.layout, presence := .present none }) }
          stack } := by
  unfold Step step currentBlock runInstruction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold ConstructorView at viewed
  rw [viewed]
  simp [unitRC, Credit.presentFor, Frame.advance, Frame.pushValues,
    Frame.pushCredit]

/-- A unit-refcount physical shared reset reserves the source slot and exposes
its location in a present credit. -/
theorem Step.resetSharedPhysicalHot {context : Context} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {target : Atom} {cid : CtorId} {schema : CtorSchema} {location : Nat}
    {box : NodeBox} {fields : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .resetShared target cid)
    (schemaAt : context.schemas .shared cid = some schema)
    (resolved : resolveAtom frame.values target = .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared cid box fields)
    (unitRC : box.rc = 1) :
    Step context .physical machine
      { machine with
        store :=
          ((machine.store.tickResetAttempt).reserve location).tickHotReset
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values ++ fields
            credits := frame.credits.push (some
              { layout := schema.layout,
                presence := .present (some location) }) }
          stack } := by
  unfold Step step currentBlock runInstruction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold ConstructorView at viewed
  rw [viewed]
  simp [unitRC, Credit.presentFor, Frame.advance, Frame.pushValues,
    Frame.pushCredit]

/-- A multiply referenced shared reset takes the common cold path in either
interpretation: decrement the parent, retain its projected fields, and emit
an absent optional credit. -/
theorem Step.resetSharedCold {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {target : Atom} {cid : CtorId} {schema : CtorSchema} {location : Nat}
    {box : NodeBox} {fields : Array RVal} {store : Store}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .resetShared target cid)
    (schemaAt : context.schemas .shared cid = some schema)
    (resolved : resolveAtom frame.values target = .ok (.loc location))
    (viewed : ConstructorView machine.store location .shared cid box fields)
    (shared : 1 < box.rc)
    (retained : RetainSharedMany
      ((((machine.store.tickResetAttempt).setBox location
        { box with rc := box.rc - 1 }).rcTick).tickColdReset)
      fields store) :
    Step context interpretation machine
      { machine with
        store
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values ++ fields
            credits := frame.credits.push (some
              { layout := schema.layout, presence := .absent }) }
          stack } := by
  unfold Step step currentBlock runInstruction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  unfold lookupSchema
  rw [schemaAt]
  simp only
  rw [resolved]
  simp only
  unfold ConstructorView at viewed
  rw [viewed]
  simp only
  have nonzero : (box.rc == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  have nonunit : (box.rc == 1) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  rw [nonzero, nonunit]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold RetainSharedMany at retained
  rw [retained]
  rfl

/-- Reduction rule for a successful shared retain. -/
theorem Step.retainShared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {atom : Atom} {value : RVal} {store : Store}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .retainShared atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (retained : retainShared machine.store value = .ok store) :
    Step context interpretation machine
      { machine with
        store
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value }
          stack } := by
  unfold Step step currentBlock runInstruction Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  rw [resolved]
  simp only
  rw [retained]

/-- Reduction rule for a successful deep shared release. -/
theorem Step.releaseShared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {atom : Atom} {value : RVal} {store : Store} {heapFuel : Nat}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .releaseShared atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (released : releaseShared machine.heapFuel machine.store value =
      .ok (store, heapFuel)) :
    Step context interpretation machine
      { store, heapFuel,
        control := .running { frame with pc := frame.pc + 1 } stack } := by
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  rw [resolved]
  simp only
  rw [released]

/-- Reduction rule for a successful deep unique drop. -/
theorem Step.dropUnique {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {atom : Atom} {value : RVal} {store : Store} {heapFuel : Nat}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .dropUnique atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (dropped : dropUnique machine.heapFuel machine.store value =
      .ok (store, heapFuel)) :
    Step context interpretation machine
      { store, heapFuel,
        control := .running { frame with pc := frame.pc + 1 } stack } := by
  unfold Step step currentBlock runInstruction Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  rw [resolved]
  simp only
  rw [dropped]

/-- Reduction rule for a checked all-scalar unique constructor free. -/
theorem Step.freeUnique {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {atom : Atom} {cid : CtorId} {location : Nat}
    {box : NodeBox} {fields : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .freeUnique atom cid)
    (resolved : resolveAtom frame.values atom = .ok (.loc location))
    (boxAt : machine.store.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN cid fields)
    (scalarFields : fields.all RVal.isScalar = true) :
    Step context interpretation machine
      { machine with
        store := machine.store.kill location
        control := .running { frame with pc := frame.pc + 1 } stack } := by
  unfold Step step currentBlock runInstruction Frame.advance requireCtor
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  rw [resolved]
  simp only
  rw [boxAt]
  simp [unique, node, scalarFields]

/-- Reduction rule for a successful checked constructor projection. -/
theorem Step.fetch {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {stack : List Continuation}
    {block : Block} {atom : Atom} {cid : CtorId} {field location : Nat}
    {box : NodeBox} {fields : Array RVal} {value : RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .fetch atom cid field)
    (resolved : resolveAtom frame.values atom = .ok (.loc location))
    (boxAt : machine.store.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (fieldAt : fields[field]? = some value) :
    Step context interpretation machine
      { machine with
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value }
          stack } := by
  unfold Step step currentBlock runInstruction Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp only
  rw [resolved]
  simp only
  rw [boxAt]
  simp only
  rw [node]
  simp [fieldAt]

/-- Reduction rule for entering a directly addressed compiler function and
suspending the advanced caller frame. -/
theorem Step.callFn {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame}
    {stack : List Continuation} {block : Block}
    {address : Address} {arguments : Array Atom} {values : Array RVal}
    {definition : Function}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .call address arguments)
    (noCredits : frame.credits = #[])
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (declaration : context.declarations address = some (.fn definition))
    (arity : values.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition, values }
          (.resume { frame with pc := frame.pc + 1 } :: stack) } := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp [noCredits, resolved, declaration, arity, nonempty]

/-- Reduction rule for entering the current function recursively and
suspending the advanced caller frame. -/
theorem Step.callSelf {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame}
    {stack : List Continuation} {block : Block}
    {arguments : Array Atom} {values : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .callSelf arguments)
    (noCredits : frame.credits = #[])
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (arity : values.size = frame.definition.signature.params.size)
    (nonempty : frame.definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition := frame.definition, values }
          (.resume { frame with pc := frame.pc + 1 } :: stack) } := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp [noCredits, resolved, arity, nonempty]

/-- Reduction rule for allocating a strictly under-saturated PAP whose target
is a compiler function.  Baseline lowering carries no credits, so its call
boundary is discharged by the empty credit file. -/
theorem Step.pappFn {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {stack : List Continuation}
    {block : Block} {address : Address} {arguments : Array Atom}
    {values : Array RVal} {definition : Function}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .papp address arguments)
    (noCredits : frame.credits = #[])
    (declaration : context.declarations address = some (.fn definition))
    (papSafe : definition.signature.papSafe = true)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (under : values.size < definition.signature.params.size) :
    let allocation := machine.store.allocNode .shared
      (.papN address definition.signature.params.size values)
    Step context interpretation machine
      { machine with
        store := allocation.1
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push (.loc allocation.2) }
          stack } := by
  dsimp only
  unfold Step step currentBlock runInstruction Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp [ensureCallBoundary, Frame.hasCredits, noCredits, resolved,
    declaration, declarationArity, declarationPapSafe, papSafe,
    Nat.not_le.mpr under]
  rfl

/-- Reduction rule for a scalar external call. -/
theorem Step.extern {context : Context} {interpretation : Interpretation}
    {machine : Machine} {frame : Frame} {stack : List Continuation}
    {block : Block} {address : Address} {arguments : Array Atom}
    {values : Array RVal} {arity : Nat} {value : RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .extern address arguments)
    (noCredits : frame.credits = #[])
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (declaration : context.declarations address = some (.extern arity))
    (argumentArity : values.size = arity)
    (called : ScalarOracleCall context address values value) :
    Step context interpretation machine
      { machine with
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value }
          stack } := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp [noCredits, resolved, declaration, argumentArity]
  unfold ScalarOracleCall at called
  rw [called]

/-- Reduction rule for dynamic application.  Operand resolution and the
advanced caller coordinate are discharged here; the shared `ApplyTransfer`
relation describes whether dispatch resumes immediately, enters a PAP target,
or installs an `applyMore` continuation. -/
theorem Step.apply {context : Context} {interpretation : Interpretation}
    {machine target : Machine} {frame : Frame}
    {stack : List Continuation} {block : Block}
    {functionAtom : Atom} {argumentAtoms : Array Atom}
    {function : RVal} {arguments : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .apply functionAtom argumentAtoms)
    (noCredits : frame.credits = #[])
    (functionResolved : resolveAtom frame.values functionAtom = .ok function)
    (argumentsResolved :
      resolveAtoms frame.values argumentAtoms = .ok arguments)
    (transferred : ApplyTransfer context interpretation machine.store
      machine.heapFuel function arguments { frame with pc := frame.pc + 1 }
      stack target) :
    Step context interpretation machine target := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  simp [noCredits, functionResolved, argumentsResolved]
  simpa [ApplyTransfer, noCredits] using transferred

/-- Returning through an over-application continuation dispatches the
callee's value through the same `ApplyTransfer` relation used by the original
`apply` instruction. -/
theorem Step.retApplyMore {context : Context}
    {interpretation : Interpretation} {machine target : Machine}
    {frame caller : Frame} {arguments : Array RVal}
    {rest : List Continuation} {block : Block}
    {atom : Atom} {value : RVal}
    (control : machine.control =
      .running frame (.applyMore arguments caller :: rest))
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (noCredits : frame.credits = #[])
    (world : value.hasWorld machine.store
      frame.definition.signature.result = true)
    (transferred : ApplyTransfer context interpretation machine.store
      machine.heapFuel value arguments caller rest target) :
    Step context interpretation machine target := by
  unfold Step step currentBlock runTerminator finishReturn
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  simp [resolved, Frame.hasCredits, noCredits, world]
  exact transferred

/-! ## Exhaustive call-boundary rules

The baseline-facing rules above use an empty credit array because lowered
source frames never allocate credit registers.  Generated helper frames and
the raw evaluator can instead reach a call boundary with a nonempty array
whose every slot has been consumed.  The following rules expose that full
successful evaluator domain through `NoLiveCredits`. -/

/-- Return to an ordinary continuation after every credit slot has been
consumed, including a nonempty file of `none` entries. -/
theorem Step.retResumeCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame caller : Frame} {rest : List Continuation} {block : Block}
    {atom : Atom} {value : RVal}
    (control : machine.control =
      .running frame (.resume caller :: rest))
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (noCredits : NoLiveCredits frame)
    (world : value.hasWorld machine.store
      frame.definition.signature.result = true) :
    Step context interpretation machine
      { machine with
        control := .running
          { caller with values := caller.values.push value } rest } := by
  unfold Step step currentBlock runTerminator finishReturn Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  unfold NoLiveCredits at noCredits
  simp [resolved, Frame.hasCredits, noCredits, world]

/-- Return from the outermost frame after every credit slot has been
consumed. -/
theorem Step.retHaltCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {block : Block} {atom : Atom} {value : RVal}
    (control : machine.control = .running frame [])
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (noCredits : NoLiveCredits frame)
    (world : value.hasWorld machine.store
      frame.definition.signature.result = true) :
    Step context interpretation machine
      { machine with control := .halted value } := by
  unfold Step step currentBlock runTerminator finishReturn
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  unfold NoLiveCredits at noCredits
  simp [resolved, Frame.hasCredits, noCredits, world]

/-- Return through an over-application continuation after every credit slot
has been consumed. -/
theorem Step.retApplyMoreCleared {context : Context}
    {interpretation : Interpretation} {machine target : Machine}
    {frame caller : Frame} {arguments : Array RVal}
    {rest : List Continuation} {block : Block}
    {atom : Atom} {value : RVal}
    (control : machine.control =
      .running frame (.applyMore arguments caller :: rest))
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .ret atom)
    (resolved : resolveAtom frame.values atom = .ok value)
    (noCredits : NoLiveCredits frame)
    (world : value.hasWorld machine.store
      frame.definition.signature.result = true)
    (transferred : ApplyTransfer context interpretation machine.store
      machine.heapFuel value arguments caller rest target) :
    Step context interpretation machine target := by
  unfold Step step currentBlock runTerminator finishReturn
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  unfold NoLiveCredits at noCredits
  simp [resolved, Frame.hasCredits, noCredits, world]
  exact transferred

/-- Direct tail-call entry with an arbitrary fully consumed credit file. -/
theorem Step.tailCallFnCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {address : Address} {arguments : Array Atom} {values : Array RVal}
    {definition : Function}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminator : block.terminator = .tailCall address arguments)
    (noCredits : NoLiveCredits frame)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (declaration : context.declarations address = some (.fn definition))
    (arity : values.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition, values } stack } := by
  unfold Step step currentBlock runTerminator ensureCallBoundary
    Frame.hasCredits enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  have pcBeq : (frame.pc == block.instructions.size) = true :=
    beq_iff_eq.mpr pc
  rw [dif_neg (by omega), if_pos pcBeq, terminator]
  unfold NoLiveCredits at noCredits
  simp [noCredits, resolved, declaration, arity, nonempty]

/-- Direct call entry with an arbitrary fully consumed credit file. -/
theorem Step.callFnCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {address : Address} {arguments : Array Atom} {values : Array RVal}
    {definition : Function}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .call address arguments)
    (noCredits : NoLiveCredits frame)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (declaration : context.declarations address = some (.fn definition))
    (arity : values.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition, values }
          (.resume { frame with pc := frame.pc + 1 } :: stack) } := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  unfold NoLiveCredits at noCredits
  simp [noCredits, resolved, declaration, arity, nonempty]

/-- Recursive call entry with an arbitrary fully consumed credit file. -/
theorem Step.callSelfCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {arguments : Array Atom} {values : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .callSelf arguments)
    (noCredits : NoLiveCredits frame)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (arity : values.size = frame.definition.signature.params.size)
    (nonempty : frame.definition.blocks.isEmpty = false) :
    Step context interpretation machine
      { machine with
        control := .running { definition := frame.definition, values }
          (.resume { frame with pc := frame.pc + 1 } :: stack) } := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance enterFunction
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  unfold NoLiveCredits at noCredits
  simp [noCredits, resolved, arity, nonempty]

/-- Function-targeted PAP construction with an arbitrary fully consumed
credit file. -/
theorem Step.pappFnCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {address : Address} {arguments : Array Atom} {values : Array RVal}
    {definition : Function}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .papp address arguments)
    (noCredits : NoLiveCredits frame)
    (declaration : context.declarations address = some (.fn definition))
    (papSafe : definition.signature.papSafe = true)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (under : values.size < definition.signature.params.size) :
    let allocation := machine.store.allocNode .shared
      (.papN address definition.signature.params.size values)
    Step context interpretation machine
      { machine with
        store := allocation.1
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push (.loc allocation.2) }
          stack } := by
  dsimp only
  unfold Step step currentBlock runInstruction Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  unfold NoLiveCredits at noCredits
  simp [ensureCallBoundary, Frame.hasCredits, noCredits, resolved,
    declaration, declarationArity, declarationPapSafe, papSafe,
    Nat.not_le.mpr under]
  rfl

/-- Extern-targeted PAP construction is a genuine successful evaluator
shape when the captured vector is strictly under-saturated. -/
theorem Step.pappExternCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {address : Address} {arguments : Array Atom} {values : Array RVal}
    {arity : Nat}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .papp address arguments)
    (noCredits : NoLiveCredits frame)
    (declaration : context.declarations address = some (.extern arity))
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (under : values.size < arity) :
    let allocation := machine.store.allocNode .shared
      (.papN address arity values)
    Step context interpretation machine
      { machine with
        store := allocation.1
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push (.loc allocation.2) }
          stack } := by
  dsimp only
  unfold Step step currentBlock runInstruction Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  unfold NoLiveCredits at noCredits
  simp [ensureCallBoundary, Frame.hasCredits, noCredits, resolved,
    declaration, declarationArity, declarationPapSafe,
    Nat.not_le.mpr under]
  rfl

/-- Scalar extern invocation with an arbitrary fully consumed credit file. -/
theorem Step.externCleared {context : Context}
    {interpretation : Interpretation} {machine : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {address : Address} {arguments : Array Atom}
    {values : Array RVal} {arity : Nat} {value : RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .extern address arguments)
    (noCredits : NoLiveCredits frame)
    (resolved : resolveAtoms frame.values arguments = .ok values)
    (declaration : context.declarations address = some (.extern arity))
    (argumentArity : values.size = arity)
    (called : ScalarOracleCall context address values value) :
    Step context interpretation machine
      { machine with
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value }
          stack } := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance Frame.pushValue
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  unfold NoLiveCredits at noCredits
  simp [noCredits, resolved, declaration, argumentArity]
  unfold ScalarOracleCall at called
  rw [called]

/-- Dynamic application with an arbitrary fully consumed credit file. -/
theorem Step.applyCleared {context : Context}
    {interpretation : Interpretation} {machine target : Machine}
    {frame : Frame} {stack : List Continuation} {block : Block}
    {functionAtom : Atom} {argumentAtoms : Array Atom}
    {function : RVal} {arguments : Array RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .apply functionAtom argumentAtoms)
    (noCredits : NoLiveCredits frame)
    (functionResolved : resolveAtom frame.values functionAtom = .ok function)
    (argumentsResolved :
      resolveAtoms frame.values argumentAtoms = .ok arguments)
    (transferred : ApplyTransfer context interpretation machine.store
      machine.heapFuel function arguments { frame with pc := frame.pc + 1 }
      stack target) :
    Step context interpretation machine target := by
  unfold Step step currentBlock runInstruction ensureCallBoundary
    Frame.hasCredits Frame.advance
  rw [control]
  simp only
  rw [blockAt]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos pc, instruction]
  unfold NoLiveCredits at noCredits
  simp [noCredits, functionResolved, argumentsResolved]
  simpa [ApplyTransfer, noCredits] using transferred

/-! ## Exhaustive successful-step classification -/

/-- Public equation for the private instruction worker at a canonical running
machine. -/
def InstructionTransfer (context : Context)
    (interpretation : Interpretation) (store : Store) (heapFuel : Nat)
    (frame : Frame) (stack : List Continuation) (instruction : Instr)
    (target : Machine) : Prop :=
  runInstruction context interpretation
    { store, heapFuel, control := .running frame stack }
    frame stack instruction = .ok target

/-- Every successful runtime shape of one IxIR₂ instruction.  The relation is
indexed by the instruction and exact output machine, so eliminating it exposes
all dynamic evidence needed by simulation clients. -/
inductive InstructionTransferCase (context : Context)
    (interpretation : Interpretation) (store : Store) (heapFuel : Nat)
    (frame : Frame) (stack : List Continuation) : Instr → Machine → Prop where
  | move {atom : Atom} {value : RVal}
      (resolved : resolveAtom frame.values atom = .ok value) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.move atom)
        { store, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack }
  | alloc {world : Owned} {cid : CtorId} {arguments : Array Atom}
      {schema : CtorSchema} {values : Array RVal}
      (schemaAt : context.schemas world cid = some schema)
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (fields : FieldWorlds store schema values) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.alloc world cid arguments)
        (let allocation := store.allocNode world (.ctorN cid values)
        { store := allocation.1, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc allocation.2) }
            stack })
  | allocWithAbsent {creditId : CreditId} {credit : Credit}
      {world : Owned} {cid : CtorId} {arguments : Array Atom}
      {schema : CtorSchema} {values : Array RVal} {next : Frame}
      (schemaAt : context.schemas world cid = some schema)
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (fields : FieldWorlds store schema values)
      (taken : CreditTake { frame with pc := frame.pc + 1 }
        creditId next credit)
      (layout : credit.layout = schema.layout)
      (absent : credit.presence = .absent) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.allocWith creditId world cid arguments)
        (let allocation := store.allocNode world (.ctorN cid values)
        { store := allocation.1, heapFuel
          control := .running
            { next with values := next.values.push (.loc allocation.2) }
            stack })
  | allocWithLogical {creditId : CreditId} {credit : Credit}
      {world : Owned} {cid : CtorId} {arguments : Array Atom}
      {schema : CtorSchema} {values : Array RVal} {next : Frame}
      (mode : interpretation = .logical)
      (schemaAt : context.schemas world cid = some schema)
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (fields : FieldWorlds store schema values)
      (taken : CreditTake { frame with pc := frame.pc + 1 }
        creditId next credit)
      (layout : credit.layout = schema.layout)
      (present : credit.presence = .present none) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.allocWith creditId world cid arguments)
        (let allocation := store.allocNode world (.ctorN cid values)
        { store := allocation.1, heapFuel
          control := .running
            { next with values := next.values.push (.loc allocation.2) }
            stack })
  | allocWithPhysical {creditId : CreditId} {credit : Credit}
      {world : Owned} {cid : CtorId} {arguments : Array Atom}
      {schema : CtorSchema} {values : Array RVal} {next : Frame}
      {location : Nat} {outStore : Store}
      (mode : interpretation = .physical)
      (schemaAt : context.schemas world cid = some schema)
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (fields : FieldWorlds store schema values)
      (taken : CreditTake { frame with pc := frame.pc + 1 }
        creditId next credit)
      (layout : credit.layout = schema.layout)
      (present : credit.presence = .present (some location))
      (reused : store.reuseReservation location world (.ctorN cid values)
        schema.fields.size = .ok outStore) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.allocWith creditId world cid arguments)
        { store := outStore, heapFuel
          control := .running
            { next with values := next.values.push (.loc location) } stack }
  | discardAbsent {creditId : CreditId} {credit : Credit} {next : Frame}
      (taken : CreditTake { frame with pc := frame.pc + 1 }
        creditId next credit)
      (absent : credit.presence = .absent) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.discardCredit creditId)
        { store, heapFuel, control := .running next stack }
  | discardLogical {creditId : CreditId} {credit : Credit} {next : Frame}
      (mode : interpretation = .logical)
      (taken : CreditTake { frame with pc := frame.pc + 1 }
        creditId next credit)
      (present : credit.presence = .present none) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.discardCredit creditId)
        { store, heapFuel, control := .running next stack }
  | discardPhysical {creditId : CreditId} {credit : Credit} {next : Frame}
      {location : Nat} {outStore : Store}
      (mode : interpretation = .physical)
      (taken : CreditTake { frame with pc := frame.pc + 1 }
        creditId next credit)
      (present : credit.presence = .present (some location))
      (released : store.releaseReservation location = .ok outStore) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.discardCredit creditId)
        { store := outStore, heapFuel, control := .running next stack }
  | takeUniqueLogical {target : Atom} {cid : CtorId}
      {schema : CtorSchema} {location : Nat} {box : NodeBox}
      {fields : Array RVal}
      (mode : interpretation = .logical)
      (schemaAt : context.schemas .unique cid = some schema)
      (resolved : resolveAtom frame.values target = .ok (.loc location))
      (viewed : ConstructorView store location .unique cid box fields)
      (unitRC : box.rc = 1) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.takeUnique target cid)
        { store := store.kill location, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values ++ fields
              credits := frame.credits.push (some
                { layout := schema.layout, presence := .present none }) }
            stack }
  | takeUniquePhysical {target : Atom} {cid : CtorId}
      {schema : CtorSchema} {location : Nat} {box : NodeBox}
      {fields : Array RVal}
      (mode : interpretation = .physical)
      (schemaAt : context.schemas .unique cid = some schema)
      (resolved : resolveAtom frame.values target = .ok (.loc location))
      (viewed : ConstructorView store location .unique cid box fields)
      (unitRC : box.rc = 1) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.takeUnique target cid)
        { store := store.reserve location, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values ++ fields
              credits := frame.credits.push (some
                { layout := schema.layout,
                  presence := .present (some location) }) }
            stack }
  | resetSharedLogicalHot {target : Atom} {cid : CtorId}
      {schema : CtorSchema} {location : Nat} {box : NodeBox}
      {fields : Array RVal}
      (mode : interpretation = .logical)
      (schemaAt : context.schemas .shared cid = some schema)
      (resolved : resolveAtom frame.values target = .ok (.loc location))
      (viewed : ConstructorView store location .shared cid box fields)
      (unitRC : box.rc = 1) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.resetShared target cid)
        { store := ((store.tickResetAttempt).kill location).tickHotReset
          heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values ++ fields
              credits := frame.credits.push (some
                { layout := schema.layout, presence := .present none }) }
            stack }
  | resetSharedPhysicalHot {target : Atom} {cid : CtorId}
      {schema : CtorSchema} {location : Nat} {box : NodeBox}
      {fields : Array RVal}
      (mode : interpretation = .physical)
      (schemaAt : context.schemas .shared cid = some schema)
      (resolved : resolveAtom frame.values target = .ok (.loc location))
      (viewed : ConstructorView store location .shared cid box fields)
      (unitRC : box.rc = 1) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.resetShared target cid)
        { store := ((store.tickResetAttempt).reserve location).tickHotReset
          heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values ++ fields
              credits := frame.credits.push (some
                { layout := schema.layout,
                  presence := .present (some location) }) }
            stack }
  | resetSharedCold {target : Atom} {cid : CtorId}
      {schema : CtorSchema} {location : Nat} {box : NodeBox}
      {fields : Array RVal} {outStore : Store}
      (schemaAt : context.schemas .shared cid = some schema)
      (resolved : resolveAtom frame.values target = .ok (.loc location))
      (viewed : ConstructorView store location .shared cid box fields)
      (shared : 1 < box.rc)
      (retained : RetainSharedMany
        ((((store.tickResetAttempt).setBox location
          { box with rc := box.rc - 1 }).rcTick).tickColdReset)
        fields outStore) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.resetShared target cid)
        { store := outStore, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values ++ fields
              credits := frame.credits.push (some
                { layout := schema.layout, presence := .absent }) }
            stack }
  | retainShared {target : Atom} {value : RVal} {outStore : Store}
      (resolved : resolveAtom frame.values target = .ok value)
      (retained : Eval.retainShared store value = .ok outStore) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.retainShared target)
        { store := outStore, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack }
  | releaseShared {target : Atom} {value : RVal} {outStore : Store}
      {outHeapFuel : Nat}
      (resolved : resolveAtom frame.values target = .ok value)
      (released : Eval.releaseShared heapFuel store value =
        .ok (outStore, outHeapFuel)) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.releaseShared target)
        { store := outStore, heapFuel := outHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack }
  | dropUnique {target : Atom} {value : RVal} {outStore : Store}
      {outHeapFuel : Nat}
      (resolved : resolveAtom frame.values target = .ok value)
      (dropped : Eval.dropUnique heapFuel store value =
        .ok (outStore, outHeapFuel)) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.dropUnique target)
        { store := outStore, heapFuel := outHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack }
  | freeUnique {target : Atom} {cid : CtorId} {location : Nat}
      {box : NodeBox} {fields : Array RVal}
      (resolved : resolveAtom frame.values target = .ok (.loc location))
      (viewed : ConstructorView store location .unique cid box fields)
      (scalarFields : fields.all RVal.isScalar = true) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.freeUnique target cid)
        { store := store.kill location, heapFuel
          control := .running { frame with pc := frame.pc + 1 } stack }
  | fetch {target : Atom} {cid : CtorId} {field location : Nat}
      {box : NodeBox} {fields : Array RVal} {value : RVal}
      (resolved : resolveAtom frame.values target = .ok (.loc location))
      (boxAt : store.get? location = some box)
      (node : box.node = .ctorN cid fields)
      (fieldAt : fields[field]? = some value) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.fetch target cid field)
        { store, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack }
  | callFn {address : Address} {arguments : Array Atom}
      {values : Array RVal} {definition : Function}
      (noCredits : NoLiveCredits frame)
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (declaration : context.declarations address = some (.fn definition))
      (arity : values.size = definition.signature.params.size)
      (nonempty : definition.blocks.isEmpty = false) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.call address arguments)
        { store, heapFuel
          control := .running { definition, values }
            (.resume { frame with pc := frame.pc + 1 } :: stack) }
  | callSelf {arguments : Array Atom} {values : Array RVal}
      (noCredits : NoLiveCredits frame)
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (arity : values.size = frame.definition.signature.params.size)
      (nonempty : frame.definition.blocks.isEmpty = false) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.callSelf arguments)
        { store, heapFuel
          control := .running { definition := frame.definition, values }
            (.resume { frame with pc := frame.pc + 1 } :: stack) }
  | pappFn {address : Address} {arguments : Array Atom}
      {values : Array RVal} {definition : Function}
      (noCredits : NoLiveCredits frame)
      (declaration : context.declarations address = some (.fn definition))
      (papSafe : definition.signature.papSafe = true)
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (under : values.size < definition.signature.params.size) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.papp address arguments)
        (let allocation := store.allocNode .shared
          (.papN address definition.signature.params.size values)
        { store := allocation.1, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc allocation.2) }
            stack })
  | pappExtern {address : Address} {arguments : Array Atom}
      {values : Array RVal} {arity : Nat}
      (noCredits : NoLiveCredits frame)
      (declaration : context.declarations address = some (.extern arity))
      (resolved : resolveAtoms frame.values arguments = .ok values)
      (under : values.size < arity) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.papp address arguments)
        (let allocation := store.allocNode .shared
          (.papN address arity values)
        { store := allocation.1, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc allocation.2) }
            stack })
  | apply {functionAtom : Atom} {argumentAtoms : Array Atom}
      {function : RVal} {arguments : Array RVal} {target : Machine}
      (noCredits : NoLiveCredits frame)
      (functionResolved : resolveAtom frame.values functionAtom = .ok function)
      (argumentsResolved :
        resolveAtoms frame.values argumentAtoms = .ok arguments)
      (transferred : ApplyTransfer context interpretation store heapFuel
        function arguments { frame with pc := frame.pc + 1 } stack target) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.apply functionAtom argumentAtoms) target
  | extern {address : Address} {argumentAtoms : Array Atom}
      {arguments : Array RVal} {arity : Nat} {value : RVal}
      (noCredits : NoLiveCredits frame)
      (resolved : resolveAtoms frame.values argumentAtoms = .ok arguments)
      (declaration : context.declarations address = some (.extern arity))
      (argumentArity : arguments.size = arity)
      (called : ScalarOracleCall context address arguments value) :
      InstructionTransferCase context interpretation store heapFuel frame stack
        (.extern address argumentAtoms)
        { store, heapFuel
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack }

/-- Each classified instruction shape reconstructs the public small step once
the enclosing block lookup and program-counter facts are supplied. -/
theorem InstructionTransferCase.step {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation}
    {instruction : Instr} {target : Machine}
    (classified : InstructionTransferCase context interpretation store
      heapFuel frame stack instruction target)
    {block : Block}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instructionAt : block.instructions[frame.pc] = instruction) :
    Step context interpretation
      { store, heapFuel, control := .running frame stack } target := by
  cases classified with
  | move resolved =>
      exact Step.move rfl blockAt pc instructionAt resolved
  | alloc schemaAt resolved fields =>
      exact Step.alloc rfl blockAt pc instructionAt schemaAt resolved fields
  | allocWithAbsent schemaAt resolved fields taken layout absent =>
      exact Step.allocWithAbsent rfl blockAt pc instructionAt schemaAt
        resolved fields taken layout absent
  | allocWithLogical mode schemaAt resolved fields taken layout present =>
      cases mode
      exact Step.allocWithLogical rfl blockAt pc instructionAt schemaAt
        resolved fields taken layout present
  | allocWithPhysical mode schemaAt resolved fields taken layout present reused =>
      cases mode
      exact Step.allocWithPhysical rfl blockAt pc instructionAt schemaAt
        resolved fields taken layout present reused
  | discardAbsent taken absent =>
      exact Step.discardCreditAbsent rfl blockAt pc instructionAt taken absent
  | discardLogical mode taken present =>
      cases mode
      exact Step.discardCreditLogical rfl blockAt pc instructionAt taken present
  | discardPhysical mode taken present released =>
      cases mode
      exact Step.discardCreditPhysical rfl blockAt pc instructionAt taken
        present released
  | takeUniqueLogical mode schemaAt resolved viewed unitRC =>
      cases mode
      exact Step.takeUniqueLogical rfl blockAt pc instructionAt schemaAt
        resolved viewed unitRC
  | takeUniquePhysical mode schemaAt resolved viewed unitRC =>
      cases mode
      exact Step.takeUniquePhysical rfl blockAt pc instructionAt schemaAt
        resolved viewed unitRC
  | resetSharedLogicalHot mode schemaAt resolved viewed unitRC =>
      cases mode
      exact Step.resetSharedLogicalHot rfl blockAt pc instructionAt schemaAt
        resolved viewed unitRC
  | resetSharedPhysicalHot mode schemaAt resolved viewed unitRC =>
      cases mode
      exact Step.resetSharedPhysicalHot rfl blockAt pc instructionAt schemaAt
        resolved viewed unitRC
  | resetSharedCold schemaAt resolved viewed shared retained =>
      exact Step.resetSharedCold rfl blockAt pc instructionAt schemaAt resolved
        viewed shared retained
  | retainShared resolved retained =>
      exact Step.retainShared rfl blockAt pc instructionAt resolved retained
  | releaseShared resolved released =>
      exact Step.releaseShared rfl blockAt pc instructionAt resolved released
  | dropUnique resolved dropped =>
      exact Step.dropUnique rfl blockAt pc instructionAt resolved dropped
  | freeUnique resolved viewed scalarFields =>
      obtain ⟨boxAt, unique, node⟩ := viewed.parts
      exact Step.freeUnique rfl blockAt pc instructionAt resolved boxAt unique
        node scalarFields
  | fetch resolved boxAt node fieldAt =>
      exact Step.fetch rfl blockAt pc instructionAt resolved boxAt node fieldAt
  | callFn noCredits resolved declaration arity nonempty =>
      exact Step.callFnCleared rfl blockAt pc instructionAt noCredits resolved
        declaration arity nonempty
  | callSelf noCredits resolved arity nonempty =>
      exact Step.callSelfCleared rfl blockAt pc instructionAt noCredits resolved
        arity nonempty
  | pappFn noCredits declaration papSafe resolved under =>
      exact Step.pappFnCleared rfl blockAt pc instructionAt noCredits declaration
        papSafe resolved under
  | pappExtern noCredits declaration resolved under =>
      exact Step.pappExternCleared rfl blockAt pc instructionAt noCredits
        declaration resolved under
  | apply noCredits functionResolved argumentsResolved transferred =>
      exact Step.applyCleared rfl blockAt pc instructionAt noCredits
        functionResolved argumentsResolved transferred
  | extern noCredits resolved declaration argumentArity called =>
      exact Step.externCleared rfl blockAt pc instructionAt noCredits resolved
        declaration argumentArity called

/-- Invert an arbitrary successful instruction-worker equation into its exact
runtime case. -/
theorem InstructionTransfer.classify {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation}
    {instruction : Instr} {target : Machine}
    (transferred : InstructionTransfer context interpretation store heapFuel
      frame stack instruction target) :
    InstructionTransferCase context interpretation store heapFuel frame stack
      instruction target := by
  unfold InstructionTransfer runInstruction at transferred
  simp only [bind, Except.bind, pure, Except.pure] at transferred
  cases instruction with
  | move atom =>
      cases resolved : resolveAtom frame.values atom with
      | error error => simp [resolved] at transferred
      | ok value =>
          simp [resolved, Frame.advance, Frame.pushValue] at transferred
          subst target
          exact .move resolved
  | alloc world cid arguments =>
      cases schemaAt : context.schemas world cid with
      | none => simp [lookupSchema, schemaAt] at transferred
      | some schema =>
          simp only [lookupSchema, schemaAt] at transferred
          cases resolved : resolveAtoms frame.values arguments with
          | error error => simp [resolved] at transferred
          | ok values =>
              simp only [resolved] at transferred
              cases fields : checkFieldWorlds store schema values with
              | error error => simp [fields] at transferred
              | ok checkedUnit =>
                  cases checkedUnit
                  simp [fields, Frame.advance, Frame.pushValue] at transferred
                  subst target
                  exact .alloc schemaAt resolved fields
  | allocWith creditId world cid arguments =>
      cases schemaAt : context.schemas world cid with
      | none => simp [lookupSchema, schemaAt] at transferred
      | some schema =>
          simp only [lookupSchema, schemaAt] at transferred
          cases resolved : resolveAtoms frame.values arguments with
          | error error => simp [resolved] at transferred
          | ok values =>
              simp only [resolved] at transferred
              cases fields : checkFieldWorlds store schema values with
              | error error => simp [fields] at transferred
              | ok checkedUnit =>
                  cases checkedUnit
                  simp only [fields] at transferred
                  cases taken : takeCredit frame.advance creditId with
                  | error error => simp [taken] at transferred
                  | ok output =>
                      obtain ⟨next, credit⟩ := output
                      simp only [taken] at transferred
                      have taken' : CreditTake
                          { frame with pc := frame.pc + 1 }
                          creditId next credit := by
                        simpa [CreditTake, Frame.advance] using taken
                      by_cases layout : credit.layout = schema.layout
                      · cases presence : credit.presence with
                        | absent =>
                            simp [layout, presence, Frame.pushValue]
                              at transferred
                            subst target
                            exact .allocWithAbsent schemaAt resolved fields
                              taken' layout presence
                        | present reservation =>
                            cases interpretation with
                            | logical =>
                                cases reservation with
                                | none =>
                                    simp [layout, presence, Frame.pushValue]
                                      at transferred
                                    subst target
                                    exact .allocWithLogical rfl schemaAt
                                      resolved fields taken' layout presence
                                | some location =>
                                    simp [layout, presence] at transferred
                            | physical =>
                                cases reservation with
                                | none =>
                                    simp [layout, presence] at transferred
                                | some location =>
                                    cases reused : store.reuseReservation
                                        location world (.ctorN cid values)
                                        schema.fields.size with
                                    | error error =>
                                        simp [layout, presence, reused]
                                          at transferred
                                    | ok outStore =>
                                        simp [layout, presence, reused,
                                          Frame.pushValue]
                                          at transferred
                                        subst target
                                        exact .allocWithPhysical rfl schemaAt
                                          resolved fields taken' layout
                                          presence reused
                      · simp [layout] at transferred
  | discardCredit creditId =>
      cases taken : takeCredit frame.advance creditId with
      | error error => simp [taken] at transferred
      | ok output =>
          obtain ⟨next, credit⟩ := output
          simp only [taken] at transferred
          have taken' : CreditTake { frame with pc := frame.pc + 1 }
              creditId next credit := by
            simpa [CreditTake, Frame.advance] using taken
          cases presence : credit.presence with
          | absent =>
              simp [presence] at transferred
              subst target
              exact .discardAbsent taken' presence
          | present reservation =>
              cases interpretation with
              | logical =>
                  cases reservation with
                  | none =>
                      simp [presence] at transferred
                      subst target
                      exact .discardLogical rfl taken' presence
                  | some location => simp [presence] at transferred
              | physical =>
                  cases reservation with
                  | none => simp [presence] at transferred
                  | some location =>
                      cases released : store.releaseReservation location with
                      | error error => simp [presence, released] at transferred
                      | ok outStore =>
                          simp [presence, released] at transferred
                          subst target
                          exact .discardPhysical rfl taken' presence released
  | takeUnique targetAtom cid =>
      cases schemaAt : context.schemas .unique cid with
      | none => simp [lookupSchema, schemaAt] at transferred
      | some schema =>
          simp only [lookupSchema, schemaAt] at transferred
          cases resolved : resolveAtom frame.values targetAtom with
          | error error => simp [resolved] at transferred
          | ok value =>
              cases value with
              | lit literal => simp [resolved] at transferred
              | erased => simp [resolved] at transferred
              | loc location =>
                  simp only [resolved] at transferred
                  cases viewed : requireCtor store location .unique cid with
                  | error error => simp [viewed] at transferred
                  | ok output =>
                      obtain ⟨box, fields⟩ := output
                      simp only [viewed] at transferred
                      by_cases unitRC : box.rc = 1
                      · cases interpretation with
                        | logical =>
                            simp [unitRC, Credit.presentFor, Frame.advance,
                              Frame.pushValues, Frame.pushCredit] at transferred
                            subst target
                            exact .takeUniqueLogical rfl schemaAt resolved
                              viewed unitRC
                        | physical =>
                            simp [unitRC, Credit.presentFor, Frame.advance,
                              Frame.pushValues, Frame.pushCredit] at transferred
                            subst target
                            exact .takeUniquePhysical rfl schemaAt resolved
                              viewed unitRC
                      · simp [unitRC] at transferred
  | resetShared targetAtom cid =>
      cases schemaAt : context.schemas .shared cid with
      | none => simp [lookupSchema, schemaAt] at transferred
      | some schema =>
          simp only [lookupSchema, schemaAt] at transferred
          cases resolved : resolveAtom frame.values targetAtom with
          | error error => simp [resolved] at transferred
          | ok value =>
              cases value with
              | lit literal => simp [resolved] at transferred
              | erased => simp [resolved] at transferred
              | loc location =>
                  simp only [resolved] at transferred
                  cases viewed : requireCtor store location .shared cid with
                  | error error => simp [viewed] at transferred
                  | ok output =>
                      obtain ⟨box, fields⟩ := output
                      simp only [viewed] at transferred
                      by_cases zero : box.rc = 0
                      · simp [zero] at transferred
                      · by_cases unitRC : box.rc = 1
                        · cases interpretation with
                          | logical =>
                              simp [unitRC, Credit.presentFor,
                                Frame.advance, Frame.pushValues,
                                Frame.pushCredit] at transferred
                              subst target
                              exact .resetSharedLogicalHot rfl schemaAt
                                resolved viewed unitRC
                          | physical =>
                              simp [unitRC, Credit.presentFor,
                                Frame.advance, Frame.pushValues,
                                Frame.pushCredit] at transferred
                              subst target
                              exact .resetSharedPhysicalHot rfl schemaAt
                                resolved viewed unitRC
                        · have shared : 1 < box.rc := by omega
                          let beforeRetain :=
                            ((((store.tickResetAttempt).setBox location
                              { box with rc := box.rc - 1 }).rcTick).tickColdReset)
                          cases retained : retainSharedMany beforeRetain fields with
                          | error error =>
                              simp [zero, unitRC, beforeRetain, retained]
                                at transferred
                          | ok outStore =>
                              simp [zero, unitRC, beforeRetain, retained,
                                Frame.advance, Frame.pushValues,
                                Frame.pushCredit] at transferred
                              subst target
                              exact .resetSharedCold schemaAt resolved viewed
                                shared retained
  | retainShared targetAtom =>
      cases resolved : resolveAtom frame.values targetAtom with
      | error error => simp [resolved] at transferred
      | ok value =>
          simp only [resolved] at transferred
          cases retained : Eval.retainShared store value with
          | error error => simp [retained] at transferred
          | ok outStore =>
              simp [retained, Frame.advance, Frame.pushValue] at transferred
              subst target
              exact .retainShared resolved retained
  | releaseShared targetAtom =>
      cases resolved : resolveAtom frame.values targetAtom with
      | error error => simp [resolved] at transferred
      | ok value =>
          simp only [resolved] at transferred
          cases released : Eval.releaseShared heapFuel store value with
          | error error => simp [released] at transferred
          | ok output =>
              obtain ⟨outStore, outHeapFuel⟩ := output
              simp [released, Frame.advance] at transferred
              subst target
              exact .releaseShared resolved released
  | dropUnique targetAtom =>
      cases resolved : resolveAtom frame.values targetAtom with
      | error error => simp [resolved] at transferred
      | ok value =>
          simp only [resolved] at transferred
          cases dropped : Eval.dropUnique heapFuel store value with
          | error error => simp [dropped] at transferred
          | ok output =>
              obtain ⟨outStore, outHeapFuel⟩ := output
              simp [dropped, Frame.advance] at transferred
              subst target
              exact .dropUnique resolved dropped
  | freeUnique targetAtom cid =>
      cases resolved : resolveAtom frame.values targetAtom with
      | error error => simp [resolved] at transferred
      | ok value =>
          cases value with
          | lit literal => simp [resolved] at transferred
          | erased => simp [resolved] at transferred
          | loc location =>
              simp only [resolved] at transferred
              cases viewed : requireCtor store location .unique cid with
              | error error => simp [viewed] at transferred
              | ok output =>
                  obtain ⟨box, fields⟩ := output
                  simp only [viewed] at transferred
                  cases scalarFields : fields.all RVal.isScalar with
                  | false => simp [scalarFields] at transferred
                  | true =>
                      simp [scalarFields, Frame.advance] at transferred
                      subst target
                      exact .freeUnique resolved viewed scalarFields
  | fetch targetAtom cid field =>
      cases resolved : resolveAtom frame.values targetAtom with
      | error error => simp [resolved] at transferred
      | ok value =>
          cases value with
          | lit literal => simp [resolved] at transferred
          | erased => simp [resolved] at transferred
          | loc location =>
              simp only [resolved] at transferred
              cases boxAt : store.get? location with
              | none => simp [boxAt] at transferred
              | some box =>
                  simp only [boxAt] at transferred
                  cases node : box.node with
                  | papN address arity captured => simp [node] at transferred
                  | ctorN actual fields =>
                      simp only [node] at transferred
                      by_cases same : actual = cid
                      · subst actual
                        cases fieldAt : fields[field]? with
                        | none => simp [fieldAt] at transferred
                        | some fieldValue =>
                            simp [fieldAt, Frame.advance, Frame.pushValue]
                              at transferred
                            subst target
                            exact .fetch resolved boxAt node fieldAt
                      · simp [same] at transferred
  | call address arguments =>
      cases live : frame.hasCredits with
      | true => simp [ensureCallBoundary, live] at transferred
      | false =>
          have noCredits : NoLiveCredits frame := by
            simpa [NoLiveCredits, Frame.hasCredits] using live
          simp only [ensureCallBoundary, live, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure] at transferred
          cases resolved : resolveAtoms frame.values arguments with
          | error error => simp [resolved] at transferred
          | ok values =>
              simp only [resolved] at transferred
              cases declaration : context.declarations address with
              | none => simp [declaration] at transferred
              | some declared =>
                  simp only [declaration] at transferred
                  cases declared with
                  | extern arity => simp at transferred
                  | fn definition =>
                      by_cases arity :
                          values.size = definition.signature.params.size
                      · cases empty : definition.blocks.isEmpty with
                        | true =>
                            simp [enterFunction, arity, empty] at transferred
                        | false =>
                            simp [enterFunction, arity, empty, Frame.advance]
                              at transferred
                            subst target
                            exact .callFn noCredits resolved declaration arity
                              empty
                      · simp [enterFunction, arity] at transferred
  | callSelf arguments =>
      cases live : frame.hasCredits with
      | true => simp [ensureCallBoundary, live] at transferred
      | false =>
          have noCredits : NoLiveCredits frame := by
            simpa [NoLiveCredits, Frame.hasCredits] using live
          simp only [ensureCallBoundary, live, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure] at transferred
          cases resolved : resolveAtoms frame.values arguments with
          | error error => simp [resolved] at transferred
          | ok values =>
              simp only [resolved] at transferred
              by_cases arity :
                  values.size = frame.definition.signature.params.size
              · cases empty : frame.definition.blocks.isEmpty with
                | true =>
                    simp [enterFunction, arity, empty]
                      at transferred
                | false =>
                    simp [enterFunction, arity, empty, Frame.advance]
                      at transferred
                    subst target
                    exact .callSelf noCredits resolved arity empty
              · simp [enterFunction, arity] at transferred
  | papp address arguments =>
      cases live : frame.hasCredits with
      | true => simp [ensureCallBoundary, live] at transferred
      | false =>
          have noCredits : NoLiveCredits frame := by
            simpa [NoLiveCredits, Frame.hasCredits] using live
          simp only [ensureCallBoundary, live, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure] at transferred
          cases resolved : resolveAtoms frame.values arguments with
          | error error => simp [resolved] at transferred
          | ok values =>
              simp only [resolved] at transferred
              cases declaration : context.declarations address with
              | none => simp [declaration] at transferred
              | some declared =>
                  simp only [declaration] at transferred
                  cases declared with
                  | fn definition =>
                      cases papSafe : definition.signature.papSafe with
                      | false =>
                          simp [declarationPapSafe, papSafe] at transferred
                      | true =>
                          by_cases under :
                              values.size < definition.signature.params.size
                          · have notEnough : ¬
                                definition.signature.params.size ≤
                                  values.size := Nat.not_le_of_gt under
                            simp [declarationArity, declarationPapSafe,
                              papSafe, notEnough, Frame.advance,
                              Frame.pushValue] at transferred
                            subst target
                            exact .pappFn noCredits declaration papSafe
                              resolved under
                          · have enough : definition.signature.params.size ≤
                                values.size := Nat.le_of_not_gt under
                            simp [declarationArity, declarationPapSafe,
                              papSafe, enough] at transferred
                  | extern arity =>
                      by_cases under : values.size < arity
                      · have notEnough : ¬arity ≤ values.size :=
                          Nat.not_le_of_gt under
                        simp [declarationArity, declarationPapSafe,
                          notEnough, Frame.advance, Frame.pushValue]
                          at transferred
                        subst target
                        exact .pappExtern noCredits declaration resolved under
                      · have enough : arity ≤ values.size :=
                          Nat.le_of_not_gt under
                        simp [declarationArity, declarationPapSafe, enough]
                          at transferred
  | apply functionAtom argumentAtoms =>
      cases live : frame.hasCredits with
      | true => simp [ensureCallBoundary, live] at transferred
      | false =>
          have noCredits : NoLiveCredits frame := by
            simpa [NoLiveCredits, Frame.hasCredits] using live
          simp only [ensureCallBoundary, live, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure] at transferred
          cases functionResolved : resolveAtom frame.values functionAtom with
          | error error => simp [functionResolved] at transferred
          | ok function =>
              simp only [functionResolved] at transferred
              cases argumentsResolved :
                  resolveAtoms frame.values argumentAtoms with
              | error error => simp [argumentsResolved] at transferred
              | ok arguments =>
                  simp only [argumentsResolved] at transferred
                  change ApplyTransfer context interpretation store heapFuel
                    function arguments { frame with pc := frame.pc + 1 }
                    stack target at transferred
                  exact .apply noCredits functionResolved argumentsResolved
                    transferred
  | extern address arguments =>
      cases live : frame.hasCredits with
      | true => simp [ensureCallBoundary, live] at transferred
      | false =>
          have noCredits : NoLiveCredits frame := by
            simpa [NoLiveCredits, Frame.hasCredits] using live
          simp only [ensureCallBoundary, live, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure] at transferred
          cases resolved : resolveAtoms frame.values arguments with
          | error error => simp [resolved] at transferred
          | ok values =>
              simp only [resolved] at transferred
              cases declaration : context.declarations address with
              | none => simp [declaration] at transferred
              | some declared =>
                  simp only [declaration] at transferred
                  cases declared with
                  | fn definition => simp at transferred
                  | extern arity =>
                      by_cases argumentArity : values.size = arity
                      · cases called : callScalarOracle context address values with
                        | error error => simp [argumentArity, called] at transferred
                        | ok value =>
                            simp [argumentArity, called, Frame.advance,
                              Frame.pushValue] at transferred
                            subst target
                            exact .extern noCredits resolved declaration
                              argumentArity called
                      · simp [argumentArity] at transferred

/-- Public equation for the private terminator worker at a canonical running
machine. -/
def TerminatorTransfer (context : Context)
    (interpretation : Interpretation) (store : Store) (heapFuel : Nat)
    (frame : Frame) (stack : List Continuation) (terminator : Terminator)
    (target : Machine) : Prop :=
  runTerminator context interpretation
    { store, heapFuel, control := .running frame stack }
    frame stack terminator = .ok target

/-- Every successful runtime shape of one IxIR₂ terminator. -/
inductive TerminatorTransferCase (context : Context)
    (interpretation : Interpretation) (store : Store) (heapFuel : Nat)
    (frame : Frame) : List Continuation → Terminator → Machine → Prop where
  | jump {stack : List Continuation} {edge : Edge} {target : Frame}
      (transferred : EdgeTransfer frame edge #[] target) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.jump edge)
        { store, heapFuel, control := .running target stack }
  | switchCtor {stack : List Continuation} {scrutinee : Atom}
      {constructors : Array CtorAlt} {natPeel : Option NatPeel}
      {location : Nat} {box : NodeBox} {cid : CtorId}
      {fields : Array RVal} {alternative : CtorAlt} {target : Frame}
      (resolved : resolveAtom frame.values scrutinee = .ok (.loc location))
      (boxAt : store.get? location = some box)
      (node : box.node = .ctorN cid fields)
      (alternativeAt : constructors.find? (fun candidate =>
        candidate.cid == cid) = some alternative)
      (transferred : EdgeTransfer frame alternative.edge #[] target) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.switchValue scrutinee constructors natPeel)
        { store, heapFuel, control := .running target stack }
  | switchNatZero {stack : List Continuation} {scrutinee : Atom}
      {constructors : Array CtorAlt} {peel : NatPeel} {target : Frame}
      (resolved : resolveAtom frame.values scrutinee =
        .ok (.lit (.nat 0)))
      (transferred : EdgeTransfer frame peel.zero #[] target) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.switchValue scrutinee constructors (some peel))
        { store, heapFuel, control := .running target stack }
  | switchNatSucc {stack : List Continuation} {scrutinee : Atom}
      {constructors : Array CtorAlt} {peel : NatPeel} {predecessor : Nat}
      {target : Frame}
      (resolved : resolveAtom frame.values scrutinee =
        .ok (.lit (.nat (predecessor + 1))))
      (transferred : EdgeTransfer frame peel.succ
        #[.lit (.nat predecessor)] target) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.switchValue scrutinee constructors (some peel))
        { store, heapFuel, control := .running target stack }
  | branchPresent {stack : List Continuation} {creditId : CreditId}
      {credit : Credit} {someEdge noneEdge : Edge} {target : Frame}
      (lookedUp : CreditLookup frame creditId credit)
      (present : credit.isPresent = true)
      (transferred : EdgeTransfer frame someEdge #[] target) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.branchCredit creditId someEdge noneEdge)
        { store, heapFuel, control := .running target stack }
  | branchAbsent {stack : List Continuation} {creditId : CreditId}
      {credit : Credit} {someEdge noneEdge : Edge} {target : Frame}
      (lookedUp : CreditLookup frame creditId credit)
      (absent : credit.isPresent = false)
      (transferred : EdgeTransfer frame noneEdge #[] target) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.branchCredit creditId someEdge noneEdge)
        { store, heapFuel, control := .running target stack }
  | retResume {caller : Frame} {rest : List Continuation}
      {atom : Atom} {value : RVal}
      (resolved : resolveAtom frame.values atom = .ok value)
      (noCredits : NoLiveCredits frame)
      (world : value.hasWorld store frame.definition.signature.result = true) :
      TerminatorTransferCase context interpretation store heapFuel frame
        (.resume caller :: rest) (.ret atom)
        { store, heapFuel
          control := .running
            { caller with values := caller.values.push value } rest }
  | retHalt {atom : Atom} {value : RVal}
      (resolved : resolveAtom frame.values atom = .ok value)
      (noCredits : NoLiveCredits frame)
      (world : value.hasWorld store frame.definition.signature.result = true) :
      TerminatorTransferCase context interpretation store heapFuel frame
        [] (.ret atom) { store, heapFuel, control := .halted value }
  | retApplyMore {caller : Frame} {arguments : Array RVal}
      {rest : List Continuation} {atom : Atom} {value : RVal}
      {target : Machine}
      (resolved : resolveAtom frame.values atom = .ok value)
      (noCredits : NoLiveCredits frame)
      (world : value.hasWorld store frame.definition.signature.result = true)
      (transferred : ApplyTransfer context interpretation store heapFuel value
        arguments caller rest target) :
      TerminatorTransferCase context interpretation store heapFuel frame
        (.applyMore arguments caller :: rest) (.ret atom) target
  | tailCallFn {stack : List Continuation} {address : Address}
      {argumentAtoms : Array Atom} {arguments : Array RVal}
      {definition : Function}
      (noCredits : NoLiveCredits frame)
      (resolved : resolveAtoms frame.values argumentAtoms = .ok arguments)
      (declaration : context.declarations address = some (.fn definition))
      (arity : arguments.size = definition.signature.params.size)
      (nonempty : definition.blocks.isEmpty = false) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.tailCall address argumentAtoms)
        { store, heapFuel
          control := .running { definition, values := arguments } stack }
  | tailCallSelf {stack : List Continuation} {argumentAtoms : Array Atom}
      {arguments : Array RVal}
      (noCredits : NoLiveCredits frame)
      (resolved : resolveAtoms frame.values argumentAtoms = .ok arguments)
      (arity : arguments.size = frame.definition.signature.params.size)
      (nonempty : frame.definition.blocks.isEmpty = false) :
      TerminatorTransferCase context interpretation store heapFuel frame stack
        (.tailCallSelf argumentAtoms)
        { store, heapFuel
          control := .running
            { definition := frame.definition, values := arguments } stack }

/-- Each classified terminator shape reconstructs the public small step once
the enclosing terminal position is supplied. -/
theorem TerminatorTransferCase.step {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation}
    {terminator : Terminator} {target : Machine}
    (classified : TerminatorTransferCase context interpretation store
      heapFuel frame stack terminator target)
    {block : Block}
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc = block.instructions.size)
    (terminatorAt : block.terminator = terminator) :
    Step context interpretation
      { store, heapFuel, control := .running frame stack } target := by
  cases classified with
  | jump transferred =>
      exact Step.jump rfl blockAt pc terminatorAt transferred
  | switchCtor resolved boxAt node alternativeAt transferred =>
      exact Step.switchCtor rfl blockAt pc terminatorAt resolved boxAt node
        alternativeAt transferred
  | switchNatZero resolved transferred =>
      exact Step.switchNatZero rfl blockAt pc terminatorAt resolved transferred
  | switchNatSucc resolved transferred =>
      exact Step.switchNatSucc rfl blockAt pc terminatorAt resolved transferred
  | branchPresent lookedUp present transferred =>
      exact Step.branchCreditPresent rfl blockAt pc terminatorAt lookedUp
        present transferred
  | branchAbsent lookedUp absent transferred =>
      exact Step.branchCreditAbsent rfl blockAt pc terminatorAt lookedUp absent
        transferred
  | retResume resolved noCredits world =>
      exact Step.retResumeCleared rfl blockAt pc terminatorAt resolved noCredits
        world
  | retHalt resolved noCredits world =>
      exact Step.retHaltCleared rfl blockAt pc terminatorAt resolved noCredits
        world
  | retApplyMore resolved noCredits world transferred =>
      exact Step.retApplyMoreCleared rfl blockAt pc terminatorAt resolved
        noCredits world transferred
  | tailCallFn noCredits resolved declaration arity nonempty =>
      exact Step.tailCallFnCleared rfl blockAt pc terminatorAt noCredits
        resolved declaration arity nonempty
  | tailCallSelf noCredits resolved arity nonempty =>
      exact Step.tailCallSelfCleared rfl blockAt pc terminatorAt noCredits
        resolved arity nonempty

/-- Invert an arbitrary successful terminator-worker equation into its exact
runtime case. -/
theorem TerminatorTransfer.classify {context : Context}
    {interpretation : Interpretation} {store : Store} {heapFuel : Nat}
    {frame : Frame} {stack : List Continuation}
    {terminator : Terminator} {target : Machine}
    (transferred : TerminatorTransfer context interpretation store heapFuel
      frame stack terminator target) :
    TerminatorTransferCase context interpretation store heapFuel frame stack
      terminator target := by
  unfold TerminatorTransfer runTerminator at transferred
  simp only [bind, Except.bind, pure, Except.pure] at transferred
  cases terminator with
  | jump edge =>
      cases edgeRun : transferEdge frame edge with
      | error error => simp [edgeRun] at transferred
      | ok targetFrame =>
          simp [edgeRun] at transferred
          subst target
          exact .jump edgeRun
  | switchValue scrutinee constructors natPeel =>
      cases resolved : resolveAtom frame.values scrutinee with
      | error error => simp [resolved] at transferred
      | ok value =>
          cases value with
          | erased => simp [resolved] at transferred
          | loc location =>
              simp only [resolved] at transferred
              cases boxAt : store.get? location with
              | none => simp [boxAt] at transferred
              | some box =>
                  simp only [boxAt] at transferred
                  cases node : box.node with
                  | papN address arity arguments =>
                      simp [node] at transferred
                  | ctorN cid fields =>
                      simp only [node] at transferred
                      cases alternativeAt : constructors.find?
                          (fun candidate => candidate.cid == cid) with
                      | none => simp [alternativeAt] at transferred
                      | some alternative =>
                          simp only [alternativeAt] at transferred
                          cases edgeRun : transferEdge frame alternative.edge with
                          | error error => simp [edgeRun] at transferred
                          | ok targetFrame =>
                              simp [edgeRun] at transferred
                              subst target
                              exact .switchCtor resolved boxAt node alternativeAt
                                edgeRun
          | lit literal =>
              cases literal with
              | str string => simp [resolved] at transferred
              | nat number =>
                  cases natPeel with
                  | none => simp [resolved] at transferred
                  | some peel =>
                      cases number with
                      | zero =>
                          simp only [resolved] at transferred
                          cases edgeRun : transferEdge frame peel.zero with
                          | error error => simp [edgeRun] at transferred
                          | ok targetFrame =>
                              simp [edgeRun] at transferred
                              subst target
                              exact .switchNatZero resolved edgeRun
                      | succ predecessor =>
                          simp only [resolved] at transferred
                          cases edgeRun : transferEdge frame peel.succ
                              #[.lit (.nat predecessor)] with
                          | error error => simp [edgeRun] at transferred
                          | ok targetFrame =>
                              simp [edgeRun] at transferred
                              subst target
                              exact .switchNatSucc resolved edgeRun
  | branchCredit creditId someEdge noneEdge =>
      cases lookedUp : creditAt frame creditId with
      | error error => simp [lookedUp] at transferred
      | ok credit =>
          simp only [lookedUp] at transferred
          cases present : credit.isPresent with
          | false =>
              cases edgeRun : transferEdge frame noneEdge with
              | error error => simp [present, edgeRun] at transferred
              | ok targetFrame =>
                  simp [present, edgeRun] at transferred
                  subst target
                  exact .branchAbsent lookedUp present edgeRun
          | true =>
              cases edgeRun : transferEdge frame someEdge with
              | error error => simp [present, edgeRun] at transferred
              | ok targetFrame =>
                  simp [present, edgeRun] at transferred
                  subst target
                  exact .branchPresent lookedUp present edgeRun
  | ret atom =>
      cases resolved : resolveAtom frame.values atom with
      | error error => simp [resolved] at transferred
      | ok value =>
          simp only [resolved] at transferred
          unfold finishReturn at transferred
          simp only [pure, Except.pure] at transferred
          cases live : frame.hasCredits with
          | true => simp [live] at transferred
          | false =>
              have noCredits : NoLiveCredits frame := by
                simpa [NoLiveCredits, Frame.hasCredits] using live
              simp only [live, Bool.false_eq_true, ↓reduceIte] at transferred
              cases world : value.hasWorld store
                  frame.definition.signature.result with
              | false => simp [world] at transferred
              | true =>
                  simp only [world, Bool.not_true, Bool.false_eq_true,
                    ↓reduceIte] at transferred
                  cases stack with
                  | nil =>
                      simp at transferred
                      subst target
                      exact .retHalt resolved noCredits world
                  | cons continuation rest =>
                      cases continuation with
                      | resume caller =>
                          simp [Frame.pushValue] at transferred
                          subst target
                          exact .retResume resolved noCredits world
                      | applyMore arguments caller =>
                          change ApplyTransfer context interpretation store
                            heapFuel value arguments caller rest target
                            at transferred
                          exact .retApplyMore resolved noCredits world
                            transferred
  | tailCall address argumentAtoms =>
      cases live : frame.hasCredits with
      | true => simp [ensureCallBoundary, live] at transferred
      | false =>
          have noCredits : NoLiveCredits frame := by
            simpa [NoLiveCredits, Frame.hasCredits] using live
          simp only [ensureCallBoundary, live, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure] at transferred
          cases resolved : resolveAtoms frame.values argumentAtoms with
          | error error => simp [resolved] at transferred
          | ok arguments =>
              simp only [resolved] at transferred
              cases declaration : context.declarations address with
              | none => simp [declaration] at transferred
              | some declared =>
                  simp only [declaration] at transferred
                  cases declared with
                  | extern arity => simp at transferred
                  | fn definition =>
                      by_cases arity :
                          arguments.size = definition.signature.params.size
                      · cases empty : definition.blocks.isEmpty with
                        | true =>
                            simp [enterFunction, arity, empty] at transferred
                        | false =>
                            simp [enterFunction, arity, empty] at transferred
                            subst target
                            exact .tailCallFn noCredits resolved declaration
                              arity empty
                      · simp [enterFunction, arity] at transferred
  | tailCallSelf argumentAtoms =>
      cases live : frame.hasCredits with
      | true => simp [ensureCallBoundary, live] at transferred
      | false =>
          have noCredits : NoLiveCredits frame := by
            simpa [NoLiveCredits, Frame.hasCredits] using live
          simp only [ensureCallBoundary, live, Bool.false_eq_true,
            ↓reduceIte, pure, Except.pure] at transferred
          cases resolved : resolveAtoms frame.values argumentAtoms with
          | error error => simp [resolved] at transferred
          | ok arguments =>
              simp only [resolved] at transferred
              by_cases arity :
                  arguments.size = frame.definition.signature.params.size
              · cases empty : frame.definition.blocks.isEmpty with
                | true => simp [enterFunction, arity, empty] at transferred
                | false =>
                    simp [enterFunction, arity, empty] at transferred
                    subst target
                    exact .tailCallSelf noCredits resolved arity empty
              · simp [enterFunction, arity] at transferred

/-- Exhaustive successful shapes of the public one-step evaluator. -/
inductive StepCase (context : Context) (interpretation : Interpretation) :
    Machine → Machine → Prop where
  | halted {store : Store} {heapFuel : Nat} {value : RVal} :
      StepCase context interpretation
        { store, heapFuel, control := .halted value }
        { store, heapFuel, control := .halted value }
  | instruction {store : Store} {heapFuel : Nat} {frame : Frame}
      {stack : List Continuation} {block : Block} {instruction : Instr}
      {target : Machine}
      (blockAt : frame.definition.blocks[frame.block]? = some block)
      (pc : frame.pc < block.instructions.size)
      (instructionAt : block.instructions[frame.pc] = instruction)
      (classified : InstructionTransferCase context interpretation store
        heapFuel frame stack instruction target) :
      StepCase context interpretation
        { store, heapFuel, control := .running frame stack } target
  | terminator {store : Store} {heapFuel : Nat} {frame : Frame}
      {stack : List Continuation} {block : Block} {terminator : Terminator}
      {target : Machine}
      (blockAt : frame.definition.blocks[frame.block]? = some block)
      (pc : frame.pc = block.instructions.size)
      (terminatorAt : block.terminator = terminator)
      (classified : TerminatorTransferCase context interpretation store
        heapFuel frame stack terminator target) :
      StepCase context interpretation
        { store, heapFuel, control := .running frame stack } target

/-- Every classified whole-step shape reconstructs the public evaluator
equation. -/
theorem StepCase.step {context : Context} {interpretation : Interpretation}
    {before after : Machine}
    (classified : StepCase context interpretation before after) :
    Step context interpretation before after := by
  cases classified with
  | halted => rfl
  | instruction blockAt pc instructionAt instructionCase =>
      exact instructionCase.step blockAt pc instructionAt
  | terminator blockAt pc terminatorAt terminatorCase =>
      exact terminatorCase.step blockAt pc terminatorAt

/-- Every successful public step is either the halted self-step, one exact
instruction runtime shape, or one exact terminator runtime shape. -/
theorem Step.classify {context : Context} {interpretation : Interpretation}
    {before after : Machine}
    (stepped : Step context interpretation before after) :
    StepCase context interpretation before after := by
  unfold Step step at stepped
  cases before with
  | mk store heapFuel control =>
      cases control with
      | halted value =>
          change Except.ok
            { store, heapFuel, control := .halted value } = .ok after
            at stepped
          injection stepped with afterEq
          subst after
          exact .halted
      | running frame stack =>
          unfold currentBlock at stepped
          cases blockAt : frame.definition.blocks[frame.block]? with
          | none =>
              simp [blockAt, bind, Except.bind] at stepped
          | some block =>
              simp only [blockAt, bind, Except.bind]
                at stepped
              by_cases pc : frame.pc < block.instructions.size
              · rw [dif_pos pc] at stepped
                change InstructionTransfer context interpretation store
                  heapFuel frame stack block.instructions[frame.pc] after
                  at stepped
                exact .instruction blockAt pc rfl stepped.classify
              · rw [dif_neg pc] at stepped
                by_cases terminal : frame.pc = block.instructions.size
                · have terminalBool :
                      (frame.pc == block.instructions.size) = true :=
                    beq_iff_eq.mpr terminal
                  rw [terminalBool] at stepped
                  change TerminatorTransfer context interpretation store
                    heapFuel frame stack block.terminator after at stepped
                  exact .terminator blockAt terminal rfl stepped.classify
                · have terminalBool :
                      (frame.pc == block.instructions.size) = false :=
                    Bool.eq_false_iff.mpr (by
                      intro equal
                      exact terminal (beq_iff_eq.mp equal))
                  rw [terminalBool] at stepped
                  simp at stepped

/-- A finite sequence of genuine running-state transitions.  Requiring the
source of each transition to be running prevents the evaluator's halted
self-step from pretending to consume control fuel. -/
inductive Steps (context : Context) (interpretation : Interpretation) :
    Nat → Machine → Machine → Prop where
  | refl (machine : Machine) : Steps context interpretation 0 machine machine
  | cons {count : Nat} {before middle after : Machine}
      {frame : Frame} {stack : List Continuation}
      (running : before.control = .running frame stack)
      (head : Step context interpretation before middle)
      (tail : Steps context interpretation count middle after) :
      Steps context interpretation (Nat.succ count) before after

/-- One running small step is a one-element finite execution. -/
theorem Step.toSteps {context : Context} {interpretation : Interpretation}
    {before after : Machine} {frame : Frame} {stack : List Continuation}
    (running : before.control = .running frame stack)
    (step : Step context interpretation before after) :
    Steps context interpretation 1 before after :=
  .cons running step (.refl after)

/-- The evaluator's one-step relation is deterministic because it is the
successful graph of the executable `step` function. -/
theorem Step.deterministic {context : Context}
    {interpretation : Interpretation} {before left right : Machine}
    (leftStep : Step context interpretation before left)
    (rightStep : Step context interpretation before right) :
    left = right := by
  exact Except.ok.inj (leftStep.symm.trans rightStep)

/-- Finite executions compose and their exact step counts add. -/
theorem Steps.trans {context : Context} {interpretation : Interpretation}
    {firstCount secondCount : Nat} {before middle after : Machine}
    (first : Steps context interpretation firstCount before middle)
    (second : Steps context interpretation secondCount middle after) :
    Steps context interpretation (firstCount + secondCount) before after := by
  induction first with
  | refl => simpa using second
  | cons running head tail ih =>
      simpa only [Nat.succ_add] using
        (Steps.cons running head (ih second))

/-- Any finite prefix of an execution that eventually halts can be cancelled
from the unique execution path.  In particular the prefix cannot run past the
halted endpoint, because `Steps` admits transitions only from running states. -/
theorem Steps.cancelPrefixToHalted {context : Context}
    {interpretation : Interpretation}
    {prefixCount totalCount : Nat} {before middle final : Machine}
    {store : Store} {heapFuel : Nat} {value : RVal}
    (prefixSteps : Steps context interpretation prefixCount before middle)
    (total : Steps context interpretation totalCount before final)
    (halted : final = { store, heapFuel, control := .halted value }) :
    ∃ suffixCount,
      totalCount = prefixCount + suffixCount ∧
        Steps context interpretation suffixCount middle final := by
  induction prefixSteps generalizing totalCount final with
  | refl machine =>
      exact ⟨totalCount, by simp, total⟩
  | @cons prefixCount before prefixMiddle middle frame stack running head tail
      ih =>
      cases total with
      | refl =>
          have controls : Control.running frame stack = .halted value := by
            rw [← running]
            exact congrArg Machine.control halted
          contradiction
      | @cons totalCount _ totalMiddle final totalFrame totalStack
          totalRunning totalHead totalTail =>
          have middleEq : prefixMiddle = totalMiddle :=
            head.deterministic totalHead
          subst totalMiddle
          obtain ⟨suffixCount, countEq, suffix⟩ :=
            ih totalTail halted
          exact ⟨suffixCount, by omega, suffix⟩

/-- Total runner with a control budget independent of `Machine.heapFuel`. -/
def runMachine (context : Context) (interpretation : Interpretation) :
    Nat → Machine → Except Error Result
  | controlFuel, { store, heapFuel, control := .halted value } =>
      let result : Result :=
        { store := store
          value := value
          controlRemaining := controlFuel
          heapRemaining := heapFuel }
      .ok result
  | 0, { store := _, heapFuel := _, control := .running .. } =>
      .error .controlFuel
  | controlFuel + 1,
      machine@{ store := _, heapFuel := _, control := .running .. } => do
      let machine ← step context interpretation machine
      runMachine context interpretation controlFuel machine

/-- Exact machine state from which `runFunction` starts after its entry checks
succeed. Keeping this constructor public lets compiler simulations connect a
certified entry block to the finite-step runner without unfolding private
evaluator helpers. -/
def initialMachine (definition : Function) (arguments : Array RVal)
    (heapFuel : Nat) (store : Store := {}) : Machine :=
  { store := store.withPeak
    heapFuel
    control := .running { definition, values := arguments } [] }

/-- A fresh initial machine has the literal empty target store; peak tracking
does not perturb it. -/
@[simp] theorem initialMachine_store_empty (definition : Function)
    (arguments : Array RVal) (heapFuel : Nat) :
    (initialMachine definition arguments heapFuel).store = ({} : Store) := by
  rfl

def runFunction (context : Context) (interpretation : Interpretation)
    (definition : Function) (arguments : Array RVal) (controlFuel heapFuel : Nat)
    (store : Store := {}) : Except Error Result := do
  let frame ← enterFunction definition arguments
  runMachine context interpretation controlFuel
    { store := store.withPeak, heapFuel, control := .running frame [] }

/-- Public reduction of a successful function-entry check to the exact
initial machine. -/
theorem runFunction_eq_runMachine {context : Context}
    {interpretation : Interpretation} {definition : Function}
    {arguments : Array RVal} {controlFuel heapFuel : Nat} {store : Store}
    (arity : arguments.size = definition.signature.params.size)
    (nonempty : definition.blocks.isEmpty = false) :
    runFunction context interpretation definition arguments controlFuel
        heapFuel store =
      runMachine context interpretation controlFuel
        (initialMachine definition arguments heapFuel store) := by
  simp [runFunction, initialMachine, enterFunction, arity, nonempty]
  rfl

def runMain (context : Context) (interpretation : Interpretation)
    (program : Program) (controlFuel : Nat := 100000)
    (heapFuel : Nat := 100000) : Except Error Result :=
  runFunction context interpretation program.main #[] controlFuel heapFuel

/-- Public main-entry specialization of `runFunction_eq_runMachine`. -/
theorem runMain_eq_runMachine {context : Context}
    {interpretation : Interpretation} {program : Program}
    {controlFuel heapFuel : Nat}
    (arity : program.main.signature.params.size = 0)
    (nonempty : program.main.blocks.isEmpty = false) :
    runMain context interpretation program controlFuel heapFuel =
      runMachine context interpretation controlFuel
        (initialMachine program.main #[] heapFuel) := by
  unfold runMain
  apply runFunction_eq_runMachine
  · simpa using arity.symm
  · exact nonempty

/-- Running a finite execution prefix spends exactly its step count from the
control budget and leaves evaluation of the suffix unchanged. -/
theorem Steps.runMachine {context : Context}
    {interpretation : Interpretation} {count controlFuel : Nat}
    {before after : Machine}
    (steps : Steps context interpretation count before after) :
    Ix.Compiler.IxIR2.Eval.runMachine context interpretation
        (count + controlFuel) before =
      Ix.Compiler.IxIR2.Eval.runMachine context interpretation
        controlFuel after := by
  induction steps with
  | refl => simp only [Nat.zero_add]
  | @cons count before middle after frame stack running head tail ih =>
      rw [Nat.succ_add]
      cases before with
      | mk store heapFuel beforeControl =>
          simp only at running
          subst beforeControl
          simp only [Ix.Compiler.IxIR2.Eval.runMachine]
          rw [head]
          simp only [bind, Except.bind]
          exact ih

/-- A finite execution ending in a halt gives an exact successful runner
witness with no unused control fuel. -/
theorem Steps.runMachine_halted {context : Context}
    {interpretation : Interpretation} {count : Nat}
    {before : Machine} {store : Store} {heapFuel : Nat} {value : RVal}
    (steps : Steps context interpretation count before
      { store, heapFuel, control := .halted value }) :
    Ix.Compiler.IxIR2.Eval.runMachine context interpretation count before =
      .ok
        { store
          value
          controlRemaining := 0
          heapRemaining := heapFuel } := by
  simpa [Ix.Compiler.IxIR2.Eval.runMachine] using
    (steps.runMachine (controlFuel := 0))

/-- A successful runner exposes its exact finite execution and the unused
control budget. The execution stops at the reported halted store and value. -/
theorem runMachine_steps {context : Context} {interpretation : Interpretation}
    {controlFuel : Nat} {machine : Machine} {result : Result}
    (run : runMachine context interpretation controlFuel machine = .ok result) :
    ∃ count,
      controlFuel = count + result.controlRemaining ∧
        Steps context interpretation count machine
          { store := result.store
            heapFuel := result.heapRemaining
            control := .halted result.value } := by
  induction controlFuel generalizing machine with
  | zero =>
      rcases machine with ⟨store, heapFuel, control⟩
      cases control with
      | halted value =>
          simp only [runMachine, Except.ok.injEq] at run
          subst result
          exact ⟨0, by simp, .refl _⟩
      | running frame stack => cases run
  | succ controlFuel ih =>
      rcases machine with ⟨store, heapFuel, control⟩
      cases control with
      | halted value =>
          simp only [runMachine, Except.ok.injEq] at run
          subst result
          exact ⟨0, by simp, .refl _⟩
      | running frame stack =>
          simp only [runMachine] at run
          cases stepped : step context interpretation
              { store, heapFuel, control := .running frame stack } with
          | error error => simp [stepped, bind, Except.bind] at run
          | ok next =>
              simp only [stepped, bind, Except.bind] at run
              obtain ⟨count, budget, steps⟩ := ih run
              exact ⟨count + 1, by omega, .cons rfl stepped steps⟩


end Ix.Compiler.IxIR2.Eval
