import Compilatrix.IxIR1.Eval
import Compilatrix.IxIR2.Validate

/-!
# Logical and physical execution for IxIR₂

The two interpretations share one small-step control machine.  Logical
execution frees a consumed constructor immediately and allocates freshly at
`allocWith`; physical execution reserves the slot and either reuses or
releases it.  Calls are represented by an explicit continuation stack, so the
total runner spends exactly one control unit per IxIR₂ instruction or
terminator.  Recursive heap traversal has an independent budget.
-/

namespace Compilatrix.IxIR2.Eval

open Compilatrix.Ixon (Address Owned)
open Compilatrix.IxIR2

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

def Store.kill (store : Store) (location : Nat) : Store :=
  { store with heap := store.heap.kill location }

def Store.rcTick (store : Store) : Store :=
  { store with heap := store.heap.rcTick }

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

private def retainShared (store : Store) (value : RVal) : Except Error Store :=
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

private def enterFunction (definition : Function) (arguments : Array RVal) :
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

def runFunction (context : Context) (interpretation : Interpretation)
    (definition : Function) (arguments : Array RVal) (controlFuel heapFuel : Nat)
    (store : Store := {}) : Except Error Result := do
  let frame ← enterFunction definition arguments
  runMachine context interpretation controlFuel
    { store := store.withPeak, heapFuel, control := .running frame [] }

def runMain (context : Context) (interpretation : Interpretation)
    (program : Program) (controlFuel : Nat := 100000)
    (heapFuel : Nat := 100000) : Except Error Result :=
  runFunction context interpretation program.main #[] controlFuel heapFuel

end Compilatrix.IxIR2.Eval
