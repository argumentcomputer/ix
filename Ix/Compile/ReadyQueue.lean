module

public import Ix.Compile.ReadyPublication
public import Ix.Compile.Parallel
import all Ix.Compile.WorkerReplay

/-! # Bounded dependency-ready computation

Only the calling IO thread changes queue state. Workers receive immutable
source input and a sparse address table, and never wait for parent tasks.
Publication still uses `ReadyPublication` and the original frozen snapshots.
-/

public section

namespace Ix.Compile.ReadyQueue

open Ix.CompileM Ix.Compile.WorkerReplay

structure Config where
  workers : Nat := 32
  lookahead : Nat := 8192
  pendingEdges : Nat := 65536
  payloadBytes : Nat := 1024 * 1024 * 1024

structure Descriptor where
  key : Ix.Name
  representative : Ix.Name
  members : Ix.Set Ix.Name
  dependencies : Array Ix.Name
  parents : Array Nat
  deriving Inhabited

structure Plan where
  descriptors : Array Descriptor
  indices : Std.HashMap Ix.Compile.ExactKey.ExactName Nat

/-- Predicted publication ranks only guide computation. The checked publisher
retains the real readiness and refusal rules, including malformed graphs. -/
def makePlan (blocks : Ix.CondensedBlocks) (sched : FoldSchedule) (st : FoldState) : Plan := Id.run do
  let mut ready := initialReady blocks sched st
  let mut unmet := st.unmet
  let mut rows : WaveBlocks := #[]
  for _ in [:blocks.blocks.size + 1] do
    if ready.isEmpty then break
    rows := rows ++ ready
    let (nextUnmet, nextReady) := predictedNext blocks sched unmet ready
    unmet := nextUnmet
    ready := nextReady
  let indices := rows.zipIdx.foldl (fun indices ((_, rep, _), i) =>
    indices.insert rep i) (Std.HashMap.emptyWithCapacity rows.size)
  let descriptors := Ix.Compile.Parallel.map 256 (fun (key, representative, members) => Id.run do
    let dependencies := (sched.deps.getD representative {}).toArray
    let mut parents : Array Nat := #[]
    for name in dependencies do
      if let some owner := blocks.lowLinks.get? name then
        if let some index := indices.get? owner then
          if !parents.contains index then parents := parents.push index
    return { key, representative, members, dependencies, parents : Descriptor }) rows
  return { descriptors, indices }

private def pushReady (heap : Array Nat) (value : Nat) : Array Nat := Id.run do
  let mut heap := heap.push value
  let mut i := heap.size - 1
  for _ in [:heap.size] do
    if i == 0 then break
    let parent := (i - 1) / 2
    if heap[parent]! ≤ heap[i]! then break
    heap := heap.swapIfInBounds parent i
    i := parent
  return heap

private def popReady (heap : Array Nat) : Option (Nat × Array Nat) := Id.run do
  let some first := heap[0]? | return none
  if heap.size == 1 then return some (first, #[])
  let mut heap := (heap.set! 0 heap.back!).pop
  let mut i := 0
  for _ in [:heap.size] do
    let left := 2 * i + 1
    if left ≥ heap.size then break
    let right := left + 1
    let child := if right < heap.size && heap[right]! < heap[left]! then right else left
    if heap[i]! ≤ heap[child]! then break
    heap := heap.swapIfInBounds i child
    i := child
  return some (first, heap)

structure Metrics where
  started : Nat := 0
  completed : Nat := 0
  drained : Nat := 0
  fallbackRequests : Nat := 0
  reused : Nat := 0
  sourceFallbacks : Nat := 0
  failedFallbacks : Nat := 0
  addressFallbacks : Nat := 0
  blobFallbacks : Nat := 0
  waitMs : Nat := 0
  maxActive : Nat := 0
  maxAdmitted : Nat := 0
  maxPendingEdges : Nat := 0
  maxResults : Nat := 0
  maxPayloadBytes : Nat := 0
  deriving Repr, Inhabited

structure State (input : FixedInput) where
  next : Nat := 0
  frontier : Nat := 0
  admitted : Std.HashSet Nat := {}
  completed : Std.HashSet Nat := {}
  published : Std.HashSet Nat := {}
  unmet : Std.HashMap Nat Nat := {}
  waiters : Std.HashMap Nat (Array Nat) := {}
  ready : Array Nat := #[]
  active : List (Nat × Task (Nat × Candidate input)) := []
  bank : Std.HashMap Nat (Candidate input) := {}
  claims : AddressTable := {}
  sizes : Std.HashMap Nat Nat := {}
  edges : Nat := 0
  bytes : Nat := 0
  metrics : Metrics := {}

structure Controller (input : FixedInput) where
  config : Config
  plan : Plan
  state : IO.Ref (State input)

private def admit (config : Config) (plan : Plan) (st : State input) : State input := Id.run do
  let mut st := st
  for _ in [:plan.descriptors.size] do
    if st.next ≥ plan.descriptors.size || st.next ≥ st.frontier + max 1 config.lookahead then break
    let i := st.next
    if st.published.contains i then
      st := { st with next := i + 1 }
      continue
    if st.bytes ≥ config.payloadBytes then break
    let pending := plan.descriptors[i]!.parents.filter (!st.completed.contains ·)
    if st.edges + pending.size > config.pendingEdges then break
    let admitted := st.admitted
    let unmet := st.unmet
    let mut waiters := st.waiters
    let ready := st.ready
    st := { st with
      admitted := {}
      unmet := {}
      waiters := {}
      ready := #[] }
    for parent in pending do
      let children := waiters.getD parent #[]
      waiters := waiters.erase parent
      waiters := waiters.insert parent (children.push i)
    let admitted := admitted.insert i
    let unmet := unmet.insert i pending.size
    let ready := if pending.isEmpty then pushReady ready i else ready
    let edges := st.edges + pending.size
    let maxAdmitted := max st.metrics.maxAdmitted admitted.size
    let maxPendingEdges := max st.metrics.maxPendingEdges edges
    st := { st with
      next := i + 1
      admitted
      unmet
      waiters
      edges
      ready
      metrics := { st.metrics with maxAdmitted, maxPendingEdges } }
  return st

private def startReady (input : FixedInput) (config : Config) (plan : Plan)
    (st : State input) : State input := Id.run do
  let mut st := st
  -- One slot is reserved for the publisher's exact fallback computation.
  for _ in [:plan.descriptors.size] do
    if st.active.length ≥ config.workers - 1 || st.bytes ≥ config.payloadBytes then break
    if st.ready.isEmpty then break
    let heap := st.ready
    st := { st with ready := #[] }
    let some (i, ready) := popReady heap | break
    st := { st with ready }
    if st.completed.contains i || st.published.contains i then continue
    let descriptor := plan.descriptors[i]!
    let mut addresses : AddressTable := {}
    for name in descriptor.dependencies do
      if let some address := st.claims.get? name then addresses := addresses.insert name address
    let task := Task.spawn fun _ =>
      (i, speculate input descriptor.key descriptor.members addresses)
    st := { st with
      active := (i, task) :: st.active
      metrics := { st.metrics with
        started := st.metrics.started + 1
        maxActive := max st.metrics.maxActive (st.active.length + 1) } }
  return st

private def wake (i : Nat) (st : State input) : State input := Id.run do
  if st.completed.contains i then return st
  let children := st.waiters.getD i #[]
  let completed := st.completed
  let waiters := st.waiters
  let mut unmet := st.unmet
  let mut ready := st.ready
  let st := { st with
    completed := {}
    waiters := {}
    unmet := {}
    ready := #[]
    edges := st.edges - children.size }
  let completed := completed.insert i
  let waiters := waiters.erase i
  for child in children do
    match unmet.get? child with
    | some 1 =>
      unmet := unmet.erase child
      ready := pushReady ready child
    | some remaining => unmet := unmet.insert child (remaining - 1)
    | none => pure ()
  return { st with completed, waiters, unmet, ready }

/-- Serialized block/blob payload is a retention proxy, not a heap or RSS
bound. In-flight completions can overshoot it by at most their payloads. -/
private def payloadSize (candidate : Candidate input) : Nat :=
  match candidate.compiled with
  | none => 0
  | some (result, cache) => result.blockBytes.size +
      cache.blockBlobs.fold (fun total _ bytes => total + bytes.size) 0

private def collect (i : Nat) (candidate : Candidate input) (st : State input) : State input := Id.run do
  let claims := st.claims
  let mut st := { st with
    active := st.active.filter (·.1 != i)
    claims := {}
    metrics := { st.metrics with completed := st.metrics.completed + 1 } }
  let claims := (candidateClaims candidate).fold (fun claims name address =>
    claims.insert name address) claims
  st := { st with claims }
  if !st.published.contains i then
    let bytes := payloadSize candidate
    let bank := st.bank
    let sizes := st.sizes
    st := { st with bank := {}, sizes := {} }
    let bank := bank.insert i candidate
    let sizes := sizes.insert i bytes
    let totalBytes := st.bytes + bytes
    st := { st with
      bank
      sizes
      bytes := totalBytes
      metrics := { st.metrics with
        maxResults := max st.metrics.maxResults bank.size
        maxPayloadBytes := max st.metrics.maxPayloadBytes totalBytes } }
  return wake i st

def create (input : FixedInput) (config : Config) (blocks : Ix.CondensedBlocks)
    (sched : FoldSchedule) (st : FoldState) : IO (Controller input) := do
  let plan := makePlan blocks sched st
  let state ← IO.mkRef { claims := st.acc.cenv.nameToAddr : State input }
  return { config, plan, state }

/-- Collect completed workers even when the next publication is already in
the bank. A backlog of completed rows must not prevent worker-slot reuse. -/
def Controller.pump (controller : Controller input) : IO Unit := do
  let active := (← controller.state.get).active
  for (_, task) in active do
    if ← IO.hasFinished task then
      let (finished, candidate) ← IO.wait task
      controller.state.modify (collect finished candidate)
  controller.state.modify fun st => startReady input controller.config controller.plan
    (admit controller.config controller.plan st)

def chooseLoop (controller : Controller input) (i : Nat) : Nat → IO (Option (Candidate input))
  | 0 => pure none
  | fuel + 1 => do
    controller.pump
    let found ← controller.state.modifyGet fun st => (st.bank.get? i, st)
    if found.isSome then return found
    let active := (← controller.state.get).active
    match active with
    | [] => return none
    | first :: rest =>
      let start ← IO.monoMsNow
      let (finished, candidate) ← IO.waitAny (first.2 :: rest.map (·.2))
      let elapsed := (← IO.monoMsNow) - start
      controller.state.modify fun st => collect finished candidate
        { st with metrics := { st.metrics with waitMs := st.metrics.waitMs + elapsed } }
      chooseLoop controller i fuel

def Controller.choose (controller : Controller input) (rep : Ix.Name) : IO (Option (Candidate input)) := do
  let candidate ← match controller.plan.indices.get? rep with
    | none => pure none
    | some i => chooseLoop controller i (controller.plan.descriptors.size + 1)
  if candidate.isNone then controller.state.modify fun st =>
    { st with metrics := { st.metrics with fallbackRequests := st.metrics.fallbackRequests + 1 } }
  return candidate

def Controller.observe (controller : Controller input)
    (disposition : ReadyPublication.Disposition) : IO Unit :=
  controller.state.modify fun state =>
    let metrics := match disposition with
      | .reused => { state.metrics with reused := state.metrics.reused + 1 }
      | .absent => state.metrics
      | .sourceMismatch => { state.metrics with sourceFallbacks := state.metrics.sourceFallbacks + 1 }
      | .workerFailed => { state.metrics with failedFallbacks := state.metrics.failedFallbacks + 1 }
      | .addressMismatch => { state.metrics with addressFallbacks := state.metrics.addressFallbacks + 1 }
      | .blobMismatch => { state.metrics with blobFallbacks := state.metrics.blobFallbacks + 1 }
    { state with metrics }

def Controller.published (controller : Controller input) (rep : Ix.Name) : IO Unit := do
  let some i := controller.plan.indices.get? rep | return ()
  controller.state.modify fun st => Id.run do
    let published := st.published
    let admitted := st.admitted
    let bank := st.bank
    let sizes := st.sizes
    let bytes := st.bytes - sizes.getD i 0
    let mut st := { st with
      published := {}
      admitted := {}
      bank := {}
      sizes := {}
      bytes }
    st := { st with
      published := published.insert i
      admitted := admitted.erase i
      bank := bank.erase i
      sizes := sizes.erase i }
    -- An unlaunched fallback has completed on the publication thread.
    -- A running speculation still owns its completion and is drained normally.
    if !st.active.any (·.1 == i) then st := wake i st
    for _ in [:controller.plan.descriptors.size] do
      if !st.published.contains st.frontier then break
      st := { st with frontier := st.frontier + 1 }
    return st
  controller.pump

/-- Consume every remaining task even on a terminal compiler refusal or IO
exception. Completion values reach the metrics, so no unused pure get can
erase the wait. Each block retains the production sharing task behavior. -/
def Controller.drain (controller : Controller input) : IO Unit := do
  let active := (← controller.state.get).active
  for (_, task) in active do
    let (i, _) ← IO.wait task
    controller.state.modify fun st => { st with
      active := st.active.filter (·.1 != i)
      metrics := { st.metrics with drained := st.metrics.drained + 1 } }
  controller.state.modify fun st => { st with
    bank := {}
    claims := {}
    sizes := {}
    admitted := {}
    unmet := {}
    waiters := {}
    ready := #[]
    bytes := 0
    edges := 0 }

def run (config : Config) (blocks : Ix.CondensedBlocks) (sched : FoldSchedule)
    (width : Nat) (dbg : Bool) (fuel : Nat) (st : FoldState) :
    IO ({ result : Except String FoldState // result = foldWaves blocks sched width dbg fuel st } × Metrics) := do
  let input := FixedInput.ofEnv st.acc.cenv
  let controller ← create input config blocks sched st
  let result ← try
      ReadyPublication.foldWavesIO input blocks sched width dbg controller.choose controller.published
        controller.observe fuel st ⟨rfl, rfl⟩
    finally controller.drain
  return (result, (← controller.state.get).metrics)

end Ix.Compile.ReadyQueue
