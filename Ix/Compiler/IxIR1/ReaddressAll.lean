import Ix.Compiler.IxIR1.MutualBlock

/-!
# Whole-program IxIR₁ content addressing

Ordinary declaration hashing handles a dependency DAG, while
`IxIR1.MutualBlock` gives a finite spelling to genuine address cycles.  This
module joins those two artifact forms.  It discovers strongly connected
components across one flat IxIR₁ environment, processes the component DAG
from dependencies to users, hashes acyclic singletons as ordinary
declarations, and sends cyclic components through the mutual-block boundary.

The pass is independent of lowering's current source/generated partition.
Function keys are producer names to readdress.  `.extern` declaration keys
remain stable because they select an opaque oracle ABI not represented by the
arity-only declaration bytes; caller-owned identities absent from the
declaration environment (notably constructor blocks) are supplied separately
as `reserved`.  The result retains a complete map (including identity entries
for stable externs) and ordered stable/ordinary/block artifact provenance for
later pipeline and proof integration.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address)

namespace ReaddressAll

abbrev Renaming := Readdress.Renaming

/-! ## Deterministic strongly connected components -/

/-- One SCC, with members retained in input declaration order. -/
structure Component where
  members : List (Address × Decl)

namespace Component

def keys (component : Component) : List Address :=
  component.members.map (·.1)

/-- A singleton with an explicit self-address edge is cyclic.  `callSelf`
does not carry an address and therefore remains an ordinary singleton. -/
def cyclic (component : Component) : Bool :=
  match component.members with
  | [(address, declaration)] =>
      (Readdress.Decl.references declaration).contains address
  | _ :: _ :: _ => true
  | _ => false

end Component

private structure GraphPartition where
  /-- Source-index to SCC number.  Numbers are assigned in user-to-dependency
  topological order by the second Kosaraju pass. -/
  componentOf : Array Nat
  componentCount : Nat
  /-- Source-indexed internal dependency edges. -/
  edges : Array (Array Nat)

/-- Iterative Kosaraju partitioning.  Both depth-first passes use explicit
arrays as stacks, so a long dependency chain does not consume the native call
stack.  Address lookup is hash-indexed; graph construction and both passes are
linear in declarations plus address-reference edges. -/
private def graphPartition (raw : List (Address × Decl)) : GraphPartition :=
  Id.run do
    let entries := raw.toArray
    let count := entries.size
    let mut keyIndex : Std.HashMap Address Nat := {}
    let mut sourceIndex := 0
    for entry in entries do
      keyIndex := keyIndex.insert entry.1 sourceIndex
      sourceIndex := sourceIndex + 1

    let mut edges : Array (Array Nat) := Array.replicate count #[]
    let mut reverseEdges : Array (Array Nat) := Array.replicate count #[]
    let mut edgeIndex := 0
    for entry in entries do
      let mut outgoing : Array Nat := #[]
      for reference in Readdress.Decl.references entry.2 do
        match keyIndex.get? reference with
        | none => pure ()
        | some dependency => outgoing := outgoing.push dependency
      edges := edges.set! edgeIndex outgoing
      for dependency in outgoing do
        reverseEdges := reverseEdges.set! dependency
          (reverseEdges[dependency]!.push edgeIndex)
      edgeIndex := edgeIndex + 1

    -- Finish times in the original user-to-dependency graph.
    let mut visited := Array.replicate count false
    let mut finished : Array Nat := #[]
    for root in [:count] do
      if !visited[root]! then
        visited := visited.set! root true
        let mut stack : Array (Nat × Nat) := #[(root, 0)]
        while !stack.isEmpty do
          let frame := stack.back!
          let node := frame.1
          let next := frame.2
          let outgoing := edges[node]!
          if next < outgoing.size then
            stack := stack.set! (stack.size - 1) (node, next + 1)
            let dependency := outgoing[next]!
            if !visited[dependency]! then
              visited := visited.set! dependency true
              stack := stack.push (dependency, 0)
          else
            stack := stack.pop
            finished := finished.push node

    -- Descending finish time over the transpose assigns components in
    -- user-to-dependency topological order.
    let mut componentOf := Array.replicate count count
    let mut componentCount := 0
    for root in finished.reverse do
      if componentOf[root]! == count then
        componentOf := componentOf.set! root componentCount
        let mut stack : Array Nat := #[root]
        while !stack.isEmpty do
          let node := stack.back!
          stack := stack.pop
          for user in reverseEdges[node]! do
            if componentOf[user]! == count then
              componentOf := componentOf.set! user componentCount
              stack := stack.push user
        componentCount := componentCount + 1
    return { componentOf, componentCount, edges }

private def componentBuckets (raw : List (Address × Decl))
    (partition : GraphPartition) : Array (Array (Address × Decl)) :=
  Id.run do
    let entries := raw.toArray
    let mut buckets := Array.replicate partition.componentCount #[]
    let mut sourceIndex := 0
    for entry in entries do
      let component := partition.componentOf[sourceIndex]!
      buckets := buckets.set! component
        (buckets[component]!.push entry)
      sourceIndex := sourceIndex + 1
    return buckets

/-- Discover the SCC partition in first-member source order.  Member order is
also the original declaration order, independent of DFS traversal details. -/
def discoverComponents (raw : List (Address × Decl)) : List Component :=
  let partition := graphPartition raw
  let buckets := componentBuckets raw partition
  Id.run do
    let mut emitted := Array.replicate partition.componentCount false
    let mut components : Array Component := #[]
    for index in [:raw.length] do
      let component := partition.componentOf[index]!
      if !emitted[component]! then
        emitted := emitted.set! component true
        components := components.push ⟨buckets[component]!.toList⟩
    return components.toList

/-- Insert one component in a source-rank min heap. -/
private def heapInsert (rank : Array Nat) (heap : Array Nat)
    (component : Nat) : Array Nat :=
  Id.run do
    let mut result := heap.push component
    let mut index := result.size - 1
    let mut rising := true
    while rising && index > 0 do
      let parent := (index - 1) / 2
      if rank[result[index]!]! < rank[result[parent]!]! then
        let childValue := result[index]!
        let parentValue := result[parent]!
        result := result.set! index parentValue
        result := result.set! parent childValue
        index := parent
      else
        rising := false
    return result

/-- Remove the source-rank-minimal component from a nonempty heap. -/
private def heapTakeMin (rank : Array Nat)
    (heap : Array Nat) : Nat × Array Nat :=
  Id.run do
    let minimum := heap[0]!
    let last := heap.back!
    let mut result := heap.pop
    if !result.isEmpty then
      result := result.set! 0 last
      let mut index := 0
      let mut falling := true
      while falling do
        let left := 2 * index + 1
        if left < result.size then
          let right := left + 1
          let child :=
            if right < result.size &&
                rank[result[right]!]! < rank[result[left]!]! then
              right
            else
              left
          if rank[result[child]!]! < rank[result[index]!]! then
            let parentValue := result[index]!
            let childValue := result[child]!
            result := result.set! index childValue
            result := result.set! child parentValue
            index := child
          else
            falling := false
        else
          falling := false
    return (minimum, result)

/-- SCCs in the same stable dependency-first order as repeatedly selecting
the first ready source component, implemented with a component DAG and a
source-rank min heap. -/
private def discoverComponentsDependencyFirst
    (raw : List (Address × Decl)) : List Component :=
  let partition := graphPartition raw
  let buckets := componentBuckets raw partition
  Id.run do
    let count := partition.componentCount
    let mut rank := Array.replicate count raw.length
    for sourceIndex in [:partition.componentOf.size] do
      let component := partition.componentOf[sourceIndex]!
      if rank[component]! == raw.length then
        rank := rank.set! component sourceIndex

    let mut dependencyCount := Array.replicate count 0
    let mut users : Array (Array Nat) := Array.replicate count #[]
    -- `seen[dependency] == user` records that this component edge has already
    -- been charged while traversing another member/reference of the same SCC.
    let mut seen := Array.replicate count count
    for sourceIndex in [:partition.componentOf.size] do
      let user := partition.componentOf[sourceIndex]!
      for dependencyIndex in partition.edges[sourceIndex]! do
        let dependency := partition.componentOf[dependencyIndex]!
        if dependency != user && seen[dependency]! != user then
          seen := seen.set! dependency user
          dependencyCount := dependencyCount.set! user
            (dependencyCount[user]! + 1)
          users := users.set! dependency (users[dependency]!.push user)

    let mut ready : Array Nat := #[]
    for component in [:count] do
      if dependencyCount[component]! == 0 then
        ready := heapInsert rank ready component

    let mut components : Array Component := #[]
    while !ready.isEmpty do
      let (component, residual) := heapTakeMin rank ready
      ready := residual
      components := components.push ⟨buckets[component]!.toList⟩
      for user in users[component]! do
        let remaining := dependencyCount[user]! - 1
        dependencyCount := dependencyCount.set! user remaining
        if remaining == 0 then
          ready := heapInsert rank ready user
    return components.toList

/-! ## Artifact/result model -/

/-- One dependency-ordered stored artifact.  Equal ordinary declarations and
equal mutual blocks may be shared by several raw keys, so an artifact list can
be shorter than the complete address map. -/
inductive Artifact where
  | stable (address : Address) (declaration : Decl)
  | ordinary (address : Address) (declaration : Decl)
  | mutual (block : MutualBlock.Result)

namespace Artifact

def declarations : Artifact → List (Address × Decl)
  | .stable address declaration => [(address, declaration)]
  | .ordinary address declaration => [(address, declaration)]
  | .mutual block => block.members

def identities : Artifact → List Address
  | .stable address _ => [address]
  | .ordinary address _ => [address]
  | .mutual block => block.blockAddress :: block.derivedAddresses

def contentAddressed : Artifact → Bool
  | .stable _ (.extern _) => true
  | .stable _ _ => false
  | .ordinary address declaration => address == declaration.address
  | .mutual block =>
      block.blockAddress == MutualBlock.Block.address block.blockMembers &&
        block.memberKeysDerived && block.blockStable

end Artifact

/-- A fully readdressed flat IxIR₁ program. -/
structure Result where
  artifacts : List Artifact
  main : Code
  addressMap : Renaming
  /-- Caller-owned identities absent from the declaration producer
  environment.  These are retained so constructor-key protection remains an
  artifact-auditable fact rather than only a construction-time check. -/
  reserved : List Address

private def allUnique : List Address → Bool
  | [] => true
  | address :: rest => !rest.contains address && allUnique rest

namespace Result

def declarations (result : Result) : List (Address × Decl) :=
  result.artifacts.flatMap Artifact.declarations

/-- Forget artifact provenance while retaining the generic address-image
interface used by `ReaddressSim`.  The generated-only pass's `Result` is also
the semantic carrier for an arbitrary certified declaration image. -/
def asReaddressResult (result : Result) : Readdress.Result :=
  { source := result.declarations
    generated := []
    main := result.main
    addressMap := result.addressMap }

def blocks (result : Result) : List MutualBlock.Result :=
  result.artifacts.filterMap fun
    | .stable _ _ => none
    | .ordinary _ _ => none
    | .mutual block => some block

def ordinary (result : Result) : List (Address × Decl) :=
  result.artifacts.filterMap fun
    | .stable _ _ => none
    | .ordinary address declaration => some (address, declaration)
    | .mutual _ => none

def stable (result : Result) : List (Address × Decl) :=
  result.artifacts.filterMap fun
    | .stable address declaration => some (address, declaration)
    | .ordinary _ _ | .mutual _ => none

def blockAddresses (result : Result) : List Address :=
  result.blocks.map (·.blockAddress)

def transientAddresses (result : Result) : List Address :=
  (result.addressMap.filter fun entry => entry.1 != entry.2).map (·.1)

def finalAddresses (result : Result) : List Address :=
  result.declarations.map (·.1)

def noTransientKeys (result : Result) : Bool :=
  !result.finalAddresses.any result.transientAddresses.contains

def noTransientReferences (result : Result) : Bool :=
  let references := result.declarations.flatMap fun entry =>
    Readdress.Decl.references entry.2
  !(references ++ Readdress.Code.references result.main).any
    result.transientAddresses.contains

def contentAddressed (result : Result) : Bool :=
  result.artifacts.all Artifact.contentAddressed

def protectsReserved (result : Result) : Bool :=
  result.reserved.all fun address =>
    Readdress.Renaming.apply result.addressMap address == address

def mappingComplete (result : Result)
    (raw : List (Address × Decl)) : Bool :=
  result.addressMap.length == raw.length &&
    raw.all fun entry => result.addressMap.contains entry.1

/-- Total address action used to transport an already-addressed graph without
adding semantic aliases to its source environment.  Existing producer keys
move forward.  A newly emitted key that was not already a producer key moves
back to one of its old (now unoccupied) producer spellings; every other
address stays fixed. -/
def rebuildRename (result : Result)
    (raw : List (Address × Decl)) (address : Address) : Address :=
  match Env.ofList raw address with
  | some _ => Readdress.Renaming.apply result.addressMap address
  | none =>
      match result.addressMap.find? fun entry => entry.2 == address with
      | some entry => entry.1
      | none => address

/-- Executable whole-program certificate.  It checks the exact declaration
and main-code address image, fixed-point stability of every emitted lookup,
canonical ordinary/block identities, complete provenance, and absence of the
transient namespace. -/
def semanticAudit (result : Result)
    (raw : List (Address × Decl)) (rawMain : Code) : Bool :=
  result.asReaddressResult.semanticAudit raw rawMain &&
    (result.protectsReserved && result.mappingComplete raw &&
      result.contentAddressed && allUnique result.finalAddresses &&
      result.noTransientKeys && result.noTransientReferences)

/-- Executable exact-source audit for rebuilding an already-addressed graph.
Besides the ordinary content-address image audit, it checks that
`rebuildRename` maps the main and every raw row to the emitted graph, that
reverse-image keys land in holes of the emitted environment, and that every
emitted declaration has a producer preimage.  Those finite checks eliminate
the alias context needed by generic total readdressing. -/
def rebuildSemanticAudit (result : Result)
    (raw : List (Address × Decl)) (rawMain : Code) : Bool :=
  let rename := result.rebuildRename raw
  let emitted := Env.ofList result.declarations
  let original := Env.ofList raw
  result.semanticAudit raw rawMain &&
    Readdress.Code.structurallyEq result.main
      (Readdress.Code.mapAddresses rename rawMain) &&
    raw.all (fun entry =>
      match original entry.1, emitted (rename entry.1) with
      | some before, some after =>
          Readdress.Decl.structurallyEq before entry.2 &&
            Readdress.Decl.structurallyEq after
              (Readdress.Decl.mapAddresses rename before)
      | _, _ => false) &&
    result.addressMap.all (fun entry =>
      (match original entry.2 with
       | some _ => true
       | none => (emitted entry.1).isNone) &&
      match original entry.1 with
      | some _ => result.rebuildRename raw entry.1 == entry.2
      | none => false) &&
    result.declarations.all (fun entry =>
      result.addressMap.any fun mapping => mapping.2 == entry.1)

/-- The whole-program audit contains the exact generic semantic image audit
consumed by evaluator equivariance. -/
theorem semanticAudit_asReaddressResult {result : Result}
    {raw : List (Address × Decl)} {rawMain : Code}
    (haudit : result.semanticAudit raw rawMain = true) :
    result.asReaddressResult.semanticAudit raw rawMain = true := by
  simp only [semanticAudit, Bool.and_eq_true] at haudit
  exact haudit.1

theorem protectsReserved_of_semanticAudit {result : Result}
    {raw : List (Address × Decl)} {rawMain : Code}
    (haudit : result.semanticAudit raw rawMain = true) :
    result.protectsReserved = true := by
  simp only [semanticAudit, Bool.and_eq_true] at haudit
  exact haudit.2.1.1.1.1.1

/-- Pointwise constructor/reserved-identity stability exposed by the audited
artifact. -/
theorem apply_reserved {result : Result}
    {raw : List (Address × Decl)} {rawMain : Code}
    (haudit : result.semanticAudit raw rawMain = true)
    {address : Address} (haddress : address ∈ result.reserved) :
    Readdress.Renaming.apply result.addressMap address = address := by
  have hfixed := (List.all_eq_true.mp
    (result.protectsReserved_of_semanticAudit haudit)) address haddress
  exact Address.eq_of_beq hfixed

end Result

abbrev CertifiedResult (reserved : List Address)
    (raw : List (Address × Decl)) (rawMain : Code) :=
  { result : Result //
    result.semanticAudit raw rawMain = true ∧ result.reserved = reserved ∧
      result.rebuildSemanticAudit raw rawMain = true }

/-- A rebuilt graph additionally certifies transport from the exact old-keyed
source environment, rather than only from the generic alias-bearing one. -/
abbrev RebuildCertifiedResult (reserved : List Address)
    (raw : List (Address × Decl)) (rawMain : Code) :=
  { result : Result //
    result.semanticAudit raw rawMain = true ∧ result.reserved = reserved ∧
      result.rebuildSemanticAudit raw rawMain = true }

/-! ## Dependency-ordered construction -/

private def firstDuplicate? : List Address → Option Address
  | [] => none
  | address :: rest =>
      if rest.contains address then some address else firstDuplicate? rest

private def firstOverlap? (left right : List Address) : Option Address :=
  left.find? right.contains

private def externalReferences (keys : List Address)
    (raw : List (Address × Decl)) (main : Code) : List Address :=
  let references := raw.flatMap (fun entry =>
      Readdress.Decl.references entry.2) ++ Readdress.Code.references main
  references.filter fun address => !keys.contains address

private def stableExternKeys (raw : List (Address × Decl)) : List Address :=
  raw.filterMap fun
    | (address, .extern _) => some address
    | _ => none

private structure BuildState where
  addressMap : Renaming := []
  /-- Reverse dependency order while building. -/
  artifactsRev : List Artifact := []

namespace BuildState

def declarationKeys (state : BuildState) : List Address :=
  state.artifactsRev.flatMap fun artifact =>
    (Artifact.declarations artifact).map (·.1)

def blockAddresses (state : BuildState) : List Address :=
  state.artifactsRev.filterMap fun
    | .stable _ _ => none
    | .ordinary _ _ => none
    | .mutual block => some block.blockAddress

def usedIdentities (state : BuildState) : List Address :=
  state.artifactsRev.flatMap Artifact.identities

def findOrdinary? (state : BuildState) (address : Address) : Option Decl :=
  let rec loop : List Artifact → Option Decl
    | [] => none
    | .stable _ _ :: rest => loop rest
    | .ordinary found declaration :: rest =>
        if found == address then some declaration else loop rest
    | .mutual _ :: rest => loop rest
  loop state.artifactsRev

def findBlock? (state : BuildState)
    (address : Address) : Option MutualBlock.Result :=
  let rec loop : List Artifact → Option MutualBlock.Result
    | [] => none
    | .stable _ _ :: rest => loop rest
    | .ordinary _ _ :: rest => loop rest
    | .mutual block :: rest =>
        if block.blockAddress == address then some block else loop rest
  loop state.artifactsRev

end BuildState

private def samePreimage (left right : Decl) : Bool :=
  left.preimage == right.preimage

private def appendMap (state : BuildState) (mapping : Renaming) : BuildState :=
  { state with addressMap := state.addressMap ++ mapping }

/-- Preserve an opaque extern ABI identity.  Its declaration bytes encode
only arity and therefore cannot independently identify the oracle ledger. -/
private def installStable (old : Address) (declaration : Decl)
    (state : BuildState) : Except String BuildState :=
  match declaration with
  | .extern _ =>
      .ok
        { addressMap := state.addressMap ++ [(old, old)]
          artifactsRev := .stable old declaration :: state.artifactsRev }
  | _ => .error "internal: non-extern declaration reached stable installation"

/-- Hash and install one acyclic singleton. -/
private def installOrdinary (keys protectedIdentities : List Address)
    (old : Address) (rawDeclaration : Decl)
    (state : BuildState) : Except String BuildState := do
  let declaration := Readdress.Decl.mapAddresses
    (Readdress.Renaming.apply state.addressMap) rawDeclaration
  let address := declaration.address
  if keys.contains address then
    throw s!"IxIR1 content address overlaps transient namespace {Address.toHex address}"
  if protectedIdentities.contains address then
    throw s!"IxIR1 content address collides with protected identity {Address.toHex address}"
  match state.findOrdinary? address with
  | some found =>
      if samePreimage found declaration then
        return appendMap state [(old, address)]
      else
        throw s!"BLAKE3 collision while readdressing IxIR1 declaration {Address.toHex old}"
  | none =>
      if state.usedIdentities.contains address then
        .error s!"IxIR1 declaration address collides with a mutual-block identity {Address.toHex address}"
      else
        .ok
          { addressMap := state.addressMap ++ [(old, address)]
            artifactsRev := .ordinary address declaration :: state.artifactsRev }

/-- Build or exact-content-deduplicate one cyclic component. -/
private def installMutual (keys protectedIdentities : List Address)
    (component : Component) (state : BuildState) : Except String BuildState := do
  let localKeys := component.keys
  let rename := Readdress.Renaming.apply state.addressMap
  let rewritten := component.members.map fun entry =>
    (entry.1, Readdress.Decl.mapAddresses rename entry.2)
  /- Protect every other producer key here.  The one-block constructor already
  protects this component's own transient keys and all of its external edges. -/
  let otherTransient := keys.filter fun address => !localKeys.contains address
  let candidate ← MutualBlock.run
    (protectedIdentities ++ otherTransient) rewritten
  match state.findBlock? candidate.blockAddress with
  | some existing =>
      if MutualBlock.DeclList.structurallyEq
          existing.blockMembers candidate.blockMembers then
        if existing.derivedAddresses == candidate.derivedAddresses then
          return appendMap state candidate.addressMap
        else
          throw "internal: equal IxIR1 mutual blocks derived different member keys"
      else
        throw s!"BLAKE3 collision between IxIR1 mutual blocks {Address.toHex candidate.blockAddress}"
  | none =>
      if state.usedIdentities.contains candidate.blockAddress then
        .error s!"IxIR1 mutual-block identity collides with an emitted identity {Address.toHex candidate.blockAddress}"
      else
        match firstOverlap? candidate.derivedAddresses
            state.usedIdentities with
        | some overlap =>
            .error s!"IxIR1 mutual-block member key collides with an emitted identity {Address.toHex overlap}"
        | none =>
            .ok
              { addressMap := state.addressMap ++ candidate.addressMap
                artifactsRev := .mutual candidate :: state.artifactsRev }

private def installComponent (keys protectedIdentities : List Address)
    (component : Component) (state : BuildState) : Except String BuildState :=
  if component.cyclic then
    installMutual keys protectedIdentities component state
  else
    match component.members with
    | [(old, declaration@(.extern _))] =>
        installStable old declaration state
    | [(old, declaration)] =>
        installOrdinary keys protectedIdentities old declaration state
    | _ => .error "internal: non-cyclic IxIR1 SCC was not a singleton"

private def build (keys protectedIdentities : List Address) :
    List Component → BuildState → Except String BuildState
  | [], state => .ok state
  | component :: rest, state => do
      let state ← installComponent keys protectedIdentities component state
      build keys protectedIdentities rest state

private def certify (reserved : List Address)
    (raw : List (Address × Decl)) (rawMain : Code)
    (result : Result) : Except String (CertifiedResult reserved raw rawMain) :=
  if haudit : result.semanticAudit raw rawMain then
    if hreserved : result.reserved = reserved then
      if hexact : result.rebuildSemanticAudit raw rawMain then
        .ok ⟨result, haudit, hreserved, hexact⟩
      else
        .error "internal: whole-program IxIR1 readdressing failed exact-source semantic audit"
    else
      .error "internal: whole-program IxIR1 readdressing retained the wrong reserved identities"
  else
    .error "internal: whole-program IxIR1 readdressing failed semantic audit"

/-- Discover, dependency-order, and content-address a complete flat IxIR₁
environment.  `reserved` contains caller-owned identities that are not
declaration producer keys (notably constructor/oracle identities). -/
def runCertified (reserved : List Address)
    (raw : List (Address × Decl)) (main : Code) :
    Except String (CertifiedResult reserved raw main) := do
  let keys := raw.map (·.1)
  if let some duplicate := firstDuplicate? keys then
    throw s!"duplicate IxIR1 declaration producer key {Address.toHex duplicate}"
  if let some overlap := firstOverlap? keys reserved then
    throw s!"IxIR1 declaration producer key overlaps reserved identity {Address.toHex overlap}"
  let protectedIdentities :=
    reserved ++ stableExternKeys raw ++ externalReferences keys raw main
  let components := discoverComponentsDependencyFirst raw
  let state ← build keys protectedIdentities components {}
  let result : Result :=
    { artifacts := state.artifactsRev.reverse
      main := Readdress.Code.mapAddresses
        (Readdress.Renaming.apply state.addressMap) main
      addressMap := state.addressMap
      reserved }
  unless result.mappingComplete raw do
    throw "internal: whole-program IxIR1 readdressing produced an incomplete map"
  unless result.noTransientKeys do
    throw "internal: whole-program IxIR1 readdressing emitted a transient key"
  unless result.noTransientReferences do
    throw "internal: whole-program IxIR1 readdressing left a transient reference"
  unless result.protectsReserved do
    throw "internal: whole-program IxIR1 readdressing rewrote a reserved identity"
  certify reserved raw main result

def run (reserved : List Address)
    (raw : List (Address × Decl)) (main : Code) : Except String Result := do
  return (← runCertified reserved raw main).1

/-! ## Rebuilding an already-addressed graph -/

/-- Domain-separated temporary producer name used only while rebuilding an
already-content-addressed graph.  It cannot escape: `rebuildCertified`
re-certifies the final artifact against the caller's original keys. -/
def rebuildTemporaryAddress (address : Address) : Address :=
  Address.blake3
    (IxIR.Encoding.domain "compilatrix/ixir1/rebuild-temporary/1" ++
      IxIR.Encoding.address address)

/-- Existing extern keys are stable ABI identities; function keys receive a
temporary producer spelling before the ordinary SCC pass runs again. -/
def rebuildTemporaryRenaming (raw : List (Address × Decl)) : Renaming :=
  raw.map fun entry =>
    match entry.2 with
    | .fn _ => (entry.1, rebuildTemporaryAddress entry.1)
    | .extern _ => (entry.1, entry.1)

private def rebuildTemporaryKeys
    (raw : List (Address × Decl)) : List Address :=
  raw.filterMap fun entry =>
    match entry.2 with
    | .fn _ => some (rebuildTemporaryAddress entry.1)
    | .extern _ => none

private def composeRebuildMap (raw : List (Address × Decl))
    (temporary final : Renaming) : Renaming :=
  raw.map fun entry =>
    (entry.1, Readdress.Renaming.apply final
      (Readdress.Renaming.apply temporary entry.1))

/-- Rebuild a graph whose current keys may already be its declaration or
mutual-block content addresses.  The ordinary producer rejects output keys in
its transient namespace, so this adapter first alpha-renames function
producers into a domain-separated temporary namespace.  Extern identities and
all caller-owned/external identities remain fixed.  The returned result is
then certified directly against the original graph; neither a temporary key
nor the intermediate address map is exposed. -/
def rebuildCertified (reserved : List Address)
    (raw : List (Address × Decl)) (main : Code) :
    Except String (RebuildCertifiedResult reserved raw main) := do
  let keys := raw.map (·.1)
  if let some duplicate := firstDuplicate? keys then
    throw s!"duplicate IxIR1 declaration key while rebuilding {Address.toHex duplicate}"
  let temporaryKeys := rebuildTemporaryKeys raw
  let protectedIdentities :=
    keys ++ reserved ++ externalReferences keys raw main
  if let some overlap := firstOverlap? temporaryKeys protectedIdentities then
    throw s!"IxIR1 rebuild temporary address collides with an existing identity {Address.toHex overlap}"
  if let some duplicate := firstDuplicate? temporaryKeys then
    throw s!"BLAKE3 collision between IxIR1 rebuild temporary addresses {Address.toHex duplicate}"
  let temporary := rebuildTemporaryRenaming raw
  let rename := Readdress.Renaming.apply temporary
  let temporaryRaw := raw.map fun entry =>
    (rename entry.1, Readdress.Decl.mapAddresses rename entry.2)
  let temporaryMain := Readdress.Code.mapAddresses rename main
  let intermediate ← runCertified reserved temporaryRaw temporaryMain
  let result : Result :=
    { intermediate.1 with
      addressMap := composeRebuildMap raw temporary
        intermediate.1.addressMap
      reserved }
  if haudit : result.semanticAudit raw main then
    if hreserved : result.reserved = reserved then
      if hexact : result.rebuildSemanticAudit raw main then
        return ⟨result, haudit, hreserved, hexact⟩
      else
        throw "internal: IxIR1 rebuild failed exact-source semantic audit"
    else
      throw "internal: IxIR1 rebuild retained the wrong reserved identities"
  else
    throw "internal: IxIR1 rebuild failed semantic audit"

/-- Unbundled already-addressed graph rebuild. -/
def rebuild (reserved : List Address)
    (raw : List (Address × Decl)) (main : Code) : Except String Result := do
  return (← rebuildCertified reserved raw main).1

theorem semanticAudit_of_rebuild_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result} (hrebuild : rebuild reserved raw main = .ok result) :
    result.semanticAudit raw main = true := by
  unfold rebuild at hrebuild
  cases hcertified : rebuildCertified reserved raw main with
  | error message =>
      rw [hcertified] at hrebuild
      contradiction
  | ok certified =>
      rw [hcertified] at hrebuild
      have hvalue : certified.1 = result := by injection hrebuild
      subst result
      exact certified.2.1

theorem reserved_of_rebuild_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result} (hrebuild : rebuild reserved raw main = .ok result) :
    result.reserved = reserved := by
  unfold rebuild at hrebuild
  cases hcertified : rebuildCertified reserved raw main with
  | error message =>
      rw [hcertified] at hrebuild
      contradiction
  | ok certified =>
      rw [hcertified] at hrebuild
      have hvalue : certified.1 = result := by injection hrebuild
      subst result
      exact certified.2.2.1

theorem rebuildSemanticAudit_of_rebuild_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result} (hrebuild : rebuild reserved raw main = .ok result) :
    result.rebuildSemanticAudit raw main = true := by
  unfold rebuild at hrebuild
  cases hcertified : rebuildCertified reserved raw main with
  | error message =>
      rw [hcertified] at hrebuild
      contradiction
  | ok certified =>
      rw [hcertified] at hrebuild
      have hvalue : certified.1 = result := by injection hrebuild
      subst result
      exact certified.2.2.2

theorem semanticAudit_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result} (hrun : run reserved raw main = .ok result) :
    result.semanticAudit raw main = true := by
  unfold run at hrun
  cases hcertified : runCertified reserved raw main with
  | error message =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2.1

theorem reserved_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result} (hrun : run reserved raw main = .ok result) :
    result.reserved = reserved := by
  unfold run at hrun
  cases hcertified : runCertified reserved raw main with
  | error message =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2.2.1

/-- Every successful ordinary SCC pass supports transport from the exact raw
declaration environment, without installing aliases at newly emitted content
keys. -/
theorem rebuildSemanticAudit_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result} (hrun : run reserved raw main = .ok result) :
    result.rebuildSemanticAudit raw main = true := by
  unfold run at hrun
  cases hcertified : runCertified reserved raw main with
  | error message =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2.2.2

theorem protectsReserved_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result} (hrun : run reserved raw main = .ok result) :
    result.protectsReserved = true :=
  Result.protectsReserved_of_semanticAudit
    (semanticAudit_of_run_eq_ok hrun)

/-! Pure SCC/dispatch guards.  Digest behavior is exercised by the compiled
test executable. -/

private def fixtureA : Address := Address.replicate 0xa1
private def fixtureB : Address := Address.replicate 0xa2
private def fixtureC : Address := Address.replicate 0xa3
private def fixtureD : Address := Address.replicate 0xa4

private def fixtureRaw : List (Address × Decl) :=
  [(fixtureA, .fn ⟨1, .shared, true,
      .letOp (.call fixtureB #[.var 0]) (.ret (.var 0))⟩),
   (fixtureB, .fn ⟨0, .shared, true,
      .letOp (.papp fixtureA #[]) (.ret .erased)⟩),
   (fixtureC, .fn ⟨0, .shared, true,
      .letOp (.call fixtureA #[]) (.ret .erased)⟩),
   (fixtureD, .extern 0)]

#guard (discoverComponents fixtureRaw).map Component.keys ==
  [[fixtureA, fixtureB], [fixtureC], [fixtureD]]
#guard (discoverComponents
  [(fixtureA, .fn ⟨0, .shared, true,
      .letOp (.call fixtureA #[]) (.ret .erased)⟩)]).all Component.cyclic
#guard !(discoverComponents
  [(fixtureA, .fn ⟨0, .shared, true,
      .letOp (.callSelf #[]) (.ret .erased)⟩)]).any Component.cyclic

end ReaddressAll

end Ix.Compiler.IxIR1
