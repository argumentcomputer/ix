import Ix.Compiler.IxIR0.MutualBlock

/-!
# Whole-program IxIR₀ mutual-block readdressing

`MutualBlock.run` handles one strongly connected declaration block.  This
module lifts that operation to an entire erased program: stable declarations
and the main expression are rewritten through the union of every block map,
while cross-block temporary edges and all global namespace captures fail
closed.

The pass deliberately leaves the existing erasure theorem boundary intact.
That boundary may continue to produce transient `memberAddr` keys; a later
evaluator-renaming theorem can transport its result through the certified map
returned here.
-/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon (Address)

namespace Readdress

/-- One ordered erasure-output group. Stable groups retain their keys; mutual
groups are addressed as a complete local-edge artifact. -/
inductive Group where
  | stable (entries : List (Address × Decl))
  | mutual (entries : List (Address × Decl))
  deriving Repr

namespace Group

def entries : Group → List (Address × Decl)
  | .stable entries | .mutual entries => entries

def mutualEntries? : Group → Option (List (Address × Decl))
  | .stable _ => none
  | .mutual entries => some entries

end Group

/-- Flatten groups in producer order. -/
def rawDeclarations (groups : List Group) : List (Address × Decl) :=
  groups.flatMap Group.entries

/-- Ordered mutual-block inputs in producer order. -/
def rawBlocks (groups : List Group) : List (List (Address × Decl)) :=
  groups.filterMap Group.mutualEntries?

/-- All stable environment keys. -/
def stableKeys (groups : List Group) : List Address :=
  groups.flatMap fun group =>
    match group with
    | .stable entries => entries.map (·.1)
    | .mutual _ => []

/-- Every transient mutual-member key. -/
def transientKeys (groups : List Group) : List Address :=
  groups.flatMap fun group =>
    match group with
    | .stable _ => []
    | .mutual entries => entries.map (·.1)

namespace Renaming

/-- First source key whose recorded image is `address`.  Readdressing is not
globally invertible; this operation is deliberately restricted to resolving a
called final producer key back to its legacy name. -/
def reverseLookup (mapping : MutualBlock.Renaming)
    (address : Address) : Option Address :=
  (List.find? (fun entry => entry.2 == address) mapping).map (·.1)

/-- Reverse a recorded image key, leaving every other key unchanged. -/
def reverseApply (mapping : MutualBlock.Renaming) (address : Address) : Address :=
  (reverseLookup mapping address).getD address

/-- An identity is absent from both the producer and image sides of a map.
This is stronger than merely being a fixed point and is the namespace fact
needed by a key-sensitive oracle adapter. -/
def isolates (mapping : MutualBlock.Renaming) (address : Address) : Bool :=
  mapping.all fun entry => entry.1 != address && entry.2 != address

end Renaming

/-- Concrete references in the raw program which are not transient member
edges. Stable declarations may refer to transient members and are rewritten;
inside a mutual block, own-member edges are local while another block's
temporary key is rejected separately. -/
def externalReferences (groups : List Group) (main : Expr) : List Address :=
  let transient := transientKeys groups
  ((rawDeclarations groups).flatMap (fun entry =>
      MutualBlock.Concrete.Decl.references entry.2) ++
    MutualBlock.Concrete.Expr.references main).filter fun address =>
        !transient.contains address

/-- Identities whose external meaning must not be captured by either side of
the member-address map. -/
def oracleIdentities (reserved : List Address) (groups : List Group)
    (main : Expr) : List Address :=
  reserved ++ stableKeys groups ++ externalReferences groups main

/-- Result of addressing every mutual block and applying their combined map
to the complete program. -/
structure Result where
  declarations : List (Address × Decl)
  main : Expr
  blocks : List MutualBlock.Result
  addressMap : MutualBlock.Renaming

namespace Result

def transientAddresses (result : Result) : List Address :=
  result.addressMap.map (·.1)

def derivedAddresses (result : Result) : List Address :=
  result.addressMap.map (·.2)

def blockAddresses (result : Result) : List Address :=
  result.blocks.map (·.blockAddress)

def noTransientKeys (result : Result) : Bool :=
  !(result.declarations.map (·.1)).any result.transientAddresses.contains

def noTransientReferences (result : Result) : Bool :=
  let declarationReferences := result.declarations.flatMap fun entry =>
    MutualBlock.Concrete.Decl.references entry.2
  !(declarationReferences ++
      MutualBlock.Concrete.Expr.references result.main).any
    result.transientAddresses.contains

private def blockAudits :
    List MutualBlock.Result → List (List (Address × Decl)) → Bool
  | [], [] => true
  | result :: results, raw :: raws =>
      result.semanticAudit raw && blockAudits results raws
  | _, _ => false

/-- Every block result retains its own producer audit. -/
def blocksAudited (result : Result) (groups : List Group) : Bool :=
  blockAudits result.blocks (rawBlocks groups)

/-- Every caller-protected identity is fixed by the completed map. -/
def protects (result : Result) (reserved : List Address) : Bool :=
  reserved.all fun address =>
    MutualBlock.Renaming.apply result.addressMap address == address

/-- Stable, caller-owned, and externally referenced identities occur on
neither side of the member renaming.  In particular, reverse oracle dispatch
cannot mistake a final member key for an opaque ABI key. -/
def oracleIdentityAudit (result : Result) (reserved : List Address)
    (groups : List Group) (main : Expr) : Bool :=
  (oracleIdentities reserved groups main).all fun address =>
    Renaming.isolates result.addressMap address

/-- Exact list/main image under the completed address map. -/
def imageAudit (result : Result) (groups : List Group)
    (rawMain : Expr) : Bool :=
  let rename := MutualBlock.Renaming.apply result.addressMap
  result.declarations ==
      (rawDeclarations groups).map (fun entry =>
        (rename entry.1,
          MutualBlock.Concrete.Decl.mapAddresses rename entry.2)) &&
    result.main == MutualBlock.Concrete.Expr.mapAddresses rename rawMain

/-- Every emitted declaration row is the row selected by the transparent
first-binding-wins environment.  This makes producer-key collision freedom
available to proof clients without re-running the private collision check. -/
def declarationRowsSelected (result : Result) : Bool :=
  result.declarations.all fun entry =>
    match Env.ofList result.declarations entry.1 with
    | some declaration => declaration == entry.2
    | none => false

/-- Global block, namespace, and fixed-point checks. -/
def safetyAudit (result : Result) (reserved : List Address)
    (groups : List Group) (rawMain : Expr) : Bool :=
  let rename := MutualBlock.Renaming.apply result.addressMap
  result.blocksAudited groups && result.protects reserved &&
    result.noTransientKeys && result.noTransientReferences &&
    result.declarations.all (fun entry =>
      MutualBlock.Concrete.Decl.mapAddresses rename entry.2 == entry.2) &&
    result.oracleIdentityAudit reserved groups rawMain &&
    result.declarationRowsSelected

/-- Exact forward environment lookup check. -/
def lookupAudit (result : Result) (groups : List Group) : Bool :=
  let rename := MutualBlock.Renaming.apply result.addressMap
  let original := Env.ofList (rawDeclarations groups)
  let emitted := Env.ofList result.declarations
  (rawDeclarations groups).all (fun entry =>
    match original entry.1, emitted (rename entry.1) with
    | some before, some after =>
        after == MutualBlock.Concrete.Decl.mapAddresses rename before
    | _, _ => false)

/-- Every successful emitted lookup is stable under the completed map. -/
def stableLookupAudit (result : Result) : Bool :=
  let rename := MutualBlock.Renaming.apply result.addressMap
  let emitted := Env.ofList result.declarations
  result.declarations.all (fun entry =>
    match emitted entry.1 with
    | some declaration =>
        MutualBlock.Concrete.Decl.mapAddresses rename declaration ==
          declaration
    | none => false)

/-- Exact structural audit for the whole address image. -/
def semanticAudit (result : Result) (reserved : List Address)
    (groups : List Group) (rawMain : Expr) : Bool :=
  result.imageAudit groups rawMain &&
    result.safetyAudit reserved groups rawMain &&
    result.lookupAudit groups && result.stableLookupAudit

/-- Extract the bidirectional oracle-identity namespace certificate from the
whole-program audit. -/
theorem oracleIdentityAudit_of_semanticAudit {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true) :
    result.oracleIdentityAudit reserved groups main = true := by
  simp only [semanticAudit, Bool.and_eq_true] at haudit
  have hsafety : result.safetyAudit reserved groups main = true :=
    haudit.1.1.2
  simp only [safetyAudit, Bool.and_eq_true] at hsafety
  exact hsafety.1.2

/-- Pointwise producer-key selection exposed by the whole-program audit. -/
theorem declaration_lookup_of_mem_of_semanticAudit {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    {address : Address} {declaration : Decl}
    (hmember : (address, declaration) ∈ result.declarations) :
    Env.ofList result.declarations address = some declaration := by
  simp only [semanticAudit, Bool.and_eq_true] at haudit
  have hsafety : result.safetyAudit reserved groups main = true :=
    haudit.1.1.2
  simp only [safetyAudit, Bool.and_eq_true] at hsafety
  have hrows : result.declarationRowsSelected = true := hsafety.2
  simp only [declarationRowsSelected] at hrows
  have hrow := (List.all_eq_true.mp hrows)
    (address, declaration) hmember
  cases hlookup : Env.ofList result.declarations address with
  | none => simp [hlookup] at hrow
  | some selected =>
      have hselected : selected = declaration :=
        (beq_iff_eq).mp (by simpa [hlookup] using hrow)
      simpa [hlookup, hselected]

/-- Pointwise form consumed by concrete key-sensitive oracle proofs. -/
theorem addressMap_isolates_of_semanticAudit {result : Result}
    {reserved : List Address} {groups : List Group} {main : Expr}
    (haudit : result.semanticAudit reserved groups main = true)
    {address : Address}
    (haddress : address ∈ oracleIdentities reserved groups main) :
    Renaming.isolates result.addressMap address = true :=
  (List.all_eq_true.mp
    (result.oracleIdentityAudit_of_semanticAudit haudit)) address haddress

end Result

/-- A successful program readdressing carries its runtime-erased audit. -/
abbrev CertifiedResult (reserved : List Address) (groups : List Group)
    (main : Expr) :=
  { result : Result // result.semanticAudit reserved groups main = true }

private def firstDuplicate? : List Address → Option Address
  | [] => none
  | address :: rest =>
      if rest.contains address then some address else firstDuplicate? rest

private def firstOverlap? (left right : List Address) : Option Address :=
  left.find? right.contains

/-- Previously produced identities may be reused only by the same complete
symbolic and materialized artifact. Producer names deliberately do not enter
this comparison: each producer retains its independently audited map. A block
identity can never stand for a member, and members of different blocks cannot
alias even when their materialized declarations happen to agree. -/
def compatibleBlocks (left right : MutualBlock.Result) : Bool :=
  !left.derivedAddresses.contains right.blockAddress &&
    !right.derivedAddresses.contains left.blockAddress &&
    if left.blockAddress == right.blockAddress then
      left.blockMembers == right.blockMembers &&
        left.members == right.members &&
        left.derivedAddresses == right.derivedAddresses
    else
      !left.derivedAddresses.any right.derivedAddresses.contains

/-- Reusing a block identity requires equal symbolic preimages, without any
assumption that the hash function is injective. -/
theorem blockMembers_eq_of_compatibleBlocks
    {left right : MutualBlock.Result}
    (hcompatible : compatibleBlocks left right = true)
    (haddress : left.blockAddress = right.blockAddress) :
    left.blockMembers = right.blockMembers := by
  simp only [compatibleBlocks, haddress, beq_self_eq_true, ite_true,
    Bool.and_eq_true] at hcompatible
  exact (beq_iff_eq).mp hcompatible.2.1.1

/-- Reuse also preserves the complete ordered member environment. -/
theorem members_eq_of_compatibleBlocks
    {left right : MutualBlock.Result}
    (hcompatible : compatibleBlocks left right = true)
    (haddress : left.blockAddress = right.blockAddress) :
    left.members = right.members := by
  simp only [compatibleBlocks, haddress, beq_self_eq_true, ite_true,
    Bool.and_eq_true] at hcompatible
  exact (beq_iff_eq).mp hcompatible.2.1.2

private structure BuildState where
  blocks : List MutualBlock.Result := []
  addressMap : MutualBlock.Renaming := []

private def buildBlocks (baseProtected allTransient : List Address) :
    List Group → BuildState → Except String BuildState
  | [], state => .ok state
  | .stable _ :: rest, state =>
      buildBlocks baseProtected allTransient rest state
  | .mutual raw :: rest, state => do
      let ownTransient := raw.map (·.1)
      let otherTransient := allTransient.filter fun address =>
        !ownTransient.contains address
      let protectedKeys := baseProtected ++ otherTransient
      let result ← MutualBlock.run protectedKeys raw
      unless state.blocks.all (compatibleBlocks · result) do
        throw s!"conflicting generated mutual-block or member identity {Address.toHex result.blockAddress}"
      buildBlocks baseProtected allTransient rest
        { blocks := state.blocks ++ [result]
          addressMap := state.addressMap ++ result.addressMap }

private def crossBlockTemporary? (allTransient : List Address) :
    List Group → Option Address
  | [] => none
  | .stable _ :: rest => crossBlockTemporary? allTransient rest
  | .mutual raw :: rest =>
      let external := (MutualBlock.abstractMembers raw).flatMap
        MutualBlock.Decl.externalReferences
      match external.find? allTransient.contains with
      | some address => some address
      | none => crossBlockTemporary? allTransient rest

private def certify (reserved : List Address) (groups : List Group)
    (main : Expr) (result : Result) :
    Except String (CertifiedResult reserved groups main) :=
  if haudit : result.semanticAudit reserved groups main then
    .ok ⟨result, haudit⟩
  else
    .error "internal: whole-program IxIR0 readdressing failed semantic audit"

/-- Address every mutual group, union the maps, and rewrite the complete
program and main expression.

`reserved` is the caller-owned namespace not represented by stable group
keys—for erasure this includes every source constant address, notably the
Ixon address of each mutual block itself. -/
def runCertified (reserved : List Address) (groups : List Group)
    (main : Expr) : Except String (CertifiedResult reserved groups main) := do
  let declarations := rawDeclarations groups
  let allKeys := declarations.map (·.1)
  if let some duplicate := firstDuplicate? allKeys then
    throw s!"duplicate raw IxIR0 declaration key {Address.toHex duplicate}"
  let transient := transientKeys groups
  let stable := stableKeys groups
  let baseProtected := reserved ++ stable
  if let some overlap := firstOverlap? transient baseProtected then
    throw s!"mutual-block temporary address overlaps stable or reserved identity {Address.toHex overlap}"
  if let some cross := crossBlockTemporary? transient groups then
    throw s!"cross-block reference uses another mutual block's temporary address {Address.toHex cross}"
  let state ← buildBlocks baseProtected transient groups {}
  let derived := state.addressMap.map (·.2)
  let blockAddresses := state.blocks.map (·.blockAddress)
  let external := externalReferences groups main
  if let some overlap := firstOverlap? derived external then
    throw s!"derived mutual-member key captures a program external reference {Address.toHex overlap}"
  if let some overlap := firstOverlap? blockAddresses external then
    throw s!"mutual-block identity captures a program external reference {Address.toHex overlap}"
  let rename := MutualBlock.Renaming.apply state.addressMap
  let result : Result :=
    { declarations := declarations.map fun entry =>
        (rename entry.1,
          MutualBlock.Concrete.Decl.mapAddresses rename entry.2)
      main := MutualBlock.Concrete.Expr.mapAddresses rename main
      blocks := state.blocks
      addressMap := state.addressMap }
  certify reserved groups main result

/-- Artifact-facing projection of `runCertified`. -/
def run (reserved : List Address) (groups : List Group)
    (main : Expr) : Except String Result := do
  return (← runCertified reserved groups main).1

/-- Every successful artifact-facing run retains the whole-program audit. -/
theorem semanticAudit_of_run_eq_ok
    {reserved : List Address} {groups : List Group} {main : Expr}
    {result : Result} (hrun : run reserved groups main = .ok result) :
    result.semanticAudit reserved groups main = true := by
  unfold run at hrun
  cases hcertified : runCertified reserved groups main with
  | error message =>
      rw [hcertified] at hrun
      contradiction
  | ok certified =>
      rw [hcertified] at hrun
      have hvalue : certified.1 = result := by injection hrun
      subst result
      exact certified.2

/-- Every protected/stable/external identity is absent from both sides of the
map returned by a successful pass. -/
theorem isolates_of_run_eq_ok
    {reserved : List Address} {groups : List Group} {main : Expr}
    {result : Result} (hrun : run reserved groups main = .ok result)
    {address : Address}
    (haddress : address ∈ oracleIdentities reserved groups main) :
    Renaming.isolates result.addressMap address = true :=
  result.addressMap_isolates_of_semanticAudit
    (semanticAudit_of_run_eq_ok hrun) haddress

end Readdress

end Ix.Compiler.IxIR0
