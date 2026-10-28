/-
  `ix aggregate --ixc` and `ix verify --aggregate --ixc`: join the aggregate
  roots of a `.ixc` catalog's members, which may come from different Lean
  toolchains and so carry different role bindings, into one root
  (`Aggr.catalogPlan`), and verify that root against the catalog.

  A member's statement is the unconditional `CheckEnv` claim its own
  aggregate root states (`ix aggregate --ixe --ixes --binding-proof`):
  validating the member's binding, over its piece's constants. It is the
  canonical claim of the piece (`ix verify --aggregate --ixe`), or, when the
  catalog directory holds `<label>.ixes` beside the piece, the claim of the
  aggregate of that shard manifest (`ix verify --aggregate --ixe --ixes`).
-/
module
public import Cli
public import Ix.Aggr
public import Ix.Aggr.Backend
public import Ix.Aggr.CatalogPlan
public import Ix.Aggr.Verification
public import Ix.Catalog
public import Ix.Cli.CatalogCmd
public import Ix.IxVM.ClaimHarness
public import Ix.Store
public import MultiStark

public section

namespace Ix.Cli.CatalogAggregate

open Aggr

/-- A catalog's members as the plan sees them, with each member's constant
count. The catalog must verify (`ix catalog verify`: a fat catalog whose
pieces match the manifest), and each piece must carry its role binding. -/
def catalogMembers (ixc : String) (structuralAbove : Nat) :
    IO (Except String (Array (CatalogMember × Ix.Catalog.Member × Nat))) := do
  try
    discard <| Ix.Cli.CatalogCmd.rsCatalogVerifyFFI ixc false
  catch e => return .error s!"{ixc}: {e}"
  let dir : System.FilePath := ixc
  let manifest ← match Ix.Catalog.de (← IO.FS.readBinFile (dir / "manifest")) with
    | .ok m => pure m
    | .error e => return .error s!"{ixc}: {e}"
  let mut out : Array (CatalogMember × Ix.Catalog.Member × Nat) := #[]
  for m in manifest.members do
    let piece := dir / s!"{m.label}.ixe"
    let env ← match Ixon.deEnvAnon (← IO.FS.readBinFile piece) with
      | .ok env => pure env
      | .error e => return .error s!"{piece}: {e}"
    let some binding := env.roleBinding
      | return .error s!"{piece}: the piece carries no role binding"
    unless binding.address == m.binding do
      return .error s!"{piece}: role binding {binding.address} is not the manifest's {m.binding}"
    let literalClass ← match Ix.ClaimContext.literalClassOfBytes binding.bytes with
      | .ok k => pure k
      | .error e => return .error s!"{piece}: {e}"
    let ixes := dir / s!"{m.label}.ixes"
    let (claim, count) ← if ← ixes.pathExists then
        let handle ← match ← IO.lazyPure fun _ => Aiur.EnvHandle.fromIxe piece.toString with
          | .ok handle => pure handle
          | .error e => return .error s!"{piece}: {e}"
        let expected ← match ← IO.lazyPure fun _ =>
            Aiur.AiurSystem.aggregateExpected handle ixes.toString structuralAbove with
          | .ok expected => pure expected
          | .error e => return .error s!"{ixes}: {e}"
        match Ix.Claim.de expected.claimBytes with
        | .ok claim => pure (claim, expected.constantCount)
        | .error e => return .error s!"{ixes}: the expected claim does not decode: {e}"
      else
        let some tree := IxVM.ClaimHarness.envCanonicalTree env
          | return .error s!"{piece}: the piece has no constants"
        let ctx ← match Ix.ClaimContext.ofEnv env with
          | .ok ctx => pure ctx
          | .error e => return .error s!"{piece}: {e}"
        let statement : CheckEnvTrees := { ctx, subjects := tree, assumptions := none }
        match auditAggregateConstants env statement with
        | .ok count => pure (statement.claim, count)
        | .error e => return .error s!"{piece}: {e}"
    let member : CatalogMember :=
      { label := m.label, toolchain := m.toolchain, claim, bindingSection := binding.bytes,
        literalClass }
    out := out.push (member, m, count)
  return .ok out

/-- The plan of a catalog's members, and its root claim. -/
def catalogRoot (members : Array CatalogMember) : Except String (CatalogPlan × Ix.Claim) := do
  let plan ← catalogPlan members
  return (plan, plan.statements[plan.root]!.claim)

/-- Print each member's statement and the root. -/
def printStatements (members : Array (CatalogMember × Ix.Catalog.Member × Nat))
    (plan : CatalogPlan) : IO Unit := do
  for (m, entry, count) in members do
    let .checkEnv ctx root _ := m.claim | continue
    IO.println s!"[catalog] member {m.label} (toolchain {m.toolchain}): {count} constants, \
      binding {entry.binding}, literal class {m.literalClass}, spec {ctx.spec}, \
      subjects {root}"
  for i in [0:plan.nodes.size] do
    match plan.nodes[i]! with
    | .crossBinding klass l r =>
      IO.println s!"[catalog] node {i}: nodes {l} and {r} under literal class {klass} \
        (cross-binding pair): {plan.statements[i]!.claim}"
    | .catalogJoin l r =>
      IO.println s!"[catalog] node {i}: nodes {l} and {r} (catalog join): \
        {plan.statements[i]!.claim}"
    | .member _ => pure ()
  IO.println s!"[catalog] root: {plan.statements[plan.root]!.claim}"

/-- A proven node: its claim, its `ix_aggr` proof and the address of its proof
wrapper in the store. -/
structure Proven where
  claim : Ix.Claim
  proof : Aiur.Proof
  address : Address

private def addressOfHex (hex : String) : Except String Address :=
  match Address.fromString hex with
  | some a => .ok a
  | none => .error s!"aggregate proof: expected a 64-character hex address, got {hex}"

/-- Read the aggregate proof wrapper at `address`. -/
def readProven (address : Address) : IO (Except String Proven) := do
  let bytes ← StoreIO.toIO (Store.read address)
  let wrapper ← match decodeAggregateWrapperAt address bytes with
    | .ok wrapper => pure wrapper
    | .error e => return .error e
  match Aiur.Proof.ofBytesChecked wrapper.proof with
  | .ok proof => return .ok { claim := wrapper.claim, proof, address }
  | .error e => return .error s!"aggregate proof {address} does not decode: {e}"

/-- `ix aggregate --ixc <cat.ixc> <member-root>…`: prove every join of the
plan, each within `maxRamBytes`, persist each proof wrapper, and print the
root's address. -/
def aggregateCatalog (ixc : String) (hexes : Array String) (maxRamBytes structuralAbove : Nat)
    (recursionParameters : RecursionParameters) : IO UInt32 := do
  let members ← match ← catalogMembers ixc structuralAbove with
    | .ok members => pure members
    | .error e => IO.eprintln s!"error: {e}"; return 1
  let (plan, _) ← match catalogRoot (members.map (·.1)) with
    | .ok r => pure r
    | .error e => IO.eprintln s!"error: {e}"; return 1
  printStatements members plan
  let mut roots : Array Proven := #[]
  for hex in hexes do
    let address ← match addressOfHex hex with
      | .ok a => pure a
      | .error e => IO.eprintln s!"error: {e}"; return 1
    match ← readProven address with
    | .ok root => roots := roots.push root
    | .error e => IO.eprintln s!"error: {e}"; return 1
  -- One root proof per member, bound by its claim.
  let mut proven : Array (Option Proven) := plan.nodes.map fun _ => none
  for (m, i) in members.zipIdx do
    let (member, _, _) := m
    match roots.filter (·.claim == member.claim) with
    | #[root] => proven := proven.set! i (some root)
    | #[] =>
      IO.eprintln s!"error: no aggregate root states member {member.label}'s claim {member.claim}"
      return 1
    | _ =>
      IO.eprintln s!"error: several aggregate roots state member {member.label}'s claim"
      return 1
  for root in roots do
    unless members.any (·.1.claim == root.claim) do
      IO.eprintln s!"error: aggregate root {root.address} states no member's claim: {root.claim}"
      return 1
  let started ← IO.monoMsNow
  let ixvmTask ← IO.asTask (prio := .dedicated) do
    compileBackend "IxVM" (fun _ => IxVM.ixVM) IxVM.functionGroups
      Aiur.defaultCommitmentParameters Aiur.defaultFriParameters
  let aggrTask ← IO.asTask (prio := .dedicated) do
    compileBackend "ixAggr recursion" (fun _ => Aggr.ixAggr) Aggr.functionGroups
      recursionParameters.commitment recursionParameters.fri
  let ixvm ← match ← IO.ofExcept ixvmTask.get with
    | .ok backend => pure backend
    | .error e => IO.eprintln e; return 1
  let aggr ← match ← IO.ofExcept aggrTask.get with
    | .ok backend => pure backend
    | .error e => IO.eprintln e; return 1
  let verifyIdx := ixvm.compiled.getFuncIdx `verify_claim |>.get!
  let aggrIdx := aggr.compiled.getFuncIdx `ix_aggr |>.get!
  let allowed := Aggr.allowedBlob ixvm.vk verifyIdx aggr.vk aggrIdx
  IO.eprintln s!"[aggregate] backends: {(← IO.monoMsNow) - started} ms; every node verifies its \
    children under one identity: IxVM key {Address.blake3 ixvm.vk}, ix_aggr key \
    {Address.blake3 aggr.vk}"
  for i in [0:plan.nodes.size] do
    let some (shape, preimages, trees) := plan.advice (members.map (·.1)) i | continue
    let mut advice : Array (ByteArray × ByteArray) := #[]
    for c in plan.nodes[i]!.children do
      let some child := proven[c]!
        | IO.eprintln s!"error: node {c} has no proof"; return 1
      let outer := aggregateOuterClaim allowed aggrIdx child.claim
      match aggr.system.proofToAdviceBytes outer child.proof with
      | .ok bytes => advice := advice.push (bytes, MultiStark.serializeClaims #[outer])
      | .error e => IO.eprintln s!"error: node {c}'s proof does not verify: {e}"; return 1
    let claim := plan.statements[i]!.claim
    let outBytes := Ix.Claim.ser claim
    let stepStarted ← IO.monoMsNow
    let result ← IO.lazyPure fun _ =>
      aggr.system.proveIxAggrWithin aggrIdx (pubInput allowed outBytes) shape
        advice[0]!.1 advice[1]!.1 ixvm.vk aggr.vk advice[0]!.2 advice[1]!.2 outBytes allowed
        (preimagesBlob preimages) (treesBlob trees) (pathsBlob #[]) maxRamBytes
    let (outer, proof) ← match result with
      | .ok r => pure r
      | .error e => IO.eprintln s!"error: node {i} (shape {shape}): {e}"; return 1
    unless outer == aggregateOuterClaim allowed aggrIdx claim do
      IO.eprintln s!"error: node {i}: the proof's claim is not the node's"
      return 1
    let address ← StoreIO.toIO (Store.write (Ixon.Proof.ser { claim, proof := proof.toBytes }))
    IO.eprintln s!"[aggregate] node {i} (shape {shape}, {proof.shardCount} trace shards) \
      proved in {(← IO.monoMsNow) - stepStarted} ms: {address}"
    proven := proven.set! i (some { claim, proof, address })
  let some root := proven[plan.root]!
    | IO.eprintln "error: the root has no proof"; return 1
  IO.println root.address
  return 0

/-- `ix verify --aggregate <root> --ixc <cat.ixc>`: recompute the catalog's
root claim from its manifest and pieces, check that each proof states it, and
verify each proof. -/
def verifyCatalog (ixc : String) (hexes : List String) (structuralAbove : Nat)
    (backend : VerificationBackend) : IO UInt32 := do
  let members ← match ← catalogMembers ixc structuralAbove with
    | .ok members => pure members
    | .error e => IO.eprintln s!"error: {e}"; return 1
  let (plan, expected) ← match catalogRoot (members.map (·.1)) with
    | .ok r => pure r
    | .error e => IO.eprintln s!"error: {e}"; return 1
  printStatements members plan
  let constants := members.foldl (fun n m => n + m.2.2) 0
  let mut rc : UInt32 := 0
  for hex in hexes do
    match ← verifyOne backend expected constants members.size hex with
    | .ok message => IO.println message
    | .error e => IO.eprintln s!"error: {e}"; rc := 1
  return rc
where
  verifyOne (backend : VerificationBackend) (expected : Ix.Claim) (constants count : Nat)
      (hex : String) :
      IO (Except String String) := do
    let address ← match addressOfHex hex with
      | .ok a => pure a
      | .error e => return .error e
    let root ← match ← readProven address with
      | .ok root => pure root
      | .error e => return .error e
    if root.claim != expected then
      return .error s!"aggregate proof {address} states {root.claim}, not the catalog's \
        root {expected}"
    match backend.system.verify (aggregateOuterClaim backend.allowed backend.aggrIdx expected)
        root.proof with
    | .ok () =>
      return .ok s!"ok: aggregate proof {address} verifies the catalog's root {expected}: \
        {count} members, all {constants} of their constants well-typed, each member's under \
        its own role binding"
    | .error e => return .error s!"aggregate verification of {address} failed: {e}"

end Ix.Cli.CatalogAggregate

end
