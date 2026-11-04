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
public import Ix.Aggr.CatalogPlan
public import Ix.Aggr.Verification
public import Ix.Catalog
public import Ix.Cli.CatalogCmd
public import Ix.Cli.FormalAggregate
public import Ix.IxVM.ClaimHarness
public import Ix.Store

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
    let some table := Ix.Kernel.RoleTable.ofBytes binding.bytes
      | return .error s!"{piece}: not a canonical role binding section"
    let literalClass ← if table.bound.size == Ix.Kernel.Role.all.length then
        match Ix.ClaimContext.literalClassOf table with
        | .ok k => pure (some k)
        | .error e => return .error s!"{piece}: {e}"
      else pure none
    let ixes := dir / s!"{m.label}.ixes"
    let (claim, count) ← if ← ixes.pathExists then
        let view ← match Ix.Shard.parseIxesManifest (← IO.FS.readBinFile ixes) with
          | .ok v => pure v
          | .error e => return .error s!"{ixes}: {e}"
        unless ← Ix.Shard.shardsCover env view.shards do
          return .error s!"{ixes}: invalid manifest coverage"
        let statement ← match Reference.expectedFromManifest env view structuralAbove with
          | .ok s => pure s
          | .error e => return .error s!"{ixes}: {e}"
        match auditAggregateConstants env statement with
        | .ok count => pure (statement.claim, count)
        | .error e => return .error s!"{ixes}: {e}"
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
    let classLabel := m.literalClass.map toString |>.getD "unavailable for an incomplete binding"
    IO.println s!"[catalog] member {m.label} (toolchain {m.toolchain}): {count} constants, \
      binding {entry.binding}, literal class {classLabel}, spec {ctx.spec}, \
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

/-- A proven node: its claim, its `ix_aggr` wrapper and the address of its proof
wrapper in the store. -/
structure Proven where
  claim : Ix.Claim
  wrapper : Ixon.Proof
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
  return .ok { claim := wrapper.claim, wrapper, address }

/-- `ix verify --aggregate <root> --ixc <cat.ixc>`: recompute the catalog's
root claim from its manifest and pieces, check that each proof states it, and
verify each proof. -/
def verifyCatalog (p : Cli.Parsed) (ixc : String) : IO UInt32 := do
  if p.hasFlag "ixe" then
    IO.eprintln "error: --ixc takes the members from the catalog; drop --ixe"
    return 1
  let hexes := (p.variableArgsAs! String).toList
  if hexes.isEmpty then
    IO.eprintln "error: --aggregate requires at least one aggregate proof address"
    return 1
  let structuralAbove := ((p.flag? "structural-above").map (·.as! Nat)).getD
    defaultStructuralAbove
  let members ← match ← catalogMembers ixc structuralAbove with
    | .ok members => pure members
    | .error e => IO.eprintln s!"error: {e}"; return 1
  let (plan, expected) ← match catalogRoot (members.map (·.1)) with
    | .ok r => pure r
    | .error e => IO.eprintln s!"error: {e}"; return 1
  printStatements members plan
  let ctx ← FormalAggregate.context p
  let constants := members.foldl (fun n m => n + m.2.2) 0
  let mut rc : UInt32 := 0
  for hex in hexes do
    match ← verifyOne ctx expected constants members.size hex with
    | .ok message => IO.println message
    | .error e => IO.eprintln s!"error: {e}"; rc := 1
  return rc
where
  verifyOne (ctx : FormalAggregate.Context) (expected : Ix.Claim) (constants count : Nat)
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
    try
      FormalAggregate.verifyWrapper ctx .aggr root.wrapper
      return .ok s!"ok: aggregate proof {address} verifies the catalog's root {expected}: \
        {count} members, all {constants} of their constants well-typed, each member's under \
        its own role binding"
    catch e =>
      return .error s!"aggregate verification of {address} failed: {e}"

/-- The acceptance check of `ix verify --aggregate --ixc`, applied to a catalog
root that an untrusted prover produced: the catalog's root claim is recomputed
from its manifest and pieces, and the proof at `address` must state exactly
that claim and verify under the certified artifacts. Returns the number of
members and of their constants. -/
def acceptCatalog (ctx : FormalAggregate.Context) (ixc : String) (structuralAbove : Nat)
    (address : Address) : IO (Nat × Nat) := do
  let members ← match ← catalogMembers ixc structuralAbove with
    | .ok members => pure members
    | .error e => throw (IO.userError e)
  let (_, expected) ← IO.ofExcept (catalogRoot (members.map (·.1)))
  let root ← IO.ofExcept (← readProven address)
  unless root.claim == expected do
    throw (IO.userError s!"aggregate proof {address} states {root.claim}, not the catalog's \
      root {expected}")
  FormalAggregate.verifyWrapper ctx .aggr root.wrapper
  return (members.size, members.foldl (fun n m => n + m.2.2) 0)

open Lean in
/-- `ix aggregate --ixc <cat.ixc> <member-root>…`: prove every join of the
plan on the aggregate controller, which binds each member root to its member,
recomputes the plan from the members and must reach this plan's root claim,
then persists every join's proof wrapper. The root is printed only after
`acceptCatalog`. -/
def aggregateCatalog (p : Cli.Parsed) (ixc : String) : IO UInt32 := do
  let structuralAbove := ((p.flag? "structural-above").map (·.as! Nat)).getD
    defaultStructuralAbove
  let members ← match ← catalogMembers ixc structuralAbove with
    | .ok members => pure members
    | .error e => IO.eprintln s!"error: {e}"; return 1
  let (plan, expected) ← match catalogRoot (members.map (·.1)) with
    | .ok r => pure r
    | .error e => IO.eprintln s!"error: {e}"; return 1
  printStatements members plan
  let options ← FormalAiur.hostOptions p
  let ctx ← FormalAggregate.context p
  let proofs ← (p.variableArgsAs! String).mapM fun hex => do
    let some address := Address.fromString hex
      | throw (IO.userError s!"expected a 64-character hex address, got {hex}")
    pure address.hash
  let config : FormalProver.CatalogConfig := {
    members := members.map fun (m, _, _) => {
      label := m.label, claim := Ix.Claim.ser m.claim, bindingSection := m.bindingSection
      literalClass := m.literalClass.map (·.hash) }
    proofs, expectedRoot := Ix.Claim.ser expected, device := options.device
    options := options.job, useCache := !(p.hasFlag "no-cache"), writeOutputs := true }
  let address ← match ← (FormalProver.aggregateCatalog ctx.ixvmSystem ctx.aggrSystem
      config).toBaseIO with
    | .ok bytes => pure (⟨bytes⟩ : Address)
    | .error e => IO.eprintln s!"error: {e}"; return 1
  let root := toString address
  let (count, constants) ← acceptCatalog ctx ixc structuralAbove address
  IO.println s!"ok: aggregate proof {address} verifies the catalog's root {expected}: \
    {count} members, all {constants} of their constants well-typed, each member's under \
    its own role binding"
  IO.println root
  return 0

end Ix.Cli.CatalogAggregate

end
