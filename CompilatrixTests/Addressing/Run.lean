import CompilatrixTests.Addressing.Fixtures
import Compilatrix.IxIR1.ReaddressIndexTests
import Compilatrix.Modular.PreparationTests
import Compilatrix.IxIR1.WellModedGen

namespace CompilatrixTests.Addressing

open Compilatrix.Ixon

def run : IO Bool := do
  let mut ok := true

  let ir0Bytes := Compilatrix.IxIR0.Decl.preimage IxIRAddressFixtures.ir0Decl
  if ir0Bytes != IxIRAddressFixtures.expectedIr0Bytes then
    IO.eprintln s!"FAIL: IxIR₀ declaration preimage drifted: {repr ir0Bytes.data.toList}"
    ok := false
  let ir0Address := Compilatrix.IxIR0.Decl.address IxIRAddressFixtures.ir0Decl
  if hashNats ir0Address != IxIRAddressFixtures.expectedIr0Hash then
    IO.eprintln s!"FAIL: IxIR₀ declaration address drifted: {ir0Address}"
    ok := false
  if !IxIRAddressFixtures.ir0DecodeOk then
    IO.eprintln "FAIL: IxIR₀ canonical declaration did not decode"
    ok := false
  for fixture in IxIRAddressFixtures.ir0Malformed do
    if !IxIRAddressFixtures.ir0Rejects fixture.2 then
      IO.eprintln s!"FAIL: IxIR₀ decoder accepted {fixture.1}"
      ok := false

  let ir1Bytes := Compilatrix.IxIR1.Decl.preimage IxIRAddressFixtures.ir1Decl
  if ir1Bytes != IxIRAddressFixtures.expectedIr1Bytes then
    IO.eprintln s!"FAIL: IxIR₁ declaration preimage drifted: {repr ir1Bytes.data.toList}"
    ok := false
  let ir1Address := Compilatrix.IxIR1.Decl.address IxIRAddressFixtures.ir1Decl
  if hashNats ir1Address != IxIRAddressFixtures.expectedIr1Hash then
    IO.eprintln s!"FAIL: IxIR₁ declaration address drifted: {ir1Address}"
    ok := false
  if !IxIRAddressFixtures.ir1DecodeOk then
    IO.eprintln "FAIL: IxIR₁ canonical declaration did not decode"
    ok := false
  for fixture in IxIRAddressFixtures.ir1Malformed do
    if !IxIRAddressFixtures.ir1Rejects fixture.2 then
      IO.eprintln s!"FAIL: IxIR₁ decoder accepted {fixture.1}"
      ok := false

  if !IxIR1OwnedMainFixtures.ownedBoundaryOk then
    IO.eprintln "FAIL: IxIR₁ owned-main result-world boundary drifted"
    ok := false

  if !IxIR1OwnedMainFixtures.noReuseChecksOk then
    IO.eprintln "FAIL: IxIR₁ executable no-reuse reflection drifted"
    ok := false

  match IxIRMutualBlockFixtures.built with
  | .error message =>
    IO.eprintln s!"FAIL: cycle-safe IxIR₀ mutual block failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRMutualBlockFixtures.builtOk result then
      IO.eprintln s!"FAIL: IxIR₀ mutual-block identity drifted (block={result.blockAddress}, members={repr (result.derivedAddresses.map Address.toHex)}, audit={result.semanticAudit IxIRMutualBlockFixtures.raw})"
      ok := false
  if !IxIRMutualBlockFixtures.decodeOk then
    IO.eprintln "FAIL: canonical mutual block did not decode and materialize identically"
    ok := false
  for fixture in IxIRMutualBlockFixtures.malformed do
    if !IxIRMutualBlockFixtures.rejectsArtifactBytes fixture.2 then
      IO.eprintln s!"FAIL: mutual-block decoder accepted {fixture.1}"
      ok := false
  if !IxIRMutualBlockFixtures.transientSpellingIndependent then
    IO.eprintln "FAIL: mutual-block identity depends on transient member names"
    ok := false
  if !IxIRMutualBlockFixtures.orderSensitive then
    IO.eprintln "FAIL: mutual-block member order did not affect identity"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsEmpty then
    IO.eprintln "FAIL: empty mutual block was accepted"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsDuplicateTemporary then
    IO.eprintln "FAIL: duplicate mutual-block temporary key was accepted"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsLegacyWrapAlias then
    IO.eprintln "FAIL: the legacy 2^64 member-address alias crossed the block boundary"
    ok := false
  if !IxIRMutualBlockFixtures.rejectsDerivedReservedCollision then
    IO.eprintln "FAIL: a derived mutual-member key captured a reserved identity"
    ok := false

  match IxIR1MutualBlockFixtures.built with
  | .error message =>
    IO.eprintln s!"FAIL: cycle-safe IxIR₁ mutual block failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1MutualBlockFixtures.builtOk result then
      IO.eprintln s!"FAIL: IxIR₁ mutual-block identity drifted (block={result.blockAddress}, members={repr (result.derivedAddresses.map Address.toHex)}, audit={result.semanticAudit IxIR1MutualBlockFixtures.raw})"
      ok := false
  if !IxIR1MutualBlockFixtures.decodeOk then
    IO.eprintln "FAIL: canonical IxIR₁ mutual block did not decode and materialize identically"
    ok := false
  for fixture in IxIR1MutualBlockFixtures.malformed do
    if !IxIR1MutualBlockFixtures.rejectsArtifactBytes fixture.2 then
      IO.eprintln s!"FAIL: IxIR₁ mutual-block decoder accepted {fixture.1}"
      ok := false
  if !IxIR1MutualBlockFixtures.transientSpellingIndependent then
    IO.eprintln "FAIL: IxIR₁ mutual-block identity depends on transient member names"
    ok := false
  if !IxIR1MutualBlockFixtures.orderSensitive then
    IO.eprintln "FAIL: IxIR₁ mutual-block member order did not affect identity"
    ok := false
  if !IxIR1MutualBlockFixtures.rejectsEmpty then
    IO.eprintln "FAIL: empty IxIR₁ mutual block was accepted"
    ok := false
  if !IxIR1MutualBlockFixtures.rejectsDuplicateTemporary then
    IO.eprintln "FAIL: duplicate IxIR₁ mutual-block temporary key was accepted"
    ok := false
  if !IxIR1MutualBlockFixtures.rejectsDerivedReservedCollision then
    IO.eprintln "FAIL: a derived IxIR₁ mutual-member key captured a reserved identity"
    ok := false

  for (label, passed) in [
      ("repeated erased blocks preserve both producers", RepeatedErasureFixtures.checkedReuse),
      ("conflicting block/member identities reject", RepeatedErasureFixtures.conflictsRejected),
      ("repeated blocks preserve protected namespaces", RepeatedErasureFixtures.protectedNamespaces),
      ("repeated cycles preserve ordered member maps", RepeatedErasureFixtures.repeatedCycles)] do
    if !passed then
      IO.eprintln s!"FAIL: {label}"
      ok := false
  match AddressedErasureFixtures.built with
  | .error error =>
    IO.eprintln s!"FAIL: addressed erasure rejected a cyclic program: {repr error}"
    ok := false
  | .ok result =>
    if !AddressedErasureFixtures.builtOk result then
      IO.eprintln s!"FAIL: addressed erasure drifted (blocks={repr (result.addressed.blockAddresses.map Address.toHex)}, members={repr (result.addressed.derivedAddresses.map Address.toHex)}, audit={result.semanticAudit AddressedErasureFixtures.eraseCtx AddressedErasureFixtures.constants (.ref AddressedErasureFixtures.projection) 200})"
      ok := false
  if !AddressedErasureFixtures.crossBlockTemporaryRejected then
    IO.eprintln "FAIL: a cross-block transient reference was accepted"
    ok := false
  match AddressedErasureFixtures.pipelineBuilt,
      AddressedErasureFixtures.validatedPipelineBuilt with
  | .ok direct, .ok gated =>
    if !AddressedErasureFixtures.validatedPipelineAgrees direct gated then
      IO.eprintln "FAIL: direct and validated cyclic pipelines disagree"
      ok := false
  | _, .error error =>
    IO.eprintln s!"FAIL: validated pipeline rejected the certified cyclic fixture: {repr error}"
    ok := false
  | _, _ =>
    IO.eprintln "FAIL: direct cyclic pipeline failed during agreement check"
    ok := false

  if !ReaddressOracleFixtures.adapterOk then
    IO.eprintln "FAIL: the IxIR₀ opaque-oracle adapter did not reverse the call key, preserve scalar arity, and map the result"
    ok := false
  match ReaddressOracleFixtures.ledgerBuilt with
  | .error message =>
    IO.eprintln s!"FAIL: the ledger-oracle mutual-block fixture did not readdress: {message}"
    ok := false
  | .ok result =>
    if !ReaddressOracleFixtures.ledgerCycleOk result then
      IO.eprintln s!"FAIL: the concrete Nat-add oracle lost coherence across the member map (blocks={repr (result.blockAddresses.map Address.toHex)}, members={repr (result.derivedAddresses.map Address.toHex)})"
      ok := false
  if !ReaddressOracleFixtures.mainExternalCaptureRejected then
    IO.eprintln "FAIL: an IxIR₀ member key captured an external identity referenced only by main"
    ok := false

  match IxIRReaddressFixtures.chain with
  | .error message =>
    IO.eprintln s!"FAIL: dependency-ordered IxIR₁ readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.chainOk result then
      IO.eprintln s!"FAIL: dependency-ordered IxIR₁ readdressing drifted (content={repr (IxIRReaddressFixtures.contentHexes result)})"
      ok := false

  match IxIRReaddressFixtures.deduplicate with
  | .error message =>
    IO.eprintln s!"FAIL: identical IxIR₁ content did not deduplicate: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.deduplicateOk result then
      IO.eprintln s!"FAIL: IxIR₁ content deduplication drifted (content={repr (IxIRReaddressFixtures.contentHexes result)})"
      ok := false

  if !IxIRReaddressFixtures.cycleRejected then
    IO.eprintln "FAIL: generated IxIR₁ address cycle did not fail closed"
    ok := false
  if !IxIRReaddressFixtures.overlapRejected then
    IO.eprintln "FAIL: generated/source temporary-address overlap was accepted"
    ok := false
  if !IxIRReaddressFixtures.sourceKeyCollisionRejected then
    IO.eprintln "FAIL: generated content/source-key collision was accepted"
    ok := false
  if !IxIRReaddressFixtures.contentTemporaryOverlapRejected then
    IO.eprintln "FAIL: generated content/temporary namespace overlap was accepted"
    ok := false
  if !IxIRReaddressFixtures.protectedSourceIdentityRejected then
    IO.eprintln "FAIL: a transient key rewrote a constructor source identity"
    ok := false

  let _ ← Compilatrix.IxIR1.ReaddressIndexTests.run
  let _ ← Compilatrix.Modular.PreparationTests.run

  if !IxIR1ReaddressAllFixtures.componentsOk then
    IO.eprintln "FAIL: IxIR₁ SCC discovery did not preserve deterministic source-member order"
    ok := false
  if !IxIR1ReaddressAllFixtures.longChainComponentsOk then
    IO.eprintln "FAIL: IxIR₁ SCC discovery failed the iterative long-chain guard"
    ok := false
  match IxIR1ReaddressAllFixtures.built with
  | .error message =>
    IO.eprintln s!"FAIL: whole-program IxIR₁ SCC readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1ReaddressAllFixtures.builtOk result then
      IO.eprintln s!"FAIL: whole-program IxIR₁ SCC identities or audit drifted (targets={repr (result.addressMap.map fun entry => Address.toHex entry.2)}, blocks={repr (result.blockAddresses.map Address.toHex)}, audit={result.semanticAudit IxIR1ReaddressAllFixtures.raw IxIR1ReaddressAllFixtures.mainCode})"
      ok := false
  if !IxIR1ReaddressAllFixtures.transientSpellingIndependent then
    IO.eprintln "FAIL: whole-program IxIR₁ identities depend on transient producer names"
    ok := false
  if !IxIR1ReaddressAllFixtures.memberOrderSensitive then
    IO.eprintln "FAIL: IxIR₁ SCC member order did not affect block/program identity"
    ok := false
  if !IxIR1ReaddressAllFixtures.ordinaryDeduplicates then
    IO.eprintln "FAIL: whole-program IxIR₁ ordinary content did not deduplicate"
    ok := false
  if !IxIR1ReaddressAllFixtures.explicitSelfUsesBlock then
    IO.eprintln "FAIL: an explicit IxIR₁ self-address edge did not use a block artifact"
    ok := false
  if !IxIR1ReaddressAllFixtures.callSelfUsesOrdinaryHash then
    IO.eprintln "FAIL: address-free IxIR₁ callSelf did not retain the ordinary hash path"
    ok := false
  if !IxIR1ReaddressAllFixtures.emptyOk then
    IO.eprintln "FAIL: empty whole-program IxIR₁ readdressing drifted"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsDuplicateProducer then
    IO.eprintln "FAIL: duplicate whole-program IxIR₁ producer key was accepted"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsReservedProducer then
    IO.eprintln "FAIL: an IxIR₁ producer key overlapped a reserved identity"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsProtectedContent then
    IO.eprintln "FAIL: an IxIR₁ content address captured a protected identity"
    ok := false
  if !IxIR1ReaddressAllFixtures.rejectsContentInTransientNamespace then
    IO.eprintln "FAIL: an IxIR₁ content address overlapped the transient namespace"
    ok := false

  match IxIR1ReaddressAllFixtures.fullyNested with
  | .error message =>
    IO.eprintln s!"FAIL: fully addressed nested IxIR₁ lowering failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1ReaddressAllFixtures.fullyNestedOk result then
      IO.eprintln s!"FAIL: fully addressed nested IxIR₁ lowering drifted (map={repr (result.addressMap.map fun entry => Address.toHex entry.2)}, blocks={repr (result.blockAddresses.map Address.toHex)}, stable={repr (result.stable.map fun entry => Address.toHex entry.1)})"
      ok := false
  match IxIR1ReaddressAllFixtures.fullyCyclicLowering with
  | .error message =>
    IO.eprintln s!"FAIL: source/lifted IxIR₁ cycle lowering failed: {message}"
    ok := false
  | .ok result =>
    if !IxIR1ReaddressAllFixtures.fullyCyclicLoweringOk result then
      IO.eprintln s!"FAIL: source/lifted IxIR₁ cycle did not become one two-member block (targets={repr (result.addressMap.map fun entry => Address.toHex entry.2)}, blocks={repr (result.blockAddresses.map Address.toHex)}, declarations={result.declarations.length}, audit={IxIR1ReaddressAllFixtures.fullyLoweredAudit [(IxIR1ReaddressAllFixtures.cyclicSourceKey, IxIR1ReaddressAllFixtures.cyclicSourceDeclaration)] (.ref IxIR1ReaddressAllFixtures.cyclicSourceKey) result})"
      ok := false
  if !IxIR1ReaddressAllFixtures.fullyProtectedSourceIdentityRejected then
    IO.eprintln "FAIL: fully addressed lowering allowed a generated key to capture a constructor identity"
    ok := false

  match IxIRReaddressFixtures.nestedLowering with
  | .error message =>
    IO.eprintln s!"FAIL: nested lifted-lambda readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.nestedLoweringOk result then
      IO.eprintln s!"FAIL: nested lifted-lambda addresses or runtime changed (map={result.addressMap.length}, generated={result.generated.length}, no-transient={result.noTransientReferences}, addressed={result.generatedAreAddressed}, entries={repr result.addressMap})"
      ok := false

  match IxIRReaddressFixtures.wrapperLowering with
  | .error message =>
    IO.eprintln s!"FAIL: constructor-wrapper readdressing failed: {message}"
    ok := false
  | .ok result =>
    if !IxIRReaddressFixtures.wrapperLoweringOk result then
      IO.eprintln s!"FAIL: constructor-wrapper content addressing drifted (map={result.addressMap.length}, generated={result.generated.length}, no-transient={result.noTransientReferences}, addressed={result.generatedAreAddressed}, entries={repr result.addressMap})"
      ok := false

  let generatedSummary := Compilatrix.IxIR1.WellModedGen.summarize
  let expectedGeneratedSummary :
      Compilatrix.IxIR1.WellModedGen.Summary :=
    { checked := 280
      differential := 180
      expectedRejections := 100
      allKindsSeen := true
      finalState := 1151165198556225096
      fingerprint := 6965325113816880105 }
  if generatedSummary != expectedGeneratedSummary then
    IO.eprintln s!"FAIL: well-moded generator corpus drifted: {repr generatedSummary}"
    ok := false
  match Compilatrix.IxIR1.WellModedGen.checkCorpus with
  | none => pure ()
  | some failure =>
    IO.eprintln s!"FAIL: seeded IxIR₀ property case failed: {repr failure}"
    IO.eprintln s!"      original expr: {repr failure.original.template.expr}"
    IO.eprintln s!"      minimized expr: {repr failure.minimized.template.expr}"
    ok := false


  return ok

end CompilatrixTests.Addressing
