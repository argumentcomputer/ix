import CompilatrixTests.HPT.Fixtures

namespace CompilatrixTests.HPT

open Compilatrix.Ixon

def run : IO Bool := do
  let mut ok := true

  match AddressedErasureFixtures.pipelineBuilt with
  | .error error =>
    IO.eprintln s!"FAIL: full pipeline rejected the cyclic definition fixture: {repr error}"
    ok := false
  | .ok artifact =>
    if !AddressedErasureFixtures.pipelineOk artifact then
      IO.eprintln s!"FAIL: full pipeline did not emit the expected IxIR₁ block (blocks={repr (artifact.targetBlocks.map fun block => Address.toHex block.blockAddress)}, map={repr (artifact.targetAddressMap.map fun entry => Address.toHex entry.2)})"
      ok := false
    if !HPTFixtures.pipelineTopOk artifact then
      IO.eprintln "FAIL: the production target artifact rejected the universal checked HPT fallback"
      ok := false
    if !HPTFixtures.pipelineProducerOk artifact then
      IO.eprintln "FAIL: the production target artifact rejected deterministic HPT production"
      ok := false
    if !HPTFixtures.pipelineCacheOk artifact then
      IO.eprintln "FAIL: the production target artifact rejected checked persistent HPT caching"
      ok := false
    if !(← HPTFixtures.pipelineCacheFileOk artifact) then
      IO.eprintln "FAIL: the production target artifact rejected file-backed persistent HPT caching"
      ok := false
    if !(← HPTFixtures.pipelineCacheDirectoryOk artifact) then
      IO.eprintln "FAIL: the production target artifact rejected indexed chunk-directory HPT caching"
      ok := false
  match HPTFixtures.addressed with
  | .error message =>
    IO.eprintln s!"FAIL: HPT fixture did not content-address: {message}"
    ok := false
  | .ok program =>
    match HPTFixtures.precise program, HPTFixtures.widened program with
    | .ok precise, .ok widened =>
      if !HPTFixtures.preciseOk program precise then
        IO.eprintln s!"FAIL: checked HPT facts or SCC materialization drifted (cacheKeys={repr (precise.cacheKeys.map Address.toHex)}, addresses={repr (precise.addresses.map Address.toHex)})"
        ok := false
      if !HPTFixtures.fieldSensitiveOk program precise then
        IO.eprintln "FAIL: field-sensitive HPT allocation/fetch facts disagreed with concrete execution"
        ok := false
      if !HPTFixtures.caseBinderFieldOk then
        IO.eprintln "FAIL: HPT case binders lost field precision, binding order, tag filtering, or conservative widening"
        ok := false
      if !HPTFixtures.recursiveFieldOk then
        IO.eprintln "FAIL: recursive HPT fields lost depth-two projection, case-binder, budget, producer, or cache precision"
        ok := false
      if !HPTFixtures.casePruneOk program then
        IO.eprintln "FAIL: checked HPT case simplification changed execution or crossed a conservative collapse boundary"
        ok := false
      if !HPTFixtures.recursiveCasePruneOk program then
        IO.eprintln "FAIL: recursive checked HPT case simplification missed a nested rewrite or changed execution"
        ok := false
      if !HPTFixtures.callSelfCasePruneOk program then
        IO.eprintln "FAIL: recursive checked HPT case simplification changed a terminating callSelf execution or failed to rewrite its current frame"
        ok := false
      if !HPTFixtures.pipelineCallSelfMainPruneOk program then
        IO.eprintln "FAIL: checked HPT artifact-main pruning changed an exact finite-fuel callSelf result"
        ok := false
      if !HPTFixtures.declarationGraphCasePruneOk then
        IO.eprintln "FAIL: checked HPT declaration-graph simplification failed to readdress a changed body, rewrite its main edge, or preserve execution"
        ok := false
      if !HPTFixtures.optimizerHarnessOk then
        IO.eprintln "FAIL: optimizer policy, observations, deterministic report, fail-soft controls, address transport, or idempotence drifted"
        ok := false
      if !HPTFixtures.reachabilityCertificateOk then
        IO.eprintln "FAIL: rooted reachability production, validation, adversarial rejection, fallback, or exact execution drifted"
        ok := false
      if !HPTFixtures.reachabilityHarnessOk then
        IO.eprintln "FAIL: rooted reachability optimizer reporting, exported roots, one-rebuild content addressing, or execution drifted"
        ok := false
      if !HPTFixtures.papFusionHarnessOk then
        IO.eprintln "FAIL: checked PAP/apply fusion drifted across saturation classes, rejection gates, reporting, execution, or idempotence"
        ok := false
      if !HPTFixtures.fetchForwardHarnessOk then
        IO.eprintln "FAIL: checked scalar fetch forwarding drifted across allocation/reuse, rejection gates, reporting, exact execution, or idempotence"
        ok := false
      if !HPTFixtures.cacheConeOk program precise widened then
        IO.eprintln "FAIL: HPT cache invalidation escaped or missed the dependency cone"
        ok := false
      if !HPTFixtures.persistentCacheOk program precise widened then
        IO.eprintln "FAIL: persistent HPT cache ingress, recovery, or dependency-cone rebuilding drifted"
        ok := false
      if !HPTFixtures.persistentCacheBudgetsOk program precise then
        IO.eprintln "FAIL: persistent HPT cache resource gates drifted at an exact or one-below boundary"
        ok := false
      if !(← HPTFixtures.persistentCacheFileOk program) then
        IO.eprintln "FAIL: persistent HPT cache file ingress, framing rejection, or local repair drifted"
        ok := false
      if !(← HPTFixtures.persistentCacheDirectoryOk program) then
        IO.eprintln "FAIL: indexed HPT chunk caching, lazy repair, or directory budgets drifted"
        ok := false
    | .error message, _ =>
      IO.eprintln s!"FAIL: precise HPT post-fixpoint was rejected: {message}"
      ok := false
    | _, .error message =>
      IO.eprintln s!"FAIL: widened HPT post-fixpoint was rejected: {message}"
      ok := false
    if !HPTFixtures.rejectsBadCertificates program then
      IO.eprintln "FAIL: HPT checker accepted an underclaim, noncanonical fact, wrong identity, or reordered artifact list"
      ok := false
    if !HPTFixtures.resourceBudgetsOk program then
      IO.eprintln "FAIL: HPT structural preflight drifted at an exact or one-below boundary"
      ok := false
    if !HPTFixtures.producerOk program then
      IO.eprintln "FAIL: deterministic HPT production drifted in precision, repeatability, or bounded fallback"
      ok := false

  match HPTFixtures.aliasAddressed with
  | .error message =>
    IO.eprintln s!"FAIL: HPT alias/reuse fixture did not content-address: {message}"
    ok := false
  | .ok program =>
    if !HPTFixtures.aliasReuseRegressionOk program then
      IO.eprintln "FAIL: HPT retained a stale constructor fact across aliased reuse"
      ok := false


  return ok

end CompilatrixTests.HPT
