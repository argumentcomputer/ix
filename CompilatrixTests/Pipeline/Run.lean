import CompilatrixTests.Pipeline.Integration
import CompilatrixTests.Pipeline.Fixtures
import Compilatrix.X86.ValidatedScalar
import Compilatrix.Recursion.Rejections
import Compilatrix.CallReuse.Rejections
import Compilatrix.UniqueReuse.Rejections
import Compilatrix.IxIR2.ReuseExamples
import Compilatrix.IxIR2.LivenessExamples

namespace CompilatrixTests.Pipeline

open Compilatrix.Ixon

def run : IO Bool := do
  let mut ok := true


  for check in Compilatrix.Pipeline.nativeIntegrationChecks do
    if !check.2 then
      IO.eprintln s!"FAIL: pipeline integration: {check.1}"
      ok := false

  if !AddressedErasureFixtures.validatedIxIR2AttachmentOk then
    IO.eprintln "FAIL: validated IxIR₁ pipeline did not attach and validate the conservative IxIR₂ sidecars"
    ok := false

  for number in [0, 42, 4294967296, UInt64.size - 1] do
    match Compilatrix.X86.ValidatedScalar.compile number with
    | .error error =>
        IO.eprintln s!"FAIL: validated Ixon scalar {number} did not compile: {repr error}"
        ok := false
    | .ok compiled =>
        match compiled.observe with
        | .ok _ => pure ()
        | .error message =>
            IO.eprintln s!"FAIL: validated Ixon scalar {number}: {message}"
            ok := false
  if !Compilatrix.X86.ValidatedScalar.rejectsBareLiteral 42 then
    IO.eprintln "FAIL: bare unique source literal lost its shared-result freezeNeeded rejection"
    ok := false
  if !Compilatrix.X86.ValidatedScalar.rejectsOverflow then
    IO.eprintln "FAIL: validated Ixon scalar above 64 bits lost its selector rejection"
    ok := false

  match Compilatrix.Recursion.Examples.runAll with
  | .ok _ => pure ()
  | .error message =>
    IO.eprintln s!"FAIL: Ixon source recursion/reuse: {message}"
    ok := false

  match Compilatrix.CallReuse.Examples.runAll with
  | .ok _ => pure ()
  | .error message =>
    IO.eprintln s!"FAIL: Ixon source call reuse: {message}"
    ok := false

  match Compilatrix.UniqueReuse.Examples.runAll with
  | .ok _ => pure ()
  | .error message =>
    IO.eprintln s!"FAIL: Ixon source unique reuse: {message}"
    ok := false

  match Compilatrix.IxIR2.Reuse.Examples.checkUnaliased with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Compilatrix.IxIR2.Reuse.Examples.checkAliased with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  for aliased in [false, true] do
    match Compilatrix.IxIR2.Reuse.Examples.checkZeroFieldChild aliased with
    | .ok _ => pure ()
    | .error message =>
        IO.eprintln s!"FAIL: {message}"
        ok := false

  for overApplied in [false, true] do
    for aliased in [false, true] do
      match Compilatrix.IxIR2.Reuse.Examples.checkPapTailReturn overApplied aliased with
      | .ok _ => pure ()
      | .error message =>
          IO.eprintln s!"FAIL: {message}"
          ok := false

  for underApplied in [false, true] do
    match Compilatrix.IxIR2.Reuse.Examples.checkImmediateApplyMore underApplied with
    | .ok _ => pure ()
    | .error message =>
        IO.eprintln s!"FAIL: {message}"
        ok := false

  for fallback in [false, true] do
    match Compilatrix.IxIR2.Reuse.Examples.checkProductionSelection fallback with
    | .ok _ => pure ()
    | .error message =>
        IO.eprintln s!"FAIL: {message}"
        ok := false

  match Compilatrix.IxIR2.Reuse.Examples.checkProductionSourceRejection with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Compilatrix.IxIR2.Reuse.Examples.checkIncompatibleLayout with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Compilatrix.IxIR2.Reuse.Examples.checkGeneralizedShape with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Compilatrix.IxIR2.Reuse.Examples.checkLateSourceUse with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  match Compilatrix.IxIR2.Liveness.Examples.checkSuite with
  | .ok _ => pure ()
  | .error message =>
      IO.eprintln s!"FAIL: {message}"
      ok := false

  if !IxIR2PipelineFixtures.ambiguousFetchAcceptedByProducerFact then
    IO.eprintln "FAIL: exact local HPT producer provenance did not disambiguate an IxIR₂ fetch"
    ok := false

  if !IxIR2PipelineFixtures.ambiguousCaseAcceptedByProducerFact then
    IO.eprintln "FAIL: exact local HPT producer provenance did not disambiguate an IxIR₂ constructor switch"
    ok := false

  if !IxIR2PipelineFixtures.unresolvedFetchRejected then
    IO.eprintln "FAIL: IxIR₂ producer provenance accepted an unresolved fetch parameter"
    ok := false

  if !IxIR2PipelineFixtures.ambiguousScalarFreeAcceptedByProducerFact then
    IO.eprintln "FAIL: exact local HPT producer provenance did not disambiguate an IxIR₂ shallow free"
    ok := false

  if !IxIR2PipelineFixtures.pappCapabilityTransitionAccepted then
    IO.eprintln "FAIL: checked IxIR₂ function-PAP capability transition drifted"
    ok := false

  if !IxIR2PipelineFixtures.pappSafetyCheckRejectsUnsafe then
    IO.eprintln "FAIL: IxIR₂ attachment PAP-safety check accepted an unsafe declaration"
    ok := false

  if !IxIR2PipelineFixtures.lenderDestructionRetiresBorrow then
    IO.eprintln "FAIL: checked IxIR₂ destruction retained a dead lender loan"
    ok := false

  if !IxIR2PipelineFixtures.exactRecursorCaseAccepted then
    IO.eprintln "FAIL: ambiguous recursor case did not cover and execute both full IxIR₂ constructor identities"
    ok := false

  if !IxIR2PipelineFixtures.recursorOriginExtractionOk then
    IO.eprintln "FAIL: recursor-origin extraction lost the final owner map or accepted conflicting blocks"
    ok := false


  return ok

end CompilatrixTests.Pipeline
