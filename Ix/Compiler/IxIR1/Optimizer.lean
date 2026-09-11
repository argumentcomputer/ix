import Ix.Compiler.IxIR1.HPTCache
import Ix.Compiler.IxIR1.HPTPAPFuseProgram

/-!
# Deterministic IxIR₁ optimizer harness

This module is the control and observation boundary for whole-program IxIR₁
optimization.  It wraps the checked, fact-propagating HPT case simplifier
(impossible-alternative pruning plus exact unary case collapse), exact scalar
fetch forwarding after allocation/reuse, scalar and exact-leaf destruction
specialization, local PAP/application fusion, and checked rooted declaration
reachability with:

- explicit harness and pass-policy versions;
- deterministic, fail-soft resource controls;
- exact static before/after observations;
- content-addressed input, output, certificate, and report identities; and
- an explicit disabled path that returns the input graph unchanged.

The observations are structural compiler counters, not dynamic execution
counters.  `instructions` counts each `ret`, `letOp`, and `case` node once;
operation-specific fields classify the operation bound by each `letOp`.
`codeBytes` is the sum of canonical function-body and main spellings, while
`storedArtifactBytes` follows the actual ordinary/mutual artifact framing.

An exhausted optimizer budget, unsupported policy version, or failed graph
rebuild selects the unoptimized graph and records why.  It never turns an
otherwise accepted program into a compiler rejection.
-/

namespace Ix.Compiler.IxIR1.Optimizer

open Ix.Compiler.Ixon (Address)
open Ix.Compiler.IxIR

def currentHarnessVersion : Nat := 5
def currentCasePruneVersion : Nat := 3
def currentFetchForwardVersion : Nat := 1
def currentDestructionVersion : Nat := 1
def currentPAPFuseVersion : Nat := 1
def currentReachabilityVersion : Nat := Reachability.currentVersion

/-! ## Structural observations -/

/-- Static control, call, and heap-operation counts over IxIR₁ code. -/
structure Counts where
  instructions : Nat := 0
  returns : Nat := 0
  cases : Nat := 0
  alternatives : Nat := 0
  allocations : Nat := 0
  reuses : Nat := 0
  frees : Nat := 0
  rcIncrements : Nat := 0
  rcDecrements : Nat := 0
  uniqueDrops : Nat := 0
  fetches : Nat := 0
  directCalls : Nat := 0
  selfCalls : Nat := 0
  papAllocations : Nat := 0
  applies : Nat := 0
  externCalls : Nat := 0
  deriving BEq, Repr, Inhabited

def Counts.add (left right : Counts) : Counts :=
  { instructions := left.instructions + right.instructions
    returns := left.returns + right.returns
    cases := left.cases + right.cases
    alternatives := left.alternatives + right.alternatives
    allocations := left.allocations + right.allocations
    reuses := left.reuses + right.reuses
    frees := left.frees + right.frees
    rcIncrements := left.rcIncrements + right.rcIncrements
    rcDecrements := left.rcDecrements + right.rcDecrements
    uniqueDrops := left.uniqueDrops + right.uniqueDrops
    fetches := left.fetches + right.fetches
    directCalls := left.directCalls + right.directCalls
    selfCalls := left.selfCalls + right.selfCalls
    papAllocations := left.papAllocations + right.papAllocations
    applies := left.applies + right.applies
    externCalls := left.externCalls + right.externCalls }

private def countsOfOp : Op → Counts
  | .pure _ => {}
  | .alloc _ _ _ => { allocations := 1 }
  | .reuse _ _ _ => { reuses := 1 }
  | .free _ => { frees := 1 }
  | .dup _ => { rcIncrements := 1 }
  | .drop _ => { rcDecrements := 1 }
  | .dropU _ => { uniqueDrops := 1 }
  | .fetch _ _ => { fetches := 1 }
  | .call _ _ => { directCalls := 1 }
  | .callSelf _ => { selfCalls := 1 }
  | .papp _ _ => { papAllocations := 1 }
  | .apply _ _ => { applies := 1 }
  | .extern _ _ => { externCalls := 1 }

mutual

def countsCode : Code → Counts
  | .ret _ => { instructions := 1, returns := 1 }
  | .letOp operation rest =>
      (countsOfOp operation).add
        ((countsCode rest).add { instructions := 1 })
  | .case _ _ alternatives =>
      alternatives.foldl
        (fun total alternative => total.add (countsAlternative alternative))
        { instructions := 1
          cases := 1
          alternatives := alternatives.size }

def countsAlternative : Alt → Counts
  | .mk _ _ body => countsCode body

end

/-- Deterministic whole-program static observation. -/
structure Observation where
  storedArtifacts : Nat := 0
  mutualBlocks : Nat := 0
  functions : Nat := 0
  externs : Nat := 0
  counts : Counts := {}
  codeBytes : Nat := 0
  storedArtifactBytes : Nat := 0
  deriving BEq, Repr, Inhabited

private def declarationCounts : Decl → Counts
  | .fn function => countsCode function.body
  | .extern _ => {}

private def declarationCodeBytes : Decl → Nat
  | .fn function => function.body.bytes.size
  | .extern _ => 0

private def artifactStoredBytes : ReaddressAll.Artifact → Nat
  | .stable _ declaration | .ordinary _ declaration =>
      declaration.preimage.size
  | .mutual block => MutualBlock.Block.preimage block.blockMembers |>.size

/-- Observe the exact addressed declaration graph plus its main code. -/
def observe (program : List ReaddressAll.Artifact) (main : Code) : Observation :=
  let declarations := HPT.declarationEntries program
  { storedArtifacts := program.length
    mutualBlocks := program.countP fun
      | .mutual _ => true
      | _ => false
    functions := declarations.countP fun
      | (_, .fn _) => true
      | _ => false
    externs := declarations.countP fun
      | (_, .extern _) => true
      | _ => false
    counts := declarations.foldl
      (fun total entry => total.add (declarationCounts entry.2))
      (countsCode main)
    codeBytes := declarations.foldl
      (fun total entry => total + declarationCodeBytes entry.2)
      main.bytes.size
    storedArtifactBytes := program.foldl
      (fun total artifact => total + artifactStoredBytes artifact) 0 }

/-! ## Exact graph and certificate identities -/

private def graphDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/optimizer-graph/1" ++ Encoding.tag 0

private def artifactBytes : ReaddressAll.Artifact → ByteArray
  | .stable address declaration =>
      Encoding.tag 0 ++ Encoding.address address ++
        Encoding.blob declaration.preimage
  | .ordinary address declaration =>
      Encoding.tag 1 ++ Encoding.address address ++
        Encoding.blob declaration.preimage
  | .mutual block =>
      Encoding.tag 2 ++ Encoding.address block.blockAddress ++
        Encoding.blob (MutualBlock.Block.preimage block.blockMembers)

/-- One digest commits to artifact kind/order, stable ABI rows, addressed
ordinary/mutual payloads, and the exact main code. -/
def graphRoot (program : List ReaddressAll.Artifact) (main : Code) : Address :=
  Address.blake3
    (graphDomain ++ Encoding.list artifactBytes program ++
      Encoding.blob main.bytes)

private def checkedStore (result : HPT.Result) : HPT.Cache.Store :=
  HPT.Cache.Store.ofResult result

def certificateBytes (result : HPT.Result) : Nat :=
  (checkedStore result).framedSize

def certificateRoot (result : HPT.Result) : Address :=
  Address.blake3 (HPT.Cache.encodeStore (checkedStore result))

/-! ## Versioned fail-soft policy -/

/-- Deterministic admission limits for the existing shrinking pass.  HPT
production/checking has its own limits; these bound optimizer traversal and
report inputs after a checked analysis already exists. -/
structure Budget where
  maxInputInstructions : Nat := 16 * 1024 * 1024
  maxInputCodeBytes : Nat := 64 * 1024 * 1024
  maxCertificateBytes : Nat := 64 * 1024 * 1024
  deriving BEq, Repr

structure CasePrunePolicy where
  version : Nat := currentCasePruneVersion
  enabled : Bool := true
  budget : Budget := {}
  deriving BEq, Repr

structure FetchForwardPolicy where
  version : Nat := currentFetchForwardVersion
  enabled : Bool := true
  deriving BEq, Repr

structure DestructionPolicy where
  version : Nat := currentDestructionVersion
  enabled : Bool := true
  deriving BEq, Repr

structure PAPFusePolicy where
  version : Nat := currentPAPFuseVersion
  enabled : Bool := true
  deriving BEq, Repr

structure ReachabilityPolicy where
  version : Nat := currentReachabilityVersion
  enabled : Bool := true
  /-- Additional exported declarations which must remain addressable even when
  they are not reachable from top-level main. -/
  roots : List Address := []
  deriving BEq, Repr

structure Policy where
  version : Nat := currentHarnessVersion
  casePrune : CasePrunePolicy := {}
  fetchForward : FetchForwardPolicy := {}
  destruction : DestructionPolicy := {}
  papFuse : PAPFusePolicy := {}
  reachability : ReachabilityPolicy := {}
  deriving BEq, Repr

def defaultPolicy : Policy := {}

namespace Policy

/-- Executable optimizer policy projected into the proof-facing composed
pass selection.  Keeping this projection public ensures the harness and its
semantic theorem refer to literally the same pass bundle. -/
def passes (policy : Policy) : HPT.OptimizeProgram.Passes :=
  { casePrune := policy.casePrune.enabled
    fetchForward := policy.fetchForward.enabled
    destroy := policy.destruction.enabled
    papFuse := policy.papFuse.enabled
    reachability := policy.reachability.enabled
    roots := policy.reachability.roots }

/-- Exact old-keyed declaration rows consumed by the optimizer's single
content-address rebuild. -/
def rebuildEntries (policy : Policy)
    (program : List ReaddressAll.Artifact) (summaries : HPT.SummaryEnv)
    (main : Code) : List (Address × Decl) :=
  (HPT.OptimizeProgram.selectReachable policy.passes
    (HPT.OptimizeProgram.rewriteEntries policy.passes
      (HPT.programDeclEnv program) summaries
      (HPT.declarationEntries program))
    (HPT.OptimizeProgram.rewriteMain policy.passes
      (HPT.programDeclEnv program) summaries main).code).entries

end Policy

inductive SkipReason where
  | unsupportedHarnessVersion (actual expected : Nat)
  | unsupportedPassVersion (actual expected : Nat)
  | unsupportedFetchForwardVersion (actual expected : Nat)
  | unsupportedDestructionVersion (actual expected : Nat)
  | unsupportedPAPFuseVersion (actual expected : Nat)
  | unsupportedReachabilityVersion (actual expected : Nat)
  | disabled
  | instructionBudget (actual limit : Nat)
  | codeByteBudget (actual limit : Nat)
  | certificateByteBudget (actual limit : Nat)
  | rebuildRejected
  deriving BEq, Repr

inductive Disposition where
  | skipped (reason : SkipReason)
  | unchanged
  | changed
  deriving BEq, Repr

structure Report where
  policy : Policy
  disposition : Disposition
  inputRoot : Address
  outputRoot : Address
  certificateRoot : Address
  certificateBytes : Nat
  before : Observation
  after : Observation
  removedAlternatives : Nat
  collapsedCases : Nat
  materializedFetches : Nat
  forwardedFetches : Nat
  elidedScalarDrops : Nat
  specializedUniqueDrops : Nat
  fusedPaps : Nat
  underSaturatedPaps : Nat
  exactlySaturatedPaps : Nat
  overSaturatedPaps : Nat
  removedDeclarations : Nat
  /-- Populated only when the semantics-preserving rebuild rejected and the
  harness selected the original graph. -/
  diagnostic : String := ""
  deriving BEq, Repr

private def natFields (values : List Nat) : ByteArray :=
  Encoding.list Encoding.nat values

private def Counts.bytes (counts : Counts) : ByteArray :=
  natFields
    [counts.instructions, counts.returns, counts.cases, counts.alternatives,
     counts.allocations, counts.reuses, counts.frees, counts.rcIncrements,
     counts.rcDecrements, counts.uniqueDrops, counts.fetches,
     counts.directCalls, counts.selfCalls, counts.papAllocations,
     counts.applies, counts.externCalls]

private def Observation.bytes (observation : Observation) : ByteArray :=
  natFields
      [observation.storedArtifacts, observation.mutualBlocks,
       observation.functions, observation.externs] ++
    observation.counts.bytes ++
    natFields [observation.codeBytes, observation.storedArtifactBytes]

private def Budget.bytes (budget : Budget) : ByteArray :=
  natFields [budget.maxInputInstructions, budget.maxInputCodeBytes,
    budget.maxCertificateBytes]

private def Policy.bytes (policy : Policy) : ByteArray :=
  Encoding.nat policy.version ++ Encoding.nat policy.casePrune.version ++
    Encoding.bool policy.casePrune.enabled ++ policy.casePrune.budget.bytes ++
    Encoding.nat policy.fetchForward.version ++
    Encoding.bool policy.fetchForward.enabled ++
    Encoding.nat policy.destruction.version ++
    Encoding.bool policy.destruction.enabled ++
    Encoding.nat policy.papFuse.version ++ Encoding.bool policy.papFuse.enabled ++
    Encoding.nat policy.reachability.version ++
    Encoding.bool policy.reachability.enabled ++
    Encoding.list Encoding.address policy.reachability.roots

private def SkipReason.bytes : SkipReason → ByteArray
  | .unsupportedHarnessVersion actual expected =>
      Encoding.tag 0 ++ natFields [actual, expected]
  | .unsupportedPassVersion actual expected =>
      Encoding.tag 1 ++ natFields [actual, expected]
  | .unsupportedPAPFuseVersion actual expected =>
      Encoding.tag 2 ++ natFields [actual, expected]
  | .disabled => Encoding.tag 3
  | .instructionBudget actual limit =>
      Encoding.tag 4 ++ natFields [actual, limit]
  | .codeByteBudget actual limit =>
      Encoding.tag 5 ++ natFields [actual, limit]
  | .certificateByteBudget actual limit =>
      Encoding.tag 6 ++ natFields [actual, limit]
  | .rebuildRejected => Encoding.tag 7
  | .unsupportedFetchForwardVersion actual expected =>
      Encoding.tag 8 ++ natFields [actual, expected]
  | .unsupportedReachabilityVersion actual expected =>
      Encoding.tag 9 ++ natFields [actual, expected]
  | .unsupportedDestructionVersion actual expected =>
      Encoding.tag 10 ++ natFields [actual, expected]

private def Disposition.bytes : Disposition → ByteArray
  | .skipped reason => Encoding.tag 0 ++ reason.bytes
  | .unchanged => Encoding.tag 1
  | .changed => Encoding.tag 2

namespace Report

def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/optimizer-report/6" ++ Encoding.tag 0

/-- Canonical machine-independent report spelling. -/
def bytes (report : Report) : ByteArray :=
  addressDomain ++ report.policy.bytes ++ report.disposition.bytes ++
    Encoding.address report.inputRoot ++ Encoding.address report.outputRoot ++
    Encoding.address report.certificateRoot ++
    Encoding.nat report.certificateBytes ++ report.before.bytes ++
    report.after.bytes ++ Encoding.nat report.removedAlternatives ++
    Encoding.nat report.collapsedCases ++
    Encoding.nat report.materializedFetches ++
    Encoding.nat report.forwardedFetches ++
    Encoding.nat report.elidedScalarDrops ++
    Encoding.nat report.specializedUniqueDrops ++
    Encoding.nat report.fusedPaps ++
    Encoding.nat report.underSaturatedPaps ++
    Encoding.nat report.exactlySaturatedPaps ++
    Encoding.nat report.overSaturatedPaps ++
    Encoding.nat report.removedDeclarations ++
    Encoding.string report.diagnostic

def address (report : Report) : Address :=
  Address.blake3 report.bytes

end Report

/-! ## Checked optimization execution -/

structure Outcome where
  /-- `none` means the original graph is the selected output. -/
  rebuilt : Option ReaddressAll.Result
  report : Report

namespace Outcome

def artifacts (outcome : Outcome)
    (input : List ReaddressAll.Artifact) : List ReaddressAll.Artifact :=
  outcome.rebuilt.map (fun result => result.artifacts) |>.getD input

def main (outcome : Outcome) (input : Code) : Code :=
  outcome.rebuilt.map (fun result => result.main) |>.getD input

/-- Oracle seen by the selected input program.  A rebuilt outcome pulls the
final oracle back through the optimizer's exact rebuild renaming; a skipped
outcome uses it literally. -/
def sourceOracle (outcome : Outcome) (policy : Policy)
    (program : List ReaddressAll.Artifact) (summaries : HPT.SummaryEnv)
    (main : Code) (oracle : Address → List RVal → Option RVal) :
    Address → List RVal → Option RVal :=
  match outcome.rebuilt with
  | none => oracle
  | some result => fun address arguments =>
      oracle (result.rebuildRename
        (policy.rebuildEntries program summaries main) address) arguments

/-- Old addressed program context from which the selected optimizer result is
proved. -/
def sourceCtx (outcome : Outcome) (policy : Policy)
    (program : List ReaddressAll.Artifact) (summaries : HPT.SummaryEnv)
    (main : Code) (oracle : Address → List RVal → Option RVal) : Ctx :=
  { decls := HPT.programDeclEnv program
    oracle := outcome.sourceOracle policy program summaries main oracle }

/-- Runtime context of the fail-soft selected graph. -/
def targetCtx (outcome : Outcome) (program : List ReaddressAll.Artifact)
    (oracle : Address → List RVal → Option RVal) : Ctx :=
  match outcome.rebuilt with
  | none => { decls := HPT.programDeclEnv program, oracle }
  | some result => result.addressedCtx oracle

/-- Result relation for the fail-soft harness.  Skipping is literal equality.
A successful optimization first relates logical executions modulo allocation
history, then maps declaration identities stored in the optimized heap through
the single certified rebuild. -/
def RunRefines (outcome : Outcome) (policy : Policy)
    (program : List ReaddressAll.Artifact) (summaries : HPT.SummaryEnv)
    (main : Code) (sourceOut targetOut : Store × RVal) : Prop :=
  match outcome.rebuilt with
  | none => targetOut = sourceOut
  | some result =>
      ∃ logicalOut,
        targetOut =
          (Readdress.Store.mapAddresses
            (result.rebuildRename
              (policy.rebuildEntries program summaries main)) logicalOut.1,
            logicalOut.2) ∧
          Sim.RunHistoryIso HPT.OptimizeProgram.emptyHistoryIso
            sourceOut logicalOut

/-- The proof-facing selected context uses exactly the declaration environment
committed to by `Outcome.artifacts`. -/
theorem targetCtx_decls (outcome : Outcome)
    (program : List ReaddressAll.Artifact)
    (oracle : Address → List RVal → Option RVal) :
    (outcome.targetCtx program oracle).decls =
      HPT.programDeclEnv (outcome.artifacts program) := by
  cases hrebuilt : outcome.rebuilt with
  | none => simp [targetCtx, artifacts, hrebuilt]
  | some result =>
      have henv := HPT.OptimizeProgram.envOfList_declarationEntries
        result.artifacts
      change
        Env.ofList
            (result.artifacts.flatMap ReaddressAll.Artifact.declarations) =
          HPT.programDeclEnv result.artifacts at henv
      simpa only [targetCtx, artifacts, hrebuilt, Option.map_some,
        Option.getD_some, ReaddressAll.Result.addressedCtx,
        ReaddressAll.Result.asReaddressResult,
        Readdress.Result.addressedCtx, Readdress.Result.declarations,
        List.append_nil, ReaddressAll.Result.declarations] using henv

end Outcome

private def skipReason? (policy : Policy) (before : Observation)
    (checkedBytes : Nat) : Option SkipReason :=
  if policy.version != currentHarnessVersion then
    some (.unsupportedHarnessVersion policy.version currentHarnessVersion)
  else if policy.casePrune.version != currentCasePruneVersion then
    some (.unsupportedPassVersion policy.casePrune.version
      currentCasePruneVersion)
  else if policy.fetchForward.version != currentFetchForwardVersion then
    some (.unsupportedFetchForwardVersion policy.fetchForward.version
      currentFetchForwardVersion)
  else if policy.destruction.version != currentDestructionVersion then
    some (.unsupportedDestructionVersion policy.destruction.version
      currentDestructionVersion)
  else if policy.papFuse.version != currentPAPFuseVersion then
    some (.unsupportedPAPFuseVersion policy.papFuse.version
      currentPAPFuseVersion)
  else if policy.reachability.version != currentReachabilityVersion then
    some (.unsupportedReachabilityVersion policy.reachability.version
      currentReachabilityVersion)
  else if !policy.casePrune.enabled && !policy.fetchForward.enabled &&
      !policy.destruction.enabled && !policy.papFuse.enabled &&
      !policy.reachability.enabled then
    some .disabled
  else if before.counts.instructions >
      policy.casePrune.budget.maxInputInstructions then
    some (.instructionBudget before.counts.instructions
      policy.casePrune.budget.maxInputInstructions)
  else if before.codeBytes > policy.casePrune.budget.maxInputCodeBytes then
    some (.codeByteBudget before.codeBytes
      policy.casePrune.budget.maxInputCodeBytes)
  else if checkedBytes > policy.casePrune.budget.maxCertificateBytes then
    some (.certificateByteBudget checkedBytes
      policy.casePrune.budget.maxCertificateBytes)
  else
    none

private def skippedOutcome (policy : Policy) (reason : SkipReason)
    (root checkedRoot : Address) (checkedBytes : Nat)
    (before : Observation) (diagnostic : String := "") : Outcome :=
  { rebuilt := none
    report :=
      { policy
        disposition := .skipped reason
        inputRoot := root
        outputRoot := root
        certificateRoot := checkedRoot
        certificateBytes := checkedBytes
        before
        after := before
        removedAlternatives := 0
        collapsedCases := 0
        materializedFetches := 0
        forwardedFetches := 0
        elidedScalarDrops := 0
        specializedUniqueDrops := 0
        fusedPaps := 0
        underSaturatedPaps := 0
        exactlySaturatedPaps := 0
        overSaturatedPaps := 0
        removedDeclarations := 0
        diagnostic } }

private def runChecked (policy : Policy)
    (program : List ReaddressAll.Artifact) (main : Code)
    (summaries : HPT.SummaryEnv) (analysis : HPT.Result) : Outcome :=
  let before := observe program main
  let inputRoot := graphRoot program main
  let checkedBytes := certificateBytes analysis
  let checkedRoot := certificateRoot analysis
  match skipReason? policy before checkedBytes with
  | some reason =>
      skippedOutcome policy reason inputRoot checkedRoot checkedBytes before
  | none =>
      match HPT.OptimizeProgram.rebuildProgram policy.passes [] program summaries
          main with
      | .error message =>
          skippedOutcome policy .rebuildRejected inputRoot checkedRoot
            checkedBytes before message
      | .ok pruned =>
          let after := observe pruned.result.artifacts pruned.result.main
          let outputRoot := graphRoot pruned.result.artifacts pruned.result.main
          let caseChanges := pruned.changes.casePrune
          let fetchChanges := pruned.changes.fetchForward
          let destructionChanges := pruned.changes.destroy
          let papChanges := pruned.changes.papFuse
          { rebuilt := some pruned.result
            report :=
              { policy
                disposition :=
                  if caseChanges.removedAlternatives == 0 &&
                      caseChanges.collapsedCases == 0 &&
                      caseChanges.materializedFetches == 0 &&
                      fetchChanges.forwardedFetches == 0 &&
                      destructionChanges.elidedScalarDrops == 0 &&
                      destructionChanges.specializedUniqueDrops == 0 &&
                      papChanges.fusedPaps == 0 &&
                      pruned.changes.removedDeclarations == 0 then .unchanged
                  else .changed
                inputRoot
                outputRoot
                certificateRoot := checkedRoot
                certificateBytes := checkedBytes
                before
                after
                removedAlternatives := caseChanges.removedAlternatives
                collapsedCases := caseChanges.collapsedCases
                materializedFetches := caseChanges.materializedFetches
                forwardedFetches := fetchChanges.forwardedFetches
                elidedScalarDrops := destructionChanges.elidedScalarDrops
                specializedUniqueDrops :=
                  destructionChanges.specializedUniqueDrops
                fusedPaps := papChanges.fusedPaps
                underSaturatedPaps := papChanges.underSaturated
                exactlySaturatedPaps := papChanges.exactlySaturated
                overSaturatedPaps := papChanges.overSaturated
                removedDeclarations := pruned.changes.removedDeclarations } }

/-- A selected rebuilt result can only come from the successful branch of the
same composed pass invocation used by the harness. -/
private theorem runChecked_rebuilt_eq_some
    {policy : Policy} {program : List ReaddressAll.Artifact} {main : Code}
    {summaries : HPT.SummaryEnv} {analysis : HPT.Result}
    {result : ReaddressAll.Result}
    (hselected :
      (runChecked policy program main summaries analysis).rebuilt =
        some result) :
    ∃ optimized,
      HPT.OptimizeProgram.rebuildProgram policy.passes [] program summaries
          main = .ok optimized ∧
        optimized.result = result := by
  cases hskip : skipReason? policy (observe program main)
      (certificateBytes analysis) with
  | some reason =>
      simp [runChecked, hskip, skippedOutcome] at hselected
  | none =>
      cases hrebuild : HPT.OptimizeProgram.rebuildProgram policy.passes []
          program summaries main with
      | error message =>
          simp [runChecked, hskip, hrebuild, skippedOutcome] at hselected
      | ok optimized =>
          refine ⟨optimized, rfl, ?_⟩
          simpa [runChecked, hskip, hrebuild] using hselected

/-- Run the versioned harness from an in-process HPT production that already
crossed the ordinary checker. -/
def runWithProducedHPT (policy : Policy)
    (program : List ReaddressAll.Artifact) (main : Code)
    {limits : HPT.Limits}
    (production : HPT.Production limits program) : Outcome :=
  runChecked policy program main production.certificate.summaryEnv
    production.result

/-- Cached HPT hits and rebuilt rows carry the same whole-program checked
boundary, so they can drive the identical deterministic harness. -/
def runWithCachedHPT (policy : Policy)
    (program : List ReaddressAll.Artifact) (main : Code)
    {limits : HPT.Cache.Limits}
    (production : HPT.Cache.Production limits program) : Outcome :=
  runChecked policy program main production.certificate.summaryEnv
    production.result

/-- Proof-facing inversion of the produced-HPT harness's rebuilt branch. -/
theorem rebuilt_eq_some_of_runWithProducedHPT
    {policy : Policy} {program : List ReaddressAll.Artifact} {main : Code}
    {limits : HPT.Limits} {production : HPT.Production limits program}
    {result : ReaddressAll.Result}
    (hselected :
      (runWithProducedHPT policy program main production).rebuilt =
        some result) :
    ∃ optimized,
      HPT.OptimizeProgram.rebuildProgram policy.passes [] program
          production.certificate.summaryEnv main = .ok optimized ∧
        optimized.result = result := by
  exact runChecked_rebuilt_eq_some hselected

/-- Proof-facing inversion of the cached-HPT harness's rebuilt branch. -/
theorem rebuilt_eq_some_of_runWithCachedHPT
    {policy : Policy} {program : List ReaddressAll.Artifact} {main : Code}
    {limits : HPT.Cache.Limits}
    {production : HPT.Cache.Production limits program}
    {result : ReaddressAll.Result}
    (hselected :
      (runWithCachedHPT policy program main production).rebuilt =
        some result) :
    ∃ optimized,
      HPT.OptimizeProgram.rebuildProgram policy.passes [] program
          production.certificate.summaryEnv main = .ok optimized ∧
        optimized.result = result := by
  exact runChecked_rebuilt_eq_some hselected

/-- Every directly produced fail-soft optimizer selection preserves a
successful execution at the same fuel under its explicit oracle pullback. -/
theorem runMain_of_runWithProducedHPT_eq
    {policy : Policy} {program : List ReaddressAll.Artifact} {main : Code}
    {limits : HPT.Limits} {production : HPT.Production limits program}
    {outcome : Outcome}
    (houtcome : runWithProducedHPT policy program main production = outcome)
    (oracle : Address → List RVal → Option RVal) (fuel : Nat)
    {sourceOut : Store × RVal}
    (hrun : runMain
      (outcome.sourceCtx policy program production.certificate.summaryEnv
        main oracle) main fuel = .ok sourceOut) :
    ∃ targetOut,
      runMain (outcome.targetCtx program oracle) (outcome.main main) fuel =
          .ok targetOut ∧
        outcome.RunRefines policy program production.certificate.summaryEnv
          main sourceOut targetOut := by
  cases hrebuilt : outcome.rebuilt with
  | none =>
      refine ⟨sourceOut, ?_, ?_⟩
      · simpa [Outcome.sourceCtx, Outcome.sourceOracle,
          Outcome.targetCtx, Outcome.main, hrebuilt] using hrun
      · simp [Outcome.RunRefines, hrebuilt]
  | some result =>
      have hselected :
          (runWithProducedHPT policy program main production).rebuilt =
            some result := by
        rw [houtcome, hrebuilt]
      obtain ⟨optimized, hrebuild, hresult⟩ :=
        rebuilt_eq_some_of_runWithProducedHPT hselected
      subst result
      have hsource :
          runMain
            (HPT.OptimizeProgram.rebuildOriginalCtx optimized.result
              (policy.rebuildEntries program
                production.certificate.summaryEnv main)
              (HPT.programDeclEnv program) oracle)
            main fuel = .ok sourceOut := by
        simpa [Outcome.sourceCtx, Outcome.sourceOracle, hrebuilt,
          HPT.OptimizeProgram.rebuildOriginalCtx,
          ReaddressAll.Result.rebuildSourceCtx] using hrun
      obtain ⟨logicalOut, htarget, hhistory⟩ :=
        HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok
          production.checked hrebuild oracle fuel hsource
      let targetOut : Store × RVal :=
        (Readdress.Store.mapAddresses
          (optimized.result.rebuildRename
            (policy.rebuildEntries program
              production.certificate.summaryEnv main)) logicalOut.1,
          logicalOut.2)
      refine ⟨targetOut, ?_, ?_⟩
      · simpa [targetOut, Outcome.targetCtx, Outcome.main, hrebuilt,
          Policy.rebuildEntries] using htarget
      · simp only [Outcome.RunRefines, hrebuilt]
        exact ⟨logicalOut, rfl, hhistory⟩

/-- Cached checked summaries expose the identical fail-soft successful-run
contract. -/
theorem runMain_of_runWithCachedHPT_eq
    {policy : Policy} {program : List ReaddressAll.Artifact} {main : Code}
    {limits : HPT.Cache.Limits}
    {production : HPT.Cache.Production limits program}
    {outcome : Outcome}
    (houtcome : runWithCachedHPT policy program main production = outcome)
    (oracle : Address → List RVal → Option RVal) (fuel : Nat)
    {sourceOut : Store × RVal}
    (hrun : runMain
      (outcome.sourceCtx policy program production.certificate.summaryEnv
        main oracle) main fuel = .ok sourceOut) :
    ∃ targetOut,
      runMain (outcome.targetCtx program oracle) (outcome.main main) fuel =
          .ok targetOut ∧
        outcome.RunRefines policy program production.certificate.summaryEnv
          main sourceOut targetOut := by
  cases hrebuilt : outcome.rebuilt with
  | none =>
      refine ⟨sourceOut, ?_, ?_⟩
      · simpa [Outcome.sourceCtx, Outcome.sourceOracle,
          Outcome.targetCtx, Outcome.main, hrebuilt] using hrun
      · simp [Outcome.RunRefines, hrebuilt]
  | some result =>
      have hselected :
          (runWithCachedHPT policy program main production).rebuilt =
            some result := by
        rw [houtcome, hrebuilt]
      obtain ⟨optimized, hrebuild, hresult⟩ :=
        rebuilt_eq_some_of_runWithCachedHPT hselected
      subst result
      have hsource :
          runMain
            (HPT.OptimizeProgram.rebuildOriginalCtx optimized.result
              (policy.rebuildEntries program
                production.certificate.summaryEnv main)
              (HPT.programDeclEnv program) oracle)
            main fuel = .ok sourceOut := by
        simpa [Outcome.sourceCtx, Outcome.sourceOracle, hrebuilt,
          HPT.OptimizeProgram.rebuildOriginalCtx,
          ReaddressAll.Result.rebuildSourceCtx] using hrun
      obtain ⟨logicalOut, htarget, hhistory⟩ :=
        HPT.OptimizeProgram.runMain_rebuildProgram_of_runWith_eq_ok
          production.checked hrebuild oracle fuel hsource
      let targetOut : Store × RVal :=
        (Readdress.Store.mapAddresses
          (optimized.result.rebuildRename
            (policy.rebuildEntries program
              production.certificate.summaryEnv main)) logicalOut.1,
          logicalOut.2)
      refine ⟨targetOut, ?_, ?_⟩
      · simpa [targetOut, Outcome.targetCtx, Outcome.main, hrebuilt,
          Policy.rebuildEntries] using htarget
      · simp only [Outcome.RunRefines, hrebuilt]
        exact ⟨logicalOut, rfl, hhistory⟩

end Ix.Compiler.IxIR1.Optimizer
