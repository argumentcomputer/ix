import Compilatrix.IxIR1.HPTCache
import Compilatrix.IxIR1.HPTPAPFuseProgram

/-!
# Deterministic IxIR₁ optimizer harness

This module is the O0 control and observation boundary for whole-program
IxIR₁ optimization.  It wraps the checked, fact-propagating HPT case
simplifier (impossible-alternative pruning plus exact unary case collapse)
and the opt-in O1 local PAP/application fusion pass with:

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

namespace Compilatrix.IxIR1.Optimizer

open Compilatrix.Ixon (Address)
open Compilatrix.IxIR

def currentHarnessVersion : Nat := 2
def currentCasePruneVersion : Nat := 3
def currentPAPFuseVersion : Nat := 1

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

structure PAPFusePolicy where
  version : Nat := currentPAPFuseVersion
  /-- Opt-in until the local heap-history refinement is lifted through the
  complete declaration-context rewrite. -/
  enabled : Bool := false
  deriving BEq, Repr

structure Policy where
  version : Nat := currentHarnessVersion
  casePrune : CasePrunePolicy := {}
  papFuse : PAPFusePolicy := {}
  deriving BEq, Repr

def defaultPolicy : Policy := {}

inductive SkipReason where
  | unsupportedHarnessVersion (actual expected : Nat)
  | unsupportedPassVersion (actual expected : Nat)
  | unsupportedPAPFuseVersion (actual expected : Nat)
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
  fusedPaps : Nat
  underSaturatedPaps : Nat
  exactlySaturatedPaps : Nat
  overSaturatedPaps : Nat
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
    Encoding.nat policy.papFuse.version ++ Encoding.bool policy.papFuse.enabled

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

private def Disposition.bytes : Disposition → ByteArray
  | .skipped reason => Encoding.tag 0 ++ reason.bytes
  | .unchanged => Encoding.tag 1
  | .changed => Encoding.tag 2

namespace Report

def addressDomain : ByteArray :=
  Encoding.domain "compilatrix/ixir1/optimizer-report/3" ++ Encoding.tag 0

/-- Canonical machine-independent report spelling. -/
def bytes (report : Report) : ByteArray :=
  addressDomain ++ report.policy.bytes ++ report.disposition.bytes ++
    Encoding.address report.inputRoot ++ Encoding.address report.outputRoot ++
    Encoding.address report.certificateRoot ++
    Encoding.nat report.certificateBytes ++ report.before.bytes ++
    report.after.bytes ++ Encoding.nat report.removedAlternatives ++
    Encoding.nat report.collapsedCases ++
    Encoding.nat report.materializedFetches ++
    Encoding.nat report.fusedPaps ++
    Encoding.nat report.underSaturatedPaps ++
    Encoding.nat report.exactlySaturatedPaps ++
    Encoding.nat report.overSaturatedPaps ++
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

end Outcome

private def skipReason? (policy : Policy) (before : Observation)
    (checkedBytes : Nat) : Option SkipReason :=
  if policy.version != currentHarnessVersion then
    some (.unsupportedHarnessVersion policy.version currentHarnessVersion)
  else if policy.casePrune.version != currentCasePruneVersion then
    some (.unsupportedPassVersion policy.casePrune.version
      currentCasePruneVersion)
  else if policy.papFuse.version != currentPAPFuseVersion then
    some (.unsupportedPAPFuseVersion policy.papFuse.version
      currentPAPFuseVersion)
  else if !policy.casePrune.enabled && !policy.papFuse.enabled then
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
        fusedPaps := 0
        underSaturatedPaps := 0
        exactlySaturatedPaps := 0
        overSaturatedPaps := 0
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
      let passes : HPT.OptimizeProgram.Passes :=
        { casePrune := policy.casePrune.enabled
          papFuse := policy.papFuse.enabled }
      match HPT.OptimizeProgram.rebuildProgram passes [] program summaries
          main with
      | .error message =>
          skippedOutcome policy .rebuildRejected inputRoot checkedRoot
            checkedBytes before message
      | .ok pruned =>
          let after := observe pruned.result.artifacts pruned.result.main
          let outputRoot := graphRoot pruned.result.artifacts pruned.result.main
          let caseChanges := pruned.changes.casePrune
          let papChanges := pruned.changes.papFuse
          { rebuilt := some pruned.result
            report :=
              { policy
                disposition :=
                  if caseChanges.removedAlternatives == 0 &&
                      caseChanges.collapsedCases == 0 &&
                      caseChanges.materializedFetches == 0 &&
                      papChanges.fusedPaps == 0 then .unchanged
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
                fusedPaps := papChanges.fusedPaps
                underSaturatedPaps := papChanges.underSaturated
                exactlySaturatedPaps := papChanges.exactlySaturated
                overSaturatedPaps := papChanges.overSaturated } }

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

end Compilatrix.IxIR1.Optimizer
