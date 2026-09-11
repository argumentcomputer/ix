import Ix.Compiler.IxIR1.HPTSound

/-!
# Deterministic bounded HPT certificate production

The checker deliberately trusts no producer.  This module supplies a canonical
in-process producer for callers that do not have an external analysis result.
It follows the dependency order already committed to by `ReaddressAll`: each
ordinary declaration or mutual SCC is solved from bottom against final prior
summaries, using synchronous inflationary rounds inside the artifact.

Both local and whole-schedule round counts are explicit resources. Exhausting
either round budget, or exceeding a finite-shape, field-vector, or coordinate
budget during iteration, widens only the current artifact's function rows to
`top`. The finished certificate still crosses the ordinary untrusted `runWith`
checker, so the schedule and its fallback are outside the trusted proof
boundary.
-/

namespace Ix.Compiler.IxIR1.HPT

open Ix.Compiler.Ixon (Address)

/-- Independent resource controls for deterministic production and final
checking.  `maxRounds` bounds the sum of transfer rounds across all artifacts;
`maxRoundsPerArtifact` prevents one recursive SCC from consuming it all. -/
structure ProducerLimits where
  checker : Limits := {}
  maxRoundsPerArtifact : Nat := 256
  maxRounds : Nat := 64 * 1024
  deriving BEq, Repr

def defaultProducerLimits : ProducerLimits := {}

/-- Observable deterministic schedule statistics. `widenedArtifacts` counts
artifacts forced to their conservative function facts by a round, shape, field,
or coordinate budget; it does not count a naturally inferred `top`. -/
structure ProducerStats where
  rounds : Nat := 0
  widenedArtifacts : Nat := 0
  deriving BEq, Repr, Inhabited

/-- A generated certificate together with the checked materialization and the
kernel equality witnessing that it crossed the same untrusted boundary as an
external candidate.  The equality is erased at runtime. -/
structure Production (limits : Limits)
    (program : List ReaddressAll.Artifact) where
  certificate : Certificate
  result : Result
  stats : ProducerStats
  checked : runWith limits program certificate = .ok result

private def seedFact : Decl → Fact
  | .extern _ => Fact.scalar
  | .fn _ => Fact.bottom

private def fallbackFact : Decl → Fact
  | .extern _ => Fact.scalar
  | .fn _ => Fact.top

private def seedMembers (members : List (Address × Decl)) :
    List (Address × Fact) :=
  members.map fun member => (member.1, seedFact member.2)

private def fallbackMembers (members : List (Address × Decl)) :
    List (Address × Fact) :=
  members.map fun member => (member.1, fallbackFact member.2)

private def hasFunction (members : List (Address × Decl)) : Bool :=
  members.any fun member =>
    match member.2 with
    | .fn _ => true
    | .extern _ => false

private def insertMembers (index : AddressEnv.Index Fact)
    (members : List (Address × Fact)) : AddressEnv.Index Fact :=
  members.foldl (fun current member =>
    current.insert member.1 member.2) index

private def producerEnforce (label : String) (actual limit : Nat) :
    Except String Unit :=
  if actual ≤ limit then .ok ()
  else .error s!"HPT producer {label} budget exceeded: {actual} > {limit}"

private structure ProducedPayload where
  shapes : Nat := 0
  fields : Nat := 0

private def checkProducedFact (limits : Limits) (fact : Fact) :
    Except String ProducedPayload := do
  let payload ← checkFactPayload limits fact
  return { shapes := payload.shapes, fields := payload.fields }

/-- Validate only the changing fact payload.  Full program/certificate counts
are checked once before scheduling; rescanning the entire graph per round would
turn an SCC-local solver back into a whole-program quadratic loop. -/
private def checkProducedMembers (limits : Limits) (priorShapes priorFields : Nat)
    (members : List (Address × Fact)) : Except String ProducedPayload := do
  let mut shapes := priorShapes
  let mut fields := priorFields
  for member in members do
    let payload ← checkProducedFact limits member.2
    shapes := shapes + payload.shapes
    fields := fields + payload.fields
    producerEnforce "total-shape" shapes limits.maxShapes
    producerEnforce "total-constructor-field" fields limits.maxFields
  return { shapes, fields }

private def stepMembers (declarations : DeclEnv) (summaries : SummaryEnv) :
    List (Address × Decl) → List (Address × Fact) →
      Except String (List (Address × Fact))
  | [], [] => .ok []
  | (address, declaration) :: declarations',
      (claimedAddress, previous) :: previous' => do
      if address != claimedAddress then
        throw "internal: HPT producer member alignment drift"
      let next ← match declaration with
        | .extern _ => pure Fact.scalar
        | .fn function => do
            let inferred ← inferFunction declarations summaries address function
            pure (previous.join inferred)
      let rest ← stepMembers declarations summaries declarations' previous'
      return (address, next) :: rest
  | _, _ => .error "internal: HPT producer member arity drift"

private structure ArtifactSolution where
  members : List (Address × Fact)
  summaries : AddressEnv.Index Fact
  totalShapes : Nat
  totalFields : Nat
  rounds : Nat
  remainingRounds : Nat
  widened : Bool

private def fallbackSolution (baseIndex : AddressEnv.Index Fact)
    (members : List (Address × Decl)) (priorShapes priorFields rounds remaining : Nat) :
    ArtifactSolution :=
  let facts := fallbackMembers members
  { members := facts
    summaries := insertMembers baseIndex facts
    totalShapes := priorShapes
    totalFields := priorFields
    rounds
    remainingRounds := remaining
    widened := true }

private def solveArtifactAux (limits : ProducerLimits)
    (declarations : DeclEnv) (baseIndex : AddressEnv.Index Fact)
    (declarationMembers : List (Address × Decl))
    (priorShapes priorFields : Nat) :
    Nat → Nat → List (Address × Fact) → Nat →
      Except String ArtifactSolution
  | 0, remaining, _, rounds =>
      .ok (fallbackSolution baseIndex declarationMembers priorShapes priorFields rounds
        remaining)
  | _ + 1, 0, _, rounds =>
      .ok (fallbackSolution baseIndex declarationMembers priorShapes priorFields rounds 0)
  | localRemaining + 1, totalRemaining + 1, current, rounds => do
      let currentIndex := insertMembers baseIndex current
      let next ← stepMembers declarations (AddressEnv.lookup currentIndex)
        declarationMembers current
      let rounds := rounds + 1
      match checkProducedMembers limits.checker priorShapes priorFields next with
      | .error _ =>
          return fallbackSolution baseIndex declarationMembers priorShapes
            priorFields rounds totalRemaining
      | .ok payload =>
          if next == current then
            return { members := next
                     summaries := insertMembers baseIndex next
                     totalShapes := payload.shapes
                     totalFields := payload.fields
                     rounds
                     remainingRounds := totalRemaining
                     widened := false }
          else
            solveArtifactAux limits declarations baseIndex declarationMembers
              priorShapes priorFields localRemaining totalRemaining next rounds

private def solveArtifact (limits : ProducerLimits)
    (declarations : DeclEnv) (baseIndex : AddressEnv.Index Fact)
    (members : List (Address × Decl)) (priorShapes priorFields remainingRounds : Nat) :
    Except String ArtifactSolution :=
  let seed := seedMembers members
  if hasFunction members then
    solveArtifactAux limits declarations baseIndex members priorShapes priorFields
      limits.maxRoundsPerArtifact remainingRounds seed 0
  else
    .ok
      { members := seed
        summaries := insertMembers baseIndex seed
        totalShapes := priorShapes
        totalFields := priorFields
        rounds := 0
        remainingRounds
        widened := false }

namespace Producer

/-- Artifact-local producer output used by the persistent cache scheduler.
The summary index already contains the returned rows. -/
structure ArtifactResult where
  candidate : CandidateArtifact
  summaries : AddressEnv.Index Fact
  totalShapes : Nat
  totalFields : Nat
  rounds : Nat
  remainingRounds : Nat
  widened : Bool

/-- Extend an already-built summary index with one exact artifact row set. -/
def extendSummaries (summaries : AddressEnv.Index Fact)
    (members : List (Address × Fact)) : AddressEnv.Index Fact :=
  insertMembers summaries members

/-- Apply the producer's finite-payload gates to a cache hit while retaining
the totals accumulated by earlier dependency artifacts. -/
def validatePayload (limits : Limits) (priorShapes priorFields : Nat)
    (members : List (Address × Fact)) : Except String (Nat × Nat) := do
  let payload ← checkProducedMembers limits priorShapes priorFields members
  return (payload.shapes, payload.fields)

/-- Produce exactly one dependency-ordered program artifact against fixed
prior summaries. This is the same solver used by whole-program production; it
is exposed so cache misses can rebuild locally instead of discarding unrelated
hits. -/
def produceArtifactWith (limits : ProducerLimits) (declarations : DeclEnv)
    (summaries : AddressEnv.Index Fact) (program : ReaddressAll.Artifact)
    (priorShapes priorFields remainingRounds : Nat) :
    Except String ArtifactResult := do
  let solved ← solveArtifact limits declarations summaries
    (programMembers program) priorShapes priorFields remainingRounds
  let candidate : CandidateArtifact :=
    { programIdentity := Ix.Compiler.IxIR1.HPT.programIdentity program
      members := solved.members }
  pure ⟨candidate, solved.summaries, solved.totalShapes, solved.totalFields,
    solved.rounds, solved.remainingRounds, solved.widened⟩

end Producer

private structure ScheduleState where
  artifactsRev : List CandidateArtifact := []
  summaries : AddressEnv.Index Fact := AddressEnv.build []
  totalShapes : Nat := 0
  totalFields : Nat := 0
  rounds : Nat := 0
  remainingRounds : Nat := 0
  widenedArtifacts : Nat := 0

private def solveArtifacts (limits : ProducerLimits)
    (declarations : DeclEnv) :
    List ReaddressAll.Artifact → ScheduleState → Except String ScheduleState
  | [], state => .ok state
  | artifact :: artifacts, state => do
      let members := programMembers artifact
      let solved ← solveArtifact limits declarations state.summaries members
        state.totalShapes state.totalFields state.remainingRounds
      let candidate : CandidateArtifact :=
        { programIdentity := programIdentity artifact
          members := solved.members }
      solveArtifacts limits declarations artifacts
        { artifactsRev := candidate :: state.artifactsRev
          summaries := solved.summaries
          totalShapes := solved.totalShapes
          totalFields := solved.totalFields
          rounds := state.rounds + solved.rounds
          remainingRounds := solved.remainingRounds
          widenedArtifacts := state.widenedArtifacts +
            (if solved.widened then 1 else 0) }

/-- Produce the deterministic candidate and its schedule statistics.  The
result has exact program/artifact/member layout but has not yet been assigned
cache identities; use `produceWith` at an external boundary. -/
def produceCertificateWith (limits : ProducerLimits)
    (program : List ReaddressAll.Artifact) :
    Except String (Certificate × ProducerStats) := do
  let _ ← preflight limits.checker program (Certificate.top program)
  let declarations := programDeclEnv program
  let state ← solveArtifacts limits declarations program
    { remainingRounds := limits.maxRounds }
  return (⟨state.artifactsRev.reverse⟩,
    { rounds := state.rounds
      widenedArtifacts := state.widenedArtifacts })

def produceCertificate (program : List ReaddressAll.Artifact) :
    Except String (Certificate × ProducerStats) :=
  produceCertificateWith defaultProducerLimits program

/-- Produce, validate, and content-address one deterministic HPT result. -/
def produceWith (limits : ProducerLimits)
    (program : List ReaddressAll.Artifact) :
    Except String (Production limits.checker program) := do
  let (certificate, stats) ← produceCertificateWith limits program
  match hrun : runWith limits.checker program certificate with
  | .error error => .error error
  | .ok result =>
      .ok { certificate, result, stats, checked := hrun }

def produce (program : List ReaddressAll.Artifact) :
    Except String (Production defaultProducerLimits.checker program) :=
  produceWith defaultProducerLimits program

namespace Production

theorem postFixpoint {limits : Limits} {program : List ReaddressAll.Artifact}
    (production : Production limits program) :
    production.certificate.postFixpoint program = true :=
  postFixpoint_of_runWith_eq_ok production.checked

theorem semanticAudit {limits : Limits} {program : List ReaddressAll.Artifact}
    (production : Production limits program) :
    production.result.semanticAudit = true :=
  semanticAudit_of_runWith_eq_ok production.checked

/-- Every generated function row has the same concrete evaluator guarantee as
an externally supplied accepted certificate. -/
theorem functionSummary_sound
    {limits : Limits} {program : List ReaddressAll.Artifact}
    (production : Production limits program)
    {ctx : Ctx} {address : Address} {function : FnDef} {claimed : Fact}
    {arguments : List RVal} {store outputStore : Store}
    {outputValue : RVal} {fuel : Nat}
    (hctx : ctx.decls = programDeclEnv program)
    (hdeclaration : programDeclEnv program address = some (.fn function))
    (hsummary : production.certificate.summaryEnv address = some claimed)
    (hinvoke : invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds (programDeclEnv program) outputStore outputValue := by
  exact functionSummary_sound_of_runWith_eq_ok production.checked hctx
    hdeclaration hsummary hinvoke

end Production

end Ix.Compiler.IxIR1.HPT
