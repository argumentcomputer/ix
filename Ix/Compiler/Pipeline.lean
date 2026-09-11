import Ix.Compiler.Ixon.UsageCheck
import Ix.Compiler.Ixon.Work
import Ix.Compiler.EraseAddressed
import Ix.Compiler.EraseValidator
import Ix.Compiler.IxIR1.LowerFullyAddressed
import Ix.Compiler.IxIR1.HPTCacheDirIO
import Ix.Compiler.IxIR1.Optimizer

/-!
# Checked source-to-IxIR₁ pipeline

The first executable composition of the three previously independent
gatekeepers:

1. every Ixon constant passes `UsageCheck.checkConstant` against the
   same closed-world resolver;
2. the checked program is erased through `EraseAddressed.run`, retaining the
   exact legacy erasure while replacing mutual-member temporary keys by
   canonical block-derived keys;
3. the addressed IxIR₀ declarations are lowered, the complete IxIR₁ graph
   is partitioned into SCCs, and source/generated functions are rekeyed to
   ordinary declaration hashes or cycle-safe mutual-block identities.  Opaque
   extern keys and constructor identities remain stable.

`compile` is the unvalidated engineering gate: it deliberately accepts
out-of-fragment programs that the proof-producing validator cannot yet
certify. `compileValidated` closes that seam with the sharing-aware validator,
failing closed on the first rejected declaration. Its proof-facing sibling,
`compileValidatedWithTrace`, retains the exact member scope, erasure
certificate, simultaneous-member coverage, and lowering/addressing equations
consumed by `PipelineSound`. It also rejects externs on the exact addressed
IxIR₀ input and emitted IxIR₁ graph, retaining both checks as proof fields.
The resulting semantic endpoint keeps only genuine source execution and
oracle-correspondence obligations explicit.
-/

namespace Ix.Compiler.Pipeline

open Ix.Compiler.Ixon (Address Constant Owned)

inductive Error where
  | usage (address : Address) (error : Ixon.UsageCheck.UsageErr)
  | erase (error : Erase.EraseErr)
  | readdress (message : String)
  /-- The erasure validator rejected this declaration (or the main
  entry) with the given diagnostic — `compileValidated` only. -/
  | validate (address : Address) (message : String)
  | lower (message : String)
  | resource (exceeded : Ixon.Work.Exceeded)
  deriving BEq, Repr

/-- Inclusive structural limits for one compilation unit.  These are
deterministic preflight counters, not machine-dependent timeouts.  The
certificate limits deliberately bound both proof-database size and the
quadratic dependency-discovery fixpoint. -/
structure Limits where
  maxConstants : Nat := 16 * 1024
  maxExpressionUnits : Nat := 1024 * 1024
  maxExpandedExpressionUnits : Nat := 1024 * 1024
  maxLayer1NodeVisits : Nat := 64 * 1024 * 1024
  maxErasedDeclarations : Nat := 32 * 1024
  maxErasureAppendCells : Nat := 64 * 1024 * 1024
  maxCertificateCandidates : Nat := 512
  maxCertificateValidationAttempts : Nat := 512 * 513 / 2 + 512
  maxCertificateSourceNodeWork : Nat := 128 * 1024 * 1024
  maxUsageFuel : Nat := Ixon.UsageCheck.defaultFuel
  maxErasureFuel : Nat := Erase.defaultFuel
  maxValidationFuel : Nat := Erase.defaultFuel
  maxLoweringFuel : Nat := 100000
  deriving BEq, Repr

def defaultLimits : Limits := {}

/-- Non-constant inputs needed while erasing a closed Ixon program. -/
structure Config where
  blobs : Address → Option Ixon.Eval.Blob := fun _ => none
  natBlock : Option Address := none
  limits : Limits := {}

/-- Locate the first extern declaration at the validator-to-lowerer boundary.
The certified pipeline stays closed to externs until a heap ownership ABI is
chosen; the unvalidated engineering pipeline retains the evaluator's
scalar-only extern support. -/
def firstValidatedExtern? : List (Address × IxIR0.Decl) → Option Address
  | [] => none
  | (address, .extern _) :: _ => some address
  | _ :: declarations => firstValidatedExtern? declarations

/-- Executable proof-facing statement of the validated extern policy. -/
def ValidatedExternsRejected
    (declarations : List (Address × IxIR0.Decl)) : Prop :=
  firstValidatedExtern? declarations = none

/-- Target-side twin of `firstValidatedExtern?`, run over the exact emitted
artifact graph rather than inferred from lowering behavior. -/
def firstValidatedTargetExtern? :
    List (Address × IxIR1.Decl) → Option Address
  | [] => none
  | (address, .extern _) :: _ => some address
  | _ :: declarations => firstValidatedTargetExtern? declarations

/-- The emitted certified IxIR₁ graph is closed to extern declarations. -/
def ValidatedTargetExternsRejected
    (declarations : List (Address × IxIR1.Decl)) : Prop :=
  firstValidatedTargetExtern? declarations = none

namespace ValidatedExternsRejected

/-- A closed validated extern boundary excludes every extern row from the
exact declaration list. -/
theorem not_mem {declarations : List (Address × IxIR0.Decl)}
    (hboundary : ValidatedExternsRejected declarations)
    {address : Address} {arity : Nat} :
    (address, .extern arity) ∉ declarations := by
  intro hmember
  induction declarations with
  | nil => simp at hmember
  | cons head tail ih =>
      rcases head with ⟨headAddress, headDeclaration⟩
      cases headDeclaration <;>
        simp_all [ValidatedExternsRejected, firstValidatedExtern?]

private theorem envOfList_some_mem
    {declarations : List (Address × IxIR0.Decl)} {address : Address}
    {declaration : IxIR0.Decl}
    (hlookup : IxIR0.Env.ofList declarations address = some declaration) :
    (address, declaration) ∈ declarations := by
  unfold IxIR0.Env.ofList at hlookup
  obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryDeclaration⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Address × IxIR0.Decl => entry.1 == address) hfind
  have haddress : entryAddress = address := Address.eq_of_beq hbeq
  have hdeclaration : entryDeclaration = declaration := by
    simpa using hvalue
  subst entryAddress
  subst entryDeclaration
  exact List.mem_of_find?_eq_some hfind

/-- The proof-facing list certificate rules out extern lookup through the
actual first-binding-wins IxIR₀ environment used by validation. -/
theorem env_ne_extern {declarations : List (Address × IxIR0.Decl)}
    (hboundary : ValidatedExternsRejected declarations)
    {address : Address} {arity : Nat} :
    IxIR0.Env.ofList declarations address ≠ some (.extern arity) := by
  intro hlookup
  exact hboundary.not_mem (envOfList_some_mem hlookup)

end ValidatedExternsRejected

namespace ValidatedTargetExternsRejected

/-- The target certificate excludes every extern row from the exact emitted
artifact list. -/
theorem not_mem {declarations : List (Address × IxIR1.Decl)}
    (hboundary : ValidatedTargetExternsRejected declarations)
    {address : Address} {arity : Nat} :
    (address, .extern arity) ∉ declarations := by
  intro hmember
  induction declarations with
  | nil => simp at hmember
  | cons head tail ih =>
      rcases head with ⟨headAddress, headDeclaration⟩
      cases headDeclaration <;>
        simp_all [ValidatedTargetExternsRejected,
          firstValidatedTargetExtern?]

private theorem lookupBuild_some_mem {α : Type}
    {declarations : List (Address × α)} {address : Address} {value : α}
    (hlookup : AddressEnv.lookup (AddressEnv.build declarations) address =
      some value) :
    (address, value) ∈ declarations := by
  rw [AddressEnv.lookup_build_apply] at hlookup
  obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryValue⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Address × α => entry.1 == address) hfind
  have haddress : entryAddress = address := Address.eq_of_beq hbeq
  have hentryValue : entryValue = value := by simpa using hvalue
  subst entryAddress
  subst entryValue
  exact List.mem_of_find?_eq_some hfind

/-- The target list certificate also rules out extern lookup through the
indexed first-binding-wins environment used by artifact consumers. -/
theorem env_ne_extern {declarations : List (Address × IxIR1.Decl)}
    (hboundary : ValidatedTargetExternsRejected declarations)
    {address : Address} {arity : Nat} :
    AddressEnv.lookup (AddressEnv.build declarations) address ≠
      some (.extern arity) := by
  intro hlookup
  exact hboundary.not_mem (lookupBuild_some_mem hlookup)

end ValidatedTargetExternsRejected

/-- The executable compiler boundaries, retained together so validators and
artifact consumers can inspect both the theorem-facing legacy erasure and the
cycle-safe addressed program. -/
structure Artifact where
  /-- Exact output of the existing proof-facing eraser. -/
  rawErasedDecls : List (Address × IxIR0.Decl)
  /-- Executable IxIR₀ environment after mutual-block readdressing. -/
  erasedDecls : List (Address × IxIR0.Decl)
  erasedBlocks : List IxIR0.MutualBlock.Result
  /-- Legacy mutual-member key to final block-derived key. -/
  erasedAddressMap : IxIR0.MutualBlock.Renaming
  /-- Dependency-ordered stable, ordinary, and mutual target artifacts. -/
  targetArtifacts : List IxIR1.ReaddressAll.Artifact
  main : IxIR1.Code
  /-- Complete raw IxIR₁ producer name to emitted identity map.  It includes
  identity entries for stable extern ABI declarations; no nonidentity domain
  key remains in the target declarations or main code. -/
  targetAddressMap : IxIR1.ReaddressAll.Renaming

namespace Artifact

/-- Flat evaluator environment projected from the richer target artifacts. -/
def targetDecls (artifact : Artifact) : List (Address × IxIR1.Decl) :=
  artifact.targetArtifacts.flatMap IxIR1.ReaddressAll.Artifact.declarations

/-- The exact evaluator declaration environment committed to by the target
artifact graph and used to interpret checked HPT facts. -/
def targetDeclEnv (artifact : Artifact) : IxIR1.Env :=
  IxIR1.HPT.programDeclEnv artifact.targetArtifacts

def targetBlocks (artifact : Artifact) : List IxIR1.MutualBlock.Result :=
  artifact.targetArtifacts.filterMap fun
    | .stable _ _ | .ordinary _ _ => none
    | .mutual block => some block

/-- Install a rebuilt target graph while composing the compiler's original
producer-to-target map through the old-target-to-new-target rebuild map. -/
def withRebuiltTarget (artifact : Artifact)
    (result : IxIR1.ReaddressAll.Result) : Artifact :=
  { artifact with
    targetArtifacts := result.artifacts
    main := result.main
    targetAddressMap := artifact.targetAddressMap.map fun mapping =>
      (mapping.1, IxIR1.Readdress.Renaming.apply result.addressMap mapping.2) }

/-- Resource-configurable validation and cache addressing of an untrusted HPT
result against this artifact's exact dependency-ordered target graph. -/
def checkHPTWith (artifact : Artifact) (limits : IxIR1.HPT.Limits)
    (certificate : IxIR1.HPT.Certificate) :
    Except String IxIR1.HPT.Result :=
  IxIR1.HPT.runWith limits artifact.targetArtifacts certificate

/-- Default-budget HPT checking. Analysis remains optional until an
optimization consumes it; callers cannot substitute a different program. -/
def checkHPT (artifact : Artifact) (certificate : IxIR1.HPT.Certificate) :
    Except String IxIR1.HPT.Result :=
  artifact.checkHPTWith IxIR1.HPT.defaultLimits certificate

/-- Deterministically produce, validate, and content-address an HPT
certificate for this artifact's exact target graph. -/
def produceHPTWith (artifact : Artifact)
    (limits : IxIR1.HPT.ProducerLimits) :
    Except String
      (IxIR1.HPT.Production limits.checker artifact.targetArtifacts) :=
  IxIR1.HPT.produceWith limits artifact.targetArtifacts

def produceHPT (artifact : Artifact) :
    Except String
      (IxIR1.HPT.Production IxIR1.HPT.defaultProducerLimits.checker
        artifact.targetArtifacts) :=
  artifact.produceHPTWith IxIR1.HPT.defaultProducerLimits

/-- Validate dependency-addressed persistent cache hits and rebuild misses
artifact-locally before crossing the ordinary whole-program HPT checker. -/
def produceHPTCachedWith (artifact : Artifact)
    (limits : IxIR1.HPT.Cache.Limits) (store : IxIR1.HPT.Cache.Store) :
    Except String
      (IxIR1.HPT.Cache.Production limits artifact.targetArtifacts) :=
  IxIR1.HPT.Cache.runWith limits artifact.targetArtifacts store

def produceHPTCached (artifact : Artifact)
    (store : IxIR1.HPT.Cache.Store) :
    Except String
      (IxIR1.HPT.Cache.Production IxIR1.HPT.Cache.defaultLimits
        artifact.targetArtifacts) :=
  artifact.produceHPTCachedWith IxIR1.HPT.Cache.defaultLimits store

/-- Persistent specialization: cold-start an absent file, validate every
present hit against this artifact, rebuild misses, and save the merged store. -/
def produceHPTCachedFileWith (artifact : Artifact)
    (limits : IxIR1.HPT.Cache.Limits) (path : System.FilePath) :
    IO (Except IxIR1.HPT.CacheIO.Error
      (IxIR1.HPT.Cache.Production limits artifact.targetArtifacts)) :=
  IxIR1.HPT.CacheIO.refreshFileWith limits artifact.targetArtifacts path

def produceHPTCachedFile (artifact : Artifact) (path : System.FilePath) :
    IO (Except IxIR1.HPT.CacheIO.Error
      (IxIR1.HPT.Cache.Production IxIR1.HPT.Cache.defaultLimits
        artifact.targetArtifacts)) :=
  artifact.produceHPTCachedFileWith IxIR1.HPT.Cache.defaultLimits path

/-- Scaling specialization: index canonical per-key chunks without retaining
their payloads, lazily read only dependency-selected records, rebuild local
misses/rejections, and durably publish each changed chunk. -/
def produceHPTCachedDirectoryWith (artifact : Artifact)
    (limits : IxIR1.HPT.CacheDirIO.Limits) (directory : System.FilePath) :
    IO (Except IxIR1.HPT.CacheIO.Error
      (IxIR1.HPT.Cache.Production limits.cache artifact.targetArtifacts)) :=
  IxIR1.HPT.CacheDirIO.refreshDirectoryWith limits artifact.targetArtifacts
    directory

def produceHPTCachedDirectory (artifact : Artifact)
    (directory : System.FilePath) :
    IO (Except IxIR1.HPT.CacheIO.Error
      (IxIR1.HPT.Cache.Production IxIR1.HPT.CacheDirIO.defaultLimits.cache
        artifact.targetArtifacts)) :=
  artifact.produceHPTCachedDirectoryWith
    IxIR1.HPT.CacheDirIO.defaultLimits directory

/-! ## First checked HPT consumer -/

/-- Check an untrusted HPT certificate against this exact artifact graph and
then use it to prune one root `call`→`case` redex. -/
def checkAndPruneCaseWith (artifact : Artifact) (limits : IxIR1.HPT.Limits)
    (certificate : IxIR1.HPT.Certificate) (input : IxIR1.Code) :
    Except String (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.Outcome) := do
  let analysis ← artifact.checkHPTWith limits certificate
  return (analysis, IxIR1.HPT.CasePrune.run artifact.targetDeclEnv
    certificate.summaryEnv input)

def checkAndPruneCase (artifact : Artifact)
    (certificate : IxIR1.HPT.Certificate) (input : IxIR1.Code) :
    Except String (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.Outcome) :=
  artifact.checkAndPruneCaseWith IxIR1.HPT.defaultLimits certificate input

/-- Directly produced summaries have already crossed the same checker. -/
def pruneCaseWithProducedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts)
    (input : IxIR1.Code) : IxIR1.HPT.CasePrune.Outcome :=
  IxIR1.HPT.CasePrune.run artifact.targetDeclEnv
    production.certificate.summaryEnv input

/-- Cached hits and local rebuilds likewise carry whole-program checker
evidence before they can drive the consumer. -/
def pruneCaseWithCachedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts)
    (input : IxIR1.Code) : IxIR1.HPT.CasePrune.Outcome :=
  IxIR1.HPT.CasePrune.run artifact.targetDeclEnv
    production.certificate.summaryEnv input

/-- Check an untrusted HPT certificate and recursively prune every eligible
`call`→`case` redex in the supplied code fragment. -/
def checkAndPruneCasesRecursiveWith (artifact : Artifact)
    (limits : IxIR1.HPT.Limits) (certificate : IxIR1.HPT.Certificate)
    (input : IxIR1.Code) :
    Except String (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.Outcome) := do
  let analysis ← artifact.checkHPTWith limits certificate
  return (analysis, IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
    certificate.summaryEnv input)

def checkAndPruneCasesRecursive (artifact : Artifact)
    (certificate : IxIR1.HPT.Certificate) (input : IxIR1.Code) :
    Except String (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.Outcome) :=
  artifact.checkAndPruneCasesRecursiveWith IxIR1.HPT.defaultLimits
    certificate input

/-- Recursively consume a directly produced, already checked summary. -/
def pruneCasesRecursiveWithProducedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts)
    (input : IxIR1.Code) : IxIR1.HPT.CasePrune.Outcome :=
  IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
    production.certificate.summaryEnv input

/-- Recursively consume a persistent-cache production, whose hits and
rebuilt misses have crossed whole-program checking. -/
def pruneCasesRecursiveWithCachedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts)
    (input : IxIR1.Code) : IxIR1.HPT.CasePrune.Outcome :=
  IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
    production.certificate.summaryEnv input

/-- Check a certificate and recursively prune the artifact's unhashed main.
The resulting main is safe for `runMain`, including `callSelf` re-entry. -/
def checkAndPruneMainWith (artifact : Artifact) (limits : IxIR1.HPT.Limits)
    (certificate : IxIR1.HPT.Certificate) :
    Except String (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.Outcome) := do
  let analysis ← artifact.checkHPTWith limits certificate
  return (analysis, IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
    certificate.summaryEnv artifact.main)

def checkAndPruneMain (artifact : Artifact)
    (certificate : IxIR1.HPT.Certificate) :
    Except String (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.Outcome) :=
  artifact.checkAndPruneMainWith IxIR1.HPT.defaultLimits certificate

/-- Recursively prune the main with a directly produced checked summary. -/
def pruneMainWithProducedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts) :
    IxIR1.HPT.CasePrune.Outcome :=
  IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
    production.certificate.summaryEnv artifact.main

/-- Recursively prune the main with a checked persistent-cache production. -/
def pruneMainWithCachedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts) :
    IxIR1.HPT.CasePrune.Outcome :=
  IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
    production.certificate.summaryEnv artifact.main

/-! ## Readdressed declaration-graph case pruning -/

/-- Check an untrusted HPT certificate, recursively prune every stored
function body and the main, and rebuild all affected content addresses.  The
returned HPT analysis describes the input graph and must not be reused as a
certificate for the rebuilt graph. -/
def checkAndPruneProgramWith (artifact : Artifact)
    (limits : IxIR1.HPT.Limits) (certificate : IxIR1.HPT.Certificate) :
    Except String
      (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.ProgramOutcome) := do
  let analysis ← artifact.checkHPTWith limits certificate
  let outcome ← IxIR1.HPT.CasePrune.rebuildProgram []
    artifact.targetArtifacts certificate.summaryEnv artifact.main
  return (analysis, outcome)

def checkAndPruneProgram (artifact : Artifact)
    (certificate : IxIR1.HPT.Certificate) :
    Except String
      (IxIR1.HPT.Result × IxIR1.HPT.CasePrune.ProgramOutcome) :=
  artifact.checkAndPruneProgramWith IxIR1.HPT.defaultLimits certificate

/-- Rebuild a complete program using a directly produced checked summary. -/
def pruneProgramWithProducedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts) :
    Except String IxIR1.HPT.CasePrune.ProgramOutcome :=
  IxIR1.HPT.CasePrune.rebuildProgram [] artifact.targetArtifacts
    production.certificate.summaryEnv artifact.main

/-- Rebuild a complete program using a checked persistent-cache production. -/
def pruneProgramWithCachedHPT (artifact : Artifact)
    {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts) :
    Except String IxIR1.HPT.CasePrune.ProgramOutcome :=
  IxIR1.HPT.CasePrune.rebuildProgram [] artifact.targetArtifacts
    production.certificate.summaryEnv artifact.main

/-- Materialize the pipeline artifact represented by a successful complete
program pruning outcome. -/
def installPrunedProgram (artifact : Artifact)
    (outcome : IxIR1.HPT.CasePrune.ProgramOutcome) : Artifact :=
  artifact.withRebuiltTarget outcome.result

/-- Logical old-keyed declaration rows supplied to the rebuild stage. -/
def prunedTargetEntries (artifact : Artifact)
    (summaries : IxIR1.HPT.SummaryEnv) :
    List (Address × IxIR1.Decl) :=
  IxIR1.HPT.CasePrune.rewriteEntries
    (IxIR1.HPT.programDeclEnv artifact.targetArtifacts) summaries
    (IxIR1.HPT.declarationEntries artifact.targetArtifacts)

/-- Source evaluator context paired with a rebuilt graph's oracle pullback. -/
def pruneProgramSourceCtx (artifact : Artifact)
    (summaries : IxIR1.HPT.SummaryEnv)
    (outcome : IxIR1.HPT.CasePrune.ProgramOutcome)
    (oracle : Address → List IxIR1.RVal → Option IxIR1.RVal) : IxIR1.Ctx :=
  IxIR1.HPT.CasePrune.rebuildOriginalCtx outcome.result
    (artifact.prunedTargetEntries summaries)
    (IxIR1.HPT.programDeclEnv artifact.targetArtifacts) oracle

/-- Checked complete-graph pruning transports the full evaluator result,
including address-bearing heap nodes and errors. -/
theorem runMain_pruneProgram_of_checkHPTWith_eq_ok
    {artifact : Artifact} {limits : IxIR1.HPT.Limits}
    {certificate : IxIR1.HPT.Certificate} {analysis : IxIR1.HPT.Result}
    {outcome : IxIR1.HPT.CasePrune.ProgramOutcome}
    (hcheck : artifact.checkHPTWith limits certificate = .ok analysis)
    (hrebuild : IxIR1.HPT.CasePrune.rebuildProgram []
      artifact.targetArtifacts certificate.summaryEnv artifact.main =
      .ok outcome)
    (oracle : Address → List IxIR1.RVal → Option IxIR1.RVal :=
      fun _ _ => none)
    (fuel : Nat := 100000) :
    IxIR1.runMain (outcome.result.addressedCtx oracle)
        outcome.result.main fuel =
      IxIR1.Readdress.mapRunResult
        (outcome.result.rebuildRename
          (artifact.prunedTargetEntries certificate.summaryEnv))
        (IxIR1.runMain
          (artifact.pruneProgramSourceCtx certificate.summaryEnv
            outcome oracle)
          artifact.main fuel) := by
  exact IxIR1.HPT.CasePrune.runMain_rebuildProgram_of_runWith_eq_ok
    (by simpa [checkHPTWith] using hcheck) hrebuild oracle fuel

/-- One successful combined pipeline call carries both checker and rebuild
evidence needed by the complete evaluator transport theorem. -/
theorem runMain_pruneProgram_of_checkAndPruneProgramWith_eq_ok
    {artifact : Artifact} {limits : IxIR1.HPT.Limits}
    {certificate : IxIR1.HPT.Certificate} {analysis : IxIR1.HPT.Result}
    {outcome : IxIR1.HPT.CasePrune.ProgramOutcome}
    (hrun : artifact.checkAndPruneProgramWith limits certificate =
      .ok (analysis, outcome))
    (oracle : Address → List IxIR1.RVal → Option IxIR1.RVal :=
      fun _ _ => none)
    (fuel : Nat := 100000) :
    IxIR1.runMain (outcome.result.addressedCtx oracle)
        outcome.result.main fuel =
      IxIR1.Readdress.mapRunResult
        (outcome.result.rebuildRename
          (artifact.prunedTargetEntries certificate.summaryEnv))
        (IxIR1.runMain
          (artifact.pruneProgramSourceCtx certificate.summaryEnv
            outcome oracle)
          artifact.main fuel) := by
  unfold checkAndPruneProgramWith at hrun
  simp only [bind, Except.bind] at hrun
  cases hcheck : artifact.checkHPTWith limits certificate with
  | error message =>
      rw [hcheck] at hrun
      contradiction
  | ok checked =>
      rw [hcheck] at hrun
      cases hrebuild : IxIR1.HPT.CasePrune.rebuildProgram []
          artifact.targetArtifacts certificate.summaryEnv artifact.main with
      | error message =>
          rw [hrebuild] at hrun
          contradiction
      | ok rebuilt =>
          rw [hrebuild] at hrun
          have hpair : (checked, rebuilt) = (analysis, outcome) := by
            injection hrun
          have hanalysis : checked = analysis := congrArg Prod.fst hpair
          have houtcome : rebuilt = outcome := congrArg Prod.snd hpair
          subst analysis
          subst outcome
          exact runMain_pruneProgram_of_checkHPTWith_eq_ok
            hcheck hrebuild oracle fuel

/-- Checked pipeline specialization of the core exact evaluator theorem. -/
theorem runCode_pruneCase_of_checkHPTWith_eq_ok
    {artifact : Artifact} {limits : IxIR1.HPT.Limits}
    {certificate : IxIR1.HPT.Certificate} {analysis : IxIR1.HPT.Result}
    (hcheck : artifact.checkHPTWith limits certificate = .ok analysis)
    {ctx : IxIR1.Ctx} {current : IxIR1.FnDef} {store : IxIR1.Store}
    {environment : List IxIR1.RVal} {input : IxIR1.Code} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runCode ctx fuel current store environment
        (IxIR1.HPT.CasePrune.run artifact.targetDeclEnv
          certificate.summaryEnv input).code =
      IxIR1.runCode ctx fuel current store environment input := by
  exact IxIR1.HPT.CasePrune.runCode_run_eq_of_runWith_eq_ok
    (program := artifact.targetArtifacts)
    (by simpa [checkHPTWith] using hcheck)
    (by simpa [targetDeclEnv] using hctx)

/-- Direct-production consumer specialization. -/
theorem runCode_pruneCaseWithProducedHPT_eq
    {artifact : Artifact} {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {current : IxIR1.FnDef} {store : IxIR1.Store}
    {environment : List IxIR1.RVal} {input : IxIR1.Code} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runCode ctx fuel current store environment
        (artifact.pruneCaseWithProducedHPT production input).code =
      IxIR1.runCode ctx fuel current store environment input := by
  exact IxIR1.HPT.CasePrune.runCode_run_eq_of_postFixpoint
    production.postFixpoint (by simpa [targetDeclEnv] using hctx)

/-- Persistent-cache consumer specialization. -/
theorem runCode_pruneCaseWithCachedHPT_eq
    {artifact : Artifact} {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {current : IxIR1.FnDef} {store : IxIR1.Store}
    {environment : List IxIR1.RVal} {input : IxIR1.Code} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runCode ctx fuel current store environment
        (artifact.pruneCaseWithCachedHPT production input).code =
      IxIR1.runCode ctx fuel current store environment input := by
  exact IxIR1.HPT.CasePrune.runCode_run_eq_of_postFixpoint
    production.postFixpoint (by simpa [targetDeclEnv] using hctx)

/-- Checked pipeline specialization for recursive supplied-code pruning. -/
theorem runCode_pruneCasesRecursive_of_checkHPTWith_eq_ok
    {artifact : Artifact} {limits : IxIR1.HPT.Limits}
    {certificate : IxIR1.HPT.Certificate} {analysis : IxIR1.HPT.Result}
    (hcheck : artifact.checkHPTWith limits certificate = .ok analysis)
    {ctx : IxIR1.Ctx} {current : IxIR1.FnDef} {store : IxIR1.Store}
    {environment : List IxIR1.RVal} {input : IxIR1.Code} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runCode ctx fuel current store environment
        (IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
          certificate.summaryEnv input).code =
      IxIR1.runCode ctx fuel current store environment input := by
  exact IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_runWith_eq_ok
    (program := artifact.targetArtifacts)
    (by simpa [checkHPTWith] using hcheck)
    (by simpa [targetDeclEnv] using hctx)

/-- Direct-production specialization for recursive supplied-code pruning. -/
theorem runCode_pruneCasesRecursiveWithProducedHPT_eq
    {artifact : Artifact} {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {current : IxIR1.FnDef} {store : IxIR1.Store}
    {environment : List IxIR1.RVal} {input : IxIR1.Code} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runCode ctx fuel current store environment
        (artifact.pruneCasesRecursiveWithProducedHPT production input).code =
      IxIR1.runCode ctx fuel current store environment input := by
  exact IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_postFixpoint
    production.postFixpoint (by simpa [targetDeclEnv] using hctx)

/-- Persistent-cache specialization for recursive supplied-code pruning. -/
theorem runCode_pruneCasesRecursiveWithCachedHPT_eq
    {artifact : Artifact} {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {current : IxIR1.FnDef} {store : IxIR1.Store}
    {environment : List IxIR1.RVal} {input : IxIR1.Code} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runCode ctx fuel current store environment
        (artifact.pruneCasesRecursiveWithCachedHPT production input).code =
      IxIR1.runCode ctx fuel current store environment input := by
  exact IxIR1.HPT.CasePrune.runCode_runRecursive_eq_of_postFixpoint
    production.postFixpoint (by simpa [targetDeclEnv] using hctx)

/-- A checked candidate preserves exact `runMain` behavior for the recursively
pruned artifact main, including self calls. -/
theorem runMain_pruneMain_of_checkHPTWith_eq_ok
    {artifact : Artifact} {limits : IxIR1.HPT.Limits}
    {certificate : IxIR1.HPT.Certificate} {analysis : IxIR1.HPT.Result}
    (hcheck : artifact.checkHPTWith limits certificate = .ok analysis)
    {ctx : IxIR1.Ctx} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runMain ctx
        (IxIR1.HPT.CasePrune.runRecursive artifact.targetDeclEnv
          certificate.summaryEnv artifact.main).code fuel =
      IxIR1.runMain ctx artifact.main fuel := by
  exact IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_runWith_eq_ok
    (program := artifact.targetArtifacts)
    (by simpa [checkHPTWith] using hcheck)
    (by simpa [targetDeclEnv] using hctx)

/-- Direct-production specialization for recursive main pruning. -/
theorem runMain_pruneMainWithProducedHPT_eq
    {artifact : Artifact} {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runMain ctx (artifact.pruneMainWithProducedHPT production).code
        fuel =
      IxIR1.runMain ctx artifact.main fuel := by
  exact IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_postFixpoint
    production.postFixpoint (by simpa [targetDeclEnv] using hctx)

/-- Persistent-cache specialization for recursive main pruning. -/
theorem runMain_pruneMainWithCachedHPT_eq
    {artifact : Artifact} {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv) :
    IxIR1.runMain ctx (artifact.pruneMainWithCachedHPT production).code fuel =
      IxIR1.runMain ctx artifact.main fuel := by
  exact IxIR1.HPT.CasePrune.runMain_runRecursive_eq_of_postFixpoint
    production.postFixpoint (by simpa [targetDeclEnv] using hctx)

/-- A function fact admitted by configurable HPT checking covers every
successful invocation in a context backed by this artifact's exact target
declaration environment. -/
theorem functionSummary_sound_of_checkHPTWith_eq_ok
    {artifact : Artifact} {limits : IxIR1.HPT.Limits}
    {certificate : IxIR1.HPT.Certificate} {result : IxIR1.HPT.Result}
    {ctx : IxIR1.Ctx} {address : Address} {function : IxIR1.FnDef}
    {claimed : IxIR1.HPT.Fact} {arguments : List IxIR1.RVal}
    {store outputStore : IxIR1.Store} {outputValue : IxIR1.RVal}
    {fuel : Nat}
    (hcheck : artifact.checkHPTWith limits certificate = .ok result)
    (hctx : ctx.decls = artifact.targetDeclEnv)
    (hdeclaration : artifact.targetDeclEnv address = some (.fn function))
    (hsummary : certificate.summaryEnv address = some claimed)
    (hinvoke : IxIR1.invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds artifact.targetDeclEnv outputStore outputValue := by
  exact IxIR1.HPT.functionSummary_sound_of_runWith_eq_ok
    (program := artifact.targetArtifacts) (by simpa [checkHPTWith] using hcheck)
    (by simpa [targetDeclEnv] using hctx)
    (by simpa [targetDeclEnv] using hdeclaration) hsummary hinvoke

/-- Default-limit specialization of
`functionSummary_sound_of_checkHPTWith_eq_ok`. -/
theorem functionSummary_sound_of_checkHPT_eq_ok
    {artifact : Artifact} {certificate : IxIR1.HPT.Certificate}
    {result : IxIR1.HPT.Result} {ctx : IxIR1.Ctx} {address : Address}
    {function : IxIR1.FnDef} {claimed : IxIR1.HPT.Fact}
    {arguments : List IxIR1.RVal} {store outputStore : IxIR1.Store}
    {outputValue : IxIR1.RVal} {fuel : Nat}
    (hcheck : artifact.checkHPT certificate = .ok result)
    (hctx : ctx.decls = artifact.targetDeclEnv)
    (hdeclaration : artifact.targetDeclEnv address = some (.fn function))
    (hsummary : certificate.summaryEnv address = some claimed)
    (hinvoke : IxIR1.invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds artifact.targetDeclEnv outputStore outputValue := by
  exact functionSummary_sound_of_checkHPTWith_eq_ok
    (limits := IxIR1.HPT.defaultLimits)
    (by simpa [checkHPT] using hcheck) hctx hdeclaration hsummary hinvoke

/-- A row returned by deterministic production has the same evaluator
guarantee as an accepted external certificate. -/
theorem functionSummary_sound_of_producedHPT
    {artifact : Artifact} {limits : IxIR1.HPT.ProducerLimits}
    (production :
      IxIR1.HPT.Production limits.checker artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {address : Address} {function : IxIR1.FnDef}
    {claimed : IxIR1.HPT.Fact} {arguments : List IxIR1.RVal}
    {store outputStore : IxIR1.Store} {outputValue : IxIR1.RVal}
    {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv)
    (hdeclaration : artifact.targetDeclEnv address = some (.fn function))
    (hsummary : production.certificate.summaryEnv address = some claimed)
    (hinvoke : IxIR1.invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds artifact.targetDeclEnv outputStore outputValue := by
  exact production.functionSummary_sound
    (by simpa [targetDeclEnv] using hctx)
    (by simpa [targetDeclEnv] using hdeclaration) hsummary hinvoke

/-- Cache hits and rebuilt rows have the same evaluator guarantee as ordinary
checked and directly produced summaries. -/
theorem functionSummary_sound_of_cachedHPT
    {artifact : Artifact} {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts)
    {ctx : IxIR1.Ctx} {address : Address} {function : IxIR1.FnDef}
    {claimed : IxIR1.HPT.Fact} {arguments : List IxIR1.RVal}
    {store outputStore : IxIR1.Store} {outputValue : IxIR1.RVal}
    {fuel : Nat}
    (hctx : ctx.decls = artifact.targetDeclEnv)
    (hdeclaration : artifact.targetDeclEnv address = some (.fn function))
    (hsummary : production.certificate.summaryEnv address = some claimed)
    (hinvoke : IxIR1.invoke ctx fuel address arguments store =
      .ok (outputStore, outputValue)) :
    claimed.Holds artifact.targetDeclEnv outputStore outputValue := by
  exact production.functionSummary_sound
    (by simpa [targetDeclEnv] using hctx)
    (by simpa [targetDeclEnv] using hdeclaration) hsummary hinvoke

/-- Compatibility projection for consumers interested only in compiler-
generated producer labels.  The authoritative provenance is the complete
`targetAddressMap`; this view removes source-backed IxIR₀ declaration keys. -/
def generatedAddressMap (artifact : Artifact) : IxIR1.Readdress.Renaming :=
  let sourceKeys := artifact.erasedDecls.map Prod.fst
  artifact.targetAddressMap.filter fun entry => !sourceKeys.contains entry.1

/-! ## Versioned optimizer harness -/

/-- Run the optimizer harness with a directly produced checked HPT artifact.  A
disabled pass, unsupported policy, exhausted optimizer budget, or rejected
rebuild returns this artifact unchanged and records the fail-soft decision. -/
def optimizeWithProducedHPT (artifact : Artifact)
    (policy : IxIR1.Optimizer.Policy)
    {limits : IxIR1.HPT.Limits}
    (production : IxIR1.HPT.Production limits artifact.targetArtifacts) :
    Artifact × IxIR1.Optimizer.Report :=
  let outcome := IxIR1.Optimizer.runWithProducedHPT policy
    artifact.targetArtifacts artifact.main production
  let optimized := outcome.rebuilt.map artifact.withRebuiltTarget |>.getD artifact
  (optimized, outcome.report)

/-- Cached checked summaries drive the same policy and report boundary. -/
def optimizeWithCachedHPT (artifact : Artifact)
    (policy : IxIR1.Optimizer.Policy)
    {limits : IxIR1.HPT.Cache.Limits}
    (production :
      IxIR1.HPT.Cache.Production limits artifact.targetArtifacts) :
    Artifact × IxIR1.Optimizer.Report :=
  let outcome := IxIR1.Optimizer.runWithCachedHPT policy
    artifact.targetArtifacts artifact.main production
  let optimized := outcome.rebuilt.map artifact.withRebuiltTarget |>.getD artifact
  (optimized, outcome.report)

end Artifact

/-- Turn an enumerable closed world into the proof-friendly resolver
shared by checking and erasure. -/
def resolverOf (constants : List (Address × Constant)) :
    Address → Option Constant :=
  fun address =>
    (constants.find? (fun entry => entry.1 == address)).map (·.2)

/-- Prebuilt source-constant index for corpus execution. Its two stages are
explicit so repeated usage-check/evaluator resolution shares one hash map. -/
abbrev ResolverIndex := AddressEnv.Index Constant

def ResolverIndex.ofList (constants : List (Address × Constant)) :
    ResolverIndex :=
  AddressEnv.build constants

def ResolverIndex.resolve (index : ResolverIndex) :
    Address → Option Constant :=
  AddressEnv.lookup index

@[simp] theorem ResolverIndex.resolve_ofList
    (constants : List (Address × Constant)) :
    (ResolverIndex.ofList constants).resolve = resolverOf constants := by
  exact AddressEnv.lookup_build constants

private def enforce (metric : Ixon.Work.Metric) (actual limit : Nat) :
    Except Error Unit :=
  match Ixon.Work.ensure metric actual limit with
  | .ok _ => .ok ()
  | .error exceeded => .error (.resource exceeded)

/-- Budget the shared checking prefix and return its single computed stats
record so later stages do not need to rescan the source merely to preflight. -/
def preflightCheck (limits : Limits)
    (constants : List (Address × Constant)) (checkFuel : Nat) :
    Except Error Ixon.Work.ProgramStats := do
  let stats := Ixon.Work.programStats constants
  enforce .programConstants stats.constants limits.maxConstants
  enforce .programExpressionUnits stats.expressionUnits
    limits.maxExpressionUnits
  enforce .programExpandedExpressionUnits stats.expandedExpressionUnits
    limits.maxExpandedExpressionUnits
  enforce .layer1NodeVisits stats.layer1NodeVisits
    limits.maxLayer1NodeVisits
  enforce .usageFuel checkFuel limits.maxUsageFuel
  return stats

/-- Preflight the unvalidated compiler path, including the current
append-based whole-program eraser. -/
def preflightCompile (limits : Limits)
    (constants : List (Address × Constant)) (checkFuel eraseFuel lowerFuel : Nat) :
    Except Error Ixon.Work.ProgramStats := do
  let stats ← preflightCheck limits constants checkFuel
  enforce .erasedDeclarations stats.erasedDeclarations
    limits.maxErasedDeclarations
  enforce .erasureAppendCells stats.erasureAppendCells
    limits.maxErasureAppendCells
  enforce .erasureFuel eraseFuel limits.maxErasureFuel
  enforce .loweringFuel lowerFuel limits.maxLoweringFuel
  return stats

/-- Preflight the proof-producing compiler path.  The attempt count charges
the worst dependency order (one newly covered declaration per round) plus the
final ordered certificate pass.  No catalog-wide `decide` is used: an
over-sized proof-producing job is rejected before validation starts. -/
def preflightValidated (limits : Limits)
    (constants : List (Address × Constant))
    (checkFuel eraseFuel validateFuel lowerFuel : Nat) :
    Except Error Ixon.Work.ProgramStats := do
  let stats ← preflightCompile limits constants checkFuel eraseFuel lowerFuel
  enforce .certificateCandidates stats.certificateCandidates
    limits.maxCertificateCandidates
  enforce .certificateValidationAttempts stats.certificateValidationAttempts
    limits.maxCertificateValidationAttempts
  enforce .certificateSourceNodeWork stats.certificateSourceNodeWork
    limits.maxCertificateSourceNodeWork
  enforce .validationFuel validateFuel limits.maxValidationFuel
  return stats

/-- Check every constant after the caller has completed structural preflight. -/
private def checkProgramCore (constants : List (Address × Constant))
    (fuel : Nat) : Except Error Unit := do
  let resolverIndex := ResolverIndex.ofList constants
  let resolve := resolverIndex.resolve
  for (address, constant) in constants do
    match Ixon.UsageCheck.checkConstant resolve constant fuel with
    | .ok _ => pure ()
    | .error error => throw (.usage address error)

/-- Check every constant, reporting which address failed. -/
def checkProgram (constants : List (Address × Constant))
    (fuel : Nat := Ixon.UsageCheck.defaultFuel)
    (limits : Limits := {}) : Except Error Unit := do
  let _ ← preflightCheck limits constants fuel
  checkProgramCore constants fuel

/-- Check, erase, and lower a closed program. `mainAddress` names the
closed entry value or computation in the source environment; lowering
rejects an unknown address or an entry incompatible with the requested
result demand.

The erasure step is **unvalidated**: this entry point accepts
declarations and expression shapes beyond the configured
`Covered`/`PErase` fragment. Use `compileValidated` when every
declaration must carry a simulation certificate. -/
def compile (constants : List (Address × Constant))
    (mainAddress : Address) (config : Config := {})
    (mainWorld : Owned := .shared)
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel)
    (eraseFuel : Nat := Erase.defaultFuel)
    (lowerFuel : Nat := 10000) : Except Error Artifact := do
  let _ ← preflightCompile config.limits constants checkFuel eraseFuel lowerFuel
  checkProgramCore constants checkFuel
  let resolverIndex := ResolverIndex.ofList constants
  let resolve := resolverIndex.resolve
  let eraseCtx : Erase.EraseCtx :=
    { resolve, blobs := config.blobs, natBlock := config.natBlock }
  let erased ←
    match EraseAddressed.run eraseCtx constants (.ref mainAddress) eraseFuel with
    | .ok result => pure result
    | .error (.erase error) => throw (.erase error)
    | .error (.readdress message) => throw (.readdress message)
  match IxIR1.Lower.lowerAllIndexedFullyAddressed
      erased.declarations erased.main
      mainWorld lowerFuel with
  | .ok addressed =>
    pure
      { rawErasedDecls := erased.raw
        erasedDecls := erased.declarations
        erasedBlocks := erased.addressed.blocks
        erasedAddressMap := erased.addressMap
        targetArtifacts := addressed.artifacts
        main := addressed.main
        targetAddressMap := addressed.addressMap }
  | .error message => throw (.lower message)

/-! ## The validator-gated entry point

`compile` runs the eraser unvalidated, so the proof-producing
`EraseValidator` is bypassable in the composed path.
`compileValidated` closes that seam: after the usage gate and the
(strict) eraser it requires a `Covered` certificate for **every**
non-block constant against the exact erased environment, obtained
uniformly through `EraseValidator.certifySharedProgram`. With empty sharing
tables this route reduces to ordinary erasure. Mutual blocks themselves have no
block-level judgment — their members are certified through the
projection constants (`iPrj`/`cPrj`/`rPrj`/`dPrj`); an erased direct
member reference without a certified projection fails closed at the
referencing declaration. -/

/-- Every executable definition/recursor member receives one finite slot in
the simultaneous validator scope.  Inductive members have no executable body
to certify. -/
private def memberPlanForBlock (block : Address) :
    Nat → List Ixon.MutConst → List Sim.MemberKey
  | _, [] => []
  | index, .indc _ :: rest =>
      memberPlanForBlock block (index + 1) rest
  | index, .defn _ :: rest =>
      { block, idx := index } :: memberPlanForBlock block (index + 1) rest
  | index, .recr _ :: rest =>
      { block, idx := index } :: memberPlanForBlock block (index + 1) rest

/-- Runtime-derived simultaneous-member scope for the exact closed program. -/
def programMemberPlan
    (constants : List (Address × Constant)) : List Sim.MemberKey :=
  constants.flatMap fun entry =>
    match entry.2.info with
    | .muts members => memberPlanForBlock entry.1 0 members.toList
    | _ => []

/-- The source evaluator context used by the validated pipeline.  Exposing
this exact closure lets semantic clients state source evaluation and sharing
well-formedness against the same resolver that validation used. -/
def validatedEvalCtx (constants : List (Address × Constant))
    (config : Config) : Ixon.Eval.EvalCtx :=
  let resolverIndex := ResolverIndex.ofList constants
  { resolve := resolverIndex.resolve
    blobs := config.blobs
    natBlock := config.natBlock }

/-- Closed source frame whose sole reference is the selected program main. -/
def validatedMainFrame (mainAddress : Address) : Ixon.Eval.Frame :=
  { refs := #[mainAddress] }

/-- Canonical closed Ixon entry expression for `compileValidated`. -/
def validatedMainSource : Ixon.Expr := .ref 0 #[]

/-- Proof-facing result of validator-gated compilation.  It retains the exact
closed-expression erasure certificate and both successful execution traces
consumed by the fully addressed semantic theorem.  The production artifact is
the `artifact` projection below; proof fields erase at runtime. -/
structure ValidatedCompilation
    (constants : List (Address × Constant)) (mainAddress : Address)
    (config : Config) (mainWorld : Owned)
    (eraseFuel lowerFuel : Nat) where
  memberScope : Sim.MemberScope
  erasure : EraseAddressed.RunTrace
    (EraseValidator.eraseCtxOf (validatedEvalCtx constants config))
    constants (.ref mainAddress) eraseFuel
  entry : @EraseValidator.CertifiedSharedExpr
    (validatedEvalCtx constants config)
    { env := IxIR0.Env.ofList erasure.result.raw }
    none (EraseValidator.tablesOfFrame (validatedMainFrame mainAddress))
    (validatedMainFrame mainAddress).selfAddr [] eraseFuel
    validatedMainSource memberScope
  entryTarget : entry.target = (.ref mainAddress : IxIR0.Expr)
  members : Sim.MemberCoverage
    (validatedEvalCtx constants config).inlineSharing
    { env := IxIR0.Env.ofList erasure.result.raw } memberScope.plan
  strict : (validatedEvalCtx constants config).Strict
  /-- The exact addressed IxIR₀ graph admitted to lowering contains no extern
  declaration. This is the conservative certified ownership ABI: reopening
  the boundary requires replacing this field with an explicit policy. -/
  externsRejected : ValidatedExternsRejected erasure.result.declarations
  lowering : IxIR1.Lower.FullyAddressedTrace
    erasure.result.declarations erasure.result.main mainWorld lowerFuel
  /-- Defense in depth over the actual emitted graph: lowering and content
  addressing did not introduce an extern behind the source-side gate. -/
  targetExternsRejected : ValidatedTargetExternsRejected
    (lowering.result.artifacts.flatMap
      IxIR1.ReaddressAll.Artifact.declarations)

namespace ValidatedCompilation

/-- Ordinary production artifact projected from the proof-facing traces. -/
def artifact {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel) : Artifact :=
  { rawErasedDecls := compilation.erasure.result.raw
    erasedDecls := compilation.erasure.result.declarations
    erasedBlocks := compilation.erasure.result.addressed.blocks
    erasedAddressMap := compilation.erasure.result.addressMap
    targetArtifacts := compilation.lowering.result.artifacts
    main := compilation.lowering.result.main
    targetAddressMap := compilation.lowering.result.addressMap }

/-- No extern can be resolved from the exact addressed IxIR₀ input admitted
to certified lowering. -/
theorem addressedSourceEnv_ne_extern
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    {address : Address} {arity : Nat} :
    IxIR0.Env.ofList compilation.erasure.result.declarations address ≠
      some (.extern arity) :=
  compilation.externsRejected.env_ne_extern

/-- The exact IxIR₁ declaration list returned to artifact consumers contains
no extern declaration. -/
theorem targetExtern_not_mem
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    {address : Address} {arity : Nat} :
    (address, .extern arity) ∉ compilation.artifact.targetDecls := by
  simpa [artifact, Artifact.targetDecls] using
    compilation.targetExternsRejected.not_mem (address := address)
      (arity := arity)

/-- Artifact consumers cannot resolve an extern through the exact indexed
IxIR₁ declaration environment returned by validated compilation. -/
theorem targetDeclEnv_ne_extern
    {constants : List (Address × Constant)} {mainAddress : Address}
    {config : Config} {mainWorld : Owned} {eraseFuel lowerFuel : Nat}
    (compilation : ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel)
    {address : Address} {arity : Nat} :
    compilation.artifact.targetDeclEnv address ≠ some (.extern arity) := by
  change AddressEnv.lookup
      (AddressEnv.build (compilation.lowering.result.artifacts.flatMap
        IxIR1.ReaddressAll.Artifact.declarations)) address ≠
    some (.extern arity)
  exact compilation.targetExternsRejected.env_ne_extern

end ValidatedCompilation

/-- One fixpoint round of coverage validation: attempt every pending
address against the current database, extending it in place. Returns
the grown database, this round's successes (in attempt order), and the
still-rejected addresses with their diagnostics (in attempt order). -/
private def coverageRound [Sim.MemberScope]
    (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (validateFuel : Nat) (db : EraseValidator.CoverageDB ectx ictx) :
    List Address →
      EraseValidator.CoverageDB ectx ictx × List Address ×
        List (Address × String)
  | [] => (db, [], [])
  | address :: rest =>
    match EraseValidator.validateCovered ectx ictx db validateFuel address with
    | .ok ha =>
      let (db', oks, failed) := coverageRound ectx ictx validateFuel
        ({ address, covered := ha.down } :: db) rest
      (db', address :: oks, failed)
    | .error message =>
      let (db', oks, failed) := coverageRound ectx ictx validateFuel db rest
      (db', oks, (address, message) :: failed)

/-- Discover a dependency order for `certifyProgram` by fixpoint:
repeat `coverageRound` until every candidate validates. Fail-closed —
a round without progress reports the first still-rejected address and
its validator diagnostic. At most `candidates + 1` rounds are needed,
since a productive round covers at least one address. -/
def coveragePlan [Sim.MemberScope]
    (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (validateFuel : Nat) :
    Nat → EraseValidator.CoverageDB ectx ictx → List Address →
      List Address → Except (Address × String) (List Address)
  | _, _, done, [] => .ok done.reverse
  | 0, _, _, address :: _ =>
    .error (address, "coverage validation did not converge")
  | rounds + 1, db, done, pending =>
    let (db', oks, failed) := coverageRound ectx ictx validateFuel db pending
    if oks.isEmpty then
      match failed with
      | (address, message) :: _ => .error (address, message)
      | [] => .ok done.reverse
    else
      coveragePlan ectx ictx validateFuel rounds db'
        (oks.reverse ++ done) (failed.map (·.1))

/-- Check, erase, **validate the exact erased output**, and lower.

The composition of `compile` with the proof-producing erasure validator:
after `checkProgram` and the strict eraser, every non-block constant must earn
a `Covered` certificate against the erased environment. The whole program is
then re-certified through the sharing-aware entry point, whose result records
the erasure equation and simultaneous-member coverage for this exact constant
list. The closed main is certified in the same runtime-derived member scope,
and both lowering address passes retain their successful equations. The first
declaration the validator rejects is reported as `Error.validate` with the
validator's own diagnostic; `mainAddress` itself must be a certifiable
declaration. Out-of-fragment programs belong to `compile`. -/
private def compileValidatedCore [Sim.MemberScope]
    (constants : List (Address × Constant))
    (mainAddress : Address) (config : Config)
    (mainWorld : Owned) (checkFuel eraseFuel validateFuel lowerFuel : Nat) :
    Except Error (ValidatedCompilation constants mainAddress config
      mainWorld eraseFuel lowerFuel) := do
  let _ ← preflightValidated config.limits constants checkFuel eraseFuel
    validateFuel lowerFuel
  checkProgramCore constants checkFuel
  let ectx := validatedEvalCtx constants config
  -- the artifact of record: the strict pipeline eraser (split
  -- constructor spines already fail closed here)
  let eraseCtx := EraseValidator.eraseCtxOf ectx
  let erasure ←
    match EraseAddressed.runWithTrace eraseCtx constants (.ref mainAddress)
        eraseFuel with
    | .ok trace => pure trace
    | .error (.erase error) => throw (.erase error)
    | .error (.readdress message) => throw (.readdress message)
  let erased := erasure.result
  let externsRejected : PLift
      (ValidatedExternsRejected erased.declarations) ←
    match hboundary : firstValidatedExtern? erased.declarations with
    | none => pure ⟨hboundary⟩
    | some address =>
      throw (.validate address
        "validated extern ownership ABI rejects this declaration")
  let rawErasedDecls := erased.raw
  let erasedIndex := IxIR0.Env.Index.ofList rawErasedDecls
  let ictx : IxIR0.Ctx := { env := erasedIndex.toEnv }
  -- blocks carry no block-level judgment; everything else must certify
  let candidates := constants.filterMap fun entry =>
    match entry.2.info with
    | .muts _ => none
    | _ => some entry.1
  unless candidates.contains mainAddress do
    throw (.validate mainAddress "main address is not a certifiable declaration")
  let rounds := candidates.length + 1
  -- The sharing-aware validator is a strict generalization of the plain
  -- route: with empty sharing tables its inliner is the identity, while one
  -- uniform certificate type lets the closed main cross the semantic API.
  let order ←
    match coveragePlan ectx.inlineSharing ictx validateFuel rounds [] []
        candidates with
    | .error (address, message) => throw (.validate address message)
    | .ok order => pure order
  let program ←
    match EraseValidator.certifySharedProgram ectx constants order
        eraseFuel validateFuel with
    | .error (.erase error) => throw (.erase error)
    | .error (.relation message) => throw (.validate mainAddress message)
    | .ok cert => pure cert
  -- the certificate re-runs the (validator-configured) eraser; its
  -- recorded target must be exactly what this pipeline lowers
  if hprogramTarget : program.target == rawErasedDecls then
    have hprogramTargetEq : program.target = rawErasedDecls :=
      beq_iff_eq.mp hprogramTarget
    let coverage : EraseValidator.CoverageDB ectx.inlineSharing ictx := by
      simpa [ictx, erasedIndex] using hprogramTargetEq ▸ program.coverage
    let entry ←
      match EraseValidator.certifySharedClosedExpr ectx ictx coverage.oracle
          (validatedMainFrame mainAddress) validatedMainSource eraseFuel
          validateFuel with
      | .error (.erase error) => throw (.erase error)
      | .error (.relation message) => throw (.validate mainAddress message)
      | .ok cert => pure cert
    if hentryTarget : entry.target == (.ref mainAddress : IxIR0.Expr) then
      have hentryTargetEq : entry.target =
          (.ref mainAddress : IxIR0.Expr) := beq_iff_eq.mp hentryTarget
      let lowering ←
        match IxIR1.Lower.lowerAllIndexedFullyAddressedWithTrace
            erased.declarations erased.main mainWorld lowerFuel with
        | .ok trace => pure trace
        | .error message => throw (.lower message)
      let targetExternsRejected : PLift
          (ValidatedTargetExternsRejected
            (lowering.result.artifacts.flatMap
              IxIR1.ReaddressAll.Artifact.declarations)) ←
        match hboundary : firstValidatedTargetExtern?
            (lowering.result.artifacts.flatMap
              IxIR1.ReaddressAll.Artifact.declarations) with
        | none => pure ⟨hboundary⟩
        | some address =>
          throw (.validate address
            "certified lowering emitted an extern outside its ownership ABI")
      let retainedEntry : @EraseValidator.CertifiedSharedExpr
          (validatedEvalCtx constants config)
          { env := IxIR0.Env.ofList erasure.result.raw }
          none (EraseValidator.tablesOfFrame
            (validatedMainFrame mainAddress))
          (validatedMainFrame mainAddress).selfAddr [] eraseFuel
          validatedMainSource (inferInstance : Sim.MemberScope) := by
        simpa [ictx, erasedIndex] using entry
      have retainedEntryTarget : retainedEntry.target =
          (.ref mainAddress : IxIR0.Expr) := by
        have hsame : retainedEntry.target = entry.target :=
          Except.ok.inj (retainedEntry.erased.symm.trans entry.erased)
        exact hsame.trans hentryTargetEq
      have hstrictInline := program.members.strict
      let retainedMembers : Sim.MemberCoverage
          (validatedEvalCtx constants config).inlineSharing
          { env := IxIR0.Env.ofList erasure.result.raw }
          (inferInstance : Sim.MemberScope).plan := by
        have hmembers := program.members
        rw [hprogramTargetEq] at hmembers
        simpa [rawErasedDecls] using hmembers
      pure
        { memberScope := inferInstance
          erasure
          entry := retainedEntry
          entryTarget := retainedEntryTarget
          members := retainedMembers
          strict :=
            { neutralElims := by simpa using hstrictInline.neutralElims
              stringLiterals := by
                simpa using hstrictInline.stringLiterals }
          externsRejected := externsRejected.down
          lowering
          targetExternsRejected := targetExternsRejected.down }
    else
      throw (.validate mainAddress
        "certified main differs from the compiled main reference")
  else
    throw (.validate mainAddress
      "certified erasure differs from the compiled erasure")

/-- Validator-gated production compiler with a simultaneous-member scope
derived from the exact runtime program and all proof-facing pass equations
retained. -/
def compileValidatedWithTrace (constants : List (Address × Constant))
    (mainAddress : Address) (config : Config := {})
    (mainWorld : Owned := .shared)
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel)
    (lowerFuel : Nat := 10000) : Except Error
      (ValidatedCompilation constants mainAddress config mainWorld eraseFuel
        lowerFuel) :=
  letI _memberScope : Sim.MemberScope :=
    { plan := programMemberPlan constants }
  compileValidatedCore constants mainAddress config mainWorld checkFuel
    eraseFuel validateFuel lowerFuel

/-- Validator-gated production compiler with its proof-facing execution
record erased from the returned artifact API. -/
def compileValidated (constants : List (Address × Constant))
    (mainAddress : Address) (config : Config := {})
    (mainWorld : Owned := .shared)
    (checkFuel : Nat := Ixon.UsageCheck.defaultFuel)
    (eraseFuel : Nat := Erase.defaultFuel)
    (validateFuel : Nat := Erase.defaultFuel)
    (lowerFuel : Nat := 10000) : Except Error Artifact := do
  return (← compileValidatedWithTrace constants mainAddress config mainWorld
    checkFuel eraseFuel validateFuel lowerFuel).artifact

/-! ## End-to-end integration fixture

A two-constructor `Box` block gives the first constructor a unique
result/field world and the second a shared result/field world. Its
identity-like recursor rebuilds either major with the shared constructor.
`dropFirst : Box →ᵃ Box →ω Box`
discards its affine first argument and returns its shared second one;
`main` constructs both boxes, calls `dropFirst`, then runs the block
recursor on the survivor.

The fixture forces all integration seams at once: the checker accepts
the mixed modes, the eraser emits a real recursor declaration, the
lowerer consumes that declaration, and the IxIR₁ runtime observes one
unique deep-free plus shared RC traffic. -/

section Guards

private def address (byte : UInt8) : Address := Address.replicate byte

private def aBlock := address 0x70
private def aBox := address 0x71
private def aCtor := address 0x72
private def aRec := address 0x73
private def aDropFirst := address 0x74
private def aMain := address 0x75
private def aEleven := address 0x76
private def aTwentyTwo := address 0x77
private def aUnused := address 0x78
private def aSharedCtor := address 0x79

private def boxType : Ixon.Expr := .ref 0 #[]

private def boxInductive : Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 1
        typ := .all .affine .unique (.sort 0) (.recur 0 #[]) },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.sort 0) (.recur 0 #[]) }
    ] }

/-- `Box.rec box = Box.mk box.field`, deliberately nontrivial so the
lowered case body allocates a fresh shared result. -/
private def boxRecursor : Ixon.Recursor :=
  { k := false, isUnsafe := false, lvls := 0
    params := 0, indices := 0, motives := 0, minors := 0
    typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[])
    rules := #[
      { fields := 1
        rhs := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) },
      { fields := 1
        rhs := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) }
    ] }

private def cBlock : Constant :=
  { info := .muts #[.indc boxInductive, .recr boxRecursor]
    sharing := #[], refs := #[aSharedCtor], univs := #[.zero] }

private def projection (info : Ixon.ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def cBox :=
  projection (.iPrj { idx := 0, block := aBlock })

private def cCtor :=
  projection (.cPrj { idx := 0, cidx := 0, block := aBlock })

private def cSharedCtor :=
  projection (.cPrj { idx := 0, cidx := 1, block := aBlock })

private def cRec :=
  projection (.rPrj { idx := 1, block := aBlock })

private def dropFirstValue : Ixon.Expr :=
  .lam .affine boxType (.lam .many boxType (.var 0))

private def cDropFirst : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .affine .shared boxType
          (.all .many .shared boxType boxType)
        value := dropFirstValue }
    sharing := #[], refs := #[aBox], univs := #[.zero] }

private def boxOfNat (blobRef : UInt64) : Ixon.Expr :=
  .app (.ref 2 #[]) (.nat blobRef)

/-- Manufacture a checker-shared, computational Nat field without an
implicit freeze: projection is a shared borrow, and its temporary unique
box is lowered in the projection's shared demand. -/
private def sharedBoxOfNat (blobRef : UInt64) : Ixon.Expr :=
  .app (.ref 6 #[]) (.prj 0 0 (boxOfNat blobRef))

private def cMain : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .ref 0 #[]
        value := .app (.ref 3 #[])
          (.app (.app (.ref 1 #[]) (boxOfNat 4)) (sharedBoxOfNat 5)) }
    sharing := #[]
    refs := #[aBox, aDropFirst, aCtor, aRec, aEleven, aTwentyTwo,
      aSharedCtor]
    univs := #[.zero] }

/-- A validated function deliberately absent from main's transitive runtime
references. The compiler emits it; rooted reachability must remove
its lowered declaration rather than relying only on a hand-written graph. -/
private def cUnused : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .shared boxType boxType
        value := .lam .many boxType
          (.app (.ref 1 #[]) (.var 0)) }
    sharing := #[]
    refs := #[aBox, aRec]
    univs := #[.zero] }

/-- A usage-valid shared constructor result whose lowered main contains no
dynamic application. The surrounding catalog still emits stored functions,
so it gives rooted reachability an observable compiler-produced deletion. -/
private def cReachMain : Constant :=
  { cMain with
    info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .ref 0 #[]
        value := sharedBoxOfNat 4 } }

private def constants : List (Address × Constant) :=
  [(aBlock, cBlock), (aBox, cBox), (aCtor, cCtor),
   (aSharedCtor, cSharedCtor), (aRec, cRec),
   (aDropFirst, cDropFirst), (aMain, cMain)]

private def blobs : Address → Option Ixon.Eval.Blob := fun a =>
  if a == aEleven then some (.natB 11)
  else if a == aTwentyTwo then some (.natB 22)
  else none

/-! Exact structural-budget boundary fixtures.  Every field is set to the
measured requirement of this program; lowering any one field by one must name
that precise metric, actual value, and limit before checking begins. -/

private def budgetStats : Ixon.Work.ProgramStats :=
  Ixon.Work.programStats constants

private def exactLimits : Limits :=
  { maxConstants := budgetStats.constants
    maxExpressionUnits := budgetStats.expressionUnits
    maxExpandedExpressionUnits := budgetStats.expandedExpressionUnits
    maxLayer1NodeVisits := budgetStats.layer1NodeVisits
    maxErasedDeclarations := budgetStats.erasedDeclarations
    maxErasureAppendCells := budgetStats.erasureAppendCells
    maxCertificateCandidates := budgetStats.certificateCandidates
    maxCertificateValidationAttempts :=
      budgetStats.certificateValidationAttempts
    maxCertificateSourceNodeWork := budgetStats.certificateSourceNodeWork
    maxUsageFuel := Ixon.UsageCheck.defaultFuel
    maxErasureFuel := Erase.defaultFuel
    maxValidationFuel := Erase.defaultFuel
    maxLoweringFuel := 10000 }

private def validatedPreflight (limits : Limits) :
    Except Error Ixon.Work.ProgramStats :=
  preflightValidated limits constants Ixon.UsageCheck.defaultFuel
    Erase.defaultFuel Erase.defaultFuel 10000

private def rejectsResource (metric : Ixon.Work.Metric)
    (actual limit : Nat) (result : Except Error Ixon.Work.ProgramStats) : Bool :=
  match result with
  | .error (.resource exceeded) =>
    exceeded.metric == metric && exceeded.actual == actual &&
      exceeded.limit == limit
  | _ => false

private def exactBudgetAccepted : Bool :=
  match validatedPreflight exactLimits with
  | .ok stats => stats == budgetStats
  | .error _ => false

private def everyOneBelowBudgetRejected : Bool :=
  let s := budgetStats
  #[
    rejectsResource .programConstants s.constants (s.constants - 1)
      (validatedPreflight
        { exactLimits with maxConstants := s.constants - 1 }),
    rejectsResource .programExpressionUnits s.expressionUnits
      (s.expressionUnits - 1)
      (validatedPreflight
        { exactLimits with maxExpressionUnits := s.expressionUnits - 1 }),
    rejectsResource .programExpandedExpressionUnits s.expandedExpressionUnits
      (s.expandedExpressionUnits - 1)
      (validatedPreflight
        { exactLimits with maxExpandedExpressionUnits :=
            s.expandedExpressionUnits - 1 }),
    rejectsResource .layer1NodeVisits s.layer1NodeVisits
      (s.layer1NodeVisits - 1)
      (validatedPreflight
        { exactLimits with maxLayer1NodeVisits := s.layer1NodeVisits - 1 }),
    rejectsResource .usageFuel Ixon.UsageCheck.defaultFuel
      (Ixon.UsageCheck.defaultFuel - 1)
      (validatedPreflight
        { exactLimits with maxUsageFuel := Ixon.UsageCheck.defaultFuel - 1 }),
    rejectsResource .erasedDeclarations s.erasedDeclarations
      (s.erasedDeclarations - 1)
      (validatedPreflight
        { exactLimits with maxErasedDeclarations := s.erasedDeclarations - 1 }),
    rejectsResource .erasureAppendCells s.erasureAppendCells
      (s.erasureAppendCells - 1)
      (validatedPreflight
        { exactLimits with maxErasureAppendCells :=
            s.erasureAppendCells - 1 }),
    rejectsResource .erasureFuel Erase.defaultFuel
      (Erase.defaultFuel - 1)
      (validatedPreflight
        { exactLimits with maxErasureFuel := Erase.defaultFuel - 1 }),
    rejectsResource .loweringFuel 10000 9999
      (validatedPreflight { exactLimits with maxLoweringFuel := 9999 }),
    rejectsResource .certificateCandidates s.certificateCandidates
      (s.certificateCandidates - 1)
      (validatedPreflight
        { exactLimits with maxCertificateCandidates :=
            s.certificateCandidates - 1 }),
    rejectsResource .certificateValidationAttempts
      s.certificateValidationAttempts (s.certificateValidationAttempts - 1)
      (validatedPreflight
        { exactLimits with maxCertificateValidationAttempts :=
            s.certificateValidationAttempts - 1 }),
    rejectsResource .certificateSourceNodeWork s.certificateSourceNodeWork
      (s.certificateSourceNodeWork - 1)
      (validatedPreflight
        { exactLimits with maxCertificateSourceNodeWork :=
            s.certificateSourceNodeWork - 1 }),
    rejectsResource .validationFuel Erase.defaultFuel
      (Erase.defaultFuel - 1)
      (validatedPreflight
        { exactLimits with maxValidationFuel := Erase.defaultFuel - 1 })
  ].all id

#guard exactBudgetAccepted
#guard everyOneBelowBudgetRejected

private def compiled : Except Error Artifact :=
  compile constants aMain { blobs }

/-- The source evaluator returns the box built from the second
argument, after rebuilding it through the recursor. -/
private def sourceAgrees : Bool :=
  let resolverIndex := ResolverIndex.ofList constants
  let ctx : Ixon.Eval.EvalCtx := { resolve := resolverIndex.resolve, blobs }
  let frame : Ixon.Eval.Frame := { refs := #[aMain] }
  match Ixon.Eval.evalClosed ctx frame (.ref 0 #[]) with
  | .ok (.ctorV block 0 1 [.litV (.natL 22)]) => block == aBlock
  | _ => false

/-- The actual erased recursor reaches IxIR₁ as a unary `case`
function; this is not a hand-written IxIR₀ recursor fixture. -/
private def recursorCrossesBothPasses : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
    let transient := Erase.memberAddr aBlock 1
    match artifact.erasedAddressMap.lookup transient,
        artifact.rawErasedDecls.find? (fun entry => entry.1 == transient) with
    | some member, some (_, .recursor 0 false rawRules) =>
      match artifact.erasedDecls.find? (fun entry => entry.1 == member),
          artifact.targetAddressMap.lookup member with
      | some (_, .recursor 0 false rules), some targetMember =>
        match artifact.targetDecls.find? (fun entry =>
            entry.1 == targetMember) with
        | some (_, .fn fn) =>
          member != transient && targetMember != member &&
          artifact.erasedBlocks.length == 1 &&
          rawRules.size == 2 && rules.size == 2 && fn.arity == 1 &&
          !(artifact.erasedDecls.map (·.1)).contains transient &&
          !(artifact.targetDecls.map (·.1)).contains transient &&
          !(artifact.targetDecls.map (·.1)).contains member &&
          match fn.body with
          | .case _ false alts => alts.size == 2
          | _ => false
        | _ => false
      | _, _ => false
    | _, _ => false

/-- Runtime result and cost facts for the composed pipeline. Before
releasing the result: two input boxes + one pap + one rebuilt box were
allocated; the unique input, pap, and shared major were reclaimed.
Releasing the result leaves an empty store. -/
private def targetAgrees : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
    let targetIndex := IxIR1.Env.Index.ofList artifact.targetDecls
    let ctx : IxIR1.Ctx := { decls := targetIndex.toEnv }
    match IxIR1.runMain ctx artifact.main with
    | .ok (store, value@(.loc location)) =>
      let shape := match store.get? location with
        | some box =>
          match box.node with
          | .ctorN cid fields =>
            cid.block == aSharedCtor && cid.cidx == 1 &&
              fields.toList == [.lit (.nat 22)]
          | _ => false
        | none => false
      shape && store.allocs == 5 && store.frees == 4 &&
        store.rcops == 3 && store.live == 1 &&
        match IxIR1.dropVal ctx 100000 store value with
        | .ok released =>
          released.allocs == 5 && released.frees == 5 &&
            released.rcops == 4 && released.live == 0
        | .error _ => false
    | _ => false

/-- Optimizer observations run on actual compiler output, not only a
hand-written IxIR₁ graph. Independent runs must agree byte-for-byte on their
reports and output roots; disabling the pass must select the exact input
graph. -/
private def optimizerHarnessOnCompiled : Bool :=
  match compiled with
  | .error _ => false
  | .ok artifact =>
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let (firstArtifact, firstReport) :=
            artifact.optimizeWithProducedHPT IxIR1.Optimizer.defaultPolicy
              production
          let (repeatArtifact, repeatReport) :=
            artifact.optimizeWithProducedHPT IxIR1.Optimizer.defaultPolicy
              production
          let disabledPolicy : IxIR1.Optimizer.Policy :=
            { casePrune := { enabled := false }
              fetchForward := { enabled := false }
              destruction := { enabled := false }
              papFuse := { enabled := false }
              reachability := { enabled := false } }
          let (disabledArtifact, disabledReport) :=
            artifact.optimizeWithProducedHPT disabledPolicy production
          let inputRoot := IxIR1.Optimizer.graphRoot artifact.targetArtifacts
            artifact.main
          let firstRoot := IxIR1.Optimizer.graphRoot
            firstArtifact.targetArtifacts firstArtifact.main
          let repeatRoot := IxIR1.Optimizer.graphRoot
            repeatArtifact.targetArtifacts repeatArtifact.main
          firstReport.before.functions > 0 &&
            firstReport.before.counts.instructions > 0 &&
            firstReport.before.codeBytes > 0 &&
            firstReport.certificateBytes > 0 &&
            firstReport.inputRoot == inputRoot &&
            firstReport.outputRoot == firstRoot &&
            firstReport.after == IxIR1.Optimizer.observe
              firstArtifact.targetArtifacts firstArtifact.main &&
            firstRoot == repeatRoot &&
            firstReport.bytes == repeatReport.bytes &&
            firstReport.address == repeatReport.address &&
            disabledReport.disposition ==
              .skipped IxIR1.Optimizer.SkipReason.disabled &&
            disabledReport.inputRoot == inputRoot &&
            disabledReport.outputRoot == inputRoot &&
            IxIR1.Optimizer.graphRoot disabledArtifact.targetArtifacts
              disabledArtifact.main == inputRoot

private def destructionCid : IxIR1.CtorId :=
  { block := address 0x7d, indIdx := 0, cidx := 0 }

/-- The first binding proves scalar-drop elimination; the unique allocation
proves exact all-scalar leaf destruction.  Keeping both in `main` exercises
the sentinel analysis owner as well as the empty-program rebuild path. -/
private def destructionMain : IxIR1.Code :=
  .letOp (.pure (.lit (.nat 5)))
    (.letOp (.drop (.var 0))
      (.letOp (.alloc .unique destructionCid #[.lit (.nat 7)])
        (.letOp (.dropU (.var 0))
          (.ret (.lit (.nat 42))))))

private def destructionRuntimeOk (code : IxIR1.Code) : Bool :=
  match IxIR1.runMain { decls := IxIR1.Env.empty } code with
  | .ok (store, .lit (.nat 42)) =>
      store.allocs == 1 && store.frees == 1 && store.rcops == 0 &&
        store.live == 0
  | _ => false

/-- Checked production specializes both destructor sites, attributes the
changes, preserves the exact executable observation, and reaches a structural
fixed point on the immediately rechecked output. -/
private def optimizerSpecializesDestruction : Bool :=
  match IxIR1.HPT.produce ([] : List IxIR1.ReaddressAll.Artifact) with
  | .error _ => false
  | .ok production =>
      let first := IxIR1.Optimizer.runWithProducedHPT
        IxIR1.Optimizer.defaultPolicy [] destructionMain production
      let optimizedMain := first.main destructionMain
      let second := IxIR1.Optimizer.runWithProducedHPT
        IxIR1.Optimizer.defaultPolicy [] optimizedMain production
      let unsupportedPolicy : IxIR1.Optimizer.Policy :=
        { destruction := { version := 0 } }
      let unsupported := IxIR1.Optimizer.runWithProducedHPT
        unsupportedPolicy [] destructionMain production
      destructionRuntimeOk destructionMain &&
        destructionRuntimeOk optimizedMain &&
        first.report.disposition == .changed &&
        first.report.elidedScalarDrops == 1 &&
        first.report.specializedUniqueDrops == 1 &&
        first.report.before.counts.rcDecrements == 1 &&
        first.report.before.counts.uniqueDrops == 1 &&
        first.report.before.counts.frees == 0 &&
        first.report.after.counts.rcDecrements == 0 &&
        first.report.after.counts.uniqueDrops == 0 &&
        first.report.after.counts.frees == 1 &&
        second.report.disposition == .unchanged &&
        second.report.elidedScalarDrops == 0 &&
        second.report.specializedUniqueDrops == 0 &&
        second.report.inputRoot == second.report.outputRoot &&
        (second.main optimizedMain).bytes == optimizedMain.bytes &&
        unsupported.rebuilt.isNone &&
        unsupported.report.disposition ==
          .skipped (.unsupportedDestructionVersion 0
            IxIR1.Optimizer.currentDestructionVersion)

private def reachabilityConstants : List (Address × Constant) :=
  [(aBlock, cBlock), (aBox, cBox), (aCtor, cCtor),
   (aSharedCtor, cSharedCtor), (aRec, cRec),
   (aDropFirst, cDropFirst), (aMain, cReachMain),
   (aUnused, cUnused)]

/-- Production Ixon→IxIR₁ compilation emits stored functions which the
default rooted pass then removes. This closes the compiler-emitted witness,
rather than relying only on a hand-written IxIR₁ declaration graph. -/
private def compilerReachabilityRemovesUnused : Bool :=
  match compile reachabilityConstants aMain { blobs } with
  | .error _ => false
  | .ok artifact =>
      match artifact.produceHPT with
      | .error _ => false
      | .ok production =>
          let (optimized, report) := artifact.optimizeWithProducedHPT
            IxIR1.Optimizer.defaultPolicy production
          let ctx : IxIR1.Ctx := { decls := optimized.targetDeclEnv }
          let result := IxIR1.runMain ctx optimized.main
          report.disposition == .changed &&
            report.removedDeclarations == 5 &&
            report.before.functions == 6 && report.after.functions == 1 &&
            match result with
            | .ok (store, .loc location) =>
                match store.get? location with
                | some box =>
                    match box.node with
                    | .ctorN cid fields =>
                        cid.block == aSharedCtor && cid.cidx == 1 &&
                          fields.toList == [.lit (.nat 11)]
                    | _ => false
                | none => false
            | _ => false

/-- A double use of the affine parameter is stopped at the first
pipeline gate, before erasure or lowering can observe the program. -/
private def badDropFirst : Constant :=
  { cDropFirst with
    info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .affine .shared boxType
          (.all .many .shared boxType boxType)
        value := .lam .affine boxType
          (.lam .many boxType (.app (.var 1) (.var 1))) } }

private def rejectsBadUsage : Bool :=
  let bad := constants.map fun entry =>
    if entry.1 == aDropFirst then (aDropFirst, badDropFirst) else entry
  match compile bad aMain { blobs } with
  | .error (.usage address (.binderCovers .affine .many)) =>
    address == aDropFirst
  | _ => false

#guard sourceAgrees

/-! ### The validated entry point

The same mixed-mode/add fixture must compile identically through
`compileValidated` (every constant of the fixture is inside the
validator's fragment), and one out-of-fragment declaration must flip
the verdict between the two entry points. -/

private def validated : Except Error Artifact :=
  compileValidated constants aMain { blobs }

/-- `compileValidated` reproduces `compile` on the in-fragment
fixture: the same erased declarations, the same target addresses, and
the same runtime result and cost facts as `targetAgrees` pins. -/
private def validatedAgrees : Bool :=
  match compiled, validated with
  | .ok direct, .ok gated =>
    direct.rawErasedDecls == gated.rawErasedDecls &&
    direct.erasedDecls == gated.erasedDecls &&
    direct.erasedAddressMap == gated.erasedAddressMap &&
    direct.targetAddressMap == gated.targetAddressMap &&
    direct.targetBlocks.map (·.blockAddress) ==
      gated.targetBlocks.map (·.blockAddress) &&
    direct.targetDecls.map (·.1) == gated.targetDecls.map (·.1) &&
    (let targetIndex := IxIR1.Env.Index.ofList gated.targetDecls
     let ctx : IxIR1.Ctx := { decls := targetIndex.toEnv }
     match IxIR1.runMain ctx gated.main with
     | .ok (store, .loc location) =>
       (match store.get? location with
        | some box =>
          match box.node with
          | .ctorN cid fields =>
            cid.block == aSharedCtor && cid.cidx == 1 &&
              fields.toList == [.lit (.nat 22)]
          | _ => false
        | none => false) &&
       store.allocs == 5 && store.frees == 4 && store.rcops == 3 &&
       store.live == 1
     | _ => false)
  | _, _ => false

/-- An axiom is UsageCheck-clean and erases to an extern, so the
unvalidated pipeline accepts it. The certified pipeline rejects the exact
addressed extern graph before lowering and retains that check as a proof field. -/
private def aGhostAxiom := address 0x7c

private def cGhostAxiom : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

private def outOfFragment : List (Address × Constant) :=
  constants ++ [(aGhostAxiom, cGhostAxiom)]

private def acceptsOutOfFragment : Bool :=
  match compile outOfFragment aMain { blobs } with
  | .ok _ => true
  | .error _ => false

private def rejectsOutOfFragment : Bool :=
  match compileValidated outOfFragment aMain { blobs } with
  | .error (.validate rejected message) =>
    rejected == aGhostAxiom &&
      message == "validated extern ownership ABI rejects this declaration"
  | _ => false

/-- Native integration fixtures are evaluated by the compiled test executable:
the cycle-safe block pass invokes the BLAKE3 FFI and therefore cannot live in
an elaboration-time `#guard`. -/
def nativeIntegrationChecks : List (String × Bool) :=
  [("addressed recursor crosses erasure and lowering",
      recursorCrossesBothPasses),
   ("addressed pipeline runtime and cost", targetAgrees),
   ("compiler-produced optimizer report is deterministic and disable-safe",
      optimizerHarnessOnCompiled),
   ("checked optimizer specializes exact destruction and reaches a fixed point",
      optimizerSpecializesDestruction),
   ("compiler-emitted unreachable declarations are removed",
      compilerReachabilityRemovesUnused),
   ("usage rejection precedes addressed erasure", rejectsBadUsage),
   ("validated and direct addressed pipelines agree", validatedAgrees),
   ("unvalidated addressed pipeline accepts configured fragment",
      acceptsOutOfFragment),
   ("validated addressed pipeline rejects uncovered extern",
      rejectsOutOfFragment)]

end Guards

end Ix.Compiler.Pipeline
