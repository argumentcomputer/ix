module

/-!
Typed comparison record for the formal Aiur modular-library refactor
(`docs/formal-aiur-modules.md`).
Replaces `docs/benchmarks/formal-aiur-modules/summary.json`.
-/

@[expose] public section

namespace Benchmarks.FormalAiur.ModulesSummary

structure WorkloadSummary where
  name : String
  equivalentArtifactsModuloNamesAndNoops : Bool
  functions : Nat
  maps : Nat
  chips : Nat
  groups : Nat
  removedEmptyGuards : Nat
  beforeSha256 : String
  afterSha256 : String
  ungroupedFunctionColumns : Nat
  deriving BEq, Repr, Inhabited

structure LibraryValidation where
  nativeTableReferenceTraceComparisons : Nat
  rejectedDishonestHintProofs : Nat
  verifiedU64Blake3Proofs : Nat
  leanU8U32U64DomainOpacityTests : String
  abstractSignatureClientsAndOpaqueHintRejections : String
  deriving BEq, Repr, Inhabited

structure ControllerValidation where
  success : Bool
  commands : Nat
  report : String
  deriving BEq, Repr, Inhabited

structure CpuParityValidation where
  success : Bool
  workloads : Nat
  hardwareValidated : Bool
  report : String
  deriving BEq, Repr, Inhabited

structure IntegrationValidation where
  leanPackagesAndCliBuild : String
  ixvmValidInvalidClaimsAndLegacyBytecodeCheck : String
  recursiveProofAndNegativeCases : String
  aggregationShapesAndNegativeCases : String
  controller : ControllerValidation
  cpuParity : CpuParityValidation
  clippyAndFormat : String
  note : String
  deriving BEq, Repr, Inhabited

structure Summary where
  baselineRevision : String
  legacyProgramRevision : String
  legacyProgramSourcesUnchangedSincePin : Bool
  comparison : String
  workloads : Array WorkloadSummary
  libraryValidation : LibraryValidation
  integrationValidation : IntegrationValidation
  deriving BEq, Repr, Inhabited

def summary : Summary := {
  baselineRevision := "44ea874244a16dd2347c7f2ff1675bad8bc4a258"
  legacyProgramRevision := "827550579ea660a4749c520968ad6f58be63acf4"
  legacyProgramSourcesUnchangedSincePin := true
  comparison := "Complete artifacts equal after global renaming, empty-guard removal with PC relocation, and identity trace assignment removal."
  workloads := #[
    {
      name := "ixvm"
      equivalentArtifactsModuloNamesAndNoops := true
      functions := 828
      maps := 10
      chips := 778
      groups := 112
      removedEmptyGuards := 3404
      beforeSha256 := "1f8c10da7b10587e985d5166b26ad0c7edd4f4cbdfe0978c7deb237cf6683d9a"
      afterSha256 := "d2572d9787a384ba6f4e99d45070407182dcbaaa9791480a31c08167120934fa"
      ungroupedFunctionColumns := 19675
    },
    {
      name := "recursion"
      equivalentArtifactsModuloNamesAndNoops := true
      functions := 224
      maps := 10
      chips := 189
      groups := 39
      removedEmptyGuards := 390
      beforeSha256 := "40e88dd1f84e4f119626189e83f8eb181f6ef9875c190f33cdd7853e83c5afe1"
      afterSha256 := "53a2fe4442dd1db1b082c54ac425930cf4746c1268a2f92f261acfc9e2bba1a3"
      ungroupedFunctionColumns := 5907
    },
    {
      name := "aggregate"
      equivalentArtifactsModuloNamesAndNoops := true
      functions := 285
      maps := 10
      chips := 245
      groups := 39
      removedEmptyGuards := 528
      beforeSha256 := "50638b554026d4db272e725cf07f70d27b280ca9e62b0323a197fa572f21cb60"
      afterSha256 := "aa69584ed7f0e746094f46f367c27d72c3178030a048be86a960436f0ba08f0d"
      ungroupedFunctionColumns := 7878
    }
  ]
  libraryValidation := {
    nativeTableReferenceTraceComparisons := 2586
    rejectedDishonestHintProofs := 2
    verifiedU64Blake3Proofs := 2
    leanU8U32U64DomainOpacityTests := "passed"
    abstractSignatureClientsAndOpaqueHintRejections := "passed"
  }
  integrationValidation := {
    leanPackagesAndCliBuild := "passed"
    ixvmValidInvalidClaimsAndLegacyBytecodeCheck := "passed"
    recursiveProofAndNegativeCases := "passed"
    aggregationShapesAndNegativeCases := "passed"
    controller := {
      success := true
      commands := 19
      report := ".lake/modular-library/integration/controller-check-wa8xjhpn/report.json"
    }
    cpuParity := {
      success := true
      workloads := 3
      hardwareValidated := false
      report := ".lake/modular-library/integration/cuda-check-gmcsnb_g/report.json"
    }
    clippyAndFormat := "passed"
    note := "Initial controller run found the old check_owned name; after adding old/new name compatibility, the controller gate passed. The CPU parity gate was then completed separately."
  }
}

end Benchmarks.FormalAiur.ModulesSummary
