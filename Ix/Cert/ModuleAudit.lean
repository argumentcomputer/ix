import IxC.Kernel.Audit.Axioms
import Ix.Cert.Canon
import Ix.Cert.Closure
import Ix.Cert.CompileCorrect
import Ix.Cert.ConversionValues
import Ix.Cert.Hybrid
import Ix.Cert.ReaderClosureKeys
import Ix.Cert.TableAdmission
import Ix.Compile.ReadyCompile
import Ix.CompileCertified
import Ix.HostAdmission.Theorems
import Ix.LeanIngress.NominalQuotient
import Ix.RoleBinding.ArtifactOrderTheorems
import Ix.RoleBinding.ArtifactTheorems
import Ix.RoleBinding.ArtifactTieredTheorems
import Ix.RoleBinding.Generate

/-! # Axioms of the proof modules outside the statement roots

`Ix/Cert/Audit.lean` fixes the axioms of the certification statements, and so
bounds every declaration they reach. The modules named here are reached by
none of them, or only in part:
* the computed closure (`Ix.Cert.Closure`);
* the executed admission of a role table (`Ix.Cert.TableAdmission`);
* the theorems of the artifact and host admission entries
  (`Ix.RoleBinding.Artifact*Theorems`, `Ix.HostAdmission.Theorems`);
* parallel canonical record decoding used by artifact-specific generation
  (`Ix.RoleBinding.RecordDecoding`);
* the compiler worker's exact environment read frame (`Ix.Compile.WorkerContext`)
  and the bounded ready-queue scheduler (`Ix.Compile.TaskWindow`,
  `Ix.Compile.WorkerSuccess`, `Ix.Compile.WorkerReplay`,
  `Ix.Compile.ReadyPublication`, `Ix.Compile.ReadyQueue`,
  `Ix.Compile.ReadyCompile`);
* the front end, driver, role-binding generator, and certified compiler entry
  (`Ix.Compile.FrontEnd`, `Ix.CompileDriver`, `Ix.RoleBinding.Generate`,
  `Ix.CompileCertified`).

`lake lint` (`check-modules`) and `lake run check-kernel` build this module.

Every safe declaration of each named module, and of every `Ix.Cert` and
`Ix.CompileCert` module this module imports, depends on no axiom beyond
`propext`, `Classical.choice` and `Quot.sound` (`#guard_module_axioms`,
`IxC/Kernel/Audit/Axioms.lean`). Importing the IO pipeline's agreement
(`Ix.Cert.Hybrid`), the checked conversion values (`Ix.Cert.ConversionValues`)
and the reader's closure keys (`Ix.Cert.ReaderClosureKeys`) keeps the
expression, emission, preseed and universe proofs they import under that
bound. A named module fails if it is no longer imported or declares nothing. -/

#guard_module_axioms
  Ix.Cert.Closure
  Ix.Cert.TableAdmission
  Ix.HostAdmission.Theorems
  Ix.RoleBinding.ArtifactOrderTheorems
  Ix.RoleBinding.ArtifactTheorems
  Ix.RoleBinding.ArtifactTieredTheorems
  Ix.RoleBinding.RecordDecoding
  Ix.RoleBinding.Generate
  Ix.Compile.FrontEnd
  Ix.CompileDriver
  Ix.Compile.WorkerContext
  Ix.Compile.TaskWindow
  Ix.Compile.WorkerSuccess
  Ix.Compile.WorkerReplay
  Ix.Compile.ReadyPublication
  Ix.Compile.ReadyQueue
  Ix.Compile.ReadyCompile
  Ix.CompileCertified
  Ix.LeanIngress.Theorems
  Ix.LeanIngress.NominalQuotient

#guard_kernel_axioms Ix.RoleBinding.RecordDecoding.parallel_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.recordStore_eq_parallel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.CompileM.WorkerSnapshot.runBlock_same [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.CompileM.waveTasks_eq_projected [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Compile.ReadyCompile.reportIO [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.LeanIngress.prepareSourceCollapsedAt_trace [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.LeanIngress.Converted.quotient_eq_substKeys_canon [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.LeanIngress.canonDecl_substKeys [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.LeanIngress.checkGroupFiberSafe_sound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.LeanIngress.collapseRead_substKeys_canon_beqF [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.EnvSubstRel.toModelPullback [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.EnvSubstRel.toPullback [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxonCommutesCovering.nominalModelPullback [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxonCommutesCovering.nominalBridgeAt [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.IxonCommutesCovering.nominalPullback [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.NominalSemanticBridgeAt.of_covering [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.CompileCorrect.nominalBridgeAt [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.CompileCorrect.nominalPullback [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.model_exists_of_no_user_axioms [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_consistent [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.checkDeclsWithUserAxioms_sound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.no_proof_of_False_cached_userAxioms [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.TableAdmission.tableAdmitted_of_check [propext, Classical.choice, Quot.sound]

#guard_module_axioms_under Ix.Cert Ix.CompileCert
