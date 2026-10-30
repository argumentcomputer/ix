import IxC.Kernel.Audit.Axioms
import Ix.Cert.Closure
import Ix.Cert.ConversionValues
import Ix.Cert.Hybrid
import Ix.Cert.ReaderClosureKeys
import Ix.Compile.ReadyCompile
import Ix.HostAdmission.Theorems
import Ix.RoleBinding.ArtifactOrderTheorems
import Ix.RoleBinding.ArtifactTheorems
import Ix.RoleBinding.ArtifactTieredTheorems
import Ix.RoleBinding.Generate

/-! # Axioms of the proof modules outside the statement roots

`Ix/Cert/Audit.lean` fixes the axioms of the certification statements, and so
bounds every declaration they reach. The modules named here are reached by
none of them, or only in part:
* the computed closure (`Ix.Cert.Closure`);
* the theorems of the artifact and host admission entries
  (`Ix.RoleBinding.Artifact*Theorems`, `Ix.HostAdmission.Theorems`);
* parallel canonical record decoding used by artifact-specific generation
  (`Ix.RoleBinding.RecordDecoding`);
* the compiler worker's exact environment read frame (`Ix.Compile.WorkerContext`)
  and the bounded ready-queue scheduler (`Ix.Compile.TaskWindow`,
  `Ix.Compile.WorkerSuccess`, `Ix.Compile.WorkerReplay`,
  `Ix.Compile.ReadyPublication`, `Ix.Compile.ReadyQueue`,
  `Ix.Compile.ReadyCompile`).

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
  Ix.HostAdmission.Theorems
  Ix.RoleBinding.ArtifactOrderTheorems
  Ix.RoleBinding.ArtifactTheorems
  Ix.RoleBinding.ArtifactTieredTheorems
  Ix.RoleBinding.RecordDecoding
  Ix.Compile.WorkerContext
  Ix.Compile.TaskWindow
  Ix.Compile.WorkerSuccess
  Ix.Compile.WorkerReplay
  Ix.Compile.ReadyPublication
  Ix.Compile.ReadyQueue
  Ix.Compile.ReadyCompile

#guard_kernel_axioms Ix.RoleBinding.RecordDecoding.parallel_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.RoleBinding.recordStore_eq_parallel [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.CompileM.WorkerSnapshot.runBlock_same [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.CompileM.waveTasks_eq_projected [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Compile.ReadyCompile.reportIO [propext, Classical.choice, Quot.sound]

#guard_module_axioms_under Ix.Cert Ix.CompileCert
