import Lean.Elab.Command
import IxC.Kernel.Admission
import IxC.Kernel.Admission.Tier
import Ix.Ixon.Authenticated
import IxC.Kernel.Audit.Runtime
import Ix.Cert.Compile
import Ix.LeanIngress
import Benchmarks.Kernel.CheckIxeMeta

/-! # The display-only read stays out of every certified closure (step 6b)

`Ix.KernelDisplay.peekSquash` is the one `unsafe` step 6b adds: it reads a
display annotation (a `Squash`) to print a name, and it is allowlisted in the
trust-surface fence for that reason alone (`Tests/Ix/Kernel/TrustSurface.lean`).
This module checks, on the compiled code (`Ix.Kernel.Audit.runtimeClosure`,
the walk the frozen root audits use), that no certified root reaches it:

* the verified fold `Ix.Kernel.Cached.checkDecls`, the Ixon reader
  `Ix.Kernel.Reader.readRecords` and the certified entries
  (`Ix.Kernel.Admission.checkBytes`, `checkConstants` and their `With` forms);
* the typing tier's entries (`checkBytesTiered`, `checkConstantsTiered`,
  `Ixon.Authenticated.checkBytesTiered`);
* the compiler `Ix.Cert.compile` and the Source checks
  `Ix.LeanIngress.checkSource` and `checkSourceTiered`, whose terms carry
  Lean's names.

The positive control: the erasure run (`kernel-check-ixe --meta`), which
prints failures with names, does reach it. -/

open Lean Elab Command

/-- info: certified roots reaching the display read: [] -/
#guard_msgs in
run_cmd liftTermElabM do
  let env ← getEnv
  let roots := #[``Ix.Kernel.Cached.checkDecls, ``Ix.Kernel.Reader.readRecords,
    ``Ix.Kernel.Admission.checkBytes, ``Ix.Kernel.Admission.checkBytesWith,
    ``Ix.Kernel.Admission.checkConstants, ``Ix.Kernel.Admission.checkConstantsWith,
    ``Ix.Kernel.Admission.checkBytesTiered, ``Ix.Kernel.Admission.checkConstantsTiered,
    ``Ixon.Authenticated.checkBytesTiered,
    ``Ix.Cert.compile, ``Ix.LeanIngress.checkSource, ``Ix.LeanIngress.checkSourceTiered]
  let hits := roots.filter fun root =>
    (Ix.Kernel.Audit.runtimeClosure env #[root]).visited.contains ``Ix.KernelDisplay.peekSquash
  logInfo m!"certified roots reaching the display read: {hits}"

/-- info: the erasure run reaches the display read: true -/
#guard_msgs in
run_cmd liftTermElabM do
  let env ← getEnv
  let r := Ix.Kernel.Audit.runtimeClosure env #[``Benchmarks.Kernel.CheckIxeMeta.run]
  logInfo m!"the erasure run reaches the display read: \
    {r.visited.contains ``Ix.KernelDisplay.peekSquash}"
