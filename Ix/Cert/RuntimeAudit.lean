import Ix.Cert.Compile
import Ix.Cert.CompileCorrect
import Ix.CompileCertified
import IxC.Kernel.Audit.Runtime
import IxC.Kernel.Audit.Roots

/-! # The compiler's runtime closure, frozen

`#print axioms Ix.Cert.compile` (`Ix.Cert.Audit`) does not show what executes
in place of the logic. This freezes the compiled code `compile` reaches
beyond `Init` and `Std`: the runtime audit
(`Ix.Kernel.Audit.checkRuntimeWith`) with the `csimp` replacements of `Ix`
modules admitted, each only when its theorem depends on the standard axioms
alone, and nothing else. It reports every other replacement it reaches:
* the Rust BLAKE3 primitives (`@[extern]`);
* the Ixon codec's `getTagN` and `putTagN` (`getTagN_eq_fast`,
  `putTagN_eq_fast`), with which the reference check (`Ix.Cert.referenceCycle`)
  reads the stored records and the compiler writes them;
* the `partial` definitions of the ground filter, of the inductive flags check
  (`Ix.IndFlags`: `hasIndOcc`, `replaceAllNested`,
  `replaceCtorResultHeadWithAux`, `replaceFVarsMap` and `substLevel`, which
  recompute Lean's nested expansion for `computeLeanIndFlags`), of the name
  and expression printers and of the name-component walk.

A proof about `compile` meets each of them as an opaque constant. Adding one,
or removing one, changes the list below; the change that re-records it states
why. The expression-table walks (`collectExprTables`, `preseedExprTables`) run
as proved `csimp` replacements (`collectExprTables_eq_worklist`,
`preseedExprTables_eq_worklist`) since they left the list.

The compiler compiles Lean's declarations as given: every block's records are
compiled from its Lean declarations, and no auxiliary is regenerated. The code
of the flags check is `Ix.IndFlags`'s.

`lake run check-kernel` builds this module with the other root audits. No
executable imports it: the runtime audit's controls declare an `@[extern]`
symbol that no library defines, so a binary that links them fails. -/

-- The audit finds a substitution at its implementation too: `compile` calls
-- `Address.blake3`, which implements `Address.admissionHash`, so the list names that substitution
-- beside the BLAKE3 primitives it reaches. Nothing else changes.
-- Both `Ix.Cert.compile` (which drives `Ix.Compile.compileEnv` / `compileEnvFold`) and
-- `Ix.Compile.ReadyCompile.reportIO` (the parallel ready-queue driver used by
-- `Ix.CompileM.compileCertifiedPrepared`) are audited here.
-- Binder-data annotation runs inside compilation through `IxC.Kernel` expressions,
-- keys, levels, and names, adding their computed-field constructors/overrides
-- (including `Level.hasParamData`) and `Ix.Kernel.{levelHasParam,Expr.instantiate1Lift,
-- Expr.liftLooseBVars}` csimp replacements to the unruled list (all admitted by
-- `Ix.Kernel.Audit.runtimeRulings` in the checks below).
/-- error: project-level execution replacements reached from [Ix.Cert.compile]:
[Address.admissionHash,
 Ix.groundExpr,
 Ix.groundLevel,
 Ixon.getTagN,
 Ixon.putTagN,
 Blake3.Rust.hasherFinalize,
 Blake3.Rust.hasherInit,
 Blake3.Rust.hasherInitDeriveKey,
 Blake3.Rust.hasherInitKeyed,
 Blake3.Rust.hasherUpdate,
 Ix.IndFlags.hasIndOcc,
 Ix.IndFlags.replaceAllNested,
 Ix.IndFlags.replaceCtorResultHeadWithAux,
 Ix.IndFlags.replaceFVarsMap,
 Ix.IndFlags.substLevel,
 Ix.Kernel.levelHasParam,
 Ix.Kernel.withExclusive,
 Ix.Kernel.withExclusiveUnsafe,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax,
 Ix.Kernel.Expr.app,
 Ix.Kernel.Expr.beq,
 Ix.Kernel.Expr.bvar,
 Ix.Kernel.Expr.casesOn,
 Ix.Kernel.Expr.const,
 Ix.Kernel.Expr.data,
 Ix.Kernel.Expr.forallE,
 Ix.Kernel.Expr.fvar,
 Ix.Kernel.Expr.instantiate1Lift,
 Ix.Kernel.Expr.lam,
 Ix.Kernel.Expr.letE,
 Ix.Kernel.Expr.liftLooseBVars,
 Ix.Kernel.Expr.lit,
 Ix.Kernel.Expr.proj,
 Ix.Kernel.Expr.sort,
 Ix.Kernel.Key.aux,
 Ix.Kernel.Key.beq,
 Ix.Kernel.Key.casesOn,
 Ix.Kernel.Key.hashData,
 Ix.Kernel.Key.id,
 Ix.Kernel.Key.role,
 Ix.Kernel.Level.beq,
 Ix.Kernel.Level.casesOn,
 Ix.Kernel.Level.hasParamData,
 Ix.Kernel.Level.hashData,
 Ix.Kernel.Level.imax,
 Ix.Kernel.Level.max,
 Ix.Kernel.Level.param,
 Ix.Kernel.Level.succ,
 Ix.Kernel.Level.zero,
 Ix.Kernel.Name.anonymous,
 Ix.Kernel.Name.casesOn,
 Ix.Kernel.Name.hashData,
 Ix.Kernel.Name.num,
 Ix.Kernel.Name.str,
 Ix.Kernel.Expr.app._override,
 Ix.Kernel.Expr.bvar._override,
 Ix.Kernel.Expr.casesOn._override,
 Ix.Kernel.Expr.const._override,
 Ix.Kernel.Expr.data._override,
 Ix.Kernel.Expr.forallE._override,
 Ix.Kernel.Expr.fvar._override,
 Ix.Kernel.Expr.lam._override,
 Ix.Kernel.Expr.letE._override,
 Ix.Kernel.Expr.lit._override,
 Ix.Kernel.Expr.proj._override,
 Ix.Kernel.Expr.sort._override,
 Ix.Kernel.Key.aux._override,
 Ix.Kernel.Key.casesOn._override,
 Ix.Kernel.Key.hashData._override,
 Ix.Kernel.Key.id._override,
 Ix.Kernel.Key.role._override,
 Ix.Kernel.Level.casesOn._override,
 Ix.Kernel.Level.hasParamData._override,
 Ix.Kernel.Level.hashData._override,
 Ix.Kernel.Level.imax._override,
 Ix.Kernel.Level.max._override,
 Ix.Kernel.Level.param._override,
 Ix.Kernel.Level.succ._override,
 Ix.Kernel.Level.zero._override,
 Ix.Kernel.Name.anonymous._override,
 Ix.Kernel.Name.casesOn._override,
 Ix.Kernel.Name.hashData._override,
 Ix.Kernel.Name.num._override,
 Ix.Kernel.Name.str._override,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_1,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_impl_2] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.Cert.compile] #[`Init, `Std] { csimpModules := #[`Ix] }

/-- error: project-level execution replacements reached from [Ix.Compile.ReadyCompile.reportIO]:
[Address.admissionHash,
 Ix.groundExpr,
 Ix.groundLevel,
 Ixon.getTagN,
 Ixon.putTagN,
 Blake3.Rust.hasherFinalize,
 Blake3.Rust.hasherInit,
 Blake3.Rust.hasherInitDeriveKey,
 Blake3.Rust.hasherInitKeyed,
 Blake3.Rust.hasherUpdate,
 Ix.IndFlags.hasIndOcc,
 Ix.IndFlags.replaceAllNested,
 Ix.IndFlags.replaceCtorResultHeadWithAux,
 Ix.IndFlags.replaceFVarsMap,
 Ix.IndFlags.substLevel,
 Ix.Kernel.levelHasParam,
 Ix.Kernel.withExclusive,
 Ix.Kernel.withExclusiveUnsafe,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax,
 Ix.Kernel.Expr.app,
 Ix.Kernel.Expr.beq,
 Ix.Kernel.Expr.bvar,
 Ix.Kernel.Expr.casesOn,
 Ix.Kernel.Expr.const,
 Ix.Kernel.Expr.data,
 Ix.Kernel.Expr.forallE,
 Ix.Kernel.Expr.fvar,
 Ix.Kernel.Expr.instantiate1Lift,
 Ix.Kernel.Expr.lam,
 Ix.Kernel.Expr.letE,
 Ix.Kernel.Expr.liftLooseBVars,
 Ix.Kernel.Expr.lit,
 Ix.Kernel.Expr.proj,
 Ix.Kernel.Expr.sort,
 Ix.Kernel.Key.aux,
 Ix.Kernel.Key.beq,
 Ix.Kernel.Key.casesOn,
 Ix.Kernel.Key.hashData,
 Ix.Kernel.Key.id,
 Ix.Kernel.Key.role,
 Ix.Kernel.Level.beq,
 Ix.Kernel.Level.casesOn,
 Ix.Kernel.Level.hasParamData,
 Ix.Kernel.Level.hashData,
 Ix.Kernel.Level.imax,
 Ix.Kernel.Level.max,
 Ix.Kernel.Level.param,
 Ix.Kernel.Level.succ,
 Ix.Kernel.Level.zero,
 Ix.Kernel.Name.anonymous,
 Ix.Kernel.Name.casesOn,
 Ix.Kernel.Name.hashData,
 Ix.Kernel.Name.num,
 Ix.Kernel.Name.str,
 Ix.Kernel.Expr.app._override,
 Ix.Kernel.Expr.bvar._override,
 Ix.Kernel.Expr.casesOn._override,
 Ix.Kernel.Expr.const._override,
 Ix.Kernel.Expr.data._override,
 Ix.Kernel.Expr.forallE._override,
 Ix.Kernel.Expr.fvar._override,
 Ix.Kernel.Expr.lam._override,
 Ix.Kernel.Expr.letE._override,
 Ix.Kernel.Expr.lit._override,
 Ix.Kernel.Expr.proj._override,
 Ix.Kernel.Expr.sort._override,
 Ix.Kernel.Key.aux._override,
 Ix.Kernel.Key.casesOn._override,
 Ix.Kernel.Key.hashData._override,
 Ix.Kernel.Key.id._override,
 Ix.Kernel.Key.role._override,
 Ix.Kernel.Level.casesOn._override,
 Ix.Kernel.Level.hasParamData._override,
 Ix.Kernel.Level.hashData._override,
 Ix.Kernel.Level.imax._override,
 Ix.Kernel.Level.max._override,
 Ix.Kernel.Level.param._override,
 Ix.Kernel.Level.succ._override,
 Ix.Kernel.Level.zero._override,
 Ix.Kernel.Name.anonymous._override,
 Ix.Kernel.Name.casesOn._override,
 Ix.Kernel.Name.hashData._override,
 Ix.Kernel.Name.num._override,
 Ix.Kernel.Name.str._override,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_1,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_impl_2] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.Compile.ReadyCompile.reportIO] #[`Init, `Std] { csimpModules := #[`Ix] }

/-- info: 'Ix.Cert.checkReport_eq_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.checkReport_eq_par

/-- info: 'Ix.Cert.compileReport_eq_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ix.Cert.compileReport_eq_shared

/-! ## The checks that establish `CompileCorrect`'s premises

A user learns that `Ix.Cert.ReaderStreamsTrace.compileCorrect` applies to an
artifact by running these: quotient Source's check at the artifact
(`checkSourceCollapsedBundledAt`), the compile with the artifact's checks
(`compileChecked`, `artifactCheck`), the pinned role closure's certificate
check (`roleEvidenceCheck`), the closure of the roots (`Ix.Cert.closure`) and
the default role table (`defaultTable`). Their compiled code is frozen here.

They run the kernel, so the audit takes the kernel's rulings
(`Ix.Kernel.Audit.runtimeRulings`) with two additions:
* the `csimp` replacements of `Ix` modules, admitted as for `compile`;
* the admission hash's substitution, admitted on its assumption
  (`assumedSubstitutions`).

These are the rulings of the authenticated entries
(`Ixon.Authenticated.Audit.rulings`). Among them:
* the kernel's `csimp` replacements, each admitted only when its equation
  depends on the standard axioms alone;
* the compiler-generated computed fields of the kernel's expressions, levels,
  names and keys, admitted in every kernel closure.

The list that remains is a strict subset of `compile`'s list above: its
`partial` definitions plus the inlined `unsafeImplOf` pointer helper in
`Ix.Sharing.Exact.Basic` surfaced by `Runtime.lean`'s logical-body walk. -/

/-- error: project-level execution replacements reached from [Ix.LeanIngress.checkSourceCollapsedBundledAt,
 Ix.Cert.compileChecked,
 Ix.Cert.artifactCheck,
 Ix.Cert.RoleClosure.roleEvidenceCheck,
 Ix.Cert.closure,
 Ix.Kernel.Reader.defaultTable]:
[Ix.groundExpr,
 Ix.groundLevel,
 Ix.IndFlags.hasIndOcc,
 Ix.IndFlags.replaceAllNested,
 Ix.IndFlags.replaceCtorResultHeadWithAux,
 Ix.IndFlags.replaceFVarsMap,
 Ix.IndFlags.substLevel,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_1,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_impl_2] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  Ix.Kernel.Audit.checkRuntimeWith
    #[``Ix.LeanIngress.checkSourceCollapsedBundledAt, ``Ix.Cert.compileChecked,
      ``Ix.Cert.artifactCheck, ``Ix.Cert.RoleClosure.roleEvidenceCheck, ``Ix.Cert.closure,
      ``Ix.Kernel.Reader.defaultTable]
    #[`Init, `Std]
    { Ix.Kernel.Audit.runtimeRulings with
      csimpModules := Ix.Kernel.Audit.runtimeRulings.csimpModules.push `Ix,
      assumed := Ix.Kernel.Audit.assumedSubstitutions }

/-! ## The CLI certified compiler and role-binding finalizer

`ix compile`, `ix compile-lean`, `ix compile-export` and `ix validate-lean`
invoke `Ix.CompileM.compileAndFinalize`: `Ix.CompileM.compileCertified` (over
`Ix.Compile.ReadyCompile.reportIO`, the parallel ready-queue driver audited
above), `Ix.RoleBinding.Compile.finalize` with the certified backend,
`Ix.CompileM.validateFinalized` and `Ixon.serEnv`. Beyond `Init`, `Std`,
`Lean`, and the `compileChecked` list above, their runtime closure reaches the
source-contract environment extensions, the syntax equality helper, the
Merkle tree builder, the name topological sort, and the `partial` helpers of
role-evidence and role-binding synthesis, frozen here. -/

/-- error: project-level execution replacements reached from [Ix.CompileM.compileAndFinalize]:
[Ix.groundExpr,
 Ix.groundLevel,
 instBEqSyntax_ix.beq,
 Ix.Compile.sourceContractExtension,
 Ix.Compile.sourceDefAssertsExtension,
 Ix.Compile.sourceMeasureExtension,
 Ix.IndFlags.hasIndOcc,
 Ix.IndFlags.replaceAllNested,
 Ix.IndFlags.replaceCtorResultHeadWithAux,
 Ix.IndFlags.replaceFVarsMap,
 Ix.IndFlags.substLevel,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ix.RoleEvidence.instGo,
 Ix.RoleEvidence.instLevelsGo,
 Ix.RoleEvidence.simpGo,
 Ix.RoleEvidence.unfoldGo,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax,
 _private.Ix.Merkle.0.Ix.Merkle.buildTree,
 Ix.RoleBinding.Evidence.countUses,
 Ix.RoleBinding.Evidence.egress,
 _private.Ix.CanonM.0.Ix.CanonM.leanExprPtr.unsafe_1,
 _private.Ix.CanonM.0.Ix.CanonM.leanExprPtr.unsafe_impl_2,
 _private.Ix.CanonM.0.Ix.CanonM.leanLevelPtr.unsafe_1,
 _private.Ix.CanonM.0.Ix.CanonM.leanLevelPtr.unsafe_impl_2,
 _private.Ix.CanonM.0.Ix.CanonM.leanNamePtr.unsafe_1,
 _private.Ix.CanonM.0.Ix.CanonM.leanNamePtr.unsafe_impl_2,
 _private.Ix.Ixon.0.Ixon.Env.topologicalSortNames.visit,
 Ix.RoleBinding.Evidence.egress.build,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.install.unsafe_23,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.install.unsafe_26,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.install.unsafe_impl_24,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.install.unsafe_impl_27,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.phaseAWorkers.unsafe_10,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.phaseAWorkers.unsafe_5,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.phaseAWorkers.unsafe_impl_11,
 _private.Ix.Compile.KernelAnnotate.0.Ix.Compile.KernelAnnotate.phaseAWorkers.unsafe_impl_6,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_1,
 _private.Ix.Sharing.Exact.Basic.0.Ix.Sharing.Exact.exprPtr.unsafe_impl_2] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  Ix.Kernel.Audit.checkRuntimeWith
    #[``Ix.CompileM.compileAndFinalize]
    #[`Init, `Std, `Lean]
    { Ix.Kernel.Audit.runtimeRulings with
      csimpModules := Ix.Kernel.Audit.runtimeRulings.csimpModules.push `Ix,
      assumed := Ix.Kernel.Audit.assumedSubstitutions }
