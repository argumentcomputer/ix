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
* the Ixon codec's `getTagN` (`getTagN_eq_fast`), with which the reference
  check (`Ix.Cert.referenceCycle`) reads the stored records;
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

-- The audit finds a substitution at its implementation too (2026-10-28): `compile` calls
-- `Address.blake3`, which implements `Address.admissionHash`, so the list names that substitution
-- beside the BLAKE3 primitives it reaches. Nothing else changes.
/-- error: project-level execution replacements reached from [Ix.Cert.compile]:
[Address.admissionHash,
 Ix.groundExpr,
 Ix.groundLevel,
 Ixon.getTagN,
 Blake3.Rust.hasherFinalize,
 Blake3.Rust.hasherInit,
 Blake3.Rust.hasherUpdate,
 Ix.IndFlags.hasIndOcc,
 Ix.IndFlags.replaceAllNested,
 Ix.IndFlags.replaceCtorResultHeadWithAux,
 Ix.IndFlags.replaceFVarsMap,
 Ix.IndFlags.substLevel,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.Cert.compile] #[`Init, `Std] { csimpModules := #[`Ix] }

/-- error: project-level execution replacements reached from [Ix.Compile.ReadyCompile.reportIO]:
[Address.admissionHash,
 Ix.groundExpr,
 Ix.groundLevel,
 Ixon.getTagN,
 Blake3.Rust.hasherFinalize,
 Blake3.Rust.hasherInit,
 Blake3.Rust.hasherUpdate,
 Ix.IndFlags.hasIndOcc,
 Ix.IndFlags.replaceAllNested,
 Ix.IndFlags.replaceCtorResultHeadWithAux,
 Ix.IndFlags.replaceFVarsMap,
 Ix.IndFlags.substLevel,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax] -/
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
`partial` definitions. -/

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
 _private.Ix.Environment.0.Ix.Expr.hashSyntax] -/
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

`ix compile` and `ix compile-lean` invoke `Ix.CanonM.canonEnv`,
`Ix.CompileM.compileCertified`, `Ix.CompileM.validateFinalized`,
`Ix.RoleBinding.Compile.finalize`, and `Ixon.serEnv`. Beyond `Init`, `Std`,
`Lean`, and the `compileChecked` list above, their runtime closure reaches the
source-contract environment extensions, the syntax equality helper, the Merkle
tree builder, the name topological sort, and the `partial` helpers of
role-evidence and role-binding synthesis, frozen here. -/

/-- error: project-level execution replacements reached from [Ix.CanonM.canonEnv,
 Ix.CompileM.compileCertified,
 Ix.CompileM.validateFinalized,
 Ix.RoleBinding.Compile.finalize,
 Ixon.serEnv]:
[Ix.groundExpr,
 Ix.groundLevel,
 instBEqSyntax_ix.beq,
 Ix.Compile.sourceContractExtension,
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
 _private.Ix.Ixon.0.Ixon.Env.topologicalSortNames.visit,
 Ix.RoleBinding.Evidence.egress.build] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  Ix.Kernel.Audit.checkRuntimeWith
    #[``Ix.CanonM.canonEnv, ``Ix.CompileM.compileCertified,
      ``Ix.CompileM.validateFinalized, ``Ix.RoleBinding.Compile.finalize,
      ``Ixon.serEnv]
    #[`Init, `Std, `Lean]
    { Ix.Kernel.Audit.runtimeRulings with
      csimpModules := Ix.Kernel.Audit.runtimeRulings.csimpModules.push `Ix,
      assumed := Ix.Kernel.Audit.assumedSubstitutions }
