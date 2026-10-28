import Ix.Cert.Compile
import IxC.Kernel.Audit.Runtime

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
`preseedExprTables_eq_worklist`) since they left the list, and the class
refinement (`Ix.Compile.Canon.sortClasses`) adds nothing to it.

The compiler compiles Lean's declarations as given: every block's records are
compiled from its Lean declarations, and no auxiliary is regenerated. The code
of the flags check is `Ix.IndFlags`'s.

`lake run check-kernel` builds this module with the other root audits. No
executable imports it: the runtime audit's controls declare an `@[extern]`
symbol that no library defines, so a binary that links them fails. -/

/-- error: project-level execution replacements reached from [Ix.Cert.compile]:
[Ix.groundExpr,
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
