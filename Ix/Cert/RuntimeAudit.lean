import Ix.Cert.Compile
import IxC.Kernel.Audit.Runtime

/-! # The compiler's runtime closure, frozen

`#print axioms Ix.Cert.compile` (`Ix.Cert.Audit`) does not show what executes
in place of the logic. This freezes the compiled code `compile` reaches
beyond `Init` and `Std`: the runtime audit
(`Ix.Kernel.Audit.checkRuntimeWith`) with the `csimp` replacements of `Ix`
modules admitted, each only when its theorem depends on the standard axioms
alone, and nothing else. It reports every other replacement it reaches:
* the Rust BLAKE3 primitives and `UInt64.toLEBytes` (`@[extern]`);
* the `partial` definitions of the ground filter, AuxGen, the surgical
  expression compiler, the name and expression printers and the
  name-component walk.

A proof about `compile` meets each of them as an opaque constant. Adding one,
or removing one, changes the list below; the change that re-records it states
why. The expression-table walks (`collectExprTables`, `preseedExprTables`) run
as proved `csimp` replacements (`collectExprTables_eq_worklist`,
`preseedExprTables_eq_worklist`) since they left the list.

`lake run check-kernel` builds this module with the other root audits. No
executable imports it: the runtime audit's controls declare an `@[extern]`
symbol that no library defines, so a binary that links them fails. -/

/-- error: project-level execution replacements reached from [Ix.Cert.compile]:
[Ix.groundExpr,
 Ix.groundLevel,
 UInt64.toLEBytes,
 Blake3.Rust.hasherFinalize,
 Blake3.Rust.hasherInit,
 Blake3.Rust.hasherUpdate,
 Ix.AuxGen.abstractFVar,
 Ix.AuxGen.auxSpecEq,
 Ix.AuxGen.batchAbstract,
 Ix.AuxGen.buildProofForRemaining,
 Ix.AuxGen.canonicalizeConstNames,
 Ix.AuxGen.collectLeanSourceNameHints,
 Ix.AuxGen.collectMemberRefs,
 Ix.AuxGen.consumeTypeAnnotations,
 Ix.AuxGen.ensureInKenvOfInner,
 Ix.AuxGen.exprContainsFVar,
 Ix.AuxGen.exprHasBVar,
 Ix.AuxGen.exprHasLooseBVar,
 Ix.AuxGen.getMaxArgsAux,
 Ix.AuxGen.handleSubstcoreStep,
 Ix.AuxGen.hasDeeperStr,
 Ix.AuxGen.hasIndOcc,
 Ix.AuxGen.hasLooseBVarInExplicitDomain,
 Ix.AuxGen.hasOutOfSccConst,
 Ix.AuxGen.inferImplicit,
 Ix.AuxGen.instantiate1At,
 Ix.AuxGen.instantiateRevAt,
 Ix.AuxGen.isAlreadyNormalizedCheap,
 Ix.AuxGen.isNeverZero,
 Ix.AuxGen.kexprToLean,
 Ix.AuxGen.kunivToLevel,
 Ix.AuxGen.leanExprToKexprCached,
 Ix.AuxGen.leanLevelToKuniv,
 Ix.AuxGen.levelAlphaEqStruct,
 Ix.AuxGen.levelNormalize,
 Ix.AuxGen.levelPretty,
 Ix.AuxGen.levelPrettyAtom,
 Ix.AuxGen.metaDefeq,
 Ix.AuxGen.mkLevelSucc,
 Ix.AuxGen.mkPiUnit,
 Ix.AuxGen.nameAppendAfter,
 Ix.AuxGen.normLtAux,
 Ix.AuxGen.normLtMerge,
 Ix.AuxGen.normLtMergeSort,
 Ix.AuxGen.normalizeLevel,
 Ix.AuxGen.replaceAllNested,
 Ix.AuxGen.replaceConstNamesCached,
 Ix.AuxGen.replaceCtorResultHeadWithAux,
 Ix.AuxGen.replaceFVarsMap,
 Ix.AuxGen.replaceResultSortWithProp,
 Ix.AuxGen.restoreLeanSourceNameHints,
 Ix.AuxGen.restoreSourceNamesSameContent,
 Ix.AuxGen.rewriteNestedConstLevelsCached,
 Ix.AuxGen.rewriteNestedConstLevelsWalk,
 Ix.AuxGen.shiftVars,
 Ix.AuxGen.stripMdata,
 Ix.AuxGen.stripMdataRef,
 Ix.AuxGen.stripPrefixComponents,
 Ix.AuxGen.substFVar,
 Ix.AuxGen.substLevel,
 Ix.AuxGen.substLevelInExpr,
 Ix.AuxGen.substLevelParam,
 Ix.AuxGen.substLevels,
 Ix.AuxGen.toKexprStatic,
 Ix.CompileM.buildCallSite,
 Ix.CompileM.compileAppSpine,
 Ix.CompileM.compileBRecOnCallSite,
 Ix.CompileM.compileBelowCallSite,
 Ix.CompileM.compileExprSurgical,
 Ix.CompileM.compileHeadRewriteCallSite,
 Ix.CompileM.compileRecCallSite,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax,
 Ix.AuxGen.RestoreCtx.replaceWalk,
 Ix.AuxGen.RestoreCtx.replaceWalkUncached,
 Ix.AuxGen.TcScopeSt.isNotZeroLevel,
 Ix.AuxGen.TcScopeSt.kunivToLevelWithConstLevels] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.Cert.compile] #[`Init, `Std] { csimpModules := #[`Ix] }
