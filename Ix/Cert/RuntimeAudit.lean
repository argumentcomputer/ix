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
* the `partial` definitions of the ground filter, AuxGen, the name and
  expression printers and the name-component walk.

A proof about `compile` meets each of them as an opaque constant. Adding one,
or removing one, changes the list below; the change that re-records it states
why. The expression-table walks (`collectExprTables`, `preseedExprTables`) run
as proved `csimp` replacements (`collectExprTables_eq_worklist`,
`preseedExprTables_eq_worklist`) since they left the list. AuxGen's
`batchAbstract` (through `batchAbstractWith`), `inferImplicit`, `instantiate1At`,
`substLevelInExpr` and `substLevelParam` left it when they became structurally
recursive definitions. `hasOutOfSccConst` left it when the auxiliary
permutation became Pass 1's total `Ix.Compile.Canon.computePerm`; the class
refinement (`Ix.Compile.Canon.sortClasses`) that replaced the compiler's
comparators adds nothing to it. The reference check (Route A, B4,
`Ix.Cert.referenceCycle`) reads the stored records with the Ixon codec's
`getTagN` (`getTagN_eq_fast`, listed below for AuxGen M1) and adds no entry.
The surgical expression compiler's seven `partial` definitions
(`buildCallSite`, `compileAppSpine`, `compileBRecOnCallSite`,
`compileBelowCallSite`, `compileExprSurgical`, `compileHeadRewriteCallSite`,
`compileRecCallSite`) left it when the call-site surgery was deleted (CQ3.5,
dead code since Pass 3: no compile registers a call-site plan).

Retiring AuxGen's Tc backend removes twelve opaque conversion, restoration
and scope helpers from this closure, together with `UInt64.toLEBytes`, which
was reached through their literal encoding. Comparing the same runtime
roots before and after retirement adds no execution replacement: all
existing `csimp` entries, their targets and theorem axioms are unchanged.

**AuxGen M1** (the drivers' Source service, `Ix.AuxGen.Source.Chain`): the
wave fold carries IxC's verified fold over the Source ingress of its input,
so `compile` now reaches IxC's executable kernel, and with it 46 entries,
each one of the replacements IxC's own runtime audit rules on
(`Ix.Kernel.Audit.runtimeRulings`, `IxC/Kernel/Audit/Roots.lean`): the
`@[computed_field]` overrides of the kernel's `Expr`, `Level`, `Name` and
`Key` (21); the kernel's `@[csimp]` replacements (`Ix.Kernel.canonEqList`,
`structProjGuards`, `BinderMeta.shareAlways`, `ConstantInfo.canonEq`,
`ConstantVal.canonEq`, `ConstantVal.matchesPin`, `Msg.withTerms` and 17 of
`Expr`'s operations; 24: the 17th, `Expr.constsResolveBy`, is the IxC lane's
`.indDecl` shape guard's walk, 2026-10-20) and the Ixon codec's `getTagN`
(`getTagN_eq_fast`, reading the committed prelude and evidence bundle; 1),
each on the standard axioms. The in-model generator's nine `partial` definitions
(`IxC/Kernel/Frontend/InModel*`) left the list when its walks became total (IxC, S1:
the prerequisite of the generator's parametricity proof). Nothing the service
computes reaches `compile`'s result.

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
 Ix.AuxGen.abstractFVar,
 Ix.AuxGen.auxSpecEq,
 Ix.AuxGen.buildProofForRemaining,
 Ix.AuxGen.canonicalizeConstNames,
 Ix.AuxGen.collectMemberRefs,
 Ix.AuxGen.consumeTypeAnnotations,
 Ix.AuxGen.exprContainsFVar,
 Ix.AuxGen.exprHasLooseBVar,
 Ix.AuxGen.getMaxArgsAux,
 Ix.AuxGen.handleSubstcoreStep,
 Ix.AuxGen.hasDeeperStr,
 Ix.AuxGen.hasIndOcc,
 Ix.AuxGen.hasLooseBVarInExplicitDomain,
 Ix.AuxGen.instantiateRevAt,
 Ix.AuxGen.isAlreadyNormalizedCheap,
 Ix.AuxGen.isNeverZero,
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
 Ix.AuxGen.rewriteNestedConstLevelsCached,
 Ix.AuxGen.rewriteNestedConstLevelsWalk,
 Ix.AuxGen.shiftVars,
 Ix.AuxGen.stripMdata,
 Ix.AuxGen.stripMdataRef,
 Ix.AuxGen.stripPrefixComponents,
 Ix.AuxGen.substFVar,
 Ix.AuxGen.substLevel,
 Ix.AuxGen.substLevels,
 Ix.Kernel.canonEqList,
 Ix.Kernel.structProjGuards,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax,
 Ix.AuxGen.RestoreCtx.replaceWalk,
 Ix.AuxGen.RestoreCtx.replaceWalkUncached,
 Ix.Kernel.BinderMeta.shareAlways,
 Ix.Kernel.ConstantInfo.canonEq,
 Ix.Kernel.ConstantVal.canonEq,
 Ix.Kernel.ConstantVal.matchesPin,
 Ix.Kernel.Expr.abstract1,
 Ix.Kernel.Expr.allLevelParamsDefined,
 Ix.Kernel.Expr.constsResolveBy,
 Ix.Kernel.Expr.constsResolveF,
 Ix.Kernel.Expr.hasFvar,
 Ix.Kernel.Expr.hasLooseBVarB,
 Ix.Kernel.Expr.instantiate1,
 Ix.Kernel.Expr.instantiate1Lift,
 Ix.Kernel.Expr.instantiateLevelParams,
 Ix.Kernel.Expr.instantiateList,
 Ix.Kernel.Expr.liftLooseBVars,
 Ix.Kernel.Expr.looseBVarsBounded,
 Ix.Kernel.Expr.lowerBVars,
 Ix.Kernel.Expr.mentionsConst,
 Ix.Kernel.Expr.mentionsFvar,
 Ix.Kernel.Expr.renameConsts,
 Ix.Kernel.Expr.resetMeta,
 Ix.Kernel.Msg.withTerms,
 Ix.Kernel.Expr.app._override,
 Ix.Kernel.Expr.bvar._override,
 Ix.Kernel.Expr.const._override,
 Ix.Kernel.Expr.forallE._override,
 Ix.Kernel.Expr.fvar._override,
 Ix.Kernel.Expr.lam._override,
 Ix.Kernel.Expr.letE._override,
 Ix.Kernel.Expr.lit._override,
 Ix.Kernel.Expr.proj._override,
 Ix.Kernel.Expr.sort._override,
 Ix.Kernel.Key.aux._override,
 Ix.Kernel.Key.id._override,
 Ix.Kernel.Key.role._override,
 Ix.Kernel.Level.hashData._override,
 Ix.Kernel.Level.imax._override,
 Ix.Kernel.Level.max._override,
 Ix.Kernel.Level.param._override,
 Ix.Kernel.Level.succ._override,
 Ix.Kernel.Name.hashData._override,
 Ix.Kernel.Name.num._override,
 Ix.Kernel.Name.str._override] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.Cert.compile] #[`Init, `Std] { csimpModules := #[`Ix] }
