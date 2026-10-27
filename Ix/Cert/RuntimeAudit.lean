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
the prerequisite of the generator's parametricity proof).

The service's answers do shape `compile`'s result: the levels IxC answers set
the spelling of generated universes (`Ix/AuxGen/LevelEgress.lean`), its `whnf`
results reach generated binder names (`Ix/AuxGen/IxcScope.lean`), and its
refusals fail blocks. That is acceptable for the same reason as any other
compiler output: the records `compile` emits are admitted only through the
certified checker, which checks them again, so an answer can make a block
fail or change its spelling but cannot get an ill-typed record admitted; and
the code that runs is the code this module freezes and audits.

Four expression helpers, `shiftVars`, `instantiateRevAt`, `substLevels` and
`consumeTypeAnnotations`, are total with their existing computation. The
first three recurse structurally; the annotation consumer uses its actual
application-argument subterm bound. These four leave the
opaque-code list; `substLevel` remains. The generated C entry bodies are
unchanged, and the measured compiler replacement list loses exactly these
four entries. No runtime ruling is broadened.

Compiling Lean's declarations as given takes AuxGen's generation and the
Source service off `compile`'s path: a block's records are compiled from its
Lean declarations. The AuxGen code that still runs is the registration of a
block's `Muts` entry (`registerMutualAuxEntry`) and the inductive flags check
(`validateIndGroup`). That removes 78 entries and adds none. AuxGen's
generation loses 31 `partial` definitions
(`abstractFVar`, `auxSpecEq`, `buildProofForRemaining`, `collectMemberRefs`,
`exprContainsFVar`, `exprHasLooseBVar`, `getMaxArgsAux`,
`handleSubstcoreStep`, `hasDeeperStr`, `hasLooseBVarInExplicitDomain`,
`isAlreadyNormalizedCheap`, `isNeverZero`, `levelAlphaEqStruct`,
`levelNormalize`, `levelPretty`, `levelPrettyAtom`, `metaDefeq`,
`mkLevelSucc`, `mkPiUnit`, `nameAppendAfter`, `normLtAux`, `normLtMerge`,
`normLtMergeSort`, `normalizeLevel`, `replaceConstNamesCached`,
`replaceResultSortWithProp`, `rewriteNestedConstLevelsCached`,
`rewriteNestedConstLevelsWalk`, `stripMdata`, `stripMdataRef`, `substFVar`)
and the two restoration walks (`RestoreCtx.replaceWalk`,
`RestoreCtx.replaceWalkUncached`). The Source service's 45 IxC kernel entries
leave with it: the 21 `@[computed_field]` overrides and the 24 kernel
`@[csimp]` replacements listed above. `Ixon.getTagN` stays, reached through
the reference check's codec. The seven AuxGen definitions that remain
(`canonicalizeConstNames`, `hasIndOcc`, `replaceAllNested`,
`replaceCtorResultHeadWithAux`, `replaceFVarsMap`, `stripPrefixComponents`,
`substLevel`) are the flags check's: `computeLeanIndFlags` counts nested
occurrences through the nested expansion `expandNestedBlock`.

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
 Ix.AuxGen.canonicalizeConstNames,
 Ix.AuxGen.hasIndOcc,
 Ix.AuxGen.replaceAllNested,
 Ix.AuxGen.replaceCtorResultHeadWithAux,
 Ix.AuxGen.replaceFVarsMap,
 Ix.AuxGen.stripPrefixComponents,
 Ix.AuxGen.substLevel,
 Ix.Name.pretty,
 Ix.Name.toStringAux,
 Ixon.RawEnv.addNameComponentsWithBlobs,
 _private.Ix.Environment.0.Address.mutsName.go,
 _private.Ix.Environment.0.Ix.Expr.hashSyntax] -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith #[``Ix.Cert.compile] #[`Init, `Std] { csimpModules := #[`Ix] }
