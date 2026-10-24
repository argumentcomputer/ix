import Tests.Ix.AuxGen.AcceptanceProbe
import Tests.Ix.AuxGen.GenerationOnlyDependencies
import Tests.Ix.Compile.NestedAgreement
import Tests.Ix.AuxGen.PatchReference

/-! W2's real callers: exact patch records and Prop-family recursors against
the retained Tc reference, explicit driver providers, named absence/policy
errors, and non-inductive paths that still need no kernel. -/

namespace Tests.Ix.AuxGen.ExplicitKernel

open _root_.Ix _root_.Ix.AuxGen
open Tests.Ix.AuxGen.BelowIxc (runIn)

deriving instance BEq for AuxDef, BelowDef, BelowCtor, BelowIndc,
  BRecOnDef, PatchedConstant, AuxPatchesOutput

inductive Tree where
  | leaf
  | node : Tree → Tree

inductive Predicate : Tree → Prop where
  | leaf : Predicate .leaf
  | node : Predicate t → Predicate (.node t)

private def need (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError why)

private def refused (r : Except String α) (want : String) : IO Unit := do
  match r with
  | .error e => need (e == want) s!"expected {want}, got {e}"
  | .ok _ => throw (IO.userError s!"unexpected success: {want}")

private def policy (o : AuxOracle) (mode : IxcMode) (recursors : Bool)
    (retry : Option AuxOracle) : AuxOracle :=
  match o with
  | .mk _ trace scope flat below _ asked lazyScope admit status _ family =>
    .mk mode trace scope flat below recursors asked lazyScope admit status retry family

/-- The no-inductive branch must retain both the bytes and complete state
of the provider branch, including the otherwise easy-to-drop Muts entry. -/
private def noKernelPaths : IO Unit := do
  let n (s : String) := Name.mkStr .mkAnon s
  let a := n "W2.A"
  let b := n "W2.B"
  let single := n "W2.single"
  let defn name all level : ConstantInfo := .defnInfo
    { cnst := ⟨name, #[], Expr.mkSort (Level.mkSucc level)⟩
      value := Expr.mkSort level, hints := .abbrev, safety := .safe, all }
  let env : Environment := {
    consts := ({} : Map Name ConstantInfo)
      |>.insert a (defn a #[a, b] .mkZero)
      |>.insert b (defn b #[a, b] (.mkSucc .mkZero))
      |>.insert single (defn single #[single] .mkZero) }
  let cenv := CompileM.CompileEnv.new env
  let unavailable := Ixc.oracleOf .failClosed false { recursors := true } none 0
    (fun _ => .error "non-inductive path forced a service")
  let supplied := { cenv with auxOracle := some (fun _ => some unavailable) }
  let run cenv members key := (CompileM.runBlockWithAux cenv members key).mapError toString
  for members in #[#[single], #[a, b]] do
    let all := members.foldl (fun s n => s.insert n) ({} : Set Name)
    let key := CompileM.blockKey members[0]! all
    let absent ← IO.ofExcept (run cenv all key)
    let explicit ← IO.ofExcept (run supplied all key)
    need (absent == explicit) "non-inductive output/state depends on an unused provider"
    if members.size == 2 then
      need ((absent.1.block.info matches .muts _) && absent.2.1.auxNamed.size == 1 &&
        absent.2.1.auxNamed.all (fun (_, named) => named.constMeta.info matches .muts _ none))
        "non-inductive mutual block lost its Muts entry"

def evaluate : IO Unit := do
  noKernelPaths
  let patchReferences ← IO.ofExcept PatchReference.read
  let leanEnv ← getCompileEnv #[`Tests.Ix.AuxGen.ExplicitKernel,
    `Tests.Ix.Compile.AuxCert.NestedSortUK]
  let env ← Tests.Ix.Kernel.SourceIngress.envOf leanEnv
    #[``Tree.brecOn, ``Predicate.brecOn,
      `Tests.Ix.Compile.Mutual.AlphaCollapse.A.brecOn, `NestedSortUK.T, `NestedSortUK.t_rec]
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense env
  let (_, _, compiled) ← IO.ofExcept (← IO.lazyPure fun _ => CompileM.compileEnvFold env blocks)
  let options : CompileM.AuxIxcOptions := {}
  let source := Source.RunAhead.start env.get? blocks
    (CompileM.scheduleLevels blocks (CompileM.FoldSchedule.of blocks)) options.asks
  let cenv := options.withSourceProviders env.get? blocks source compiled
  let owners := #[Name.fromLeanName ``Tree, Name.fromLeanName ``Predicate,
    Name.fromLeanName `Tests.Ix.Compile.Mutual.AlphaCollapse.A, Name.fromLeanName `NestedSortUK.T]
  let mut checked := 0
  let mut families := 0
  for owner in owners do
    let some rep := blocks.lowLinks.get? owner | throw (IO.userError "fixture owner absent")
    let some members := blocks.blocks.get? rep | throw (IO.userError "fixture block absent")
    let key := CompileM.blockKey rep members
    let all := members.toArray
    let some block ← IO.ofExcept (FlatBlockSource.blockAux compiled key all)
      | throw (IO.userError "flat caller skipped a fixture")
    let maps := AddrMaps.ofCompileEnv compiled
    let legacy ← IO.ofExcept (runIn compiled key
      ((generateAuxPatches block.classes block.originalAll maps (.tc maps)).run AuxKernelCtx.new))
    need (block.out == legacy.1.1 && !block.out.canonicalRecs.isEmpty)
      s!"patch records changed: {owner.pretty}"
    let explicit ← IO.ofExcept (runIn compiled key do
      let kernel ← checkedFamilyKernel compiled maps block.originalAll
      (generateAuxPatches block.classes block.originalAll maps kernel).run AuxKernelCtx.new)
    let ctx := explicit.1.2
    need (ctx.scopeEpoch == 0 && ctx.ingressCache.isEmpty && ctx.auxIngressSeen.isEmpty &&
      ctx.sourceNames.isEmpty && ctx.tcState.env.consts.isEmpty) s!"legacy activity: {owner.pretty}"
    let some probe ← IO.ofExcept (AcceptanceProbe.generate compiled key all)
      | throw (IO.userError "acceptance caller skipped a fixture")
    need (probe.out == block.out) "acceptance caller changed the patch records"
    if !probe.family.isEmpty then
      let mut overlay : Std.HashMap Name ConstantInfo := {}
      for (ind, ctors) in probe.family do
        overlay := overlay.insert ind.cnst.name (.inductInfo ind)
        for ctor in ctors do overlay := overlay.insert ctor.cnst.name (.ctorInfo ctor)
      let expected ← IO.ofExcept (runIn compiled key
        ((generateCanonicalRecursorsWithOverlay (probe.family.map fun (ind, _) => #[ind.cnst.name])
          (some overlay) none (.tc maps)).run AuxKernelCtx.new))
      need (probe.familyRecs == expected.1.1.1 && !probe.familyRecs.isEmpty)
        "checked Prop-family recursors changed"
      families := families + 1
    IO.ofExcept (PatchReference.check patchReferences checked owner block.classes block.originalAll
      block.out probe.family probe.familyRecs)
    let dump ← IO.ofExcept (runIn compiled key (Tests.Compile.AuxGenDiff.leanDumpPatchesBlock key all))
    need ((dump.1.splitOn "patch ").length > 1 && !(dump.1.startsWith "error "))
      "patch dump lost nonempty coverage"
    if owner == Name.fromLeanName `NestedSortUK.T then
      let inds := all.filter fun n => (env.get? n).any (fun c => c matches .inductInfo _)
      let nested := Tests.Ix.Compile.NestedAgreement.compilerScc compiled key inds block.originalAll
      need (nested.err.isNone && nested.canonRecs.toOption.any (!·.isEmpty))
        "nested-agreement caller lost its canonical recursors"
    if owner == Name.fromLeanName ``Tree then
      let run c := (CompileM.runBlockWithAux c members key).mapError toString
      let actual ← IO.ofExcept (run cenv)
      let some oracle := cenv.auxOracle.bind (· key) | throw (IO.userError "ordinary provider absent")
      let reference ← IO.ofExcept (run { cenv with auxOracle := some (fun _ => some oracle) })
      need (actual == reference && !actual.2.1.auxReport.generated.isEmpty)
        "explicit provider changed complete block output"
      let noProvider := { cenv with
        auxOracle := none
        auxGenerationRetry := some (fun _ => .error "missing provider forced retry") }
      let want := s!"unsupportedExpr: AuxGen (configuration): block {key.pretty}: IxC provider is absent"
      refused (run noProvider) want
      refused (run { noProvider with auxOracle := some (fun _ => none) }) want
      let helper c := (runIn c key (checkedFamilyKernel c maps block.originalAll)).map (fun _ => ())
      refused (helper { compiled with sourceFamilyOracle := none })
        s!"unsupportedExpr: source family {owner.pretty}: original-source provider is absent"
      refused (helper { compiled with sourceFamilyOracle := some (fun _ => .error "source sentinel") })
        "unsupportedExpr: source sentinel"
      let checkedOracle ← IO.ofExcept (compiled.familyOracle owner)
      for bad in #[policy checkedOracle .shadow true none, policy checkedOracle .fallback true none,
          policy checkedOracle .fallbackEager true none, policy checkedOracle .failClosed false none,
          policy checkedOracle .failClosed true (some checkedOracle)] do
        refused (helper { compiled with sourceFamilyOracle := some (fun _ => .ok bad) })
          s!"unsupportedExpr: AuxGen diagnostic: {owner.pretty}: failClosed recursor capability without retry required"
    checked := checked + 1
  need (checked == 4 && families ≥ 1) "explicit caller coverage was empty or incomplete"
  IO.println s!"explicit callers: {checked} exact patch records, {families} exact Prop families; missing providers/policies; singleton/mutual no-kernel paths"
  IO.println "patch references: 4 owners, 13 patches, 2 aliases, 5 canonical and 1 Prop recursor; rule/alias perturbations"

end Tests.Ix.AuxGen.ExplicitKernel
