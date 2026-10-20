import Ix.CompileCert.EmissionBlocks
import Ix.CompileCert.ProjectionLayout
import Ix.CompileCert.InductiveReading

/-! # Inductives through the driver's mutual path (N-READS, N5 b)

The driver (`Ix.CompileM.compileBlockWithAux`) compiles every inductive block,
singletons included, through `compileMutualBlock` over `MutConst.mkIndc`
members, not through `compileConstantInfo (.inductInfo …)` (the
`compileInductiveFamilyBlock` emitter, which `InductiveReading.inductive_reads`
covers; only `compileConstNoAuxPure` takes it). This module carries the family
reading over to the mutual path.

**A one-member inductive class** (`singletonBlock_correct`): `compileMutualBlock
[[.indc d]]` runs the same member emitter as the family path
(`compileMutConstMember (.indc d)` is `compileInductiveData d` under
`withCurrent`, and `compileInductive` is `compileInductiveData` of the
family's `sourceData`, `Emission.compileInductive_eq`), the same sharing
builder over `.muts #[.indc ind]` (`ProjectionLayout.finish_mutual_ok`), and
only the projections differ (`buildMutualProjections`). So the emitted record
keeps the payload's skeleton and reads its roots as terms related to the
source's, as `EmissionBlocks.familyBlock_correct` states for the family path. -/

namespace Ix.CompileCert.MutualInductiveReading

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM MemberReader)

/-- The context `compileMutualBlock classes` runs its members in. -/
def mutContext (classes : List (List MutConst)) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := MutConst.ctx classes })

/-- **A one-member inductive class compiles as its member emitter**:
`compileMutConsts [[.indc d]]` is `compileInductiveData d` under `withCurrent`,
with the payload as its one member and its metadata after the member's name. -/
theorem mutConsts_indc (d : Ix.Ind) {context : CompileEnv × BlockEnv} {before after : BlockState}
    {payload : Array Ixon.MutConst × Array Ixon.Expr × Array (Ix.Name × Ixon.ConstantMeta)}
    (ran : rawRun (compileMutConsts [[.indc d]]) context before = (.ok payload, after)) :
    ∃ out, rawRun (compileInductiveData d) (Emission.current d.name context) before = (.ok out, after) ∧
      payload.1 = #[.indc out.1] ∧ payload.2.2 = #[] ++ (#[(d.name, out.2.1)] ++ out.2.2.1) := by
  unfold compileMutConsts at ran
  obtain ⟨state, middle, classesRan, finish⟩ := bind_ok ran
  rw [rawRun_pure] at finish
  cases finish
  rw [compileMutConstClasses] at classesRan
  obtain ⟨classState, classMiddle, classRan, restRan⟩ := bind_ok classesRan
  rw [compileMutConstClasses, rawRun_pure] at restRan
  cases restRan
  rw [compileMutConstClass] at classRan
  obtain ⟨member, memberMiddle, memberRan, equivRan⟩ := bind_ok classRan
  rw [compileEquivalentMutConsts, rawRun_pure] at equivRan
  cases equivRan
  unfold compileMutConstMember at memberRan
  obtain ⟨out, outMiddle, outRan, wrapRan⟩ := bind_ok memberRan
  unfold withCurrent at outRan
  rw [rawRun_withBlockEnv] at outRan
  obtain ⟨ind, constMeta, ctorMetaPairs, exprs⟩ := out
  dsimp only at wrapRan
  rw [rawRun_pure] at wrapRan
  cases wrapRan
  exact ⟨_, outRan, rfl, rfl⟩

/-! ## A one-member inductive class -/

section Blocks

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
  (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self

/-- **A one-member inductive class reads back as its source** through
`compileMutualBlock`: `EmissionBlocks.familyBlock_correct`'s conclusions, with
the mutual path's projections (`buildMutualProjections`) and the member run in
the class's mutual context (`mutContext`). -/
theorem singletonBlock_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (d : Ix.Ind)
    (scope : ConstsSatisfy (SelfName (mutContext [[.indc d]] context).2 self names) d.type)
    (ctorScope : ∀ ctor ∈ d.ctors.toList,
      ConstsSatisfy (SelfName (mutContext [[.indc d]] context).2 self names) ctor.cnst.type)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileMutualBlock [[.indc d]]) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ metas, output = BlockResult.mk' output.block .empty
        (buildMutualProjections [[.indc d]] (Address.admissionHash (Ixon.ser output.block)) metas)) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (EmissionBlocks.inductiveSkeleton d) ∧
      SharingRoots.RootsRead (EmissionBlocks.recordReader cx param self after output.block)
        (Emission.related param names σ
          (Emission.inner d.name d.levelParams.toList (mutContext [[.indc d]] context)))
        (d.type :: d.ctors.toList.map (·.cnst.type))
        (constantInfoRootExprs output.block.info).toList := by
  unfold compileMutualBlock at ran
  obtain ⟨_, audited, auditRan, rest⟩ := bind_ok ran
  rw [EmissionDispatch.auditClasses_free context free] at auditRan
  cases auditRan
  dsimp only at rest
  unfold withMutCtx at rest
  rw [rawRun_withBlockEnv] at rest
  obtain ⟨_, seededState, seeded, compiled⟩ := bind_ok rest
  have kept := EmissionBlocks.preseed_then cx param self bindings
    (related := Emission.related param names σ
      (Emission.inner d.name d.levelParams.toList (mutContext [[.indc d]] context)))
    (context := mutContext [[.indc d]] context) aligned (clean.good cx param self _) seeded
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  obtain ⟨out, outRan, members, metas⟩ := mutConsts_indc d payloadRan
  obtain ⟨ind, indMeta, pairs, exprs⟩ := out
  obtain ⟨cleanD, growth, shape, ctorShapes, _, roots⟩ := Emission.inductiveData_correct cx param self names σ
    bindings (Emission.current d.name (mutContext [[.indc d]] context)) free aligned external d scope ctorScope
    kept.1 outRan
  obtain ⟨same, _, built⟩ := ProjectionLayout.finish_mutual_ok _ _ _ _ finished
  subst same
  obtain ⟨members', roots', metadata'⟩ := payload
  dsimp only at members metas built
  subst members
  unfold buildCompiledMutualBlock at built
  have standalone : standaloneMutConstInfo? #[Ixon.MutConst.indc ind] = none := rfl
  simp only [standalone] at built
  obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
  cases Except.ok.inj returned
  dsimp only at shape ctorShapes roots
  have rootsList := EmissionBlocks.family_roots ind
  rw [← rootsList] at roots
  obtain ⟨erased, read⟩ := SharingRoots.build_read cx param self after context.1.sharingLimits
    (.muts #[.indc ind]) block hb roots
  refine ⟨cleanD, extends_trans kept.2 growth, ⟨_, rfl⟩, ?_, read⟩
  change SharingRoots.erase block.info = _
  rw [erased, shape]
  exact EmissionBlocks.inductive_erase _ _ _ ctorShapes

end Blocks

/-! ## The one-member class's headers -/

/-- **The headers of a one-member inductive class**: one inductive whose header
and every constructor's header are the source's, as natural numbers
(`InductiveReading.family_headers` over the mutual path). -/
theorem singleton_headers (d : Ix.Ind) :
    Emission.Yields (compileMutualBlock [[.indc d]]) (fun output =>
      ∃ target, output.block.info = .muts #[.indc target] ∧ ProjectionLayout.IndHeader d target ∧
        List.Forall₂ ProjectionLayout.CtorHeader d.ctors.toList target.ctors.toList) := by
  refine ProjectionLayout.mutual_block _ _ ?_
  intro context before output after ran
  unfold compileMutualPayload at ran
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok ran
  obtain ⟨out, outRan, members, _⟩ := mutConsts_indc d payloadRan
  obtain ⟨header, ctorHeaders, _⟩ := ProjectionLayout.inductiveData_headers d _ before out middle outRan
  obtain ⟨ind, indMeta, pairs, exprs⟩ := out
  dsimp only at header ctorHeaders
  obtain ⟨_, _, built⟩ := ProjectionLayout.finish_mutual_ok _ _ _ _ finished
  obtain ⟨members', roots', metadata'⟩ := payload
  dsimp only at members built
  subst members
  unfold buildCompiledMutualBlock at built
  have standalone : standaloneMutConstInfo? #[Ixon.MutConst.indc ind] = none := rfl
  simp only [standalone] at built
  obtain ⟨block, hb, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok built
  cases Except.ok.inj returned
  obtain ⟨erased, _, _, _⟩ := SharingRoots.build_roots (md := .anon) _ _ _ _ _ hb
  obtain ⟨target, info, _, lvls, params, indices, ctors⟩ := InductiveReading.erase_singleton erased
  refine ⟨target, info, ?_, InductiveReading.headers_transfer ctorHeaders ctors⟩
  obtain ⟨headerLvls, headerParams, headerIndices, headerCtors⟩ := header
  have sizes : target.ctors.size = ind.ctors.size := by
    simpa using congrArg List.length ctors
  exact ⟨lvls ▸ headerLvls, params ▸ headerParams, indices ▸ headerIndices, sizes ▸ headerCtors⟩

/-! ## The reading -/

section Reading

open Ix.Kernel.Reader (State BlockShape readRecord lowerInductive)
open Ix.Sharing.Verify (BlockWireTablesWF BlockResultCodecWF)

variable {md : Mode} (cx : Ctx md) (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam)
  (bindings : Bindings)

/-- **A standalone inductive compiled through the driver's mutual path is read
back as its source**: `InductiveReading.inductive_reads` for
`compileMutualBlock [[.indc (sourceData source constructors)]]`, the block the
driver compiles a one-inductive block as (`MutConst.mkIndc` of the source over
its constructors). The self references are given in the class's mutual context
(`scope`, `ctorScope`). -/
theorem inductive_reads_mutual (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : InductiveVal)
    (constructors : Array ConstructorVal) {before after : BlockState} {output : BlockResult}
    (state : State md) {shape : BlockShape} (indexed : cx.index.blocks[output.blockAddr]? = some shape)
    (order : shape.order = #[0]) {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (ctorKey : Nat → CName md)
    (ctorKeyed : ∀ j, j < constructors.size → cx.memberKey (.ctor output.blockAddr 0 j) = .ok (ctorKey j))
    (scope : ConstsSatisfy (SelfName (mutContext [[.indc (Emission.sourceData source constructors)]] context).2
      (InductiveReading.inductiveSelf cx output.blockAddr) names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors.toList,
      ConstsSatisfy (SelfName (mutContext [[.indc (Emission.sourceData source constructors)]] context).2
        (InductiveReading.inductiveSelf cx output.blockAddr) names) ctor.cnst.type)
    (safe : source.isUnsafe = false) (ctorSafe : ∀ ctor ∈ constructors.toList, ctor.isUnsafe = false)
    (positions : ∀ j (inside : j < constructors.size), constructors[j].cidx = j)
    (arity : ∀ ctor ∈ constructors.toList, ∃ types body,
      ReaderSourceSpines.sourceStrip (source.numParams + ctor.numFields) ctor.cnst.type = some (types, body) ∧
        ReaderSourceSpines.SourceNonForall body)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileMutualBlock [[.indc (Emission.sourceData source constructors)]]) context before =
      (.ok output, after)) :
    BlockResultCodecWF output ∧
      ∃ type ctorTypes, InductiveReading.related names σ source source.cnst.type type ∧
        List.Forall₂ (InductiveReading.related names σ source) (constructors.toList.map (·.cnst.type)) ctorTypes ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          InductiveReading.readRecursors (ExpressionRead.withBlockBlobs cx after)
              (List.range source.cnst.levelParams.size) shape.recs >>= fun recs =>
            lowerInductive state (InductiveReading.sourceBlock key ctorKey type ctorTypes source constructors recs) := by
  have codec := EmissionDispatch.mutualBlock_codec context free _ wire ran
  obtain ⟨_, _, _, erased, roots⟩ := singletonBlock_correct cx id (InductiveReading.inductiveSelf cx output.blockAddr)
    names σ bindings context free aligned external (Emission.sourceData source constructors) scope ctorScope clean ran
  obtain ⟨target, info, indHeader, ctorHeaders⟩ :=
    singleton_headers (Emission.sourceData source constructors) _ before output after ran
  obtain ⟨target', info', unsafeEq, ctorUnsafe⟩ := InductiveReading.erase_family erased
  rw [info] at info'
  cases info'
  rw [info, EmissionBlocks.family_roots] at roots
  obtain ⟨⟨type, typeRel, typeRead⟩, ctorRoots⟩ := InductiveReading.rootsRead_cons roots
  obtain ⟨ctorTypes, ctorRels, ctorReadList⟩ := InductiveReading.rootsRead_split ctorRoots
  obtain ⟨lvls, params, indices, _⟩ := indHeader
  simp only [Emission.sourceData] at lvls params indices
  have selfEq : InductiveReading.blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr
      #[Ixon.MutConst.indc target] = InductiveReading.inductiveSelf cx output.blockAddr :=
    InductiveReading.blockSelf_singleton cx after output.blockAddr _
  have typeRead' : (MemberReader.mk' (ExpressionRead.withBlockBlobs cx after) output.block id
      (InductiveReading.blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr #[.indc target])).read
        target.typ = .ok type := by
    rw [selfEq]
    exact typeRead
  have readsMapped : List.Forall₂ (fun (ctor : Ixon.Constructor) ctorType =>
      (MemberReader.mk' (ExpressionRead.withBlockBlobs cx after) output.block id
        (InductiveReading.blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr #[.indc target])).read
          ctor.typ = .ok ctorType) target.ctors.toList ctorTypes := by
    rw [selfEq]
    exact InductiveReading.forall₂_map_left ctorReadList
  have facts := InductiveReading.ctorFacts_of (ExpressionRead.withBlockBlobs cx after) output.blockAddr
    (MemberReader.mk' (ExpressionRead.withBlockBlobs cx after) output.block id
      (InductiveReading.blockSelf (ExpressionRead.withBlockBlobs cx after) output.blockAddr #[.indc target]))
    target.params.toNat ctorKey constructors.toList target.ctors.toList ctorTypes 0 ctorHeaders ctorUnsafe
    readsMapped ctorRels
    (fun k inside => by simpa using positions k (by simpa using inside))
    (fun k inside => by rw [Nat.zero_add]; exact ctorKeyed k (by simpa using inside)) ctorSafe
    (fun ctor present => by rw [params]; exact arity ctor present)
  have read := InductiveReading.readRecord_singleton (ExpressionRead.withBlockBlobs cx after) state output.blockAddr
    output.block target info indexed order (unsafeEq.trans safe) keyed typeRead' ctorKey ctorTypes facts
  refine ⟨codec, type, ctorTypes, typeRel, ctorRels, ?_⟩
  rw [read, lvls, params, indices, InductiveReading.ctorReads_source ctorKey 0 ctorTypes ctorHeaders]
  unfold InductiveReading.sourceBlock
  rfl

end Reading

end Ix.CompileCert.MutualInductiveReading
