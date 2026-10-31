import Ix.CompileCert.EmissionBlocks
import Ix.CompileCert.ProjectionLayout
import Ix.CompileCert.InductiveReading
import Ix.CompileCert.SourceConstructorPositions

/-! # Inductives through the driver's mutual path

The driver (`Ix.CompileM.compileBlock`) compiles every inductive block,
singletons included, through `compileMutualBlock` over `MutConst.mkIndc`
members, not through `compileConstantInfo (.inductInfo …)` (the
`compileInductiveFamilyBlock` emitter, which `InductiveReading.inductive_reads`
covers). This module carries the family reading over to the mutual path for
a block of one inductive. `Ix.Cert.InductiveCompile` handles families with
several members.

**A one-member inductive block** (`singletonBlock_correct`): `compileMutualBlock
[.indc d]` runs the same member emitter as the family path
(`compileMutConstMember (.indc d)` is `compileInductiveData d` under
`withCurrent`, and `compileInductive` is `compileInductiveData` of the
family's `sourceData`, `Emission.compileInductive_eq`), the same sharing
builder over `.muts #[.indc ind]` (`ProjectionLayout.finish_mutual_ok`), and
only the projections differ (`buildMutualProjections`). So the emitted record
keeps the payload's skeleton and reads its roots as terms related to the
source's, as `EmissionBlocks.familyBlock_correct` states for the family path.

**The block's mutual context is the family's** (`mutCtx_singleton`): the
inductive at slot 0, its constructors after it. So the family path's self
references (`InductiveReading.scope_of_noCtor`: no constructor of the family
occurs, and the family's name is related to its key) serve the mutual path
unchanged.

**The reading** (`inductive_reads_mutual`): `InductiveReading.inductive_reads`'
reading, for `compileMutualBlock [.indc (sourceData source constructors)]`.

`MutConst.mkIndc`'s constructors are the compile environment's
(`mkIndc_constructors`). -/

namespace Ix.CompileCert.MutualInductiveReading

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM MemberReader)

/-- The context `compileMutualBlock classes` runs its members in. -/
def mutContext (classes : List MutConst) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := MutConst.ctx classes })

/-- **A one-member inductive block compiles as its member emitter**:
`compileMutConsts [.indc d]` is `compileInductiveData d` under `withCurrent`,
with the payload as its one member and its metadata after the member's name. -/
theorem mutConsts_indc (d : Ix.Ind) {context : CompileEnv × BlockEnv} {before after : BlockState}
    {payload : Array Ixon.MutConst × Array Ixon.Expr × Array (Ix.Name × Ixon.ConstantMeta)}
    (ran : rawRun (compileMutConsts [.indc d]) context before = (.ok payload, after)) :
    ∃ out, rawRun (compileInductiveData d) (Emission.current d.name context) before = (.ok out, after) ∧
      payload.1 = #[.indc out.1] ∧ payload.2.2 = #[] ++ (#[(d.name, out.2.1)] ++ out.2.2.1) := by
  unfold compileMutConsts at ran
  obtain ⟨state, middle, classesRan, finish⟩ := bind_ok ran
  rw [rawRun_pure] at finish
  cases finish
  rw [compileMutConstMembers] at classesRan
  obtain ⟨member, memberMiddle, memberRan, restRan⟩ := bind_ok classesRan
  rw [compileMutConstMembers, rawRun_pure] at restRan
  cases restRan
  unfold compileMutConstMember at memberRan
  obtain ⟨out, outMiddle, outRan, wrapRan⟩ := bind_ok memberRan
  unfold withCurrent at outRan
  rw [rawRun_withBlockEnv] at outRan
  obtain ⟨ind, constMeta, ctorMetaPairs, exprs⟩ := out
  dsimp only at wrapRan
  rw [rawRun_pure] at wrapRan
  cases wrapRan
  exact ⟨_, outRan, rfl, rfl⟩

/-- **A one-inductive block's mutual context is the family's**: the inductive
at slot 0 and its constructors after it, as `buildInductiveMutCtx` lays
them out. -/
theorem mutCtx_singleton (source : InductiveVal) (constructors : Array ConstructorVal) :
    MutConst.ctx [.indc (Emission.sourceData source constructors)] = buildInductiveMutCtx source constructors := by
  have unfolded : buildInductiveMutCtx source constructors =
      constructors.zipIdx.foldl (fun ctx entry => ctx.insert entry.1.cnst.name (entry.2 + 1))
        ((Std.TreeMap.empty : Ix.MutCtx).insert source.cnst.name 0) := by
    simp [buildInductiveMutCtx]
  rw [Canon.ctx_fold, unfolded, ← Array.foldl_toList, Array.toList_zipIdx]
  simp only [Canon.ctxPairs, Canon.pairsOf, List.append_nil,
    List.foldl_cons, List.foldl_map, List.length_singleton, MutConst.name, MutConst.ctors, Emission.sourceData]
  have same : (fun (acc : Ix.MutCtx) (entry : ConstructorVal × Nat) => Canon.insP acc (entry.1.cnst.name, 1 + entry.2)) =
      fun acc entry => acc.insert entry.1.cnst.name (entry.2 + 1) := by
    funext acc entry
    simp only [Canon.insP, Nat.add_comm]
  rw [same]
  rfl

/-- **The block's environment is the family's**: `compileMutualBlock
[.indc (sourceData source constructors)]` runs its member in the block
environment the family compile installs. -/
theorem mutBlock_family (source : InductiveVal) (constructors : Array ConstructorVal)
    (context : CompileEnv × BlockEnv) :
    (mutContext [.indc (Emission.sourceData source constructors)] context).2 =
      InductiveReading.familyBlock source constructors context := by
  unfold mutContext InductiveReading.familyBlock EmissionDispatch.familyContext EmissionDispatch.singletonContext
  rw [mutCtx_singleton]

/-! ## A one-member inductive block -/

section Blocks

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam) (self : Nat → Option (ReadM (CName md)))
  (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self

/-- **A one-member inductive block reads back as its source** through
`compileMutualBlock`: `EmissionBlocks.familyBlock_correct`'s conclusions, with
the mutual path's projections (`buildMutualProjections`) and the member run in
the block's mutual context (`mutContext`). -/
theorem singletonBlock_correct (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (d : Ix.Ind)
    (scope : ConstsSatisfy (SelfName (mutContext [.indc d] context).2 self names) d.type)
    (ctorScope : ∀ ctor ∈ d.ctors.toList,
      ConstsSatisfy (SelfName (mutContext [.indc d] context).2 self names) ctor.cnst.type)
    {before after : BlockState} {output : BlockResult} (clean : Emission.Clean bindings before)
    (ran : rawRun (compileMutualBlock [.indc d]) context before = (.ok output, after)) :
    Emission.Clean bindings after ∧ ExpressionRead.Extends (reader before).ecx (reader after).ecx ∧
      (∃ metas, output = BlockResult.mk' output.block .empty
        (buildMutualProjections [.indc d] (Address.admissionHash (Ixon.ser output.block)) metas)) ∧
      SharingRoots.erase output.block.info = SharingRoots.erase (EmissionBlocks.inductiveSkeleton d) ∧
      SharingRoots.RootsRead (EmissionBlocks.recordReader cx param self after output.block)
        (Emission.related param names σ
          (Emission.inner d.name d.levelParams.toList (mutContext [.indc d] context)))
        (d.type :: d.ctors.toList.map (·.cnst.type))
        (constantInfoRootExprs output.block.info).toList := by
  unfold compileMutualBlock at ran
  dsimp only at ran
  unfold withMutCtx at ran
  rw [rawRun_withBlockEnv] at ran
  obtain ⟨_, seededState, seeded, compiled⟩ := bind_ok ran
  have kept := EmissionBlocks.preseed_then cx param self bindings
    (related := Emission.related param names σ
      (Emission.inner d.name d.levelParams.toList (mutContext [.indc d] context)))
    (context := mutContext [.indc d] context) aligned (clean.good cx param self _) seeded
  unfold compileMutualPayload at compiled
  obtain ⟨payload, middle, payloadRan, finished⟩ := bind_ok compiled
  obtain ⟨out, outRan, members, metas⟩ := mutConsts_indc d payloadRan
  obtain ⟨ind, indMeta, pairs, exprs⟩ := out
  obtain ⟨cleanD, growth, shape, ctorShapes, _, roots⟩ := Emission.inductiveData_correct cx param self names σ
    bindings (Emission.current d.name (mutContext [.indc d] context)) aligned external d scope ctorScope
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

/-! ## The one-member block's headers -/

/-- **The headers of a one-member inductive block**: one inductive whose header
and every constructor's header are the source's, as natural numbers
(`InductiveReading.family_headers` over the mutual path). -/
theorem singleton_headers (d : Ix.Ind) :
    Emission.Yields (compileMutualBlock [.indc d]) (fun output =>
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

/-! ## The driver's members -/

/-- **`MutConst.mkIndc`'s constructors are the compile environment's**: an
inductive member it builds over `constructors` has, under each of the
source's constructor names, the constructor the environment has there, in
order. -/
theorem mkIndc_constructors (context : CompileEnv × BlockEnv) (source : InductiveVal)
    (constructors : Array ConstructorVal) {made : BlockState}
    (found : (rawRun (MutConst.mkIndc source) context made).1 = .ok (.indc (Emission.sourceData source constructors))) :
    List.Forall₂ (fun n c => context.1.env.get? n = some (.ctorInfo c)) source.ctors.toList constructors.toList := by
  obtain ⟨cs, looked, same⟩ := SourceConstructorPositions.mkIndc_lookups context source made found
  have ctors : constructors = cs.toArray := congrArg MutConst.ctors same
  rw [ctors, List.toList_toArray]
  exact looked

/-! ## The reading -/

section Reading

open Ix.Kernel.Reader (State BlockShape readRecord lowerInductive)
open Ix.Sharing.Verify (BlockWireTablesWF BlockResultCodecWF)

variable {md : Mode} (cx : Ctx md) (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam)
  (bindings : Bindings)

/-- **A standalone inductive compiled through the driver's mutual path is read
back as its source**: `InductiveReading.inductive_reads` for
`compileMutualBlock [.indc (sourceData source constructors)]`, the block the
driver compiles a one-inductive block as (`MutConst.mkIndc` of the source over
its constructors). The premises are `inductive_reads`': the self references
(the family's own name related to its key, `selfKey`, and no
constructor of the family in its types, `NoCtorIn`) serve the class's mutual
context, which is the family's (`mutBlock_family`). -/
theorem inductive_reads_mutual (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : InductiveVal)
    (constructors : Array ConstructorVal) {before after : BlockState} {output : BlockResult}
    (state : State md) {shape : BlockShape} (indexed : cx.index.blocks[output.blockAddr]? = some shape)
    (order : shape.order = #[0]) {key : CName md} (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (ctorKey : Nat → CName md)
    (ctorKeyed : ∀ j, j < constructors.size → cx.memberKey (.ctor output.blockAddr 0 j) = .ok (ctorKey j))
    (selfKey : names source.cnst.name key)
    (typeNoCtor : InductiveReading.NoCtorIn constructors source.cnst.type)
    (ctorNoCtor : ∀ ctor ∈ constructors.toList, InductiveReading.NoCtorIn constructors ctor.cnst.type)
    (safe : source.isUnsafe = false) (ctorSafe : ∀ ctor ∈ constructors.toList, ctor.isUnsafe = false)
    (positions : ∀ j (inside : j < constructors.size), constructors[j].cidx = j)
    (arity : ∀ ctor ∈ constructors.toList, ∃ types body,
      ReaderSourceSpines.sourceStrip (source.numParams + ctor.numFields) ctor.cnst.type = some (types, body) ∧
        ReaderSourceSpines.SourceNonForall body)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileMutualBlock [.indc (Emission.sourceData source constructors)]) context before =
      (.ok output, after)) :
    BlockResultCodecWF output ∧
      ∃ type ctorTypes, InductiveReading.related names σ source source.cnst.type type ∧
        List.Forall₂ (InductiveReading.related names σ source) (constructors.toList.map (·.cnst.type)) ctorTypes ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          InductiveReading.readRecursors (ExpressionRead.withBlockBlobs cx after)
              (List.range source.cnst.levelParams.size) shape.recs >>= fun recs =>
            lowerInductive state (InductiveReading.sourceBlock key ctorKey type ctorTypes source constructors recs) := by
  have codec := EmissionDispatch.mutualBlock_codec context _ wire ran
  have scope : ∀ {e : Ix.Expr}, InductiveReading.NoCtorIn constructors e →
      ConstsSatisfy (SelfName (mutContext [.indc (Emission.sourceData source constructors)] context).2
        (InductiveReading.inductiveSelf cx output.blockAddr) names) e := by
    intro e noCtor
    rw [mutBlock_family]
    exact InductiveReading.scope_of_noCtor cx names source constructors context output.blockAddr keyed selfKey noCtor
  obtain ⟨_, _, _, erased, roots⟩ := singletonBlock_correct cx id (InductiveReading.inductiveSelf cx output.blockAddr)
    names σ bindings context aligned external (Emission.sourceData source constructors) (scope typeNoCtor)
    (fun ctor present => scope (ctorNoCtor ctor present)) clean ran
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
