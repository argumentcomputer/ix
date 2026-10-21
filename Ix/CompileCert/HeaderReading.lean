import Ix.CompileCert.DefinitionReading

/-! # Compiled axioms and quotients are read back as their sources

Public dispatch of an axiom or a quotient compiles one singleton block
(`EmissionDispatch.axiom_run`, `quotient_run`). The certified reader reads
such a record with `readRecord`: an unsafe axiom is declined before its
type is read; otherwise the record contributes one declaration under its
key (`Ctx.memberKey (.member owner 0)`), with level parameters
`List.range lvls` and the reading of its type by `ReaderSpec.headerReader`
(universe variables positional, no `recur`).

`axiom_reads` and `quotient_reads` compose the compile-side theorems
(`EmissionBlocks.axiomInfo_correct`, `quotientInfo_correct`, with exactly
that reader) with the reader: a successful compile from a clean state, whose
type does not mention the declaration itself (the reader has no self slot
for a header) and whose record's key reads, reads as exactly the expected
declaration, with a type `Related` to the source's; the block decodes
exactly; an unsafe axiom is declined (`axiom_declines`, with no other
premise). CT-16's `HeaderReading`, adapted to `memberKey` and positional
levels. Under `surgeryFree` until CQ3.5. -/

namespace Ix.CompileCert.HeaderReading

open Ix.CompileM Ix.CompileCert Ix.CompileCert.ExpressionState Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader
open Ix.Sharing.Verify (BlockWireTablesWF BlockResultCodecWF)

variable {md : Mode}

/-! ## The reader on header records -/

theorem readAxiom_ok (cx : Ctx md) (state : State md) (owner : Address) (record : Ixon.Constant)
    (target : Ixon.Axiom) (info : record.info = .axio target) (safe : target.isUnsafe = false)
    {key : CName md} {type : CExpr md} (keyed : cx.memberKey (.member owner 0) = .ok key)
    (typeRead : (headerReader cx record).read target.typ = .ok type) :
    readRecord cx state owner record =
      .ok { decls := #[.axiomDecl ⟨key, singletonLps target.lvls, type⟩] } := by
  unfold readRecord
  rw [info]
  simp only [headerReader] at typeRead
  simp only [safe, Bool.false_eq_true, ↓reduceIte, keyed, typeRead, bind, Except.bind, pure, Except.pure,
    singletonLps]

theorem readAxiom_declines (cx : Ctx md) (state : State md) (owner : Address) (record : Ixon.Constant)
    (target : Ixon.Axiom) (info : record.info = .axio target) (unsafeTarget : target.isUnsafe = true) :
    readRecord cx state owner record = .error (.declined "unsafe axiom") := by
  unfold readRecord
  rw [info]
  simp [unsafeTarget, declined, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem readQuotient_ok (cx : Ctx md) (state : State md) (owner : Address) (record : Ixon.Constant)
    (target : Ixon.Quotient) (info : record.info = .quot target)
    {key : CName md} {type : CExpr md} (keyed : cx.memberKey (.member owner 0) = .ok key)
    (typeRead : (headerReader cx record).read target.typ = .ok type) :
    readRecord cx state owner record =
      .ok { decls := #[.quotDecl (quotKind target.kind) ⟨key, singletonLps target.lvls, type⟩] } := by
  unfold readRecord
  rw [info]
  simp only [headerReader] at typeRead
  simp only [keyed, typeRead, bind, Except.bind, pure, Except.pure, singletonLps]
  obtain ⟨kind, lvls, typ⟩ := target
  cases kind <;> rfl

/-! ## The compiled records -/

theorem erase_axio {info : Ixon.ConstantInfo} {payload : Ixon.Axiom}
    (same : SharingRoots.erase info = SharingRoots.erase (.axio payload)) :
    ∃ target : Ixon.Axiom, info = .axio target ∧ target.isUnsafe = payload.isUnsafe ∧
      target.lvls = payload.lvls := by
  cases info with
  | axio target =>
    have inner : Ixon.ConstantInfo.axio { target with typ := .sort 0 } =
        .axio { payload with typ := .sort 0 } := same
    have fields := Ixon.ConstantInfo.axio.inj inner
    refine ⟨target, rfl, ?_, ?_⟩
    · have field := congrArg Ixon.Axiom.isUnsafe fields; exact field
    · have field := congrArg Ixon.Axiom.lvls fields; exact field
  | _ => cases same

theorem erase_quot {info : Ixon.ConstantInfo} {source : QuotVal}
    (same : SharingRoots.erase info = SharingRoots.erase (EmissionBlocks.quotientSkeleton source)) :
    ∃ target : Ixon.Quotient, info = .quot target ∧ target.kind = convertQuotKind source.kind ∧
      target.lvls = source.cnst.levelParams.size.toUInt64 := by
  cases info with
  | quot target =>
    have inner : Ixon.ConstantInfo.quot { target with typ := .sort 0 } =
        .quot (Emission.quotientPayload source (.sort 0)) := same
    have fields := Ixon.ConstantInfo.quot.inj inner
    exact ⟨target, rfl, congrArg Ixon.Quotient.kind fields, congrArg Ixon.Quotient.lvls fields⟩
  | _ => cases same

theorem axiomInfo_levels (source : AxiomVal) :
    Emission.Yields (compileAxiomInfo source) (fun output =>
      ∀ target : Ixon.Axiom, output.block.info = .axio target →
        target.lvls.toNat = source.cnst.levelParams.size) := by
  intro context before output after ran
  unfold compileAxiomInfo at ran
  obtain ⟨_, middle, _, compiled⟩ := bind_ok ran
  unfold compileAxiomBlock at compiled
  obtain ⟨payload, payloadRan, built, _⟩ := EmissionBlocks.block_ok (fun payload => .axio payload.1)
    (fun payload => payload.2.1) (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) compiled
  have header := Emission.axiomPayload_header source context middle payload after payloadRan
  obtain ⟨erased, _, _, _⟩ := SharingRoots.build_roots (md := .anon) _ _ _ _ _ built
  intro target info
  rw [info] at erased
  have fields := Ixon.ConstantInfo.axio.inj (show Ixon.ConstantInfo.axio { target with typ := .sort 0 } =
    .axio { payload.1 with typ := .sort 0 } from erased)
  have lvlsEq : target.lvls = payload.1.lvls := by
    have same := congrArg Ixon.Axiom.lvls fields; exact same
  rw [lvlsEq]
  exact header

theorem quotientInfo_levels (source : QuotVal) :
    Emission.Yields (compileQuotientInfo source) (fun output =>
      ∀ target : Ixon.Quotient, output.block.info = .quot target →
        target.lvls.toNat = source.cnst.levelParams.size) := by
  intro context before output after ran
  unfold compileQuotientInfo at ran
  obtain ⟨_, middle, _, compiled⟩ := bind_ok ran
  unfold compileQuotientBlock at compiled
  obtain ⟨payload, payloadRan, built, _⟩ := EmissionBlocks.block_ok (fun payload => .quot payload.1)
    (fun payload => payload.2.1) (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) compiled
  have header := Emission.quotientPayload_header source context middle payload after payloadRan
  obtain ⟨erased, _, _, _⟩ := SharingRoots.build_roots (md := .anon) _ _ _ _ _ built
  intro target info
  rw [info] at erased
  have fields := Ixon.ConstantInfo.quot.inj (show Ixon.ConstantInfo.quot { target with typ := .sort 0 } =
    .quot { payload.1 with typ := .sort 0 } from erased)
  have lvlsEq : target.lvls = payload.1.lvls := by
    have same := congrArg Ixon.Quotient.lvls fields; exact same
  rw [lvlsEq]
  exact header

section Reading

variable (cx : Ctx md) (names : Ix.Name → CName md → Prop) (σ : Ix.Name → LevelParam) (bindings : Bindings)

/-- **A compiled axiom is read back as its source**: public dispatch, under
an environment without Pass 3 records, from a clean state whose tables are
on the wire, returns a block that decodes exactly and that `readRecord` reads
as exactly the axiom declaration of the record's key, the level parameters
`0, …, n - 1` and a type related to the source's; given that the type does
not mention the declaration itself, that the record's key reads, and that
the axiom is safe. -/
theorem axiom_reads (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : AxiomVal)
    {before after : BlockState} {output : BlockResult} (state : State md) {key : CName md}
    (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (scope : ConstsSatisfy (SelfName (EmissionDispatch.singletonContext source.cnst.name context).2
      (fun _ => none) names) source.cnst.type)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (safe : source.isUnsafe = false)
    (ran : rawRun (compileConstantInfo (.axiomInfo source)) context before = (.ok output, after)) :
    BlockResultCodecWF output ∧ (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      ∃ type, Related names (LevelMeaning source.cnst.levelParams.toList σ id) source.cnst.type type ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          .ok { decls := #[.axiomDecl ⟨key, List.range source.cnst.levelParams.size, type⟩] } := by
  have codec := EmissionDispatch.constant_codec context free _ wire ran
  rw [EmissionDispatch.axiom_run context free] at ran
  have levels := axiomInfo_levels source _ before output after ran
  obtain ⟨_, _, wrapped, erased, roots⟩ := EmissionBlocks.axiomInfo_correct cx id (fun _ => none) names σ bindings
    (EmissionDispatch.singletonContext source.cnst.name context) free aligned external source scope clean ran
  obtain ⟨target, info, unsafeEq, lvls⟩ := erase_axio (payload := Emission.axiomPayload source (.sort 0)) erased
  have count := levels target info
  rw [info] at roots
  cases roots with
  | cons head _ =>
    obtain ⟨type, typeRel, typeRead⟩ := head
    have keyed' : (ExpressionRead.withBlockBlobs cx after).memberKey (.member output.blockAddr 0) = .ok key :=
      keyed
    have read := readAxiom_ok (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block target
      info (unsafeEq.trans safe) keyed' typeRead
    have range : singletonLps target.lvls = List.range source.cnst.levelParams.size := by
      unfold singletonLps
      rw [count]
    rw [range] at read
    exact ⟨codec, wrapped, type, typeRel, read⟩

/-- A successful axiom payload keeps the source's safety flag. -/
theorem axiom_unsafe (source : AxiomVal) :
    Emission.Yields (compileAxiom source) (fun output => output.1.isUnsafe = source.isUnsafe) := by
  unfold compileAxiom
  refine Emission.Yields.withCurrent _ (Emission.Yields.withUnivCtx _
    (Emission.Yields.bindAny _ fun _ => Emission.Yields.bindAny _ fun typed => ?_))
  obtain ⟨typeExpr, typeRoot⟩ := typed
  dsimp only
  unfold finishAxiomCompilation
  with_reducible repeat' first
    | exact Emission.Yields.pure rfl
    | refine Emission.Yields.bindAny _ (fun _ => ?_)

/-- **A compiled unsafe axiom is declined**, with no premise but a
successful compile without Pass 3 records. -/
theorem axiom_declines (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (source : AxiomVal) (unsafeSource : source.isUnsafe = true) {before after : BlockState}
    {output : BlockResult} (state : State md)
    (ran : rawRun (compileConstantInfo (.axiomInfo source)) context before = (.ok output, after)) :
    readRecord cx state output.blockAddr output.block = .error (.declined "unsafe axiom") := by
  rw [EmissionDispatch.axiom_run context free] at ran
  unfold compileAxiomInfo at ran
  obtain ⟨_, middle, _, compiled⟩ := bind_ok ran
  unfold compileAxiomBlock at compiled
  obtain ⟨payload, payloadRan, built, _⟩ := EmissionBlocks.block_ok (fun payload => .axio payload.1)
    (fun payload => payload.2.1) (fun payload => by obtain ⟨_, _, _⟩ := payload; rfl) compiled
  have flag := axiom_unsafe source _ middle payload after payloadRan
  obtain ⟨erased, _, _, _⟩ := SharingRoots.build_roots (md := .anon) _ _ _ _ _ built
  obtain ⟨target, info, unsafeEq, _⟩ := erase_axio erased
  exact readAxiom_declines cx state output.blockAddr output.block target info
    (unsafeEq.trans (flag.trans unsafeSource))

/-- **A compiled quotient is read back as its source**: as `axiom_reads`,
with the quotient declaration of the source's kind. -/
theorem quotient_reads (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : BindingsCorrect context.1 bindings cx names) (source : QuotVal)
    {before after : BlockState} {output : BlockResult} (state : State md) {key : CName md}
    (keyed : cx.memberKey (.member output.blockAddr 0) = .ok key)
    (scope : ConstsSatisfy (SelfName (EmissionDispatch.singletonContext source.cnst.name context).2
      (fun _ => none) names) source.cnst.type)
    (clean : Emission.Clean bindings before) (wire : BlockWireTablesWF before)
    (ran : rawRun (compileConstantInfo (.quotInfo source)) context before = (.ok output, after)) :
    BlockResultCodecWF output ∧ (∃ blockMeta, output = BlockResult.mk' output.block blockMeta) ∧
      ∃ type, Related names (LevelMeaning source.cnst.levelParams.toList σ id) source.cnst.type type ∧
        readRecord (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block =
          .ok { decls := #[.quotDecl (quotKind (convertQuotKind source.kind))
            ⟨key, List.range source.cnst.levelParams.size, type⟩] } := by
  have codec := EmissionDispatch.constant_codec context free _ wire ran
  rw [EmissionDispatch.quotient_run context free] at ran
  have levels := quotientInfo_levels source _ before output after ran
  obtain ⟨_, _, wrapped, erased, roots⟩ := EmissionBlocks.quotientInfo_correct cx id (fun _ => none) names σ bindings
    (EmissionDispatch.singletonContext source.cnst.name context) free aligned external source scope clean ran
  obtain ⟨target, info, kindEq, lvls⟩ := erase_quot erased
  have count := levels target info
  rw [info] at roots
  cases roots with
  | cons head _ =>
    obtain ⟨type, typeRel, typeRead⟩ := head
    have keyed' : (ExpressionRead.withBlockBlobs cx after).memberKey (.member output.blockAddr 0) = .ok key :=
      keyed
    have read := readQuotient_ok (ExpressionRead.withBlockBlobs cx after) state output.blockAddr output.block target
      info keyed' typeRead
    have range : singletonLps target.lvls = List.range source.cnst.levelParams.size := by
      unfold singletonLps
      rw [count]
    rw [range, kindEq] at read
    exact ⟨codec, wrapped, type, typeRel, read⟩

end Reading

end Ix.CompileCert.HeaderReading
