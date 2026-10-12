import Ix.CompileCert.SharingRead

/-! Source-related anonymous readings and exact stored bytes for the actual
singleton definition-like compiler. Finalization preserves the payload state
on every outcome. Preseeding, publication, whole-declaration admission and
source-domain totality remain separate; no hash or FFI law is assumed here. -/

namespace Ix.CompileCert.DefinitionBlock

open Ix.CompileM Ix.CompileCert.HeadWriterFrame

theorem rawRun_timedC (phase : Ix.PhaseTimers.Phase) (action : CompileM α)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (timedC phase action) context state = rawRun action context state := by
  simp only [rawRun, timedC, ExceptT.run, ExceptT.mk, StateT.run,
    Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV, ite_self]

theorem finish_run (info : Ixon.ConstantInfo) (metadata : Ixon.ConstantMeta)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (finishConstantInfoWithSharing info metadata) context state =
      ((buildConstantWithSharing context.1.sharingLimits info state.refs state.univs).map
        (fun block => BlockResult.mk' block metadata), state) := by
  have readRun : rawRun (read : CompileM (CompileEnv × BlockEnv)) context state = (.ok context, state) := rfl
  simp only [finishConstantInfoWithSharing, finishConstantWithSharing, buildBlockConstant,
    rawRun_bind, rawRun_get, readRun]
  cases buildConstantWithSharing context.1.sharingLimits info state.refs state.univs <;> rfl

/-- The singleton wrapper stores the emitted anonymous block, its exact
serialization and computed address. This states no collision or FFI law. -/
def Wrapped (result : BlockResult) : Prop :=
  result.blockBytes = Ixon.serConstant result.block ∧
    result.blockAddr = Address.blake3 result.blockBytes ∧
    result.projections = #[] ∧ result.classNames = #[]

theorem wrapped_mk (block : Ixon.Constant) (metadata : Ixon.ConstantMeta) :
    Wrapped (BlockResult.mk' block metadata) := ⟨rfl, rfl, rfl, rfl⟩

theorem compileDefinitionDataBlock_eq_ok (environment : CompileEnv × BlockEnv) (source : Ix.Def)
    (before : BlockState) (out : BlockResult) (after : BlockState)
    (compiled : rawRun (compileDefinitionDataBlock source) environment before = (.ok out, after)) :
    ∃ payload : Ixon.Definition × Ixon.ConstantMeta × Ixon.Expr × Ixon.Expr,
      rawRun (compileDefinitionData source) environment before = (.ok payload, after) ∧
      buildConstantWithSharing environment.1.sharingLimits (.defn payload.1) after.refs after.univs = .ok out.block ∧
      Wrapped out := by
  simp only [compileDefinitionDataBlock, rawRun_bind] at compiled
  cases payloadRun : rawRun (compileDefinitionData source) environment before with
  | mk payloadOutcome middle =>
    rw [payloadRun] at compiled
    cases payloadOutcome with
    | error error => cases compiled
    | ok payload =>
      rcases payload with ⟨definition, metadata, type, value⟩
      dsimp only at compiled
      rw [rawRun_timedC, finish_run] at compiled
      cases built : buildConstantWithSharing environment.1.sharingLimits (.defn definition) middle.refs middle.univs with
      | error error => simp [built, Except.map] at compiled
      | ok block =>
        simp only [built, Except.map, Prod.mk.injEq, Except.ok.injEq] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        exact ⟨(definition, metadata, type, value), rfl, built, wrapped_mk block metadata⟩

/-- The finalizer changes no block state, on success or sharing failure. -/
theorem compileDefinitionDataBlock_state (environment : CompileEnv × BlockEnv) (source : Ix.Def) (before : BlockState) :
    (rawRun (compileDefinitionDataBlock source) environment before).2 =
      (rawRun (compileDefinitionData source) environment before).2 := by
  rw [compileDefinitionDataBlock, rawRun_bind]
  cases payloadRun : rawRun (compileDefinitionData source) environment before with
  | mk payloadOutcome middle =>
    cases payloadOutcome with
    | error error => rfl
    | ok payload =>
      dsimp only
      rw [rawRun_timedC, finish_run]

theorem compileDefinitionBlock_eq (source : Ix.DefinitionVal) :
    compileDefinitionBlock source = compileDefinitionDataBlock (definitionValData source) := rfl

def Related (context : Kernel.Reader.Ctx) (self : Nat → Option Kernel.Name)
    (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (state : BlockState) (source : Ix.Def) (result : BlockResult) : Prop :=
  Wrapped result ∧ ∃ target, result.block.info = .defn target ∧
    DefinitionEmission.PayloadRelated names source.levelParams.toList params
      (Kernel.Reader.MemberReader.mk' (SharingRead.blobContext context state)
        result.block (Kernel.Reader.paramOf params) self) source target

/-- The actual singleton definition-like compiler, including canonical sharing
and the production serialization/address wrapper, preserves source-related
type/value readings. Preseeding and publication are separate driver steps. -/
theorem compileDefinitionDataBlock_correct (context : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (bindings : ExpressionState.Bindings) (environment : CompileEnv × BlockEnv)
    (source : Ix.Def) (arity : params.length = source.levelParams.size)
    (aligned : ∀ address, context.blob address = environment.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect environment.1 bindings context names)
    (selfSound : ExpressionState.SelfCorrect environment.2 self names)
    (before : BlockState) (ready : DefinitionEmission.Ready bindings before)
    (out : BlockResult) (after : BlockState)
    (compiled : rawRun (compileDefinitionDataBlock source) environment before = (.ok out, after)) :
    DefinitionEmission.Clean bindings after ∧ Related context self names params after source out := by
  obtain ⟨payload, payloadRun, built, wrapped⟩ := compileDefinitionDataBlock_eq_ok environment source before out after compiled
  have related := SharingRead.compileDefinitionData_shared_correct context base self names params bindings environment source
    arity aligned external selfSound before ready payload after payloadRun out.block built
  exact ⟨related.1, wrapped, related.2⟩

/-- The actual returned bytes decode exactly to the returned anonymous block.
The successful sharing run supplies expression bounds; table bounds remain explicit. -/
theorem compileDefinitionDataBlock_codec (environment : CompileEnv × BlockEnv) (source : Ix.Def)
    (before : BlockState) (out : BlockResult) (after : BlockState)
    (compiled : rawRun (compileDefinitionDataBlock source) environment before = (.ok out, after))
    (tables : Ix.Sharing.Verify.BlockWireTablesWF after) :
    out.block.wireWF ∧ Ixon.deConstant out.blockBytes = .ok out.block := by
  obtain ⟨payload, _, built, wrapped⟩ := compileDefinitionDataBlock_eq_ok environment source before out after compiled
  refine ⟨SharingRead.buildDefinition_wireWF environment.1.sharingLimits payload.1 after tables out.block built, ?_⟩
  rw [wrapped.1]
  exact SharingRead.buildDefinition_codec environment.1.sharingLimits payload.1 after tables out.block built

end Ix.CompileCert.DefinitionBlock
