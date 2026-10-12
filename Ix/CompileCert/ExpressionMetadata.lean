import Ix.CompileCert.ExpressionSteps

/-! Metadata serialization preserves the certified reader and expression
cache, including errors. Semantic-contract lowering preserves the reader's
kernel expression; resource/VM interpretations are separate contracts. -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Ix.CompileCert.ExpressionCacheRun (Meaning Valid)

open private Ix.CompileM.compileKVMap.match_5
  Ix.CompileM.compileKVMap._sparseCasesOn_5 from Ix.CompileM

section Constructors

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant)
  (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
  (related : Ix.Expr → Kernel.Expr → Prop) (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx base param self
local notation "meaning" => ExpressionRead.Reading related reader

def Safe (action : CompileM α) (context : CompileEnv × BlockEnv) : Prop :=
  ∀ before, Good cx base param self related bindings before →
    Good cx base param self related bindings (rawRun action context before).2 ∧
      ExpressionRead.Extends (reader before).ecx (reader (rawRun action context before).2).ecx

theorem Safe.pure (value : α) (context : CompileEnv × BlockEnv) :
    Safe cx base param self related bindings (pure value) context :=
  fun _ good => ⟨good, extends_refl _⟩

theorem Safe.throw (error : CompileError) (context : CompileEnv × BlockEnv) :
    Safe cx base param self related bindings (throw error : CompileM α) context :=
  fun _ good => ⟨good, extends_refl _⟩

theorem Safe.get (context : CompileEnv × BlockEnv) :
    Safe cx base param self related bindings getBlockState context :=
  fun _ good => ⟨good, extends_refl _⟩

theorem Safe.read (context : CompileEnv × BlockEnv) :
    Safe cx base param self related bindings getCompileEnv context :=
  fun _ good => ⟨good, extends_refl _⟩

theorem Safe.bind {action : CompileM α} {next : α → CompileM β} (context : CompileEnv × BlockEnv)
    (first : Safe cx base param self related bindings action context)
    (tail : ∀ value, Safe cx base param self related bindings (next value) context) :
    Safe cx base param self related bindings (action >>= next) context := by
  intro before good
  have head := first before good
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact head
    | ok value =>
      have next := tail value middle head.1
      exact ⟨next.1, extends_trans head.2 next.2⟩

theorem Safe.mapM_list (items : List α) (action : α → CompileM β) (context : CompileEnv × BlockEnv)
    (each : ∀ item ∈ items, Safe cx base param self related bindings (action item) context) :
    Safe cx base param self related bindings (items.mapM action) context := by
  induction items with
  | nil => exact Safe.pure cx base param self related bindings _ context
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply Safe.bind cx base param self related bindings context (each item (by simp))
    intro _
    apply Safe.bind cx base param self related bindings context (ih (fun item member => each item (by simp [member])))
    intro _
    exact Safe.pure cx base param self related bindings _ context

theorem Safe.mapM_array (items : Array α) (action : α → CompileM β) (context : CompileEnv × BlockEnv)
    (each : ∀ item ∈ items, Safe cx base param self related bindings (action item) context) :
    Safe cx base param self related bindings (items.mapM action) context := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  apply Safe.bind cx base param self related bindings context
    (Safe.mapM_list cx base param self related bindings _ action context (fun item member => each item (by simpa using member)))
  intro _
  exact Safe.pure cx base param self related bindings _ context

theorem Safe.compileName (name : Ix.Name) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (compileName name) context :=
  fun before good => compileName_good cx base param self related bindings name context before good aligned

theorem Safe.storeBlob (bytes : ByteArray) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (storeBlob bytes) context := by
  intro before good
  have preserved := storeBlob_good cx base param self related bindings bytes context before good aligned
  exact ⟨preserved.1, preserved.2.1⟩

theorem Safe.storeString (value : String) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (storeString value) context :=
  Safe.storeBlob cx base param self related bindings _ context aligned

theorem Safe.serializeIxSubstring (value : Ix.Substring) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (serializeIxSubstring value) context :=
  Safe.bind cx base param self related bindings context (Safe.storeString cx base param self related bindings _ context aligned)
    (fun _ => Safe.pure cx base param self related bindings _ context)

theorem Safe.serializeIxSourceInfo (value : Ix.SourceInfo) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (serializeIxSourceInfo value) context := by
  cases value <;> unfold Ix.CompileM.serializeIxSourceInfo
  · exact Safe.bind cx base param self related bindings context
      (Safe.serializeIxSubstring cx base param self related bindings _ context aligned) fun _ =>
        Safe.bind cx base param self related bindings context
          (Safe.serializeIxSubstring cx base param self related bindings _ context aligned) fun _ =>
            Safe.pure cx base param self related bindings _ context
  all_goals exact Safe.pure cx base param self related bindings _ context

theorem Safe.serializeIxSyntaxPreresolved (value : Ix.SyntaxPreresolved) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (serializeIxSyntaxPreresolved value) context := by
  cases value <;> unfold Ix.CompileM.serializeIxSyntaxPreresolved
  all_goals
    apply Safe.bind cx base param self related bindings context
      (Safe.compileName cx base param self related bindings _ context aligned)
    intro _
  · exact Safe.pure cx base param self related bindings _ context
  · apply Safe.bind cx base param self related bindings context
      (Safe.mapM_array cx base param self related bindings _ _ context
        (fun _ _ => Safe.storeString cx base param self related bindings _ context aligned))
    intro _
    exact Safe.pure cx base param self related bindings _ context

theorem Safe.serializeIxSyntax (value : Ix.Syntax) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (serializeIxSyntax value) context := by
  induction value using Ix.CompileM.serializeIxSyntax.induct with
  | case1 => rw [Ix.CompileM.serializeIxSyntax]; exact Safe.pure cx base param self related bindings _ context
  | case2 info kind args ih =>
    rw [Ix.CompileM.serializeIxSyntax]
    apply Safe.bind cx base param self related bindings context (Safe.compileName cx base param self related bindings _ context aligned)
    intro _
    apply Safe.bind cx base param self related bindings context (Safe.serializeIxSourceInfo cx base param self related bindings _ context aligned)
    intro _
    apply Safe.bind cx base param self related bindings context
    · apply Safe.mapM_array cx base param self related bindings _ _ context
      intro arg _
      exact ih arg
    · intro _; exact Safe.pure cx base param self related bindings _ context
  | case3 info value =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Safe.bind cx base param self related bindings context
      (Safe.serializeIxSourceInfo cx base param self related bindings _ context aligned) fun _ =>
        Safe.bind cx base param self related bindings context
          (Safe.storeString cx base param self related bindings _ context aligned) fun _ =>
            Safe.pure cx base param self related bindings _ context
  | case4 info raw value resolved =>
    rw [Ix.CompileM.serializeIxSyntax]
    exact Safe.bind cx base param self related bindings context (Safe.compileName cx base param self related bindings _ context aligned) fun _ =>
      Safe.bind cx base param self related bindings context (Safe.serializeIxSourceInfo cx base param self related bindings _ context aligned) fun _ =>
        Safe.bind cx base param self related bindings context (Safe.serializeIxSubstring cx base param self related bindings _ context aligned) fun _ =>
          Safe.bind cx base param self related bindings context
            (Safe.mapM_array cx base param self related bindings _ _ context
              (fun _ _ => Safe.serializeIxSyntaxPreresolved cx base param self related bindings _ context aligned)) fun _ =>
                Safe.pure cx base param self related bindings _ context

theorem Safe.compileDataValue (value : Ix.DataValue) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (compileDataValue value) context := by
  cases value <;> unfold Ix.CompileM.compileDataValue
  all_goals with_reducible repeat' first
    | exact Safe.pure cx base param self related bindings _ context
    | exact Safe.compileName cx base param self related bindings _ context aligned
    | exact Safe.serializeIxSyntax cx base param self related bindings _ context aligned
    | exact Safe.storeBlob cx base param self related bindings _ context aligned
    | refine Safe.bind cx base param self related bindings context ?_ (fun _ => ?_)

theorem Safe.compileKVMap (values : Array (Ix.Name × Ix.DataValue)) (context : CompileEnv × BlockEnv)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address) :
    Safe cx base param self related bindings (compileKVMap values) context := by
  rcases values with ⟨_ | ⟨⟨name, value⟩, _ | ⟨next, rest⟩⟩⟩ <;> try cases value
  all_goals unfold Ix.CompileM.compileKVMap
  all_goals delta Ix.CompileM.compileKVMap.match_5
  all_goals simp only [Array.size, List.length_cons, List.length_nil,
    Nat.succ.injEq, Nat.add_one_ne_zero, Nat.reduceEqDiff, ↓reduceDIte]
  all_goals try delta Ix.CompileM.compileKVMap._sparseCasesOn_5
  all_goals try simp only [← Array.getElem_toList, List.getElem_cons_zero]
  all_goals with_reducible repeat' first
    | exact Safe.pure cx base param self related bindings _ context
    | exact Safe.throw cx base param self related bindings _ context
    | exact Safe.read cx base param self related bindings context
    | exact Safe.get cx base param self related bindings context
    | exact Safe.compileName cx base param self related bindings _ context aligned
    | exact Safe.compileDataValue cx base param self related bindings _ context aligned
    | refine Safe.bind cx base param self related bindings context ?_ (fun _ => ?_)
    | refine Safe.mapM_array cx base param self related bindings _ _ context (fun _ _ => ?_)
    | dsimp only
    | split

theorem contract_lower_read (contract : Ix.SemanticContract.Contract) (source : Ix.Expr) (value : Ixon.Expr)
    {lowered : Ixon.Expr} (success : contract.lower source value = .ok lowered) (state : BlockState) :
    (reader state).read lowered = (reader state).read value := by
  unfold Ix.SemanticContract.Contract.lower at success
  split at success
  all_goals first
    | cases Except.ok.inj success; rfl
    | cases success

def finishMetadata (kvmap : Ixon.KVMap) (value : Ixon.Expr × UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.mdata #[kvmap] value.2)
  pure (value.1, root)

theorem finishMetadata_checked (data : Array (Ix.Name × Ix.DataValue)) (source : Ix.Expr) (hash : Address)
    (kvmap : Ixon.KVMap) (value : Ixon.Expr × UInt64) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx base param self related bindings before) (child : meaning before source value)
    (wrap : ∀ target, related source target → related (.mdata data source hash) target) :
    Checked cx base param self related bindings (.mdata data source hash) before
      (rawRun (finishMetadata kvmap value) context before) := by
  let after := { before with arena := { nodes := before.arena.nodes.push (.mdata #[kvmap] value.2) } }
  change Checked cx base param self related bindings (.mdata data source hash) before
    (.ok (value.1, before.arena.nodes.size.toUInt64), after)
  have frame : ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := rfl
  refine ⟨good_metadata cx base param self related bindings frame good, extends_refl _, ?_⟩
  intro result success
  cases Except.ok.inj success
  obtain ⟨target, rel, read⟩ := child
  exact ⟨target, wrap target rel, read⟩

def metadataStep (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (data : Array (Ix.Name × Ix.DataValue)) (source : Ix.Expr) : CompileM (Ixon.Expr × UInt64) := do
  if Ix.SemanticContract.hasMetadata data then
    let contract ← match Ix.SemanticContract.read data with
      | .ok contract => pure contract
      | .error error => throw (.unsupportedExpr error)
    let (value, root) ← compile source
    match contract.lower source value with
    | .ok lowered => return (lowered, root)
    | .error error => throw (.unsupportedExpr error)
  else
    let kvmap ← compileKVMap data
    let value ← compile source
    finishMetadata kvmap value

theorem metadata_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (data : Array (Ix.Name × Ix.DataValue)) (source : Ix.Expr) (hash : Address) :
    compileExprTotalStep compile (.mdata data source hash) = metadataStep compile data source := rfl

theorem metadata_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (data : Array (Ix.Name × Ix.DataValue)) (source : Ix.Expr) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (good : Good cx base param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (childCorrect : ∀ state, Good cx base param self related bindings state →
      Checked cx base param self related bindings source state (rawRun (compile source) context state))
    (wrap : ∀ target, related source target → related (.mdata data source hash) target) :
    Checked cx base param self related bindings (.mdata data source hash) before
      (rawRun (compileExprTotalStep compile (.mdata data source hash)) context before) := by
  rw [metadata_step_eq]
  unfold metadataStep
  split
  · cases parsed : Ix.SemanticContract.read data with
    | error error => exact ⟨good, extends_refl _, by intro value bad; cases bad⟩
    | ok contract =>
      simp only [rawRun_bind, rawRun_pure]
      have child := childCorrect before good
      cases childRun : rawRun (compile source) context before with
      | mk outcome after =>
        rw [childRun] at child
        cases outcome with
        | error error => exact ⟨child.1, child.2.1, by intro value bad; cases bad⟩
        | ok value =>
          rcases value with ⟨value, root⟩
          dsimp only
          cases lowered : contract.lower source value with
          | error error => exact ⟨child.1, child.2.1, by intro value bad; cases bad⟩
          | ok result =>
            refine ⟨child.1, child.2.1, ?_⟩
            intro output success
            cases Except.ok.inj success
            obtain ⟨target, rel, read⟩ := child.2.2 (value, root) rfl
            refine ⟨target, wrap target rel, ?_⟩
            change (reader after).read result = .ok target
            rw [contract_lower_read cx base param self contract source value lowered after]
            exact read
  · rw [rawRun_bind]
    have safe := Safe.compileKVMap cx base param self related bindings data context aligned before good
    cases prepared : rawRun (compileKVMap data) context before with
    | mk outcome middle =>
      rw [prepared] at safe
      cases outcome with
      | error error => exact ⟨safe.1, safe.2, by intro value bad; cases bad⟩
      | ok kvmap =>
        dsimp only
        rw [rawRun_bind]
        have child := childCorrect middle safe.1
        cases childRun : rawRun (compile source) context middle with
        | mk outcome after =>
          rw [childRun] at child
          have growth := extends_trans safe.2 child.2.1
          cases outcome with
          | error error => exact ⟨child.1, growth, by intro value bad; cases bad⟩
          | ok value =>
            have finished := finishMetadata_checked cx base param self related bindings data source hash kvmap value context after
              child.1 (child.2.2 value rfl) wrap
            exact ⟨finished.1, extends_trans growth finished.2.1, finished.2.2⟩


end Constructors

end Ix.CompileCert.ExpressionState
