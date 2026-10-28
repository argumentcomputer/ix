import Ix.CompileCert.ExpressionState

/-! # The ordinary expression compiler's steps

One lemma per constructor of `Ix.CompileM.compileExprNoSurgeryStep`, with a
non-dependent callback `compile` (`step compile e`): every run keeps `Good`
and extends the in-flight reader, and a successful one returns a value that
reads as a term related to the source, given the same of each child's
compile (`Checked`). Errors keep the invariant and every earlier reading.

The App arm compiles the head and the arguments of the whole spine
(`Ix.CompileM.decomposeApps`) and folds the applications
(`app_step_eq`: a `foldlM` of `appStep`); a spine reads as the head's
reading applied to the arguments' (`spine_related`). -/

namespace Ix.CompileCert.ExpressionState

open Ix.CompileM Ix.CompileCert Ix.CompileCert.UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)

/-- One step of the ordinary expression compiler with a non-dependent
callback. -/
def step (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (e : Ix.Expr) :
    CompileM (Ixon.Expr × UInt64) :=
  compileExprNoSurgeryStep e (fun x _ => compile x)

/-! ## The steps as sequences of named finishers -/

theorem bvar_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (index : Nat) (hash : Address) :
    step compile (.bvar index hash) = (do
      let slot ← checkedTableIndex "bound variable" index
      let root ← allocArenaNode .leaf
      pure (.var slot, root)) := rfl

def finishSort (index : UInt64) (patch : Option UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode .leaf
  if let some original := patch then pushUnivPatch root #[original]
  pure (.sort index, root)

theorem sort_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (level : Ix.Level)
    (hash : Address) :
    step compile (.sort level hash) = (do
      let (index, patch) ← compileAndInternUnivCanon level
      finishSort index patch) := rfl

theorem const_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (name : Ix.Name)
    (levels : Array Ix.Level) (hash : Address) :
    step compile (.const name levels hash) = compileConstExprRaw name levels := rfl

def binderSource (isAll : Bool) (name : Ix.Name) (type body : Ix.Expr) (info : Lean.BinderInfo)
    (hash : Address) : Ix.Expr :=
  if isAll then .forallE name type body info hash else .lam name type body info hash

def finishBinder (isAll : Bool) (name : Ix.Name) (info : Lean.BinderInfo)
    (type body : Ixon.Expr × UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.binder name.getHash info type.2 body.2)
  pure ((if isAll then .leanAll type.1 body.1 else .leanLam type.1 body.1), root)

theorem binder_step_eq (isAll : Bool) (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type body : Ix.Expr) (info : Lean.BinderInfo) (hash : Address) :
    step compile (binderSource isAll name type body info hash) = (do
      compileName name
      let t ← compile type
      let b ← compile body
      finishBinder isAll name info t b) := by cases isAll <;> rfl

def finishLet (name : Ix.Name) (nonDep : Bool) (type value body : Ixon.Expr × UInt64) :
    CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.letBinder name.getHash type.2 value.2 body.2)
  pure (.leanLet nonDep type.1 value.1 body.1, root)

theorem let_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type value body : Ix.Expr) (nonDep : Bool) (hash : Address) :
    step compile (.letE name type value body nonDep hash) = (do
      compileName name
      let t ← compile type
      let v ← compile value
      let b ← compile body
      finishLet name nonDep t v b) := rfl

def finishLiteral (wire : UInt64 → Ixon.Expr) (index : UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode .leaf
  pure (wire index, root)

def compileLiteral (bytes : ByteArray) (wire : UInt64 → Ixon.Expr) : CompileM (Ixon.Expr × UInt64) := do
  let address ← storeBlob bytes
  let index ← internRef address
  finishLiteral wire index

theorem nat_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (value : Nat) (hash : Address) :
    step compile (.lit (.natVal value) hash) = compileLiteral (ByteArray.mk (Nat.toBytesLE value)) .nat :=
  rfl

theorem string_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (value : String)
    (hash : Address) :
    step compile (.lit (.strVal value) hash) = compileLiteral value.toUTF8 .str := rfl

def finishProjection (name : Ix.Name) (reference field : UInt64) (value : Ixon.Expr × UInt64) :
    CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.prj name.getHash value.2)
  pure (.prj reference field value.1, root)

theorem projection_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address) :
    step compile (.proj name field source hash) = (do
      let slot ← checkedTableIndex "projection field" field
      compileName name
      let address ← lookupConstAddr name
      let reference ← internRef address
      let value ← compile source
      finishProjection name reference slot value) := rfl

def finishMetadata (kvmap : Ixon.KVMap) (value : Ixon.Expr × UInt64) : CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.mdata #[kvmap] value.2)
  pure (value.1, root)

def readContract (data : Array (Ix.Name × Ix.DataValue)) : CompileM Ix.SemanticContract.Contract :=
  match Ix.SemanticContract.read data with
  | .ok contract => pure contract
  | .error error => throw (.unsupportedExpr error)

def lowerContract (contract : Ix.SemanticContract.Contract) (source : Ix.Expr)
    (value : Ixon.Expr × UInt64) : CompileM (Ixon.Expr × UInt64) :=
  match contract.lower source value.1 with
  | .ok lowered => pure (lowered, value.2)
  | .error error => throw (.unsupportedExpr error)

def metadataStep (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (data : Array (Ix.Name × Ix.DataValue)) (source : Ix.Expr) : CompileM (Ixon.Expr × UInt64) :=
  if Ix.SemanticContract.hasMetadata data then do
    let contract ← readContract data
    let value ← compile source
    lowerContract contract source value
  else do
    let kvmap ← compileKVMap data
    let value ← compile source
    finishMetadata kvmap value

/-! ## Effects composed -/

section Steps

variable {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
  (self : Nat → Option (ReadM (CName md))) (related : Ix.Expr → CExpr md → Prop)
  (bindings : Bindings)

local notation "reader" => ExpressionRead.blockReader cx param self
local notation "meaning" => ExpressionRead.Reading related reader

/-- An effect that keeps `Good` and extends the reader, then a `Checked`
continuation from the state it leaves. -/
theorem then_checked {action : CompileM α} {next : α → CompileM (Ixon.Expr × UInt64)}
    (source : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (head : Good cx param self related bindings (rawRun action context before).2 ∧
      ExpressionRead.Extends (reader before).ecx (reader (rawRun action context before).2).ecx)
    (tail : ∀ value state, rawRun action context before = (.ok value, state) →
      Good cx param self related bindings state →
      Checked cx param self related bindings source state (rawRun (next value) context state)) :
    Checked cx param self related bindings source before (rawRun (action >>= next) context before) := by
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact checked_error cx param self related bindings error head.1 head.2
    | ok value =>
      have later := tail value middle ran head.1
      exact ⟨later.1, extends_trans head.2 later.2.1, later.2.2⟩

/-- A child's compile, then a continuation that may use the child's reading
and the reader extension so far. -/
theorem child_then_checked {action : CompileM (Ixon.Expr × UInt64)}
    {next : Ixon.Expr × UInt64 → CompileM (Ixon.Expr × UInt64)}
    (source child : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (first : Checked cx param self related bindings child before (rawRun action context before))
    (tail : ∀ value state, Good cx param self related bindings state →
      ExpressionRead.Extends (reader before).ecx (reader state).ecx → meaning state child value →
      Checked cx param self related bindings source state (rawRun (next value) context state)) :
    Checked cx param self related bindings source before (rawRun (action >>= next) context before) := by
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at first
    cases outcome with
    | error error => exact checked_error cx param self related bindings error first.1 first.2.1
    | ok value =>
      have later := tail value middle first.1 first.2.1 (first.2.2 value rfl)
      exact ⟨later.1, extends_trans first.2.1 later.2.1, later.2.2⟩

/-- A checked index conversion, then a continuation given its bound. -/
theorem index_then_checked {next : UInt64 → CompileM (Ixon.Expr × UInt64)}
    (source : Ix.Expr) (table : String) (index : Nat) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx param self related bindings before)
    (tail : index < UInt64.size →
      Checked cx param self related bindings source before (rawRun (next index.toUInt64) context before)) :
    Checked cx param self related bindings source before
      (rawRun (checkedTableIndex table index >>= next) context before) := by
  unfold checkedTableIndex
  split
  · rename_i bounded
    rw [rawRun_bind, rawRun_pure]
    exact tail bounded
  · rw [rawRun_bind, rawRun_throw]
    exact checked_error cx param self related bindings _ good (ExpressionRead.Extends.refl _)

/-- A metadata node's final allocation. -/
theorem allocFinish_checked (source : Ix.Expr) (node : Ixon.ExprMetaData) (value : Ixon.Expr)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (prior : ∃ target, related source target ∧ (reader before).read value = .ok target) :
    Checked cx param self related bindings source before
      (rawRun (allocArenaNode node >>= fun root => pure (value, root)) context before) :=
  checked_metadata cx param self related bindings
    (before := before) (after := { before with arena := { nodes := before.arena.nodes.push node } }) rfl good
    (value := (value, before.arena.nodes.size.toUInt64)) prior

/-! ## Leaves -/

theorem bvar_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (index : Nat)
    (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (rel : related (.bvar index hash) (Ix.Kernel.Expr.mkBvar index)) :
    Checked cx param self related bindings (.bvar index hash) before
      (rawRun (step compile (.bvar index hash)) context before) := by
  rw [bvar_step_eq]
  apply index_then_checked cx param self related bindings _ _ _ context before good
  intro bounded
  refine allocFinish_checked cx param self related bindings _ .leaf (.var index.toUInt64) context before good ?_
  refine ⟨Ix.Kernel.Expr.mkBvar index, rel, ?_⟩
  change (Except.ok (Ix.Kernel.Expr.mkBvar index.toUInt64.toNat) : ReadM (CExpr md)) = _
  rw [UInt64.toNat_ofNat_of_lt' bounded]

theorem finishSort_run (index : UInt64) (patch : Option UInt64) (context : CompileEnv × BlockEnv)
    (before : BlockState) :
    ∃ root after, rawRun (finishSort index patch) context before = (.ok (.sort index, root), after) ∧
      withoutExprMetadata after = withoutExprMetadata before := by
  unfold finishSort allocArenaNode
  simp only [rawRun_bind, rawRun_modifyGet]
  cases patch with
  | none => exact ⟨_, _, rfl, rfl⟩
  | some original =>
    simp only [pushUnivPatch, rawRun_bind, rawRun_modify, rawRun_pure]
    exact ⟨_, _, rfl, rfl⟩

theorem sort_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (source : Ix.Level)
    (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before) (σ : Ix.Name → LevelParam)
    (sortRelated : ∀ level, LevelMeaning context.2.univCtx σ param source level →
      related (.sort source hash) (.sort level)) :
    Checked cx param self related bindings (.sort source hash) before
      (rawRun (step compile (.sort source hash)) context before) := by
  rw [sort_step_eq, rawRun_bind]
  have head := compileLevel_good cx param self related bindings source context before good σ
  cases ran : rawRun (compileAndInternUnivCanon source) context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact checked_error cx param self related bindings error head.1 head.2.1
    | ok value =>
      obtain ⟨level, readLevel, levelMeaning⟩ := head.2.2 value rfl
      obtain ⟨index, patch⟩ := value
      obtain ⟨root, after, finished, frame⟩ := finishSort_run index patch context middle
      dsimp only
      rw [finished]
      have later := checked_metadata cx param self related bindings (source := .sort source hash)
        frame head.1 (value := (.sort index, root)) ⟨.sort level, sortRelated level levelMeaning, by
          change (do pure (Ix.Kernel.Expr.sort (← (reader middle).ecx.level index))) = _
          rw [readLevel]
          rfl⟩
      exact ⟨later.1, extends_trans head.2.1 later.2.1, later.2.2⟩

theorem finishLiteral_checked (source : Ix.Expr) (wire : UInt64 → Ixon.Expr) (index : UInt64)
    (target : CExpr md) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before) (rel : related source target)
    (read : (reader before).read (wire index) = .ok target) :
    Checked cx param self related bindings source before (rawRun (finishLiteral wire index) context before) :=
  allocFinish_checked cx param self related bindings source .leaf (wire index) context before good ⟨target, rel, read⟩

theorem literal_checked (source : Ix.Expr) (bytes : ByteArray) (wire : UInt64 → Ixon.Expr)
    (target : CExpr md) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (rel : related source target)
    (decode : ∀ state index, (reader state).ecx.blobAt index = .ok bytes →
      (reader state).read (wire index) = .ok target) :
    Checked cx param self related bindings source before (rawRun (compileLiteral bytes wire) context before) := by
  unfold compileLiteral
  have blob := storeBlob_good cx param self related bindings bytes context before good aligned
  apply then_checked cx param self related bindings source context before ⟨blob.1, blob.2.1⟩
  intro address stored ranBlob storedGood
  rw [ranBlob] at blob
  have bytesFound := blob.2.2 address rfl
  have reference := internRef_good cx param self related bindings address context stored storedGood
  have frame := internRef_frame address context stored
  apply then_checked cx param self related bindings source context stored ⟨reference.1, reference.2.1⟩
  intro index referenced ranRef referencedGood
  rw [ranRef] at reference frame
  have sameBlobs : referenced.blockBlobs = stored.blockBlobs := by
    have same := congrArg BlockState.blockBlobs frame; exact same
  have reads := blockReader_blob cx param self referenced (reference.2.2 index rfl)
    (by rw [sameBlobs]; exact bytesFound)
  exact finishLiteral_checked cx param self related bindings source wire index target context referenced
    referencedGood rel (decode referenced index reads)

theorem nat_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (value : Nat)
    (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (rel : related (.lit (.natVal value) hash) (.lit (.natVal value))) :
    Checked cx param self related bindings (.lit (.natVal value) hash) before
      (rawRun (step compile (.lit (.natVal value) hash)) context before) := by
  rw [nat_step_eq]
  apply literal_checked cx param self related bindings _ _ _ _ context before good aligned rel
  intro state index read
  change (do pure (Ix.Kernel.Expr.lit (.natVal (Kernel.Reader.natural (← (reader state).ecx.blobAt index))))) = _
  rw [read]
  simp only [bind, Except.bind, pure, Except.pure, natural_toBytes]

theorem string_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (value : String)
    (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (rel : related (.lit (.strVal value) hash) (.lit (.strVal value))) :
    Checked cx param self related bindings (.lit (.strVal value) hash) before
      (rawRun (step compile (.lit (.strVal value) hash)) context before) := by
  rw [string_step_eq]
  apply literal_checked cx param self related bindings _ _ _ _ context before good aligned rel
  intro state index read
  change (do
    let bytes ← (reader state).ecx.blobAt index
    let some text := String.fromUTF8? bytes | Kernel.Reader.malformed "string literal is not valid UTF-8"
    pure (Ix.Kernel.Expr.lit (.strVal text))) = _
  rw [read]
  simp only [bind, Except.bind, pure, Except.pure, string_toBytes]

/-! ## Constants -/

def finishReference (name : Ix.Name) (levels : Array (UInt64 × Option UInt64)) (value : Ixon.Expr) :
    CompileM (Ixon.Expr × UInt64) := do
  let root ← allocArenaNode (.ref name.getHash)
  if levels.any (·.2.isSome) then
    pushUnivPatch root (levels.map fun (canonical, original) => original.getD canonical)
  pure (value, root)

theorem finishReference_run (name : Ix.Name) (levels : Array (UInt64 × Option UInt64))
    (value : Ixon.Expr) (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ root after, rawRun (finishReference name levels value) context before = (.ok (value, root), after) ∧
      withoutExprMetadata after = withoutExprMetadata before := by
  unfold finishReference allocArenaNode
  simp only [rawRun_bind, rawRun_modifyGet]
  split
  · exact ⟨_, _, rfl, rfl⟩
  · exact ⟨_, _, rfl, rfl⟩

theorem finishReference_checked (source : Ix.Expr) (name : Ix.Name)
    (levels : Array (UInt64 × Option UInt64)) (value : Ixon.Expr) (target : CExpr md)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before) (rel : related source target)
    (read : (reader before).read value = .ok target) :
    Checked cx param self related bindings source before
      (rawRun (finishReference name levels value) context before) := by
  obtain ⟨root, after, ran, frame⟩ := finishReference_run name levels value context before
  rw [ran]
  exact checked_metadata cx param self related bindings frame good ⟨target, rel, read⟩

def constBody (name : Ix.Name) (compiled : Array (UInt64 × Option UInt64)) (mutCtx : Ix.MutCtx) :
    CompileM (Ixon.Expr × UInt64) := do
  match mutCtx.get? name with
  | some slot =>
    let index ← checkedTableIndex "mutual reference" slot
    finishReference name compiled (.recur index (compiled.map Prod.fst))
  | none =>
    let address ← lookupConstAddr name
    let index ← internRef address
    finishReference name compiled (.ref index (compiled.map Prod.fst))

theorem compileConstExprRaw_eq (name : Ix.Name) (levels : Array Ix.Level) :
    compileConstExprRaw name levels = (do
      let mutCtx := (← getBlockEnv).mutCtx
      let compiled ← levels.mapM compileAndInternUnivCanon
      compileName name
      constBody name compiled mutCtx) := by
  unfold compileConstExprRaw
  apply congrArg (fun next : BlockEnv → CompileM (Ixon.Expr × UInt64) => getBlockEnv >>= next)
  funext block
  apply congrArg (fun next : Array (UInt64 × Option UInt64) → CompileM (Ixon.Expr × UInt64) =>
    levels.mapM compileAndInternUnivCanon >>= next)
  funext compiled
  apply congrArg (fun next : Unit → CompileM (Ixon.Expr × UInt64) => compileName name >>= next)
  funext _done
  unfold constBody
  cases block.mutCtx.get? name <;> dsimp only
  all_goals
    by_cases patches : compiled.any (·.2.isSome) = true
    · simp only [finishReference, patches, ↓reduceIte]
    · simp only [finishReference, patches, Bool.false_eq_true, ↓reduceIte, pure_bind]

theorem constBody_checked (name : Ix.Name) (sources : Array Ix.Level) (hash : Address)
    (compiled : Array (UInt64 × Option UInt64)) (levels : List Kernel.Level)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (names : Ix.Name → CName md → Prop) (external : BindingsCorrect context.1 bindings cx names)
    (selfSound : ∀ index, context.2.mutCtx.get? name = some index →
      ∃ key, self index = some (.ok key) ∧ names name key)
    (readLevels : (reader before).ecx.levels (compiled.map Prod.fst) = .ok levels)
    (constantRelated : ∀ key, names name key → related (.const name sources hash) (.const key levels)) :
    Checked cx param self related bindings (.const name sources hash) before
      (rawRun (constBody name compiled context.2.mutCtx) context before) := by
  unfold constBody
  cases found : context.2.mutCtx.get? name with
  | some slot =>
    dsimp only
    apply index_then_checked cx param self related bindings _ _ _ context before good
    intro bounded
    obtain ⟨key, selfFound, nameRel⟩ := selfSound slot found
    apply finishReference_checked cx param self related bindings _ name compiled _ (.const key levels)
      context before good (constantRelated key nameRel)
    change (do
      let some member := self (slot.toUInt64).toNat | Kernel.Reader.malformed "recursive reference is outside its block"
      pure (Ix.Kernel.Expr.const (← member) (← (reader before).ecx.levels (compiled.map Prod.fst)))) = _
    rw [UInt64.toNat_ofNat_of_lt' bounded, selfFound]
    dsimp only
    rw [readLevels]
    rfl
  | none =>
    dsimp only
    rw [rawRun_bind]
    have unchanged := lookupConstAddr_state name context before
    cases looked : rawRun (lookupConstAddr name) context before with
    | mk outcome after =>
      rw [looked] at unchanged
      dsimp only at unchanged
      subst after
      cases outcome with
      | error error =>
        exact checked_error cx param self related bindings error good (ExpressionRead.Extends.refl _)
      | ok address =>
        obtain ⟨key, keyRead, nameRel⟩ := lookupConstAddr_correct name context before bindings good.1.2.2
          cx names external (congrArg Prod.fst looked)
        dsimp only
        have interned := internRef_good cx param self related bindings address context before good
        apply then_checked cx param self related bindings _ context before ⟨interned.1, interned.2.1⟩
        intro index referenced ranRef referencedGood
        rw [ranRef] at interned
        have reads := blockReader_key cx param self referenced (interned.2.2 index rfl) keyRead
        have retainedLevels := interned.2.1.levels (compiled.map Prod.fst) levels readLevels
        exact finishReference_checked cx param self related bindings _ name compiled
          (.ref index (compiled.map Prod.fst)) (.const key levels) context referenced referencedGood
          (constantRelated key nameRel) (by
            change (do
              let k ← (reader referenced).ecx.keyAt index
              pure (Ix.Kernel.Expr.const k (← (reader referenced).ecx.levels (compiled.map Prod.fst)))) = _
            rw [reads, retainedLevels]
            rfl)

theorem const_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (sources : Array Ix.Level) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx param self related bindings before)
    (σ : Ix.Name → LevelParam)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (names : Ix.Name → CName md → Prop) (external : BindingsCorrect context.1 bindings cx names)
    (selfSound : ∀ index, context.2.mutCtx.get? name = some index →
      ∃ key, self index = some (.ok key) ∧ names name key)
    (constantRelated : ∀ key levels, names name key →
      List.Forall₂ (LevelMeaning context.2.univCtx σ param) sources.toList levels →
      related (.const name sources hash) (.const key levels)) :
    Checked cx param self related bindings (.const name sources hash) before
      (rawRun (step compile (.const name sources hash)) context before) := by
  rw [const_step_eq, compileConstExprRaw_eq]
  simp only [rawRun_bind, rawRun_readBlock]
  have levelResult := compileLevels_good cx param self related bindings sources context before good σ
  cases compiledRun : rawRun (sources.mapM compileAndInternUnivCanon) context before with
  | mk outcome leveled =>
    rw [compiledRun] at levelResult
    cases outcome with
    | error error => exact checked_error cx param self related bindings error levelResult.1 levelResult.2.1
    | ok compiled =>
      dsimp only
      obtain ⟨levels, relatedLevels, readLevels⟩ := levelResult.2.2 compiled rfl
      have named := compileName_good cx param self related bindings name context leveled levelResult.1 aligned
      cases namedRun : rawRun (compileName name) context leveled with
      | mk outcome afterName =>
        rw [namedRun] at named
        cases outcome with
        | error error =>
          exact checked_error cx param self related bindings error named.1 (extends_trans levelResult.2.1 named.2)
        | ok _done =>
          have retainedLevels := named.2.levels (compiled.map Prod.fst) levels readLevels
          have body := constBody_checked cx param self related bindings name sources hash compiled levels
            context afterName named.1 names external selfSound retainedLevels
            (fun key nameRel => constantRelated key levels nameRel relatedLevels)
          exact ⟨body.1, extends_trans (extends_trans levelResult.2.1 named.2) body.2.1, body.2.2⟩

/-! ## Binders -/

def binderTarget (isAll : Bool) (type body : CExpr md) : CExpr md :=
  if isAll then .forallE type body { pw := .never } else .lam type body { pw := .never }

theorem finishBinder_checked (isAll : Bool) (name : Ix.Name) (type body : Ix.Expr)
    (info : Lean.BinderInfo) (hash : Address) (targetType targetBody : Ixon.Expr × UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (typeRead : meaning before type targetType) (bodyRead : meaning before body targetBody)
    (congruent : ∀ t b, related type t → related body b →
      related (binderSource isAll name type body info hash) (binderTarget isAll t b)) :
    Checked cx param self related bindings (binderSource isAll name type body info hash) before
      (rawRun (finishBinder isAll name info targetType targetBody) context before) := by
  obtain ⟨t, rt, readType⟩ := typeRead
  obtain ⟨b, rb, readBody⟩ := bodyRead
  refine allocFinish_checked cx param self related bindings _ (.binder name.getHash info targetType.2 targetBody.2)
    (if isAll then .leanAll targetType.1 targetBody.1 else .leanLam targetType.1 targetBody.1) context before
    good ⟨binderTarget isAll t b, congruent t b rt rb, ?_⟩
  cases isAll with
  | false =>
    change (do pure (Ix.Kernel.Expr.lam (← (reader before).read targetType.1)
      (← (reader before).read targetBody.1) (Ix.Kernel.BinderMeta.ofContracts .many .shared))) = _
    rw [readType, readBody, Ix.Kernel.BinderMeta.ofContracts_eq]
    rfl
  | true =>
    change (do pure (Ix.Kernel.Expr.forallE (← (reader before).read targetType.1)
      (← (reader before).read targetBody.1) (Ix.Kernel.BinderMeta.ofContracts .many .shared))) = _
    rw [readType, readBody, Ix.Kernel.BinderMeta.ofContracts_eq]
    rfl

theorem binder_step_checked (isAll : Bool) (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type body : Ix.Expr) (info : Lean.BinderInfo) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (typeCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings type state (rawRun (compile type) context state))
    (bodyCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings body state (rawRun (compile body) context state))
    (congruent : ∀ t b, related type t → related body b →
      related (binderSource isAll name type body info hash) (binderTarget isAll t b)) :
    Checked cx param self related bindings (binderSource isAll name type body info hash) before
      (rawRun (step compile (binderSource isAll name type body info hash)) context before) := by
  rw [binder_step_eq]
  have named := compileName_good cx param self related bindings name context before good aligned
  apply then_checked cx param self related bindings _ context before named
  intro _ named namedRun namedGood
  apply child_then_checked cx param self related bindings _ type context named (typeCorrect named namedGood)
  intro typeValue typed typedGood _ typeRead
  apply child_then_checked cx param self related bindings _ body context typed (bodyCorrect typed typedGood)
  intro bodyValue bodied bodiedGood growth bodyRead
  exact finishBinder_checked cx param self related bindings isAll name type body info hash
    typeValue bodyValue context bodied bodiedGood (meaning_grows cx param self related growth typeRead)
    bodyRead congruent

theorem finishLet_checked (name : Ix.Name) (type value body : Ix.Expr) (nonDep : Bool) (hash : Address)
    (targetType targetValue targetBody : Ixon.Expr × UInt64) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx param self related bindings before)
    (typeRead : meaning before type targetType) (valueRead : meaning before value targetValue)
    (bodyRead : meaning before body targetBody)
    (congruent : ∀ t v b, related type t → related value v → related body b →
      related (.letE name type value body nonDep hash) (.letE t v b { contract := .lean nonDep })) :
    Checked cx param self related bindings (.letE name type value body nonDep hash) before
      (rawRun (finishLet name nonDep targetType targetValue targetBody) context before) := by
  obtain ⟨t, rt, readType⟩ := typeRead
  obtain ⟨v, rv, readValue⟩ := valueRead
  obtain ⟨b, rb, readBody⟩ := bodyRead
  refine allocFinish_checked cx param self related bindings _
    (.letBinder name.getHash targetType.2 targetValue.2 targetBody.2)
    (.leanLet nonDep targetType.1 targetValue.1 targetBody.1) context before good
    ⟨.letE t v b { contract := .lean nonDep }, congruent t v b rt rv rb, ?_⟩
  change (do pure (Ix.Kernel.Expr.letE (← (reader before).read targetType.1)
    (← (reader before).read targetValue.1) (← (reader before).read targetBody.1)
    { contract := .lean nonDep })) = _
  rw [readType, readValue, readBody]
  rfl

theorem let_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (type value body : Ix.Expr) (nonDep : Bool) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (typeCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings type state (rawRun (compile type) context state))
    (valueCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings value state (rawRun (compile value) context state))
    (bodyCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings body state (rawRun (compile body) context state))
    (congruent : ∀ t v b, related type t → related value v → related body b →
      related (.letE name type value body nonDep hash) (.letE t v b { contract := .lean nonDep })) :
    Checked cx param self related bindings (.letE name type value body nonDep hash) before
      (rawRun (step compile (.letE name type value body nonDep hash)) context before) := by
  rw [let_step_eq]
  have named := compileName_good cx param self related bindings name context before good aligned
  apply then_checked cx param self related bindings _ context before named
  intro _ named namedRun namedGood
  apply child_then_checked cx param self related bindings _ type context named (typeCorrect named namedGood)
  intro typeValue typed typedGood _ typeRead
  apply child_then_checked cx param self related bindings _ value context typed (valueCorrect typed typedGood)
  intro valueValue valued valuedGood valueGrowth valueRead
  apply child_then_checked cx param self related bindings _ body context valued (bodyCorrect valued valuedGood)
  intro bodyValue bodied bodiedGood bodyGrowth bodyRead
  exact finishLet_checked cx param self related bindings name type value body nonDep hash
    typeValue valueValue bodyValue context bodied bodiedGood
    (meaning_grows cx param self related (extends_trans valueGrowth bodyGrowth) typeRead)
    (meaning_grows cx param self related bodyGrowth valueRead) bodyRead congruent

/-! ## Projections -/

theorem finishProjection_checked (source : Ix.Expr) (name : Ix.Name) (reference field : UInt64)
    (value : Ixon.Expr × UInt64) (target : CExpr md) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx param self related bindings before) (rel : related source target)
    (read : (reader before).read (.prj reference field value.1) = .ok target) :
    Checked cx param self related bindings source before
      (rawRun (finishProjection name reference field value) context before) :=
  allocFinish_checked cx param self related bindings source (.prj name.getHash value.2)
    (.prj reference field value.1) context before good ⟨target, rel, read⟩

theorem projection_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (names : Ix.Name → CName md → Prop) (external : BindingsCorrect context.1 bindings cx names)
    (childCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings source state (rawRun (compile source) context state))
    (projectionRelated : ∀ key target, names name key → related source target →
      related (.proj name field source hash) (.proj key field target)) :
    Checked cx param self related bindings (.proj name field source hash) before
      (rawRun (step compile (.proj name field source hash)) context before) := by
  rw [projection_step_eq]
  apply index_then_checked cx param self related bindings _ _ _ context before good
  intro bounded
  have named := compileName_good cx param self related bindings name context before good aligned
  apply then_checked cx param self related bindings _ context before named
  intro _ named namedRun namedGood
  rw [rawRun_bind]
  have unchanged := lookupConstAddr_state name context named
  cases looked : rawRun (lookupConstAddr name) context named with
  | mk outcome foundState =>
    rw [looked] at unchanged
    dsimp only at unchanged
    subst foundState
    cases outcome with
    | error error =>
      exact checked_error cx param self related bindings error namedGood (ExpressionRead.Extends.refl _)
    | ok address =>
      obtain ⟨key, keyRead, nameRel⟩ := lookupConstAddr_correct name context named bindings namedGood.1.2.2
        cx names external (congrArg Prod.fst looked)
      dsimp only
      have interned := internRef_good cx param self related bindings address context named namedGood
      apply then_checked cx param self related bindings _ context named ⟨interned.1, interned.2.1⟩
      intro reference referenced ranRef referencedGood
      rw [ranRef] at interned
      have readKey := blockReader_key cx param self referenced (interned.2.2 reference rfl) keyRead
      apply child_then_checked cx param self related bindings _ source context referenced
        (childCorrect referenced referencedGood)
      intro value afterChild childGood growth childRead
      obtain ⟨target, targetRel, readTarget⟩ := childRead
      have retainedKey := growth.key reference key readKey
      exact finishProjection_checked cx param self related bindings _ name reference field.toUInt64 value
        (.proj key field target) context afterChild childGood (projectionRelated _ _ nameRel targetRel) (by
          change (do
            let k ← (reader afterChild).ecx.keyAt reference
            pure (Ix.Kernel.Expr.proj k field.toUInt64.toNat (← (reader afterChild).read value.1))) = _
          rw [retainedKey, UInt64.toNat_ofNat_of_lt' bounded, readTarget]
          rfl)

/-- An unrepresentable bound-variable index is refused before any state
change; it never wraps. -/
theorem bvar_step_refuses (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (index : Nat)
    (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState) (large : UInt64.size ≤ index) :
    ∃ reason, rawRun (step compile (.bvar index hash)) context before =
      (.error (.resourceLimit reason), before) := by
  rw [bvar_step_eq]
  simp only [checkedTableIndex, Nat.not_lt.mpr large, ↓reduceIte, rawRun_bind, rawRun_throw]
  exact ⟨_, rfl⟩

/-- An unrepresentable projection field is refused before any state
change; it never wraps. -/
theorem projection_step_refuses (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) (large : UInt64.size ≤ field) :
    ∃ reason, rawRun (step compile (.proj name field source hash)) context before =
      (.error (.resourceLimit reason), before) := by
  rw [projection_step_eq]
  simp only [checkedTableIndex, Nat.not_lt.mpr large, ↓reduceIte, rawRun_bind, rawRun_throw]
  exact ⟨_, rfl⟩

/-! ## Metadata and contract frames -/


theorem read_lam {state : BlockState} {contract : Ixon.BinderContract} {type body : Ixon.Expr}
    {target : CExpr md} (read : (reader state).read (.lam contract type body) = .ok target) :
    ∃ t b, (reader state).read type = .ok t ∧ (reader state).read body = .ok b ∧
      target = .lam t b (Ix.Kernel.BinderMeta.ofContracts contract .shared) := by
  change ((reader state).read type >>= fun t => (reader state).read body >>= fun b =>
    pure (Ix.Kernel.Expr.lam t b (Ix.Kernel.BinderMeta.ofContracts contract .shared))) = _ at read
  cases ht : (reader state).read type with
  | error e => rw [ht] at read; cases read
  | ok t =>
    cases hb : (reader state).read body with
    | error e => rw [ht, hb] at read; cases read
    | ok b => rw [ht, hb] at read; cases read; exact ⟨t, b, rfl, rfl, rfl⟩

theorem read_all {state : BlockState} {contract : Ixon.BinderContract} {result : Ixon.ValueContract}
    {type body : Ixon.Expr} {target : CExpr md}
    (read : (reader state).read (.all contract result type body) = .ok target) :
    ∃ t b, (reader state).read type = .ok t ∧ (reader state).read body = .ok b ∧
      target = .forallE t b (Ix.Kernel.BinderMeta.ofContracts contract result) := by
  change ((reader state).read type >>= fun t => (reader state).read body >>= fun b =>
    pure (Ix.Kernel.Expr.forallE t b (Ix.Kernel.BinderMeta.ofContracts contract result))) = _ at read
  cases ht : (reader state).read type with
  | error e => rw [ht] at read; cases read
  | ok t =>
    cases hb : (reader state).read body with
    | error e => rw [ht, hb] at read; cases read
    | ok b => rw [ht, hb] at read; cases read; exact ⟨t, b, rfl, rfl, rfl⟩

theorem read_letE {state : BlockState} {contract : Ixon.LetContract} {type value body : Ixon.Expr}
    {target : CExpr md} (read : (reader state).read (.letE contract type value body) = .ok target) :
    ∃ t v b, (reader state).read type = .ok t ∧ (reader state).read value = .ok v ∧
      (reader state).read body = .ok b ∧ target = .letE t v b { contract := contract } := by
  change ((reader state).read type >>= fun t => (reader state).read value >>= fun v =>
    (reader state).read body >>= fun b => pure (Ix.Kernel.Expr.letE t v b { contract := contract })) = _ at read
  cases ht : (reader state).read type with
  | error e => rw [ht] at read; cases read
  | ok t =>
    cases hv : (reader state).read value with
    | error e => rw [ht, hv] at read; cases read
    | ok v =>
      cases hb : (reader state).read body with
      | error e => rw [ht, hv, hb] at read; cases read
      | ok b => rw [ht, hv, hb] at read; cases read; exact ⟨t, v, b, rfl, rfl, rfl, rfl⟩

/-- Reading a lowered binder is reading the compiled binder with the frame's
contract on it: the checker side of `Ix.SemanticContract.Contract.lower`
is `withContract`, the ingress's. -/
theorem lowerContract_read (contract : Ix.SemanticContract.Contract) (source : Ix.Expr)
    {value lowered : Ixon.Expr} (success : contract.lower source value = .ok lowered)
    (state : BlockState) {target : CExpr md} (read : (reader state).read value = .ok target) :
    ∃ result, withContract contract source target = some result ∧
      (reader state).read lowered = .ok result := by
  obtain ⟨kind, binder, valueContract, letKind⟩ := contract
  cases kind <;> cases source <;> cases value <;>
    simp only [Ix.SemanticContract.Contract.lower, pure, Except.pure] at success <;>
    (try cases success)
  · obtain ⟨t, b, readType, readBody, rfl⟩ := read_lam cx param self read
    refine ⟨_, rfl, ?_⟩
    change ((reader state).read _ >>= fun t => (reader state).read _ >>= fun b =>
      pure (Ix.Kernel.Expr.lam t b (Ix.Kernel.BinderMeta.ofContracts binder .shared))) = _
    rw [readType, readBody, Ix.Kernel.BinderMeta.ofContracts_eq, Ix.Kernel.BinderMeta.ofContracts_eq]
    rfl
  · obtain ⟨t, b, readType, readBody, rfl⟩ := read_all cx param self read
    refine ⟨_, rfl, ?_⟩
    change ((reader state).read _ >>= fun t => (reader state).read _ >>= fun b =>
      pure (Ix.Kernel.Expr.forallE t b (Ix.Kernel.BinderMeta.ofContracts binder valueContract))) = _
    rw [readType, readBody, Ix.Kernel.BinderMeta.ofContracts_eq, Ix.Kernel.BinderMeta.ofContracts_eq]
    rfl
  · obtain ⟨t, v, b, readType, readValue, readBody, rfl⟩ := read_letE cx param self read
    refine ⟨_, rfl, ?_⟩
    change ((reader state).read _ >>= fun t => (reader state).read _ >>= fun v =>
      (reader state).read _ >>= fun b => pure (Ix.Kernel.Expr.letE t v b { contract := _ })) = _
    rw [readType, readValue, readBody]
    rfl

theorem metadata_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (data : Array (Ix.Name × Ix.DataValue)) (source : Ix.Expr) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (childCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings source state (rawRun (compile source) context state))
    (plainWrap : Ix.SemanticContract.hasMetadata data = false →
      ∀ target, related source target → related (.mdata data source hash) target)
    (frameWrap : Ix.SemanticContract.hasMetadata data = true → ∀ c, Ix.SemanticContract.read data = .ok c →
      ∀ target result, related source target → withContract c source target = some result →
        related (.mdata data source hash) result) :
    Checked cx param self related bindings (.mdata data source hash) before
      (rawRun (step compile (.mdata data source hash)) context before) := by
  unfold step compileExprNoSurgeryStep
  dsimp only
  split
  · rename_i frame
    cases parsed : Ix.SemanticContract.read data with
    | error error =>
      dsimp only
      simp only [rawRun_bind, rawRun_throw]
      exact checked_error cx param self related bindings _ good (ExpressionRead.Extends.refl _)
    | ok contract =>
      dsimp only
      rw [rawRun_bind, rawRun_pure]
      dsimp only
      apply child_then_checked cx param self related bindings _ source context before
        (childCorrect before good)
      intro value state stateGood growth childRead
      cases lowered : contract.lower source value.1 with
      | error error =>
        dsimp only
        simp only [rawRun_bind, rawRun_throw]
        exact checked_error cx param self related bindings _ stateGood (ExpressionRead.Extends.refl _)
      | ok result =>
        dsimp only
        refine ⟨stateGood, ExpressionRead.Extends.refl _, ?_⟩
        intro output same
        cases Except.ok.inj same
        obtain ⟨target, rel, read⟩ := childRead
        obtain ⟨res, withC, readRes⟩ := lowerContract_read cx param self contract source lowered state read
        exact ⟨res, frameWrap frame contract parsed target res rel withC, readRes⟩
  · rename_i plain
    have plain : Ix.SemanticContract.hasMetadata data = false := by simpa using plain
    have prepared := compileKVMap_good cx param self related bindings data context before good aligned
    apply then_checked cx param self related bindings _ context before prepared
    intro kvmap middle _ middleGood
    apply child_then_checked cx param self related bindings _ source context middle
      (childCorrect middle middleGood)
    intro value state stateGood _ childRead
    obtain ⟨target, rel, read⟩ := childRead
    exact allocFinish_checked cx param self related bindings _ _ value.1 context state stateGood
      ⟨target, plainWrap plain target rel, read⟩

/-! ## Applications -/

theorem decomposeApps_go (e : Ix.Expr) (acc : Array Ix.Expr) :
    Ix.CompileM.decomposeApps.go e acc =
      ((Ix.CompileM.decomposeApps e).1, (Ix.CompileM.decomposeApps e).2 ++ acc.reverse) := by
  induction e generalizing acc with
  | app f a h ihf _ =>
    show Ix.CompileM.decomposeApps.go f (acc.push a) =
      ((Ix.CompileM.decomposeApps.go f (#[].push a)).1, (Ix.CompileM.decomposeApps.go f (#[].push a)).2 ++ acc.reverse)
    rw [ihf (acc.push a), ihf (#[].push a)]
    simp [Array.reverse_push]
  | _ => simp [Ix.CompileM.decomposeApps, Ix.CompileM.decomposeApps.go]

theorem decomposeApps_app (f a : Ix.Expr) (h : Address) :
    Ix.CompileM.decomposeApps (.app f a h) =
      ((Ix.CompileM.decomposeApps f).1, (Ix.CompileM.decomposeApps f).2.push a) := by
  show Ix.CompileM.decomposeApps.go f (#[].push a) = _
  rw [decomposeApps_go]
  simp

/-- The head and the arguments of a spine are among its subterms, so they
keep every property of the spine's constant occurrences. -/
theorem constsSatisfy_spine {P : Ix.Name → Prop} :
    ∀ (e : Ix.Expr), ConstsSatisfy P e →
      ConstsSatisfy P (Ix.CompileM.decomposeApps e).1 ∧
        ∀ x ∈ (Ix.CompileM.decomposeApps e).2, ConstsSatisfy P x := by
  intro e
  induction e with
  | app f a h ihf _ =>
    intro scope
    obtain ⟨fScope, aScope⟩ := scope
    rw [decomposeApps_app]
    obtain ⟨headScope, argsScope⟩ := ihf fScope
    refine ⟨headScope, fun x member => ?_⟩
    rw [Array.mem_push] at member
    rcases member with old | rfl
    · exact argsScope x old
    · exact aScope
  | _ =>
    intro scope
    simp only [Ix.CompileM.decomposeApps, Ix.CompileM.decomposeApps.go, Array.reverse_empty]
    exact ⟨scope, fun x member => by simp at member⟩

theorem forall₂_snoc {R : α → β → Prop} {items : List α} {item : α} {targets : List β}
    (related : List.Forall₂ R (items ++ [item]) targets) :
    ∃ init last, targets = init ++ [last] ∧ List.Forall₂ R items init ∧ R item last := by
  induction items generalizing targets with
  | nil =>
    cases related with
    | cons head tail =>
      cases tail
      exact ⟨[], _, rfl, .nil, head⟩
  | cons first rest ih =>
    cases related with
    | cons head tail =>
      obtain ⟨init, last, rfl, initRel, lastRel⟩ := ih tail
      exact ⟨_ :: init, last, rfl, .cons head initRel, lastRel⟩

/-- **A spine reads as its head applied to its arguments**: if the head of
`e`'s application spine is related to `head` and its arguments to
`targets`, then `e` is related to the applications of `head` to `targets`. -/
theorem spine_related (applications : ∀ f a h tf ta, related f tf → related a ta →
      related (.app f a h) (.app tf ta)) :
    ∀ (e : Ix.Expr) (head : CExpr md) (targets : List (CExpr md)),
      related (Ix.CompileM.decomposeApps e).1 head →
      List.Forall₂ related (Ix.CompileM.decomposeApps e).2.toList targets →
      related e (targets.foldl .app head) := by
  intro e
  induction e with
  | app f a h ihf _ =>
    intro head targets headRel argsRel
    rw [decomposeApps_app] at headRel argsRel
    rw [Array.toList_push] at argsRel
    obtain ⟨init, last, rfl, initRel, lastRel⟩ := forall₂_snoc argsRel
    rw [List.foldl_append]
    exact applications f a h _ _ (ihf head init headRel initRel) lastRel
  | _ =>
    intro head targets headRel argsRel
    simp only [Ix.CompileM.decomposeApps, Ix.CompileM.decomposeApps.go, Array.reverse_empty,
      Array.toList_empty] at headRel argsRel
    cases argsRel
    exact headRel

/-- One application of the spine's fold. -/
def appBody (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (acc : Ixon.Expr × UInt64)
    (x : Ix.Expr) : CompileM (ForInStep (Ixon.Expr × UInt64)) := do
  let child ← compile x
  let root ← allocArenaNode (.app acc.2 child.2)
  pure (ForInStep.yield (Ixon.Expr.app acc.1 child.1, root))

theorem app_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (fn arg : Ix.Expr)
    (hash : Address) :
    step compile (.app fn arg hash) = (do
      let head ← compile (Ix.CompileM.decomposeApps (.app fn arg hash)).1
      let spine ← forIn' (Ix.CompileM.decomposeApps (.app fn arg hash)).2 ((head.1, head.2) : Ixon.Expr × UInt64)
        fun x _ (acc : Ixon.Expr × UInt64) => appBody compile acc x
      pure (spine.1, spine.2)) := rfl

/-- The spine's fold: every run keeps `Good` and extends the reader, and a
successful one reads as the accumulator's reading applied to the arguments'
readings. -/
theorem appLoop_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (context : CompileEnv × BlockEnv) (items : List Ix.Expr)
    (children : ∀ x ∈ items, ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings x state (rawRun (compile x) context state)) :
    ∀ (acc : Ixon.Expr × UInt64) (target : CExpr md) (before : BlockState),
      Good cx param self related bindings before → (reader before).read acc.1 = .ok target →
      let result := rawRun (forIn items acc (fun x acc => appBody compile acc x)) context before
      Good cx param self related bindings result.2 ∧
        ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
        ∀ value, result.1 = .ok value → ∃ targets, List.Forall₂ related items targets ∧
          (reader result.2).read value.1 = .ok (targets.foldl .app target) := by
  induction items with
  | nil =>
    intro acc target before good read
    refine ⟨good, ExpressionRead.Extends.refl _, ?_⟩
    intro value same
    cases Except.ok.inj same
    exact ⟨[], .nil, read⟩
  | cons x rest ih =>
    intro acc target before good read
    have childResult := children x (by simp) before good
    cases ran : rawRun (compile x) context before with
    | mk outcome middle =>
      rw [ran] at childResult
      cases outcome with
      | error error =>
        have run : rawRun (forIn (x :: rest) acc (fun x acc => appBody compile acc x)) context before =
            (.error error, middle) := by
          simp only [List.forIn_cons, appBody, rawRun_bind, ran]
        rw [run]
        exact ⟨childResult.1, childResult.2.1, by intro value bad; cases bad⟩
      | ok child =>
        obtain ⟨tx, rx, readChild⟩ := childResult.2.2 child rfl
        let after : BlockState := { middle with arena := { nodes := middle.arena.nodes.push (.app acc.2 child.2) } }
        have frame : withoutExprMetadata after = withoutExprMetadata middle := rfl
        have afterGood := good_metadata cx param self related bindings frame childResult.1
        have sameReader := withoutExprMetadata_reader cx param self frame
        have readApp : (reader after).read (Ixon.Expr.app acc.1 child.1) = .ok (.app target tx) := by
          rw [sameReader]
          have readAcc := read_grows cx param self childResult.2.1 read
          change ((reader middle).read acc.1 >>= fun f => (reader middle).read child.1 >>= fun a =>
            pure (Ix.Kernel.Expr.app f a)) = _
          rw [readAcc, readChild]
          rfl
        have run : rawRun (forIn (x :: rest) acc (fun x acc => appBody compile acc x)) context before =
            rawRun (forIn rest (Ixon.Expr.app acc.1 child.1, middle.arena.nodes.size.toUInt64)
              (fun x acc => appBody compile acc x)) context after := by
          simp only [List.forIn_cons, appBody, rawRun_bind, ran, allocArenaNode, rawRun_modifyGet,
            rawRun_pure]
          rfl
        have tail := ih (fun y member => children y (by simp [member]))
          (Ixon.Expr.app acc.1 child.1, middle.arena.nodes.size.toUInt64) (.app target tx) after afterGood readApp
        rw [run]
        rw [sameReader] at tail
        refine ⟨tail.1, extends_trans childResult.2.1 tail.2.1, ?_⟩
        intro value success
        obtain ⟨targets, rel, readSpine⟩ := tail.2.2 value success
        exact ⟨tx :: targets, .cons rx rel, readSpine⟩

theorem app_step_checked (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64)) (fn arg : Ix.Expr)
    (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (good : Good cx param self related bindings before)
    (headCorrect : ∀ state, Good cx param self related bindings state →
      Checked cx param self related bindings (Ix.CompileM.decomposeApps (.app fn arg hash)).1 state
        (rawRun (compile (Ix.CompileM.decomposeApps (.app fn arg hash)).1) context state))
    (argsCorrect : ∀ x ∈ (Ix.CompileM.decomposeApps (.app fn arg hash)).2, ∀ state,
      Good cx param self related bindings state →
      Checked cx param self related bindings x state (rawRun (compile x) context state))
    (applications : ∀ f a h tf ta, related f tf → related a ta → related (.app f a h) (.app tf ta)) :
    Checked cx param self related bindings (.app fn arg hash) before
      (rawRun (step compile (.app fn arg hash)) context before) := by
  rw [app_step_eq]
  apply child_then_checked cx param self related bindings _ _ context before
    (headCorrect before good)
  intro head state stateGood _ headRead
  obtain ⟨th, headRel, readHead⟩ := headRead
  rw [forIn'_eq_forIn _ _ _ (fun x acc => appBody compile acc x) (fun _ _ _ => rfl),
    ← Array.forIn_toList, rawRun_bind]
  have loop := appLoop_checked cx param self related bindings compile context
    (Ix.CompileM.decomposeApps (.app fn arg hash)).2.toList
    (fun x member => argsCorrect x (Array.mem_toList_iff.mp member))
    (head.1, head.2) th state stateGood readHead
  cases ran : rawRun (forIn (Ix.CompileM.decomposeApps (.app fn arg hash)).2.toList (head.1, head.2)
      (fun x acc => appBody compile acc x)) context state with
  | mk outcome after =>
    rw [ran] at loop
    cases outcome with
    | error error => exact checked_error cx param self related bindings error loop.1 loop.2.1
    | ok spine =>
      refine ⟨loop.1, loop.2.1, ?_⟩
      intro value same
      cases Except.ok.inj same
      obtain ⟨targets, argsRel, readSpine⟩ := loop.2.2 spine rfl
      exact ⟨targets.foldl .app th, spine_related related applications (.app fn arg hash) th targets
        headRel argsRel, readSpine⟩

end Steps

end Ix.CompileCert.ExpressionState
