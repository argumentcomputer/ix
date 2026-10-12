import Ix.CompileCert.MetadataMode

/-! Correctness of production expression compilation, including the actual
Pass 3 metadata-record loop. Ordinary callers enter with a valid cache and
reader; successful metadata compilation restores the saved ordinary cache
against unchanged primary tables and compatible blobs. Errors retain their
current valid reader view. Rewriting, declaration assembly, sharing and
serialization remain separate obligations. -/

namespace Ix.CompileCert.MetadataMode

open Ix.CompileM Ix.CompileCert.HeadWriterFrame

def inMode (mode : Bool) (state : BlockState) : BlockState := { state with p3MetaMode := mode }

theorem inMode_eq (mode : Bool) (state : BlockState) (same : state.p3MetaMode = mode) : inMode mode state = state := by
  cases state
  cases same
  rfl

theorem stateSound_mode (mode : Bool) (state : BlockState) (bindings : ExpressionState.Bindings)
    (sound : ExpressionState.StateSound bindings state) : ExpressionState.StateSound bindings (inMode mode state) :=
  ⟨⟨sound.1.rawCache, sound.1.canonCache, sound.1.tables⟩, sound.2.1, sound.2.2.1, sound.2.2.2⟩

theorem prefix_retains (primary extra : Array α) : Interning.Retains primary (primary ++ extra) := by
  intro index value found
  rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp found).1]
  exact found

section Reading

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
local notation "reader" => ExpressionRead.blockReader cx base param self

theorem enter_growth (state : BlockState) (mode : state.p3MetaMode = false) :
    ExpressionRead.Extends (reader state).ecx (reader (inMode true state)).ecx := by
  apply Interning.blockReader_growth cx base param self
  · simpa only [Interning.refTable, inMode, mode, Bool.false_eq_true, ↓reduceIte] using
      prefix_retains state.refs state.p3MetaRefs
  · simpa only [Interning.univTable, inMode, mode, Bool.false_eq_true, ↓reduceIte] using
      prefix_retains state.univs state.metaUnivs
  · rfl

theorem enter_good (related : Ix.Expr → Kernel.Expr → Prop) (bindings : ExpressionState.Bindings)
    (state : BlockState) (mode : state.p3MetaMode = false)
    (good : ExpressionState.Good cx base param self related bindings state) :
    ExpressionState.Good cx base param self related bindings (inMode true state) := by
  refine ⟨stateSound_mode true state bindings good.1, ?_⟩
  apply ExpressionRead.cache_sound_of_growth (enter_growth cx base param self state mode)
  · intro index value found
    change (#[] : Array (Kernel.Reader.ReadM Kernel.Expr))[index]? = some (.ok value) at found
    simp at found
  · rfl
  · exact good.2

def blobLookup (state : BlockState) (refs : Array Address) (index : UInt64) : Kernel.Reader.ReadM ByteArray := do
  let some address := refs[index.toNat]? | Kernel.Reader.malformed "literal reference index is out of bounds"
  let some bytes := (state.blockBlobs.get? address).orElse (fun _ => cx.blob address)
    | Kernel.Reader.malformed s!"literal blob {address} is missing"
  pure bytes

theorem blob_modes (state : BlockState) (index : UInt64) {address : Address}
    (found : state.refs[index.toNat]? = some address) :
    (reader (inMode false state)).ecx.blobAt index = (reader (inMode true state)).ecx.blobAt index := by
  change blobLookup cx state state.refs index = blobLookup cx state (state.refs ++ state.p3MetaRefs) index
  unfold blobLookup
  rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp found).1]

/-- Restrict a metadata reader extension back to its fixed primary tables.
Only the source lookup of an old literal must be transported through the
metadata view; primary reference/universe lookups are unchanged. -/
theorem primary_growth (before after : BlockState) (refs : after.refs = before.refs) (univs : after.univs = before.univs)
    (growth : ExpressionRead.Extends (reader (inMode true before)).ecx (reader (inMode true after)).ecx) :
    ExpressionRead.Extends (reader (inMode false before)).ecx (reader (inMode false after)).ecx := by
  constructor
  · intro index level found
    change (match (after.univs.map (Kernel.Reader.convUniv param))[index.toNat]? with
      | some value => pure value | none => Kernel.Reader.malformed "universe table index is out of bounds") = .ok level
    rw [univs]
    exact found
  · intro index ref found
    change (do
      let some address := after.refs[index.toNat]? | Kernel.Reader.malformed "reference index is out of bounds"
      let some resolved := Kernel.Reader.resolve cx.store address | Kernel.Reader.malformed s!"reference {address} is missing or has invalid ownership"
      pure resolved) = .ok ref
    rw [refs]
    exact found
  · intro index bytes found
    have slot : ∃ address, before.refs[index.toNat]? = some address := by
      change blobLookup cx before before.refs index = .ok bytes at found
      unfold blobLookup at found
      cases got : before.refs[index.toNat]? with
      | none => simp only [got, Kernel.Reader.malformed] at found; cases found
      | some address => exact ⟨address, rfl⟩
    obtain ⟨address, slot⟩ := slot
    have afterSlot : after.refs[index.toNat]? = some address := by rw [refs]; exact slot
    rw [blob_modes cx base param self before index slot] at found
    rw [blob_modes cx base param self after index afterSlot]
    exact growth.blob index bytes found
  · intro index name found; exact found
  · intro ref; rfl

def restore (before after : BlockState) (index : Nat) (value : Ixon.Expr × UInt64) : BlockState :=
  { after with
    p3MetaMode := false, exprCache := before.exprCache,
    p3Records := after.p3Records.insert index (after.metaSharing.size, value.2),
    metaSharing := after.metaSharing.push value.1 }

theorem restore_reader (before after : BlockState) (index : Nat) (value : Ixon.Expr × UInt64) :
    reader (restore before after index value) = reader (inMode false after) := rfl

theorem restore_good (related : Ix.Expr → Kernel.Expr → Prop) (bindings : ExpressionState.Bindings)
    (before after : BlockState) (index : Nat) (value : Ixon.Expr × UInt64)
    (mode : before.p3MetaMode = false) (good : ExpressionState.Good cx base param self related bindings before)
    (sound : ExpressionState.StateSound bindings after) (refs : after.refs = before.refs) (univs : after.univs = before.univs)
    (growth : ExpressionRead.Extends (reader (inMode true before)).ecx (reader (inMode true after)).ecx) :
    ExpressionState.Good cx base param self related bindings (restore before after index value) ∧
      ExpressionRead.Extends (reader before).ecx (reader (restore before after index value)).ecx := by
  have primary := primary_growth cx base param self before after refs univs growth
  rw [inMode_eq false before mode] at primary
  have restored : ExpressionRead.Extends (reader before).ecx (reader (restore before after index value)).ecx := primary
  refine ⟨⟨⟨⟨sound.1.rawCache, sound.1.canonCache, sound.1.tables⟩, sound.2.1, sound.2.2.1, sound.2.2.2⟩, ?_⟩, restored⟩
  apply ExpressionRead.cache_sound_of_growth restored
  · intro slot target found
    change (#[] : Array (Kernel.Reader.ReadM Kernel.Expr))[slot]? = some (.ok target) at found
    simp at found
  · rfl
  · exact good.2

end Reading

def recordStep (env : CompileEnv) (index : Nat) : CompileM Unit := do
  if (← getBlockState).p3Records.contains index then return ()
  let some source := env.p3Sources.get? index
    | throw (.invalidMutualBlock s!"Pass 3: no source occurrence for call-site record {index}")
  let savedCache := (← getBlockState).exprCache
  modifyBlockState fun state => { state with p3MetaMode := true }
  let (value, root) ← compileExprPartial source
  modifyBlockState fun state => { state with
    p3MetaMode := false, exprCache := savedCache,
    p3Records := state.p3Records.insert index (state.metaSharing.size, root),
    metaSharing := state.metaSharing.push value }

section Records

variable (cx : Kernel.Reader.Ctx) (base : Ixon.Constant) (self : Nat → Option Kernel.Name)
  (names : Ix.Name → Kernel.Name → Prop) (params : List Kernel.Name)
  (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)

local notation "param" => Kernel.Reader.paramOf params
local notation "related" => ExpressionState.Related names (BlockEnv.univCtx (Prod.snd context)) params
local notation "reader" => ExpressionRead.blockReader cx base param self
local notation "Good" => ExpressionState.Good cx base param self related bindings

def RecordResult (before : BlockState) (result : Except CompileError α × BlockState) : Prop :=
  Good result.2 ∧ ExpressionRead.Extends (reader before).ecx (reader result.2).ecx ∧
    ∀ value, result.1 = .ok value → result.2.p3MetaMode = false

theorem recordStep_correct (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (env : CompileEnv) (index : Nat) (before : BlockState) (good : Good before) (mode : before.p3MetaMode = false) :
    RecordResult cx base self names params bindings context before (rawRun (recordStep env index) context before) := by
  unfold recordStep
  simp only [rawRun_bind, rawRun_get]
  by_cases already : before.p3Records.contains index = true
  · simp only [already, ↓reduceIte, rawRun_pure]
    exact ⟨good, ExpressionState.extends_refl _, fun _ _ => mode⟩
  · simp only [already, Bool.false_eq_true, ↓reduceIte]
    cases sourceFound : env.p3Sources.get? index with
    | none => exact ⟨good, ExpressionState.extends_refl _, by intro value bad; cases bad⟩
    | some source =>
      simp only [rawRun_bind, rawRun_get, rawRun_modify]
      have enteredGood := enter_good cx base param self related bindings before mode good
      have enteredGrowth := enter_growth cx base param self before mode
      have checked := ExpressionState.compileExprPartial_checked cx base self names params bindings context
        arity aligned external selfSound source (inMode true before) enteredGood
      have framed := Frame.compileExprPartial source context (inMode true before)
      simp only [inMode] at checked framed
      cases compiled : rawRun (compileExprPartial source) context { before with p3MetaMode := true } with
      | mk outcome after =>
        rw [compiled] at checked framed
        have afterMode : after.p3MetaMode = true := framed.1
        cases outcome with
        | error error => exact ⟨checked.1, ExpressionState.extends_trans enteredGrowth checked.2.1,
            by intro value bad; cases bad⟩
        | ok value =>
          rcases value with ⟨value, root⟩
          have tables := framed.2 rfl
          have metaGrowth : ExpressionRead.Extends (reader (inMode true before)).ecx (reader (inMode true after)).ecx := by
            rw [inMode_eq true after afterMode]
            exact checked.2.1
          have restored := restore_good cx base param self related bindings before after index (value, root) mode good checked.1.1
            tables.1 tables.2 metaGrowth
          exact ⟨restored.1, restored.2, by intro result _; rfl⟩

def RecordSafe (action : CompileM α) : Prop :=
  ∀ before, Good before → before.p3MetaMode = false →
    RecordResult cx base self names params bindings context before (rawRun action context before)

theorem RecordSafe.pure (value : α) : RecordSafe cx base self names params bindings context (pure value) :=
  fun _ good mode => ⟨good, ExpressionState.extends_refl _, fun _ _ => mode⟩

theorem RecordSafe.read : RecordSafe cx base self names params bindings context getCompileEnv :=
  fun _ good mode => ⟨good, ExpressionState.extends_refl _, fun _ _ => mode⟩

theorem RecordSafe.bind {action : CompileM α} {next : α → CompileM β}
    (first : RecordSafe cx base self names params bindings context action)
    (later : ∀ value, RecordSafe cx base self names params bindings context (next value)) :
    RecordSafe cx base self names params bindings context (action >>= next) := by
  intro before good mode
  have head := first before good mode
  rw [rawRun_bind]
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at head
    cases outcome with
    | error error => exact ⟨head.1, head.2.1, by intro value bad; cases bad⟩
    | ok value =>
      have tail := later value middle head.1 (head.2.2 value rfl)
      exact ⟨tail.1, ExpressionState.extends_trans head.2.1 tail.2.1, tail.2.2⟩

theorem RecordSafe.forIn_list (items : List α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item acc, RecordSafe cx base self names params bindings context (body item acc)) :
    RecordSafe cx base self names params bindings context (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact RecordSafe.pure cx base self names params bindings context _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply RecordSafe.bind cx base self names params bindings context (each item initial)
    intro step
    cases step with
    | done value => exact RecordSafe.pure cx base self names params bindings context value
    | yield value => exact ih value

theorem RecordSafe.forIn_array (items : Array α) (initial : β) (body : α → β → CompileM (ForInStep β))
    (each : ∀ item acc, RecordSafe cx base self names params bindings context (body item acc)) :
    RecordSafe cx base self names params bindings context (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact RecordSafe.forIn_list cx base self names params bindings context _ initial body each

theorem pass3CompileRecords_eq (source : Ix.Expr) :
    pass3CompileRecords source = (do
      let env ← getCompileEnv
      for index in pass3Placeholders source do recordStep env index) := by
  unfold pass3CompileRecords
  apply congrArg (fun next : CompileEnv → CompileM Unit => getCompileEnv >>= next)
  funext env
  apply congrArg (fun action : CompileM PUnit => action >>= fun _ => pure ())
  apply congrArg (fun body : Nat → PUnit → CompileM (ForInStep PUnit) => forIn (pass3Placeholders source) () body)
  funext index acc
  unfold recordStep
  simp only [bind_assoc]
  apply congrArg (fun next : BlockState → CompileM (ForInStep PUnit) => getBlockState >>= next)
  funext state
  cases state.p3Records.contains index <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases env.p3Sources.get? index <;> simp only [bind_assoc]

theorem pass3CompileRecords_correct (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names) (source : Ix.Expr) :
    RecordSafe cx base self names params bindings context (pass3CompileRecords source) := by
  rw [pass3CompileRecords_eq]
  apply RecordSafe.bind cx base self names params bindings context (RecordSafe.read cx base self names params bindings context)
  intro env
  apply RecordSafe.bind cx base self names params bindings context
  · apply RecordSafe.forIn_array cx base self names params bindings context
    intro index _
    exact RecordSafe.bind cx base self names params bindings context
      (recordStep_correct cx base self names params bindings context arity aligned external selfSound env index)
      (fun _ => RecordSafe.pure cx base self names params bindings context _)
  · intro _; exact RecordSafe.pure cx base self names params bindings context _

theorem ordinary_correct (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (source : Ix.Expr) (before : BlockState) (good : Good before) (mode : before.p3MetaMode = false) :
    ExpressionState.Checked cx base param self related bindings source before (rawRun (compileExprPartial source) context before) ∧
      (rawRun (compileExprPartial source) context before).2.p3MetaMode = false :=
  ⟨ExpressionState.compileExprPartial_checked cx base self names params bindings context arity aligned external selfSound source before good,
    (Frame.compileExprPartial source context before).1.trans mode⟩

/-- Production expression compilation, including the real Pass 3 metadata
prepass. Successful runs finish in ordinary mode; failed runs keep a valid
current reader view and all earlier readings. -/
theorem compileExpr_checked (arity : params.length = context.2.univCtx.length)
    (aligned : ∀ address, cx.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings cx names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (source : Ix.Expr) (before : BlockState) (good : Good before) (mode : before.p3MetaMode = false) :
    let result := rawRun (compileExpr source) context before
    ExpressionState.Checked cx base param self related bindings source before result ∧
      ∀ value, result.1 = .ok value → result.2.p3MetaMode = false := by
  unfold compileExpr
  simp only [rawRun_bind, rawRun_read]
  by_cases pass3 : context.1.pass3 = true
  · simp only [pass3, ↓reduceIte]
    by_cases empty : context.1.p3Sources.isEmpty = true
    · simp only [empty, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have checked := ordinary_correct cx base self names params bindings context arity aligned external selfSound source before good mode
      exact ⟨checked.1, fun _ _ => checked.2⟩
    · have nonempty : context.1.p3Sources.isEmpty = false := Bool.eq_false_iff.mpr empty
      simp only [nonempty, Bool.not_false, ↓reduceIte, rawRun_bind]
      have prepass := pass3CompileRecords_correct cx base self names params bindings context arity aligned external selfSound source before good mode
      cases ran : rawRun (pass3CompileRecords source) context before with
      | mk outcome middle =>
        rw [ran] at prepass
        cases outcome with
        | error error => exact ⟨⟨prepass.1, prepass.2.1, by intro value bad; cases bad⟩, by intro value bad; cases bad⟩
        | ok doneValue =>
          have checked := ordinary_correct cx base self names params bindings context arity aligned external selfSound source middle
            prepass.1 (prepass.2.2 doneValue rfl)
          exact ⟨⟨checked.1.1, ExpressionState.extends_trans prepass.2.1 checked.1.2.1, checked.1.2.2⟩,
            fun _ _ => checked.2⟩
  · simp only [pass3, Bool.false_eq_true, ↓reduceIte]
    rw [compileExprTotal_eq_partial]
    have checked := ordinary_correct cx base self names params bindings context arity aligned external selfSound source before good mode
    exact ⟨checked.1, fun _ _ => checked.2⟩

end Records

end Ix.CompileCert.MetadataMode
