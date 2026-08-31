import Ix.Compile.Verify.CompileState

/-!
# Expression-metadata refinement

This module relates production `DataValue` and `KVMap` compilation to a
small total reference compiler. Recursive syntax metadata is included through
the kernel-visible total production `serializeIxSyntax` traversal.
-/

namespace Ix.Compile.Verify

/-- Concatenate serialized pieces in source order. -/
def concatSerialized (parts : Array ByteArray) : ByteArray :=
  parts.foldl (fun bytes part => bytes ++ part) ByteArray.empty

/-- Pure reference encoding for a source substring. -/
def serializeIxSubstringRef (source : Ix.Substring) : ByteArray :=
  (Address.blake3 source.str.toUTF8).hash ++
    Ix.CompileM.putTag0 source.startPos ++
    Ix.CompileM.putTag0 source.stopPos

/-- Pure reference encoding for source-location metadata. -/
def serializeIxSourceInfoRef : Ix.SourceInfo → ByteArray
  | .original leading leadingPos trailing trailingPos =>
    ByteArray.mk #[0] ++ serializeIxSubstringRef leading ++
      Ix.CompileM.putTag0 leadingPos ++ serializeIxSubstringRef trailing ++
      Ix.CompileM.putTag0 trailingPos
  | .synthetic start stop canonical =>
    ByteArray.mk #[1] ++ Ix.CompileM.putTag0 start ++
      Ix.CompileM.putTag0 stop ++ ByteArray.mk #[if canonical then 1 else 0]
  | .none => ByteArray.mk #[2]

/-- Pure reference encoding for a preresolved syntax identifier. -/
def serializeIxSyntaxPreresolvedRef : Ix.SyntaxPreresolved → ByteArray
  | .namespace name => ByteArray.mk #[0] ++ name.getHash.hash
  | .decl name aliases =>
    let header := ByteArray.mk #[1] ++ name.getHash.hash ++
      Ix.CompileM.putTag0 aliases.size
    let aliasHashes := aliases.map fun aliasValue =>
      (Address.blake3 aliasValue.toUTF8).hash
    header ++ concatSerialized aliasHashes

/-- Pure total reference encoding for recursive syntax metadata. -/
def serializeIxSyntaxRef (source : Ix.Syntax) : ByteArray :=
  match source with
  | .missing => ByteArray.mk #[0]
  | .node info kind args =>
    let serializedArgs := args.attach.map fun arg =>
      serializeIxSyntaxRef arg.1
    ByteArray.mk #[1] ++ serializeIxSourceInfoRef info ++ kind.getHash.hash ++
      Ix.CompileM.putTag0 args.size ++ concatSerialized serializedArgs
  | .atom info value =>
    ByteArray.mk #[2] ++ serializeIxSourceInfoRef info ++
      (Address.blake3 value.toUTF8).hash
  | .ident info rawValue value preresolved =>
    let serializedPres := preresolved.map serializeIxSyntaxPreresolvedRef
    ByteArray.mk #[3] ++ serializeIxSourceInfoRef info ++
      serializeIxSubstringRef rawValue ++ value.getHash.hash ++
      Ix.CompileM.putTag0 preresolved.size ++ concatSerialized serializedPres
termination_by sizeOf source
decreasing_by
  simp_wf
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem arg.property) (by omega)

/-- Pure wire encoding for every metadata value. -/
def compileDataValueRef : Ix.DataValue → Option Ixon.DataValue
  | .ofString value => some (.ofString (Address.blake3 value.toUTF8))
  | .ofBool value => some (.ofBool value)
  | .ofName value => some (.ofName value.getHash)
  | .ofNat value => some
      (.ofNat (Address.blake3 (ByteArray.mk (Nat.toBytesLE value))))
  | .ofInt value => some
      (.ofInt (Address.blake3 (Ix.CompileM.serializeIxInt value)))
  | .ofSyntax value => some
      (.ofSyntax (Address.blake3 (serializeIxSyntaxRef value)))

private def compileKVEntryRef
    (entry : Ix.Name × Ix.DataValue) : Option (Address × Ixon.DataValue) :=
  match entry with
  | (name, value) => do
    let encoded ← compileDataValueRef value
    pure (name.getHash, encoded)

/-- Pure reference compiler for an expression metadata map. -/
def compileKVMapRef (entries : Array (Ix.Name × Ix.DataValue)) :
    Option Ixon.KVMap :=
  entries.mapM compileKVEntryRef

/-- Source metadata is supported when every value has a total wire encoding.
After syntax totalization this predicate holds for every source map; it is
retained as the support interface consumed by the ordinary-expression layer. -/
def KVMapSupported (entries : Array (Ix.Name × Ix.DataValue)) : Prop :=
  ∃ encoded, compileKVMapRef entries = some encoded

theorem KVMapSupported.empty : KVMapSupported #[] := by
  exact ⟨#[], by simp [compileKVMapRef]⟩

private theorem compileKVEntryRef_some
    (entry : Ix.Name × Ix.DataValue) :
    ∃ encoded, compileKVEntryRef entry = some encoded := by
  rcases entry with ⟨name, value⟩
  cases value <;> exact ⟨_, rfl⟩

private theorem compileKVMapRef_list_some
    (entries : List (Ix.Name × Ix.DataValue)) :
    ∃ encoded, entries.mapM compileKVEntryRef = some encoded := by
  induction entries with
  | nil => exact ⟨[], rfl⟩
  | cons entry entries ih =>
    obtain ⟨head, hhead⟩ := compileKVEntryRef_some entry
    obtain ⟨tail, htail⟩ := ih
    exact ⟨head :: tail, by simp [List.mapM_cons, hhead, htail]⟩

/-- Syntax totalization makes every source metadata map supported. -/
theorem KVMapSupported.all (entries : Array (Ix.Name × Ix.DataValue)) :
    KVMapSupported entries := by
  obtain ⟨encoded, href⟩ := compileKVMapRef_list_some entries.toList
  refine ⟨encoded.toArray, ?_⟩
  rw [compileKVMapRef, Array.mapM_eq_mapM_toList, map_eq_pure_bind, href]
  rfl

/-- Metadata serialization may grow only the presentation-side name and blob
stores.  Every field used by expression semantics, memoization, universe
compilation, or arena reasoning remains fixed. -/
structure MetaStateFrame (before after : Ix.CompileM.BlockState) : Prop where
  tables : exprTableView after = exprTableView before
  exprCache : after.exprCache = before.exprCache
  univCache : after.univCache = before.univCache
  canonUnivCache : after.canonUnivCache = before.canonUnivCache
  arena : after.arena = before.arena

theorem MetaStateFrame.refl (state : Ix.CompileM.BlockState) :
    MetaStateFrame state state := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem MetaStateFrame.trans {first second third : Ix.CompileM.BlockState}
    (hfirst : MetaStateFrame first second)
    (hsecond : MetaStateFrame second third) : MetaStateFrame first third := by
  exact
    { tables := hsecond.tables.trans hfirst.tables
      exprCache := hsecond.exprCache.trans hfirst.exprCache
      univCache := hsecond.univCache.trans hfirst.univCache
      canonUnivCache := hsecond.canonUnivCache.trans hfirst.canonUnivCache
      arena := hsecond.arena.trans hfirst.arena }

private def insertBlobState (state : Ix.CompileM.BlockState)
    (addr : Address) (bytes : ByteArray) : Ix.CompileM.BlockState :=
  { state with blockBlobs := state.blockBlobs.insert addr bytes }

private theorem MetaStateFrame.insertBlob (state : Ix.CompileM.BlockState)
    (addr : Address) (bytes : ByteArray) :
    MetaStateFrame state (insertBlobState state addr bytes) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Pure name compilation has the same metadata-only frame. -/
theorem MetaStateFrame.compileName (state : Ix.CompileM.BlockState)
    (name : Ix.Name) : MetaStateFrame state (state.compileName name) := by
  induction name generalizing state with
  | anonymous hash =>
    rw [Ix.CompileM.BlockState.compileName.eq_1]
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | str parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · let next : Ix.CompileM.BlockState :=
        { state with
          blockNames := state.blockNames.insert
            (parent.str value hash).getHash (parent.str value hash)
          blockBlobs := state.blockBlobs.insert
            (Address.blake3 value.toUTF8) value.toUTF8 }
      have hprefix : MetaStateFrame state next :=
        ⟨rfl, rfl, rfl, rfl, rfl⟩
      simpa [next] using hprefix.trans (ih next)
  | num parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · let next : Ix.CompileM.BlockState :=
        { state with
          blockNames := state.blockNames.insert
            (parent.num value hash).getHash (parent.num value hash) }
      have hprefix : MetaStateFrame state next :=
        ⟨rfl, rfl, rfl, rfl, rfl⟩
      simpa [next] using hprefix.trans (ih next)

/-- Compiling an ordered array of names preserves the same metadata-only
frame. -/
theorem MetaStateFrame.compileNames (state : Ix.CompileM.BlockState)
    (names : Array Ix.Name) :
    MetaStateFrame state (state.compileNames names) := by
  unfold Ix.CompileM.BlockState.compileNames
  apply Array.foldl_induction
    (motive := fun _ current => MetaStateFrame state current)
  · exact MetaStateFrame.refl state
  · intro i current hcurrent
    exact hcurrent.trans (MetaStateFrame.compileName current names[i])

private theorem run_bind (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (action : Ix.CompileM.CompileM α) (next : α → Ix.CompileM.CompileM β) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (action >>= next) =
      match Ix.CompileM.CompileM.run compileEnv blockEnv state action with
      | .error err => .error err
      | .ok (value, state') =>
        Ix.CompileM.CompileM.run compileEnv blockEnv state' (next value) := by
  simp [Ix.CompileM.CompileM.run, ReaderT.run_bind, ExceptT.run_bind,
    StateT.run_bind]
  generalize
    (ReaderT.run action (compileEnv, blockEnv)).run.run state = result
  rcases result with ⟨result, state'⟩
  cases result <;> rfl

private theorem run_pure (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (value : α) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state (pure value) =
      .ok (value, state) := by
  rfl

private theorem run_compileName (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileName name) =
      .ok ((), state.compileName name) := by
  rfl

private theorem run_storeString (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (value : String) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.storeString value) =
      let bytes := value.toUTF8
      let addr := Address.blake3 bytes
      .ok (addr, insertBlobState state addr bytes) := by
  rfl

private theorem storeString_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (value : String) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.storeString value) =
        .ok (Address.blake3 value.toUTF8, state') ∧
      MetaStateFrame state state' := by
  let bytes := value.toUTF8
  let addr := Address.blake3 bytes
  exact ⟨insertBlobState state addr bytes,
    run_storeString compileEnv blockEnv state value,
    MetaStateFrame.insertBlob state addr bytes⟩

/-- A left-to-right list traversal inherits the metadata frame from each
element transition. -/
private theorem mapM_list_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (action : α → Ix.CompileM.CompileM β) (reference : α → β)
    (hstep : ∀ (state : Ix.CompileM.BlockState) (item : α),
      ∃ state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state (action item) =
          .ok (reference item, state') ∧ MetaStateFrame state state')
    (state : Ix.CompileM.BlockState) (items : List α) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (items.mapM action) = .ok (items.map reference, state') ∧
      MetaStateFrame state state' := by
  induction items generalizing state with
  | nil => exact ⟨state, rfl, MetaStateFrame.refl state⟩
  | cons item items ih =>
    obtain ⟨headState, hheadRun, hheadFrame⟩ := hstep state item
    obtain ⟨finalState, htailRun, htailFrame⟩ := ih headState
    refine ⟨finalState, ?_, hheadFrame.trans htailFrame⟩
    rw [List.mapM_cons, run_bind compileEnv blockEnv state _ _, hheadRun]
    simp only
    rw [run_bind compileEnv blockEnv headState _ _, htailRun]
    rfl

/-- Array form of `mapM_list_run_refines`, matching production serializer
loops. -/
private theorem mapM_array_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    (action : α → Ix.CompileM.CompileM β) (reference : α → β)
    (hstep : ∀ (state : Ix.CompileM.BlockState) (item : α),
      ∃ state',
        Ix.CompileM.CompileM.run compileEnv blockEnv state (action item) =
          .ok (reference item, state') ∧ MetaStateFrame state state')
    (state : Ix.CompileM.BlockState) (items : Array α) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (items.mapM action) = .ok (items.map reference, state') ∧
      MetaStateFrame state state' := by
  obtain ⟨state', hrun, hframe⟩ :=
    mapM_list_run_refines compileEnv blockEnv action reference hstep state
      items.toList
  refine ⟨state', ?_, hframe⟩
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind,
    run_bind compileEnv blockEnv state _ _, hrun]
  simp only
  rw [run_pure compileEnv blockEnv state']
  rw [List.map_toArray]

/-- Production substring serialization returns the pure reference bytes and
only commits the backing string blob. -/
theorem serializeIxSubstring_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.Substring) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.serializeIxSubstring source) =
        .ok (serializeIxSubstringRef source, state') ∧
      MetaStateFrame state state' := by
  obtain ⟨state', hrun, hframe⟩ :=
    storeString_run_refines compileEnv blockEnv state source.str
  refine ⟨state', ?_, hframe⟩
  rw [Ix.CompileM.serializeIxSubstring,
    run_bind compileEnv blockEnv state _ _, hrun]
  rfl

/-- Production source-info serialization refines its pure reference bytes. -/
theorem serializeIxSourceInfo_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.SourceInfo) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.serializeIxSourceInfo source) =
        .ok (serializeIxSourceInfoRef source, state') ∧
      MetaStateFrame state state' := by
  cases source with
  | original leading leadingPos trailing trailingPos =>
    obtain ⟨leadingState, hleadingRun, hleadingFrame⟩ :=
      serializeIxSubstring_run_refines compileEnv blockEnv state leading
    obtain ⟨finalState, htrailingRun, htrailingFrame⟩ :=
      serializeIxSubstring_run_refines compileEnv blockEnv leadingState trailing
    refine ⟨finalState, ?_, hleadingFrame.trans htrailingFrame⟩
    rw [Ix.CompileM.serializeIxSourceInfo,
      run_bind compileEnv blockEnv state _ _, hleadingRun]
    simp only
    rw [run_bind compileEnv blockEnv leadingState _ _, htrailingRun]
    rfl
  | synthetic start stop canonical =>
    exact ⟨state, rfl, MetaStateFrame.refl state⟩
  | none =>
    exact ⟨state, rfl, MetaStateFrame.refl state⟩

/-- Production preresolved-identifier serialization refines its pure
reference bytes. -/
theorem serializeIxSyntaxPreresolved_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.SyntaxPreresolved) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.serializeIxSyntaxPreresolved source) =
        .ok (serializeIxSyntaxPreresolvedRef source, state') ∧
      MetaStateFrame state state' := by
  cases source with
  | «namespace» name =>
    exact ⟨state.compileName name, rfl,
      MetaStateFrame.compileName state name⟩
  | decl name aliases =>
    let nameState := state.compileName name
    obtain ⟨finalState, haliasesRun, haliasesFrame⟩ :=
      mapM_array_run_refines compileEnv blockEnv Ix.CompileM.storeString
        (fun value => Address.blake3 value.toUTF8)
        (fun current value =>
          storeString_run_refines compileEnv blockEnv current value)
        nameState aliases
    refine ⟨finalState, ?_,
      (MetaStateFrame.compileName state name).trans haliasesFrame⟩
    rw [Ix.CompileM.serializeIxSyntaxPreresolved,
      run_bind compileEnv blockEnv state _ _, run_compileName]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, haliasesRun]
    simp only
    rw [run_pure]
    simp [serializeIxSyntaxPreresolvedRef, concatSerialized]
    rw [Array.foldl_map' (w := rfl), Array.foldl_map' (w := rfl)]

private theorem serializeIxSyntaxPreresolved_array_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (sources : Array Ix.SyntaxPreresolved) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (sources.mapM Ix.CompileM.serializeIxSyntaxPreresolved) =
        .ok (sources.map serializeIxSyntaxPreresolvedRef, state') ∧
      MetaStateFrame state state' := by
  exact mapM_array_run_refines compileEnv blockEnv
    Ix.CompileM.serializeIxSyntaxPreresolved
    serializeIxSyntaxPreresolvedRef
    (fun current source =>
      serializeIxSyntaxPreresolved_run_refines compileEnv blockEnv current source)
    state sources

/-- The total production syntax serializer returns exactly the pure recursive
reference bytes and changes only presentation-side name/blob stores. -/
theorem serializeIxSyntax_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (source : Ix.Syntax) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.serializeIxSyntax source) =
        .ok (serializeIxSyntaxRef source, state') ∧
      MetaStateFrame state state' := by
  induction source using Ix.CompileM.serializeIxSyntax.induct generalizing state with
  | case1 =>
    exact ⟨state, by
      rw [Ix.CompileM.serializeIxSyntax.eq_1,
        serializeIxSyntaxRef.eq_1]
      rfl, MetaStateFrame.refl state⟩
  | case2 info kind args ih =>
    let nameState := state.compileName kind
    obtain ⟨infoState, hinfoRun, hinfoFrame⟩ :=
      serializeIxSourceInfo_run_refines compileEnv blockEnv nameState info
    obtain ⟨finalState, hargsRun, hargsFrame⟩ :=
      mapM_array_run_refines compileEnv blockEnv
        (fun arg : { child // child ∈ args } =>
          Ix.CompileM.serializeIxSyntax arg.1)
        (fun arg : { child // child ∈ args } =>
          serializeIxSyntaxRef arg.1)
        (fun current arg => ih arg current) infoState args.attach
    refine ⟨finalState, ?_,
      (MetaStateFrame.compileName state kind).trans
        (hinfoFrame.trans hargsFrame)⟩
    rw [Ix.CompileM.serializeIxSyntax.eq_2,
      run_bind compileEnv blockEnv state _ _, run_compileName]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, hinfoRun]
    simp only
    rw [run_bind compileEnv blockEnv infoState _ _, hargsRun]
    simp only
    rw [run_pure, serializeIxSyntaxRef.eq_2]
    rfl
  | case3 info value =>
    obtain ⟨infoState, hinfoRun, hinfoFrame⟩ :=
      serializeIxSourceInfo_run_refines compileEnv blockEnv state info
    obtain ⟨finalState, hvalueRun, hvalueFrame⟩ :=
      storeString_run_refines compileEnv blockEnv infoState value
    refine ⟨finalState, ?_, hinfoFrame.trans hvalueFrame⟩
    rw [Ix.CompileM.serializeIxSyntax.eq_3,
      run_bind compileEnv blockEnv state _ _, hinfoRun]
    simp only
    rw [run_bind compileEnv blockEnv infoState _ _, hvalueRun]
    simp only
    rw [run_pure, serializeIxSyntaxRef.eq_3]
  | case4 info rawValue value preresolved =>
    let nameState := state.compileName value
    obtain ⟨infoState, hinfoRun, hinfoFrame⟩ :=
      serializeIxSourceInfo_run_refines compileEnv blockEnv nameState info
    obtain ⟨rawState, hrawRun, hrawFrame⟩ :=
      serializeIxSubstring_run_refines compileEnv blockEnv infoState rawValue
    obtain ⟨finalState, hpresRun, hpresFrame⟩ :=
      serializeIxSyntaxPreresolved_array_run_refines compileEnv blockEnv
        rawState preresolved
    refine ⟨finalState, ?_,
      (MetaStateFrame.compileName state value).trans
        (hinfoFrame.trans (hrawFrame.trans hpresFrame))⟩
    rw [Ix.CompileM.serializeIxSyntax.eq_4,
      run_bind compileEnv blockEnv state _ _, run_compileName]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, hinfoRun]
    simp only
    rw [run_bind compileEnv blockEnv infoState _ _, hrawRun]
    simp only
    rw [run_bind compileEnv blockEnv rawState _ _, hpresRun]
    simp only
    rw [run_pure, serializeIxSyntaxRef.eq_4]
    rfl

/-- Production metadata compilation returns exactly the reference
wire value and changes only presentation-side metadata stores. -/
theorem compileDataValue_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    {source : Ix.DataValue} {target : Ixon.DataValue}
    (href : compileDataValueRef source = some target) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDataValue source) = .ok (target, state') ∧
      MetaStateFrame state state' := by
  cases source with
  | ofString value =>
    simp only [compileDataValueRef, Option.some.injEq] at href
    subst target
    let bytes := value.toUTF8
    let addr := Address.blake3 bytes
    refine ⟨insertBlobState state addr bytes, ?_,
      MetaStateFrame.insertBlob state addr bytes⟩
    rfl
  | ofBool value =>
    simp only [compileDataValueRef, Option.some.injEq] at href
    subst target
    exact ⟨state, rfl, MetaStateFrame.refl state⟩
  | ofName value =>
    simp only [compileDataValueRef, Option.some.injEq] at href
    subst target
    exact ⟨state.compileName value, rfl,
      MetaStateFrame.compileName state value⟩
  | ofNat value =>
    simp only [compileDataValueRef, Option.some.injEq] at href
    subst target
    let bytes := ByteArray.mk (Nat.toBytesLE value)
    let addr := Address.blake3 bytes
    refine ⟨insertBlobState state addr bytes, ?_,
      MetaStateFrame.insertBlob state addr bytes⟩
    rfl
  | ofInt value =>
    simp only [compileDataValueRef, Option.some.injEq] at href
    subst target
    let bytes := Ix.CompileM.serializeIxInt value
    let addr := Address.blake3 bytes
    refine ⟨insertBlobState state addr bytes, ?_,
      MetaStateFrame.insertBlob state addr bytes⟩
    rfl
  | ofSyntax value =>
    simp only [compileDataValueRef, Option.some.injEq] at href
    subst target
    obtain ⟨syntaxState, hsyntaxRun, hsyntaxFrame⟩ :=
      serializeIxSyntax_run_refines compileEnv blockEnv state value
    let bytes := serializeIxSyntaxRef value
    let addr := Address.blake3 bytes
    let finalState := insertBlobState syntaxState addr bytes
    refine ⟨finalState, ?_,
      hsyntaxFrame.trans (MetaStateFrame.insertBlob syntaxState addr bytes)⟩
    rw [Ix.CompileM.compileDataValue,
      run_bind compileEnv blockEnv state _ _, hsyntaxRun]
    rfl

private theorem compileKVEntry_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    {entry : Ix.Name × Ix.DataValue} {target : Address × Ixon.DataValue}
    (href : compileKVEntryRef entry = some target) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (do
            Ix.CompileM.compileName entry.1
            let encoded ← Ix.CompileM.compileDataValue entry.2
            pure (entry.1.getHash, encoded)) = .ok (target, state') ∧
      MetaStateFrame state state' := by
  rcases entry with ⟨name, value⟩
  cases hvalue : compileDataValueRef value with
  | none => simp [compileKVEntryRef, hvalue] at href
  | some encoded =>
    have htarget : target = (name.getHash, encoded) := by
      simpa [compileKVEntryRef, hvalue] using href.symm
    subst target
    let nameState := state.compileName name
    obtain ⟨finalState, hvalueRun, hvalueFrame⟩ :=
      compileDataValue_run_refines compileEnv blockEnv nameState hvalue
    refine ⟨finalState, ?_,
      (MetaStateFrame.compileName state name).trans hvalueFrame⟩
    rw [run_bind compileEnv blockEnv state _ _, run_compileName]
    simp only
    rw [run_bind compileEnv blockEnv nameState _ _, hvalueRun]
    rfl

private theorem compileKVMap_list_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv)
    {state : Ix.CompileM.BlockState}
    {entries : List (Ix.Name × Ix.DataValue)}
    {target : List (Address × Ixon.DataValue)}
    (href : entries.mapM compileKVEntryRef = some target) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (entries.mapM fun entry => do
            Ix.CompileM.compileName entry.1
            let encoded ← Ix.CompileM.compileDataValue entry.2
            pure (entry.1.getHash, encoded)) = .ok (target, state') ∧
      MetaStateFrame state state' := by
  induction entries generalizing state target with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at href
    subst target
    exact ⟨state, rfl, MetaStateFrame.refl state⟩
  | cons entry entries ih =>
    cases hhead : compileKVEntryRef entry with
    | none => simp [List.mapM_cons, hhead] at href
    | some encoded =>
      cases htail : entries.mapM compileKVEntryRef with
      | none => simp [List.mapM_cons, hhead, htail] at href
      | some encodedTail =>
        have htarget : target = encoded :: encodedTail := by
          simpa [List.mapM_cons, hhead, htail] using href.symm
        subst target
        obtain ⟨headState, hheadRun, hheadFrame⟩ :=
          compileKVEntry_run_refines compileEnv blockEnv state hhead
        obtain ⟨finalState, htailRun, htailFrame⟩ :=
          ih htail
        refine ⟨finalState, ?_, hheadFrame.trans htailFrame⟩
        rw [List.mapM_cons,
          run_bind compileEnv blockEnv state _ _, hheadRun]
        simp only
        rw [run_bind compileEnv blockEnv headState _ _, htailRun]
        rfl

/-- Production KV-map compilation implements the total reference map
left-to-right and preserves every semantic/compiler field in the metadata
frame. -/
theorem compileKVMap_run_refines
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    {entries : Array (Ix.Name × Ix.DataValue)} {target : Ixon.KVMap}
    (href : compileKVMapRef entries = some target) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileKVMap entries) = .ok (target, state') ∧
      MetaStateFrame state state' := by
  have hrefList :
      entries.toList.mapM compileKVEntryRef = some target.toList := by
    have hmapped := congrArg (Option.map Array.toList) href
    change Array.toList <$> entries.mapM compileKVEntryRef =
      Option.map Array.toList (some target) at hmapped
    rw [Array.toList_mapM] at hmapped
    simpa [compileKVMapRef] using hmapped
  obtain ⟨state', hrun, hframe⟩ :=
    compileKVMap_list_run_refines compileEnv blockEnv hrefList
  refine ⟨state', ?_, hframe⟩
  rw [Ix.CompileM.compileKVMap, Array.mapM_eq_mapM_toList,
    map_eq_pure_bind, run_bind compileEnv blockEnv state _ _, hrun]
  rfl

end Ix.Compile.Verify
