import Ix.Compile.Verify.CompileState

/-!
# Scalar expression-metadata refinement

This module relates production `DataValue` and `KVMap` compilation to a
small total reference compiler.  Recursive syntax metadata is deliberately
excluded for now: production `serializeIxSyntax` is partial, so admitting it
would hide the remaining totalization boundary.
-/

namespace Ix.Compile.Verify

/-- Pure wire encoding for metadata values whose production serialization is
already total.  `Syntax` is the one deliberately unsupported case. -/
def compileDataValueRef : Ix.DataValue → Option Ixon.DataValue
  | .ofString value => some (.ofString (Address.blake3 value.toUTF8))
  | .ofBool value => some (.ofBool value)
  | .ofName value => some (.ofName value.getHash)
  | .ofNat value => some
      (.ofNat (Address.blake3 (ByteArray.mk (Nat.toBytesLE value))))
  | .ofInt value => some
      (.ofInt (Address.blake3 (Ix.CompileM.serializeIxInt value)))
  | .ofSyntax _ => none

private def compileKVEntryRef
    (entry : Ix.Name × Ix.DataValue) : Option (Address × Ixon.DataValue) :=
  match entry with
  | (name, value) => do
    let encoded ← compileDataValueRef value
    pure (name.getHash, encoded)

/-- Pure scalar reference compiler for an expression metadata map. -/
def compileKVMapRef (entries : Array (Ix.Name × Ix.DataValue)) :
    Option Ixon.KVMap :=
  entries.mapM compileKVEntryRef

/-- Source metadata is supported exactly when every value has a total scalar
wire encoding. -/
def KVMapSupported (entries : Array (Ix.Name × Ix.DataValue)) : Prop :=
  ∃ encoded, compileKVMapRef entries = some encoded

theorem KVMapSupported.empty : KVMapSupported #[] := by
  exact ⟨#[], by simp [compileKVMapRef]⟩

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

private theorem run_compileName (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (name : Ix.Name) :
    Ix.CompileM.CompileM.run compileEnv blockEnv state
        (Ix.CompileM.compileName name) =
      .ok ((), state.compileName name) := by
  rfl

/-- Production scalar metadata compilation returns exactly the reference
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
    simp [compileDataValueRef] at href

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

/-- Production KV-map compilation implements the total scalar reference map
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
