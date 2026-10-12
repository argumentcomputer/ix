import Ix.CompileCert.SourceFamilyTraversal

/-! Frame facts for the actual compiler monad. Name serialization and display
side-car updates preserve the head-claim accumulator, including error states.
The publication proofs use these facts before appending authenticated claims. -/

namespace Ix.CompileCert.HeadWriterFrame

open Ix (Name)
open Ix.CompileM Ix.Compile.Pass

def rawRun (action : CompileM α) (context : CompileEnv × BlockEnv) (state : BlockState) :
    Except CompileError α × BlockState := (action context).run state

theorem rawRun_bind (action : CompileM α) (next : α → CompileM β)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (action >>= next) context state =
      match rawRun action context state with
      | (.ok value, after) => rawRun (next value) context after
      | (.error error, after) => (.error error, after) := by
  rcases result : (action context).run state with ⟨outcome, after⟩
  change action context state = (outcome, after) at result
  cases outcome <;>
    simp [rawRun, ExceptT.run, ExceptT.mk, bind, ReaderT.bind, ExceptT.bind, StateT.bind,
      ExceptT.bindCont, pure, StateT.pure, result]

def Frame (action : CompileM α) : Prop :=
  ∀ context state, (rawRun action context state).2.p3Heads = state.p3Heads

theorem rawRun_pure (value : α) (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (pure value) context state = (.ok value, state) := rfl

theorem rawRun_read (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getCompileEnv context state = (.ok context.1, state) := rfl

theorem rawRun_get (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun getBlockState context state = (.ok state, state) := rfl

theorem rawRun_modify (update : BlockState → BlockState)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (modifyBlockState update) context state = (.ok (), update state) := rfl

theorem Frame.pure (value : α) : Frame (pure value) := by intro _ _; rfl

theorem Frame.bind {action : CompileM α} {next : α → CompileM β}
    (first : Frame action) (later : ∀ value, Frame (next value)) : Frame (action >>= next) := by
  intro context state
  rw [rawRun_bind]
  have prior := first context state
  cases ran : rawRun action context state with
  | mk outcome after =>
    rw [ran] at prior
    cases outcome with
    | error error => exact prior
    | ok value => exact (later value context after).trans prior

theorem Frame.read : Frame getCompileEnv := by intro _ _; rfl
theorem Frame.readBlock : Frame getBlockEnv := by intro _ _; rfl
theorem Frame.get : Frame getBlockState := by intro _ _; rfl
theorem Frame.throw (error : CompileError) : Frame (throw error : CompileM α) := by
  intro _ _
  rfl
theorem Frame.modify (update : BlockState → BlockState)
    (keeps : ∀ state, (update state).p3Heads = state.p3Heads) :
    Frame (modifyBlockState update) := by intro context state; exact keeps state

theorem Frame.modifyGet (update : BlockState → α × BlockState)
    (keeps : ∀ state, (update state).2.p3Heads = state.p3Heads) :
    Frame (modifyGetBlockState update) := by intro context state; exact keeps state

theorem Frame.map {action : CompileM α} (framed : Frame action) (f : α → β) :
    Frame (f <$> action) := Frame.bind framed (fun _ => Frame.pure _)

theorem frame_mapM_list (items : List α) (action : α → CompileM β)
    (keeps : ∀ item ∈ items, Frame (action item)) : Frame (items.mapM action) := by
  induction items with
  | nil => exact Frame.pure []
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply Frame.bind (keeps item (by simp))
    intro _
    apply Frame.bind (ih (fun item mem => keeps item (List.mem_cons_of_mem _ mem)))
    intro _
    exact Frame.pure _

theorem frame_mapM_array (items : Array α) (action : α → CompileM β)
    (keeps : ∀ item ∈ items, Frame (action item)) : Frame (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Frame.map (frame_mapM_list _ action (fun item mem => keeps item (by simpa using mem))) _

theorem frame_forIn'_list (items : List α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (keeps : ∀ item mem acc, Frame (body item mem acc)) :
    Frame (forIn' items initial body) := by
  induction items generalizing initial with
  | nil => exact Frame.pure initial
  | cons item rest ih =>
    rw [List.forIn'_cons]
    apply Frame.bind (keeps item (by simp) initial)
    intro result
    cases result with
    | done value => exact Frame.pure value
    | yield value => exact ih value _ (fun item mem acc => keeps item _ acc)

theorem frame_forIn'_array (items : Array α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (keeps : ∀ item mem acc, Frame (body item mem acc)) :
    Frame (forIn' items initial body) := by
  have listFrame := frame_forIn'_list items.toList initial
    (fun item mem acc => body item (Array.mem_toList_iff.mp mem) acc)
    (fun item mem acc => keeps item _ acc)
  simpa only [Array.forIn'_toList] using listFrame

theorem frame_forIn_list (items : List α) (initial : β)
    (body : α → β → CompileM (ForInStep β)) (keeps : ∀ item acc, Frame (body item acc)) :
    Frame (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact Frame.pure initial
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Frame.bind (keeps item initial)
    intro result
    cases result with
    | done value => exact Frame.pure value
    | yield value => exact ih value

theorem frame_forIn_array (items : Array α) (initial : β)
    (body : α → β → CompileM (ForInStep β)) (keeps : ∀ item acc, Frame (body item acc)) :
    Frame (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact frame_forIn_list items.toList initial body keeps

theorem storeBlob_heads (state : BlockState) (ambient : Std.HashMap Address ByteArray)
    (address : Address) (bytes : ByteArray) {after : BlockState}
    (success : state.storeBlob ambient address bytes = .ok after) : after.p3Heads = state.p3Heads := by
  unfold BlockState.storeBlob at success
  split at success
  · cases Except.ok.inj success; rfl
  · cases success

theorem compileName_heads (state : BlockState) (ambient : Std.HashMap Address ByteArray) (name : Name) :
    ∀ after, state.compileName ambient name = .ok after → after.p3Heads = state.p3Heads := by
  induction name generalizing state with
  | anonymous hash =>
    rw [BlockState.compileName]
    split <;> (intro after success; cases Except.ok.inj success; rfl)
  | str parent text hash ih =>
    rw [BlockState.compileName]
    dsimp only
    split
    · intro after success; cases Except.ok.inj success; rfl
    · intro after success
      cases wrote : (BlockState.storeBlob
          { state with blockNames := state.blockNames.insert (Name.str parent text hash).getHash (.str parent text hash) }
          ambient (Address.blake3 text.toUTF8) text.toUTF8) with
      | error error => simp only [wrote, bind, Except.bind] at success; cases success
      | ok middle =>
        simp only [wrote, bind, Except.bind] at success
        have kept := storeBlob_heads
          { state with blockNames := state.blockNames.insert (Name.str parent text hash).getHash (.str parent text hash) }
          ambient _ _ wrote
        exact (ih middle after success).trans kept
  | num parent index hash ih =>
    rw [BlockState.compileName]
    dsimp only
    split
    · intro after success; cases Except.ok.inj success; rfl
    · exact ih _

theorem rawRun_applyBlockState (result : Except CompileError BlockState)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (applyBlockState result) context before = match result with
      | .error error => (.error error, before)
      | .ok after => (.ok (), after) := by cases result <;> rfl

theorem Frame.compileName (name : Name) : Frame (compileName name) := by
  intro context state
  simp only [Ix.CompileM.compileName, rawRun_bind, rawRun_get, rawRun_read, rawRun_applyBlockState]
  cases ran : state.compileName context.1.blobs name with
  | error error => rfl
  | ok after => exact compileName_heads state context.1.blobs name after ran

theorem Frame.storeBlob (bytes : ByteArray) : Frame (storeBlob bytes) := by
  intro context state
  simp only [Ix.CompileM.storeBlob, rawRun_bind, rawRun_get, rawRun_read, rawRun_applyBlockState]
  cases ran : state.storeBlob context.1.blobs (Address.blake3 bytes) bytes with
  | error error => rfl
  | ok after => exact storeBlob_heads state context.1.blobs _ bytes ran

theorem Frame.moveToDisplay (all : Array Name) (representative : Name)
    (perm : Array (Option Nat)) (select : Name → Bool) :
    Frame (_root_.Ix.Compile.Pass.moveToDisplay all representative perm select) := by
  unfold Ix.Compile.Pass.moveToDisplay
  apply Frame.bind Frame.get
  intro state
  apply Frame.bind
  · apply frame_forIn_array
    intro name display
    repeat' first | exact Frame.pure _ | dsimp only | split
  · intro display
    dsimp only
    apply Frame.bind
    · rw [Std.HashMap.forIn_eq_forIn_toList]
      apply frame_forIn_list
      rintro ⟨_, target⟩ _
      apply Frame.bind (Frame.compileName target)
      intro _
      exact Frame.pure _
    · intro _
      apply Frame.bind
      · apply Frame.modify
        intro _
        rfl
      · intro _
        exact Frame.pure _

theorem run_eq_rawRun (action : CompileM α) (cenv : CompileEnv) (benv : BlockEnv) (state : BlockState) :
    CompileM.run cenv benv state action =
      match rawRun action (cenv, benv) state with
      | (.ok value, after) => .ok (value, after)
      | (.error error, _) => .error error := rfl

theorem Frame.run_heads {action : CompileM α} (framed : Frame action)
    {cenv : CompileEnv} {benv : BlockEnv} {before after : BlockState} {value : α}
    (success : CompileM.run cenv benv before action = .ok (value, after)) :
    after.p3Heads = before.p3Heads := by
  rw [run_eq_rawRun] at success
  have stable := framed (cenv, benv) before
  cases ran : rawRun action (cenv, benv) before with
  | mk outcome final =>
    rw [ran] at success stable
    cases outcome <;> try contradiction
    cases Except.ok.inj success
    exact stable

theorem run_success {action : CompileM α} {cenv : CompileEnv} {benv : BlockEnv}
    {before after : BlockState} {value : α}
    (success : CompileM.run cenv benv before action = .ok (value, after)) :
    rawRun action (cenv, benv) before = (.ok value, after) := by
  rw [run_eq_rawRun] at success
  cases ran : rawRun action (cenv, benv) before with
  | mk outcome final =>
    rw [ran] at success
    cases outcome <;> try contradiction
    cases Except.ok.inj success
    rfl

end Ix.CompileCert.HeadWriterFrame
