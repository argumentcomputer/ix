module

public import Ix.Compile.WorkerContext
import all Ix.CompileM
import all Ix.Compile.WorkerContext
import IxC.Kernel.Ingress.Records
import Std.Data.HashMap.Lemmas
import Init.Data.Array.Monadic
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.SolveByElim

/-! # Reusing successful block computations

A speculative worker may have only some of the published name addresses and
no ambient blobs. A successful run is unchanged when those addresses agree
with the real snapshot and its local blob writes have no conflict there.
The complete returned value and block state are preserved. Failed runs carry
no transport guarantee and must be recomputed against the real snapshot.
-/

public section

namespace Ix.Compile.WorkerSuccess

open Ix.CompileM
open Ix.Compile.WorkerContext (run run_bind)

/-- Every successful lookup in the smaller table has the same answer. -/
def Extends {κ α : Type} [BEq κ] [Hashable κ]
    (before after : Std.HashMap κ α) : Prop :=
  ∀ key value, before.get? key = some value → after.get? key = some value

theorem Extends.refl {κ α : Type} [BEq κ] [Hashable κ] (table : Std.HashMap κ α) :
    Extends table table := fun _ _ found => found

theorem Extends.trans {κ α : Type} [BEq κ] [Hashable κ]
    {before middle after : Std.HashMap κ α} (first : Extends before middle)
    (last : Extends middle after) : Extends before after :=
  fun key value found => last key value (first key value found)

/-- Fixed configuration and exact agreement on the speculative address domain.
Absence in that domain is not an observation of a successful global lookup. -/
structure SameInputs (left right : CompileEnv) : Prop where
  env : left.env = right.env
  addresses : Extends left.nameToAddr right.nameToAddr
  sharing : left.sharingLimits = right.sharingLimits

/-- Every observed local blob is compatible with the real published table. -/
def Compatible (ambient observed : Std.HashMap Address ByteArray) : Prop :=
  ∀ address bytes, observed.get? address = some bytes → contentMatches ambient address bytes = true

theorem Compatible.of_extends {ambient before after : Std.HashMap Address ByteArray}
    (compatible : Compatible ambient after) (grows : Extends before after) : Compatible ambient before :=
  fun address bytes found => compatible address bytes (grows address bytes found)

/-- Check the speculative table's complete domain with exact value equality. -/
def checkExtension {κ α : Type} [BEq κ] [Hashable κ] [DecidableEq α]
    (before after : Std.HashMap κ α) : Bool :=
  before.toList.all fun (key, value) => decide (after.get? key = some value)

theorem checkExtension_sound {κ α : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [DecidableEq α]
    (before after : Std.HashMap κ α) (checked : checkExtension before after = true) :
    Extends before after := by
  intro key value found
  have member : (key, value) ∈ before.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr found
  exact of_decide_eq_true ((List.all_eq_true.mp checked) (key, value) member)

/-- Check exactly the local blobs whose successful writes must be replayed. -/
def checkCompatible (ambient observed : Std.HashMap Address ByteArray) : Bool :=
  observed.toList.all fun (address, bytes) => contentMatches ambient address bytes

theorem checkCompatible_sound (ambient observed : Std.HashMap Address ByteArray)
    (checked : checkCompatible ambient observed = true) : Compatible ambient observed := by
  intro address bytes found
  exact (List.all_eq_true.mp checked) (address, bytes)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr found)

/-- Successful actions preserve earlier local blobs and transport their entire
result and state across a checked worker frame. -/
structure Successful (action : CompileM α) : Prop where
  grows : ∀ env block before value after,
    run action (env, block) before = (Except.ok value, after) → Extends before.blockBlobs after.blockBlobs
  transfer : ∀ left right, SameInputs left right → ∀ block before value after,
    run action (left, block) before = (Except.ok value, after) → Compatible right.blobs after.blockBlobs →
      run action (right, block) before = (Except.ok value, after)

theorem Successful.pure (value : α) : Successful (pure value) := by
  constructor
  · intro env block before actual after success
    cases success
    exact .refl _
  · intro left right same block before actual after success compatible
    exact success

theorem Successful.throw (error : CompileError) : Successful (throw error : CompileM α) := by
  constructor
  · intro env block before value after success
    cases success
  · intro left right same block before value after success compatible
    cases success

theorem Successful.get : Successful getBlockState := by
  constructor
  · intro env block before value after success
    cases success
    exact .refl _
  · intro left right same block before value after success compatible
    exact success

theorem Successful.read : Successful getBlockEnv := by
  constructor
  · intro env block before value after success
    cases success
    exact .refl _
  · intro left right same block before value after success compatible
    exact success

theorem Successful.modify (update : BlockState → BlockState)
    (same : ∀ before, (update before).blockBlobs = before.blockBlobs) :
    Successful (modifyBlockState update) := by
  constructor
  · intro env block before value after success
    cases success
    rw [same]
    exact .refl _
  · intro left right inputs block before value after success compatible
    exact success

theorem Successful.modifyGet (update : BlockState → α × BlockState)
    (same : ∀ before, (update before).2.blockBlobs = before.blockBlobs) :
    Successful (modifyGetBlockState update) := by
  constructor
  · intro env block before value after success
    cases success
    rw [same]
    exact .refl _
  · intro left right inputs block before value after success compatible
    exact success

theorem Successful.liftSharing (result : Except CompileError Ixon.Constant) :
    Successful (liftSharing result) := by
  cases result with
  | error error => exact Successful.throw _
  | ok value => exact Successful.pure _

theorem Successful.bind {action : CompileM α} {next : α → CompileM β}
    (first : Successful action) (later : ∀ value, Successful (next value)) :
    Successful (action >>= next) := by
  have splitSuccess (env : CompileEnv) (block : BlockEnv) (before : BlockState)
      (value : β) (after : BlockState)
      (success : run (action >>= next) (env, block) before = (Except.ok value, after)) :
      ∃ first middle, run action (env, block) before = (Except.ok first, middle) ∧
        run (next first) (env, block) middle = (Except.ok value, after) := by
    rw [run_bind] at success
    cases ran : run action (env, block) before with
    | mk outcome middle =>
      rw [ran] at success
      cases outcome with
      | error error => cases success
      | ok first => exact ⟨first, middle, rfl, success⟩
  constructor
  · intro env block before value after success
    obtain ⟨value₁, middle, ran₁, ran₂⟩ := splitSuccess env block before value after success
    exact (first.grows env block before value₁ middle ran₁).trans
      ((later value₁).grows env block middle value after ran₂)
  · intro left right same block before value after success compatible
    obtain ⟨value₁, middle, ran₁, ran₂⟩ := splitSuccess left block before value after success
    have middleCompatible := compatible.of_extends ((later value₁).grows left block middle value after ran₂)
    rw [run_bind, first.transfer left right same block before value₁ middle ran₁ middleCompatible]
    exact (later value₁).transfer left right same block middle value after ran₂ compatible

theorem Successful.map (f : α → β) {action : CompileM α} (stable : Successful action) :
    Successful (f <$> action) :=
  Successful.bind stable (fun value => Successful.pure (f value))

theorem Successful.discard {action : CompileM α} (stable : Successful action) :
    Successful (discard action) := by
  change Successful ((fun _ => PUnit.unit) <$> action)
  exact Successful.map _ stable

theorem Successful.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α}
    (stable : Successful action) : Successful (withBlockEnv update action) := by
  constructor
  · intro env block before value after success
    exact stable.grows env (update block) before value after success
  · intro left right same block before value after success compatible
    exact stable.transfer left right same (update block) before value after success compatible
theorem Successful.mapM_list (items : List α) (action : α → CompileM β)
    (stable : ∀ item ∈ items, Successful (action item)) : Successful (items.mapM action) := by
  induction items with
  | nil => exact Successful.pure []
  | cons item rest ih =>
    rw [List.mapM_cons]
    apply Successful.bind (stable item (by simp))
    intro value
    apply Successful.bind (ih (fun item mem => stable item (List.mem_cons_of_mem _ mem)))
    intro values
    exact Successful.pure (value :: values)

theorem Successful.mapM_array (items : Array α) (action : α → CompileM β)
    (stable : ∀ item ∈ items, Successful (action item)) : Successful (items.mapM action) := by
  rw [Array.mapM_eq_mapM_toList]
  exact Successful.map _ (Successful.mapM_list items.toList action (fun item mem => stable item (by simpa using mem)))

theorem Successful.forIn'_list (items : List α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (stable : ∀ item mem acc, Successful (body item mem acc)) :
    Successful (forIn' items initial body) := by
  induction items generalizing initial with
  | nil => exact Successful.pure initial
  | cons item rest ih =>
    rw [List.forIn'_cons]
    apply Successful.bind (stable item (by simp) initial)
    intro result
    cases result with
    | done value => exact Successful.pure value
    | yield value => exact ih value _ (fun item mem acc => stable item _ acc)

theorem Successful.forIn'_array (items : Array α) (initial : β)
    (body : (item : α) → item ∈ items → β → CompileM (ForInStep β))
    (stable : ∀ item mem acc, Successful (body item mem acc)) :
    Successful (forIn' items initial body) := by
  have listSuccessful := Successful.forIn'_list items.toList initial
    (fun item mem acc => body item (Array.mem_toList_iff.mp mem) acc)
    (fun item mem acc => stable item _ acc)
  simpa only [Array.forIn'_toList] using listSuccessful

theorem Successful.forIn_list (items : List α) (initial : β)
    (body : α → β → CompileM (ForInStep β)) (stable : ∀ item acc, Successful (body item acc)) :
    Successful (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact Successful.pure initial
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply Successful.bind (stable item initial)
    intro result
    cases result with
    | done value => exact Successful.pure value
    | yield value => exact ih value

theorem Successful.forIn_array (items : Array α) (initial : β)
    (body : α → β → CompileM (ForInStep β)) (stable : ∀ item acc, Successful (body item acc)) :
    Successful (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact Successful.forIn_list items.toList initial body stable


/-- The only global address read has no successful absence branch. -/
theorem lookupConstAddr_success (name : Ix.Name) : Successful (lookupConstAddr name) := by
  constructor
  · intro env block before value after success
    change run (match before.blockNameToAddr.get? name with
        | some address => pure address
        | none => match env.nameToAddr.get? name with
          | some address => pure address
          | none => throw (CompileError.missingConstant s!"{name}")) (env, block) before = (Except.ok value, after) at success
    split at success
    · cases success; exact .refl _
    · split at success
      · cases success; exact .refl _
      · cases success
  · intro left right same block before value after success compatible
    change run (match before.blockNameToAddr.get? name with
        | some address => pure address
        | none => match left.nameToAddr.get? name with
          | some address => pure address
          | none => throw (CompileError.missingConstant s!"{name}")) (left, block) before = (Except.ok value, after) at success
    change run (match before.blockNameToAddr.get? name with
        | some address => pure address
        | none => match right.nameToAddr.get? name with
          | some address => pure address
          | none => throw (CompileError.missingConstant s!"{name}")) (right, block) before = (Except.ok value, after)
    split at success
    · rename_i address found
      exact success
    · rename_i absent
      split at success
      · rename_i address found
        rw [same.addresses name address found]
        exact success
      · cases success

theorem findConst_success (name : Ix.Name) : Successful (findConst name) := by
  constructor
  · intro env block before value after success
    change run (match env.env.get? name with
      | some value => pure value
      | none => throw (CompileError.missingConstant s!"{name}")) (env, block) before = (Except.ok value, after) at success
    split at success
    · cases success; exact .refl _
    · cases success
  · intro left right same block before value after success compatible
    change run (match left.env.get? name with
        | some constant => pure constant
        | none => throw (CompileError.missingConstant s!"{name}")) (left, block) before =
      (Except.ok value, after) at success
    change run (match right.env.get? name with
        | some constant => pure constant
        | none => throw (CompileError.missingConstant s!"{name}")) (right, block) before =
      (Except.ok value, after)
    rw [same.env] at success
    cases found : right.env.get? name <;> simp only [found] at success ⊢ <;> exact success

/-- Exact checked writes keep prior local payloads and can be replayed when
the resulting local table is compatible with a different ambient table. -/
theorem storeBlob_checked (before : BlockState) (ambient : Std.HashMap Address ByteArray)
    (address : Address) (bytes : ByteArray) {after : BlockState}
    (success : before.storeBlob ambient address bytes = .ok after) :
    Extends before.blockBlobs after.blockBlobs ∧
      ∀ actual, Compatible actual after.blockBlobs → before.storeBlob actual address bytes = .ok after := by
  unfold BlockState.storeBlob at success
  split at success
  · rename_i checked
    have checks := Bool.and_eq_true_iff.mp checked
    cases Except.ok.inj success
    constructor
    · intro query old found
      by_cases same : address = query
      · subst query
        have equal : old = bytes := by
          have localCheck := checks.1
          change (match before.blockBlobs.get? address with
            | none => true | some prior => decide (prior = bytes)) = true at localCheck
          simpa only [found, decide_eq_true_eq] using localCheck
        subst old
        simp
      · change (before.blockBlobs.insert address bytes)[query]? = some old
        simpa only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          beq_iff_eq, same, ↓reduceIte] using found
    · intro actual compatible
      have same := compatible address bytes (by simp)
      simp only [BlockState.storeBlob, checks.1, same, Bool.true_and, ↓reduceIte]
  · cases success

theorem compileName_checked (before : BlockState) (ambient : Std.HashMap Address ByteArray)
    (name : Ix.Name) : ∀ after, before.compileName ambient name = .ok after →
    Extends before.blockBlobs after.blockBlobs ∧
      ∀ actual, Compatible actual after.blockBlobs → before.compileName actual name = .ok after := by
  induction name generalizing before with
  | anonymous hash =>
    rw [BlockState.compileName]
    split <;> intro after success <;> cases Except.ok.inj success
    all_goals refine ⟨.refl _, ?_⟩
    all_goals intro actual compatible; rw [BlockState.compileName]; simp_all
  | str parent text hash ih =>
    rw [BlockState.compileName]
    dsimp only
    split
    · intro after success
      cases Except.ok.inj success
      refine ⟨.refl _, ?_⟩
      intro actual compatible
      rw [BlockState.compileName]
      simp only [‹before.blockNames.contains _ = true›, ↓reduceIte]
    · intro after success
      let named := { before with blockNames := before.blockNames.insert (Ix.Name.str parent text hash).getHash (.str parent text hash) }
      change (named.storeBlob ambient (Address.admissionHash text.toUTF8) text.toUTF8 >>=
        fun current => current.compileName ambient parent) = .ok after at success
      cases wrote : named.storeBlob ambient (Address.admissionHash text.toUTF8) text.toUTF8 with
      | error error => simp only [wrote, bind, Except.bind] at success; cases success
      | ok middle =>
        simp only [wrote, bind, Except.bind] at success
        have first := storeBlob_checked named ambient _ _ wrote
        have last := ih middle after success
        refine ⟨first.1.trans last.1, ?_⟩
        intro actual compatible
        rw [BlockState.compileName]
        simp only [‹¬before.blockNames.contains _ = true›]
        change (named.storeBlob actual (Address.admissionHash text.toUTF8) text.toUTF8 >>=
          fun current => current.compileName actual parent) = .ok after
        rw [first.2 actual (compatible.of_extends last.1)]
        exact last.2 actual compatible
  | num parent index hash ih =>
    rw [BlockState.compileName]
    dsimp only
    split
    · intro after success
      cases Except.ok.inj success
      refine ⟨.refl _, ?_⟩
      intro actual compatible
      rw [BlockState.compileName]
      simp only [‹before.blockNames.contains _ = true›, ↓reduceIte]
    · intro after success
      have last := ih
        { before with blockNames := before.blockNames.insert (Ix.Name.num parent index hash).getHash (.num parent index hash) }
        after success
      refine ⟨last.1, ?_⟩
      intro actual compatible
      rw [BlockState.compileName]
      simp only [‹¬before.blockNames.contains _ = true›]
      exact last.2 actual compatible

theorem compileNames_checked (before : BlockState) (ambient : Std.HashMap Address ByteArray)
    (names : Array Ix.Name) : ∀ after, before.compileNames ambient names = .ok after →
    Extends before.blockBlobs after.blockBlobs ∧
      ∀ actual, Compatible actual after.blockBlobs → before.compileNames actual names = .ok after := by
  unfold BlockState.compileNames
  simp only [← Array.foldlM_toList]
  induction names.toList generalizing before with
  | nil =>
    intro after success
    cases Except.ok.inj success
    exact ⟨.refl _, fun _ _ => rfl⟩
  | cons name names ih =>
    simp only [List.foldlM_cons]
    intro after success
    cases ran : before.compileName ambient name with
    | error error => simp only [ran, bind, Except.bind] at success; cases success
    | ok middle =>
      simp only [ran, bind, Except.bind] at success
      have first := compileName_checked before ambient name middle ran
      have last := ih middle after success
      refine ⟨first.1.trans last.1, ?_⟩
      intro actual compatible
      rw [first.2 actual (compatible.of_extends last.1)]
      exact last.2 actual compatible

theorem Successful.checkedUpdate (action : CompileM α) (value : α)
    (update : CompileEnv → BlockState → Except CompileError BlockState)
    (meaning : ∀ env block before, run action (env, block) before =
      match update env before with
      | .ok after => (Except.ok value, after)
      | .error error => (Except.error error, before))
    (checked : ∀ left before after, update left before = .ok after →
      Extends before.blockBlobs after.blockBlobs ∧
        ∀ right, SameInputs left right → Compatible right.blobs after.blockBlobs →
          update right before = .ok after) : Successful action := by
  constructor
  · intro env block before actual after success
    rw [meaning] at success
    cases ran : update env before with
    | error error => simp only [ran] at success; cases success
    | ok final =>
      simp only [ran] at success
      cases success
      exact (checked env before _ ran).1
  · intro left right same block before actual after success compatible
    rw [meaning] at success ⊢
    cases ran : update left before with
    | error error => simp only [ran] at success; cases success
    | ok final =>
      simp only [ran] at success
      cases success
      rw [(checked left before _ ran).2 right same compatible]

theorem storeBlob_success (bytes : ByteArray) : Successful (storeBlob bytes) := by
  apply Successful.checkedUpdate _ (Address.admissionHash bytes)
    (fun env before => before.storeBlob env.blobs (Address.admissionHash bytes) bytes)
  · intro env block before
    change run (applyBlockState (before.storeBlob env.blobs (Address.admissionHash bytes) bytes) >>=
      fun _ => pure (Address.admissionHash bytes)) (env, block) before = _
    cases before.storeBlob env.blobs (Address.admissionHash bytes) bytes <;> rfl
  · intro left before after success
    have checked := storeBlob_checked before left.blobs _ _ success
    exact ⟨checked.1, fun right _ compatible => checked.2 right.blobs compatible⟩

theorem compileName_success (name : Ix.Name) : Successful (compileName name) := by
  apply Successful.checkedUpdate _ () (fun env before => before.compileName env.blobs name)
  · intro env block before
    change run (applyBlockState (before.compileName env.blobs name)) (env, block) before = _
    cases before.compileName env.blobs name <;> rfl
  · intro left before after success
    have checked := compileName_checked before left.blobs name after success
    exact ⟨checked.1, fun right _ compatible => checked.2 right.blobs compatible⟩

theorem compileNames_success (names : Array Ix.Name) : Successful (compileNames names) := by
  apply Successful.checkedUpdate _ () (fun env before => before.compileNames env.blobs names)
  · intro env block before
    change run (applyBlockState (before.compileNames env.blobs names)) (env, block) before = _
    cases before.compileNames env.blobs names <;> rfl
  · intro left before after success
    have checked := compileNames_checked before left.blobs names after success
    exact ⟨checked.1, fun right _ compatible => checked.2 right.blobs compatible⟩

theorem buildBlockConstant_success (info : Ixon.ConstantInfo) (refs : Array Address)
    (univs : Array Ixon.Univ) : Successful (buildBlockConstant info refs univs) := by
  constructor
  · intro env block before value after success
    change run (liftSharing (buildConstantWithSharing env.sharingLimits info refs univs))
      (env, block) before = _ at success
    exact (Successful.liftSharing _).grows env block before value after success
  · intro left right same block before value after success compatible
    change run (liftSharing (buildConstantWithSharing left.sharingLimits info refs univs))
      (left, block) before = _ at success
    change run (liftSharing (buildConstantWithSharing right.sharingLimits info refs univs))
      (right, block) before = _
    rw [same.sharing] at success
    exact (Successful.liftSharing _).transfer left right same block before value after success compatible

theorem internRef_blobs (before : BlockState) (address : Address) :
    (before.internRef address).1.blockBlobs = before.blockBlobs := by
  unfold BlockState.internRef
  split <;> rfl

theorem internUniv_blobs (before : BlockState) (value : Ixon.Univ) :
    (before.internUniv value).1.blockBlobs = before.blockBlobs := by
  unfold BlockState.internUniv
  split <;> rfl

theorem internMetaUniv_blobs (before : BlockState) (value : Ixon.Univ) :
    (before.internMetaUniv value).1.blockBlobs = before.blockBlobs := by
  unfold BlockState.internMetaUniv
  split <;> rfl

scoped macro "successful_step" : tactic => `(tactic|
  first
    | assumption
    | exact Successful.pure _
    | exact Successful.throw _
    | exact Successful.get
    | exact Successful.read
    | exact Successful.modify _ (by intro before; first | rfl | simp only [BlockState.cacheUniv])
    | exact Successful.modifyGet _ (by intro before; first | rfl | exact internRef_blobs _ _ | exact internUniv_blobs _ _ | exact internMetaUniv_blobs _ _)
    | exact Successful.liftSharing _
    | exact lookupConstAddr_success _
    | exact findConst_success _
    | exact storeBlob_success _
    | exact compileName_success _
    | exact compileNames_success _
    | exact buildBlockConstant_success _ _ _
    | apply Successful.discard
    | refine Successful.bind ?_ (fun _ => ?_)
    | refine Successful.mapM_array _ _ (fun _ _ => ?_)
    | refine Successful.forIn'_array _ _ _ (fun _ _ _ => ?_)
    | refine Successful.forIn_array _ _ _ (fun _ _ => ?_)
    | apply Successful.withBlockEnv
    | unfold checkedTableIndex
    | unfold checkedTableCount
    | dsimp only
    | split)

scoped macro "successful_steps" : tactic => `(tactic| with_reducible repeat' successful_step)

theorem compileUniv_success (source : Ix.Level) : Successful (compileUniv source) := by
  induction source <;> rw [compileUniv]
  all_goals successful_steps

theorem internUniv_success (value : Ixon.Univ) : Successful (internUniv value) := by
  unfold internUniv
  successful_steps

theorem canonUnivCached_success (value : Ixon.Univ) : Successful (canonUnivCached value) := by
  unfold canonUnivCached
  successful_steps

theorem internMetaUniv_success (value : Ixon.Univ) : Successful (internMetaUniv value) := by
  unfold internMetaUniv
  successful_steps

theorem compileAndInternUnivCanon_success (source : Ix.Level) :
    Successful (compileAndInternUnivCanon source) := by
  unfold compileAndInternUnivCanon
  with_reducible repeat' first
    | exact compileUniv_success _
    | exact canonUnivCached_success _
    | exact internUniv_success _
    | exact internMetaUniv_success _
    | successful_step

theorem internRef_success (address : Address) : Successful (internRef address) := by
  unfold internRef
  successful_steps

theorem allocArenaNode_success (node : Ixon.ExprMetaData) : Successful (allocArenaNode node) := by
  unfold allocArenaNode
  successful_steps

theorem takeArena_success : Successful takeArena := by
  unfold takeArena
  successful_steps

theorem resetArena_success : Successful resetArena := by
  unfold resetArena
  successful_steps

theorem clearExprCache_success : Successful clearExprCache := by
  unfold clearExprCache
  successful_steps

theorem pushUnivPatch_success (arenaIdx : UInt64) (univIdxs : Array UInt64) :
    Successful (pushUnivPatch arenaIdx univIdxs) := by
  unfold pushUnivPatch
  successful_steps

theorem takeUnivPatches_success : Successful takeUnivPatches := by
  unfold takeUnivPatches
  successful_steps

theorem recordDefHints_success (name : Ix.Name) (hints : Lean.ReducibilityHints) :
    Successful (recordDefHints name hints) := by
  unfold recordDefHints
  successful_steps

theorem Successful.withUnivCtx (params : List Ix.Name) {action : CompileM α}
    (stable : Successful action) : Successful (Ix.CompileM.withUnivCtx params action) := by
  unfold Ix.CompileM.withUnivCtx
  exact Successful.bind (Successful.modify _ (by intro before; rfl)) (fun _ => stable.withBlockEnv _)

scoped macro "core_step" : tactic => `(tactic|
  first
    | exact compileUniv_success _
    | exact internUniv_success _
    | exact canonUnivCached_success _
    | exact internMetaUniv_success _
    | exact compileAndInternUnivCanon_success _
    | exact internRef_success _
    | exact allocArenaNode_success _
    | exact takeArena_success
    | exact resetArena_success
    | exact clearExprCache_success
    | exact pushUnivPatch_success _ _
    | exact takeUnivPatches_success
    | exact recordDefHints_success _ _
    | apply Successful.withUnivCtx
    | successful_step)

scoped macro "core_steps" : tactic => `(tactic| with_reducible repeat' core_step)

theorem storeString_success (value : String) : Successful (storeString value) :=
  storeBlob_success _

theorem serializeIxSubstring_success (value : Ix.Substring) : Successful (serializeIxSubstring value) := by
  unfold serializeIxSubstring
  exact Successful.bind (storeString_success _) (fun _ => Successful.pure _)

theorem serializeIxSourceInfo_success (value : Ix.SourceInfo) : Successful (serializeIxSourceInfo value) := by
  cases value <;> unfold serializeIxSourceInfo
  all_goals with_reducible repeat' first
    | exact serializeIxSubstring_success _
    | core_step

theorem serializeIxSyntaxPreresolved_success (value : Ix.SyntaxPreresolved) :
    Successful (serializeIxSyntaxPreresolved value) := by
  cases value <;> unfold serializeIxSyntaxPreresolved
  all_goals with_reducible repeat' first
    | exact storeString_success _
    | core_step

theorem serializeIxSyntax_success (source : Ix.Syntax) : Successful (serializeIxSyntax source) := by
  induction source using (measure (fun value : Ix.Syntax => sizeOf value)).wf.induction with
  | h source ih =>
    cases source <;> rw [serializeIxSyntax]
    all_goals with_reducible repeat' first
      | exact serializeIxSourceInfo_success _
      | exact serializeIxSubstring_success _
      | exact serializeIxSyntaxPreresolved_success _
      | exact storeString_success _
      | core_step
    apply ih
    rename_i arg member
    exact Nat.lt_trans (Array.sizeOf_lt_of_mem arg.property) (by simp; omega)

theorem compileDataValue_success (value : Ix.DataValue) : Successful (compileDataValue value) := by
  cases value <;> unfold compileDataValue
  all_goals with_reducible repeat' first
    | exact serializeIxSyntax_success _
    | core_step

theorem compileKVMap_success (values : Array (Ix.Name × Ix.DataValue)) : Successful (compileKVMap values) := by
  unfold compileKVMap
  with_reducible repeat' first
    | exact compileDataValue_success _
    | core_step

theorem compileExprStep_success (source : Ix.Expr)
    (compile : (child : Ix.Expr) → sizeOf child < sizeOf source → CompileM (Ixon.Expr × UInt64))
    (stable : ∀ child smaller, Successful (compile child smaller)) :
    Successful (compileExprStep source compile) := by
  cases source
  case' lit literal hash => cases literal
  all_goals unfold compileExprStep
  all_goals with_reducible repeat' first
    | exact stable _ _
    | exact compileKVMap_success _
    | core_step

theorem compileExpr_success (source : Ix.Expr) : Successful (compileExpr source) := by
  induction source using (measure (fun value : Ix.Expr => sizeOf value)).wf.induction with
  | h source ih =>
    rw [compileExpr]
    core_steps
    exact compileExprStep_success source (fun child _ => compileExpr child)
      (fun child smaller => ih child smaller)

theorem collectExprTableUnivs_success (sources : List Ix.Level) (initial : Array Ixon.Univ) :
    Successful (collectExprTableUnivs sources initial) := by
  induction sources generalizing initial with
  | nil => exact Successful.pure _
  | cons source rest ih =>
    rw [collectExprTableUnivs]
    exact Successful.bind (compileUniv_success source) (fun value => ih (initial.push value))

theorem collectExprTablesStructural_success (key : Address) (mutCtx : Ix.MutCtx)
    (params : List Ix.Name) (source : Ix.Expr) (initial : ExprTableCollection) :
    Successful (collectExprTablesStructural key mutCtx params source initial) := by
  obtain ⟨refs, univs, seen⟩ := initial
  induction source generalizing refs univs seen
  case' lit literal hash => cases literal
  all_goals rw [collectExprTablesStructural]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact collectExprTableUnivs_success _ _
    | core_step

theorem collectExprTables_success (source : Ix.Expr) (key : Address) (initial : ExprTableCollection) :
    Successful (collectExprTables source key initial) := by
  unfold collectExprTables
  with_reducible repeat' first
    | exact collectExprTablesStructural_success _ _ _ _ _
    | core_step

theorem collectPreseedExprs_success (sources : List (Ix.Expr × List Ix.Name))
    (initial : ExprTableCollection) : Successful (collectPreseedExprs sources initial) := by
  induction sources generalizing initial with
  | nil => exact Successful.pure _
  | cons source rest ih =>
    obtain ⟨expr, params⟩ := source
    rw [collectPreseedExprs]
    exact Successful.bind ((collectExprTables_success _ _ _).withUnivCtx params) (fun result => ih result)

theorem internPreseedRefs_success (refs : List Address) (previous : Option Address) :
    Successful (internPreseedRefs refs previous) := by
  induction refs generalizing previous <;> rw [internPreseedRefs]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | core_step

theorem canonPreseedUnivs_success (univs : List Ixon.Univ) (initial : Array Ixon.Univ) :
    Successful (canonPreseedUnivs univs initial) := by
  induction univs generalizing initial <;> rw [canonPreseedUnivs]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | core_step

theorem internPreseedUnivs_success (univs : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    Successful (internPreseedUnivs univs previous) := by
  induction univs generalizing previous with
  | nil => exact Successful.pure _
  | cons entry rest ih =>
    obtain ⟨key, univ⟩ := entry
    rw [internPreseedUnivs]
    with_reducible repeat' first
      | exact ih _
      | core_step

theorem preseedExprTables_success (sources : Array (Ix.Expr × List Ix.Name)) :
    Successful (preseedExprTables sources) := by
  unfold preseedExprTables
  with_reducible repeat' first
    | exact collectPreseedExprs_success _ _
    | exact internPreseedRefs_success _ _
    | exact canonPreseedUnivs_success _ _
    | exact internPreseedUnivs_success _ _
    | unfold checkPreseedUnivs
    | core_step

theorem internalIndexError_success (what : String) (index size : Nat) :
    Successful (internalIndexError (α := α) what index size) := by
  unfold internalIndexError
  core_steps

theorem arrIdx_success (values : Array α) (index : Nat) (what : String) :
    Successful (arrIdx values index what) := by
  unfold arrIdx
  with_reducible repeat' first
    | exact internalIndexError_success _ _ _
    | core_step

theorem getMutCtxAddrs_success : Successful getMutCtxAddrs := by
  unfold getMutCtxAddrs
  core_steps

scoped macro "declaration_step" : tactic => `(tactic|
  first
    | exact compileExpr_success _
    | exact preseedExprTables_success _
    | exact internalIndexError_success _ _ _
    | exact arrIdx_success _ _ _
    | exact getMutCtxAddrs_success
    | unfold withCurrent
    | unfold withMutCtx
    | unfold withAll
    | core_step)

scoped macro "declaration_steps" : tactic => `(tactic| with_reducible repeat' declaration_step)

theorem finishDefinitionDataCompilation_success (value : Ix.Def)
    (typ : Ixon.Expr) (tyRoot : UInt64) (body : Ixon.Expr) (bodyRoot : UInt64) :
    Successful (finishDefinitionDataCompilation value typ tyRoot body bodyRoot) := by
  unfold finishDefinitionDataCompilation
  declaration_steps

theorem finishAxiomCompilation_success (value : Ix.AxiomVal) (typ : Ixon.Expr) (root : UInt64) :
    Successful (finishAxiomCompilation value typ root) := by
  unfold finishAxiomCompilation
  declaration_steps

theorem finishQuotientCompilation_success (value : Ix.QuotVal) (typ : Ixon.Expr) (root : UInt64) :
    Successful (finishQuotientCompilation value typ root) := by
  unfold finishQuotientCompilation
  declaration_steps

theorem finishConstructorCompilation_success (value : Ix.ConstructorVal) (typ : Ixon.Expr) (root : UInt64) :
    Successful (finishConstructorCompilation value typ root) := by
  unfold finishConstructorCompilation
  declaration_steps

theorem finishRecursorCompilation_success (value : Ix.RecursorVal) (typ : Ixon.Expr) (root : UInt64)
    (rules : RecursorRuleCompileState) : Successful (finishRecursorCompilation value typ root rules) := by
  unfold finishRecursorCompilation
  declaration_steps

theorem finishInductiveCompilation_success (value : Ix.InductiveVal) (typ : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (ctors : InductiveConstructorCompileState) :
    Successful (finishInductiveCompilation value typ root metadata ctors) := by
  unfold finishInductiveCompilation
  declaration_steps

theorem finishInductiveDataCompilation_success (value : Ix.Ind) (typ : Ixon.Expr) (root : UInt64)
    (metadata : InductiveTypeCompileMeta) (ctors : InductiveConstructorCompileState) :
    Successful (finishInductiveDataCompilation value typ root metadata ctors) := by
  unfold finishInductiveDataCompilation
  declaration_steps

theorem takeInductiveTypeCompileMeta_success : Successful takeInductiveTypeCompileMeta := by
  unfold takeInductiveTypeCompileMeta
  declaration_steps

theorem compileRecursorRule_success (value : Ix.RecursorRule) : Successful (compileRecursorRule value) := by
  unfold compileRecursorRule
  declaration_steps

theorem compileRecursorRules_success (values : List Ix.RecursorRule) (initial : RecursorRuleCompileState) :
    Successful (compileRecursorRules values initial) := by
  induction values generalizing initial <;> rw [compileRecursorRules]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact compileRecursorRule_success _
    | declaration_step

scoped macro "finish_step" : tactic => `(tactic|
  first
    | exact finishDefinitionDataCompilation_success _ _ _ _ _
    | exact finishAxiomCompilation_success _ _ _
    | exact finishQuotientCompilation_success _ _ _
    | exact finishConstructorCompilation_success _ _ _
    | exact finishRecursorCompilation_success _ _ _ _
    | exact finishInductiveCompilation_success _ _ _ _ _
    | exact finishInductiveDataCompilation_success _ _ _ _ _
    | exact takeInductiveTypeCompileMeta_success
    | exact compileRecursorRules_success _ _
    | unfold finishDefinitionCompilation
    | unfold finishTheoremCompilation
    | unfold finishOpaqueCompilation
    | declaration_step)

scoped macro "finish_steps" : tactic => `(tactic| with_reducible repeat' finish_step)

theorem compileDefinition_success (value : Ix.DefinitionVal) : Successful (compileDefinition value) := by
  unfold compileDefinition
  finish_steps

theorem compileDefinitionData_success (value : Ix.Def) : Successful (compileDefinitionData value) := by
  unfold compileDefinitionData
  finish_steps

theorem compileAxiom_success (value : Ix.AxiomVal) : Successful (compileAxiom value) := by
  unfold compileAxiom
  finish_steps

theorem compileQuotient_success (value : Ix.QuotVal) : Successful (compileQuotient value) := by
  unfold compileQuotient
  finish_steps

theorem compileConstructor_success (value : Ix.ConstructorVal) : Successful (compileConstructor value) := by
  unfold compileConstructor
  finish_steps

theorem compileRecursor_success (value : Ix.RecursorVal) : Successful (compileRecursor value) := by
  unfold compileRecursor
  finish_steps

theorem compileInductiveConstructors_success (values : List Ix.ConstructorVal)
    (initial : InductiveConstructorCompileState) : Successful (compileInductiveConstructors values initial) := by
  induction values generalizing initial <;> rw [compileInductiveConstructors]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact compileConstructor_success _
    | finish_step

theorem compileInductive_success (value : Ix.InductiveVal) (ctors : Array Ix.ConstructorVal) :
    Successful (compileInductive value ctors) := by
  unfold compileInductive
  with_reducible repeat' first
    | exact compileInductiveConstructors_success _ _
    | finish_step

theorem compileInductiveData_success (value : Ix.Ind) : Successful (compileInductiveData value) := by
  unfold compileInductiveData
  with_reducible repeat' first
    | exact compileInductiveConstructors_success _ _
    | finish_step

theorem collectInductiveConstructors_success (names : List Ix.Name) (initial : Array Ix.ConstructorVal) :
    Successful (collectInductiveConstructors names initial) := by
  induction names generalizing initial <;> rw [collectInductiveConstructors]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | finish_step

theorem collectMutConstConstructors_success (names : List Ix.Name) (initial : Array Ix.ConstructorVal) :
    Successful (collectMutConstConstructors names initial) := by
  induction names generalizing initial <;> rw [collectMutConstConstructors]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | finish_step

theorem mkIndc_success (value : Ix.InductiveVal) : Successful (Ix.CompileM.MutConst.mkIndc value) := by
  unfold Ix.CompileM.MutConst.mkIndc
  exact Successful.bind (collectMutConstConstructors_success _ _) (fun _ => Successful.pure _)

theorem finishConstantWithSharing_success (info : Ixon.ConstantInfo) (metadata : Ixon.ConstantMeta) :
    Successful (finishConstantWithSharing info metadata) := by
  unfold finishConstantWithSharing
  finish_steps

theorem finishInductiveFamilyBlock_success (value : Ix.InductiveVal) (payload : Ixon.Inductive)
    (metadata : Ixon.ConstantMeta) (ctors : Array (Ix.Name × Ixon.ConstantMeta)) :
    Successful (finishInductiveFamilyBlock value payload metadata ctors) := by
  unfold finishInductiveFamilyBlock
  finish_steps

theorem compileInductiveInfo_success (value : Ix.InductiveVal) : Successful (compileInductiveInfo value) := by
  unfold compileInductiveInfo lookupInductiveConstructors compileInductiveFamilyInfo compileInductiveFamilyBlock
  with_reducible repeat' first
    | exact collectInductiveConstructors_success _ _
    | exact compileInductive_success _ _
    | exact finishInductiveFamilyBlock_success _ _ _ _
    | finish_step

theorem compileConstructorInfo_success (value : Ix.ConstructorVal) : Successful (compileConstructorInfo value) := by
  unfold compileConstructorInfo
  with_reducible repeat' first
    | exact compileInductiveInfo_success _
    | finish_step

theorem compileConstantInfo_success (value : Ix.ConstantInfo) : Successful (compileConstantInfo value) := by
  cases value <;>
    simp only [compileConstantInfo, compileConstantInfoCore, compileDefinitionConstantInfo,
      compileTheoremConstantInfo, compileOpaqueConstantInfo, compileQuotientConstantInfo,
      compileRecursorConstantInfo, compileInductiveConstantInfo, compileConstructorConstantInfo,
      compileDefinitionInfo, compileDefinitionBlock, compileTheoremInfo, compileOpaqueInfo,
      compileDefinitionDataInfo, compileDefinitionDataBlock, compileAxiomInfo, compileAxiomBlock,
      compileQuotientInfo, compileQuotientBlock, compileRecursorInfo, compileRecursorBlock,
      finishConstantInfoWithSharing]
  all_goals with_reducible repeat' first
    | exact compileDefinition_success _
    | exact compileDefinitionData_success _
    | exact compileAxiom_success _
    | exact compileQuotient_success _
    | exact compileRecursor_success _
    | exact compileInductiveInfo_success _
    | exact compileConstructorInfo_success _
    | exact finishConstantWithSharing_success _ _
    | finish_step

theorem compileMutConstMember_success (value : Ix.MutConst) : Successful (compileMutConstMember value) := by
  cases value <;> unfold compileMutConstMember
  all_goals with_reducible repeat' first
    | exact compileDefinitionData_success _
    | exact compileInductiveData_success _
    | exact compileRecursor_success _
    | unfold compileRecursorData
    | finish_step

theorem compileMutConstMembers_success (values : List Ix.MutConst) (initial : MutConstCompileState) :
    Successful (compileMutConstMembers values initial) := by
  induction values generalizing initial <;> rw [compileMutConstMembers]
  all_goals with_reducible repeat' first
    | solve_by_elim only [*]
    | exact compileMutConstMember_success _
    | finish_step

theorem compileMutConsts_success (values : List Ix.MutConst) : Successful (compileMutConsts values) := by
  unfold compileMutConsts
  exact Successful.bind (compileMutConstMembers_success _ _) (fun _ => Successful.pure _)

theorem checkMutConstArrayCounts_success (value : Ixon.MutConst) : Successful (checkMutConstArrayCounts value) := by
  cases value <;> unfold checkMutConstArrayCounts
  all_goals finish_steps

theorem checkMutualPayloadCounts_success (values : Array Ixon.MutConst) : Successful (checkMutualPayloadCounts values) := by
  unfold checkMutualPayloadCounts
  with_reducible repeat' first
    | exact checkMutConstArrayCounts_success _
    | finish_step

theorem finishMutualCompilation_success (sources : List Ix.MutConst)
    (payloads : Array Ixon.MutConst) (metas : Array (Ix.Name × Ixon.ConstantMeta)) :
    Successful (finishMutualCompilation sources payloads metas) := by
  unfold finishMutualCompilation
  apply Successful.bind (checkMutualPayloadCounts_success _)
  intro _
  apply Successful.bind Successful.get
  intro cache
  constructor
  · intro env block before value after success
    change run (match buildCompiledMutualBlock env.sharingLimits sources payloads metas cache with
        | .ok result => pure result
        | .error error => throw error) (env, block) before = _ at success
    cases ran : buildCompiledMutualBlock env.sharingLimits sources payloads metas cache with
    | error error => simp only [ran] at success; cases success
    | ok result =>
      simp only [ran] at success
      cases success
      exact .refl _
  · intro left right same block before value after success compatible
    change run (match buildCompiledMutualBlock left.sharingLimits sources payloads metas cache with
        | .ok result => pure result
        | .error error => throw error) (left, block) before = _ at success
    change run (match buildCompiledMutualBlock right.sharingLimits sources payloads metas cache with
        | .ok result => pure result
        | .error error => throw error) (right, block) before = _
    rw [same.sharing] at success
    cases ran : buildCompiledMutualBlock right.sharingLimits sources payloads metas cache <;>
      simp only [ran] at success ⊢ <;> exact success

theorem compileMutualBlock_success (sources : List Ix.MutConst) : Successful (compileMutualBlock sources) := by
  unfold compileMutualBlock compileMutualPayload
  with_reducible repeat' first
    | exact compileMutConsts_success _
    | exact finishMutualCompilation_success _ _ _
    | finish_step

end Ix.Compile.WorkerSuccess
