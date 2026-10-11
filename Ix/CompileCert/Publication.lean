import Ix.CompileDriver
import Ix.CompileCert.Canon.Loop
import Ix.CompileCert.Canon.Refs

/-!
# Anonymous block publication

The anonymous projection of the production driver's block merge. Record and
blob addresses are keys; these results assume no injectivity of a digest.
Presentation metadata and compiler caches are outside this projection.

Content compatibility is a separate obligation from `checkBlockClaims`, which
checks source-name and Pass 3 claims. The production `checkCompiledBlock` checks
both; the final results below connect its success to anonymous preservation.
-/

namespace Ix.CompileCert.Publication

open Ix.CompileM

abbrev Store := Std.HashMap Address ByteArray
abbrev Writes := List (Address × ByteArray)

/-- Every previously stored payload is still available at its old key. -/
def Extends (before after : Store) : Prop :=
  ∀ (key : Address) (bytes : ByteArray), before[key]? = some bytes → after[key]? = some bytes

theorem Extends.refl (store : Store) : Extends store store := fun _ _ h => h

theorem Extends.trans {a b c : Store} (ab : Extends a b) (bc : Extends b c) :
    Extends a c := fun key bytes h => bc key bytes (ab key bytes h)

/-- Reusing an old address must retain its exact payload. -/
def Compatible (before : Store) (writes : Writes) : Prop :=
  ∀ key bytes, (key, bytes) ∈ writes →
    ∀ old, before[key]? = some old → old = bytes

/-- All writes at any one address agree, including writes within a unit. -/
def Consistent (writes : Writes) : Prop :=
  ∀ key left right, (key, left) ∈ writes → (key, right) ∈ writes → left = right

def applyWrites (before : Store) (writes : Writes) : Store :=
  writes.foldl (fun store row => store.insert row.1 row.2) before

theorem insert_extends {before : Store} {key : Address} {bytes : ByteArray}
    (agree : ∀ old, before[key]? = some old → old = bytes) :
    Extends before (before.insert key bytes) := by
  intro other old found
  rw [Std.HashMap.getElem?_insert]
  by_cases same : key = other
  · subst other
    simp only [beq_self_eq_true, ↓reduceIte]
    exact congrArg some (agree old found).symm
  · simp only [beq_iff_eq, same, ↓reduceIte, found]

theorem applyWrites_preserves {before : Store} {writes : Writes}
    (agree : Compatible before writes) : Extends before (applyWrites before writes) := by
  intro key bytes found
  unfold applyWrites
  have keep : ∀ (rest : Writes) (store : Store),
      store[key]? = some bytes →
      (∀ row ∈ rest, row.1 = key → row.2 = bytes) →
      (rest.foldl (fun store row => store.insert row.1 row.2) store)[key]? = some bytes := by
    intro rest
    induction rest with
    | nil => intro store present _; exact present
    | cons row rest ih =>
      intro store present same
      apply ih
      · rw [Std.HashMap.getElem?_insert]
        by_cases eq : row.1 = key
        · simp only [beq_iff_eq, eq, ↓reduceIte]
          exact congrArg some (same row (by simp) eq)
        · simp only [beq_iff_eq, eq, ↓reduceIte, present]
      · intro other mem
        exact same other (List.mem_cons_of_mem _ mem)
  apply keep writes before found
  rintro ⟨other, payload⟩ mem same
  simp only at same
  subst other
  exact (agree key payload mem bytes found).symm

/-- Exact record-write order of `mergeCompiledBlock`: primary block,
member/constructor projections, then auxiliary records. -/
def recordWrites (result : BlockResult) (cache : BlockState) : Writes :=
  (result.blockAddr, result.blockBytes) ::
    (result.projections.toList.map fun (_, projection, _) =>
      (Address.blake3 (Ixon.ser projection), Ixon.ser projection)) ++
    (cache.auxConsts.toList.map fun (address, constant) => (address, Ixon.ser constant))

def blobWrites (cache : BlockState) : Writes := cache.blockBlobs.toList

structure AnonymousStore where
  constants : Store
  blobs : Store

def anonymous (env : CompileEnv) : AnonymousStore := ⟨env.constants, env.blobs⟩

def publish (before : AnonymousStore) (result : BlockResult) (cache : BlockState) :
    AnonymousStore :=
  ⟨applyWrites before.constants (recordWrites result cache),
   applyWrites before.blobs (blobWrites cache)⟩

/-- A loop's observable projection follows the projected step. -/
theorem forIn_project {α β γ : Type} (xs : Array α) (initial : β)
    (body : α → β → Id (ForInStep β)) (project : β → γ) (next : γ → α → γ)
    (continues : ∀ item state, body item state = .yield (body item state).value)
    (commute : ∀ item state, project (body item state).value = next (project state) item) :
    project (forIn (m := Id) xs initial body) =
      xs.foldl next (project initial) := by
  rw [Ix.CompileCert.Canon.forIn_id_array _ continues]
  exact (Array.foldl_hom project (fun state item => (commute item state).symm)).symm

theorem forIn_preserves {α β γ : Type} (xs : Array α) (initial : β)
    (body : α → β → Id (ForInStep β)) (project : β → γ)
    (continues : ∀ item state, body item state = .yield (body item state).value)
    (unchanged : ∀ item state, project (body item state).value = project state) :
    project (forIn (m := Id) xs initial body) =
      project initial := by
  rw [forIn_project xs initial body project (fun state _ => state) continues unchanged]
  rw [← Array.foldl_toList]
  have fold_id : ∀ items : List α,
      items.foldl (fun state _ => state) (project initial) = project initial := by
    intro items
    induction items with
    | nil => rfl
    | cons _ _ ih => exact ih
  exact fold_id _

private theorem forIn_constants_preserves {α : Type} (xs : Array α) (initial : CompileEnv)
    (body : α → CompileEnv → Id (ForInStep CompileEnv))
    (continues : ∀ item state, body item state = .yield (body item state).value)
    (unchanged : ∀ item state, (body item state).value.constants = state.constants) :
    (forIn (m := Id) xs initial body).constants =
      initial.constants :=
  forIn_preserves xs initial body CompileEnv.constants continues unchanged

private theorem forIn_blobs_preserves {α : Type} (xs : Array α) (initial : CompileEnv)
    (body : α → CompileEnv → Id (ForInStep CompileEnv))
    (continues : ∀ item state, body item state = .yield (body item state).value)
    (unchanged : ∀ item state, (body item state).value.blobs = state.blobs) :
    (forIn (m := Id) xs initial body).blobs =
      initial.blobs :=
  forIn_preserves xs initial body CompileEnv.blobs continues unchanged

private theorem named_constants (xs : Array (Ix.Name × Ixon.Named)) (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun row state =>
      .yield { state with nameToNamed := state.nameToNamed.insert row.1 row.2 })).constants =
      initial.constants := by
  apply forIn_constants_preserves <;> intro item state <;> rfl

private theorem class_constants (xs : Array Ix.Name) (classes : Array (Array Ix.Name))
    (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun name state =>
      .yield { state with blocks := state.blocks.insert name classes })).constants =
      initial.constants := by
  apply forIn_constants_preserves <;> intro item state <;> rfl

private theorem classes_constants (classes : Array (Array Ix.Name)) (initial : CompileEnv) :
    (forIn (m := Id) classes initial (fun names state =>
      .yield (forIn (m := Id) names state (fun name state =>
        .yield { state with blocks := state.blocks.insert name classes })))).constants =
      initial.constants := by
  apply forIn_constants_preserves
  · intro item state; rfl
  · intro item state
    exact class_constants item classes state

private theorem aux_constants (xs : Array (Address × Ixon.Constant)) (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun row state =>
      .yield { state with constants := state.constants.insert row.1 (Ixon.ser row.2) })).constants =
      applyWrites initial.constants (xs.toList.map fun (address, constant) => (address, Ixon.ser constant)) := by
  rw [forIn_project xs initial _ CompileEnv.constants
    (fun store row => store.insert row.1 (Ixon.ser row.2)) (fun _ _ => rfl) (fun _ _ => rfl)]
  simp only [applyWrites, List.foldl_map, Array.foldl_toList]

private theorem projection_constants (xs : Array (Ix.Name × Ixon.Constant × Ixon.ConstantMeta))
    (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun row state =>
      let bytes := Ixon.ser row.2.1
      let address := Address.blake3 bytes
      .yield { state with
        totalBytes := state.totalBytes + bytes.size
        constants := state.constants.insert address bytes
        nameToNamed := state.nameToNamed.insert row.1 { addr := address, constMeta := row.2.2 }
        nameToAddr := state.nameToAddr.insert row.1 address })).constants =
      applyWrites initial.constants (xs.toList.map fun (_, projection, _) =>
        (Address.blake3 (Ixon.ser projection), Ixon.ser projection)) := by
  rw [forIn_project xs initial _ CompileEnv.constants
    (fun store row => store.insert (Address.blake3 (Ixon.ser row.2.1)) (Ixon.ser row.2.1))
    (fun _ _ => rfl) (fun _ _ => rfl)]
  simp only [applyWrites, List.foldl_map, Array.foldl_toList]

set_option maxRecDepth 2048 in
theorem merge_constants (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState) :
    (mergeCompiledBlock acc lo result cache).cenv.constants =
      applyWrites acc.cenv.constants (recordWrites result cache) := by
  unfold mergeCompiledBlock
  simp only [Id.run, bind, pure]
  split <;> split <;> split
  all_goals simp only [classes_constants, named_constants, aux_constants, projection_constants]
  all_goals simp_all only [Array.isEmpty_iff, applyWrites, recordWrites, List.foldl_cons,
    List.foldl_append, List.foldl_map, Array.toList_empty, List.map_nil, List.foldl_nil]

private theorem named_blobs (xs : Array (Ix.Name × Ixon.Named)) (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun row state =>
      .yield { state with nameToNamed := state.nameToNamed.insert row.1 row.2 })).blobs =
      initial.blobs := by
  apply forIn_blobs_preserves <;> intro item state <;> rfl

private theorem class_blobs (xs : Array Ix.Name) (classes : Array (Array Ix.Name))
    (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun name state =>
      .yield { state with blocks := state.blocks.insert name classes })).blobs =
      initial.blobs := by
  apply forIn_blobs_preserves <;> intro item state <;> rfl

private theorem classes_blobs (classes : Array (Array Ix.Name)) (initial : CompileEnv) :
    (forIn (m := Id) classes initial (fun names state =>
      .yield (forIn (m := Id) names state (fun name state =>
        .yield { state with blocks := state.blocks.insert name classes })))).blobs =
      initial.blobs := by
  apply forIn_blobs_preserves
  · intro item state; rfl
  · intro item state
    exact class_blobs item classes state

private theorem aux_blobs (xs : Array (Address × Ixon.Constant)) (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun row state =>
      .yield { state with constants := state.constants.insert row.1 (Ixon.ser row.2) })).blobs =
      initial.blobs := by
  apply forIn_blobs_preserves <;> intro item state <;> rfl

private theorem projection_blobs (xs : Array (Ix.Name × Ixon.Constant × Ixon.ConstantMeta))
    (initial : CompileEnv) :
    (forIn (m := Id) xs initial (fun row state =>
      let bytes := Ixon.ser row.2.1
      let address := Address.blake3 bytes
      .yield { state with
        totalBytes := state.totalBytes + bytes.size
        constants := state.constants.insert address bytes
        nameToNamed := state.nameToNamed.insert row.1 { addr := address, constMeta := row.2.2 }
        nameToAddr := state.nameToAddr.insert row.1 address })).blobs =
      initial.blobs := by
  apply forIn_blobs_preserves <;> intro item state <;> rfl

set_option maxRecDepth 2048 in
theorem merge_blobs (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState) :
    (mergeCompiledBlock acc lo result cache).cenv.blobs =
      applyWrites acc.cenv.blobs (blobWrites cache) := by
  unfold mergeCompiledBlock
  simp only [Id.run, bind, pure]
  split <;> split <;> split
  all_goals simp only [classes_blobs, named_blobs, aux_blobs, projection_blobs,
    Std.HashMap.fold_eq_foldl_toList, applyWrites, blobWrites]

/-- The actual merge's anonymous effect, with all presentation/cache fields
left arbitrary. No source-name or hash-injectivity premise is used. -/
theorem merge_anonymous (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState) :
    anonymous (mergeCompiledBlock acc lo result cache).cenv =
      publish (anonymous acc.cenv) result cache := by
  simp only [anonymous, publish, merge_constants, merge_blobs]

/-- Compatible block writes preserve the complete previous anonymous store.
The compatibility hypotheses still need checking or a production discharger. -/
theorem merge_extends (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (records : Compatible acc.cenv.constants (recordWrites result cache))
    (blobs : Compatible acc.cenv.blobs (blobWrites cache)) :
    Extends acc.cenv.constants (mergeCompiledBlock acc lo result cache).cenv.constants ∧
      Extends acc.cenv.blobs (mergeCompiledBlock acc lo result cache).cenv.blobs := by
  rw [merge_constants, merge_blobs]
  exact ⟨applyWrites_preserves records, applyWrites_preserves blobs⟩

/-- Equal anonymous inputs and write sets give equal anonymous publication,
regardless of metadata, scheduling counters and other cache fields. -/
theorem merge_anonymous_congr
    (left right : DriverAcc) (leftName rightName : Ix.Name)
    (leftResult rightResult : BlockResult) (leftCache rightCache : BlockState)
    (initial : anonymous left.cenv = anonymous right.cenv)
    (records : recordWrites leftResult leftCache = recordWrites rightResult rightCache)
    (blobs : blobWrites leftCache = blobWrites rightCache) :
    anonymous (mergeCompiledBlock left leftName leftResult leftCache).cenv =
      anonymous (mergeCompiledBlock right rightName rightResult rightCache).cenv := by
  rw [merge_anonymous, merge_anonymous, initial]
  simp only [publish, records, blobs]

def checkWrite (store : Store) (key : Address) (bytes : ByteArray) : Bool :=
  match store[key]? with
  | none => true
  | some old => decide (old = bytes)

/-- Validate both existing-store reuse and repeated writes within this unit. -/
def checkWrites (store : Store) : Writes → Bool
  | [] => true
  | (key, bytes) :: rest =>
    checkWrite store key bytes && checkWrites (store.insert key bytes) rest

theorem checkWrite_sound {store : Store} {key : Address} {bytes : ByteArray}
    (accepted : checkWrite store key bytes = true) :
    ∀ old, store[key]? = some old → old = bytes := by
  intro old found
  simpa only [checkWrite, found, decide_eq_true_eq] using accepted

theorem checkWrite_complete {store : Store} {key : Address} {bytes : ByteArray}
    (agree : ∀ old, store[key]? = some old → old = bytes) :
    checkWrite store key bytes = true := by
  cases found : store[key]? with
  | none => simp only [checkWrite, found]
  | some old => simp only [checkWrite, found, agree old found, decide_true]

/-- Every accepted write is present, and every old payload is preserved. -/
theorem checkWrites_sound {store : Store} {writes : Writes}
    (accepted : checkWrites store writes = true) :
    Extends store (applyWrites store writes) ∧
      ∀ key bytes, (key, bytes) ∈ writes → (applyWrites store writes)[key]? = some bytes := by
  induction writes generalizing store with
  | nil =>
    exact ⟨Extends.refl _, fun _ _ mem => False.elim (List.not_mem_nil mem)⟩
  | cons row rest ih =>
    rcases row with ⟨key, bytes⟩
    simp only [checkWrites, Bool.and_eq_true] at accepted
    obtain ⟨extended, present⟩ := ih accepted.2
    change Extends store (applyWrites (store.insert key bytes) rest) ∧ _
    refine ⟨(insert_extends (checkWrite_sound accepted.1)).trans extended, ?_⟩
    intro requested payload mem
    rcases List.mem_cons.mp mem with same | later
    · cases same
      exact extended key bytes Std.HashMap.getElem?_insert_self
    · exact present requested payload later

theorem checkWrites_compatible {store : Store} {writes : Writes}
    (accepted : checkWrites store writes = true) : Compatible store writes := by
  obtain ⟨extended, present⟩ := checkWrites_sound accepted
  intro key bytes mem old found
  exact Option.some.inj ((extended key old found).symm.trans (present key bytes mem))

theorem checkWrites_consistent {store : Store} {writes : Writes}
    (accepted : checkWrites store writes = true) : Consistent writes := by
  have present := (checkWrites_sound accepted).2
  intro key left right hleft hright
  exact Option.some.inj ((present key left hleft).symm.trans (present key right hright))

/-- The check admits fresh writes and identical aliases: it does not demand
fresh addresses or a collision-free hash function. -/
theorem checkWrites_complete {store : Store} {writes : Writes}
    (compatible : Compatible store writes) (consistent : Consistent writes) :
    checkWrites store writes = true := by
  induction writes generalizing store with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨key, bytes⟩
    simp only [checkWrites, Bool.and_eq_true]
    refine ⟨checkWrite_complete (compatible key bytes (by simp)), ih ?_ ?_⟩
    · intro other payload mem old found
      rw [Std.HashMap.getElem?_insert] at found
      by_cases same : key = other
      · subst other
        simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at found
        exact found.symm.trans (consistent key bytes payload (by simp)
          (List.mem_cons_of_mem _ mem))
      · simp only [beq_iff_eq, same, ↓reduceIte] at found
        exact compatible other payload (List.mem_cons_of_mem _ mem) old found
    · intro other left right hleft hright
      exact consistent other left right
        (List.mem_cons_of_mem _ hleft) (List.mem_cons_of_mem _ hright)

theorem checkWrites_iff (store : Store) (writes : Writes) :
    checkWrites store writes = true ↔ Compatible store writes ∧ Consistent writes :=
  ⟨fun h => ⟨checkWrites_compatible h, checkWrites_consistent h⟩,
   fun h => checkWrites_complete h.1 h.2⟩

/-- This check concerns only anonymous publication, not source meaning,
dependency closure, name claims, or target-kernel admission. -/
def checkPublication (acc : DriverAcc) (result : BlockResult) (cache : BlockState) : Bool :=
  checkWrites acc.cenv.constants (recordWrites result cache) &&
    checkWrites acc.cenv.blobs (blobWrites cache)

theorem checkPublication_extends (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkPublication acc result cache = true) :
    Extends acc.cenv.constants (mergeCompiledBlock acc lo result cache).cenv.constants ∧
      Extends acc.cenv.blobs (mergeCompiledBlock acc lo result cache).cenv.blobs := by
  simp only [checkPublication, Bool.and_eq_true] at accepted
  exact merge_extends acc lo result cache
    (checkWrites_compatible accepted.1) (checkWrites_compatible accepted.2)

/-- Every accepted local payload is present in the actual merged driver. -/
theorem checkPublication_present (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkPublication acc result cache = true) :
    (∀ key bytes, (key, bytes) ∈ recordWrites result cache →
      (mergeCompiledBlock acc lo result cache).cenv.constants[key]? = some bytes) ∧
    (∀ key bytes, (key, bytes) ∈ blobWrites cache →
      (mergeCompiledBlock acc lo result cache).cenv.blobs[key]? = some bytes) := by
  simp only [checkPublication, Bool.and_eq_true] at accepted
  rw [merge_constants, merge_blobs]
  exact ⟨(checkWrites_sound accepted.1).2, (checkWrites_sound accepted.2).2⟩

theorem checkPublication_iff (acc : DriverAcc) (result : BlockResult) (cache : BlockState) :
    checkPublication acc result cache = true ↔
      (Compatible acc.cenv.constants (recordWrites result cache) ∧
        Consistent (recordWrites result cache)) ∧
      (Compatible acc.cenv.blobs (blobWrites cache) ∧ Consistent (blobWrites cache)) := by
  simp only [checkPublication, Bool.and_eq_true, checkWrites_iff]

theorem checkContentWrites_eq (store : Store) (writes : Writes) :
    checkContentWrites store writes = checkWrites store writes := by
  induction writes generalizing store with
  | nil => rfl
  | cons row rest ih =>
    rcases row with ⟨key, bytes⟩
    simp only [checkContentWrites, checkWrites, ih]
    rfl

/-- The efficient production check has exactly the reference check's domain.
It only inserts into a fresh per-unit map, never the prior environment. -/
theorem checkAnonymousWrites_iff (store : Store) (writes : Writes) :
    checkAnonymousWrites store writes = true ↔
      Compatible store writes ∧ Consistent writes := by
  simp only [checkAnonymousWrites, Bool.and_eq_true, checkContentWrites_eq, checkWrites_iff]
  constructor
  · rintro ⟨againstOld, _, consistent⟩
    refine ⟨?_, consistent⟩
    intro key bytes mem
    exact checkWrite_sound (List.all_eq_true.mp againstOld (key, bytes) mem)
  · rintro ⟨compatible, consistent⟩
    refine ⟨?_, ?_, consistent⟩
    · apply List.all_eq_true.mpr
      rintro ⟨key, bytes⟩ mem
      exact checkWrite_complete (compatible key bytes mem)
    · intro key bytes _ old found
      simp at found

theorem checkAnonymousWrites_eq (store : Store) (writes : Writes) :
    checkAnonymousWrites store writes = checkWrites store writes := by
  apply Bool.eq_iff_iff.mpr
  exact (checkAnonymousWrites_iff store writes).trans (checkWrites_iff store writes).symm

theorem checkBlockContent_iff (acc : DriverAcc) (result : BlockResult) (cache : BlockState) :
    checkBlockContent acc.cenv result cache = .ok () ↔
      checkPublication acc result cache = true := by
  change (if checkAnonymousWrites acc.cenv.constants (recordWrites result cache) then
      if checkAnonymousWrites acc.cenv.blobs (blobWrites cache) then (Except.ok () : Except CompileError Unit)
      else .error (.invalidMutualBlock "anonymous publication: conflicting blob payload")
    else .error (.invalidMutualBlock "anonymous publication: conflicting constant payload")) =
      .ok () ↔ _
  rw [checkAnonymousWrites_eq, checkAnonymousWrites_eq]
  cases records : checkWrites acc.cenv.constants (recordWrites result cache) <;>
    cases blobs : checkWrites acc.cenv.blobs (blobWrites cache) <;>
      simp [checkPublication, records, blobs]

theorem checkCompiledBlock_publication (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock acc.cenv lo result cache = .ok ()) :
    checkPublication acc result cache = true := by
  apply (checkBlockContent_iff acc result cache).mp
  cases claims : checkBlockClaims acc.cenv (primaryClaims lo result) cache with
  | error e => simp [checkCompiledBlock, claims, bind, Except.bind] at accepted
  | ok u => simpa [checkCompiledBlock, claims, bind, Except.bind] using accepted

/-- The guard used by every aux-aware driver merge preserves the entire
anonymous prefix. This is a publication result, not source correctness. -/
theorem checkCompiledBlock_extends (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock acc.cenv lo result cache = .ok ()) :
    Extends acc.cenv.constants (mergeCompiledBlock acc lo result cache).cenv.constants ∧
      Extends acc.cenv.blobs (mergeCompiledBlock acc lo result cache).cenv.blobs :=
  checkPublication_extends acc lo result cache
    (checkCompiledBlock_publication acc lo result cache accepted)

theorem checkCompiledBlock_present (acc : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock acc.cenv lo result cache = .ok ()) :
    (∀ key bytes, (key, bytes) ∈ recordWrites result cache →
      (mergeCompiledBlock acc lo result cache).cenv.constants[key]? = some bytes) ∧
    (∀ key bytes, (key, bytes) ∈ blobWrites cache →
      (mergeCompiledBlock acc lo result cache).cenv.blobs[key]? = some bytes) :=
  checkPublication_present acc lo result cache
    (checkCompiledBlock_publication acc lo result cache accepted)

end Ix.CompileCert.Publication
