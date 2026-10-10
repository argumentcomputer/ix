import Ix.CompileCert.Publication

/-!
# Primary source-reference publication

The actual name-claim guard implies compatibility with prior direct bindings
and consistency among all primary claims, using the map's real lookup
equivalence rather than raw-name equality or a hash-injectivity assumption.
The actual merge preserves those bindings and publishes every primary address
together with its anonymous payload. The new binding is never assumed present
before publication.

These are operational lookup results. Auxiliary-only bindings, serialized Named
entries, unit ownership, scheduling and source meaning need their own
construction invariants; a provisional auxiliary may still be withdrawn by
failed promotion. This module does not claim the full compiler unit theorem.
-/

namespace Ix.CompileCert.ReferencePublication

open Ix.CompileM Ix.CompileCert.Publication

abbrev References := Std.HashMap Ix.Name Address
abbrev Claims := List (Ix.Name × Address)

def applyClaims (before : References) (claims : Claims) : References :=
  claims.foldl (fun names row => names.insert row.1 row.2) before

def CompatibleClaims (before : References) (claims : Claims) : Prop :=
  ∀ name address, (name, address) ∈ claims →
    ∀ old, before[name]? = some old → old = address

def ReferencesExtend (before after : References) : Prop :=
  ∀ (name : Ix.Name) (address : Address), before[name]? = some address → after[name]? = some address

def ClaimsConsistent (claims : Claims) : Prop :=
  ∀ left ∈ claims, ∀ right ∈ claims, (left.1 == right.1) = true → left.2 = right.2

theorem applyClaims_keeps (claims : Claims) (before : References) (name : Ix.Name) (address : Address)
    (found : before[name]? = some address)
    (agree : ∀ row ∈ claims, (row.1 == name) = true → row.2 = address) :
    (applyClaims before claims)[name]? = some address := by
  induction claims generalizing before with
  | nil => exact found
  | cons row rest ih =>
    apply ih
    · rw [Std.HashMap.getElem?_insert]
      by_cases equal : (row.1 == name) = true
      · simp only [equal, ↓reduceIte]
        exact congrArg some (agree row (by simp) equal)
      · simp [equal, found]
    · intro other mem
      exact agree other (List.mem_cons_of_mem _ mem)

theorem applyClaims_present (claims : Claims) (before : References)
    (consistent : ClaimsConsistent claims) :
    ∀ name address, (name, address) ∈ claims → (applyClaims before claims)[name]? = some address := by
  induction claims generalizing before with
  | nil => intro name address mem; cases mem
  | cons row rest ih =>
    intro name address mem
    rcases List.mem_cons.mp mem with same | later
    · subst row
      apply applyClaims_keeps rest (before.insert name address) name address
      · simp
      · intro other member equal
        exact consistent other (List.mem_cons_of_mem _ member) (name, address) (by simp) equal
    · apply ih _ (fun left hl right hr =>
        consistent left (List.mem_cons_of_mem _ hl) right (List.mem_cons_of_mem _ hr)) name address later

/-- Observe the real hash-map lookup equivalence. This does not identify raw
names or assume collision freedom of their cached hashes. -/
theorem applyClaims_preserves {before : References} {claims : Claims}
    (compatible : CompatibleClaims before claims) : ReferencesExtend before (applyClaims before claims) := by
  intro name address found
  apply applyClaims_keeps claims before name address found
  rintro ⟨other, payload⟩ mem same
  have prior : before[other]? = some address :=
    (Std.HashMap.getElem?_congr (m := before) same).trans found
  exact (compatible other payload mem address prior).symm

def SeenAgrees (before seen : References) : Prop :=
  ∀ (name : Ix.Name) (address : Address), seen[name]? = some address →
    ∀ old, before[name]? = some old → old = address

theorem seen_or_prior {before seen : References} (agrees : SeenAgrees before seen)
    {name : Ix.Name} {old : Address} (found : before[name]? = some old) :
    (seen[name]?).orElse (fun _ => before[name]?) = some old := by
  cases present : seen[name]? with
  | none => simp [found]
  | some address => simp [agrees name address present old found]

theorem seen_insert {before seen : References} (agrees : SeenAgrees before seen)
    {name : Ix.Name} {address : Address}
    (compatible : ∀ old, before[name]? = some old → old = address) :
    SeenAgrees before (seen.insert name address) := by
  intro other payload present old found
  rw [Std.HashMap.getElem?_insert] at present
  by_cases same : (name == other) = true
  · simp only [same, ↓reduceIte, Option.some.injEq] at present
    subst payload
    exact compatible old ((Std.HashMap.getElem?_congr (m := before) same).trans found)
  · simp [same] at present
    exact agrees other payload present old found

/-- The first loop of `checkBlockClaims`. The guard theorems below extract this
exact computation from production by definitional equality. -/
def primaryBody (cenv : CompileEnv) (row : Ix.Name × Address) (seen : References) :
    Except CompileError (ForInStep References) := do
  let (name, address) := row
  if let some existing := cenv.auxNameToAddr.get? name then
    if existing != address then throw (nameClaimConflict name existing address)
  if let some existing := (seen.get? name).orElse (fun _ => cenv.nameToAddr.get? name) then
    if existing != address then throw (nameClaimConflict name existing address)
  pure (.yield (seen.insert name address))

theorem primaryBody_result {cenv : CompileEnv} {row : Ix.Name × Address} {seen : References}
    {step : ForInStep References} (accepted : primaryBody cenv row seen = .ok step) :
    step = .yield (seen.insert row.1 row.2) := by
  unfold primaryBody at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals rfl

theorem primaryBody_selected {cenv : CompileEnv} {row : Ix.Name × Address} {seen : References}
    {step : ForInStep References} (accepted : primaryBody cenv row seen = .ok step)
    {old : Address}
    (selected : (seen[row.1]?).orElse (fun _ => cenv.nameToAddr[row.1]?) = some old) :
    old = row.2 := by
  rcases row with ⟨name, address⟩
  by_contra different
  unfold primaryBody at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe] at accepted
  change (seen.get? name).orElse (fun _ => cenv.nameToAddr.get? name) = some old at selected
  rw [selected] at accepted
  simp only [bne_iff_ne] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals simp_all [MonadExceptOf.throw]

theorem primaryBody_compatible {cenv : CompileEnv} {row : Ix.Name × Address} {seen : References}
    (agrees : SeenAgrees cenv.nameToAddr seen) {step : ForInStep References}
    (accepted : primaryBody cenv row seen = .ok step) :
    ∀ old, cenv.nameToAddr[row.1]? = some old → old = row.2 :=
  fun _ found => primaryBody_selected accepted (seen_or_prior agrees found)

theorem primaryBody_extends_seen {cenv : CompileEnv} {row : Ix.Name × Address} {seen : References}
    {step : ForInStep References} (accepted : primaryBody cenv row seen = .ok step) :
    ReferencesExtend seen (seen.insert row.1 row.2) := by
  apply applyClaims_preserves (claims := [row])
  intro name address mem old found
  have same := List.mem_singleton.mp mem
  subst row
  exact primaryBody_selected accepted (by simp [found])

theorem checkBlockClaims_consistent (cenv : CompileEnv) (primary : Array (Ix.Name × Address))
    (cache : BlockState) (accepted : checkBlockClaims cenv primary cache = .ok ()) :
    ClaimsConsistent primary.toList := by
  unfold checkBlockClaims at accepted
  obtain ⟨seen, checked, _⟩ := Ix.CompileCert.Canon.except_bind_ok.mp accepted
  change forIn primary ({} : References) (primaryBody cenv) = .ok seen at checked
  have present := Ix.CompileCert.Canon.forIn_except_array (primaryBody cenv)
    (fun pre current => ∀ name address, (name, address) ∈ pre → current[name]? = some address)
    (by
      rintro pre ⟨name, address⟩ current step previous success
      refine ⟨current.insert name address, primaryBody_result success, ?_⟩
      intro other payload member
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with earlier | ⟨rfl, rfl⟩
      · exact primaryBody_extends_seen success other payload (previous other payload earlier)
      · simp)
    primary (init := {}) (out := seen)
    (by intro name address mem; cases mem) checked
  intro left hl right hr same
  exact Option.some.inj ((present left.1 left.2 hl).symm.trans
    ((Std.HashMap.getElem?_congr (m := seen) same).trans (present right.1 right.2 hr)))

/-- Successful name-claim checking derives compatibility of every primary
write with the old direct-resolution table, including repeated aliases. -/
theorem checkBlockClaims_primary (cenv : CompileEnv) (primary : Array (Ix.Name × Address))
    (cache : BlockState) (accepted : checkBlockClaims cenv primary cache = .ok ()) :
    CompatibleClaims cenv.nameToAddr primary.toList := by
  unfold checkBlockClaims at accepted
  obtain ⟨seen, checked, _⟩ := Ix.CompileCert.Canon.except_bind_ok.mp accepted
  change forIn primary ({} : References) (primaryBody cenv) = .ok seen at checked
  have invariant := Ix.CompileCert.Canon.forIn_except_array (primaryBody cenv)
    (fun pre current => CompatibleClaims cenv.nameToAddr pre ∧ SeenAgrees cenv.nameToAddr current)
    (by
      rintro pre ⟨name, address⟩ current step ⟨earlierClaims, agree⟩ success
      have rowAgree := primaryBody_compatible agree success
      refine ⟨current.insert name address, primaryBody_result success, ?_⟩
      refine ⟨?_, seen_insert agree rowAgree⟩
      intro other payload member old found
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
      rcases member with earlier | ⟨rfl, rfl⟩
      · exact earlierClaims other payload earlier old found
      · exact rowAgree old found)
    primary (init := {}) (out := seen)
    (by
      constructor
      · intro name address member; cases member
      · intro name address found; simp at found)
    checked
  exact invariant.1

theorem checkCompiledBlock_primary (before : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo result cache = .ok ()) :
    CompatibleClaims before.cenv.nameToAddr (primaryClaims lo result).toList := by
  unfold checkCompiledBlock at accepted
  obtain ⟨_, checked, _⟩ := Ix.CompileCert.Canon.except_bind_ok.mp accepted
  exact checkBlockClaims_primary before.cenv _ cache checked

private theorem named_refs (rows : Array (Ix.Name × Ixon.Named)) (before : CompileEnv) :
    (forIn (m := Id) rows before (fun row state =>
      .yield { state with nameToNamed := state.nameToNamed.insert row.1 row.2 })).nameToAddr =
      before.nameToAddr := by
  apply forIn_preserves rows before _ CompileEnv.nameToAddr <;> intro row state <;> rfl

private theorem aux_refs (rows : Array (Address × Ixon.Constant)) (before : CompileEnv) :
    (forIn (m := Id) rows before (fun row state =>
      .yield { state with constants := state.constants.insert row.1 (Ixon.ser row.2) })).nameToAddr =
      before.nameToAddr := by
  apply forIn_preserves rows before _ CompileEnv.nameToAddr <;> intro row state <;> rfl

private theorem class_refs (names : Array Ix.Name) (classes : Array (Array Ix.Name))
    (before : CompileEnv) :
    (forIn (m := Id) names before (fun name state =>
      .yield { state with blocks := state.blocks.insert name classes })).nameToAddr =
      before.nameToAddr := by
  apply forIn_preserves names before _ CompileEnv.nameToAddr <;> intro row state <;> rfl

private theorem classes_refs (classes : Array (Array Ix.Name)) (before : CompileEnv) :
    (forIn (m := Id) classes before (fun names state =>
      .yield (forIn (m := Id) names state (fun name state =>
        .yield { state with blocks := state.blocks.insert name classes })))).nameToAddr =
      before.nameToAddr := by
  apply forIn_preserves classes before _ CompileEnv.nameToAddr
  · intro row state; rfl
  · intro row state
    exact class_refs row classes state

private theorem projection_refs (rows : Array (Ix.Name × Ixon.Constant × Ixon.ConstantMeta))
    (before : CompileEnv) :
    (forIn (m := Id) rows before (fun row state =>
      let bytes := Ixon.ser row.2.1
      let addr := Address.blake3 bytes
      .yield { state with
        totalBytes := state.totalBytes + bytes.size
        constants := state.constants.insert addr bytes
        nameToNamed := state.nameToNamed.insert row.1 { addr, constMeta := row.2.2 }
        nameToAddr := state.nameToAddr.insert row.1 addr })).nameToAddr =
      applyClaims before.nameToAddr
        (rows.toList.map fun row => (row.1, Address.blake3 (Ixon.ser row.2.1))) := by
  rw [forIn_project rows before _ CompileEnv.nameToAddr
    (fun names row => names.insert row.1 (Address.blake3 (Ixon.ser row.2.1)))
    (fun _ _ => rfl) (fun _ _ => rfl)]
  simp only [applyClaims, List.foldl_map, Array.foldl_toList]

set_option maxRecDepth 2048 in
/-- The direct source-resolution table is affected only by the primary
claims. Auxiliary Named metadata cannot alter this projection of the merge. -/
theorem merge_primary (before : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState) :
    (mergeCompiledBlock before lo result cache).cenv.nameToAddr =
      applyClaims before.cenv.nameToAddr (primaryClaims lo result).toList := by
  unfold mergeCompiledBlock
  simp only [Id.run, bind, pure]
  split <;> split <;> split
  all_goals simp only [classes_refs, named_refs, aux_refs, projection_refs]
  all_goals simp_all [primaryClaims, applyClaims]

/-- The actual guarded merge preserves every existing direct source binding.
This is an observation about compiler lookup, not a source-faithfulness claim. -/
theorem checked_merge_primary_extends (before : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo result cache = .ok ()) :
    ReferencesExtend before.cenv.nameToAddr
      (mergeCompiledBlock before lo result cache).cenv.nameToAddr := by
  rw [merge_primary]
  exact applyClaims_preserves (checkCompiledBlock_primary before lo result cache accepted)

theorem checked_merge_primary_present (before : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo result cache = .ok ()) :
    ∀ name address, (name, address) ∈ (primaryClaims lo result).toList →
      (mergeCompiledBlock before lo result cache).cenv.nameToAddr[name]? = some address := by
  rw [merge_primary]
  unfold checkCompiledBlock at accepted
  obtain ⟨_, checked, _⟩ := Ix.CompileCert.Canon.except_bind_ok.mp accepted
  exact applyClaims_present _ _ (checkBlockClaims_consistent before.cenv _ cache checked)

/-- A previously direct binding retains its resolved address even if the
merge adds auxiliary mappings, because direct bindings have lookup priority. -/
theorem checked_merge_resolves_prior (before : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo result cache = .ok ())
    (name : Ix.Name) (address : Address)
    (found : before.cenv.nameToAddr[name]? = some address) :
    resolveAddrPure (mergeCompiledBlock before lo result cache).cenv name = some address := by
  have preserved := checked_merge_primary_extends before lo result cache accepted name address found
  unfold resolveAddrPure
  change (match (mergeCompiledBlock before lo result cache).cenv.nameToAddr[name]? with
    | some a => some a
    | none => _) = _
  rw [preserved]

/-- Each primary address points at an actual anonymous write of the block,
including member/constructor projections rather than just the owning block. -/
theorem primary_claim_record (lo : Ix.Name) (result : BlockResult) (cache : BlockState)
    (name : Ix.Name) (address : Address)
    (claimed : (name, address) ∈ (primaryClaims lo result).toList) :
    ∃ bytes, (address, bytes) ∈ recordWrites result cache := by
  unfold primaryClaims at claimed
  split at claimed
  · simp only [List.mem_singleton, Prod.mk.injEq] at claimed
    obtain ⟨rfl, rfl⟩ := claimed
    exact ⟨result.blockBytes, List.mem_cons_self⟩
  · simp only [Array.toList_map, List.mem_map] at claimed
    obtain ⟨⟨member, projection, constMeta⟩, memberOf, equal⟩ := claimed
    simp only [Prod.mk.injEq] at equal
    obtain ⟨rfl, rfl⟩ := equal
    refine ⟨Ixon.ser projection, List.mem_cons_of_mem _ (List.mem_append_left _ ?_)⟩
    exact List.mem_map.mpr ⟨_, memberOf, rfl⟩

/-- Guard success publishes every claimed primary reference and its payload.
Neither the new reference nor its presence was assumed in the prior store. -/
theorem checked_merge_primary_record (before : DriverAcc) (lo : Ix.Name)
    (result : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo result cache = .ok ())
    (name : Ix.Name) (address : Address)
    (claimed : (name, address) ∈ (primaryClaims lo result).toList) :
    (mergeCompiledBlock before lo result cache).cenv.nameToAddr[name]? = some address ∧
      ∃ bytes, (mergeCompiledBlock before lo result cache).cenv.constants[address]? = some bytes := by
  refine ⟨checked_merge_primary_present before lo result cache accepted name address claimed, ?_⟩
  obtain ⟨bytes, write⟩ := primary_claim_record lo result cache name address claimed
  exact ⟨bytes, (checkCompiledBlock_present before lo result cache accepted).1 address bytes write⟩

end Ix.CompileCert.ReferencePublication
