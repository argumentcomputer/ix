import Ix.CompileCert.Interning

/-! # Checked blob writes

Checked local blob accumulation preserves every earlier readable payload.
The guards compare exact bytes in the block's table and in the published
prefix; no digest injectivity is assumed. Name compilation uses the same
guard and commits its accumulated changes only on success. These facts
preserve the in-flight reader's readings and the expression cache's
meanings when the reader's blobs are the published prefix (`aligned`).
Content addresses are `Address.admissionHash`, pure BLAKE3 in the logic. -/

namespace Ix.CompileCert.BlobWrites

open Ix.CompileM Ix.CompileCert
open Ix.Kernel (Mode LevelParam)

abbrev Store := Std.HashMap Address ByteArray

/-- A blob as the block reads it: its own table first, then the published
prefix. -/
def readBlob (ambient : Store) (state : BlockState) (address : Address) : Option ByteArray :=
  (state.blockBlobs.get? address).orElse (fun _ => ambient.get? address)

def Extends (ambient : Store) (before after : BlockState) : Prop :=
  ∀ address bytes, readBlob ambient before address = some bytes → readBlob ambient after address = some bytes

theorem Extends.refl (ambient : Store) (state : BlockState) : Extends ambient state state := fun _ _ found => found

theorem Extends.trans {ambient : Store} {before middle after : BlockState}
    (first : Extends ambient before middle) (last : Extends ambient middle after) : Extends ambient before after :=
  fun address bytes found => last address bytes (first address bytes found)

theorem contentMatches_agree (store : Store) (address : Address) (bytes : ByteArray)
    (checked : contentMatches store address bytes = true) {old : ByteArray}
    (found : store.get? address = some old) : old = bytes := by
  unfold contentMatches at checked
  change (match store.get? address with | none => true | some prior => decide (prior = bytes)) = true at checked
  simpa only [found, decide_eq_true_eq] using checked

/-- The block state without the two tables name compilation writes. -/
def withoutNamesBlobs (state : BlockState) : BlockState := { state with blockNames := {}, blockBlobs := {} }

theorem storeBlob_success (before : BlockState) (ambient : Store) (address : Address) (bytes : ByteArray)
    {after : BlockState} (success : before.storeBlob ambient address bytes = .ok after) :
    withoutNamesBlobs after = withoutNamesBlobs before ∧ Extends ambient before after ∧
      after.blockBlobs.get? address = some bytes := by
  unfold BlockState.storeBlob at success
  split at success
  · rename_i checked
    have checks := Bool.and_eq_true_iff.mp checked
    cases Except.ok.inj success
    refine ⟨rfl, ?_, ?_⟩
    · intro query old found
      by_cases same : address = query
      · subst query
        have agree : old = bytes := by
          unfold readBlob at found
          cases localFound : before.blockBlobs.get? address with
          | some localBytes =>
            have equal : localBytes = old := by simpa only [localFound, Option.orElse_some, Option.some.injEq] using found
            rw [← equal]
            exact contentMatches_agree before.blockBlobs address bytes checks.1 localFound
          | none =>
            have prior : ambient.get? address = some old := by simpa only [localFound, Option.orElse_none] using found
            exact contentMatches_agree ambient address bytes checks.2 prior
        subst old
        simp [readBlob]
      · change ((before.blockBlobs.insert address bytes)[query]?).orElse (fun _ => ambient.get? query) = some old
        simpa only [readBlob, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          beq_iff_eq, same, ↓reduceIte] using found
    · change (before.blockBlobs.insert address bytes)[address]? = some bytes
      simp
  · cases success

theorem compileName_success (before : BlockState) (ambient : Store) (name : Ix.Name) :
    ∀ after, before.compileName ambient name = .ok after →
      withoutNamesBlobs after = withoutNamesBlobs before ∧ Extends ambient before after := by
  induction name generalizing before with
  | anonymous hash =>
    rw [BlockState.compileName]
    split <;> (intro after success; cases Except.ok.inj success; exact ⟨rfl, .refl _ _⟩)
  | str parent text hash ih =>
    rw [BlockState.compileName]
    dsimp only
    split
    · intro after success; cases Except.ok.inj success; exact ⟨rfl, .refl _ _⟩
    · intro after success
      let named := { before with blockNames := before.blockNames.insert (Ix.Name.str parent text hash).getHash (.str parent text hash) }
      change (named.storeBlob ambient (Address.admissionHash text.toUTF8) text.toUTF8 >>=
        fun current => current.compileName ambient parent) = .ok after at success
      cases wrote : named.storeBlob ambient (Address.admissionHash text.toUTF8) text.toUTF8 with
      | error error => simp only [wrote, bind, Except.bind] at success; cases success
      | ok middle =>
        simp only [wrote, bind, Except.bind] at success
        have stored := storeBlob_success named ambient _ _ wrote
        have parentResult := ih middle after success
        exact ⟨parentResult.1.trans stored.1, Extends.trans stored.2.1 parentResult.2⟩
  | num parent index hash ih =>
    rw [BlockState.compileName]
    dsimp only
    split
    · intro after success; cases Except.ok.inj success; exact ⟨rfl, .refl _ _⟩
    · intro after success
      have correct := ih
        { before with blockNames := before.blockNames.insert (Ix.Name.num parent index hash).getHash (.num parent index hash) }
        after success
      exact correct

theorem storeBlob_run (bytes : ByteArray) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (storeBlob bytes) context before =
      match before.storeBlob context.1.blobs (Address.admissionHash bytes) bytes with
      | .error error => (.error error, before)
      | .ok after => (.ok (Address.admissionHash bytes), after) := by
  simp only [storeBlob, rawRun_bind, rawRun_get, rawRun_read, rawRun_applyBlockState]
  cases before.storeBlob context.1.blobs (Address.admissionHash bytes) bytes <;> rfl

theorem storeBlob_preserves (bytes : ByteArray) (context : CompileEnv × BlockEnv) (before : BlockState) :
    let result := rawRun (storeBlob bytes) context before
    withoutNamesBlobs result.2 = withoutNamesBlobs before ∧ Extends context.1.blobs before result.2 ∧
      ∀ address, result.1 = .ok address → result.2.blockBlobs.get? address = some bytes := by
  rw [storeBlob_run]
  cases ran : before.storeBlob context.1.blobs (Address.admissionHash bytes) bytes with
  | error error => exact ⟨rfl, .refl _ _, by intro address bad; cases bad⟩
  | ok after =>
    have correct := storeBlob_success before context.1.blobs _ bytes ran
    refine ⟨correct.1, correct.2.1, ?_⟩
    intro address same
    cases Except.ok.inj same
    exact correct.2.2

theorem compileName_preserves (name : Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState) :
    let result := rawRun (compileName name) context before
    withoutNamesBlobs result.2 = withoutNamesBlobs before ∧ Extends context.1.blobs before result.2 := by
  simp only [compileName, rawRun_bind, rawRun_get, rawRun_read, rawRun_applyBlockState]
  cases ran : before.compileName context.1.blobs name with
  | error error => exact ⟨rfl, .refl _ _⟩
  | ok after => exact compileName_success before context.1.blobs name after ran

theorem compileNames_success (before : BlockState) (ambient : Store) (names : Array Ix.Name) :
    ∀ after, before.compileNames ambient names = .ok after →
      withoutNamesBlobs after = withoutNamesBlobs before ∧ Extends ambient before after := by
  unfold BlockState.compileNames
  rw [← Array.foldlM_toList]
  induction names.toList generalizing before with
  | nil => intro after success; cases Except.ok.inj success; exact ⟨rfl, .refl _ _⟩
  | cons name names ih =>
    rw [List.foldlM_cons]
    intro after success
    cases ran : before.compileName ambient name with
    | error error => simp only [ran, bind, Except.bind] at success; cases success
    | ok middle =>
      simp only [ran, bind, Except.bind] at success
      have first := compileName_success before ambient name middle ran
      have last := ih middle after success
      exact ⟨last.1.trans first.1, Extends.trans first.2 last.2⟩

theorem compileNames_preserves (names : Array Ix.Name) (context : CompileEnv × BlockEnv) (before : BlockState) :
    let result := rawRun (compileNames names) context before
    withoutNamesBlobs result.2 = withoutNamesBlobs before ∧ Extends context.1.blobs before result.2 := by
  simp only [compileNames, rawRun_bind, rawRun_get, rawRun_read, rawRun_applyBlockState]
  cases ran : before.compileNames context.1.blobs names with
  | error error => exact ⟨rfl, .refl _ _⟩
  | ok after => exact compileNames_success before context.1.blobs names after ran

/-- A step that writes only names and blobs, and keeps every readable blob,
keeps every reading of the in-flight reader whose blobs are the published
prefix. -/
theorem reader_extends {md : Mode} (ambient : Store) (before after : BlockState)
    (frame : withoutNamesBlobs after = withoutNamesBlobs before) (grows : Extends ambient before after)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (aligned : ∀ address, reader.blob address = ambient.get? address) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader param self before).ecx
      (ExpressionRead.blockReader reader param self after).ecx := by
  apply ExpressionRead.blockReader_growth reader param self
  · intro index address found
    have same := congrArg BlockState.refs frame
    change after.refs = before.refs at same
    rw [same]
    exact found
  · intro index univ found
    have same := congrArg BlockState.univs frame
    change after.univs = before.univs at same
    rw [same]
    exact found
  · intro address bytes found
    change (before.blockBlobs.get? address).orElse (fun _ => reader.blob address) = some bytes at found
    change (after.blockBlobs.get? address).orElse (fun _ => reader.blob address) = some bytes
    rw [aligned address] at found ⊢
    exact grows address bytes found

theorem storeBlob_reading {md : Mode} (bytes : ByteArray) (context : CompileEnv × BlockEnv)
    (before : BlockState) (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader param self before).ecx
      (ExpressionRead.blockReader reader param self (rawRun (storeBlob bytes) context before).2).ecx :=
  reader_extends context.1.blobs before _ (storeBlob_preserves bytes context before).1
    (storeBlob_preserves bytes context before).2.1 reader param self aligned

theorem compileName_reading {md : Mode} (name : Ix.Name) (context : CompileEnv × BlockEnv)
    (before : BlockState) (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address) :
    ExpressionRead.Extends (ExpressionRead.blockReader reader param self before).ecx
      (ExpressionRead.blockReader reader param self (rawRun (compileName name) context before).2).ecx :=
  reader_extends context.1.blobs before _ (compileName_preserves name context before).1
    (compileName_preserves name context before).2 reader param self aligned

/-- The expression cache's meanings survive a names-and-blobs step. -/
theorem cache_preserved {md : Mode} (ambient : Store) (before after : BlockState)
    (frame : withoutNamesBlobs after = withoutNamesBlobs before) (grows : Extends ambient before after)
    (reader : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (aligned : ∀ address, reader.blob address = ambient.get? address)
    (related : Ix.Expr → Kernel.Reader.CExpr md → Prop)
    (valid : CacheSound (ExpressionRead.Reading related (ExpressionRead.blockReader reader param self) before)
      before.exprCache) :
    CacheSound (ExpressionRead.Reading related (ExpressionRead.blockReader reader param self) after)
      after.exprCache :=
  ExpressionRead.blockReader_cache_sound
    (reader_extends ambient before after frame grows reader param self aligned)
    (by have same := congrArg BlockState.exprCache frame; exact same) valid

/-- A differing local payload is refused before any state change, including
when the published prefix has no entry at the address. -/
theorem storeBlob_refuses_local (bytes old : ByteArray) (context : CompileEnv × BlockEnv) (before : BlockState)
    (found : before.blockBlobs.get? (Address.admissionHash bytes) = some old) (different : old ≠ bytes) :
    rawRun (storeBlob bytes) context before =
      (.error (.invalidMutualBlock "anonymous publication: conflicting blob payload"), before) := by
  rw [storeBlob_run]
  have refuses : contentMatches before.blockBlobs (Address.admissionHash bytes) bytes = false := by
    unfold contentMatches
    change (match before.blockBlobs.get? (Address.admissionHash bytes) with
      | none => true | some prior => decide (prior = bytes)) = false
    simp only [found, different, decide_false]
  simp only [BlockState.storeBlob, refuses, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end Ix.CompileCert.BlobWrites
