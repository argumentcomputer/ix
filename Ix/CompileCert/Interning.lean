import Ix.CompileCert.ExpressionRead
import Ix.CompileCert.RawRun
import Ix.CompileCert.UniverseEval
import Std.Data.HashMap.Lemmas

/-! # The table interners

Index-map integrity and reader preservation for the compiler's table
interners `internRef`, `internUniv` and `internMetaUniv`. Empty tables
establish the index invariant (`IndexSound`); a successful insertion is
bounded by the executed wire-range check, and a failed check changes no
state. Every interner keeps every old slot (`Retains`), so the in-flight
reader's successful readings survive it (`*_reading`), and so does the
meaning of every expression-cache entry (`*_cache_sound`). These facts do
not establish the source meaning of newly compiled universes or references;
those are the constructor steps' obligations.

`internMetaUniv` writes the current constant's extension of original
universe spellings, which the in-flight reader does not read: the primary
tables it reads stay as they are. Wire universes have lawful keys
(`Ix.CompileCert.lawfulUnivBEq`), and so do addresses. -/

namespace Ix.CompileCert.Interning

open Ix.CompileM Ix.CompileCert
open Ix.Kernel (Mode LevelParam)

/-- Every previously occupied slot retains its value. -/
def Retains (before after : Array α) : Prop :=
  ∀ (index : Nat) (value : α), before[index]? = some value → after[index]? = some value

theorem Retains.refl (table : Array α) : Retains table table := fun _ _ found => found

theorem Retains.trans {first middle last : Array α} (head : Retains first middle)
    (tail : Retains middle last) : Retains first last :=
  fun index value found => tail index value (head index value found)

theorem Retains.push (table : Array α) (value : α) : Retains table (table.push value) := by
  intro index prior found
  have bound := (Array.getElem?_eq_some_iff.mp found).1
  simpa only [Array.getElem?_push, ite_eq_right (Nat.ne_of_lt bound)] using found

theorem Retains.map {before after : Array α} (growth : Retains before after) (f : α → β) :
    Retains (before.map f) (after.map f) := by
  intro index value found
  rw [Array.getElem?_map] at found ⊢
  cases prior : before[index]? with
  | none => simp [prior] at found
  | some item => simpa [prior, growth _ _ prior] using found

theorem Retains.append_right (fixed : Array α) {before after : Array α}
    (growth : Retains before after) : Retains (fixed ++ before) (fixed ++ after) := by
  intro index value found
  by_cases bound : index < fixed.size
  · simpa [Array.getElem?_append_left bound] using found
  · have bound : fixed.size ≤ index := Nat.le_of_not_gt bound
    rw [Array.getElem?_append_right bound] at found ⊢
    exact growth _ _ found

/-- The indexing map only returns slots containing its queried value. -/
def IndexSound [BEq α] [Hashable α] (table : Array α) (indices : Std.HashMap α UInt64) : Prop :=
  ∀ value index, indices.get? value = some index → table[index.toNat]? = some value

theorem IndexSound.empty [BEq α] [Hashable α] : IndexSound (#[] : Array α) {} := by
  intro value index found
  simp at found

theorem IndexSound.insert [BEq α] [Hashable α] [LawfulBEq α]
    {table : Array α} {indices : Std.HashMap α UInt64} (sound : IndexSound table indices)
    (value : α) (room : table.size < UInt64.size) :
    IndexSound (table.push value) (indices.insert value table.size.toUInt64) := by
  intro query index found
  change (indices.insert value table.size.toUInt64)[query]? = some index at found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have same : value = query := beq_iff_eq.mp same
    subst query
    cases Option.some.inj found
    rw [show table.size.toUInt64.toNat = table.size from UInt64.toNat_ofNat_of_lt' room]
    exact Array.getElem?_push_size
  · exact Retains.push _ _ _ _ (sound query index found)

abbrev RefIndexSound (state : BlockState) : Prop := IndexSound state.refs state.refsIndex

abbrev UnivIndexSound (state : BlockState) : Prop := IndexSound state.univs state.univsIndex

abbrev MetaUnivIndexSound (state : BlockState) : Prop :=
  IndexSound state.metaUnivs state.metaUnivsIndex

theorem refIndexSound_empty (state : BlockState) :
    RefIndexSound { state with refs := #[], refsIndex := {} } := by
  intro address index found
  simp at found

/-! ## The pure helpers -/

theorem internRef_retains (state : BlockState) (address : Address) :
    Retains state.refs (state.internRef address).1.refs := by
  unfold BlockState.internRef
  split
  · exact .refl _
  · exact .push _ _

theorem internRef_lookup (state : BlockState) (address : Address)
    (sound : RefIndexSound state) (room : state.refs.size < UInt64.size) :
    (state.internRef address).1.refs[(state.internRef address).2.toNat]? = some address := by
  unfold BlockState.internRef
  split
  · rename_i index found
    exact sound address index found
  · dsimp only
    rw [show state.refs.size.toUInt64.toNat = state.refs.size from UInt64.toNat_ofNat_of_lt' room]
    exact Array.getElem?_push_size

theorem internRef_sound (state : BlockState) (address : Address)
    (sound : RefIndexSound state) (room : state.refs.size < UInt64.size) :
    RefIndexSound (state.internRef address).1 := by
  unfold BlockState.internRef
  split
  · exact sound
  · exact sound.insert address room

/-- The unchecked pure helper wraps a fresh slot at the wire limit to zero.
This symbolic statement does not allocate an enormous native array. -/
theorem internRef_limit_wraps (state : BlockState) (address : Address)
    (full : state.refs.size = UInt64.size) (miss : state.refsIndex.get? address = none) :
    (state.internRef address).2 = 0 := by
  simp only [BlockState.internRef, miss, full]
  rfl

theorem internUniv_lookup (state : BlockState) (univ : Ixon.Univ)
    (sound : UnivIndexSound state) (room : state.univs.size < UInt64.size) :
    (state.internUniv univ).1.univs[(state.internUniv univ).2.toNat]? = some univ := by
  unfold BlockState.internUniv
  split
  · rename_i index found
    exact sound univ index found
  · dsimp only
    rw [show state.univs.size.toUInt64.toNat = state.univs.size from UInt64.toNat_ofNat_of_lt' room]
    exact Array.getElem?_push_size

theorem internUniv_sound (state : BlockState) (univ : Ixon.Univ)
    (sound : UnivIndexSound state) (room : state.univs.size < UInt64.size) :
    UnivIndexSound (state.internUniv univ).1 := by
  unfold BlockState.internUniv
  split
  · exact sound
  · exact sound.insert univ room

/-! ## The checked range guards -/

theorem checkedTableIndex_state (table : String) (index : Nat)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (checkedTableIndex table index) context state).2 = state := by
  unfold checkedTableIndex
  split <;> rfl

theorem checkedTableIndex_value (table : String) (index : Nat)
    (context : CompileEnv × BlockEnv) (state : BlockState) {value : UInt64}
    (success : (rawRun (checkedTableIndex table index) context state).1 = .ok value) :
    value.toNat = index ∧ index < UInt64.size := by
  unfold checkedTableIndex at success
  split at success
  · rename_i bound
    cases Except.ok.inj success
    exact ⟨UInt64.toNat_ofNat_of_lt' bound, bound⟩
  · cases success

theorem checkedTableCount_state (table : String) (count : Nat)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (checkedTableCount table count) context state).2 = state := by
  unfold checkedTableCount
  split <;> rfl

theorem checkedTableCount_value (table : String) (count : Nat)
    (context : CompileEnv × BlockEnv) (state : BlockState) {value : UInt64}
    (success : (rawRun (checkedTableCount table count) context state).1 = .ok value) :
    value.toNat = count ∧ count < UInt64.size := by
  unfold checkedTableCount at success
  split at success
  · rename_i bound
    cases Except.ok.inj success
    exact ⟨UInt64.toNat_ofNat_of_lt' bound, bound⟩
  · cases success

/-! ## References -/

theorem internRef_hit (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) {index : UInt64}
    (found : state.refsIndex.get? address = some index) :
    rawRun (internRef address) context state = (.ok index, state) := by
  have contains : state.refsIndex.contains address = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    change (state.refsIndex.get? address).isSome = true
    rw [found]
    rfl
  unfold internRef
  simp only [rawRun_bind, rawRun_get]
  by_cases full : state.refs.size + 1 ≥ UInt64.size
  all_goals
    simp only [full, ↓reduceIte, rawRun_bind, rawRun_get, contains, Bool.not_true,
      Bool.false_eq_true, rawRun_modifyGet, BlockState.internRef, found]

theorem internRef_miss (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (miss : state.refsIndex.get? address = none) :
    rawRun (internRef address) context state =
      if state.refs.size + 1 < UInt64.size then
        (.ok state.refs.size.toUInt64,
          { state with
            refs := state.refs.push address,
            refsIndex := state.refsIndex.insert address state.refs.size.toUInt64 })
      else rawRun (checkedTableCount "reference" (state.refs.size + 1)) context state := by
  have contains : state.refsIndex.contains address = false := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    change (state.refsIndex.get? address).isSome = false
    rw [miss]
    rfl
  unfold internRef
  simp only [rawRun_bind, rawRun_get]
  by_cases room : state.refs.size + 1 < UInt64.size
  · have full : ¬ state.refs.size + 1 ≥ UInt64.size := by omega
    simp only [full, room, ↓reduceIte, rawRun_modifyGet, BlockState.internRef, miss]
  · have full : state.refs.size + 1 ≥ UInt64.size := by omega
    simp only [full, room, ↓reduceIte, rawRun_bind, rawRun_get, contains,
      Bool.not_false, checkedTableCount, Functor.discard]
    rfl

/-- The checked reference interner preserves the index invariant and every
old slot, and every successful returned index names the supplied address.
There is no caller capacity premise: an overflowing miss fails in place. -/
theorem internRef_correct (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (sound : RefIndexSound state) :
    let result := rawRun (internRef address) context state
    RefIndexSound result.2 ∧ Retains state.refs result.2.refs ∧
      ∀ index, result.1 = .ok index → result.2.refs[index.toNat]? = some address := by
  cases found : state.refsIndex.get? address with
  | some index =>
    rw [internRef_hit address context state found]
    refine ⟨sound, .refl _, ?_⟩
    intro value same
    cases Except.ok.inj same
    exact sound address index found
  | none =>
    rw [internRef_miss address context state found]
    by_cases room : state.refs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      have keeps := internRef_sound state address sound (by omega)
      have points := internRef_lookup state address sound (by omega)
      simp only [BlockState.internRef, found] at keeps points
      refine ⟨keeps, .push _ _, ?_⟩
      intro value same
      cases Except.ok.inj same
      exact points
    · simp only [room, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rwa [checkedTableCount_state]
      · rw [checkedTableCount_state]
        exact .refl _
      · intro index success
        exact (room (checkedTableCount_value _ _ _ _ success).2).elim

/-- The reference interner changes only the reference table and its index. -/
theorem internRef_tables (address : Address) (context : CompileEnv × BlockEnv) (state : BlockState) :
    let after := (rawRun (internRef address) context state).2
    after.univs = state.univs ∧ after.blockBlobs = state.blockBlobs ∧ after.exprCache = state.exprCache := by
  cases found : state.refsIndex.get? address with
  | some index => rw [internRef_hit address context state found]; exact ⟨rfl, rfl, rfl⟩
  | none =>
    rw [internRef_miss address context state found]
    split
    · exact ⟨rfl, rfl, rfl⟩
    · rw [checkedTableCount_state]; exact ⟨rfl, rfl, rfl⟩

/-- The reference interner preserves every successful reading of the
in-flight reader, failing runs included, without an index or capacity
premise. -/
theorem internRef_reading {md : Mode} (address : Address) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) :
    ExpressionRead.Extends (ExpressionRead.blockReader context param self state).ecx
      (ExpressionRead.blockReader context param self
        (rawRun (internRef address) compileContext state).2).ecx := by
  have tables := internRef_tables address compileContext state
  apply ExpressionRead.blockReader_growth_tables context param self
  · cases found : state.refsIndex.get? address with
    | some index => rw [internRef_hit address compileContext state found]; exact Retains.refl _
    | none =>
      rw [internRef_miss address compileContext state found]
      split
      · exact Retains.push _ _
      · rw [checkedTableCount_state]; exact Retains.refl _
  · rw [tables.1]; exact Retains.refl _
  · exact tables.2.1

theorem internRef_cache_sound {md : Mode} (address : Address) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (source : Ix.Expr → Kernel.Reader.CExpr md → Prop)
    (valid : CacheSound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context param self) state)
      state.exprCache) :
    let after := (rawRun (internRef address) compileContext state).2
    CacheSound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context param self) after)
      after.exprCache :=
  ExpressionRead.blockReader_cache_sound
    (internRef_reading address compileContext state context param self)
    (internRef_tables address compileContext state).2.2 valid

/-! ## Universes -/

theorem internUniv_hit (univ : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (state : BlockState) {index : UInt64} (found : state.univsIndex.get? univ = some index) :
    rawRun (internUniv univ) context state = (.ok index, state) := by
  have contains : state.univsIndex.contains univ = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    change (state.univsIndex.get? univ).isSome = true
    rw [found]
    rfl
  unfold internUniv
  simp only [rawRun_bind, rawRun_get]
  by_cases full : state.univs.size + 1 ≥ UInt64.size
  all_goals
    simp only [full, ↓reduceIte, rawRun_bind, rawRun_get, contains, Bool.not_true,
      Bool.false_eq_true, rawRun_modifyGet, BlockState.internUniv, found]

theorem internUniv_miss (univ : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (state : BlockState) (miss : state.univsIndex.get? univ = none) :
    rawRun (internUniv univ) context state =
      if state.univs.size + 1 < UInt64.size then
        (.ok state.univs.size.toUInt64, { state with
          univs := state.univs.push univ,
          univsIndex := state.univsIndex.insert univ state.univs.size.toUInt64 })
      else rawRun (checkedTableCount "universe" (state.univs.size + 1)) context state := by
  have contains : state.univsIndex.contains univ = false := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    change (state.univsIndex.get? univ).isSome = false
    rw [miss]
    rfl
  unfold internUniv
  simp only [rawRun_bind, rawRun_get]
  by_cases room : state.univs.size + 1 < UInt64.size
  · have full : ¬ state.univs.size + 1 ≥ UInt64.size := by omega
    simp only [full, room, ↓reduceIte, rawRun_modifyGet, BlockState.internUniv, miss]
  · have full : state.univs.size + 1 ≥ UInt64.size := by omega
    simp only [full, room, ↓reduceIte, rawRun_bind, rawRun_get, contains,
      Bool.not_false, checkedTableCount, Functor.discard]
    rfl

/-- The checked universe interner preserves the index invariant and every
old slot, and every successful returned index names the supplied universe. -/
theorem internUniv_correct (univ : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (state : BlockState) (sound : UnivIndexSound state) :
    let result := rawRun (internUniv univ) context state
    UnivIndexSound result.2 ∧ Retains state.univs result.2.univs ∧
      ∀ index, result.1 = .ok index → result.2.univs[index.toNat]? = some univ := by
  cases found : state.univsIndex.get? univ with
  | some index =>
    rw [internUniv_hit univ context state found]
    refine ⟨sound, .refl _, ?_⟩
    intro value same
    cases Except.ok.inj same
    exact sound univ index found
  | none =>
    rw [internUniv_miss univ context state found]
    by_cases room : state.univs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      have keeps := internUniv_sound state univ sound (by omega)
      have points := internUniv_lookup state univ sound (by omega)
      simp only [BlockState.internUniv, found] at keeps points
      refine ⟨keeps, .push _ _, ?_⟩
      intro value same
      cases Except.ok.inj same
      exact points
    · simp only [room, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rwa [checkedTableCount_state]
      · rw [checkedTableCount_state]; exact .refl _
      · intro index success
        exact (room (checkedTableCount_value _ _ _ _ success).2).elim

/-- The universe interner changes only the universe table and its index. -/
theorem internUniv_tables (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    let after := (rawRun (internUniv univ) context state).2
    after.refs = state.refs ∧ after.blockBlobs = state.blockBlobs ∧ after.exprCache = state.exprCache ∧
      after.metaUnivs = state.metaUnivs ∧ after.metaUnivsIndex = state.metaUnivsIndex := by
  cases found : state.univsIndex.get? univ with
  | some index => rw [internUniv_hit univ context state found]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | none =>
    rw [internUniv_miss univ context state found]
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [checkedTableCount_state]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem internUniv_reading {md : Mode} (univ : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) :
    ExpressionRead.Extends (ExpressionRead.blockReader context param self state).ecx
      (ExpressionRead.blockReader context param self
        (rawRun (internUniv univ) compileContext state).2).ecx := by
  have tables := internUniv_tables univ compileContext state
  apply ExpressionRead.blockReader_growth_tables context param self
  · rw [tables.1]; exact Retains.refl _
  · cases found : state.univsIndex.get? univ with
    | some index => rw [internUniv_hit univ compileContext state found]; exact Retains.refl _
    | none =>
      rw [internUniv_miss univ compileContext state found]
      split
      · exact Retains.push _ _
      · rw [checkedTableCount_state]; exact Retains.refl _
  · exact tables.2.1

theorem internUniv_cache_sound {md : Mode} (univ : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (source : Ix.Expr → Kernel.Reader.CExpr md → Prop)
    (valid : CacheSound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context param self) state)
      state.exprCache) :
    let after := (rawRun (internUniv univ) compileContext state).2
    CacheSound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context param self) after)
      after.exprCache :=
  ExpressionRead.blockReader_cache_sound
    (internUniv_reading univ compileContext state context param self)
    (internUniv_tables univ compileContext state).2.2.1 valid

/-! ## The extension of original universe spellings -/

theorem add_index_eq (base : Nat) (slot : UInt64) :
    base.toUInt64 + slot = (base + slot.toNat).toUInt64 := by
  change UInt64.ofNat base + slot = UInt64.ofNat (base + slot.toNat)
  rw [UInt64.ofNat_add, UInt64.ofNat_toNat]

theorem internMetaUniv_hit (univ : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (state : BlockState) {slot : UInt64} (found : state.metaUnivsIndex.get? univ = some slot) :
    rawRun (internMetaUniv univ) context state =
      rawRun (checkedTableIndex "metadata universe" (state.univs.size + slot.toNat)) context state := by
  simp only [internMetaUniv, rawRun_bind, rawRun_get, found]
  by_cases room : state.univs.size + slot.toNat < UInt64.size
  · simp only [checkedTableIndex, room, ↓reduceIte, Functor.discard]
    change ((.ok (state.internMetaUniv univ).2 : Except CompileError UInt64),
      (state.internMetaUniv univ).1) =
      (.ok (state.univs.size + slot.toNat).toUInt64, state)
    simp only [BlockState.internMetaUniv, found]
    rw [add_index_eq]
  · simp only [checkedTableIndex, room, ↓reduceIte, Functor.discard]
    rfl

theorem internMetaUniv_miss (univ : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (state : BlockState) (missing : state.metaUnivsIndex.get? univ = none) :
    rawRun (internMetaUniv univ) context state =
      match (rawRun (checkedTableIndex "metadata universe"
        (state.univs.size + state.metaUnivs.size)) context state).1 with
      | .error error => (.error error, state)
      | .ok index => (.ok index, { state with
          metaUnivs := state.metaUnivs.push univ,
          metaUnivsIndex := state.metaUnivsIndex.insert univ state.metaUnivs.size.toUInt64 }) := by
  simp only [internMetaUniv, rawRun_bind, rawRun_get, missing]
  by_cases room : state.univs.size + state.metaUnivs.size < UInt64.size
  · simp only [checkedTableIndex, room, ↓reduceIte, Functor.discard]
    change ((.ok (state.internMetaUniv univ).2 : Except CompileError UInt64),
      (state.internMetaUniv univ).1) = _
    simp only [BlockState.internMetaUniv, missing]
    rw [show state.univs.size.toUInt64 + state.metaUnivs.size.toUInt64 =
      (state.univs.size + state.metaUnivs.size).toUInt64 from
        (UInt64.ofNat_add _ _).symm]
    rw [rawRun_pure]
  · simp only [checkedTableIndex, room, ↓reduceIte, Functor.discard]
    rfl

/-- Both universe indices stay sound, and every successful virtual index
selects its universe in the primary table followed by the extension. -/
theorem internMetaUniv_correct (univ : Ixon.Univ) (context : CompileEnv × BlockEnv)
    (state : BlockState) (primarySound : UnivIndexSound state)
    (metadataSound : MetaUnivIndexSound state) :
    let result := rawRun (internMetaUniv univ) context state
    UnivIndexSound result.2 ∧ MetaUnivIndexSound result.2 ∧
      Retains (state.univs ++ state.metaUnivs) (result.2.univs ++ result.2.metaUnivs) ∧
      ∀ index, result.1 = .ok index →
        (result.2.univs ++ result.2.metaUnivs)[index.toNat]? = some univ := by
  cases metadata : state.metaUnivsIndex.get? univ with
  | some slot =>
    rw [internMetaUniv_hit univ context state metadata]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rwa [checkedTableIndex_state]
    · rwa [checkedTableIndex_state]
    · rw [checkedTableIndex_state]; exact .refl _
    · intro index success
      have value := checkedTableIndex_value _ _ _ _ success
      rw [checkedTableIndex_state, value.1, Array.getElem?_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using metadataSound univ slot metadata
  | none =>
    rw [internMetaUniv_miss univ context state metadata]
    cases checked : (rawRun (checkedTableIndex "metadata universe"
        (state.univs.size + state.metaUnivs.size)) context state).1 with
    | error error =>
      exact ⟨primarySound, metadataSound, .refl _, by intro index bad; cases bad⟩
    | ok index =>
      have value := checkedTableIndex_value _ _ _ _ checked
      have room : state.metaUnivs.size < UInt64.size := by omega
      refine ⟨primarySound, metadataSound.insert univ room,
        Retains.append_right state.univs (.push _ _), ?_⟩
      intro result same
      cases Except.ok.inj same
      dsimp only
      rw [value.1, Array.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left, Array.getElem?_push_size]

/-- The extension interner changes only the extension and its index. -/
theorem internMetaUniv_tables (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    let after := (rawRun (internMetaUniv univ) context state).2
    after.refs = state.refs ∧ after.univs = state.univs ∧ after.univsIndex = state.univsIndex ∧
      after.blockBlobs = state.blockBlobs ∧ after.exprCache = state.exprCache := by
  cases found : state.metaUnivsIndex.get? univ with
  | some slot =>
    rw [internMetaUniv_hit univ context state found, checkedTableIndex_state]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | none =>
    rw [internMetaUniv_miss univ context state found]
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The extension is not read by the in-flight reader, so its interner keeps
every reading. -/
theorem internMetaUniv_reading {md : Mode} (univ : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Kernel.Reader.Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md))) :
    ExpressionRead.Extends (ExpressionRead.blockReader context param self state).ecx
      (ExpressionRead.blockReader context param self
        (rawRun (internMetaUniv univ) compileContext state).2).ecx := by
  have tables := internMetaUniv_tables univ compileContext state
  apply ExpressionRead.blockReader_growth_tables context param self
  · rw [tables.1]; exact Retains.refl _
  · rw [tables.2.1]; exact Retains.refl _
  · exact tables.2.2.2.1

theorem internMetaUniv_cache_sound {md : Mode} (univ : Ixon.Univ)
    (compileContext : CompileEnv × BlockEnv) (state : BlockState) (context : Kernel.Reader.Ctx md)
    (param : Nat → LevelParam) (self : Nat → Option (Kernel.Reader.ReadM (Kernel.Reader.CName md)))
    (source : Ix.Expr → Kernel.Reader.CExpr md → Prop)
    (valid : CacheSound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context param self) state)
      state.exprCache) :
    let after := (rawRun (internMetaUniv univ) compileContext state).2
    CacheSound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context param self) after)
      after.exprCache :=
  ExpressionRead.blockReader_cache_sound
    (internMetaUniv_reading univ compileContext state context param self)
    (internMetaUniv_tables univ compileContext state).2.2.2.2 valid

end Ix.CompileCert.Interning
