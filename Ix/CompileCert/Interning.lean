import Ix.CompileCert.ExpressionRead
import Ix.CompileCert.ExpressionFrame
import Std.Data.HashMap.Lemmas

/-! Index-map integrity and reader preservation for the production table
interners. The initial invariant is established by empty tables. Successful
insertion bounds come from the executed wire-range checks, and failed checks
preserve state. These facts do not establish the source meaning of newly
compiled universes or references; those constructor obligations remain.

Primary universe growth is interpreted in ordinary mode. Metadata-mode
expression compilation uses a primary hit or grows the extension instead,
which keeps existing virtual offsets stable. -/

namespace Ix.CompileCert.Interning

open Ix.CompileM Ix.CompileCert.HeadWriterFrame

/-- Every previously occupied slot retains its value. -/
def Retains (before after : Array α) : Prop :=
  ∀ (index : Nat) (value : α), before[index]? = some value → after[index]? = some value

theorem Retains.refl (table : Array α) : Retains table table := fun _ _ found => found

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

abbrev MetaRefIndexSound (state : BlockState) : Prop :=
  IndexSound state.p3MetaRefs state.p3MetaRefsIndex

theorem univ_beq_iff (left right : Ixon.Univ) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Ixon.instBEqUniv.beq]

instance lawfulUnivKeys : LawfulBEq Ixon.Univ where
  eq_of_beq := (univ_beq_iff _ _).mp
  rfl := (univ_beq_iff _ _).mpr rfl

abbrev UnivIndexSound (state : BlockState) : Prop := IndexSound state.univs state.univsIndex

abbrev MetaUnivIndexSound (state : BlockState) : Prop :=
  IndexSound state.metaUnivs state.metaUnivsIndex

theorem refIndexSound_empty (state : BlockState) :
    RefIndexSound { state with refs := #[], refsIndex := {} } := by
  intro address index found
  simp at found

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
  · intro query index found
    change (state.refsIndex.insert address state.refs.size.toUInt64)[query]? = some index at found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · rename_i same
      have same : address = query := beq_iff_eq.mp same
      subst query
      cases Option.some.inj found
      dsimp only
      rw [show state.refs.size.toUInt64.toNat = state.refs.size from UInt64.toNat_ofNat_of_lt' room]
      exact Array.getElem?_push_size
    · exact Retains.push _ _ _ _ (sound query index found)

/-- The unchecked pure helper wraps a fresh slot at the wire limit to zero.
This symbolic statement does not allocate an enormous native array. -/
theorem internRef_limit_wraps (state : BlockState) (address : Address)
    (full : state.refs.size = UInt64.size) (miss : state.refsIndex.get? address = none) :
    (state.internRef address).2 = 0 := by
  simp only [BlockState.internRef, miss, full]
  rfl

theorem rawRun_modifyGet (update : BlockState → α × BlockState)
    (context : CompileEnv × BlockEnv) (state : BlockState) :
    rawRun (modifyGetBlockState update) context state =
      (.ok (update state).1, (update state).2) := rfl

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

theorem internRef_primary_hit (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (mode : state.p3MetaMode = false) {index : UInt64}
    (found : state.refsIndex.get? address = some index) :
    rawRun (internRef address) context state = (.ok index, state) := by
  have contains : state.refsIndex.contains address = true := by
    rw [Std.HashMap.contains_eq_isSome_getElem?]
    change (state.refsIndex.get? address).isSome = true
    rw [found]
    rfl
  unfold internRef
  simp only [rawRun_bind, rawRun_get, mode, Bool.false_eq_true, ↓reduceIte]
  by_cases full : state.refs.size + 1 ≥ UInt64.size
  all_goals
    simp only [full, ↓reduceIte, rawRun_bind, rawRun_get, contains, Bool.not_true,
      Bool.false_eq_true, rawRun_modifyGet, BlockState.internRef, found]

theorem internRef_primary_miss (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (mode : state.p3MetaMode = false)
    (miss : state.refsIndex.get? address = none) :
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
  simp only [rawRun_bind, rawRun_get, mode, Bool.false_eq_true, ↓reduceIte]
  by_cases room : state.refs.size + 1 < UInt64.size
  · have full : ¬ state.refs.size + 1 ≥ UInt64.size := by omega
    simp only [full, room, ↓reduceIte, rawRun_modifyGet, BlockState.internRef, miss, mode]
  · have full : state.refs.size + 1 ≥ UInt64.size := by omega
    simp only [full, room, ↓reduceIte, rawRun_bind, rawRun_get, contains,
      Bool.not_false, checkedTableCount, Functor.discard]
    rfl

/-- The checked primary-table operation preserves the index invariant and
every old slot, and every successful returned index names the supplied address.
There is no caller capacity premise: an overflowing miss fails in place. -/
theorem internRef_primary_correct (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (mode : state.p3MetaMode = false) (sound : RefIndexSound state) :
    let result := rawRun (internRef address) context state
    RefIndexSound result.2 ∧ Retains state.refs result.2.refs ∧
      ∀ index, result.1 = .ok index → result.2.refs[index.toNat]? = some address := by
  cases found : state.refsIndex.get? address with
  | some index =>
    rw [internRef_primary_hit address context state mode found]
    refine ⟨sound, .refl _, ?_⟩
    intro value same
    cases Except.ok.inj same
    exact sound address index found
  | none =>
    rw [internRef_primary_miss address context state mode found]
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

def refTable (state : BlockState) : Array Address :=
  if state.p3MetaMode then state.refs ++ state.p3MetaRefs else state.refs

def univTable (state : BlockState) : Array Ixon.Univ :=
  if state.p3MetaMode then state.univs ++ state.metaUnivs else state.univs

/-- Discharge the reader's lookup conditions from actual compiler table views.
Index maps, expression memos, names and arena metadata are not reader inputs. -/
theorem blockReader_growth (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName)
    (before after : BlockState) (refs : Retains (refTable before) (refTable after))
    (univs : Retains (univTable before) (univTable after))
    (blobs : after.blockBlobs = before.blockBlobs) :
    ExpressionRead.Extends (ExpressionRead.blockReader context base param self before).ecx
      (ExpressionRead.blockReader context base param self after).ecx := by
  apply ExpressionRead.Extends.of_tables
  · rfl
  · intro ref; rfl
  · intro address ref found; exact found
  · intro address bytes found
    change (after.blockBlobs.get? address).orElse (fun _ => context.blob address) = some bytes
    rw [blobs]
    exact found
  · exact refs
  · exact univs.map (Ix.Kernel.Reader.convUniv param)

theorem internRef_primary_reading (address : Address) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (mode : state.p3MetaMode = false)
    (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName) :
    ExpressionRead.Extends (ExpressionRead.blockReader context base param self state).ecx
      (ExpressionRead.blockReader context base param self
        (rawRun (internRef address) compileContext state).2).ecx := by
  cases found : state.refsIndex.get? address with
  | some index =>
    rw [internRef_primary_hit address compileContext state mode found]
    exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl
  | none =>
    rw [internRef_primary_miss address compileContext state mode found]
    by_cases room : state.refs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      apply blockReader_growth context base param self
      · simpa only [refTable, mode, Bool.false_eq_true, ↓reduceIte] using Retains.push state.refs address
      · exact .refl _
      · rfl
    · simp only [room, ↓reduceIte, checkedTableCount_state]
      exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl

theorem internRefMeta_primary_hit (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) {index : UInt64} (found : state.refsIndex.get? address = some index) :
    rawRun (internRefMeta address) context state = (.ok index, state) := by
  simp only [internRefMeta, rawRun_bind, rawRun_get, found, rawRun_pure]

theorem internRefMeta_extension_hit (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (primary : state.refsIndex.get? address = none)
    {index : UInt64} (found : state.p3MetaRefsIndex.get? address = some index) :
    rawRun (internRefMeta address) context state =
      rawRun (checkedTableIndex "metadata reference" (state.refs.size + index.toNat)) context state := by
  simp only [internRefMeta, rawRun_bind, rawRun_get, primary, found]

theorem internRefMeta_miss (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (primary : state.refsIndex.get? address = none)
    (missing : state.p3MetaRefsIndex.get? address = none) :
    rawRun (internRefMeta address) context state =
      match (rawRun (checkedTableIndex "metadata reference"
        (state.refs.size + state.p3MetaRefs.size)) context state).1 with
      | .error error => (.error error, state)
      | .ok index => (.ok index, { state with
          p3MetaRefs := state.p3MetaRefs.push address,
          p3MetaRefsIndex := state.p3MetaRefsIndex.insert address state.p3MetaRefs.size.toUInt64 }) := by
  simp only [internRefMeta, rawRun_bind, rawRun_get, primary, missing]
  cases checked : rawRun (checkedTableIndex "metadata reference"
      (state.refs.size + state.p3MetaRefs.size)) context state with
  | mk outcome after =>
    have same := checkedTableIndex_state "metadata reference"
      (state.refs.size + state.p3MetaRefs.size) context state
    rw [checked] at same
    dsimp only at same
    subst after
    cases outcome <;> simp only [rawRun_modify, rawRun_pure]

/-- Both reference indices stay sound in metadata mode. Every successful
virtual index selects its intended address in the combined table. -/
theorem internRefMeta_correct (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (primarySound : RefIndexSound state)
    (metadataSound : MetaRefIndexSound state) :
    let result := rawRun (internRefMeta address) context state
    RefIndexSound result.2 ∧ MetaRefIndexSound result.2 ∧
      Retains (state.refs ++ state.p3MetaRefs) (result.2.refs ++ result.2.p3MetaRefs) ∧
      ∀ index, result.1 = .ok index →
        (result.2.refs ++ result.2.p3MetaRefs)[index.toNat]? = some address := by
  cases primary : state.refsIndex.get? address with
  | some index =>
    rw [internRefMeta_primary_hit address context state primary]
    refine ⟨primarySound, metadataSound, .refl _, ?_⟩
    intro value same
    cases Except.ok.inj same
    have found := primarySound address index primary
    have bound := (Array.getElem?_eq_some_iff.mp found).1
    rwa [Array.getElem?_append_left bound]
  | none =>
    cases metadata : state.p3MetaRefsIndex.get? address with
    | some slot =>
      rw [internRefMeta_extension_hit address context state primary metadata]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rwa [checkedTableIndex_state]
      · rwa [checkedTableIndex_state]
      · rw [checkedTableIndex_state]; exact .refl _
      · intro index success
        have value := checkedTableIndex_value _ _ _ _ success
        rw [checkedTableIndex_state, value.1, Array.getElem?_append_right (by omega)]
        simpa only [Nat.add_sub_cancel_left] using metadataSound address slot metadata
    | none =>
      rw [internRefMeta_miss address context state primary metadata]
      cases checked : (rawRun (checkedTableIndex "metadata reference"
          (state.refs.size + state.p3MetaRefs.size)) context state).1 with
      | error error =>
        exact ⟨primarySound, metadataSound, .refl _, by intro index bad; cases bad⟩
      | ok index =>
        have value := checkedTableIndex_value _ _ _ _ checked
        have room : state.p3MetaRefs.size < UInt64.size := by omega
        refine ⟨primarySound, metadataSound.insert address room,
          Retains.append_right state.refs (.push _ _), ?_⟩
        intro result same
        cases Except.ok.inj same
        dsimp only
        rw [value.1, Array.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left, Array.getElem?_push_size]

theorem internRefMeta_reading (address : Address) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName) :
    ExpressionRead.Extends (ExpressionRead.blockReader context base param self state).ecx
      (ExpressionRead.blockReader context base param self
        (rawRun (internRefMeta address) compileContext state).2).ecx := by
  cases primary : state.refsIndex.get? address with
  | some index =>
    rw [internRefMeta_primary_hit address compileContext state primary]
    exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl
  | none =>
    cases metadata : state.p3MetaRefsIndex.get? address with
    | some slot =>
      rw [internRefMeta_extension_hit address compileContext state primary metadata,
        checkedTableIndex_state]
      exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl
    | none =>
      rw [internRefMeta_miss address compileContext state primary metadata]
      cases checked : (rawRun (checkedTableIndex "metadata reference"
          (state.refs.size + state.p3MetaRefs.size)) compileContext state).1 with
      | error error =>
        exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl
      | ok index =>
        apply blockReader_growth context base param self
        · by_cases mode : state.p3MetaMode
          · simpa only [refTable, mode, ↓reduceIte] using
              Retains.append_right state.refs (Retains.push state.p3MetaRefs address)
          · simpa only [refTable, mode, Bool.false_eq_true, ↓reduceIte] using Retains.refl state.refs
        · exact .refl _
        · rfl

theorem internRef_meta_run (address : Address) (context : CompileEnv × BlockEnv)
    (state : BlockState) (mode : state.p3MetaMode = true) :
    rawRun (internRef address) context state = rawRun (internRefMeta address) context state := by
  simp only [internRef, rawRun_bind, rawRun_get, mode, ↓reduceIte]

/-- The production operation preserves every successful old reader lookup in
both modes, including errors, without an index-map or capacity premise. -/
theorem internRef_reading (address : Address) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName) :
    ExpressionRead.Extends (ExpressionRead.blockReader context base param self state).ecx
      (ExpressionRead.blockReader context base param self
        (rawRun (internRef address) compileContext state).2).ecx := by
  cases mode : state.p3MetaMode with
  | false => exact internRef_primary_reading address compileContext state mode context base param self
  | true =>
    rw [internRef_meta_run address compileContext state mode]
    exact internRefMeta_reading address compileContext state context base param self

theorem internRef_cache (address : Address) (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (internRef address) context state).2.exprCache = state.exprCache := by
  cases mode : state.p3MetaMode with
  | false =>
    cases found : state.refsIndex.get? address with
    | some index => rw [internRef_primary_hit address context state mode found]
    | none =>
      rw [internRef_primary_miss address context state mode found]
      split
      · rfl
      · rw [checkedTableCount_state]
  | true =>
    rw [internRef_meta_run address context state mode]
    cases primary : state.refsIndex.get? address with
    | some index => rw [internRefMeta_primary_hit address context state primary]
    | none =>
      cases metadata : state.p3MetaRefsIndex.get? address with
      | some slot => rw [internRefMeta_extension_hit address context state primary metadata,
          checkedTableIndex_state]
      | none =>
        rw [internRefMeta_miss address context state primary metadata]
        split <;> rfl

theorem internRef_cache_sound (address : Address) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName)
    (source : Ix.Expr → Ix.Kernel.Reader.CExpr → Prop)
    (valid : ExpressionCache.Sound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context base param self) state)
      state.exprCache) :
    let after := (rawRun (internRef address) compileContext state).2
    ExpressionCache.Sound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context base param self) after)
      after.exprCache := by
  apply ExpressionRead.cache_sound_of_growth
    (internRef_reading address compileContext state context base param self)
    ?_ (internRef_cache address compileContext state) valid
  intro index value found
  change (#[] : Array (Ix.Kernel.Reader.ReadM Ix.Kernel.Reader.CExpr))[index]? = some (.ok value) at found
  simp at found

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

/-- Primary universe growth preserves readings in ordinary mode. In metadata
mode the actual caller uses this operation only on a primary-table hit; a
primary miss is routed to `internMetaUniv` to keep virtual offsets fixed. -/
theorem internUniv_primary_reading (univ : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (mode : state.p3MetaMode = false)
    (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName) :
    ExpressionRead.Extends (ExpressionRead.blockReader context base param self state).ecx
      (ExpressionRead.blockReader context base param self
        (rawRun (internUniv univ) compileContext state).2).ecx := by
  cases found : state.univsIndex.get? univ with
  | some index =>
    rw [internUniv_hit univ compileContext state found]
    exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl
  | none =>
    rw [internUniv_miss univ compileContext state found]
    by_cases room : state.univs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      apply blockReader_growth context base param self
      · exact .refl _
      · simpa only [univTable, mode, Bool.false_eq_true, ↓reduceIte] using Retains.push state.univs univ
      · rfl
    · simp only [room, ↓reduceIte, checkedTableCount_state]
      exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl

theorem internMetaUniv_reading (univ : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName) :
    ExpressionRead.Extends (ExpressionRead.blockReader context base param self state).ecx
      (ExpressionRead.blockReader context base param self
        (rawRun (internMetaUniv univ) compileContext state).2).ecx := by
  cases metadata : state.metaUnivsIndex.get? univ with
  | some slot =>
    rw [internMetaUniv_hit univ compileContext state metadata, checkedTableIndex_state]
    exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl
  | none =>
    rw [internMetaUniv_miss univ compileContext state metadata]
    cases checked : (rawRun (checkedTableIndex "metadata universe"
        (state.univs.size + state.metaUnivs.size)) compileContext state).1 with
    | error error =>
      exact blockReader_growth context base param self state state (.refl _) (.refl _) rfl
    | ok index =>
      apply blockReader_growth context base param self
      · exact .refl _
      · by_cases mode : state.p3MetaMode
        · simpa only [univTable, mode, ↓reduceIte] using
            Retains.append_right state.univs (Retains.push state.metaUnivs univ)
        · simpa only [univTable, mode, Bool.false_eq_true, ↓reduceIte] using Retains.refl state.univs
      · rfl

theorem internUniv_cache (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (internUniv univ) context state).2.exprCache = state.exprCache := by
  cases found : state.univsIndex.get? univ with
  | some index => rw [internUniv_hit univ context state found]
  | none =>
    rw [internUniv_miss univ context state found]
    split
    · rfl
    · rw [checkedTableCount_state]

theorem internMetaUniv_cache (univ : Ixon.Univ) (context : CompileEnv × BlockEnv) (state : BlockState) :
    (rawRun (internMetaUniv univ) context state).2.exprCache = state.exprCache := by
  cases found : state.metaUnivsIndex.get? univ with
  | some slot => rw [internMetaUniv_hit univ context state found, checkedTableIndex_state]
  | none =>
    rw [internMetaUniv_miss univ context state found]
    split <;> rfl

theorem internUniv_cache_sound (univ : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (mode : state.p3MetaMode = false)
    (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName)
    (source : Ix.Expr → Ix.Kernel.Reader.CExpr → Prop)
    (valid : ExpressionCache.Sound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context base param self) state)
      state.exprCache) :
    let after := (rawRun (internUniv univ) compileContext state).2
    ExpressionCache.Sound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context base param self) after)
      after.exprCache := by
  apply ExpressionRead.cache_sound_of_growth
    (internUniv_primary_reading univ compileContext state mode context base param self)
    ?_ (internUniv_cache univ compileContext state) valid
  intro index value found
  change (#[] : Array (Ix.Kernel.Reader.ReadM Ix.Kernel.Reader.CExpr))[index]? = some (.ok value) at found
  simp at found

theorem internMetaUniv_cache_sound (univ : Ixon.Univ) (compileContext : CompileEnv × BlockEnv)
    (state : BlockState) (context : Ix.Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Ix.Kernel.Reader.CName) (self : Nat → Option Ix.Kernel.Reader.CName)
    (source : Ix.Expr → Ix.Kernel.Reader.CExpr → Prop)
    (valid : ExpressionCache.Sound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context base param self) state)
      state.exprCache) :
    let after := (rawRun (internMetaUniv univ) compileContext state).2
    ExpressionCache.Sound
      (ExpressionRead.Reading source (ExpressionRead.blockReader context base param self) after)
      after.exprCache := by
  apply ExpressionRead.cache_sound_of_growth
    (internMetaUniv_reading univ compileContext state context base param self)
    ?_ (internMetaUniv_cache univ compileContext state) valid
  intro index value found
  change (#[] : Array (Ix.Kernel.Reader.ReadM Ix.Kernel.Reader.CExpr))[index]? = some (.ok value) at found
  simp at found

end Ix.CompileCert.Interning
