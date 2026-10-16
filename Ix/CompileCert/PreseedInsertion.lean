import Ix.CompileCert.PreseedCoverage
import Ix.CompileCert.PreseedWire
import Ix.CompileCert.Canon.QSort

/-! # After preseeding, every level of every root is preseeded

A successful `preseedExprTables` canonicalizes the collected universes and
interns them, in serialized-key order skipping adjacent duplicates, into the
primary universe table; equal serialized keys of wire-valid universes are
equal universes (`univ_key_injective`, through the codec's round trip). So
the primary index then holds the canonical form of every collected universe
(`univs_sorted`), and, with the collector's coverage
(`PreseedUniverses.roots_initial`), the canonical form of the exact lowering
of every level occurrence of every root (`preseed_preseeded`): the
`UniversePipeline.Preseeded` premise of
`compileAndInternUnivCanon_returns`, discharged for the production preseed.
CT-14's `PreseedInsertion`, universe half. -/

namespace Ix.CompileCert.PreseedInsertion

open Ix.CompileM Ix.CompileCert Ix.CompileCert.Interning
open Ix.CompileCert.UniverseMeaning (lower)
open Ix.CompileCert.CanonUnivCache (CanonCacheExact withoutCanonCache canonUnivCached_correct)

theorem bytes_beq_iff (first second : ByteArray) : (first == second) = true ↔ first = second := by
  cases first with
  | mk first =>
    cases second with
    | mk second =>
      show ByteArray.beq ⟨first⟩ ⟨second⟩ = true ↔ _
      simp [ByteArray.beq]

local instance : LawfulBEq ByteArray where
  eq_of_beq := (bytes_beq_iff _ _).mp
  rfl := (bytes_beq_iff _ _).mpr rfl

/-- Every old index binding survives. -/
def MapExtends [BEq α] [Hashable α] (before after : Std.HashMap α UInt64) : Prop :=
  ∀ key index, before.get? key = some index → after.get? key = some index

theorem MapExtends.refl [BEq α] [Hashable α] (table : Std.HashMap α UInt64) : MapExtends table table :=
  fun _ _ found => found

theorem MapExtends.trans [BEq α] [Hashable α] {first middle last : Std.HashMap α UInt64}
    (head : MapExtends first middle) (tail : MapExtends middle last) : MapExtends first last :=
  fun key index found => tail key index (head key index found)

theorem MapExtends.insert_fresh [BEq α] [Hashable α] [LawfulBEq α]
    (table : Std.HashMap α UInt64) (key : α) (index : UInt64) (missing : table.get? key = none) :
    MapExtends table (table.insert key index) := by
  intro query prior found
  have different : key ≠ query := by
    intro same
    subst query
    rw [missing] at found
    cases found
  change (table.insert key index)[query]? = some prior
  rw [Std.HashMap.getElem?_insert]
  simp only [beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ↓reduceIte]
  exact found

theorem internUniv_index (context : CompileEnv × BlockEnv) (before : BlockState) (univ : Ixon.Univ) :
    let result := rawRun (internUniv univ) context before
    MapExtends before.univsIndex result.2.univsIndex ∧
      ∀ index, result.1 = .ok index → result.2.univsIndex.get? univ = some index := by
  dsimp only
  cases found : before.univsIndex.get? univ with
  | some index =>
    rw [internUniv_hit univ context before found]
    refine ⟨.refl _, ?_⟩
    intro result same
    cases Except.ok.inj same
    exact found
  | none =>
    rw [internUniv_miss univ context before found]
    by_cases room : before.univs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      refine ⟨MapExtends.insert_fresh _ univ _ found, ?_⟩
      intro index success
      cases Except.ok.inj success
      simp
    · simp only [room, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [checkedTableCount_state]; exact .refl _
      · intro index success
        exact (room (checkedTableCount_value _ _ _ _ success).2).elim

theorem discard_ok {action : CompileM α} {context : CompileEnv × BlockEnv} {before after : BlockState}
    (ran : rawRun (Functor.discard action) context before = (.ok (), after)) :
    ∃ value, rawRun action context before = (.ok value, after) := by
  unfold Functor.discard at ran
  obtain ⟨value, middle, first, last⟩ := bind_ok ran
  have same := congrArg Prod.snd last
  dsimp only [rawRun_pure] at same
  exact ⟨value, same ▸ first⟩

/-- The universe has a slot in the primary index. -/
def UnivPresent (state : BlockState) (univ : Ixon.Univ) : Prop :=
  ∃ index, state.univsIndex.get? univ = some index

/-- Serialized keys identify wire-valid universes. -/
theorem univ_key_injective (first second : Ixon.Univ) (firstWire : first.wireWF) (secondWire : second.wireWF)
    (same : univSortKey first = univSortKey second) : first = second := by
  change Ixon.serUniv first = Ixon.serUniv second at same
  have decoded := congrArg Ixon.deUniv same
  rw [Ixon.Verify.deUniv_serUniv first firstWire, Ixon.Verify.deUniv_serUniv second secondWire] at decoded
  exact Except.ok.inj decoded

def EntryValid (entry : ByteArray × Ixon.Univ) : Prop := entry.1 = univSortKey entry.2 ∧ entry.2.wireWF

def PreviousValid (previous : Option ByteArray) (state : BlockState) : Prop :=
  ∀ key, previous = some key → ∃ univ, key = univSortKey univ ∧ univ.wireWF ∧ UnivPresent state univ

theorem univs_inserted (context : CompileEnv × BlockEnv) (univs : List (ByteArray × Ixon.Univ))
    (previous : Option ByteArray) (before after : BlockState) (sound : UnivIndexSound before)
    (valid : ∀ entry ∈ univs, EntryValid entry) (prior : PreviousValid previous before)
    (ran : rawRun (internPreseedUnivs univs previous) context before = (.ok (), after)) :
    UnivIndexSound after ∧ MapExtends before.univsIndex after.univsIndex ∧
      ∀ entry ∈ univs, UnivPresent after entry.2 := by
  induction univs generalizing previous before with
  | nil =>
    simp only [internPreseedUnivs, rawRun_pure] at ran
    have same := congrArg Prod.snd ran
    dsimp only at same
    subst after
    exact ⟨sound, .refl _, by simp⟩
  | cons entry rest ih =>
    rcases entry with ⟨key, univ⟩
    have headValid := valid (key, univ) (by simp)
    have restValid : ∀ entry ∈ rest, EntryValid entry := fun entry member => valid entry (by simp [member])
    rw [internPreseedUnivs] at ran
    by_cases different : (previous != some key) = true
    · simp only [different, ↓reduceIte] at ran
      obtain ⟨done, middle, first, tail⟩ := bind_ok ran
      cases done
      obtain ⟨index, inserted⟩ := discard_ok first
      have mapping := internUniv_index context before univ
      have indexSound := internUniv_correct univ context before sound
      rw [inserted] at mapping indexSound
      have present : UnivPresent middle univ := ⟨index, mapping.2 index rfl⟩
      have restChecked := ih (some key) middle indexSound.1 restValid (by
        intro query same
        cases Option.some.inj same
        exact ⟨univ, headValid.1, headValid.2, present⟩) tail
      refine ⟨restChecked.1, mapping.1.trans restChecked.2.1, ?_⟩
      intro query member
      rcases List.mem_cons.mp member with same | remaining
      · subst query
        exact ⟨index, restChecked.2.1 univ index (mapping.2 index rfl)⟩
      · exact restChecked.2.2 query remaining
    · have same : previous = some key := by simpa using different
      rw [ite_eq_right different] at ran
      obtain ⟨stored, storedKey, storedWire, storedPresent⟩ := prior key same
      have sameValue := univ_key_injective stored univ storedWire headValid.2 (storedKey.symm.trans headValid.1)
      subst stored
      have restChecked := ih (some key) before sound restValid (by
        intro query equal
        cases Option.some.inj equal
        exact ⟨univ, headValid.1, headValid.2, storedPresent⟩) ran
      refine ⟨restChecked.1, restChecked.2.1, ?_⟩
      intro query member
      rcases List.mem_cons.mp member with equal | remaining
      · subst query
        obtain ⟨index, found⟩ := storedPresent
        exact ⟨index, restChecked.2.1 univ index found⟩
      · exact restChecked.2.2 query remaining

/-- The production order: canonical universes keyed by their serialization,
sorted by key. -/
def sortedUnivs (univs : Array Ixon.Univ) : Array (ByteArray × Ixon.Univ) :=
  (univs.map fun u => (univSortKey u, u)).qsort fun (ka, _) (kb, _) => byteArrayCmp ka kb == .lt

theorem sortedUnivs_valid (univs : Array Ixon.Univ) (wire : ∀ univ ∈ univs, univ.wireWF) :
    ∀ entry ∈ (sortedUnivs univs).toList, EntryValid entry := by
  intro entry member
  rw [Array.mem_toList_iff, sortedUnivs, Canon.mem_qsort, Array.mem_map] at member
  obtain ⟨univ, source, rfl⟩ := member
  exact ⟨rfl, wire univ source⟩

theorem sortedUnivs_member (univs : Array Ixon.Univ) (univ : Ixon.Univ) (member : univ ∈ univs) :
    (univSortKey univ, univ) ∈ (sortedUnivs univs).toList := by
  rw [Array.mem_toList_iff, sortedUnivs, Canon.mem_qsort, Array.mem_map]
  exact ⟨univ, member, rfl⟩

/-- **Every sorted entry gets a slot.** -/
theorem univs_sorted (context : CompileEnv × BlockEnv) (univs : Array Ixon.Univ)
    (before after : BlockState) (sound : UnivIndexSound before) (wire : ∀ univ ∈ univs, univ.wireWF)
    (ran : rawRun (internPreseedUnivs (sortedUnivs univs).toList none) context before = (.ok (), after)) :
    UnivIndexSound after ∧ MapExtends before.univsIndex after.univsIndex ∧
      ∀ univ ∈ univs, UnivPresent after univ := by
  have checked := univs_inserted context _ none before after sound (sortedUnivs_valid univs wire)
    (by intro key impossible; cases impossible) ran
  exact ⟨checked.1, checked.2.1, fun univ member => checked.2.2 _ (sortedUnivs_member univs univ member)⟩

/-- The canonicalization step computes `canonUniv` of each collected
universe, from an exact canonical memo. -/
theorem canonicalize (sources : List Ixon.Univ) (initial : Array Ixon.Univ)
    (context : CompileEnv × BlockEnv) (before : BlockState) (exactCache : CanonCacheExact before) :
    ∃ after, rawRun (canonPreseedUnivs sources initial) context before =
        (.ok (initial ++ (sources.map Ixon.canonUniv).toArray), after) ∧
      CanonCacheExact after ∧ withoutCanonCache after = withoutCanonCache before := by
  induction sources generalizing initial before with
  | nil => exact ⟨before, by simp [canonPreseedUnivs, rawRun_pure], exactCache, rfl⟩
  | cons source rest ih =>
    obtain ⟨middle, compiled, exactMiddle, frame⟩ := canonUnivCached_correct source context before exactCache
    obtain ⟨after, restRan, exactAfter, restFrame⟩ := ih (initial.push (Ixon.canonUniv source)) middle exactMiddle
    refine ⟨after, ?_, exactAfter, restFrame.trans frame⟩
    rw [canonPreseedUnivs, rawRun_bind, compiled]
    dsimp only
    rw [restRan]
    congr 2
    apply Array.toList_inj.mp
    simp

/-- The reference inserter leaves the canonical memo and the universe
table alone. -/
theorem refs_frame (refs : List Address) (previous : Option Address) :
    Preserves (fun state => (state.canonUnivCache, state.univs, state.univsIndex))
      (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact Preserves.pure _ ()
  | cons address rest ih =>
    unfold internPreseedRefs
    split
    · refine Preserves.bind ?_ (fun _ => ih (some address))
      unfold Functor.discard
      refine Preserves.bind ?_ (fun _ => Preserves.pure _ _)
      intro context before
      have same := congrArg (fun state => (state.canonUnivCache, state.univs, state.univsIndex))
        (ExpressionState.internRef_frame address context before)
      exact same
    · exact ih (some address)

/-- **After a successful preseed, every level occurrence of every root is
preseeded**: the primary table is final and holds the canonical form of the
level's exact lowering under the root's parameter context. -/
theorem preseed_preseeded (context : CompileEnv × BlockEnv) (roots : Array (Ix.Expr × List Ix.Name))
    {before after : BlockState} (sound : UnivIndexSound before) (canonExact : CanonCacheExact before)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) :
    after.univsFinal = true ∧ ∀ root ∈ roots,
      PreseedUniverses.LevelsSatisfy (fun level => UniversePipeline.Preseeded root.2 level after) root.1 := by
  rw [preseedExprTables] at ran
  obtain ⟨collection, collectedState, collected, tail⟩ := bind_ok ran
  rcases collection with ⟨refs, univs, seen⟩
  dsimp only at tail
  obtain ⟨_, refState, refsRan, rest⟩ := bind_ok tail
  obtain ⟨canonical, canonState, canonRan, finish⟩ := bind_ok rest
  obtain ⟨canonicalWire, finish⟩ := PreseedValidation.after_check canonical _ context canonState after () finish
  obtain ⟨_, univState, univsRan, flagRan⟩ := bind_ok finish
  rw [rawRun_modify] at flagRan
  cases flagRan
  -- the collection keeps the canonical memo and the universe table
  have coverage := PreseedUniverses.roots_initial context before collectedState roots.toList _ collected
  have collectFrame := PreseedWire.collection_frame roots.toList (#[], #[], {}) context before
  rw [collected] at collectFrame
  have collectedCanon : collectedState.canonUnivCache = before.canonUnivCache := by
    have view := congrArg (fun view => view.2.2.2.1) collectFrame; exact view
  have collectedUnivs : collectedState.univs = before.univs := by
    have view := congrArg (fun view => view.2.1) collectFrame; exact view
  have collectedIndex : collectedState.univsIndex = before.univsIndex := by
    have view := congrArg (fun view => view.2.2.2.2) collectFrame; exact view
  -- so does the reference inserter
  have refsSame := (refs_frame _ none).of_ok refsRan
  have refsCanon : refState.canonUnivCache = collectedState.canonUnivCache := by
    have view := congrArg (fun view => view.1) refsSame; exact view
  have refsUnivs : refState.univs = collectedState.univs := by
    have view := congrArg (fun view => view.2.1) refsSame; exact view
  have refsIndex : refState.univsIndex = collectedState.univsIndex := by
    have view := congrArg (fun view => view.2.2) refsSame; exact view
  have refCanonExact : CanonCacheExact refState := by
    intro source value found
    rw [refsCanon, collectedCanon] at found
    exact canonExact source value found
  -- the canonicalization computes `canonUniv` of each collected universe
  obtain ⟨canonFinal, expected, _, canonFrame⟩ :=
    canonicalize univs.toList (Array.mkEmpty univs.size) context refState refCanonExact
  rw [canonRan] at expected
  obtain ⟨values, states⟩ := Prod.mk.inj expected
  have canonicalEq := Except.ok.inj values
  subst canonFinal
  have canonUnivs : canonState.univs = refState.univs := by
    have view := congrArg BlockState.univs canonFrame; exact view
  have canonIndex : canonState.univsIndex = refState.univsIndex := by
    have view := congrArg BlockState.univsIndex canonFrame; exact view
  have canonSound : UnivIndexSound canonState := by
    show IndexSound canonState.univs canonState.univsIndex
    rw [canonUnivs, canonIndex, refsUnivs, refsIndex, collectedUnivs, collectedIndex]
    exact sound
  -- the insertion gives every canonical universe a slot
  change rawRun (internPreseedUnivs (sortedUnivs canonical).toList none) context canonState = (.ok (), univState)
    at univsRan
  have inserted := univs_sorted context canonical canonState univState canonSound canonicalWire univsRan
  refine ⟨rfl, ?_⟩
  intro root member
  apply PreseedUniverses.LevelsSatisfy.imp _ root.1 (coverage root (by simpa using member))
  intro level present finalFlag raw lowered
  have collectedMember : raw ∈ univs := present.value lowered
  have canonicalMember : Ixon.canonUniv raw ∈ canonical := by
    rw [canonicalEq]
    simp only [Array.mem_append, List.mem_toArray, List.mem_map]
    exact Or.inr ⟨raw, Array.mem_toList_iff.mpr collectedMember, rfl⟩
  obtain ⟨index, found⟩ := inserted.2.2 _ canonicalMember
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  change (univState.univsIndex.get? (Ixon.canonUniv raw)).isSome = true
  rw [found]
  rfl

end Ix.CompileCert.PreseedInsertion
