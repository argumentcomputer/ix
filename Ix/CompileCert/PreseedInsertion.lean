import Ix.CompileCert.PreseedUniverses
import Ix.CompileCert.WireTables
import Ix.CompileCert.Canon.QSort
import IxC.Ixon.Verify.Basic
import Ix.CompileCert.PreseedCanonical

/-! Production preseed insertion preserves old index bindings and supplies
actual lookups for collected references and canonical universes. Serialized
universe-key equality is used only in the codec's wire domain. The public
composition keeps that canonical-universe bound explicit. -/

namespace Ix.CompileCert.PreseedInsertion

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame Ix.CompileCert.Interning

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

theorem internRef_index (context : CompileEnv × BlockEnv) (before : BlockState) (address : Address)
    (ordinary : before.p3MetaMode = false) :
    let result := rawRun (internRef address) context before
    MapExtends before.refsIndex result.2.refsIndex ∧
      ∀ index, result.1 = .ok index → result.2.refsIndex.get? address = some index := by
  dsimp only
  cases found : before.refsIndex.get? address with
  | some index =>
    rw [internRef_primary_hit address context before ordinary found]
    refine ⟨.refl _, ?_⟩
    intro result same
    cases Except.ok.inj same
    exact found
  | none =>
    rw [internRef_primary_miss address context before ordinary found]
    by_cases room : before.refs.size + 1 < UInt64.size
    · simp only [room, ↓reduceIte]
      refine ⟨MapExtends.insert_fresh _ address _ found, ?_⟩
      intro index success
      cases Except.ok.inj success
      simp
    · simp only [room, ↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [checkedTableCount_state]; exact .refl _
      · intro index success
        exact (room (checkedTableCount_value _ _ _ _ success).2).elim

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

theorem internRef_mode (context : CompileEnv × BlockEnv) (before : BlockState) (address : Address) :
    (rawRun (internRef address) context before).2.p3MetaMode = before.p3MetaMode := by
  have frame := ExpressionState.internRef_frame address context before
  have same := congrArg BlockState.p3MetaMode frame
  exact same

theorem discard_ok (action : CompileM α) (context : CompileEnv × BlockEnv) (before after : BlockState)
    (ran : rawRun (Functor.discard action) context before = (.ok (), after)) :
    ∃ value, rawRun action context before = (.ok value, after) := by
  obtain ⟨value, middle, first, last⟩ := PreseedReferences.bind_ok action (fun _ => pure ()) context before () after ran
  have same := congrArg Prod.snd last
  dsimp only [rawRun_pure] at same
  exact ⟨value, same ▸ first⟩

def RefPresent (state : BlockState) (address : Address) : Prop := ∃ index, state.refsIndex.get? address = some index

theorem refs_inserted (context : CompileEnv × BlockEnv) (refs : List Address) (previous : Option Address)
    (before after : BlockState) (ordinary : before.p3MetaMode = false) (sound : RefIndexSound before)
    (prior : ∀ address, previous = some address → RefPresent before address)
    (ran : rawRun (internPreseedRefs refs previous) context before = (.ok (), after)) :
    after.p3MetaMode = false ∧ RefIndexSound after ∧ MapExtends before.refsIndex after.refsIndex ∧
      ∀ address ∈ refs, RefPresent after address := by
  induction refs generalizing previous before with
  | nil =>
    simp only [internPreseedRefs, rawRun_pure] at ran
    have same := congrArg Prod.snd ran
    dsimp only at same
    subst after
    exact ⟨ordinary, sound, .refl _, by simp⟩
  | cons address rest ih =>
    rw [internPreseedRefs] at ran
    by_cases different : (previous != some address) = true
    · simp only [different, ↓reduceIte] at ran
      obtain ⟨done, middle, first, tail⟩ := PreseedReferences.bind_ok _ _ context before () after ran
      cases done
      obtain ⟨index, inserted⟩ := discard_ok (internRef address) context before middle first
      have mapping := internRef_index context before address ordinary
      have indexSound := internRef_primary_correct address context before ordinary sound
      have mode := internRef_mode context before address
      rw [inserted] at mapping indexSound mode
      have middleOrdinary : middle.p3MetaMode = false := mode.trans ordinary
      have present : RefPresent middle address := ⟨index, mapping.2 index rfl⟩
      have restChecked := ih (some address) middle middleOrdinary indexSound.1 (by
        intro query same
        cases Option.some.inj same
        exact present) tail
      refine ⟨restChecked.1, restChecked.2.1, mapping.1.trans restChecked.2.2.1, ?_⟩
      intro query member
      rcases List.mem_cons.mp member with same | remaining
      · subst query
        exact ⟨index, restChecked.2.2.1 address index (mapping.2 index rfl)⟩
      · exact restChecked.2.2.2 query remaining
    · have same : previous = some address := by simpa using different
      rw [ite_eq_right different] at ran
      have present := prior address same
      have restChecked := ih (some address) before ordinary sound (by
        intro query equal
        cases Option.some.inj equal
        exact present) ran
      refine ⟨restChecked.1, restChecked.2.1, restChecked.2.2.1, ?_⟩
      intro query member
      rcases List.mem_cons.mp member with equal | remaining
      · subst query
        obtain ⟨index, found⟩ := present
        exact ⟨index, restChecked.2.2.1 address index found⟩
      · exact restChecked.2.2.2 query remaining

theorem univ_key_injective (first second : Ixon.Univ) (firstWire : first.wireWF) (secondWire : second.wireWF)
    (same : univSortKey first = univSortKey second) : first = second := by
  change Ixon.serUniv first = Ixon.serUniv second at same
  have decoded := congrArg Ixon.deUniv same
  rw [Ixon.Verify.deUniv_serUniv first firstWire, Ixon.Verify.deUniv_serUniv second secondWire] at decoded
  exact Except.ok.inj decoded

def UnivPresent (state : BlockState) (univ : Ixon.Univ) : Prop := ∃ index, state.univsIndex.get? univ = some index

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
      obtain ⟨done, middle, first, tail⟩ := PreseedReferences.bind_ok _ _ context before () after ran
      cases done
      obtain ⟨index, inserted⟩ := discard_ok (internUniv univ) context before middle first
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

theorem refs_sorted (context : CompileEnv × BlockEnv) (refs : Array Address)
    (before after : BlockState) (ordinary : before.p3MetaMode = false) (sound : RefIndexSound before)
    (ran : rawRun (internPreseedRefs (refs.qsort (fun a b => a.cmpBytes b == .lt)).toList none) context before = (.ok (), after)) :
    after.p3MetaMode = false ∧ RefIndexSound after ∧ MapExtends before.refsIndex after.refsIndex ∧
      ∀ address ∈ refs, RefPresent after address := by
  have checked := refs_inserted context _ none before after ordinary sound (by intros; contradiction) ran
  refine ⟨checked.1, checked.2.1, checked.2.2.1, ?_⟩
  intro address member
  apply checked.2.2.2 address
  rw [Array.mem_toList_iff, Canon.mem_qsort]
  exact member

def sortedUnivs (univs : Array Ixon.Univ) : Array (ByteArray × Ixon.Univ) :=
  (univs.map (fun univ => (univSortKey univ, univ))).qsort (fun (a, _) (b, _) => byteArrayCmp a b == .lt)

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

theorem univs_sorted (context : CompileEnv × BlockEnv) (univs : Array Ixon.Univ)
    (before after : BlockState) (sound : UnivIndexSound before) (wire : ∀ univ ∈ univs, univ.wireWF)
    (ran : rawRun (internPreseedUnivs (sortedUnivs univs).toList none) context before = (.ok (), after)) :
    UnivIndexSound after ∧ MapExtends before.univsIndex after.univsIndex ∧ ∀ univ ∈ univs, UnivPresent after univ := by
  have checked := univs_inserted context _ none before after sound (sortedUnivs_valid univs wire)
    (by intro key impossible; cases impossible) ran
  exact ⟨checked.1, checked.2.1, fun univ member => checked.2.2 _ (sortedUnivs_member univs univ member)⟩

def withoutCollectionWrites (state : BlockState) : BlockState :=
  { state with univCache := {}, blockNames := {}, blockBlobs := {} }

abbrev CollectionFrame (action : CompileM α) : Prop := UniversePipeline.Preserves withoutCollectionWrites action

theorem CollectionFrame.compileUniv (source : Level) : CollectionFrame (compileUniv source) := by
  intro context before
  have frame := UniversePipeline.compileUniv_frame source context before
  have projected := congrArg withoutCollectionWrites frame
  exact projected

theorem CollectionFrame.lookup (name : Name) : CollectionFrame (lookupConstAddr name) := by
  intro context before
  rw [ExpressionState.lookupConstAddr_state]

theorem CollectionFrame.blob (bytes : ByteArray) : CollectionFrame (storeBlob bytes) := by
  intro context before
  have frame := (BlobWrites.storeBlob_preserves bytes context before).1
  have projected := congrArg withoutCollectionWrites frame
  exact projected

theorem CollectionFrame.levels (levels : List Level) (initial : Array Ixon.Univ) :
    CollectionFrame (collectExprTableUnivs levels initial) := by
  induction levels generalizing initial with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons level rest ih =>
    rw [collectExprTableUnivs]
    exact UniversePipeline.Preserves.bind (CollectionFrame.compileUniv level) (fun value => ih (initial.push value))

theorem CollectionFrame.structural (hint : Address) (mutualContext : MutCtx) (params : List Name)
    (source : Expr) (initial : ExprTableCollection) :
    CollectionFrame (collectExprTablesStructural hint mutualContext params source initial) := by
  induction source generalizing initial
  all_goals try cases ‹Lean.Literal›
  all_goals
    rcases initial with ⟨refs, univs, seen⟩
    rw [collectExprTablesStructural]
    split
    · exact UniversePipeline.Preserves.pure _ _
    · with_reducible repeat' first
        | exact UniversePipeline.Preserves.pure _ _
        | exact UniversePipeline.Preserves.throw _ _
        | exact CollectionFrame.compileUniv _
        | exact CollectionFrame.lookup _
        | exact CollectionFrame.blob _
        | exact CollectionFrame.levels _ _
        | refine UniversePipeline.Preserves.bind ?_ (fun value => ?_)
        | dsimp only
        | split
        | apply_assumption

theorem CollectionFrame.collect (source : Expr) (hint : Address) (initial : ExprTableCollection) :
    CollectionFrame (collectExprTables source hint initial) :=
  UniversePipeline.Preserves.bind (UniversePipeline.Preserves.read _) (fun block =>
    CollectionFrame.structural hint block.mutCtx block.univCtx source initial)

theorem CollectionFrame.withBlockEnv (update : BlockEnv → BlockEnv) {action : CompileM α} (framed : CollectionFrame action) :
    CollectionFrame (withBlockEnv update action) := fun context before => framed (context.1, update context.2) before

theorem CollectionFrame.withUnivCtx (params : List Name) {action : CompileM α} (framed : CollectionFrame action) :
    CollectionFrame (withUnivCtx params action) := by
  unfold Ix.CompileM.withUnivCtx
  exact UniversePipeline.Preserves.bind (UniversePipeline.Preserves.modify _ _ (fun _ => rfl))
    (fun _ => CollectionFrame.withBlockEnv _ framed)

theorem CollectionFrame.roots (roots : List (Expr × List Name)) (initial : ExprTableCollection) :
    CollectionFrame (collectPreseedExprs roots initial) := by
  induction roots generalizing initial with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons root rest ih =>
    rcases root with ⟨source, params⟩
    rw [collectPreseedExprs]
    exact UniversePipeline.Preserves.bind
      (CollectionFrame.withUnivCtx params (CollectionFrame.collect source (univParamsKey params) initial)) (fun next => ih next)

theorem preserves_discard {projection : BlockState → α} {action : CompileM β}
    (frame : UniversePipeline.Preserves projection action) : UniversePipeline.Preserves projection (Functor.discard action) := by
  unfold Functor.discard
  exact UniversePipeline.Preserves.bind frame (fun _ => UniversePipeline.Preserves.pure _ _)

theorem refs_frame (refs : List Address) (previous : Option Address) :
    UniversePipeline.Preserves ExpressionState.withoutRefTables (internPreseedRefs refs previous) := by
  induction refs generalizing previous with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons address rest ih =>
    rw [internPreseedRefs]
    split
    · exact UniversePipeline.Preserves.bind (preserves_discard (ExpressionState.internRef_frame address)) (fun _ => ih _)
    · exact ih _

theorem univs_frame (univs : List (ByteArray × Ixon.Univ)) (previous : Option ByteArray) :
    UniversePipeline.Preserves UniversePipeline.withoutUnivTables (internPreseedUnivs univs previous) := by
  induction univs generalizing previous with
  | nil => exact UniversePipeline.Preserves.pure _ _
  | cons entry rest ih =>
    rcases entry with ⟨key, univ⟩
    rw [internPreseedUnivs]
    split
    · exact UniversePipeline.Preserves.bind (preserves_discard (UniversePipeline.internUniv_frame univ)) (fun _ => ih _)
    · exact ih _

theorem canonicalize_run (sources : List Ixon.Univ) (initial output : Array Ixon.Univ)
    (context : CompileEnv × BlockEnv) (before after : BlockState) (exactCache : UniversePipeline.CanonCacheExact before)
    (ran : rawRun (canonPreseedUnivs sources initial) context before = (.ok output, after)) :
    output = initial ++ (sources.map Ixon.canonUniv).toArray ∧
      UniversePipeline.CanonCacheExact after ∧ UniversePipeline.withoutCanonCache after = UniversePipeline.withoutCanonCache before := by
  obtain ⟨finalState, expected, exactFinal, frame⟩ := PreseedCanonical.canonicalize sources initial context before exactCache
  rw [ran] at expected
  obtain ⟨values, states⟩ := Prod.mk.inj expected
  have outputEq := Except.ok.inj values
  subst finalState
  exact ⟨outputEq, exactFinal, frame⟩

/-- Coverage through the actual public preseed entry, under an explicit wire
bound on its canonicalized collected universes. The bound is not a source
validity definition and still needs a caller-side derivation. -/
theorem preseed_from_collection (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (before collectedState after : BlockState) (collection : ExprTableCollection)
    (collected : rawRun (collectPreseedExprs roots.toList (#[], #[], {})) context before = (.ok collection, collectedState))
    (ordinary : before.p3MetaMode = false) (refsSound : RefIndexSound before) (univsSound : UnivIndexSound before)
    (canonExact : UniversePipeline.CanonCacheExact before)
    (wire : ∀ univ ∈ collection.2.1, (Ixon.canonUniv univ).wireWF)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) :
    after.univsFinal = true ∧ after.p3MetaMode = false ∧ RefIndexSound after ∧ UnivIndexSound after ∧
      (∀ address ∈ collection.1, RefPresent after address) ∧
      (∀ univ ∈ collection.2.1, UnivPresent after (Ixon.canonUniv univ)) := by
  rcases collection with ⟨refs, univs, seen⟩
  rw [preseedExprTables, rawRun_bind, collected] at ran
  dsimp only at ran
  obtain ⟨doneRefs, refState, refsRan, tailRan⟩ := PreseedReferences.bind_ok _ _ context collectedState () after ran
  cases doneRefs
  obtain ⟨canonical, canonState, canonRan, finishRan⟩ := PreseedReferences.bind_ok _ _ context refState () after tailRan
  obtain ⟨doneUnivs, univState, univsRan, flagRan⟩ := PreseedReferences.bind_ok _ _ context canonState () after finishRan
  cases doneUnivs
  change rawRun (internPreseedUnivs (sortedUnivs canonical).toList none) context canonState = (.ok (), univState) at univsRan
  rw [rawRun_modify] at flagRan
  have finalState := congrArg Prod.snd flagRan
  dsimp only at finalState
  subst after
  have collectionFrame := CollectionFrame.roots roots.toList (#[], #[], {}) context before
  rw [collected] at collectionFrame
  have collectedMode := congrArg BlockState.p3MetaMode collectionFrame
  have collectedRefs := congrArg RefIndexSound collectionFrame
  have collectedUnivs := congrArg UnivIndexSound collectionFrame
  have collectedCanon := congrArg UniversePipeline.CanonCacheExact collectionFrame
  have refResult := refs_sorted context refs collectedState refState (collectedMode.trans ordinary) (collectedRefs.mpr refsSound) refsRan
  have refFrame := refs_frame (refs.qsort (fun a b => a.cmpBytes b == .lt)).toList none context collectedState
  rw [refsRan] at refFrame
  have refUnivs := congrArg UnivIndexSound refFrame
  have refCanon := congrArg UniversePipeline.CanonCacheExact refFrame
  have canonResult := canonicalize_run univs.toList (Array.mkEmpty univs.size) canonical context refState canonState
    (refCanon.mpr (collectedCanon.mpr canonExact)) canonRan
  have canonicalEq : canonical = univs.map Ixon.canonUniv := by
    rw [canonResult.1]
    apply Array.toList_inj.mp
    simp
  have canonicalWire : ∀ univ ∈ canonical, univ.wireWF := by
    intro univ member
    rw [canonicalEq, Array.mem_map] at member
    obtain ⟨source, sourceMember, rfl⟩ := member
    exact wire source sourceMember
  have canonUnivs := congrArg UnivIndexSound canonResult.2.2
  have canonRefs := congrArg RefIndexSound canonResult.2.2
  have canonRefMap := congrArg BlockState.refsIndex canonResult.2.2
  have canonMode := congrArg BlockState.p3MetaMode canonResult.2.2
  have univResult := univs_sorted context canonical canonState univState
    (canonUnivs.mpr (refUnivs.mpr (collectedUnivs.mpr univsSound))) canonicalWire univsRan
  have univFrame := univs_frame (sortedUnivs canonical).toList none context canonState
  rw [univsRan] at univFrame
  have finalRefs := congrArg RefIndexSound univFrame
  have finalRefMap := congrArg BlockState.refsIndex univFrame
  have finalMode := congrArg BlockState.p3MetaMode univFrame
  change univState.refsIndex = canonState.refsIndex at finalRefMap
  change canonState.refsIndex = refState.refsIndex at canonRefMap
  refine ⟨rfl, finalMode.trans (canonMode.trans refResult.1),
    finalRefs.mpr (canonRefs.mpr refResult.2.1), univResult.1, ?_, ?_⟩
  · intro address member
    obtain ⟨index, found⟩ := refResult.2.2.2 address member
    refine ⟨index, ?_⟩
    change univState.refsIndex.get? address = some index
    rw [finalRefMap, canonRefMap]
    exact found
  · intro univ member
    apply univResult.2.2
    rw [canonicalEq, Array.mem_map]
    exact ⟨univ, member, rfl⟩

theorem RefPresent.slot {state : BlockState} {address : Address} (present : RefPresent state address)
    (sound : RefIndexSound state) :
    ∃ index, state.refsIndex.get? address = some index ∧ state.refs[index.toNat]? = some address := by
  obtain ⟨index, found⟩ := present
  exact ⟨index, found, sound address index found⟩

theorem UnivPresent.slot {state : BlockState} {univ : Ixon.Univ} (present : UnivPresent state univ)
    (sound : UnivIndexSound state) :
    ∃ index, state.univsIndex.get? univ = some index ∧ state.univs[index.toNat]? = some univ := by
  obtain ⟨index, found⟩ := present
  exact ⟨index, found, sound univ index found⟩

theorem preseed_reads (context : CompileEnv × BlockEnv) (roots : Array (Expr × List Name))
    (before collectedState after : BlockState) (collection : ExprTableCollection)
    (collected : rawRun (collectPreseedExprs roots.toList (#[], #[], {})) context before = (.ok collection, collectedState))
    (ordinary : before.p3MetaMode = false) (refsSound : RefIndexSound before) (univsSound : UnivIndexSound before)
    (canonExact : UniversePipeline.CanonCacheExact before)
    (wire : ∀ univ ∈ collection.2.1, (Ixon.canonUniv univ).wireWF)
    (ran : rawRun (preseedExprTables roots) context before = (.ok (), after)) :
    (∀ root ∈ roots, PreseedReferences.Covered
      (ExpressionState.lookupBinding context.1 (ExpressionState.bindingView before)) context.2.mutCtx after.refs root.1) ∧
    (∀ params level, PreseedUniverses.Present params collection.2.1 level →
      ∃ raw index, UniverseExact.lower params level = some raw ∧
        after.univsIndex.get? (Ixon.canonUniv raw) = some index ∧
        after.univs[index.toNat]? = some (Ixon.canonUniv raw)) := by
  have inserted := preseed_from_collection context roots before collectedState after collection collected ordinary refsSound univsSound canonExact wire ran
  have refCoverage := PreseedReferences.roots_initial context before collectedState roots.toList collection collected
  refine ⟨?_, ?_⟩
  · intro root member
    have covered := refCoverage root (by simpa using member)
    apply PreseedReferences.Covered.mono _ _ collection.1 after.refs ?_ root.1 covered
    intro address needed
    obtain ⟨index, _, atSlot⟩ := (inserted.2.2.2.2.1 address needed).slot inserted.2.2.1
    exact Array.mem_of_getElem? atSlot
  · intro params level present
    obtain ⟨raw, lowered, member⟩ := present
    obtain ⟨index, mapped, atSlot⟩ := (inserted.2.2.2.2.2 raw member).slot inserted.2.2.2.1
    exact ⟨raw, index, lowered, mapped, atSlot⟩

/-- Exact lowering chooses a single canonical lookup, including when a
parameter occurs more than once. This is a table property, not a successful
compilation premise. -/
def ExactSeeded (params : List Name) (level : Level) (state : BlockState) : Prop :=
  ∀ raw, UniverseExact.lower params level = some raw → state.univsIndex.contains (Ixon.canonUniv raw) = true

theorem exactSeeded_of_present (params : List Name) (level : Level) (univs : Array Ixon.Univ) (state : BlockState)
    (present : PreseedUniverses.Present params univs level)
    (inserted : ∀ raw ∈ univs, UnivPresent state (Ixon.canonUniv raw)) : ExactSeeded params level state := by
  intro raw lowered
  have member := present.value lowered
  obtain ⟨index, found⟩ := inserted raw member
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  change (state.univsIndex.get? (Ixon.canonUniv raw)).isSome = true
  rw [found]
  rfl

/-- The exact preseed condition supplies the production no-growth check
without asking for every representation of repeated parameter names. -/
theorem compileAndIntern_returns_exact (source : Level) (context : CompileEnv × BlockEnv) (before : BlockState)
    (rawExact : UniverseExact.CacheExact before) (canonExact : UniversePipeline.CanonCacheExact before)
    (tables : UniversePipeline.TablesSound before)
    (bounded : context.2.univCtx.length ≤ UInt64.size) (scope : UniverseMeaning.Scoped context.2.univCtx source)
    (room : before.univs.size + before.metaUnivs.size + 1 < UInt64.size)
    (seeded : ExactSeeded context.2.univCtx source before) :
    ∃ value after, rawRun (compileAndInternUnivCanon source) context before = (.ok value, after) := by
  obtain ⟨raw, middle, compiled, _, lowered⟩ := UniverseExact.compileUniv_total source context bounded scope before rawExact
  have rawFrame := UniversePipeline.compileUniv_frame source context before
  rw [compiled] at rawFrame
  have middleCanon := congrArg UniversePipeline.CanonCacheExact rawFrame
  obtain ⟨canonicalState, canonical, _, canonFrame⟩ :=
    UniversePipeline.canonUnivCached_correct raw context middle (middleCanon.mpr canonExact)
  have sameTablesRaw := congrArg UniversePipeline.TablesSound rawFrame
  have sameTablesCanon := congrArg UniversePipeline.TablesSound canonFrame
  have finalTables := sameTablesCanon.mpr (sameTablesRaw.mpr tables)
  have sameSizesRaw := congrArg (fun state => state.univs.size + state.metaUnivs.size) rawFrame
  have sameSizesCanon := congrArg (fun state => state.univs.size + state.metaUnivs.size) canonFrame
  have sameSizes : canonicalState.univs.size + canonicalState.metaUnivs.size = before.univs.size + before.metaUnivs.size :=
    sameSizesCanon.trans sameSizesRaw
  have sameSeededRaw := congrArg (ExactSeeded context.2.univCtx source) rawFrame
  have sameSeededCanon := congrArg (ExactSeeded context.2.univCtx source) canonFrame
  have prepared : ExactSeeded context.2.univCtx source canonicalState := sameSeededCanon.mpr (sameSeededRaw.mpr seeded)
  obtain ⟨value, after, interned⟩ := UniversePipeline.internCanonical_returns raw (Ixon.canonUniv raw) context canonicalState
    finalTables (by omega) (fun _ _ => prepared raw lowered)
  refine ⟨value, after, ?_⟩
  rw [UniversePipeline.compileAndInternUnivCanon_eq, rawRun_bind, compiled]
  dsimp only
  rw [rawRun_bind, canonical]
  exact interned

end Ix.CompileCert.PreseedInsertion
