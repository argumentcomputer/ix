import Ix.Compile.Verify.CompileMeta
import Std.Data.HashMap.Lemmas

/-!
# Strict metadata side-store coherence

The semantic metadata refinement deliberately observes only emitted addresses
and the expression arena.  This module adds the stronger, presentation-facing
layer: every name and blob touched by metadata compilation is recovered from
the corresponding `blockNames` or `blockBlobs` lookup.

The hash assumptions are scoped to the finite values already present in the
input stores together with the exact values touched by the current metadata
map.  They are not premises of anonymous expression preservation.
-/

namespace Ix.Compile.Verify

local instance : LawfulBEq ByteArray where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg ByteArray.mk (eq_of_beq h)
  rfl {bytes} := beq_self_eq_true bytes.data

local instance : LawfulBEq Address where
  eq_of_beq {left right} h := by
    cases left
    cases right
    exact congrArg Address.mk (eq_of_beq h)
  rfl {addr} := by
    cases addr
    exact beq_self_eq_true (α := ByteArray) _

local instance : LawfulHashable Address where
  hash_eq left right h := by rw [eq_of_beq h]

/-- The concrete name values and blob payloads touched by one metadata
operation.  Lists intentionally retain duplicates: this is an exact traversal
support, not a normalized set, and membership is the proof-facing view. -/
structure MetaStoreItems where
  names : List Ix.Name := []
  blobs : List ByteArray := []

namespace MetaStoreItems

def append (left right : MetaStoreItems) : MetaStoreItems :=
  { names := left.names ++ right.names
    blobs := left.blobs ++ right.blobs }

instance : Append MetaStoreItems where
  append := MetaStoreItems.append

@[simp] theorem append_names (left right : MetaStoreItems) :
    (left ++ right).names = left.names ++ right.names := rfl

@[simp] theorem append_blobs (left right : MetaStoreItems) :
    (left ++ right).blobs = left.blobs ++ right.blobs := rfl

def concat (items : List MetaStoreItems) : MetaStoreItems :=
  items.foldr (· ++ ·) {}

theorem concat_singletonBlobs (values : List String) :
    concat (values.map fun value =>
      ({ blobs := [value.toUTF8] } : MetaStoreItems)) =
      { blobs := values.map String.toUTF8 } := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    change ({ blobs := [value.toUTF8] } : MetaStoreItems) ++
      concat (values.map fun item =>
        ({ blobs := [item.toUTF8] } : MetaStoreItems)) =
      { blobs := value.toUTF8 :: values.map String.toUTF8 }
    rw [ih]
    rfl

end MetaStoreItems

/-- Exact stores touched by recursively compiling one hierarchical name. -/
def compileNameStoreItems : Ix.Name → MetaStoreItems
  | .anonymous hash => { names := [.anonymous hash] }
  | .str parent value hash =>
    { names := [.str parent value hash] } ++
      { blobs := [value.toUTF8] } ++ compileNameStoreItems parent
  | .num parent value hash =>
    { names := [.num parent value hash] } ++ compileNameStoreItems parent

def substringStoreItems (source : Ix.Substring) : MetaStoreItems :=
  { blobs := [source.str.toUTF8] }

def sourceInfoStoreItems : Ix.SourceInfo → MetaStoreItems
  | .original leading _ trailing _ =>
    substringStoreItems leading ++ substringStoreItems trailing
  | .synthetic _ _ _ => {}
  | .none => {}

def syntaxPreresolvedStoreItems : Ix.SyntaxPreresolved → MetaStoreItems
  | .namespace name => compileNameStoreItems name
  | .decl name aliases =>
    compileNameStoreItems name ++
      { blobs := aliases.toList.map String.toUTF8 }

/-- Exact recursive support of the syntax serializer, excluding the final
serialized syntax value itself (which is inserted by `compileDataValue`). -/
def syntaxStoreItems (source : Ix.Syntax) : MetaStoreItems :=
  match source with
  | .missing => {}
  | .node info kind args =>
    compileNameStoreItems kind ++ sourceInfoStoreItems info ++
      MetaStoreItems.concat
        (args.attach.toList.map fun arg => syntaxStoreItems arg.1)
  | .atom info value =>
    sourceInfoStoreItems info ++ { blobs := [value.toUTF8] }
  | .ident info rawValue value preresolved =>
    compileNameStoreItems value ++ sourceInfoStoreItems info ++
      substringStoreItems rawValue ++
      MetaStoreItems.concat
        (preresolved.toList.map syntaxPreresolvedStoreItems)
termination_by sizeOf source
decreasing_by
  simp_wf
  exact Nat.lt_trans (Array.sizeOf_lt_of_mem arg.property) (by omega)

/-- Exact support of one metadata value, including its final scalar or syntax
blob when the production `compileDataValue` branch inserts one. -/
def dataValueStoreItems : Ix.DataValue → MetaStoreItems
  | .ofString value => { blobs := [value.toUTF8] }
  | .ofBool _ => {}
  | .ofName value => compileNameStoreItems value
  | .ofNat value => { blobs := [ByteArray.mk (Nat.toBytesLE value)] }
  | .ofInt value => { blobs := [Ix.CompileM.serializeIxInt value] }
  | .ofSyntax value =>
    syntaxStoreItems value ++ { blobs := [serializeIxSyntaxRef value] }

def kvEntryStoreItems (entry : Ix.Name × Ix.DataValue) : MetaStoreItems :=
  compileNameStoreItems entry.1 ++ dataValueStoreItems entry.2

/-- Exact finite traversal support of production `compileKVMap`. -/
def kvMapStoreItems (entries : Array (Ix.Name × Ix.DataValue)) :
    MetaStoreItems :=
  MetaStoreItems.concat (entries.toList.map kvEntryStoreItems)

/-- Predicates used to scope name- and blob-key faithfulness independently. -/
structure MetaStoreSupport where
  names : Ix.Name → Prop
  blobs : ByteArray → Prop

/-- The exact run support: values already physically present in the input
stores, plus values traversed or inserted by this metadata map. -/
def metaCompileSupport (before : Ix.CompileM.BlockState)
    (entries : Array (Ix.Name × Ix.DataValue)) : MetaStoreSupport :=
  let items := kvMapStoreItems entries
  { names := fun name =>
      (∃ addr, before.blockNames.get? addr = some name) ∨ name ∈ items.names
    blobs := fun bytes =>
      (∃ addr, before.blockBlobs.get? addr = some bytes) ∨ bytes ∈ items.blobs }

/-- Structural name equality is recoverable from equal digest keys on this
run's finite presentation support. -/
def NameKeyFaithfulOn (support : Ix.Name → Prop) : Prop :=
  ∀ {left right}, support left → support right →
    left.getHash = right.getHash → left = right

/-- Blob bytes are recoverable from equal content addresses on this run's
finite presentation support. -/
def BlobKeyFaithfulOn (support : ByteArray → Prop) : Prop :=
  ∀ {left right}, support left → support right →
    Address.blake3 left = Address.blake3 right → left = right

/-- The presentation-only collision premise.  Keeping its two fields
separate makes clear which kind of lookup a downstream theorem observes. -/
structure MetaKeyFaithfulOn (support : MetaStoreSupport) : Prop where
  names : NameKeyFaithfulOn support.names
  blobs : BlobKeyFaithfulOn support.blobs

/-- A predicate is represented by one finite (possibly duplicate-bearing)
list. -/
def FinitePredicate (support : α → Prop) : Prop :=
  ∃ values : List α, ∀ {value}, support value → value ∈ values

theorem metaCompileSupport_finite
    (before : Ix.CompileM.BlockState)
    (entries : Array (Ix.Name × Ix.DataValue)) :
    FinitePredicate (metaCompileSupport before entries).names ∧
      FinitePredicate (metaCompileSupport before entries).blobs := by
  let items := kvMapStoreItems entries
  constructor
  · refine ⟨before.blockNames.toList.map (·.2) ++ items.names, ?_⟩
    intro name hname
    rcases hname with ⟨addr, hlookup⟩ | hitem
    · apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨(addr, name), by simpa using hlookup, rfl⟩
    · exact List.mem_append_right _ hitem
  · refine ⟨before.blockBlobs.toList.map (·.2) ++ items.blobs, ?_⟩
    intro bytes hbytes
    rcases hbytes with ⟨addr, hlookup⟩ | hitem
    · apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨(addr, bytes), by simpa using hlookup, rfl⟩
    · exact List.mem_append_right _ hitem

/-- Every physical entry belongs to the declared run support and is stored
under the address computed from its value. -/
structure MetaStoreCovered (support : MetaStoreSupport)
    (state : Ix.CompileM.BlockState) : Prop where
  names : ∀ {addr name}, state.blockNames.get? addr = some name →
    support.names name ∧ name.getHash = addr
  blobs : ∀ {addr bytes}, state.blockBlobs.get? addr = some bytes →
    support.blobs bytes ∧ Address.blake3 bytes = addr

/-- All entries present before a transition remain exactly recoverable after
it.  This is stronger than map-domain monotonicity because it preserves the
associated value as well as the address. -/
structure MetaStoreExtends (before after : Ix.CompileM.BlockState) : Prop where
  names : ∀ {addr name}, before.blockNames.get? addr = some name →
    after.blockNames.get? addr = some name
  blobs : ∀ {addr bytes}, before.blockBlobs.get? addr = some bytes →
    after.blockBlobs.get? addr = some bytes

theorem MetaStoreExtends.refl (state : Ix.CompileM.BlockState) :
    MetaStoreExtends state state := ⟨id, id⟩

theorem MetaStoreExtends.trans {first second third : Ix.CompileM.BlockState}
    (hfirst : MetaStoreExtends first second)
    (hsecond : MetaStoreExtends second third) : MetaStoreExtends first third :=
  ⟨fun h => hsecond.names (hfirst.names h),
    fun h => hsecond.blobs (hfirst.blobs h)⟩

/-- A transition only adds values from `items`; any other final lookup was
already present with the same value. -/
structure MetaStoreDelta (before after : Ix.CompileM.BlockState)
    (items : MetaStoreItems) : Prop extends MetaStoreExtends before after where
  namesOnly : ∀ {addr name}, after.blockNames.get? addr = some name →
    before.blockNames.get? addr = some name ∨ name ∈ items.names
  blobsOnly : ∀ {addr bytes}, after.blockBlobs.get? addr = some bytes →
    before.blockBlobs.get? addr = some bytes ∨ bytes ∈ items.blobs

theorem MetaStoreDelta.refl (state : Ix.CompileM.BlockState) :
    MetaStoreDelta state state {} := by
  exact ⟨MetaStoreExtends.refl state, fun h => Or.inl h,
    fun h => Or.inl h⟩

theorem MetaStoreDelta.reflItems (state : Ix.CompileM.BlockState)
    (items : MetaStoreItems) : MetaStoreDelta state state items := by
  exact ⟨MetaStoreExtends.refl state, fun h => Or.inl h,
    fun h => Or.inl h⟩

theorem MetaStoreDelta.trans {first second third : Ix.CompileM.BlockState}
    {left right : MetaStoreItems}
    (hleft : MetaStoreDelta first second left)
    (hright : MetaStoreDelta second third right) :
    MetaStoreDelta first third (left ++ right) := by
  refine
    { toMetaStoreExtends := hleft.toMetaStoreExtends.trans
        hright.toMetaStoreExtends
      namesOnly := ?_
      blobsOnly := ?_ }
  · intro addr name hlookup
    rcases hright.namesOnly hlookup with hmiddle | hrightItem
    · rcases hleft.namesOnly hmiddle with hfirst | hleftItem
      · exact Or.inl hfirst
      · exact Or.inr (List.mem_append_left _ hleftItem)
    · exact Or.inr (List.mem_append_right _ hrightItem)
  · intro addr bytes hlookup
    rcases hright.blobsOnly hlookup with hmiddle | hrightItem
    · rcases hleft.blobsOnly hmiddle with hfirst | hleftItem
      · exact Or.inl hfirst
      · exact Or.inr (List.mem_append_left _ hleftItem)
    · exact Or.inr (List.mem_append_right _ hrightItem)

/-- Every listed value has its exact address-to-value lookup. -/
structure MetaItemsStored (state : Ix.CompileM.BlockState)
    (items : MetaStoreItems) : Prop where
  names : ∀ {name}, name ∈ items.names →
    state.blockNames.get? name.getHash = some name
  blobs : ∀ {bytes}, bytes ∈ items.blobs →
    state.blockBlobs.get? (Address.blake3 bytes) = some bytes

/-- The listed traversal values stay within the declared run support. -/
structure MetaItemsSupported (support : MetaStoreSupport)
    (items : MetaStoreItems) : Prop where
  names : ∀ {name}, name ∈ items.names → support.names name
  blobs : ∀ {bytes}, bytes ∈ items.blobs → support.blobs bytes

theorem MetaItemsStored.empty (state : Ix.CompileM.BlockState) :
    MetaItemsStored state {} := by
  constructor <;> simp

theorem MetaItemsStored.append {state : Ix.CompileM.BlockState}
    {left right : MetaStoreItems}
    (hleft : MetaItemsStored state left)
    (hright : MetaItemsStored state right) :
    MetaItemsStored state (left ++ right) := by
  constructor
  · intro name hname
    rcases List.mem_append.mp hname with hname | hname
    · exact hleft.names hname
    · exact hright.names hname
  · intro bytes hbytes
    rcases List.mem_append.mp hbytes with hbytes | hbytes
    · exact hleft.blobs hbytes
    · exact hright.blobs hbytes

theorem MetaItemsSupported.left {support : MetaStoreSupport}
    {left right : MetaStoreItems}
    (hsupported : MetaItemsSupported support (left ++ right)) :
    MetaItemsSupported support left := by
  constructor
  · exact fun h => hsupported.names (List.mem_append_left _ h)
  · exact fun h => hsupported.blobs (List.mem_append_left _ h)

theorem MetaItemsSupported.right {support : MetaStoreSupport}
    {left right : MetaStoreItems}
    (hsupported : MetaItemsSupported support (left ++ right)) :
    MetaItemsSupported support right := by
  constructor
  · exact fun h => hsupported.names (List.mem_append_right _ h)
  · exact fun h => hsupported.blobs (List.mem_append_right _ h)

theorem MetaItemsStored.of_extends {before after : Ix.CompileM.BlockState}
    {items : MetaStoreItems} (hextends : MetaStoreExtends before after)
    (hstored : MetaItemsStored before items) : MetaItemsStored after items := by
  exact
    { names := fun h => hextends.names (hstored.names h)
      blobs := fun h => hextends.blobs (hstored.blobs h) }

/-- Strict name-store closure: whenever a full name is present, every one of
its ancestor names and string-component blobs is also exactly recoverable.
This is the precondition required by production `compileName`'s early-return
branch. -/
structure StrictMetaStoreWF (support : MetaStoreSupport)
    (state : Ix.CompileM.BlockState) : Prop extends MetaStoreCovered support state where
  nameClosure : ∀ {addr name}, state.blockNames.get? addr = some name →
    MetaItemsStored state (compileNameStoreItems name)

private def insertNameState (state : Ix.CompileM.BlockState)
    (name : Ix.Name) : Ix.CompileM.BlockState :=
  { state with blockNames := state.blockNames.insert name.getHash name }

private def insertBlobStateStrict (state : Ix.CompileM.BlockState)
    (bytes : ByteArray) : Ix.CompileM.BlockState :=
  { state with
    blockBlobs := state.blockBlobs.insert (Address.blake3 bytes) bytes }

private theorem insertName_covered_delta
    {support : MetaStoreSupport} {state : Ix.CompileM.BlockState}
    (hfaithful : NameKeyFaithfulOn support.names)
    (hstate : MetaStoreCovered support state) {name : Ix.Name}
    (hname : support.names name) :
    MetaStoreCovered support (insertNameState state name) ∧
      MetaStoreDelta state (insertNameState state name)
        { names := [name] } := by
  constructor
  · constructor
    · intro addr found hfound
      simp only [insertNameState, Std.HashMap.get?_insert] at hfound
      split at hfound
      next heq =>
        have haddr : name.getHash = addr := eq_of_beq heq
        have hvalue : found = name := Option.some.inj hfound |>.symm
        subst found
        exact ⟨hname, haddr⟩
      next _ => exact hstate.names hfound
    · intro addr bytes hfound
      exact hstate.blobs hfound
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      · intro addr old hold
        simp only [insertNameState, Std.HashMap.get?_insert]
        split
        next heq =>
          have haddr : name.getHash = addr := eq_of_beq heq
          obtain ⟨holdSupport, holdKey⟩ := hstate.names hold
          have hsame : name = old :=
            hfaithful hname holdSupport (haddr.trans holdKey.symm)
          simp [hsame]
        next _ => exact hold
      · exact fun h => h
    · intro addr found hfound
      simp only [insertNameState, Std.HashMap.get?_insert] at hfound
      split at hfound
      next _ =>
        have hvalue : found = name := Option.some.inj hfound |>.symm
        subst found
        exact Or.inr (by simp)
      next _ => exact Or.inl hfound
    · exact fun h => Or.inl h

private theorem insertBlob_covered_delta
    {support : MetaStoreSupport} {state : Ix.CompileM.BlockState}
    (hfaithful : BlobKeyFaithfulOn support.blobs)
    (hstate : MetaStoreCovered support state) {bytes : ByteArray}
    (hbytes : support.blobs bytes) :
    MetaStoreCovered support (insertBlobStateStrict state bytes) ∧
      MetaStoreDelta state (insertBlobStateStrict state bytes)
        { blobs := [bytes] } := by
  constructor
  · constructor
    · intro addr name hfound
      exact hstate.names hfound
    · intro addr found hfound
      simp only [insertBlobStateStrict, Std.HashMap.get?_insert] at hfound
      split at hfound
      next heq =>
        have haddr : Address.blake3 bytes = addr := eq_of_beq heq
        have hvalue : found = bytes := Option.some.inj hfound |>.symm
        subst found
        exact ⟨hbytes, haddr⟩
      next _ => exact hstate.blobs hfound
  · refine ⟨?_, ?_, ?_⟩
    · constructor
      · exact fun h => h
      · intro addr old hold
        simp only [insertBlobStateStrict, Std.HashMap.get?_insert]
        split
        next heq =>
          have haddr : Address.blake3 bytes = addr := eq_of_beq heq
          obtain ⟨holdSupport, holdKey⟩ := hstate.blobs hold
          have hsame : bytes = old :=
            hfaithful hbytes holdSupport (haddr.trans holdKey.symm)
          simp [hsame]
        next _ => exact hold
    · exact fun h => Or.inl h
    · intro addr found hfound
      simp only [insertBlobStateStrict, Std.HashMap.get?_insert] at hfound
      split at hfound
      next _ =>
        have hvalue : found = bytes := Option.some.inj hfound |>.symm
        subst found
        exact Or.inr (by simp)
      next _ => exact Or.inl hfound

private theorem sizeOf_le_of_mem_compileNameStoreItems
    {root candidate : Ix.Name}
    (hmem : candidate ∈ (compileNameStoreItems root).names) :
    sizeOf candidate ≤ sizeOf root := by
  induction root with
  | anonymous hash =>
    simp [compileNameStoreItems] at hmem
    subst candidate
    exact Nat.le_refl _
  | str parent value hash ih =>
    simp [compileNameStoreItems] at hmem
    rcases hmem with rfl | hmem
    · exact Nat.le_refl _
    · have hle := ih hmem
      exact Nat.le_trans hle (Nat.le_of_lt (by simp_wf; omega))
  | num parent value hash ih =>
    simp [compileNameStoreItems] at hmem
    rcases hmem with rfl | hmem
    · exact Nat.le_refl _
    · have hle := ih hmem
      exact Nat.le_trans hle (Nat.le_of_lt (by simp_wf; omega))

/-- Present names in the relevant ancestor chain must already have a complete
closure.  `StrictMetaStoreWF` supplies this at the public boundary; the
recursive proof preserves it for the parent while a child is temporarily
inserted before that parent. -/
def CompileNameSafe (state : Ix.CompileM.BlockState) (root : Ix.Name) : Prop :=
  ∀ {candidate}, candidate ∈ (compileNameStoreItems root).names →
    state.blockNames.get? candidate.getHash = some candidate →
    MetaItemsStored state (compileNameStoreItems candidate)

private theorem lookup_name_of_contains
    {support : MetaStoreSupport} {state : Ix.CompileM.BlockState}
    (hfaithful : NameKeyFaithfulOn support.names)
    (hstate : MetaStoreCovered support state) {name : Ix.Name}
    (hname : support.names name)
    (hpresent : state.blockNames.contains name.getHash = true) :
    state.blockNames.get? name.getHash = some name := by
  cases hlookup : state.blockNames.get? name.getHash with
  | none =>
    change state.blockNames[name.getHash]? = none at hlookup
    have habsent : state.blockNames.contains name.getHash = false := by
      rw [Std.HashMap.contains_eq_isSome_getElem?, hlookup]
      rfl
    simp [habsent] at hpresent
  | some found =>
    obtain ⟨hfound, hkey⟩ := hstate.names hlookup
    have hsame : found = name :=
      hfaithful hfound hname hkey
    subst found
    rfl

private structure CompileNameStoreResult (support : MetaStoreSupport)
    (before after : Ix.CompileM.BlockState) (root : Ix.Name) : Prop where
  covered : MetaStoreCovered support after
  delta : MetaStoreDelta before after (compileNameStoreItems root)
  stored : MetaItemsStored after (compileNameStoreItems root)
  touchedClosed : ∀ {name}, name ∈ (compileNameStoreItems root).names →
    MetaItemsStored after (compileNameStoreItems name)

private theorem compileName_store_result
    {support : MetaStoreSupport} (hfaithful : MetaKeyFaithfulOn support)
    (root : Ix.Name) (state : Ix.CompileM.BlockState)
    (hstate : MetaStoreCovered support state)
    (hsupported : MetaItemsSupported support (compileNameStoreItems root))
    (hsafe : CompileNameSafe state root) :
    CompileNameStoreResult support state (state.compileName root) root := by
  induction root generalizing state with
  | anonymous hash =>
    rw [Ix.CompileM.BlockState.compileName.eq_1]
    split
    next hpresent =>
      have hrootSupport : support.names (.anonymous hash) :=
        hsupported.names (by simp [compileNameStoreItems])
      have hlookup := lookup_name_of_contains hfaithful.names hstate
        hrootSupport hpresent
      have hstored := hsafe (by simp [compileNameStoreItems]) hlookup
      exact
        { covered := hstate
          delta := MetaStoreDelta.reflItems state _
          stored := hstored
          touchedClosed := by
            intro name hname
            have hsame : name = .anonymous hash := by
              simpa [compileNameStoreItems] using hname
            subst name
            exact hstored }
    next _ =>
      change CompileNameStoreResult support state
        (insertNameState state (.anonymous hash)) (.anonymous hash)
      obtain ⟨hcovered, hdelta⟩ := insertName_covered_delta
        (name := .anonymous hash) hfaithful.names hstate
        (hsupported.names (by simp [compileNameStoreItems]))
      have hstored : MetaItemsStored (insertNameState state (.anonymous hash))
          (compileNameStoreItems (.anonymous hash)) := by
        constructor
        · intro name hname
          have hsame : name = .anonymous hash := by
            simpa [compileNameStoreItems] using hname
          subst name
          simp [insertNameState]
        · simp [compileNameStoreItems]
      exact
        { covered := hcovered
          delta := by simpa [compileNameStoreItems] using hdelta
          stored := hstored
          touchedClosed := by
            intro name hname
            have hsame : name = .anonymous hash := by
              simpa [compileNameStoreItems] using hname
            subst name
            exact hstored }
  | str parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    next hpresent =>
      have hrootSupport : support.names (.str parent value hash) :=
        hsupported.names (by simp [compileNameStoreItems])
      have hlookup := lookup_name_of_contains hfaithful.names hstate
        hrootSupport hpresent
      have hstored := hsafe (by simp [compileNameStoreItems]) hlookup
      refine
        { covered := hstate
          delta := MetaStoreDelta.reflItems state _
          stored := hstored
          touchedClosed := ?_ }
      intro name hname
      exact hsafe hname (hstored.names hname)
    next _ =>
      let root : Ix.Name := .str parent value hash
      let nameState := insertNameState state root
      let blobState := insertBlobStateStrict nameState value.toUTF8
      have hrootSupport : support.names root :=
        hsupported.names (by simp [root, compileNameStoreItems])
      have hblobSupport : support.blobs value.toUTF8 :=
        hsupported.blobs (by simp [compileNameStoreItems])
      obtain ⟨hnameCovered, hnameDelta⟩ :=
        insertName_covered_delta hfaithful.names hstate hrootSupport
      obtain ⟨hblobCovered, hblobDelta⟩ :=
        insertBlob_covered_delta hfaithful.blobs hnameCovered hblobSupport
      have hparentSupported :
          MetaItemsSupported support (compileNameStoreItems parent) := by
        constructor
        · intro name hname
          exact hsupported.names (by
            simp [compileNameStoreItems, hname])
        · intro bytes hbytes
          exact hsupported.blobs (by
            simp [compileNameStoreItems, hbytes])
      have hparentSafe : CompileNameSafe blobState parent := by
        intro candidate hcandidate hlookup
        have hcandidateSupport := hparentSupported.names hcandidate
        have hlookupName : nameState.blockNames.get?
            candidate.getHash = some candidate := by
          exact hlookup
        simp only [nameState, insertNameState,
          Std.HashMap.get?_insert] at hlookupName
        split at hlookupName
        next heq =>
          have hhash : root.getHash = candidate.getHash := eq_of_beq heq
          have hsame : root = candidate :=
            hfaithful.names hrootSupport hcandidateSupport hhash
          have hle := sizeOf_le_of_mem_compileNameStoreItems hcandidate
          have hstrict : sizeOf parent < sizeOf root := by
            simp_wf
            omega
          subst candidate
          omega
        next _ =>
          have hcandidateInRoot :
              candidate ∈ (compileNameStoreItems root).names := by
            simp [root, compileNameStoreItems, hcandidate]
          have holdStored := hsafe hcandidateInRoot hlookupName
          exact MetaItemsStored.of_extends
            (hnameDelta.toMetaStoreExtends.trans
              hblobDelta.toMetaStoreExtends) holdStored
      have hparentResult := ih blobState hblobCovered hparentSupported hparentSafe
      have hprefixDelta := hnameDelta.trans hblobDelta
      have htotalDelta := hprefixDelta.trans hparentResult.delta
      have hrootName :
          (blobState.compileName parent).blockNames.get? root.getHash =
            some root := by
        apply hparentResult.delta.names
        apply hblobDelta.names
        simp [insertNameState]
      have hrootBlob :
          (blobState.compileName parent).blockBlobs.get?
              (Address.blake3 value.toUTF8) = some value.toUTF8 := by
        apply hparentResult.delta.blobs
        simp [blobState, insertBlobStateStrict]
      have hrootStored : MetaItemsStored (blobState.compileName parent)
          (compileNameStoreItems root) := by
        constructor
        · intro name hname
          simp [root, compileNameStoreItems] at hname
          rcases hname with hsame | hname
          · subst name
            exact hrootName
          · exact hparentResult.stored.names hname
        · intro bytes hbytes
          simp [root, compileNameStoreItems] at hbytes
          rcases hbytes with hsame | hbytes
          · subst bytes
            exact hrootBlob
          · exact hparentResult.stored.blobs hbytes
      refine
        { covered := hparentResult.covered
          delta := ?_
          stored := hrootStored
          touchedClosed := ?_ }
      · change MetaStoreDelta state (blobState.compileName parent)
          ({ names := [root] } ++ { blobs := [value.toUTF8] } ++
            compileNameStoreItems parent)
        exact htotalDelta
      · intro name hname
        simp [compileNameStoreItems] at hname
        rcases hname with hsame | hname
        · subst name
          exact hrootStored
        · exact hparentResult.touchedClosed hname


  | num parent value hash ih =>
    simp only [Ix.CompileM.BlockState.compileName]
    split
    next hpresent =>
      have hrootSupport : support.names (.num parent value hash) :=
        hsupported.names (by simp [compileNameStoreItems])
      have hlookup := lookup_name_of_contains hfaithful.names hstate
        hrootSupport hpresent
      have hstored := hsafe (by simp [compileNameStoreItems]) hlookup
      refine
        { covered := hstate
          delta := MetaStoreDelta.reflItems state _
          stored := hstored
          touchedClosed := ?_ }
      intro name hname
      exact hsafe hname (hstored.names hname)
    next _ =>
      let root : Ix.Name := .num parent value hash
      let nameState := insertNameState state root
      have hrootSupport : support.names root :=
        hsupported.names (by simp [root, compileNameStoreItems])
      obtain ⟨hnameCovered, hnameDelta⟩ :=
        insertName_covered_delta hfaithful.names hstate hrootSupport
      have hparentSupported :
          MetaItemsSupported support (compileNameStoreItems parent) := by
        constructor
        · intro name hname
          exact hsupported.names (by
            simp [compileNameStoreItems, hname])
        · intro bytes hbytes
          exact hsupported.blobs (by
            simpa [root, compileNameStoreItems] using hbytes)
      have hparentSafe : CompileNameSafe nameState parent := by
        intro candidate hcandidate hlookup
        have hcandidateSupport := hparentSupported.names hcandidate
        simp only [nameState, insertNameState,
          Std.HashMap.get?_insert] at hlookup
        split at hlookup
        next heq =>
          have hhash : root.getHash = candidate.getHash := eq_of_beq heq
          have hsame : root = candidate :=
            hfaithful.names hrootSupport hcandidateSupport hhash
          have hle := sizeOf_le_of_mem_compileNameStoreItems hcandidate
          have hstrict : sizeOf parent < sizeOf root := by
            simp_wf
            omega
          subst candidate
          omega
        next _ =>
          have hcandidateInRoot :
              candidate ∈ (compileNameStoreItems root).names := by
            simp [root, compileNameStoreItems, hcandidate]
          have holdStored := hsafe hcandidateInRoot hlookup
          exact MetaItemsStored.of_extends
            hnameDelta.toMetaStoreExtends holdStored
      have hparentResult := ih nameState hnameCovered hparentSupported hparentSafe
      have htotalDelta := hnameDelta.trans hparentResult.delta
      have hrootName :
          (nameState.compileName parent).blockNames.get? root.getHash =
            some root := by
        apply hparentResult.delta.names
        simp [nameState, insertNameState]
      have hrootStored : MetaItemsStored (nameState.compileName parent)
          (compileNameStoreItems root) := by
        constructor
        · intro name hname
          simp [root, compileNameStoreItems] at hname
          rcases hname with hsame | hname
          · subst name
            exact hrootName
          · exact hparentResult.stored.names hname
        · intro bytes hbytes
          exact hparentResult.stored.blobs (by
            simpa [root, compileNameStoreItems] using hbytes)
      refine
        { covered := hparentResult.covered
          delta := ?_
          stored := hrootStored
          touchedClosed := ?_ }
      · change MetaStoreDelta state (nameState.compileName parent)
          ({ names := [root] } ++ compileNameStoreItems parent)
        exact htotalDelta
      · intro name hname
        simp [compileNameStoreItems] at hname
        rcases hname with hsame | hname
        · subst name
          exact hrootStored
        · exact hparentResult.touchedClosed hname

/-- Production name compilation establishes every name/substring lookup in
the hierarchical name and preserves strict coherence of all preexisting
entries. -/
theorem BlockState_compileName_strict
    {support : MetaStoreSupport} {state : Ix.CompileM.BlockState}
    (hfaithful : MetaKeyFaithfulOn support) (name : Ix.Name)
    (hstate : StrictMetaStoreWF support state)
    (hsupported : MetaItemsSupported support (compileNameStoreItems name)) :
    StrictMetaStoreWF support (state.compileName name) ∧
      MetaStoreDelta state (state.compileName name)
        (compileNameStoreItems name) ∧
      MetaItemsStored (state.compileName name)
        (compileNameStoreItems name) := by
  have hsafe : CompileNameSafe state name := by
    intro candidate _ hlookup
    exact hstate.nameClosure hlookup
  have hresult := compileName_store_result hfaithful name state
    hstate.toMetaStoreCovered hsupported hsafe
  have hstrict : StrictMetaStoreWF support (state.compileName name) := by
    refine
      { toMetaStoreCovered := hresult.covered
        nameClosure := ?_ }
    intro addr stored hlookup
    rcases hresult.delta.namesOnly hlookup with hold | htouched
    · exact MetaItemsStored.of_extends hresult.delta.toMetaStoreExtends
        (hstate.nameClosure hold)
    · exact hresult.touchedClosed htouched
  exact ⟨hstrict, hresult.delta, hresult.stored⟩

private theorem insertBlob_strict
    {support : MetaStoreSupport} {state : Ix.CompileM.BlockState}
    (hfaithful : MetaKeyFaithfulOn support)
    (hstate : StrictMetaStoreWF support state) {bytes : ByteArray}
    (hbytes : support.blobs bytes) :
    StrictMetaStoreWF support (insertBlobStateStrict state bytes) ∧
      MetaStoreDelta state (insertBlobStateStrict state bytes)
        { blobs := [bytes] } ∧
      MetaItemsStored (insertBlobStateStrict state bytes)
        { blobs := [bytes] } := by
  obtain ⟨hcovered, hdelta⟩ := insertBlob_covered_delta
    hfaithful.blobs hstate.toMetaStoreCovered hbytes
  have hstrict : StrictMetaStoreWF support
      (insertBlobStateStrict state bytes) :=
    { toMetaStoreCovered := hcovered
      nameClosure := fun hlookup =>
        MetaItemsStored.of_extends hdelta.toMetaStoreExtends
          (hstate.nameClosure hlookup) }
  have hstored : MetaItemsStored (insertBlobStateStrict state bytes)
      { blobs := [bytes] } := by
    constructor
    · simp
    · intro found hfound
      have hsame : found = bytes := by simpa using hfound
      subst found
      simp [insertBlobStateStrict]
  exact ⟨hstrict, hdelta, hstored⟩

/-- Composable strict result for one metadata-only state transition. -/
private structure StrictMetaStep (support : MetaStoreSupport)
    (before after : Ix.CompileM.BlockState) (items : MetaStoreItems) : Prop where
  strict : StrictMetaStoreWF support after
  delta : MetaStoreDelta before after items
  stored : MetaItemsStored after items

private theorem StrictMetaStep.refl {support : MetaStoreSupport}
    {state : Ix.CompileM.BlockState} (hstate : StrictMetaStoreWF support state) :
    StrictMetaStep support state state {} :=
  ⟨hstate, MetaStoreDelta.refl state, MetaItemsStored.empty state⟩

private theorem StrictMetaStep.trans
    {support : MetaStoreSupport} {first second third : Ix.CompileM.BlockState}
    {left right : MetaStoreItems}
    (hleft : StrictMetaStep support first second left)
    (hright : StrictMetaStep support second third right) :
    StrictMetaStep support first third (left ++ right) :=
  { strict := hright.strict
    delta := hleft.delta.trans hright.delta
    stored := (MetaItemsStored.of_extends
      hright.delta.toMetaStoreExtends hleft.stored).append hright.stored }

private theorem run_bind_strict (compileEnv : Ix.CompileM.CompileEnv)
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

/-- State-only strict execution fact.  The result value remains existential;
the public theorems identify it using the independent exact-encoding
refinement from `CompileMeta`. -/
private def StrictMetaRun (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (support : MetaStoreSupport)
    (state : Ix.CompileM.BlockState) (action : Ix.CompileM.CompileM α)
    (items : MetaStoreItems) : Prop :=
  ∃ value state',
    Ix.CompileM.CompileM.run compileEnv blockEnv state action =
      .ok (value, state') ∧ StrictMetaStep support state state' items

private theorem compileName_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    {state : Ix.CompileM.BlockState} (hfaithful : MetaKeyFaithfulOn support)
    (name : Ix.Name) (hstate : StrictMetaStoreWF support state)
    (hsupported : MetaItemsSupported support (compileNameStoreItems name)) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.compileName name) (compileNameStoreItems name) := by
  obtain ⟨hstrict, hdelta, hstored⟩ :=
    BlockState_compileName_strict hfaithful name hstate hsupported
  exact ⟨(), state.compileName name, rfl, ⟨hstrict, hdelta, hstored⟩⟩

private theorem storeString_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    {state : Ix.CompileM.BlockState} (hfaithful : MetaKeyFaithfulOn support)
    (value : String) (hstate : StrictMetaStoreWF support state)
    (hsupported : support.blobs value.toUTF8) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.storeString value) { blobs := [value.toUTF8] } := by
  obtain ⟨hstrict, hdelta, hstored⟩ :=
    insertBlob_strict hfaithful hstate hsupported
  exact ⟨Address.blake3 value.toUTF8,
    insertBlobStateStrict state value.toUTF8, rfl,
    ⟨hstrict, hdelta, hstored⟩⟩

private theorem mapM_list_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (action : α → Ix.CompileM.CompileM β) (itemItems : α → MetaStoreItems)
    (hstep : ∀ (state : Ix.CompileM.BlockState) (item : α),
      StrictMetaStoreWF support state →
      MetaItemsSupported support (itemItems item) →
      StrictMetaRun compileEnv blockEnv support state (action item)
        (itemItems item))
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (items : List α)
    (hsupported : MetaItemsSupported support
      (MetaStoreItems.concat (items.map itemItems))) :
    StrictMetaRun compileEnv blockEnv support state (items.mapM action)
      (MetaStoreItems.concat (items.map itemItems)) := by
  induction items generalizing state with
  | nil =>
    exact ⟨[], state, rfl, StrictMetaStep.refl hstate⟩
  | cons item items ih =>
    have hheadSupported : MetaItemsSupported support (itemItems item) := by
      exact hsupported.left
    have htailSupported : MetaItemsSupported support
        (MetaStoreItems.concat (items.map itemItems)) := by
      exact hsupported.right
    obtain ⟨headValue, headState, hheadRun, hheadStep⟩ :=
      hstep state item hstate hheadSupported
    obtain ⟨tailValue, finalState, htailRun, htailStep⟩ :=
      ih headState hheadStep.strict htailSupported
    refine ⟨headValue :: tailValue, finalState, ?_,
      hheadStep.trans htailStep⟩
    rw [List.mapM_cons,
      run_bind_strict compileEnv blockEnv state _ _, hheadRun]
    simp only
    rw [run_bind_strict compileEnv blockEnv headState _ _, htailRun]
    rfl

private theorem mapM_array_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (action : α → Ix.CompileM.CompileM β) (itemItems : α → MetaStoreItems)
    (hstep : ∀ (state : Ix.CompileM.BlockState) (item : α),
      StrictMetaStoreWF support state →
      MetaItemsSupported support (itemItems item) →
      StrictMetaRun compileEnv blockEnv support state (action item)
        (itemItems item))
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (items : Array α)
    (hsupported : MetaItemsSupported support
      (MetaStoreItems.concat (items.toList.map itemItems))) :
    StrictMetaRun compileEnv blockEnv support state (items.mapM action)
      (MetaStoreItems.concat (items.toList.map itemItems)) := by
  obtain ⟨values, state', hrun, hstrict⟩ :=
    mapM_list_run_strict compileEnv blockEnv action itemItems hstep
      state hstate items.toList hsupported
  refine ⟨values.toArray, state', ?_, hstrict⟩
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind,
    run_bind_strict compileEnv blockEnv state _ _, hrun]
  rfl

private theorem serializeIxSubstring_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (source : Ix.Substring)
    (hsupported : MetaItemsSupported support (substringStoreItems source)) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.serializeIxSubstring source) (substringStoreItems source) := by
  have hbytes : support.blobs source.str.toUTF8 :=
    hsupported.blobs (by simp [substringStoreItems])
  obtain ⟨addr, state', hrun, hstep⟩ :=
    storeString_run_strict compileEnv blockEnv hfaithful source.str hstate hbytes
  refine ⟨addr.hash ++ Ix.CompileM.putTag0 source.startPos ++
      Ix.CompileM.putTag0 source.stopPos, state', ?_, ?_⟩
  · rw [Ix.CompileM.serializeIxSubstring,
      run_bind_strict compileEnv blockEnv state _ _, hrun]
    rfl
  · simpa [substringStoreItems] using hstep

private theorem serializeIxSourceInfo_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (source : Ix.SourceInfo)
    (hsupported : MetaItemsSupported support (sourceInfoStoreItems source)) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.serializeIxSourceInfo source) (sourceInfoStoreItems source) := by
  cases source with
  | original leading leadingPos trailing trailingPos =>
    obtain ⟨leadingBytes, leadingState, hleadingRun, hleadingStep⟩ :=
      serializeIxSubstring_run_strict compileEnv blockEnv hfaithful state hstate
        leading hsupported.left
    obtain ⟨trailingBytes, finalState, htrailingRun, htrailingStep⟩ :=
      serializeIxSubstring_run_strict compileEnv blockEnv hfaithful leadingState
        hleadingStep.strict trailing hsupported.right
    refine ⟨ByteArray.mk #[0] ++ leadingBytes ++
        Ix.CompileM.putTag0 leadingPos ++ trailingBytes ++
        Ix.CompileM.putTag0 trailingPos, finalState, ?_, ?_⟩
    · rw [Ix.CompileM.serializeIxSourceInfo,
        run_bind_strict compileEnv blockEnv state _ _, hleadingRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv leadingState _ _, htrailingRun]
      rfl
    · simpa [sourceInfoStoreItems] using hleadingStep.trans htrailingStep
  | synthetic start stop canonical =>
    exact ⟨_, state, rfl, by
      simpa [sourceInfoStoreItems] using StrictMetaStep.refl hstate⟩
  | none =>
    exact ⟨_, state, rfl, by
      simpa [sourceInfoStoreItems] using StrictMetaStep.refl hstate⟩

private theorem serializeIxSyntaxPreresolved_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (source : Ix.SyntaxPreresolved)
    (hsupported : MetaItemsSupported support
      (syntaxPreresolvedStoreItems source)) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.serializeIxSyntaxPreresolved source)
      (syntaxPreresolvedStoreItems source) := by
  cases source with
  | «namespace» name =>
    obtain ⟨value, state', hrun, hstep⟩ :=
      compileName_run_strict compileEnv blockEnv hfaithful name hstate
        (by simpa [syntaxPreresolvedStoreItems] using hsupported)
    refine ⟨ByteArray.mk #[0] ++ name.getHash.hash, state', ?_, ?_⟩
    · rw [Ix.CompileM.serializeIxSyntaxPreresolved,
        run_bind_strict compileEnv blockEnv state _ _, hrun]
      rfl
    · simpa [syntaxPreresolvedStoreItems] using hstep
  | decl name aliases =>
    have hnameSupported : MetaItemsSupported support
        (compileNameStoreItems name) := hsupported.left
    have haliasSupported : MetaItemsSupported support
        { blobs := aliases.toList.map String.toUTF8 } := hsupported.right
    obtain ⟨_, nameState, hnameRun, hnameStep⟩ :=
      compileName_run_strict compileEnv blockEnv hfaithful name hstate
        hnameSupported
    obtain ⟨aliasAddrs, finalState, haliasRun, haliasStep⟩ :=
      mapM_array_run_strict compileEnv blockEnv
        Ix.CompileM.storeString
        (fun aliasValue : String =>
          ({ blobs := [aliasValue.toUTF8] } : MetaStoreItems))
        (fun current aliasValue hcurrent halias =>
          storeString_run_strict compileEnv blockEnv hfaithful aliasValue hcurrent
            (halias.blobs (by simp)))
        nameState hnameStep.strict aliases (by
          rw [MetaStoreItems.concat_singletonBlobs]
          exact haliasSupported)
    refine ⟨ByteArray.mk #[1] ++ name.getHash.hash ++
        Ix.CompileM.putTag0 aliases.size ++
        aliasAddrs.foldl (fun bytes addr => bytes ++ addr.hash)
          ByteArray.empty,
      finalState, ?_, ?_⟩
    · rw [Ix.CompileM.serializeIxSyntaxPreresolved,
        run_bind_strict compileEnv blockEnv state _ _, hnameRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv nameState _ _, haliasRun]
      rfl
    · rw [MetaStoreItems.concat_singletonBlobs] at haliasStep
      simpa [syntaxPreresolvedStoreItems] using hnameStep.trans haliasStep

private theorem serializeIxSyntaxPreresolved_array_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (sources : Array Ix.SyntaxPreresolved)
    (hsupported : MetaItemsSupported support
      (MetaStoreItems.concat
        (sources.toList.map syntaxPreresolvedStoreItems))) :
    StrictMetaRun compileEnv blockEnv support state
      (sources.mapM Ix.CompileM.serializeIxSyntaxPreresolved)
      (MetaStoreItems.concat
        (sources.toList.map syntaxPreresolvedStoreItems)) := by
  exact mapM_array_run_strict compileEnv blockEnv
    Ix.CompileM.serializeIxSyntaxPreresolved syntaxPreresolvedStoreItems
    (fun current source hcurrent hsource =>
      serializeIxSyntaxPreresolved_run_strict compileEnv blockEnv hfaithful
        current hcurrent source hsource)
    state hstate sources hsupported

private theorem serializeIxSyntax_run_strict_effect
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (source : Ix.Syntax)
    (hsupported : MetaItemsSupported support (syntaxStoreItems source)) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.serializeIxSyntax source) (syntaxStoreItems source) := by
  induction source using Ix.CompileM.serializeIxSyntax.induct generalizing state with
  | case1 =>
    exact ⟨ByteArray.mk #[0], state, by
      rw [Ix.CompileM.serializeIxSyntax.eq_1]
      rfl, by
      simpa [syntaxStoreItems] using StrictMetaStep.refl hstate⟩
  | case2 info kind args ih =>
    rw [syntaxStoreItems.eq_2] at hsupported
    have hkindSupported : MetaItemsSupported support
        (compileNameStoreItems kind) := hsupported.left.left
    have hinfoSupported : MetaItemsSupported support
        (sourceInfoStoreItems info) := hsupported.left.right
    have hargsSupported : MetaItemsSupported support
        (MetaStoreItems.concat
          (args.attach.toList.map fun arg => syntaxStoreItems arg.1)) :=
      hsupported.right
    obtain ⟨_, nameState, hnameRun, hnameStep⟩ :=
      compileName_run_strict compileEnv blockEnv hfaithful kind hstate
        hkindSupported
    obtain ⟨infoBytes, infoState, hinfoRun, hinfoStep⟩ :=
      serializeIxSourceInfo_run_strict compileEnv blockEnv hfaithful nameState
        hnameStep.strict info hinfoSupported
    obtain ⟨serializedArgs, finalState, hargsRun, hargsStep⟩ :=
      mapM_array_run_strict compileEnv blockEnv
        (fun arg : { child // child ∈ args } =>
          Ix.CompileM.serializeIxSyntax arg.1)
        (fun arg : { child // child ∈ args } => syntaxStoreItems arg.1)
        (fun current arg hcurrent harg => ih arg current hcurrent harg)
        infoState hinfoStep.strict args.attach hargsSupported
    refine ⟨ByteArray.mk #[1] ++ infoBytes ++ kind.getHash.hash ++
        Ix.CompileM.putTag0 args.size ++
        serializedArgs.foldl (fun bytes arg => bytes ++ arg) ByteArray.empty,
      finalState, ?_, ?_⟩
    · rw [Ix.CompileM.serializeIxSyntax.eq_2,
        run_bind_strict compileEnv blockEnv state _ _, hnameRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv nameState _ _, hinfoRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv infoState _ _, hargsRun]
      rfl
    · simpa [syntaxStoreItems] using
        (hnameStep.trans hinfoStep).trans hargsStep
  | case3 info value =>
    rw [syntaxStoreItems.eq_3] at hsupported
    have hinfoSupported : MetaItemsSupported support
        (sourceInfoStoreItems info) := hsupported.left
    have hvalueSupported : support.blobs value.toUTF8 :=
      hsupported.right.blobs (by simp)
    obtain ⟨infoBytes, infoState, hinfoRun, hinfoStep⟩ :=
      serializeIxSourceInfo_run_strict compileEnv blockEnv hfaithful state
        hstate info hinfoSupported
    obtain ⟨valueAddr, finalState, hvalueRun, hvalueStep⟩ :=
      storeString_run_strict compileEnv blockEnv hfaithful value
        hinfoStep.strict hvalueSupported
    refine ⟨ByteArray.mk #[2] ++ infoBytes ++ valueAddr.hash,
      finalState, ?_, ?_⟩
    · rw [Ix.CompileM.serializeIxSyntax.eq_3,
        run_bind_strict compileEnv blockEnv state _ _, hinfoRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv infoState _ _, hvalueRun]
      rfl
    · simpa [syntaxStoreItems] using hinfoStep.trans hvalueStep
  | case4 info rawValue value preresolved =>
    rw [syntaxStoreItems.eq_4] at hsupported
    have hnameSupported : MetaItemsSupported support
        (compileNameStoreItems value) := hsupported.left.left.left
    have hinfoSupported : MetaItemsSupported support
        (sourceInfoStoreItems info) := hsupported.left.left.right
    have hrawSupported : MetaItemsSupported support
        (substringStoreItems rawValue) := hsupported.left.right
    have hpreSupported : MetaItemsSupported support
        (MetaStoreItems.concat
          (preresolved.toList.map syntaxPreresolvedStoreItems)) :=
      hsupported.right
    obtain ⟨_, nameState, hnameRun, hnameStep⟩ :=
      compileName_run_strict compileEnv blockEnv hfaithful value hstate
        hnameSupported
    obtain ⟨infoBytes, infoState, hinfoRun, hinfoStep⟩ :=
      serializeIxSourceInfo_run_strict compileEnv blockEnv hfaithful nameState
        hnameStep.strict info hinfoSupported
    obtain ⟨rawBytes, rawState, hrawRun, hrawStep⟩ :=
      serializeIxSubstring_run_strict compileEnv blockEnv hfaithful infoState
        hinfoStep.strict rawValue hrawSupported
    obtain ⟨serializedPres, finalState, hpreRun, hpreStep⟩ :=
      serializeIxSyntaxPreresolved_array_run_strict compileEnv blockEnv
        hfaithful rawState hrawStep.strict preresolved hpreSupported
    refine ⟨ByteArray.mk #[3] ++ infoBytes ++ rawBytes ++
        value.getHash.hash ++ Ix.CompileM.putTag0 preresolved.size ++
        serializedPres.foldl (fun bytes pr => bytes ++ pr) ByteArray.empty,
      finalState, ?_, ?_⟩
    · rw [Ix.CompileM.serializeIxSyntax.eq_4,
        run_bind_strict compileEnv blockEnv state _ _, hnameRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv nameState _ _, hinfoRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv infoState _ _, hrawRun]
      simp only
      rw [run_bind_strict compileEnv blockEnv rawState _ _, hpreRun]
      rfl
    · simpa [syntaxStoreItems] using
        ((hnameStep.trans hinfoStep).trans hrawStep).trans hpreStep

/-- Strict store effect paired with the already-proved exact syntax bytes. -/
private theorem serializeIxSyntax_run_strict
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (source : Ix.Syntax)
    (hsupported : MetaItemsSupported support (syntaxStoreItems source)) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.serializeIxSyntax source) =
        .ok (serializeIxSyntaxRef source, state') ∧
      StrictMetaStep support state state' (syntaxStoreItems source) := by
  obtain ⟨exactState, hexact, _⟩ :=
    serializeIxSyntax_run_refines compileEnv blockEnv state source
  obtain ⟨value, strictState, hstrictRun, hstep⟩ :=
    serializeIxSyntax_run_strict_effect compileEnv blockEnv hfaithful state
      hstate source hsupported
  rw [hexact] at hstrictRun
  have hpair : (serializeIxSyntaxRef source, exactState) =
      (value, strictState) := Except.ok.inj hstrictRun
  have hvalue := congrArg Prod.fst hpair
  have hstateEq := congrArg Prod.snd hpair
  change serializeIxSyntaxRef source = value at hvalue
  change exactState = strictState at hstateEq
  subst value
  subst strictState
  exact ⟨exactState, hexact, hstep⟩

private theorem compileDataValue_run_strict_effect
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (source : Ix.DataValue)
    (hsupported : MetaItemsSupported support (dataValueStoreItems source)) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.compileDataValue source) (dataValueStoreItems source) := by
  cases source with
  | ofString value =>
    have hbytes : support.blobs value.toUTF8 :=
      hsupported.blobs (by simp [dataValueStoreItems])
    obtain ⟨hstrict, hdelta, hstored⟩ :=
      insertBlob_strict hfaithful hstate hbytes
    exact ⟨.ofString (Address.blake3 value.toUTF8),
      insertBlobStateStrict state value.toUTF8, rfl, by
        simpa [dataValueStoreItems] using
          (show StrictMetaStep support state
            (insertBlobStateStrict state value.toUTF8)
            { blobs := [value.toUTF8] } from
              ⟨hstrict, hdelta, hstored⟩)⟩
  | ofBool value =>
    exact ⟨.ofBool value, state, rfl, by
      simpa [dataValueStoreItems] using StrictMetaStep.refl hstate⟩
  | ofName value =>
    obtain ⟨encoded, state', hrun, hstep⟩ :=
      compileName_run_strict compileEnv blockEnv hfaithful value hstate
        (by simpa [dataValueStoreItems] using hsupported)
    refine ⟨.ofName value.getHash, state', ?_, ?_⟩
    · rw [Ix.CompileM.compileDataValue,
        run_bind_strict compileEnv blockEnv state _ _, hrun]
      rfl
    · simpa [dataValueStoreItems] using hstep
  | ofNat value =>
    let bytes := ByteArray.mk (Nat.toBytesLE value)
    have hbytes : support.blobs bytes :=
      hsupported.blobs (by simp [dataValueStoreItems, bytes])
    obtain ⟨hstrict, hdelta, hstored⟩ :=
      insertBlob_strict hfaithful hstate hbytes
    exact ⟨.ofNat (Address.blake3 bytes),
      insertBlobStateStrict state bytes, by rfl, by
        simpa [dataValueStoreItems, bytes] using
          (show StrictMetaStep support state
            (insertBlobStateStrict state bytes) { blobs := [bytes] } from
              ⟨hstrict, hdelta, hstored⟩)⟩
  | ofInt value =>
    let bytes := Ix.CompileM.serializeIxInt value
    have hbytes : support.blobs bytes :=
      hsupported.blobs (by simp [dataValueStoreItems, bytes])
    obtain ⟨hstrict, hdelta, hstored⟩ :=
      insertBlob_strict hfaithful hstate hbytes
    exact ⟨.ofInt (Address.blake3 bytes),
      insertBlobStateStrict state bytes, by rfl, by
        simpa [dataValueStoreItems, bytes] using
          (show StrictMetaStep support state
            (insertBlobStateStrict state bytes) { blobs := [bytes] } from
              ⟨hstrict, hdelta, hstored⟩)⟩
  | ofSyntax value =>
    have hsyntaxSupported : MetaItemsSupported support
        (syntaxStoreItems value) := hsupported.left
    have hfinalSupported : support.blobs (serializeIxSyntaxRef value) :=
      hsupported.right.blobs (by simp)
    obtain ⟨syntaxState, hsyntaxRun, hsyntaxStep⟩ :=
      serializeIxSyntax_run_strict compileEnv blockEnv hfaithful state hstate
        value hsyntaxSupported
    obtain ⟨hstrict, hdelta, hstored⟩ :=
      insertBlob_strict hfaithful hsyntaxStep.strict hfinalSupported
    let finalState := insertBlobStateStrict syntaxState
      (serializeIxSyntaxRef value)
    let hfinalStep : StrictMetaStep support syntaxState finalState
        { blobs := [serializeIxSyntaxRef value] } :=
      ⟨hstrict, hdelta, hstored⟩
    refine ⟨.ofSyntax (Address.blake3 (serializeIxSyntaxRef value)),
      finalState, ?_, ?_⟩
    · rw [Ix.CompileM.compileDataValue,
        run_bind_strict compileEnv blockEnv state _ _, hsyntaxRun]
      rfl
    · simpa [dataValueStoreItems, finalState] using
        hsyntaxStep.trans hfinalStep

private theorem compileKVEntry_run_strict_effect
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (entry : Ix.Name × Ix.DataValue)
    (hsupported : MetaItemsSupported support (kvEntryStoreItems entry)) :
    StrictMetaRun compileEnv blockEnv support state
      (do
        Ix.CompileM.compileName entry.1
        let encoded ← Ix.CompileM.compileDataValue entry.2
        pure (entry.1.getHash, encoded))
      (kvEntryStoreItems entry) := by
  rcases entry with ⟨name, value⟩
  have hnameSupported : MetaItemsSupported support
      (compileNameStoreItems name) := hsupported.left
  have hvalueSupported : MetaItemsSupported support
      (dataValueStoreItems value) := hsupported.right
  obtain ⟨_, nameState, hnameRun, hnameStep⟩ :=
    compileName_run_strict compileEnv blockEnv hfaithful name hstate
      hnameSupported
  obtain ⟨encoded, finalState, hvalueRun, hvalueStep⟩ :=
    compileDataValue_run_strict_effect compileEnv blockEnv hfaithful nameState
      hnameStep.strict value hvalueSupported
  refine ⟨(name.getHash, encoded), finalState, ?_, ?_⟩
  · rw [run_bind_strict compileEnv blockEnv state _ _, hnameRun]
    simp only
    rw [run_bind_strict compileEnv blockEnv nameState _ _, hvalueRun]
    rfl
  · simpa [kvEntryStoreItems] using hnameStep.trans hvalueStep

private theorem compileKVMap_run_strict_effect
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (entries : Array (Ix.Name × Ix.DataValue))
    (hsupported : MetaItemsSupported support (kvMapStoreItems entries)) :
    StrictMetaRun compileEnv blockEnv support state
      (Ix.CompileM.compileKVMap entries) (kvMapStoreItems entries) := by
  have hrun := mapM_array_run_strict compileEnv blockEnv
    (fun entry : Ix.Name × Ix.DataValue => do
      Ix.CompileM.compileName entry.1
      let encoded ← Ix.CompileM.compileDataValue entry.2
      pure (entry.1.getHash, encoded))
    kvEntryStoreItems
    (fun current entry hcurrent hentry =>
      compileKVEntry_run_strict_effect compileEnv blockEnv hfaithful current
        hcurrent entry hentry)
    state hstate entries (by simpa [kvMapStoreItems] using hsupported)
  simpa [Ix.CompileM.compileKVMap, kvMapStoreItems, kvEntryStoreItems] using hrun

/-- Exact syntax bytes together with strict recovery of every name and blob
touched by recursive syntax serialization. -/
theorem serializeIxSyntax_run_strictStores
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    (source : Ix.Syntax)
    (hsupported : MetaItemsSupported support (syntaxStoreItems source)) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.serializeIxSyntax source) =
        .ok (serializeIxSyntaxRef source, state') ∧
      MetaStateFrame state state' ∧
      StrictMetaStoreWF support state' ∧
      MetaStoreDelta state state' (syntaxStoreItems source) ∧
      MetaItemsStored state' (syntaxStoreItems source) := by
  obtain ⟨strictState, hstrictRun, hstrictStep⟩ :=
    serializeIxSyntax_run_strict compileEnv blockEnv hfaithful state hstate
      source hsupported
  obtain ⟨frameState, hframeRun, hframe⟩ :=
    serializeIxSyntax_run_refines compileEnv blockEnv state source
  rw [hstrictRun] at hframeRun
  have hstateEq : strictState = frameState := by
    exact congrArg (fun result => result.2)
      (Except.ok.inj hframeRun)
  subst frameState
  exact ⟨strictState, hstrictRun, hframe, hstrictStep.strict,
    hstrictStep.delta, hstrictStep.stored⟩

/-- Exact scalar/name/syntax metadata compilation with strict backing-store
coherence. -/
theorem compileDataValue_run_strictStores
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) {support : MetaStoreSupport}
    (hfaithful : MetaKeyFaithfulOn support)
    (state : Ix.CompileM.BlockState) (hstate : StrictMetaStoreWF support state)
    {source : Ix.DataValue} {target : Ixon.DataValue}
    (href : compileDataValueRef source = some target)
    (hsupported : MetaItemsSupported support (dataValueStoreItems source)) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileDataValue source) = .ok (target, state') ∧
      MetaStateFrame state state' ∧
      StrictMetaStoreWF support state' ∧
      MetaStoreDelta state state' (dataValueStoreItems source) ∧
      MetaItemsStored state' (dataValueStoreItems source) := by
  obtain ⟨strictValue, strictState, hstrictRun, hstrictStep⟩ :=
    compileDataValue_run_strict_effect compileEnv blockEnv hfaithful state
      hstate source hsupported
  obtain ⟨exactState, hexactRun, hframe⟩ :=
    compileDataValue_run_refines compileEnv blockEnv state href
  rw [hexactRun] at hstrictRun
  have hpair : (target, exactState) = (strictValue, strictState) :=
    Except.ok.inj hstrictRun
  have hvalue := congrArg Prod.fst hpair
  have hstateEq := congrArg Prod.snd hpair
  simp only at hvalue hstateEq
  subst strictValue
  subst strictState
  exact ⟨exactState, hexactRun, hframe, hstrictStep.strict,
    hstrictStep.delta, hstrictStep.stored⟩

/-- Structural integrity required of preseeded name/blob maps, before the
current metadata values are added to the exact finite run support. -/
structure InitialMetaStoreWF (state : Ix.CompileM.BlockState) : Prop where
  names : ∀ {addr name}, state.blockNames.get? addr = some name →
    name.getHash = addr
  blobs : ∀ {addr bytes}, state.blockBlobs.get? addr = some bytes →
    Address.blake3 bytes = addr
  nameClosure : ∀ {addr name}, state.blockNames.get? addr = some name →
    MetaItemsStored state (compileNameStoreItems name)

theorem InitialMetaStoreWF.empty :
    InitialMetaStoreWF (default : Ix.CompileM.BlockState) := by
  constructor
  · intro addr name hlookup
    change ({} : Std.HashMap Address Ix.Name).get? addr = some name at hlookup
    simp at hlookup
  · intro addr bytes hlookup
    change ({} : Std.HashMap Address ByteArray).get? addr = some bytes at hlookup
    simp at hlookup
  · intro addr name hlookup
    change ({} : Std.HashMap Address Ix.Name).get? addr = some name at hlookup
    simp at hlookup

private theorem InitialMetaStoreWF.toStrict
    {state : Ix.CompileM.BlockState} (hstate : InitialMetaStoreWF state)
    (entries : Array (Ix.Name × Ix.DataValue)) :
    StrictMetaStoreWF (metaCompileSupport state entries) state :=
  { toMetaStoreCovered :=
      { names := fun {addr _name} hlookup =>
          ⟨Or.inl ⟨addr, hlookup⟩, hstate.names hlookup⟩
        blobs := fun {addr _bytes} hlookup =>
          ⟨Or.inl ⟨addr, hlookup⟩, hstate.blobs hlookup⟩ }
    nameClosure := hstate.nameClosure }

/-- Exact finite-support strict side-store theorem for production metadata
compilation.  It strengthens the wire refinement with append-only lookup
preservation and exact recovery of every traversed name, name component, and
blob payload. -/
theorem compileKVMap_run_strictStores
    (compileEnv : Ix.CompileM.CompileEnv)
    (blockEnv : Ix.CompileM.BlockEnv) (state : Ix.CompileM.BlockState)
    (entries : Array (Ix.Name × Ix.DataValue)) {target : Ixon.KVMap}
    (href : compileKVMapRef entries = some target)
    (hstate : InitialMetaStoreWF state)
    (hfaithful : MetaKeyFaithfulOn (metaCompileSupport state entries)) :
    ∃ state',
      Ix.CompileM.CompileM.run compileEnv blockEnv state
          (Ix.CompileM.compileKVMap entries) = .ok (target, state') ∧
      MetaStateFrame state state' ∧
      StrictMetaStoreWF (metaCompileSupport state entries) state' ∧
      MetaStoreDelta state state' (kvMapStoreItems entries) ∧
      MetaItemsStored state' (kvMapStoreItems entries) := by
  let support := metaCompileSupport state entries
  have hinput : StrictMetaStoreWF support state := hstate.toStrict entries
  have hsupported : MetaItemsSupported support (kvMapStoreItems entries) := by
    constructor
    · exact fun hname => Or.inr hname
    · exact fun hbytes => Or.inr hbytes
  obtain ⟨strictValue, strictState, hstrictRun, hstrictStep⟩ :=
    compileKVMap_run_strict_effect compileEnv blockEnv hfaithful state hinput
      entries hsupported
  obtain ⟨exactState, hexactRun, hframe⟩ :=
    compileKVMap_run_refines compileEnv blockEnv state href
  rw [hexactRun] at hstrictRun
  have hpair : (target, exactState) = (strictValue, strictState) :=
    Except.ok.inj hstrictRun
  have hvalue := congrArg Prod.fst hpair
  have hstateEq := congrArg Prod.snd hpair
  simp only at hvalue hstateEq
  subst strictValue
  subst strictState
  exact ⟨exactState, hexactRun, hframe, hstrictStep.strict,
    hstrictStep.delta, hstrictStep.stored⟩

end Ix.Compile.Verify
