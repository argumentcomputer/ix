import Aiur.Optimized.DedupCertificate
import Aiur.Memory.Partition

/-!
The physical calling convention contains words, not nominal types or argument
grouping. Type erasure is a separate certified pass: the typed compiler and its
provenance invariant remain available when a physical derivation is lifted.
All equations, hint validation, guards, and memory widths are preserved.
-/

namespace Aiur.Circuit.Erasure

def pack (words : List α) : WireValue α :=
  ⟨.tuple (List.replicate words.length .field), words⟩

@[simp] theorem pack_words (words : List α) : (pack words).words = words := rfl

@[simp] theorem pack_map (f : α → β) (words : List α) :
    (pack words).map f = pack (words.map f) := by
  simp [pack, WireValue.map]

def shape (wire : WireValue α) : Ty × Nat := (wire.type, wire.words.length)

@[simp] theorem shape_map (f : α → β) (wire : WireValue α) :
    shape (wire.map f) = shape wire := by simp [shape, WireValue.map]

def readWords : List (Ty × Nat) → List α → List (WireValue α)
  | [], _ => []
  | (type, width) :: rest, words =>
      ⟨type, words.take width⟩ :: readWords rest (words.drop width)

theorem readWords_flatten (values : List (WireValue α)) :
    readWords (values.map shape) (values.flatMap WireValue.words) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.map_cons, List.flatMap_cons, shape, readWords,
        List.take_left, List.drop_left, ih]

def messageShape (message : Message F) : List (Ty × Nat) × (Ty × Nat) :=
  (message.args.map shape, shape message.result)

def flatten (message : Message F) : Message F :=
  ⟨message.channel, [pack (message.args.flatMap WireValue.words)], pack message.result.words⟩

theorem flatten_injective {a b : Message F}
    (shapes : messageShape a = messageShape b) (same : flatten a = flatten b) : a = b := by
  have names := congrArg Message.channel same
  have args := congrArg (fun m => m.args.flatMap WireValue.words) same
  have result := congrArg (fun m => m.result.words) same
  have argShapes := congrArg Prod.fst shapes
  have resultTypes := congrArg (fun s => s.2.1) shapes
  have sameArgs : a.args = b.args := by
    rw [← readWords_flatten a.args, ← readWords_flatten b.args]
    change a.args.map shape = b.args.map shape at argShapes
    simp only [flatten, List.flatMap_cons, List.flatMap_nil, pack_words, List.append_nil] at args
    rw [argShapes, args]
  cases a; cases b
  simp only [flatten, pack, messageShape, shape] at *
  cases names; cases sameArgs
  congr 1
  cases ‹WireValue F›; cases ‹WireValue F›
  simp_all only

def dynamic (system : System F) (name : String) : Bool := (system.findChip? name).isSome

def message (system : System F) (claim : Message F) : Message F :=
  if dynamic system claim.channel then flatten claim else claim

def send (system : System F) (call : Send F) : Send F :=
  if dynamic system call.channel then
    { call with args := [pack (call.args.flatMap WireValue.words)], result := pack call.result.words }
  else call

def memory (lookup : MemoryLookup F) : MemoryLookup F :=
  { lookup with value := pack lookup.value.words }

def chip (system : System F) (original : Chip F) : Chip F :=
  { original with
    inputs := [pack (original.inputs.flatMap WireValue.words)]
    output := pack original.output.words
    sends := original.sends.map (send system)
    memory := original.memory.map memory }

def system (original : System F) : System F :=
  { original with chips := original.chips.map (chip original) }

def signature (chip : Chip F) : List (Ty × Nat) × (Ty × Nat) :=
  (chip.inputs.map shape, shape chip.output)

/-- Calls keep the source signature in the proof, even after their physical
message has been flattened. This is a finite syntactic check, not a row check. -/
def Compatible (source : System F) : Prop :=
  (∀ c ∈ source.chips, ∀ call ∈ c.sends, ∀ target,
    source.findChip? call.channel = some target →
    (call.args.map shape, shape call.result) = signature target) ∧
  (∀ c ∈ source.chips, ∀ lookup ∈ c.memory,
    (source.enums.layout lookup.value.type).toOption.map Layout.width = some lookup.value.words.length)

instance (source : System F) : Decidable (Compatible source) := by
  unfold Compatible
  letI (call : Send F) : Decidable (∀ target, source.findChip? call.channel = some target →
      (call.args.map shape, shape call.result) = signature target) := by
    cases found : source.findChip? call.channel with
    | none => exact isTrue (by simp)
    | some target =>
      exact decidable_of_iff ((call.args.map shape, shape call.result) = signature target) (by simp)
  infer_instance

def memoryTypes (source : System F) : List Ty :=
  source.chips.flatMap fun c => c.memory.map (·.value.type)

def typedROM (source : System F) (rom : WidthROM F) : WireROM F :=
  rom.toWireROM source.enums (memoryTypes source)

def rawROM (rom : WidthROM F) : WireROM F :=
  ⟨rom.entries.map fun (address, words) => (address, pack words)⟩

@[simp] theorem mem_rawROM {rom : WidthROM F} {address : F} {words : List F} :
    (address, pack words) ∈ (rawROM rom).entries ↔ (address, words) ∈ rom.entries := by
  simp only [rawROM, List.mem_map, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ws, member, rfl, equal⟩
    have same := congrArg WireValue.words equal
    change ws = words at same
    simpa only [same] using member
  · intro member; exact ⟨address, words, member, rfl, rfl⟩

theorem rawROM_valid {rom : WidthROM F} (valid : rom.Valid) : (rawROM rom).Valid := by
  rintro a ha b hb address types
  obtain ⟨⟨x, xs⟩, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨y, ys⟩, hy, rfl⟩ := List.mem_map.mp hb
  have lengths : xs.length = ys.length := by
    simp only [pack, Ty.tuple.injEq] at types
    simpa using congrArg List.length types
  have words := valid _ hx _ hy address lengths
  exact congrArg pack words

variable [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem send_message (source : System F) (call : Send F) (assignment : Var → F) :
    (send source call).message assignment = message source (call.message assignment) := by
  simp only [send, message, Send.message]
  split <;> simp_all [flatten, pack, WireValue.map, List.flatMap_map, List.map_flatMap]

omit [DecidableEq F] in
theorem chip_receive (source : System F) (original : Chip F) (row : Row F) :
    (chip source original).receive row = flatten (original.receive row) := by
  simp [chip, Chip.receive, flatten, pack, WireValue.map, List.flatMap_map,
    List.map_flatMap]

theorem chip_premises (source : System F) (original : Chip F) (row : Row F) :
    (chip source original).premises row = (original.premises row).map (message source) := by
  simp only [chip, Chip.premises, List.filterMap_map, List.map_filterMap, Function.comp_def]
  congr 1
  funext call
  have enabled : (send source call).enable = call.enable := by unfold send; split <;> rfl
  rw [enabled]
  split <;> simp [send_message]

omit [Field F] [DecidableEq F] in
@[simp] theorem chip_wellFormed (source : System F) (original : Chip F) :
    (chip source original).wellFormed = original.wellFormed := by
  have calls (call : Send F) : (send source call).inBounds original.numVars = call.inBounds original.numVars := by
    unfold send
    split <;> simp [Send.inBounds, pack]
  simp only [chip, Chip.wellFormed, pack, MemoryLookup.inBounds, memory, List.all_map,
    Function.comp_def, calls]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.all_flatMap]
  rfl

omit [DecidableEq F] in
theorem chip_validRow (source : System F) (compatible : Compatible source)
    {original : Chip F} (member : original ∈ source.chips) (rom : WidthROM F) (row : Row F) :
    (chip source original).ValidRow (rawROM rom) row ↔ original.ValidRow (typedROM source rom) row := by
  simp only [Chip.ValidRow, chip_wellFormed]
  change (_ ∧ _ ∧ _ ∧ ∀ lookup ∈ original.memory.map memory,
    lookup.Valid (rawROM rom) row.assignment) ↔ _
  simp only [List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  apply and_congr_right'; apply and_congr_right'; apply and_congr_right'
  apply forall_congr'
  intro lookup
  apply forall_congr'
  intro lookupMember
  have sized := compatible.2 original member lookup lookupMember
  have typeMember : lookup.value.type ∈ memoryTypes source :=
    List.mem_flatMap.mpr ⟨original, member, List.mem_map.mpr ⟨lookup, lookupMember, rfl⟩⟩
  simp only [MemoryLookup.Valid, memory]
  rw [pack_map, mem_rawROM]
  simp only [typedROM, WidthROM.mem_toWireROM, WireValue.map, List.length_map]
  simp only [typeMember, sized, and_true]

omit [Field F] [DecidableEq F] in
@[simp] theorem system_findChip (source : System F) (name : String) :
    (system source).findChip? name = (source.findChip? name).map (chip source) := by
  simp [system, System.findChip?, List.find?_map, chip, Function.comp_def]

omit [DecidableEq F] in
@[simp] theorem system_mapClaims (source : System F) : (system source).mapClaims = source.mapClaims := rfl

omit [DecidableEq F] in
theorem receive_shape (original : Chip F) (row : Row F) :
    messageShape (original.receive row) = signature original := by
  simp [messageShape, Chip.receive, signature, List.map_map, Function.comp_def]

omit [DecidableEq F] in
theorem send_shape (source : System F) (compatible : Compatible source)
    {original : Chip F} (member : original ∈ source.chips) {call : Send F} (present : call ∈ original.sends)
    {target : Chip F} (found : source.findChip? call.channel = some target) (assignment : Var → F) :
    messageShape (call.message assignment) = signature target := by
  simpa [messageShape, Send.message, List.map_map, Function.comp_def] using
    compatible.1 original member call present target found

def Signed (source : System F) (claim : Message F) : Prop :=
  ∀ target, source.findChip? claim.channel = some target → messageShape claim = signature target

theorem premise_signed (source : System F) (compatible : Compatible source)
    {original : Chip F} (member : original ∈ source.chips) (row : Row F)
    {claim : Message F} (required : claim ∈ original.premises row) : Signed source claim := by
  obtain ⟨call, present, equal⟩ := List.mem_filterMap.mp required
  unfold Chip.premises at required
  split at equal
  · cases equal
    exact fun target found => send_shape source compatible member present found row.assignment
  · cases equal

omit [Field F] [DecidableEq F] in
@[simp] theorem message_channel (source : System F) (claim : Message F) :
    (message source claim).channel = claim.channel := by
  unfold message; split <;> rfl

theorem derives_forward (source : System F) (compatible : Compatible source)
    (separated : ∀ claim, source.MapClaim claim → source.findChip? claim.channel = none)
    {rom : WidthROM F} {root : Message F}
    (derived : Derives source (typedROM source rom) root) :
    Derives (system source) (rawROM rom) (message source root) := by
  obtain ⟨tree⟩ := derived
  induction tree using Derivation.rec
    (motive_2 := fun messages _ => ∀ m ∈ messages, Derives (system source) (rawROM rom) (message source m)) with
  | node original row found valid children ih =>
      have named := System.findChip_name found
      have dynamicName : dynamic source original.name = true := by simp [dynamic, named, found]
      have conclusion : message source (original.receive row) = (chip source original).receive row := by
        rw [chip_receive]; simp [message, Chip.receive, dynamicName]
      rw [conclusion]
      apply (RuleInstance.node (chip source original) row (by simp [found])
        ((chip_validRow source compatible (List.mem_of_find?_eq_some found) rom row).mpr valid)).derives
      intro claim required
      rw [RuleInstance.premises, chip_premises] at required
      obtain ⟨old, member, rfl⟩ := List.mem_map.mp required
      exact ih old member
  | table member =>
      rename_i claim
      have unchanged : message source claim = claim := by simp [message, dynamic, separated _ member]
      rw [unchanged]
      exact ⟨.table member⟩
  | nil => simp_all
  | cons _ _ head tail =>
      rename_i claim member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail claim member

/-- A physical proof can be interpreted separately at every original call
signature. Sharing a row never requires a runtime type discriminator. -/
theorem derives_backward (source : System F) (compatible : Compatible source)
    (separated : ∀ claim, source.MapClaim claim → source.findChip? claim.channel = none)
    {rom : WidthROM F} {root : Message F} (signed : Signed source root)
    (derived : Derives (system source) (rawROM rom) (message source root)) :
    Derives source (typedROM source rom) root := by
  obtain ⟨tree⟩ := derived
  have lift {m : Message F} (tree : Derivation (system source) (rawROM rom) m) :
      ∀ claim, Signed source claim → message source claim = m → Derives source (typedROM source rom) claim := by
    refine Derivation.rec
      (motive_1 := fun m _ => ∀ claim, Signed source claim → message source claim = m →
        Derives source (typedROM source rom) claim)
      (motive_2 := fun messages _ => ∀ m ∈ messages, ∀ claim, Signed source claim → message source claim = m →
        Derives source (typedROM source rom) claim) ?_ ?_ ?_ ?_ tree
    · intro next row found valid children ih claim signed same
      rw [system_findChip] at found
      obtain ⟨original, originalFound, rfl⟩ := Option.map_eq_some_iff.mp found
      have names : claim.channel = original.name := by
        simpa [Chip.receive, chip] using congrArg Message.channel same
      have foundClaim : source.findChip? claim.channel = some original := by
        rw [names, System.findChip_name originalFound]; exact originalFound
      have sameFlat : flatten claim = flatten (original.receive row) := by
        simpa only [message, dynamic, foundClaim, Option.isSome_some, ↓reduceIte, chip_receive] using same
      have equal : claim = original.receive row :=
        flatten_injective ((signed original foundClaim).trans (receive_shape original row).symm) sameFlat
      rw [equal]
      apply (RuleInstance.node original row originalFound
        ((chip_validRow source compatible (List.mem_of_find?_eq_some originalFound) rom row).mp valid)).derives
      intro required member
      apply ih (message source required) ?_ required
        (premise_signed source compatible (List.mem_of_find?_eq_some originalFound) row member) rfl
      rw [chip_premises]
      exact List.mem_map.mpr ⟨required, member, rfl⟩
    · intro m member claim _ same
      have names : claim.channel = m.channel := by simpa using congrArg Message.channel same
      have fixed : message source claim = claim := by
        simp [message, dynamic, names, separated m member]
      rw [fixed] at same
      exact ⟨same.symm ▸ .table member⟩
    · simp
    · intro head tail headTree tailTrees headIH tailIH m member claim signed same
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH claim signed same
      · exact tailIH m member claim signed same
  exact lift tree root signed rfl

theorem derives_iff (source : System F) (compatible : Compatible source)
    (separated : ∀ claim, source.MapClaim claim → source.findChip? claim.channel = none)
    {rom : WidthROM F} {root : Message F} (signed : Signed source root) :
    Derives source (typedROM source rom) root ↔ Derives (system source) (rawROM rom) (message source root) :=
  ⟨derives_forward source compatible separated, derives_backward source compatible separated signed⟩

end Aiur.Circuit.Erasure
