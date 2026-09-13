/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.KeyCodec

/-! Exact v5 byte framing, canonical round trips and checked graph meaning. -/

namespace Aiur.NativeAIR.KeyCodec

def Reads (read : Reader α) (bytes : List UInt8) (value : α) : Prop :=
  ∀ rest, read (bytes ++ rest) = some (value, rest)

theorem Reads.pure (value : α) : Reads (pure value) [] value := by
  intro rest
  rfl

theorem Reads.bind {read : Reader α} {next : α → Reader β}
    {left right : List UInt8} {middle : α} {value : β}
    (first : Reads read left middle) (second : Reads (next middle) right value) :
    Reads (read >>= next) (left ++ right) value := by
  intro rest
  change (StateT.bind read next) _ = _
  rw [List.append_assoc, StateT.bind, first (right ++ rest)]
  exact second rest

theorem Reads.map {read : Reader α} {bytes : List UInt8} {value : α}
    (readValue : Reads read bytes value) (f : α → β) :
    Reads (f <$> read) bytes (f value) := by
  intro rest
  change (StateT.map f read) _ = _
  rw [StateT.map, readValue rest]
  rfl

theorem Reads.result {read : Reader α} {bytes : List UInt8} {value : α}
    (readValue : Reads read bytes value) (f : α → β) :
    Reads (do let value ← read; Pure.pure (f value)) bytes (f value) := by
  intro rest
  change (StateT.bind read _) _ = _
  rw [StateT.bind, readValue rest]
  rfl

theorem readByte_reads (byte : UInt8) : Reads readByte [byte] byte := fun _ => rfl

theorem Reads.byte {next : UInt8 → Reader α} {byte : UInt8} {bytes : List UInt8} {value : α}
    (body : Reads (next byte) bytes value) : Reads (readByte >>= next) (byte :: bytes) value :=
  (readByte_reads byte).bind body

theorem encodeNat_length (count value : Nat) : (encodeNat count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp only [encodeNat, List.length_cons, ih]

theorem readNat_reads (count value : Nat) (bounded : value < 256^count) :
    Reads (readNat count) (encodeNat count value) value := by
  induction count generalizing value with
  | zero =>
    have zero : value = 0 := by simpa using bounded
    subst value
    exact Reads.pure 0
  | succ count ih =>
    have small : value / 256 < 256^count := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).mpr
      simpa only [Nat.pow_succ] using bounded
    have rest := ih (value / 256) small
    have number : value.toUInt8.toNat + 256 * (value / 256) = value := by
      simp only [Nat.toUInt8_eq]
      exact Nat.mod_add_div _ _
    rw [readNat, encodeNat]
    apply Reads.byte
    simpa only [number] using rest.result (fun n => value.toUInt8.toNat + 256 * n)

theorem readMany_reads {read : Reader α} (encode : α → List UInt8) (values : List α)
    (elements : ∀ value ∈ values, Reads read (encode value) value) :
    Reads (readMany read values.length) (values.flatMap encode) values := by
  induction values with
  | nil => exact Reads.pure []
  | cons value values ih =>
    have first := elements value List.mem_cons_self
    have rest := ih (fun value member => elements value (List.mem_cons_of_mem _ member))
    exact first.bind (rest.result (value :: ·))

theorem readVector_reads {read : Reader α} (encode : α → List UInt8) (values : List α)
    (bounded : values.length < 65536)
    (elements : ∀ value ∈ values, Reads read (encode value) value) :
    Reads (readVector read) (encodeVector encode values) values :=
  (readNat_reads 2 values.length bounded).bind (readMany_reads encode values elements)

def NodeWireFits : Node → Prop
  | .konst _ | .isFirstRow | .isLastRow | .isTransition => True
  | .var column => column.index < 65536
  | .publicInput index => index < 256
  | .add a b | .sub a b | .mul a b => a < 65536 ∧ b < 65536
  | .neg child => child < 65536

theorem readNode_reads (node : Node) (fits : NodeWireFits node) :
    Reads readNode (encodeNode node) node := by
  cases node with
  | konst value =>
    simp only [encodeNode]
    split
    next small =>
      unfold readNode
      apply Reads.byte
      change Reads (do let n ← readNat 2; pure (Node.konst (G.ofNat n))) _ _
      simpa only [Function.comp_apply, G.ofNat_n] using
        (readNat_reads 2 value.n small).result (Node.konst ∘ G.ofNat)
    next _ =>
      have bounded : value.n < 256^8 := UInt64.toNat_lt value.val
      unfold readNode
      apply Reads.byte
      change Reads (do let n ← readNat 8; pure (Node.konst (G.ofNat n))) _ _
      simpa only [Function.comp_apply, G.ofNat_n] using
        (readNat_reads 8 value.n bounded).result (Node.konst ∘ G.ofNat)
  | publicInput index =>
    unfold readNode encodeNode
    apply Reads.byte
    exact (readNat_reads 1 index fits).result Node.publicInput
  | isFirstRow => intro rest; rfl
  | isLastRow => intro rest; rfl
  | isTransition => intro rest; rfl
  | add a b | sub a b | mul a b =>
    unfold readNode encodeNode
    apply Reads.byte
    apply Reads.bind (readNat_reads 2 a fits.1)
    exact (readNat_reads 2 b fits.2).result _
  | neg child =>
    unfold readNode encodeNode
    apply Reads.byte
    exact (readNat_reads 2 child fits).result Node.neg
  | var column =>
    obtain ⟨source, offset, index⟩ := column
    cases source <;> cases offset <;> unfold readNode encodeNode <;>
      apply Reads.byte <;> exact (readNat_reads 2 index fits).result _

structure LookupWireFits (lookup : Lookup) : Prop where
  multiplicity : lookup.multiplicity < 65536
  count : lookup.args.length < 65536
  args : ∀ arg ∈ lookup.args, arg < 65536

theorem readLookup_reads (lookup : Lookup) (fits : LookupWireFits lookup) :
    Reads readLookup (encodeLookup lookup) lookup := by
  unfold readLookup encodeLookup
  apply Reads.bind (readNat_reads 2 lookup.multiplicity fits.multiplicity)
  exact (readVector_reads (encodeNat 2) lookup.args fits.count
    (fun arg member => readNat_reads 2 arg (fits.args arg member))).result _

structure CircuitWireFits (circuit : Circuit) : Prop where
  mainWidth : circuit.mainWidth < 65536
  preprocessedWidth : circuit.preprocessedWidth < 65536
  preprocessedHeight : circuit.preprocessedHeight < 2^32
  maxConstraintDegree : circuit.maxConstraintDegree < 65536
  lookupGroupSize : circuit.lookupGroupSize < 256
  nodesCount : circuit.graph.nodes.length < 65536
  nodes : ∀ node ∈ circuit.graph.nodes, NodeWireFits node
  zerosCount : circuit.graph.zeros.length < 65536
  zeros : ∀ index ∈ circuit.graph.zeros, index < 65536
  lookupsCount : circuit.graph.lookups.length < 65536
  lookups : ∀ lookup ∈ circuit.graph.lookups, LookupWireFits lookup

theorem readCircuitData_reads (circuit : Circuit) (fits : CircuitWireFits circuit) :
    Reads readCircuitData (encodeCircuit circuit) circuit := by
  unfold readCircuitData encodeCircuit
  simp only [List.append_assoc]
  apply Reads.bind (readNat_reads 2 circuit.mainWidth fits.mainWidth)
  apply Reads.bind (readNat_reads 2 circuit.preprocessedWidth fits.preprocessedWidth)
  apply Reads.bind (readNat_reads 4 circuit.preprocessedHeight fits.preprocessedHeight)
  apply Reads.bind (readNat_reads 2 circuit.maxConstraintDegree fits.maxConstraintDegree)
  apply Reads.bind (readNat_reads 1 circuit.lookupGroupSize fits.lookupGroupSize)
  apply Reads.bind (readVector_reads encodeNode circuit.graph.nodes fits.nodesCount
    (fun node member => readNode_reads node (fits.nodes node member)))
  apply Reads.bind (readVector_reads (encodeNat 2) circuit.graph.zeros fits.zerosCount
    (fun index member => readNat_reads 2 index (fits.zeros index member)))
  exact (readVector_reads encodeLookup circuit.graph.lookups fits.lookupsCount
    (fun lookup member => readLookup_reads lookup (fits.lookups lookup member))).result _

theorem readCircuit_reads (circuit : Circuit) (fits : CircuitWireFits circuit)
    (valid : circuit.valid = true) : Reads readCircuit (encodeCircuit circuit) circuit := by
  intro rest
  simp only [readCircuit, bind, StateT.bind, readCircuitData_reads circuit fits rest,
    Option.bind_some, valid, ite_true, pure, StateT.pure]

def ParametersWireFits (parameters : Parameters) : Prop :=
  ∀ value ∈ [parameters.logBlowup, parameters.capHeight, parameters.logFinalPolyLen,
    parameters.maxLogArity, parameters.numQueries, parameters.commitProofOfWorkBits,
    parameters.queryProofOfWorkBits], value < 65536

theorem readParameters_reads (parameters : Parameters) (fits : ParametersWireFits parameters) :
    Reads readParameters (encodeParameters parameters) parameters := by
  unfold ParametersWireFits at fits
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at fits
  unfold readParameters encodeParameters
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  apply Reads.bind (readNat_reads 2 parameters.logBlowup fits.1)
  apply Reads.bind (readNat_reads 2 parameters.capHeight fits.2.1)
  apply Reads.bind (readNat_reads 2 parameters.logFinalPolyLen fits.2.2.1)
  apply Reads.bind (readNat_reads 2 parameters.maxLogArity fits.2.2.2.1)
  apply Reads.bind (readNat_reads 2 parameters.numQueries fits.2.2.2.2.1)
  apply Reads.bind (readNat_reads 2 parameters.commitProofOfWorkBits fits.2.2.2.2.2.1)
  exact (readNat_reads 2 parameters.queryProofOfWorkBits fits.2.2.2.2.2.2).result _

def CommitmentWireFits : Option MerkleCap → Prop
  | none => True
  | some cap => cap.length < 65536 ∧ cap.length.isPowerOfTwo ∧ ∀ digest ∈ cap, digest.length = 32

theorem readCommitment_reads (commitment : Option MerkleCap) (fits : CommitmentWireFits commitment) :
    Reads readCommitment (encodeCommitment commitment) commitment := by
  cases commitment with
  | none => intro rest; rfl
  | some cap =>
    unfold readCommitment encodeCommitment
    apply Reads.byte
    have body : Reads (readVector (readMany readByte 32)) (encodeVector id cap) cap := by
      apply readVector_reads id cap fits.1
      intro digest member
      have bytes := readMany_reads (fun byte => [byte]) digest (fun byte _ => readByte_reads byte)
      simpa only [fits.2.2 digest member, List.flatMap_singleton', id_eq] using bytes
    intro rest
    change (StateT.bind (readVector (readMany readByte 32)) _) _ = _
    rw [StateT.bind, body rest]
    simp only [bind, Option.bind_some, fits.2.1, ite_true, pure, StateT.pure]

def IndexWireFits : Option Nat → Prop
  | none => True
  | some index => index < 65535

theorem readIndex_reads (index : Option Nat) (fits : IndexWireFits index) :
    Reads readIndex (encodeIndex index) index := by
  unfold readIndex encodeIndex
  have bounded : index.getD 65535 < 65536 := by
    cases index <;> simp only [IndexWireFits, Option.getD] at fits ⊢ <;> omega
  have equal : (if index.getD 65535 = 65535 then none else some (index.getD 65535)) = index := by
    cases index <;> simp only [IndexWireFits, Option.getD] at fits ⊢
    · rfl
    · rw [if_neg (by omega)]
  simpa only [equal] using
    (readNat_reads 2 (index.getD 65535) bounded).result (fun n => if n = 65535 then none else some n)

structure KeyWireFits (key : Key) : Prop where
  parameters : ParametersWireFits key.parameters
  circuitCount : key.circuits.length < 65536
  circuits : ∀ circuit ∈ key.circuits, CircuitWireFits circuit
  commitment : CommitmentWireFits key.preprocessedCommitment
  indexCount : key.preprocessedIndices.length = key.circuits.length
  indices : ∀ index ∈ key.preprocessedIndices, IndexWireFits index

theorem readKey_reads (key : Key) (fits : KeyWireFits key)
    (valid : ∀ circuit ∈ key.circuits, circuit.valid = true) :
    Reads readKey (encodeKey key) key := by
  unfold readKey encodeKey
  simp only [List.append_assoc]
  apply Reads.bind (readParameters_reads key.parameters fits.parameters)
  apply Reads.bind (readVector_reads encodeCircuit key.circuits fits.circuitCount
    (fun circuit member => readCircuit_reads circuit (fits.circuits circuit member) (valid circuit member)))
  apply Reads.bind (readCommitment_reads key.preprocessedCommitment fits.commitment)
  rw [← fits.indexCount]
  exact (readMany_reads encodeIndex key.preprocessedIndices
    (fun index member => readIndex_reads index (fits.indices index member))).result _

theorem decode_encode (key : Key) (fits : KeyWireFits key)
    (valid : ∀ circuit ∈ key.circuits, circuit.valid = true) : decode (encode key) = some key := by
  have read := readKey_reads key fits valid []
  simp only [List.append_nil] at read
  simp only [decode, encode, List.toList_data_toByteArray, read,
    bind, Option.bind_some, List.isEmpty_nil, ite_true]

theorem decodeCanonical_success {bytes : ByteArray} {key : Key}
    (accepted : decodeCanonical bytes = some key) : decode bytes = some key ∧ encode key = bytes := by
  unfold decodeCanonical at accepted
  cases parsed : decode bytes with
  | none => simp [parsed, bind, Option.bind] at accepted
  | some result =>
    simp only [parsed, bind, Option.bind_some] at accepted
    split at accepted
    next encoded => cases accepted; exact ⟨rfl, encoded⟩
    next => cases accepted

theorem decodeCanonical_encode (key : Key) (fits : KeyWireFits key)
    (valid : ∀ circuit ∈ key.circuits, circuit.valid = true) :
    decodeCanonical (encode key) = some key := by
  simp only [decodeCanonical, decode_encode key fits valid, bind, Option.bind_some, ite_true]

theorem canonical_bytes_unique {first second : ByteArray} {key : Key}
    (left : decodeCanonical first = some key) (right : decodeCanonical second = some key) : first = second :=
  (decodeCanonical_success left).2.symm.trans (decodeCanonical_success right).2

theorem encode_injective {first second : Key} (leftFits : KeyWireFits first) (rightFits : KeyWireFits second)
    (leftValid : ∀ circuit ∈ first.circuits, circuit.valid = true)
    (rightValid : ∀ circuit ∈ second.circuits, circuit.valid = true)
    (equal : encode first = encode second) : first = second := by
  have decoded := congrArg decode equal
  rw [decode_encode first leftFits leftValid, decode_encode second rightFits rightValid] at decoded
  exact Option.some.inj decoded

def Returns (read : Reader α) (property : α → Prop) : Prop :=
  ∀ bytes value rest, read bytes = some (value, rest) → property value

theorem Returns.pure {value : α} {property : α → Prop} (valid : property value) :
    Returns (Pure.pure value) property := by
  intro bytes result rest parsed
  cases parsed
  exact valid

theorem Returns.failure (property : α → Prop) : Returns failure property := by
  intro bytes value rest parsed
  cases parsed

theorem Returns.bind {read : Reader α} {next : α → Reader β} {left : α → Prop} {right : β → Prop}
    (first : Returns read left) (second : ∀ value, left value → Returns (next value) right) :
    Returns (read >>= next) right := by
  intro bytes value rest parsed
  change (StateT.bind read next) bytes = _ at parsed
  cases readFirst : read bytes with
  | none => simp [StateT.bind, readFirst] at parsed
  | some pair =>
    obtain ⟨middle, unread⟩ := pair
    rw [StateT.bind, readFirst] at parsed
    change next middle unread = some (value, rest) at parsed
    exact second middle (first bytes middle unread readFirst) unread value rest parsed

theorem Returns.bind_any {read : Reader α} {next : α → Reader β} {property : β → Prop}
    (body : ∀ value, Returns (next value) property) : Returns (read >>= next) property :=
  Returns.bind (fun _ _ _ _ => True.intro) (fun value _ => body value)

theorem Returns.weaken {read : Reader α} {left right : α → Prop}
    (valid : Returns read left) (weaken : ∀ value, left value → right value) : Returns read right :=
  fun bytes value rest parsed => weaken value (valid bytes value rest parsed)

theorem Returns.result {read : Reader α} {left : α → Prop} {right : β → Prop}
    (valid : Returns read left) (f : α → β) (preserves : ∀ value, left value → right (f value)) :
    Returns (do let value ← read; Pure.pure (f value)) right :=
  Returns.bind valid (fun value known => Returns.pure (preserves value known))

theorem readMany_returns {read : Reader α} {property : α → Prop} (valid : Returns read property) (count : Nat) :
    Returns (readMany read count) (fun values => values.length = count ∧ ∀ value ∈ values, property value) := by
  induction count with
  | zero => exact Returns.pure ⟨rfl, by simp⟩
  | succ count ih =>
    refine Returns.bind (right := fun values : List α =>
      values.length = count + 1 ∧ ∀ value ∈ values, property value) valid ?_
    intro value first
    refine Returns.result (right := fun values : List α =>
      values.length = count + 1 ∧ ∀ value ∈ values, property value) ih (value :: ·) ?_
    intro values rest
    exact ⟨by simp only [List.length_cons, rest.1], fun entry member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact rest.2 entry member⟩

theorem readVector_returns {read : Reader α} {property : α → Prop} (valid : Returns read property) :
    Returns (readVector read) (fun values => ∀ value ∈ values, property value) :=
  Returns.bind_any (fun count => (readMany_returns valid count).weaken (fun _ known => known.2))

theorem readCircuit_returns : Returns readCircuit (fun circuit => circuit.valid = true) := by
  unfold readCircuit
  apply Returns.bind_any
  intro circuit
  split
  next valid => exact Returns.pure valid
  next => exact Returns.failure _

def CommitmentValid : Option MerkleCap → Prop
  | none => True
  | some cap => cap.length.isPowerOfTwo ∧ ∀ digest ∈ cap, digest.length = 32

theorem readCommitment_returns : Returns readCommitment CommitmentValid := by
  unfold readCommitment
  refine Returns.bind_any (property := CommitmentValid) ?_
  intro byte
  split
  · exact Returns.pure True.intro
  · refine Returns.bind (right := CommitmentValid)
      (readVector_returns ((readMany_returns (read := readByte) (property := fun _ => True)
        (fun _ _ _ _ => True.intro) 32).weaken (fun _ known => known.1))) ?_
    intro cap digests
    split
    next power => exact Returns.pure ⟨power, digests⟩
    next => exact Returns.failure _
  · exact Returns.failure _

theorem readKey_returns : Returns readKey (fun key =>
    (∀ circuit ∈ key.circuits, circuit.valid = true) ∧ key.preprocessedIndices.length = key.circuits.length) := by
  unfold readKey
  refine Returns.bind_any (read := readParameters) (property := fun key : Key =>
    (∀ circuit ∈ key.circuits, circuit.valid = true) ∧ key.preprocessedIndices.length = key.circuits.length) ?_
  intro parameters
  refine Returns.bind (right := fun key : Key =>
    (∀ circuit ∈ key.circuits, circuit.valid = true) ∧ key.preprocessedIndices.length = key.circuits.length)
    (readVector_returns readCircuit_returns) ?_
  intro circuits valid
  refine Returns.bind_any (read := readCommitment) (property := fun key : Key =>
    (∀ circuit ∈ key.circuits, circuit.valid = true) ∧ key.preprocessedIndices.length = key.circuits.length) ?_
  intro commitment
  apply Returns.result (right := fun key : Key =>
    (∀ circuit ∈ key.circuits, circuit.valid = true) ∧ key.preprocessedIndices.length = key.circuits.length)
    (readMany_returns (read := readIndex) (property := fun _ => True)
    (fun _ _ _ _ => True.intro) circuits.length)
    (fun indices => Key.mk parameters circuits commitment indices)
  intro indices known
  exact ⟨valid, known.1⟩

theorem decode_success {bytes : ByteArray} {key : Key} (parsed : decode bytes = some key) :
    readKey bytes.data.toList = some (key, []) := by
  unfold decode at parsed
  cases read : readKey bytes.data.toList with
  | none => simp [read, bind, Option.bind] at parsed
  | some pair =>
    obtain ⟨result, rest⟩ := pair
    simp only [read, bind, Option.bind_some] at parsed
    split at parsed
    next empty =>
      have empty : rest = [] := List.isEmpty_iff.mp empty
      cases parsed
      simp only [empty]
    next => cases parsed

theorem decode_valid {bytes : ByteArray} {key : Key} (parsed : decode bytes = some key) :
    (∀ circuit ∈ key.circuits, circuit.valid = true) ∧ key.preprocessedIndices.length = key.circuits.length :=
  readKey_returns _ _ _ (decode_success parsed)

theorem readKey_commitment : Returns readKey (fun key => CommitmentValid key.preprocessedCommitment) := by
  unfold readKey
  refine Returns.bind_any (read := readParameters)
    (property := fun key : Key => CommitmentValid key.preprocessedCommitment) ?_
  intro parameters
  refine Returns.bind_any (read := readVector readCircuit)
    (property := fun key : Key => CommitmentValid key.preprocessedCommitment) ?_
  intro circuits
  refine Returns.bind (right := fun key : Key => CommitmentValid key.preprocessedCommitment)
    readCommitment_returns ?_
  intro commitment valid
  refine Returns.bind_any (read := readMany readIndex circuits.length)
    (property := fun key : Key => CommitmentValid key.preprocessedCommitment) ?_
  intro indices
  exact Returns.pure valid

theorem decode_commitment {bytes : ByteArray} {key : Key} (parsed : decode bytes = some key) :
    CommitmentValid key.preprocessedCommitment := readKey_commitment _ _ _ (decode_success parsed)

theorem Circuit.valid_graph {circuit : Circuit} (valid : circuit.valid = true) :
    1 ≤ circuit.lookupGroupSize ∧ circuit.lookupGroupSize ≤ 8 ∧
      circuit.graph.Valid circuit.widths ∧ circuit.computedDegree = some circuit.maxConstraintDegree := by
  simp only [Circuit.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
  obtain ⟨⟨⟨positive, bounded⟩, prefixRead⟩, degrees⟩ := valid
  cases read : checkedGraphPrefix circuit.widths circuit.graph with
  | none => simp only [read, Option.isSome_none, Bool.false_eq_true] at prefixRead
  | some index => exact ⟨positive, bounded, (checkedGraphPrefix_iff _ _ _).mp read |>.1, degrees⟩

theorem decoded_graph_sweeps {bytes : ByteArray} {key : Key} (parsed : decode bytes = some key)
    {circuit : Circuit} (member : circuit ∈ key.circuits) (ops : EvalOps W) (values : Values W)
    (fits : values.Fits circuit.widths) :
    ∃ buffer, circuit.graph.sweep ops values = some buffer ∧ buffer.size = circuit.graph.nodes.length :=
  ((Circuit.valid_graph ((decode_valid parsed).1 circuit member)).2.2.1).sweep_defined ops values fits

theorem decode_encoded_suffix (key : Key) (fits : KeyWireFits key)
    (valid : ∀ circuit ∈ key.circuits, circuit.valid = true) (rest : List UInt8) :
    decode ((encodeKey key ++ rest).toByteArray) = if rest = [] then some key else none := by
  simp only [decode, List.toList_data_toByteArray, readKey_reads key fits valid rest, bind, Option.bind_some]
  cases rest <;> rfl

end Aiur.NativeAIR.KeyCodec
