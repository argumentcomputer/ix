import Ix.Cert.MultiStark.Types
import Ix.Cert.MultiStark.LookupsPlain
import CertiFriP3.DomainSep

/-! # Multi-STARK Binary Wire Decoders (`Ix.Cert.MultiStark.Wire`)

Exact, Mathlib-free binary decoders matching Protocol `v6` (`Fp^3`, `FriBatching::Tensor`):
1. `StarkSystem.fromBytes` — full parity with `crates/stark-key/src/lib.rs` (v6 dense format):
   - strict `proto_ver == 6`, `ext_deg == 3`, `fri_batching == 1`, exact EOF;
   - canonical `ConstSmall`/`ConstBig` field encodings (rejecting `ConstBig ≤ 0xFFFF` and `≥ p`);
   - preprocessed width/height consistency and power-of-two height;
   - `1 ≤ lookupGroupSize ≤ MAX_LOOKUP_GROUP` (`8`);
   - topological node order and `u32`-bounded per-node degree recomputation;
   - column and public-input index bounds;
   - `lookupPrefixLen` coverage of all lookup roots;
   - compiler-context enforcement (`checkCompilerContexts`: no `Public`, row selectors, or
     `Stage2` in the lookup prefix; no `Stage2` reachable from `zeros` constraint roots);
   - re-derived combined `maxConstraintDegree` matching serialized metadata and blowup budget;
   - canonical BLAKE3 `derive_key("multi-stark/v6/vk")` `vk_digest` recomputation and check;
   - canonical preprocessed commitment / ranked index trailer validation;
   - proof-of-work ceiling (`≤ 32` bits).
2. `BatchProof.fromBytes` — `multi-stark/src/{prover.rs,batch.rs}` (bincode v2 `LittleEndian + Fixint`,
   strict canonical Goldilocks `< p`, 3-limb `GoldilocksExt3`, strict `bool`/`Option` tag checks, exact EOF).
-/

namespace Ix.Cert.MultiStark

open CertiFri CertiFri.P3

/-- Maximum proof-of-work bits permitted in either FRI grinding phase
(`crates/stark-key/src/security.rs`, `Aiur.maxProofOfWorkBits`). -/
def MAX_PROOF_OF_WORK_BITS : Nat := 32

/-- Maximum per-node degree multiple matching `recompute_degrees`'s `u32` arithmetic
(`crates/stark-key/src/lib.rs`). -/
def MAX_NODE_DEGREE : Nat := 0xFFFFFFFF

/-- Simple immutable byte-slice cursor. -/
private structure Cursor where
  bytes : ByteArray
  pos : Nat
  deriving Inhabited

private abbrev DecodeM := StateT Cursor (Except String)

private def readU8 : DecodeM UInt8 := do
  let c ← get
  if h : c.pos < c.bytes.size then
    set { c with pos := c.pos + 1 }
    pure c.bytes[c.pos]
  else
    throw s!"eof: need 1 byte at offset {c.pos}"

private def readBool : DecodeM Bool := do
  match ← readU8 with
  | 0 => pure false
  | 1 => pure true
  | b => throw s!"invalid bool byte {b}"

private def readU16LE : DecodeM Nat := do
  let b0 ← readU8
  let b1 ← readU8
  pure (b0.toNat + (b1.toNat <<< 8))

private def readU32LE : DecodeM Nat := do
  let b0 ← readU8
  let b1 ← readU8
  let b2 ← readU8
  let b3 ← readU8
  pure (b0.toNat + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24))

private def readU64LE : DecodeM UInt64 := do
  let lo ← readU32LE
  let hi ← readU32LE
  pure (UInt64.ofNat (lo + (hi <<< 32)))

private def readLen : DecodeM Nat := do
  let n ← readU64LE
  pure n.toNat

private def readBytes (n : Nat) : DecodeM ByteArray := do
  let c ← get
  if c.pos + n ≤ c.bytes.size then
    set { c with pos := c.pos + n }
    pure (c.bytes.extract c.pos (c.pos + n))
  else
    throw s!"eof: need {n} bytes at offset {c.pos}"

private def readDigest : DecodeM D := do
  let bs ← readBytes 32
  match Digest.ofBytes? bs with
  | some d => pure d
  | none => throw "internal error: 32-byte digest decode failed"

private def readCanonicalF : DecodeM F := do
  let w ← readU64LE
  match Goldilocks.ofCanonical? w with
  | some x => pure x
  | none => throw s!"non-canonical Goldilocks element {w}"

private def readEF : DecodeM EF := do
  let c0 ← readCanonicalF
  let c1 ← readCanonicalF
  let c2 ← readCanonicalF
  pure ⟨c0, c1, c2⟩

private def readArray (n : Nat) (f : DecodeM α) : DecodeM (Array α) := do
  let c ← get
  if n > c.bytes.size - c.pos then
    throw s!"length {n} exceeds remaining {c.bytes.size - c.pos} bytes at offset {c.pos}"
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    out := out.push (← f)
  pure out

private def readVec (f : DecodeM α) : DecodeM (Array α) := do
  let n ← readLen
  readArray n f

private def readOption (f : DecodeM α) : DecodeM (Option α) := do
  match ← readU8 with
  | 0 => pure none
  | 1 => some <$> f
  | b => throw s!"invalid option tag {b}"

private def ensureEOF : DecodeM Unit := do
  let c ← get
  unless c.pos == c.bytes.size do
    throw s!"trailing bytes: {c.bytes.size - c.pos} unread at offset {c.pos}"

/-! ## 1. Canonical Degree Recomputation, Blowup Budget, & `vk_digest` -/

private def pushU16LE (buf : ByteArray) (n : Nat) : ByteArray :=
  let buf := buf.push (n &&& 0xFF).toUInt8
  buf.push ((n >>> 8) &&& 0xFF).toUInt8

private def pushU32LE (buf : ByteArray) (n : Nat) : ByteArray :=
  let buf := buf.push (n &&& 0xFF).toUInt8
  let buf := buf.push ((n >>> 8) &&& 0xFF).toUInt8
  let buf := buf.push ((n >>> 16) &&& 0xFF).toUInt8
  buf.push ((n >>> 24) &&& 0xFF).toUInt8

private def pushU64LE (buf : ByteArray) (n : Nat) : ByteArray :=
  pushU32LE (pushU32LE buf n) (n >>> 32)

/-- Recompute per-node degree multiples in topological node order
(`crates/stark-key/src/lib.rs`, `recompute_degrees`), rejecting out-of-order child
references and `u32` degree overflow (`> MAX_NODE_DEGREE`). -/
def recomputeDegrees? (nodes : Array GraphNode) : Except String (Array Nat) := do
  let mut degrees : Array Nat := Array.mkEmpty nodes.size
  for idx in [0:nodes.size] do
    let some node := nodes[idx]? | throw "internal error: node index out of bounds"
    let d ← match node with
      | .const _ | .publicInput _ | .isTransition => pure 0
      | .var _ _ _ | .isFirstRow | .isLastRow => pure 1
      | .add a b | .sub a b =>
        match degrees[a]?, degrees[b]? with
        | some da, some db => pure (max da db)
        | _, _ => throw s!"vk: node child out of topological order ({a}, {b}) at node {idx}"
      | .mul a b =>
        match degrees[a]?, degrees[b]? with
        | some da, some db =>
          let sum := da + db
          if sum > MAX_NODE_DEGREE then
            throw s!"vk: constraint node degree overflow at node {idx}"
          pure sum
        | _, _ => throw s!"vk: node child out of topological order ({a}, {b}) at node {idx}"
      | .neg a =>
        match degrees[a]? with
        | some da => pure da
        | none => throw s!"vk: node child out of topological order ({a}) at node {idx}"
    degrees := degrees.push d
  pure degrees

/-- Total degree sweep used by `computeVkDigest` (agrees with `recomputeDegrees?` on every
topological, overflow-free circuit). -/
def sweepDegreesTotal (nodes : Array GraphNode) : Array Nat := Id.run do
  let mut degrees : Array Nat := Array.mkEmpty nodes.size
  for node in nodes do
    let d := match node with
      | .const _ | .publicInput _ | .isTransition => 0
      | .var _ _ _ | .isFirstRow | .isLastRow => 1
      | .add a b | .sub a b => max (degrees.getD a 0) (degrees.getD b 0)
      | .mul a b => min (degrees.getD a 0 + degrees.getD b 0) (MAX_NODE_DEGREE + 1)
      | .neg a => degrees.getD a 0
    degrees := degrees.push d
  return degrees

/-- Maximum degree multiple over user constraint roots (`zeros`). -/
def userMaxDegreeFrom (degrees : Array Nat) (zeros : Array Nat) : Nat :=
  zeros.foldl (fun acc z => max acc (degrees.getD z 0)) 0

/-- Analytically derive the maximum degree multiple over grouped LogUp constraints
(`multi-stark/src/lookup.rs`, `logup_max_degree`; `crates/stark-key/src/lib.rs:496-518`). -/
def deriveLookupDegree (degrees : Array Nat) (lookups : Array CompiledLookup)
    (groupSize : Nat) : Nat := Id.run do
  let k := max 1 groupSize
  let numGroups := (lookups.size + k - 1) / k
  let mut lookupDeg := 1
  for g in [0:numGroups] do
    let start := g * k
    let stop := min (start + k) lookups.size
    let mut mDegs : Array Nat := Array.mkEmpty (stop - start)
    let mut sum := 0
    for j in [start:stop] do
      if let some l := lookups[j]? then
        let md := l.args.foldl (fun acc n => max acc (degrees.getD n 0)) 0
        sum := sum + md
        mDegs := mDegs.push md
    lookupDeg := max lookupDeg (sum + 1)
    for offset in [0:(stop - start)] do
      if let some l := lookups[start + offset]? then
        let md := mDegs.getD offset 0
        let multTerm := degrees.getD l.multiplicity 0 + (sum - md)
        lookupDeg := max lookupDeg multTerm
  return lookupDeg

/-- Whether `c.quotientDegree ≤ 2 ^ logBlowup` (the PCS blowup degree budget enforced by
`multi-stark/src/system.rs`), checked without overflowing bit shifts on arbitrary `logBlowup`. -/
def respectsBlowupBudget (logBlowup : Nat) (c : SysCircuit) : Bool :=
  let n := max c.maxConstraintDegree 2 - 1
  decide (n ≤ 1) || decide (Nat.log2 (n - 1) < logBlowup)

theorem respectsBlowupBudget_iff (logBlowup : Nat) (c : SysCircuit) :
    respectsBlowupBudget logBlowup c = true ↔ c.quotientDegree ≤ 2 ^ logBlowup := by
  unfold respectsBlowupBudget SysCircuit.quotientDegree
  dsimp only
  generalize max c.maxConstraintDegree 2 - 1 = n
  by_cases h1 : n ≤ 1
  · simp only [h1, decide_true, Bool.true_or, ↓reduceIte, true_iff]
    exact Nat.one_le_two_pow
  · simp only [h1, decide_false, Bool.false_or, decide_eq_true_eq, ↓reduceIte]
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    constructor
    · intro hlt
      exact Nat.pow_le_pow_right (by decide) hlt
    · intro hle
      by_cases hlt : Nat.log2 (n - 1) + 1 ≤ logBlowup
      · omega
      · have hgt : logBlowup < Nat.log2 (n - 1) + 1 := by omega
        have hpow : 2 ^ logBlowup < 2 ^ (Nat.log2 (n - 1) + 1) :=
          Nat.pow_lt_pow_right (by decide) hgt
        omega

/-- Canonical byte preimage hashed by `multi_stark::system::compute_vk_digest::<Val, ExtVal3>`
(`multi-stark/src/system.rs:426-548`) under `BLAKE3_derive_key("multi-stark/v6/vk")`. -/
def vkDigestPreimage (circuits : Array SysCircuit) : ByteArray := Id.run do
  let mut buf := ByteArray.empty
  -- EF::D = 3 (u64 LE), EF::MODULUS = CubicTrinomial (tag = 2, u8)
  buf := pushU64LE buf 3
  buf := buf.push 2
  buf := pushU64LE buf circuits.size
  for c in circuits do
    let degrees := sweepDegreesTotal c.nodes
    let userMaxDeg := userMaxDegreeFrom degrees c.zeros
    buf := pushU64LE buf c.mainWidth
    buf := pushU64LE buf c.preprocessedWidth
    buf := pushU64LE buf c.preprocessedHeight
    buf := pushU64LE buf c.lookups.size
    buf := pushU64LE buf c.stage2Width
    buf := pushU64LE buf LOOKUP_NUM_PUBLICS
    buf := pushU64LE buf c.lookupGroupSize
    buf := pushU64LE buf c.constraintCount
    buf := pushU64LE buf c.maxConstraintDegree
    buf := pushU64LE buf c.lookupPrefixLen
    buf := pushU32LE buf userMaxDeg
    buf := pushU64LE buf c.nodes.size
    for node in c.nodes do
      match node with
      | .const v =>
        buf := Goldilocks.pushBytes (buf.push 0) v
      | .var src off col =>
        let srcTag : UInt8 := match src with
          | .preprocessed => 0
          | .main => 1
          | .stage2 => 2
        let offTag : UInt8 := match off with
          | .current => 0
          | .next => 1
        buf := pushU32LE (((buf.push 1).push srcTag).push offTag) col
      | .publicInput idx =>
        buf := pushU32LE (buf.push 2) idx
      | .isFirstRow => buf := buf.push 3
      | .isLastRow => buf := buf.push 4
      | .isTransition => buf := buf.push 5
      | .add a b => buf := pushU32LE (pushU32LE (buf.push 6) a) b
      | .sub a b => buf := pushU32LE (pushU32LE (buf.push 7) a) b
      | .mul a b => buf := pushU32LE (pushU32LE (buf.push 8) a) b
      | .neg a => buf := pushU32LE (buf.push 9) a
    buf := pushU64LE buf c.zeros.size
    for z in c.zeros do
      buf := pushU32LE buf z
    buf := pushU64LE buf c.lookups.size
    for lk in c.lookups do
      buf := pushU32LE buf lk.multiplicity
      buf := pushU64LE buf lk.args.size
      for a in lk.args do
        buf := pushU32LE buf a
  return buf

/-- Canonical Protocol `v6` (`Fp^3`) verifying-key digest under
`BLAKE3_derive_key("multi-stark/v6/vk")` (`CertiFri.P3.Blake3Domain.verifyingKey`). -/
def computeVkDigest (circuits : Array SysCircuit) : D :=
  Blake3Domain.verifyingKey.hash (vkDigestPreimage circuits)

/-! ## 2. Circuit & Verifying-Key Structural Validation -/

private def checkCircuitMeta (c : SysCircuit) : Except String Unit := do
  if c.preprocessedHeight == 0 then
    unless c.preprocessedWidth == 0 do
      throw s!"vk: nonzero preprocessed_width {c.preprocessedWidth} with zero preprocessed_height"
  else
    unless c.preprocessedWidth > 0 do
      throw s!"vk: zero preprocessed_width with nonzero preprocessed_height {c.preprocessedHeight}"
    unless c.preprocessedHeight &&& (c.preprocessedHeight - 1) == 0 do
      throw s!"vk: preprocessed_height {c.preprocessedHeight} is not a power of two"
  unless 1 ≤ c.lookupGroupSize && c.lookupGroupSize ≤ MAX_LOOKUP_GROUP do
    throw s!"vk: bad lookup group size {c.lookupGroupSize} (expected 1..={MAX_LOOKUP_GROUP})"
  unless c.lookupPrefixLen ≤ c.nodes.size do
    throw s!"vk: lookup_prefix_len {c.lookupPrefixLen} exceeds node_count {c.nodes.size}"

private def checkCircuitNodeBounds (c : SysCircuit) : Except String Unit := do
  let s2Width := c.stage2Width
  for node in c.nodes do
    match node with
    | .publicInput idx =>
      unless idx < LOOKUP_NUM_PUBLICS do
        throw s!"vk: public index {idx} out of bounds ({LOOKUP_NUM_PUBLICS})"
    | .var src _ col =>
      let width := match src with
        | .preprocessed => c.preprocessedWidth
        | .main => c.mainWidth
        | .stage2 => s2Width
      unless col < width do
        throw s!"vk: {repr src} column index {col} out of bounds ({width})"
    | _ => pure ()

private def checkCircuitZeroDegrees (c : SysCircuit) (degrees : Array Nat) : Except String Nat := do
  let mut userMaxDeg := 0
  for z in c.zeros do
    let some d := degrees[z]?
      | throw s!"vk: zero node id {z} out of bounds ({c.nodes.size})"
    userMaxDeg := max userMaxDeg d
  pure userMaxDeg

/-- Validate every per-circuit invariant enforced by `crates/stark-key/src/lib.rs`
(`decode_circuit`, `check_compiler_contexts`) and `multi-stark/src/system.rs`:
preprocessed width/height consistency & power-of-two height, lookup group size `1..=8`,
topological order + `u32` degree recomputation, column/public bounds, zero-root bounds,
`checkCompilerContexts` (`LookupsPlain` + no `Stage2` reachable from `zeros`), derived
`maxConstraintDegree` equality, and PCS blowup degree budget. -/
def validateSysCircuit (logBlowup : Nat) (c : SysCircuit) : Except String Unit := do
  checkCircuitMeta c
  unless checkTopological c.nodes do
    throw "vk: circuit graph is not in topological order"
  let degrees ← recomputeDegrees? c.nodes
  checkCircuitNodeBounds c
  let userMaxDeg ← checkCircuitZeroDegrees c degrees
  checkCompilerContexts c
  let lookupDeg := deriveLookupDegree degrees c.lookups c.lookupGroupSize
  let expectedMaxDeg := max userMaxDeg lookupDeg
  unless expectedMaxDeg == c.maxConstraintDegree do
    throw s!"vk: max_constraint_degree {c.maxConstraintDegree} does not match derived {expectedMaxDeg}"
  unless respectsBlowupBudget logBlowup c do
    throw s!"vk: max_constraint_degree {c.maxConstraintDegree} (quotient degree {c.quotientDegree}) exceeds blowup budget 2^{logBlowup}"

private def checkPreprocessedTrailer (sys : StarkSystem) : Except String Unit := do
  unless sys.preprocessedIndices.size == sys.circuits.size do
    throw s!"vk: preprocessed_indices length {sys.preprocessedIndices.size} != circuit count {sys.circuits.size}"
  let mut ranked := 0
  let mut maxPrepLog := 0
  for ci in [0:sys.circuits.size] do
    let some c := sys.circuits[ci]? | throw "internal error: circuit index out of bounds"
    let some idxOpt := sys.preprocessedIndices[ci]?
      | throw "internal error: preprocessed index out of bounds"
    let hasPrep := c.preprocessedHeight > 0
    match idxOpt with
    | none =>
      if hasPrep then
        throw s!"vk: circuit {ci} has preprocessed_height {c.preprocessedHeight} but no preprocessed index"
    | some v =>
      if !hasPrep then
        throw s!"vk: circuit {ci} has preprocessed index {v} but zero preprocessed_height"
      unless v == ranked do
        throw s!"vk: preprocessed index {v} is not the circuit's rank {ranked}"
      ranked := ranked + 1
      maxPrepLog := max maxPrepLog (Nat.log2 c.preprocessedHeight)
  match sys.preprocessedCommit, ranked != 0 with
  | some cap, true =>
    unless cap.size > 0 && cap.size &&& (cap.size - 1) == 0 do
      throw s!"vk: preprocessed commitment has {cap.size} roots, not a power of two"
    let maxPrepLdeLog := maxPrepLog + sys.params.logBlowup
    let shift := min sys.params.capHeight maxPrepLdeLog
    unless shift < 32 do
      throw s!"vk: preprocessed cap root count overflow (shift {shift})"
    let expectedRoots := 1 <<< shift
    unless cap.size == expectedRoots do
      throw s!"vk: preprocessed commitment has {cap.size} roots, expected {expectedRoots}"
  | none, false => pure ()
  | some _, false =>
    throw "vk: preprocessed commitment present with no preprocessed circuits"
  | none, true =>
    throw s!"vk: missing preprocessed commitment for {ranked} preprocessed circuits"

/-- Validate every structural invariant of a decoded `StarkSystem` matching
`crates/stark-key/src/lib.rs` (everything enforced by `from_bytes_below_floor`, plus the
blowup budget and compiler-context checks; security-floor checks live in `Preamble.lean`). -/
def validateStarkSystemStructural (sys : StarkSystem) : Except String Unit := do
  unless sys.params.commitPowBits ≤ MAX_PROOF_OF_WORK_BITS do
    throw s!"vk: commit proof of work of {sys.params.commitPowBits} bits exceeds {MAX_PROOF_OF_WORK_BITS}"
  unless sys.params.queryPowBits ≤ MAX_PROOF_OF_WORK_BITS do
    throw s!"vk: query proof of work of {sys.params.queryPowBits} bits exceeds {MAX_PROOF_OF_WORK_BITS}"
  sys.circuits.toList.forM (validateSysCircuit sys.params.logBlowup)
  let computed := computeVkDigest sys.circuits
  unless sys.vkDigest == computed do
    throw "vk: vk_digest mismatch: serialized header digest does not match decoded circuits"
  checkPreprocessedTrailer sys

private theorem except_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {r : β} (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

private theorem forM_except_ok_forall {α : Type} {f : α → Except String Unit} :
    ∀ {l : List α}, l.forM f = .ok () → ∀ x ∈ l, f x = .ok ()
  | [], _, _, hx => nomatch hx
  | hd :: tl, h, x, hx => by
    change (f hd >>= fun _ => tl.forM f) = .ok () at h
    obtain ⟨_, hhd, htl⟩ := except_bind_ok h
    cases hx with
    | head => exact hhd
    | tail _ hmem => exact forM_except_ok_forall htl x hmem

/-- Every circuit accepted by `validateSysCircuit` satisfies `Topological`, `checkLookupsPlain`,
`LookupsPlain`, and `respectsBlowupBudget`. -/
theorem validateSysCircuit_sound {logBlowup : Nat} {c : SysCircuit}
    (h : validateSysCircuit logBlowup c = .ok ()) :
    c.Topological ∧ checkLookupsPlain c = true ∧ c.LookupsPlain ∧
      c.quotientDegree ≤ 2 ^ logBlowup := by
  unfold validateSysCircuit at h
  obtain ⟨_, _, h1⟩ := except_bind_ok h
  have htopo : checkTopological c.nodes = true := by
    cases ht : checkTopological c.nodes with
    | true => rfl
    | false =>
      simp only [ht, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
        bind, Except.bind] at h1
      cases h1
  simp only [htopo, ↓reduceIte] at h1
  obtain ⟨degs, _, h2⟩ := except_bind_ok h1
  obtain ⟨_, _, h3⟩ := except_bind_ok h2
  obtain ⟨umd, _, h4⟩ := except_bind_ok h3
  obtain ⟨_, hcc, h5⟩ := except_bind_ok h4
  have hdegEq : (max umd (deriveLookupDegree degs c.lookups c.lookupGroupSize) == c.maxConstraintDegree) = true := by
    cases hd : (max umd (deriveLookupDegree degs c.lookups c.lookupGroupSize) == c.maxConstraintDegree) with
    | true => rfl
    | false =>
      simp only [hd, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
        bind, Except.bind] at h5
      cases h5
  simp only [hdegEq, ↓reduceIte] at h5
  have hbb : respectsBlowupBudget logBlowup c = true := by
    cases hb : respectsBlowupBudget logBlowup c with
    | true => rfl
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw] at h5
      cases h5
  exact ⟨checkTopological_sound htopo,
    checkCompilerContexts_implies_checkLookupsPlain hcc,
    checkCompilerContexts_implies_lookupsPlain hcc,
    (respectsBlowupBudget_iff logBlowup c).mp hbb⟩

/-- Every system accepted by `validateStarkSystemStructural` has a matching canonical `vk_digest`
and every circuit in it satisfies `Topological`, `LookupsPlain`, and the blowup degree budget. -/
theorem validateStarkSystemStructural_sound {sys : StarkSystem}
    (h : validateStarkSystemStructural sys = .ok ()) :
    sys.vkDigest = computeVkDigest sys.circuits ∧
      ∀ c ∈ sys.circuits,
        c.Topological ∧ checkLookupsPlain c = true ∧ c.LookupsPlain ∧
          c.quotientDegree ≤ 2 ^ sys.params.logBlowup := by
  unfold validateStarkSystemStructural at h
  have hcp : sys.params.commitPowBits ≤ MAX_PROOF_OF_WORK_BITS := by
    by_cases hc : sys.params.commitPowBits ≤ MAX_PROOF_OF_WORK_BITS
    · exact hc
    · simp only [hc, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      cases h
  simp only [hcp, ↓reduceIte] at h
  have hqp : sys.params.queryPowBits ≤ MAX_PROOF_OF_WORK_BITS := by
    by_cases hq : sys.params.queryPowBits ≤ MAX_PROOF_OF_WORK_BITS
    · exact hq
    · simp only [hq, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      cases h
  simp only [hqp, ↓reduceIte] at h
  obtain ⟨_, hcs, h1⟩ := except_bind_ok h
  have hvk : (sys.vkDigest == computeVkDigest sys.circuits) = true := by
    cases hv : (sys.vkDigest == computeVkDigest sys.circuits) with
    | true => rfl
    | false =>
      simp only [hv, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw,
        bind, Except.bind] at h1
      cases h1
  refine ⟨beq_iff_eq.mp hvk, fun c hc => ?_⟩
  have hmem : c ∈ sys.circuits.toList := Array.mem_toList_iff.mpr hc
  exact validateSysCircuit_sound (forM_except_ok_forall hcs c hmem)

/-! ## 3. Verifying-Key (`StarkSystem`) Wire Codec (Protocol `v6` dense format) -/

private def readGraphNode (nodeIdx : Nat) : DecodeM GraphNode := do
  let tag ← readU8
  match tag.toNat with
  | 0 =>
    let v ← readU16LE
    pure (.const (Goldilocks.ofUInt64 (UInt64.ofNat v)))
  | 1 =>
    let raw ← readU64LE
    if raw.toNat ≤ 0xFFFF then
      throw s!"vk: non-canonical ConstBig encoding for {raw}"
    match Goldilocks.ofCanonical? raw with
    | some v => pure (.const v)
    | none => throw s!"vk: non-canonical Goldilocks constant {raw}"
  | 2 =>
    let idx ← readU8
    pure (.publicInput idx.toNat)
  | 3 => pure .isFirstRow
  | 4 => pure .isLastRow
  | 5 => pure .isTransition
  | 6 =>
    let a ← readU16LE
    let b ← readU16LE
    unless a < nodeIdx && b < nodeIdx do
      throw s!"vk: add child out of topological order ({a}, {b}) at node {nodeIdx}"
    pure (.add a b)
  | 7 =>
    let a ← readU16LE
    let b ← readU16LE
    unless a < nodeIdx && b < nodeIdx do
      throw s!"vk: sub child out of topological order ({a}, {b}) at node {nodeIdx}"
    pure (.sub a b)
  | 8 =>
    let a ← readU16LE
    let b ← readU16LE
    unless a < nodeIdx && b < nodeIdx do
      throw s!"vk: mul child out of topological order ({a}, {b}) at node {nodeIdx}"
    pure (.mul a b)
  | 9 =>
    let a ← readU16LE
    unless a < nodeIdx do
      throw s!"vk: neg child out of topological order ({a}) at node {nodeIdx}"
    pure (.neg a)
  | t =>
    if 10 ≤ t && t ≤ 15 then
      let code := t - 10
      let src := match code / 2 with
        | 0 => ColSource.preprocessed
        | 1 => ColSource.main
        | _ => ColSource.stage2
      let off := if code % 2 == 0 then RowOffset.current else RowOffset.next
      let col ← readU16LE
      pure (.var src off col)
    else
      throw s!"unknown GraphNode tag {t}"

private def readSysCircuit : DecodeM SysCircuit := do
  let mainWidth ← readU16LE
  let preprocessedWidth ← readU16LE
  let preprocessedHeight ← readU32LE
  let maxConstraintDegree ← readU16LE
  let lookupGroupSize := (← readU8).toNat
  let nodeCount ← readU16LE
  let lookupPrefixLen ← readU16LE
  unless lookupPrefixLen ≤ nodeCount do
    throw s!"vk: lookup_prefix_len {lookupPrefixLen} exceeds node_count {nodeCount}"
  let mut nodes := Array.mkEmpty nodeCount
  for idx in [0:nodeCount] do
    nodes := nodes.push (← readGraphNode idx)
  let zeroCount ← readU16LE
  let zeros ← readArray zeroCount readU16LE
  let lookupCount ← readU16LE
  let lookups ← readArray lookupCount do
    let multiplicity ← readU16LE
    let argCount ← readU16LE
    let args ← readArray argCount readU16LE
    pure { multiplicity, args }
  pure {
    mainWidth, preprocessedWidth, preprocessedHeight, maxConstraintDegree
    lookupGroupSize, lookupPrefixLen, nodes, zeros, lookups
  }

private def readStarkSystemRaw : DecodeM StarkSystem := do
  let protoVer ← readU16LE
  unless protoVer == 6 do
    throw s!"vk: only Protocol v6 is accepted, got {protoVer}"
  let extDeg ← readU16LE
  unless extDeg == 3 do
    throw s!"vk: only Fp^3 cubic extension (degree 3) is accepted, got {extDeg}"
  let friBatching ← readU16LE
  unless friBatching == 1 do
    throw s!"vk: only FriBatching::Tensor (tag 1) is accepted, got {friBatching}"
  let vkDigest ← readDigest
  let params : StarkParams := {
    logBlowup := ← readU16LE
    capHeight := ← readU16LE
    logFinalPolyLen := ← readU16LE
    maxLogArity := ← readU16LE
    numQueries := ← readU16LE
    commitPowBits := ← readU16LE
    queryPowBits := ← readU16LE
  }
  let circuitCount ← readU16LE
  let circuits ← readArray circuitCount readSysCircuit
  let preprocessedCommit ← match ← readU8 with
    | 0 => pure none
    | 1 =>
      let capLen ← readU16LE
      let cap ← readArray capLen readDigest
      unless capLen > 0 && capLen &&& (capLen - 1) == 0 do
        throw s!"vk: preprocessed commitment has {capLen} roots, not a power of two"
      pure (some cap)
    | b => throw s!"invalid preprocessed commit flag {b}"
  let preprocessedIndices ← readArray circuitCount do
    let idx ← readU16LE
    pure (if idx == 0xFFFF then none else some idx)
  ensureEOF
  pure ({ vkDigest, params, circuits, preprocessedCommit, preprocessedIndices } : StarkSystem)

/-- Decode a Protocol `v6` Multi-STARK verifying key (`crates/stark-key/src/lib.rs`,
`SystemDeserialize.lean:319-348`), enforcing every structural invariant, compiler context,
derived degree, blowup budget, canonical `vk_digest`, and preprocessed trailer check. -/
def StarkSystem.fromBytes (bytes : ByteArray) : Except String StarkSystem := do
  let (sys, _) ← readStarkSystemRaw.run { bytes, pos := 0 }
  validateStarkSystemStructural sys
  pure sys

/-- Soundness of `StarkSystem.fromBytes`: any successfully decoded key has a verified canonical
`vk_digest` and every circuit in it satisfies `Topological`, `checkLookupsPlain`, `LookupsPlain`,
and the PCS blowup degree budget. -/
theorem StarkSystem.fromBytes_sound {bytes : ByteArray} {sys : StarkSystem}
    (h : StarkSystem.fromBytes bytes = .ok sys) :
    sys.vkDigest = computeVkDigest sys.circuits ∧
      ∀ c ∈ sys.circuits,
        c.Topological ∧ checkLookupsPlain c = true ∧ c.LookupsPlain ∧
          c.quotientDegree ≤ 2 ^ sys.params.logBlowup := by
  unfold StarkSystem.fromBytes at h
  obtain ⟨⟨s, _⟩, _, h1⟩ := except_bind_ok h
  obtain ⟨_, hv, h2⟩ := except_bind_ok h1
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  subst h2
  exact validateStarkSystemStructural_sound hv

/-- Serialize a `StarkSystem` in the Protocol `v6` dense verifying-key wire format
(`crates/stark-key/src/lib.rs`, `to_bytes`). -/
def StarkSystem.toBytes (sys : StarkSystem) : ByteArray := Id.run do
  let mut buf := ByteArray.empty
  buf := pushU16LE buf 6
  buf := pushU16LE buf 3
  buf := pushU16LE buf 1
  buf := buf ++ sys.vkDigest.toBytes
  buf := pushU16LE buf sys.params.logBlowup
  buf := pushU16LE buf sys.params.capHeight
  buf := pushU16LE buf sys.params.logFinalPolyLen
  buf := pushU16LE buf sys.params.maxLogArity
  buf := pushU16LE buf sys.params.numQueries
  buf := pushU16LE buf sys.params.commitPowBits
  buf := pushU16LE buf sys.params.queryPowBits
  buf := pushU16LE buf sys.circuits.size
  for c in sys.circuits do
    buf := pushU16LE buf c.mainWidth
    buf := pushU16LE buf c.preprocessedWidth
    buf := pushU32LE buf c.preprocessedHeight
    buf := pushU16LE buf c.maxConstraintDegree
    buf := buf.push c.lookupGroupSize.toUInt8
    buf := pushU16LE buf c.nodes.size
    buf := pushU16LE buf c.lookupPrefixLen
    for node in c.nodes do
      match node with
      | .const v =>
        if v.toNat ≤ 0xFFFF then
          buf := pushU16LE (buf.push 0) v.toNat
        else
          buf := Goldilocks.pushBytes (buf.push 1) v
      | .publicInput idx =>
        buf := (buf.push 2).push idx.toUInt8
      | .isFirstRow => buf := buf.push 3
      | .isLastRow => buf := buf.push 4
      | .isTransition => buf := buf.push 5
      | .add a b => buf := pushU16LE (pushU16LE (buf.push 6) a) b
      | .sub a b => buf := pushU16LE (pushU16LE (buf.push 7) a) b
      | .mul a b => buf := pushU16LE (pushU16LE (buf.push 8) a) b
      | .neg a => buf := pushU16LE (buf.push 9) a
      | .var src off col =>
        let srcCode : Nat := match src with
          | .preprocessed => 0
          | .main => 1
          | .stage2 => 2
        let offCode : Nat := match off with
          | .current => 0
          | .next => 1
        buf := pushU16LE (buf.push (10 + 2 * srcCode + offCode).toUInt8) col
    buf := pushU16LE buf c.zeros.size
    for z in c.zeros do
      buf := pushU16LE buf z
    buf := pushU16LE buf c.lookups.size
    for lk in c.lookups do
      buf := pushU16LE buf lk.multiplicity
      buf := pushU16LE buf lk.args.size
      for a in lk.args do
        buf := pushU16LE buf a
  match sys.preprocessedCommit with
  | none => buf := buf.push 0
  | some cap =>
    buf := pushU16LE (buf.push 1) cap.size
    for d in cap do
      buf := buf ++ d.toBytes
  for idxOpt in sys.preprocessedIndices do
    match idxOpt with
    | none => buf := pushU16LE buf 0xFFFF
    | some idx => buf := pushU16LE buf idx
  return buf

/-! ## 4. `BatchProof` Decoder (bincode v2 `LittleEndian + Fixint`) -/

private def readMerkleCap : DecodeM (Array D) :=
  readVec readDigest

private def readPrunedPaths : DecodeM (PrunedPaths D) := do
  let siblingHashes ← readVec readDigest
  pure { siblingHashes }

private def readOpenedRound : DecodeM OpenedRound :=
  readVec (readVec (readVec readEF))

private def readBatchOpening : DecodeM (BatchOpening F (PrunedPaths D)) := do
  let openedValues ← readVec (readVec (readVec readCanonicalF))
  let openingProof ← readPrunedPaths
  pure { openedValues, openingProof }

private def readCommitPhaseStep : DecodeM (CommitPhaseStep EF (PrunedPaths D)) := do
  let logArity := (← readU8).toNat
  let siblingValues ← readVec (readVec readEF)
  let openingProof ← readPrunedPaths
  pure { logArity, siblingValues, openingProof }

private def readFriProof : DecodeM (FriProof F EF D (PrunedPaths D) (PrunedPaths D)) := do
  -- Bincode layout of `p3_fri::TwoAdicFriPcsProof` / `FriProof` (mirrors `ProofDeserialize.lean`):
  -- commit_phase_commits : Vec<MerkleCap> (for cap_height = 0 each cap has length 1)
  let commitCaps ← readVec readMerkleCap
  let mut commitPhaseCommits := Array.mkEmpty commitCaps.size
  for cap in commitCaps do
    unless cap.size == 1 do
      throw s!"expected cap length 1 in FRI commit phase, got {cap.size}"
    let some root := cap[0]? | throw "internal error: empty FRI commit cap"
    commitPhaseCommits := commitPhaseCommits.push root
  let commitPowWitnesses ← readVec readCanonicalF
  let inputOpenings ← readVec readBatchOpening
  let commitPhaseOpenings ← readVec readCommitPhaseStep
  let finalPoly ← readVec readEF
  let queryPowWitness ← readCanonicalF
  pure {
    commitPhaseCommits
    commitPowWitnesses
    inputOpenings
    commitPhaseOpenings
    finalPoly
    queryPowWitness
  }

private def readShardProof : DecodeM ShardProof := do
  let active ← readVec readBool
  let stage1Trace ← readMerkleCap
  let stage2Trace ← readMerkleCap
  let quotientChunks ← readMerkleCap
  let commitments : ShardCommitments := { stage1Trace, stage2Trace, quotientChunks }
  let intermediateAccumulators ← readVec readEF
  let logDegrees := (← readVec readU8).map UInt8.toNat
  let openingProof ← readFriProof
  let quotientOpenedValues ← readOpenedRound
  let preprocessedOpenedValues ← readOption readOpenedRound
  let stage1OpenedValues ← readOpenedRound
  let stage2OpenedValues ← readOpenedRound
  pure {
    active, commitments, intermediateAccumulators, logDegrees, openingProof
    quotientOpenedValues, preprocessedOpenedValues, stage1OpenedValues, stage2OpenedValues
  }

private def readShardHeader : DecodeM ShardHeader := do
  let active ← readVec readBool
  let stage1Trace ← readMerkleCap
  let logDegrees := (← readVec readU8).map UInt8.toNat
  let claims ← readVec (readVec readCanonicalF)
  pure { active, stage1Trace, logDegrees, claims }

private def readBatchMessage : DecodeM BatchMessage := do
  let args ← readVec readCanonicalF
  let multiplicity ← readCanonicalF
  pure { args, multiplicity }

/-- Decode a serialized `BatchProof` (`multi-stark/src/batch.rs`),
enforcing strict canonical Goldilocks values, 3-limb `GoldilocksExt3`, strict tags, and exact EOF. -/
def BatchProof.fromBytes (bytes : ByteArray) : Except String BatchProof := do
  let (batch, _) ← (do
    let headers ← readVec readShardHeader
    let messages ← readVec readBatchMessage
    let proofs ← readVec readShardProof
    ensureEOF
    pure ({ preamble := { headers, messages }, proofs } : BatchProof)
  ).run { bytes, pos := 0 }
  pure batch

/-- Decode serialized expected claims (`Vec<Vec<Val>>` bincode). -/
def decodeClaims (bytes : ByteArray) : Except String (Array (Array F)) := do
  let (claims, _) ← (do
    let cs ← readVec (readVec readCanonicalF)
    ensureEOF
    pure cs
  ).run { bytes, pos := 0 }
  pure claims

end Ix.Cert.MultiStark
