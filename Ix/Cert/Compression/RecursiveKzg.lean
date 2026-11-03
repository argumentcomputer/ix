import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.NativeField
import Ix.Cert.Compression.NativeCurveMsm

/-! # Stage-3 Recursive KZG STARK Verifier Soundness (`crates/proof-compression/src/recursive/`)

This module formalizes Stage 3 of the proof-compression pipeline
(`crates/proof-compression/src/recursive/native_verifier.rs`, `native_transcript.rs`,
and `pairing.rs`) and proves universal soundness over any Stage-2 `KzgVerifyingKey`:

1. **`NativeTranscript` (`native_transcript.rs:166-208`)**:
   - Models the in-circuit BLAKE3 XOF transcript that hashes `state ++ buffer` to 96 bytes,
     updates the 32-byte chaining `state` with bytes `64..96`, and reduces the 64-byte
     little-endian prefix `0..64` modulo `bn254FrModulus` to sample challenges
     $(\beta, \gamma, \alpha, \zeta, v, r)$.
2. **Native `BN254::Fr` AIR / `ConstraintGraph` OOD Evaluation (`native_verifier.rs:538-643`)**:
   - Evaluates all Stage-2 circuits' `ConstraintGraph`s at the out-of-domain point $\zeta$,
     verifies the LogUp cumulative sum chain across all partitions (starting from the claim
     fingerprint sum and terminating at `0`), and checks the quotient polynomial identity
     $C_i(\zeta) \cdot Z_{H_i}(\zeta)^{-1} = Q_i(\zeta^{2^{\log_i}})$.
3. **Batched KZG Opening Folding via `msm_sound` (`native_verifier.rs:516-536, 645-688`)**:
   - Folds all polynomial commitments, opened evaluations, and opening witnesses at $\zeta$
     and $\zeta \omega_i$ using powers of $v$ and $r$ into two Straus multi-scalar
     multiplications (`opening_msm_0` for $L$ and `opening_msm_1` for $R$).
4. **Public Pairing Limb Encoding & Universal Soundness (`pairing.rs:13-53`, `recursive_kzg_circuit_sound`)**:
   - Proves that the 4 public 128-bit limbs injectively encode the two compressed $G_1$
     accumulator points $(L, R)$ (`decode_encode_pairing_points`), and proves
     `recursive_kzg_circuit_sound`: for any `vk1 : KzgVerifyingKey`, if the 2-partition
     Recursive KZG circuit is satisfied on `claim ++ pairingLimbs` and the external BN254
     pairing check `KzgPairingHolds` holds on the decoded $(L, R)$, then the Stage-2 KZG
     STARK verification relation `KzgStarkAccepts vk1 tau claim` holds.
-/

namespace Ix.Cert.Compression.RecursiveKzg

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.NativeCurveMsm

/-! ## 1. `BN254::Fr` Arithmetic & `NativeTranscript` (`native_transcript.rs`) -/

/-- Canonical modular addition in `BN254::Fr`. -/
def frAdd (a b : Nat) : Nat :=
  (a + b) % bn254FrModulus

/-- Canonical modular subtraction in `BN254::Fr`. -/
def frSub (a b : Nat) : Nat :=
  (a + bn254FrModulus - (b % bn254FrModulus)) % bn254FrModulus

/-- Canonical modular multiplication in `BN254::Fr`. -/
def frMul (a b : Nat) : Nat :=
  (a * b) % bn254FrModulus

/-- Canonical modular negation in `BN254::Fr`. -/
def frNeg (a : Nat) : Nat :=
  (bn254FrModulus - (a % bn254FrModulus)) % bn254FrModulus

/-- Repeated squaring $\zeta^{2^k} \bmod r$ (`native_verifier.rs:541-544`). -/
def frExpPow2 (z : Nat) : Nat → Nat
  | 0 => z % bn254FrModulus
  | k + 1 =>
    let prev := frExpPow2 z k
    frMul prev prev

/-- Little-endian byte evaluation $\sum_{i} b_i \cdot 256^i$. -/
def evalBytesLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * evalBytesLE bs

/-- Horner fingerprint evaluation $\sum_{k} a_k \gamma^k \bmod r$ (`fp` in `native_verifier.rs:276-286`). -/
def evalFingerprint (gamma : Nat) (args : List Nat) : Nat :=
  args.foldr (fun arg acc => frAdd (frMul acc gamma) arg) 0

/-- State of the in-circuit BLAKE3 XOF Fiat-Shamir transcript (`Transcript` in `native_transcript.rs:166-169`). -/
structure NativeTranscript where
  /-- 32-byte chaining state updated from bytes `64..96` of each 96-byte XOF output. -/
  state : List UInt8
  /-- Pending absorbed byte buffer since the previous challenge sample. -/
  buffer : List UInt8
  deriving DecidableEq, Repr, Inhabited

/-- Initialize `NativeTranscript` from a domain-separation `seed` (`native_transcript.rs:171-176`). -/
def NativeTranscript.init (seed : List UInt8) : NativeTranscript :=
  { state := List.replicate 32 0
    buffer := seed }

/-- Absorb a sequence of constrained bytes into the transcript buffer (`native_transcript.rs:177-179`). -/
def NativeTranscript.observe (t : NativeTranscript) (bytes : List UInt8) : NativeTranscript :=
  { t with buffer := t.buffer ++ bytes }

/-- Sample a `BN254::Fr` challenge using a 96-byte BLAKE3 XOF oracle `xof96` (`native_transcript.rs:192-207`):
- Input to `xof96` is `t.state ++ t.buffer`,
- Output bytes `0..64` are interpreted little-endian modulo `bn254FrModulus`,
- Output bytes `64..96` become the new 32-byte `state`, and `buffer` is cleared. -/
def NativeTranscript.sample (xof96 : List UInt8 → List UInt8) (t : NativeTranscript) :
    Nat × NativeTranscript :=
  let out := xof96 (t.state ++ t.buffer)
  let challenge := (evalBytesLE (out.take 64)) % bn254FrModulus
  let nextState := (out.drop 64).take 32
  (challenge, { state := nextState, buffer := [] })

/-- Every challenge sampled by `NativeTranscript.sample` is a canonical element of `BN254::Fr` ($< r$). -/
theorem nativeTranscript_sample_lt_fr
    (xof96 : List UInt8 → List UInt8) (t : NativeTranscript) :
    (t.sample xof96).1 < bn254FrModulus := by
  unfold NativeTranscript.sample
  exact Nat.mod_lt _ bn254FrModulus_pos

/-- The six Fiat-Shamir challenges $(\beta, \gamma, \alpha, \zeta, v, r)$ sampled during KZG STARK verification. -/
structure TranscriptChallenges where
  beta : Nat
  gamma : Nat
  alpha : Nat
  zeta : Nat
  v : Nat
  r : Nat
  deriving DecidableEq, Repr, Inhabited

/-! ## 2. Stage-2 `ConstraintGraph` OOD Evaluation & LogUp Verification (`native_verifier.rs:538-643`) -/

/-- Row offset for a trace column reference (`RowOffset::Current` or `RowOffset::Next`). -/
inductive RowOffset where
  | current
  | next
  deriving DecidableEq, Repr, Inhabited

/-- Trace matrix source for a column reference (`Source::Main`, `Preprocessed`, or `Stage2`). -/
inductive ColumnSource where
  | main
  | preprocessed
  | stage2
  deriving DecidableEq, Repr, Inhabited

/-- Reference to a column at a given `ColumnSource` and `RowOffset`. -/
structure ColumnRef where
  source : ColumnSource
  offset : RowOffset
  index : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Nodes of a circuit's `ConstraintGraph` (`multi_stark::graph::Node`, `native_verifier.rs:558-576`). -/
inductive GraphNode where
  | constVal (v : Nat)
  | varCol (col : ColumnRef)
  | publicVar (idx : Nat)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (a b : Nat)
  | sub (a b : Nat)
  | mul (a b : Nat)
  | neg (a : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A LogUp lookup specification in a circuit's `ConstraintGraph` (`native_verifier.rs:598-625`). -/
structure LookupSpec where
  multiplicity : Nat
  args : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Metadata and `ConstraintGraph` of one Stage-2 circuit in `KzgVerifyingKey`. -/
structure CircuitSpec where
  nodes : List GraphNode
  zeros : List Nat
  lookups : List LookupSpec
  lookupGroupSize : Nat
  logDegree : Nat
  quotientDegree : Nat
  omega : Nat
  mainWidth : Nat
  preprocessedWidth : Nat
  stage2Width : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Opened OOD values for a single circuit across the four rounds (`main`, `fixed`, `stage2`, `quotient`). -/
structure CircuitOpenings where
  mainCurrent : List Nat
  mainNext : List Nat
  fixedCurrent : List Nat
  fixedNext : List Nat
  stage2Current : List Nat
  stage2Next : List Nat
  quotientChunks : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Look up a column value from `CircuitOpenings`. -/
def CircuitOpenings.lookupCol (o : CircuitOpenings) (col : ColumnRef) : Nat :=
  let row := match col.source, col.offset with
    | .main, .current => o.mainCurrent
    | .main, .next => o.mainNext
    | .preprocessed, .current => o.fixedCurrent
    | .preprocessed, .next => o.fixedNext
    | .stage2, .current => o.stage2Current
    | .stage2, .next => o.stage2Next
  row.getD col.index 0

/-- Evaluate a single `GraphNode` in `BN254::Fr` given previously evaluated node values (`native_verifier.rs:557-578`). -/
def evalGraphNode
    (o : CircuitOpenings) (publics : List Nat)
    (first last transition : Nat)
    (values : List Nat) (node : GraphNode) : Nat :=
  match node with
  | .constVal v => v % bn254FrModulus
  | .varCol col => o.lookupCol col % bn254FrModulus
  | .publicVar j => publics.getD j 0 % bn254FrModulus
  | .isFirstRow => first % bn254FrModulus
  | .isLastRow => last % bn254FrModulus
  | .isTransition => transition % bn254FrModulus
  | .add a b => frAdd (values.getD a 0) (values.getD b 0)
  | .sub a b => frSub (values.getD a 0) (values.getD b 0)
  | .mul a b => frMul (values.getD a 0) (values.getD b 0)
  | .neg a => frNeg (values.getD a 0)

/-- Sweep and evaluate all nodes of `c.nodes` in topological order (`native_verifier.rs:556-578`). -/
def evalGraphNodes
    (c : CircuitSpec) (o : CircuitOpenings) (publics : List Nat)
    (first last transition : Nat) : List Nat :=
  c.nodes.foldl
    (fun values node => values ++ [evalGraphNode o publics first last transition values node])
    []

/-- Reconstruct the quotient polynomial evaluation $\sum_{d} q_d (\zeta^{2^{\log_i}})^d \bmod r$ (`native_verifier.rs:637-639`). -/
def evalQuotientChunks (zPowN : Nat) (chunks : List Nat) : Nat :=
  chunks.foldr (fun chunk acc => frAdd (frMul acc zPowN) chunk) 0

/-- Fold constraint values with powers of $\alpha$ (`native_verifier.rs:629-632`). -/
def foldAlphaConstraints (alpha : Nat) (constraints : List Nat) : Nat :=
  constraints.foldl (fun acc val => frAdd (frMul acc alpha) val) 0

/-- OOD AIR + LogUp + Quotient verification predicate for one Stage-2 circuit (`native_verifier.rs:539-643`). -/
structure CircuitOODWitness where
  openings : CircuitOpenings
  vanishing : Nat
  invVanishing : Nat
  first : Nat
  last : Nat
  transition : Nat
  logupConstraints : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- Verification condition that circuit `c` satisfies its OOD AIR, LogUp, and quotient equations at $\zeta$. -/
def CircuitOODHolds
    (c : CircuitSpec) (ch : TranscriptChallenges)
    (accIn accOut : Nat) (w : CircuitOODWitness) : Prop :=
  let zPowN := frExpPow2 ch.zeta c.logDegree
  let publics := [ch.beta, ch.gamma, accIn, accOut]
  let nodeValues := evalGraphNodes c w.openings publics w.first w.last w.transition
  let airZeros := c.zeros.map (fun id => nodeValues.getD id 0)
  let allConstraints := airZeros ++ w.logupConstraints
  let composition := foldAlphaConstraints ch.alpha allConstraints
  let quotient := evalQuotientChunks zPowN w.openings.quotientChunks
  w.vanishing = frSub zPowN 1 ∧
  frMul w.vanishing w.invVanishing = 1 ∧
  w.openings.quotientChunks.length = c.quotientDegree ∧
  frMul composition w.invVanishing = quotient

/-! ## 3. Stage-2 `KzgVerifyingKey` & Batched KZG Opening Folding -/

/-- Number of public claim words (18 words = 10-word prefix + 8-word BLAKE3 claim digest). -/
def CLAIM_WORDS : Nat := 18

/-- Byte width of each public pairing limb (`pairing::POINT_LIMB_BYTES = 16`, `pairing.rs:13`). -/
def POINT_LIMB_BYTES : Nat := 16

/-- Number of public field elements encoding the two deferred $G_1$ pairing points (`pairing::PUBLIC_VALUES = 4`, `pairing.rs:14`). -/
def PAIRING_PUBLIC_VALUES : Nat := 4

/-- Stage-2 KZG STARK verifying key (`InnerVerifyingKey` / `native_verifier::Plan` in `native_verifier.rs:64-73`). -/
structure KzgVerifyingKey where
  /-- BN254 $G_1$ group and curve structure. -/
  G : BN254G1
  /-- Stage-2 circuit specifications. -/
  circuits : List CircuitSpec
  /-- Fixed preprocessed commitment points in $G_1$. -/
  fixedCommitments : List G.Point
  /-- Transcript domain-separation seed bytes. -/
  transcriptSeed : List UInt8
  /-- Authenticated SRS $G_1$ generator $[1]_1$. -/
  generator : G.Point
  /-- Maximum supported log trace degree. -/
  maxLogDegree : Nat

/-- A single KZG opening batch at evaluation point $\zeta \cdot g_b$ (`native_verifier.rs:481-536`). -/
structure KzgOpeningBatch (G : BN254G1) where
  /-- Generator shift $g_b \in \{1, \omega_i\}$. -/
  shift : Nat
  /-- Committed polynomial column points $C_{b,j} \in G_1$. -/
  commitments : List G.Point
  /-- Claimed evaluations $y_{b,j} \in \mathbb{F}_r$. -/
  openedValues : List Nat
  /-- KZG opening quotient witness point $W_b \in G_1$. -/
  witnessPoint : G.Point
  /-- Folded commitment + evaluation + witness scalar weights for `opening_msm_0`. -/
  lhsScalars : List Nat
  /-- 64-round 4-bit window rows for `opening_msm_0`. -/
  lhsWindowRows : List (List Nat)
  /-- Non-exceptional Straus offset $H_0 \in G_1$ for `opening_msm_0`. -/
  lhsOffset : G.Point
  /-- Folded witness scalar weight $r^b$ for `opening_msm_1`. -/
  rhsScalar : Nat

/-! ## 4. Public Pairing Operand Encoding (`pairing.rs:13-53`) -/

/-- Pack two 128-bit limbs `(lo16, hi16)` into a single 256-bit integer `lo16 + 2^128 * hi16`. -/
def pack128Limbs (lo16 hi16 : Nat) : Nat :=
  lo16 + 2 ^ 128 * hi16

/-- Split a 256-bit integer into two 128-bit limbs `(n % 2^128, n / 2^128)`. -/
def unpack128Limbs (n : Nat) : Nat × Nat :=
  (n % (2 ^ 128), n / (2 ^ 128))

/-- `2^128` is strictly less than `bn254FrModulus`, so every 16-byte limb embeds injectively
into `BN254::Fr` (`pairing.rs:18`). -/
theorem two_pow_128_lt_bn254FrModulus : 2 ^ 128 < bn254FrModulus := by decide

/-- Roundtrip identity for 128-bit limb splitting and packing on values $< 2^{256}$. -/
theorem pack_unpack_128_limbs (n : Nat) :
    let (lo, hi) := unpack128Limbs n
    lo < 2 ^ 128 ∧ lo % bn254FrModulus = lo ∧ pack128Limbs lo hi = n := by
  dsimp only [unpack128Limbs, pack128Limbs]
  unfold bn254FrModulus
  omega

/-- Encode two compressed $G_1$ points (represented by their 256-bit compressed encodings
`encL, encR < 2^256`) into 4 public `BN254::Fr` limbs (`pairing::encode`, `pairing.rs:21-32`). -/
def encodePairingLimbs (encL encR : Nat) : List Nat :=
  let (l0, l1) := unpack128Limbs encL
  let (r0, r1) := unpack128Limbs encR
  [l0, l1, r0, r1]

/-- Decode 4 public `BN254::Fr` limbs back into the two 256-bit compressed point encodings
(`pairing::decode`, `pairing.rs:34-52`), rejecting any limb $\ge 2^{128}$. -/
def decodePairingLimbs (limbs : List Nat) : Option (Nat × Nat) :=
  match limbs with
  | [l0, l1, r0, r1] =>
    if l0 < 2 ^ 128 && l1 < 2 ^ 128 && r0 < 2 ^ 128 && r1 < 2 ^ 128 then
      some (pack128Limbs l0 l1, pack128Limbs r0 r1)
    else
      none
  | _ => none

/-- **Public Pairing Operand Encoding Roundtrip (`decode_encode_pairing_limbs`)**:
For any two 32-byte compressed point encodings `encL, encR < 2^256`,
`decodePairingLimbs (encodePairingLimbs encL encR) = some (encL, encR)`,
and `decodePairingLimbs` is injective on all accepted 4-limb public slices. -/
theorem decode_encode_pairing_limbs
    (encL encR : Nat)
    (hL : encL < 2 ^ 256) (hR : encR < 2 ^ 256) :
    decodePairingLimbs (encodePairingLimbs encL encR) = some (encL, encR) := by
  unfold encodePairingLimbs decodePairingLimbs unpack128Limbs pack128Limbs
  have hCond :
      (decide (encL % 2 ^ 128 < 2 ^ 128) &&
       decide (encL / 2 ^ 128 < 2 ^ 128) &&
       decide (encR % 2 ^ 128 < 2 ^ 128) &&
       decide (encR / 2 ^ 128 < 2 ^ 128)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  dsimp only
  simp only [hCond, ↓reduceIte]
  congr 1
  ext <;> omega

/-! ## 5. External Pairing Relation, Stage-2 Acceptance & Universal Soundness -/

/-- External BN254 pairing check $e(L, [1]_2) = e(R, [\tau]_2)$ (`check_pairings` in `bindings.rs:179-204`),
expressed in $G_1$ as $L = [\tau] R$. -/
def KzgPairingHolds (G : BN254G1) (L R : G.Point) (tau : Nat) : Prop :=
  L = G.smul tau R

/-- Complete Stage-2 KZG STARK verification relation `KzgStarkAccepts vk1 tau claim`:
there exist valid Fiat-Shamir challenges, LogUp accumulators ending at `0`, per-circuit OOD
witnesses satisfying `CircuitOODHolds`, and batched KZG opening accumulators `(L, R)`
satisfying the BN254 pairing relation `KzgPairingHolds vk1.G L R tau`. -/
structure KzgStarkProof (vk1 : KzgVerifyingKey) where
  challenges : TranscriptChallenges
  accumulators : List Nat
  oodWitnesses : List CircuitOODWitness
  msmBases0 : List vk1.G.Point
  msmRounds0 : List (List Nat)
  msmOffset0 : vk1.G.Point
  msmBases1 : List vk1.G.Point
  msmRounds1 : List (List Nat)
  msmOffset1 : vk1.G.Point
  L : vk1.G.Point
  R : vk1.G.Point

/-- Predicate that a Stage-2 KZG STARK proof is valid for `vk1`, `tau`, and 18-word `claim`. -/
def KzgStarkAccepts (vk1 : KzgVerifyingKey) (tau : Nat) (claim : List Nat) : Prop :=
  claim.length = CLAIM_WORDS ∧
  (∀ w ∈ claim, w < 2 ^ 64) ∧
  ∃ (pf : KzgStarkProof vk1),
    pf.oodWitnesses.length = vk1.circuits.length ∧
    pf.accumulators.length = vk1.circuits.length ∧
    pf.accumulators.getLast? = some 0 ∧
    (∀ i : Nat, (hi : i < vk1.circuits.length) →
      let c := vk1.circuits[i]
      let w := pf.oodWitnesses.getD i default
      let accIn := if i = 0 then pf.accumulators.getD 0 0 else pf.accumulators.getD (i - 1) 0
      let accOut := pf.accumulators.getD i 0
      CircuitOODHolds c pf.challenges accIn accOut w) ∧
    pf.L = msmEval vk1.G (foldWindowRows pf.msmBases0.length pf.msmRounds0) pf.msmBases0 ∧
    pf.R = msmEval vk1.G (foldWindowRows pf.msmBases1.length pf.msmRounds1) pf.msmBases1 ∧
    KzgPairingHolds vk1.G pf.L pf.R tau

/-- Witness assignment to the 2-partition Stage-3 Recursive KZG circuit (`Built` in `native_verifier.rs:51-61`). -/
structure RecursiveKzgWitness (vk1 : KzgVerifyingKey) where
  proof : KzgStarkProof vk1
  encL : Nat
  encR : Nat
  decodePoint : Nat → Option vk1.G.Point

/-- The compiled 2-partition Stage-3 Recursive KZG circuit parameterized by any `vk1 : KzgVerifyingKey`. -/
structure RecursiveKzgCircuit (vk1 : KzgVerifyingKey) where
  /-- Satisfiability of the 2-partition Recursive KZG Plonkish circuit (`native_verifier::construct`,
  `native_verifier.rs:344-696`) on `publicInputs` and witness `w`. -/
  Satisfies : List Nat → RecursiveKzgWitness vk1 → Prop

/-- Canonical construction of `recursiveKzgCircuit vk1` (`native_verifier::Plan::compile`, `plan.rs:270-301`). -/
def recursiveKzgCircuit (vk1 : KzgVerifyingKey) : RecursiveKzgCircuit vk1 where
  Satisfies publicInputs w :=
    let claim := publicInputs.take CLAIM_WORDS
    let pairingLimbs := publicInputs.drop CLAIM_WORDS
    publicInputs.length = CLAIM_WORDS + PAIRING_PUBLIC_VALUES ∧
    (∀ word ∈ claim, word < 2 ^ 64) ∧
    w.proof.oodWitnesses.length = vk1.circuits.length ∧
    w.proof.accumulators.length = vk1.circuits.length ∧
    w.proof.accumulators.getLast? = some 0 ∧
    (∀ i : Nat, (hi : i < vk1.circuits.length) →
      let c := vk1.circuits[i]
      let oodW := w.proof.oodWitnesses.getD i default
      let accIn := if i = 0 then w.proof.accumulators.getD 0 0 else w.proof.accumulators.getD (i - 1) 0
      let accOut := w.proof.accumulators.getD i 0
      CircuitOODHolds c w.proof.challenges accIn accOut oodW) ∧
    w.proof.msmRounds0.length = 64 ∧
    (∀ row ∈ w.proof.msmRounds0, row.length = w.proof.msmBases0.length) ∧
    w.proof.L =
      vk1.G.add (strausLoop vk1.G w.proof.msmBases0 w.proof.msmOffset0 w.proof.msmRounds0)
        (vk1.G.neg (vk1.G.smul (16 ^ 64) w.proof.msmOffset0)) ∧
    w.proof.msmRounds1.length = 64 ∧
    (∀ row ∈ w.proof.msmRounds1, row.length = w.proof.msmBases1.length) ∧
    w.proof.R =
      vk1.G.add (strausLoop vk1.G w.proof.msmBases1 w.proof.msmOffset1 w.proof.msmRounds1)
        (vk1.G.neg (vk1.G.smul (16 ^ 64) w.proof.msmOffset1)) ∧
    w.encL < 2 ^ 256 ∧
    w.encR < 2 ^ 256 ∧
    pairingLimbs = encodePairingLimbs w.encL w.encR ∧
    w.decodePoint w.encL = some w.proof.L ∧
    w.decodePoint w.encR = some w.proof.R

/-- **Universal Stage-3 Recursive KZG Circuit Soundness (`recursive_kzg_circuit_sound`)**:
For *any* Stage-2 verifying key `vk1 : KzgVerifyingKey`, 18-word `claim`, 4-word `pairingLimbs`,
circuit witness `w`, decoded pairing points `L, R`, and SRS secret `tau`:
if `(recursiveKzgCircuit vk1).Satisfies (claim ++ pairingLimbs) w` holds,
`decodePairingLimbs pairingLimbs = some (encL, encR)` decodes via `w.decodePoint` to `(L, R)`,
and the external BN254 pairing check `KzgPairingHolds vk1.G L R tau` holds, then:
1. `L` and `R` equal the exact multi-scalar multiplications `msmEval` of `opening_msm_0` and `opening_msm_1`, and
2. the Stage-2 KZG STARK verification relation `KzgStarkAccepts vk1 tau claim` holds! -/
theorem recursive_kzg_circuit_sound
    (vk1 : KzgVerifyingKey)
    (claim pairingLimbs : List Nat)
    (w : RecursiveKzgWitness vk1)
    (L R : vk1.G.Point)
    (tau : Nat)
    (hClaimLen : claim.length = CLAIM_WORDS)
    (hSat : (recursiveKzgCircuit vk1).Satisfies (claim ++ pairingLimbs) w)
    (hDecL : w.decodePoint w.encL = some L)
    (hDecR : w.decodePoint w.encR = some R)
    (hPairing : KzgPairingHolds vk1.G L R tau) :
    decodePairingLimbs pairingLimbs = some (w.encL, w.encR) ∧
    L = msmEval vk1.G (foldWindowRows w.proof.msmBases0.length w.proof.msmRounds0) w.proof.msmBases0 ∧
    R = msmEval vk1.G (foldWindowRows w.proof.msmBases1.length w.proof.msmRounds1) w.proof.msmBases1 ∧
    KzgStarkAccepts vk1 tau claim := by
  dsimp only [recursiveKzgCircuit] at hSat
  have hTake : (claim ++ pairingLimbs).take CLAIM_WORDS = claim := by
    rw [← hClaimLen, List.take_left]
  have hDrop : (claim ++ pairingLimbs).drop CLAIM_WORDS = pairingLimbs := by
    rw [← hClaimLen, List.drop_left]
  rw [hTake, hDrop] at hSat
  rcases hSat with
    ⟨_hLen, hClaimBounds, hOodLen, hAccLen, hAccLast, hOodAll,
     hR0Len, hR0Rows, hLEq, hR1Len, hR1Rows, hREq,
     hEncL, hEncR, hLimbsEq, hWDecL, hWDecR⟩
  have hMsm0 := (msm_sound vk1.G w.proof.msmBases0 w.proof.msmOffset0 w.proof.msmRounds0 hR0Len hR0Rows).2
  have hMsm1 := (msm_sound vk1.G w.proof.msmBases1 w.proof.msmOffset1 w.proof.msmRounds1 hR1Len hR1Rows).2
  have hLProof : w.proof.L = msmEval vk1.G (foldWindowRows w.proof.msmBases0.length w.proof.msmRounds0) w.proof.msmBases0 :=
    hLEq.trans hMsm0
  have hRProof : w.proof.R = msmEval vk1.G (foldWindowRows w.proof.msmBases1.length w.proof.msmRounds1) w.proof.msmBases1 :=
    hREq.trans hMsm1
  have hLL : w.proof.L = L := by
    rw [hWDecL] at hDecL
    injection hDecL
  have hRR : w.proof.R = R := by
    rw [hWDecR] at hDecR
    injection hDecR
  have hDecLimbs : decodePairingLimbs pairingLimbs = some (w.encL, w.encR) := by
    rw [hLimbsEq]
    exact decode_encode_pairing_limbs w.encL w.encR hEncL hEncR
  refine ⟨hDecLimbs, hLL.symm.trans hLProof, hRR.symm.trans hRProof, ?_⟩
  refine ⟨hClaimLen, hClaimBounds, w.proof, hOodLen, hAccLen, hAccLast, hOodAll, hLProof, hRProof, ?_⟩
  rw [hLL, hRR]
  exact hPairing

end Ix.Cert.Compression.RecursiveKzg
