import Ix.Cert.Aggr.MonolithicRom
import Ix.Cert.Compression.FriVerifier

/-! # Endpoint 1a: Native `Fp^3` `v6` Transparent STARK Shrinker Certification

Models and certifies the 1-circuit fixed-layout Native `Fp^3` `v6` transparent STARK Shrinker
verifying an inner `v6` aggregated root inside `MultiStark` + `FriVerifier`, where BOTH the
outer shrinker and the inner aggregation tree live in the **same pure Random Oracle Model**
(ZERO elliptic curves, ZERO SRS, ZERO `gnark` assumptions):

1. **Exact `multi-stark/v6` & `v6-zk` BLAKE3 `derive_key` Domain Separation (`Blake3Domain`):**
   Pins all 11 BLAKE3 domain modes, all 10 context strings, and all 10 precomputed 8-word
   context keys matching `multi-stark/src/p3_adapter/domain_blake3.rs` byte-for-byte, proving
   `Blake3Domain.keyWords_injective` and strict pairwise separation across `plain` (`v5`),
   `v6`, and `v6-zk`.
2. **128-Bit Native `Fp^3` `v6` Shrinker Profile (`StarkShrinkerV6Config`, `StarkShrinkerV6ProfileOk`):**
   - `GoldilocksExt3` (`extDegree = 3`, `|F| = p^3 ≥ 2^191`),
   - 48-byte BLAKE3 XOF (`digestBytes = 48`, `|D| = 2^384`, incremental sponge `c = 3/2`),
   - `FriBatching::Tensor`, 1-circuit fixed layout (`numCircuits = 1`), `queryPowBits ≥ 20`,
   - Query floors: `lb = 2, q ≥ 160` (UD) or `lb ∈ {2, 3, 4}` with `q ≥ {118, 78, 58}` (Johnson),
   - Exact kernel-verified real-number query soundness bounds (`starkShrinker_query_soundness_128`).
3. **Public-Input Digest Binding (`StarkShrinkerPublicBinding`):**
   Binds `shrinkerVkDigest` (pinned) and `shrinkerClaimDigest` (8 Goldilocks words) across
   outer shrinker ↔ `FriVerifier` ↔ inner `Aggr` root, with injectivity
   (`starkShrinker_publicBinding_injective`).
4. **Pure-ROM End-to-End Theorems (`starkShrinker_v6_sound_128`,
   `starkShrinker_v6_concrete_prob_128`):**
   Composes `MonolithicRom.monolithic_multiNode_rom_sound` + `FriVerifier.friVerifierCircuit_sound`
   + `Aggr.acceptedAggrTree_refines_derivation19` with ZERO curve/SRS/pairing hypotheses.
5. **Constructive Negative Controls:**
   Rejects `v5` / `plain` BLAKE3, `Fp^2`, 32-byte digests, `FriBatching::Powers`, under-queried
   profiles, and mismatched VK / claim digests.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`,
strictly `[propext, Classical.choice, Quot.sound]`.
-/

namespace Ix.Cert.Compression.StarkShrinker

open CertiFri.Oracle
open CertiFri.Oracle.OracleComp
open Ix.Cert.Aggr.MonolithicRom
open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.FriVerifier

/-! ## 1. Exact `multi-stark` Protocol Modes & BLAKE3 `derive_key` Domain Separation -/

/-- Protocol version tag distinguishing legacy `v5`, transparent 128-bit `v6`, and hiding `v6-zk`. -/
inductive ProtocolVersion where
  | v5
  | v6
  | v6Zk
  deriving DecidableEq, Repr, Inhabited

/-- FRI batching mode (`FriBatching::Powers` vs `FriBatching::Tensor`). -/
inductive FriBatchingMode where
  | powers
  | tensor
  deriving DecidableEq, Repr, Inhabited

/-- Proximity-gap soundness regime for 128-bit FRI query floors. -/
inductive SoundnessRegime where
  | uniqueDecoding
  | johnson
  deriving DecidableEq, Repr, Inhabited

/-- 8-word BLAKE3 chaining value / `derive_key` context key. -/
structure Blake3KeyWords where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  deriving DecidableEq, Repr

/-- Exact 11 BLAKE3 domains from `multi-stark/src/p3_adapter/domain_blake3.rs:171-194`. -/
inductive Blake3Domain where
  | plain
  | merkleLeaf
  | merkleCompress
  | transcriptSingle
  | transcriptBatch
  | verifyingKey
  | zkMerkleLeaf
  | zkMerkleCompress
  | zkTranscriptSingle
  | zkTranscriptBatch
  | zkVerifyingKey
  deriving DecidableEq, Repr, Inhabited

/-- Exact `derive_key` context string for each domain (`none` for legacy unkeyed `plain`). -/
def Blake3Domain.context : Blake3Domain → Option String
  | .plain              => none
  | .merkleLeaf         => some "multi-stark/v6/merkle/leaf"
  | .merkleCompress     => some "multi-stark/v6/merkle/compress"
  | .transcriptSingle   => some "multi-stark/v6/transcript/single"
  | .transcriptBatch    => some "multi-stark/v6/transcript/batch"
  | .verifyingKey       => some "multi-stark/v6/vk"
  | .zkMerkleLeaf       => some "multi-stark/v6-zk/merkle/leaf"
  | .zkMerkleCompress   => some "multi-stark/v6-zk/merkle/compress"
  | .zkTranscriptSingle => some "multi-stark/v6-zk/transcript/single"
  | .zkTranscriptBatch  => some "multi-stark/v6-zk/transcript/batch"
  | .zkVerifyingKey     => some "multi-stark/v6-zk/vk"

/-- Precomputed 8-word BLAKE3 chaining value (`BLAKE3_IV` for `plain`, or the exact
`derive_key` context key matching `domain_blake3.rs` and `CertiFriP3/DomainSep.lean`). -/
def Blake3Domain.keyWords : Blake3Domain → Blake3KeyWords
  | .plain =>
    ⟨0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
     0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19⟩
  | .merkleLeaf =>
    ⟨0x77042819, 0x5A1DD04F, 0x2F8D0BB8, 0x39D27832,
     0x552A30F6, 0x546C9899, 0x8510A8EF, 0x83ECCD66⟩
  | .merkleCompress =>
    ⟨0xCC4D7633, 0xF8492FEC, 0x5704B1FD, 0x2D69A6B5,
     0xA871EBB5, 0x6439610D, 0x89E86BE6, 0x02E22A34⟩
  | .transcriptSingle =>
    ⟨0x943C1E0F, 0x12B98B0B, 0x1FDA3556, 0x96ECBE49,
     0xF5D6684E, 0xBABD2C79, 0x7E6FD057, 0x4BF1113F⟩
  | .transcriptBatch =>
    ⟨0x56945548, 0x0BAEB2C2, 0xB0BC28DD, 0x9EBE2699,
     0xD7B24F82, 0x35470F4D, 0x065F18D3, 0xF3B2994F⟩
  | .verifyingKey =>
    ⟨0xD7089665, 0x2D51B3C7, 0x1E371C33, 0x324E12A1,
     0xB355FBFF, 0x402B8A4A, 0xD8256C89, 0xB1F439C2⟩
  | .zkMerkleLeaf =>
    ⟨0x8A663924, 0x051A410E, 0xB5929C7A, 0x52E6E08C,
     0x51D3B0FA, 0x1D1687C6, 0x472E9E06, 0x5A324ECA⟩
  | .zkMerkleCompress =>
    ⟨0x6E9B081E, 0xBAEEB5DA, 0x18652A0D, 0xA2D1B4E1,
     0x9E40FB01, 0xE905254D, 0x451628D5, 0x3D606842⟩
  | .zkTranscriptSingle =>
    ⟨0x89D8BDA2, 0xBDAE2046, 0x9274DB73, 0x13010FD9,
     0xC59663AB, 0x1A374FE0, 0x9FA807DF, 0xA485833F⟩
  | .zkTranscriptBatch =>
    ⟨0x761A4520, 0x275E7AD5, 0xAF9417AE, 0x5177E5AE,
     0x0E64CF93, 0x68F8718A, 0x15874B68, 0x9F503445⟩
  | .zkVerifyingKey =>
    ⟨0x486C73BD, 0x64F0F532, 0xF4D92A23, 0xAE0C2406,
     0x097D11FF, 0x4783BEC5, 0x55B051EF, 0x118424A1⟩

/-- Extra BLAKE3 block flags (`0` for `plain`, `DERIVE_KEY_MATERIAL = 64` for all keyed modes). -/
def Blake3Domain.domainFlags : Blake3Domain → UInt32
  | .plain => 0
  | _      => 64

/-- Predicate identifying the 5 non-ZK `v6` domains. -/
def Blake3Domain.isV6 : Blake3Domain → Bool
  | .merkleLeaf | .merkleCompress | .transcriptSingle | .transcriptBatch | .verifyingKey => true
  | _ => false

/-- Predicate identifying the 5 `v6-zk` domains. -/
def Blake3Domain.isZk : Blake3Domain → Bool
  | .zkMerkleLeaf | .zkMerkleCompress | .zkTranscriptSingle | .zkTranscriptBatch
  | .zkVerifyingKey => true
  | _ => false

/-- All 11 BLAKE3 domains have pairwise distinct 8-word initial chaining values (`keyWords`). -/
theorem Blake3Domain.keyWords_injective : Function.Injective Blake3Domain.keyWords := by
  intro d₁ d₂
  cases d₁ <;> cases d₂ <;> decide

/-- All 11 BLAKE3 domains have pairwise distinct `derive_key` context strings (`none` for `plain`). -/
theorem Blake3Domain.context_injective : Function.Injective Blake3Domain.context := by
  intro d₁ d₂
  cases d₁ <;> cases d₂ <;> decide

/-- Every `v6` domain is strictly separated from `plain` and from every `v6-zk` domain. -/
theorem Blake3Domain.v6_keyWords_ne_nonV6 {d₁ d₂ : Blake3Domain}
    (h₁ : d₁.isV6 = true) (h₂ : d₂.isV6 = false) :
    d₁.keyWords ≠ d₂.keyWords := by
  intro heq
  have h := Blake3Domain.keyWords_injective heq
  subst h
  rw [h₁] at h₂
  cases h₂

/-- Every `v6-zk` domain is strictly separated from every non-ZK (`v6` or `plain`) domain. -/
theorem Blake3Domain.v6Zk_keyWords_ne_nonZk {d₁ d₂ : Blake3Domain}
    (h₁ : d₁.isZk = true) (h₂ : d₂.isZk = false) :
    d₁.keyWords ≠ d₂.keyWords := by
  intro heq
  have h := Blake3Domain.keyWords_injective heq
  subst h
  rw [h₁] at h₂
  cases h₂

/-! ## 2. 128-Bit Native `Fp^3` `v6` STARK Shrinker Configuration & Query Soundness -/

/-- Configuration record for the 1-circuit fixed-layout Native `Fp^3` `v6` STARK Shrinker. -/
structure StarkShrinkerV6Config where
  version          : ProtocolVersion
  extDegree        : ℕ
  digestBytes      : ℕ
  batching         : FriBatchingMode
  regime           : SoundnessRegime
  logBlowup        : ℕ
  numQueries       : ℕ
  queryPowBits     : ℕ
  numCircuits      : ℕ
  leafDomain       : Blake3Domain
  compressDomain   : Blake3Domain
  transcriptDomain : Blake3Domain
  vkDomain         : Blake3Domain
  pinnedVkDigest   : List UInt8
  deriving DecidableEq, Repr

/-- Exact 128-bit query floor predicate for `v6` Native `Fp^3` STARK Shrinker profiles:
- Unique decoding: `lb = 2`, `q ≥ 160` (with `queryPowBits ≥ 20`),
- Johnson regime: `lb ∈ {2, 3, 4}` with `q ≥ {118, 78, 58}` (with `queryPowBits ≥ 20`). -/
def v6QueryFloorOk (regime : SoundnessRegime) (logBlowup numQueries queryPowBits : ℕ) : Prop :=
  20 ≤ queryPowBits ∧
  match regime with
  | .uniqueDecoding => logBlowup = 2 ∧ 160 ≤ numQueries
  | .johnson =>
      (logBlowup = 2 ∧ 118 ≤ numQueries) ∨
      (logBlowup = 3 ∧ 78 ≤ numQueries) ∨
      (logBlowup = 4 ∧ 58 ≤ numQueries)

/-- **Profile Acceptance Predicate for Endpoint 1a (`StarkShrinkerV6ProfileOk`):**
Enforces:
1. Protocol version `v6`,
2. Cubic Goldilocks extension `Fp^3` (`extDegree = 3`, `|F| ≥ 2^191`),
3. 48-byte BLAKE3 XOF (`digestBytes = 48`, `|D| = 2^384`, `pinnedVkDigest.length = 48`),
4. `FriBatching::Tensor`,
5. 1-circuit fixed-layout shrinker (`numCircuits = 1`),
6. 128-bit query floor (`v6QueryFloorOk`),
7. Strict `v6` BLAKE3 `derive_key` domain separation. -/
def StarkShrinkerV6ProfileOk (cfg : StarkShrinkerV6Config) : Prop :=
  cfg.version = .v6 ∧
  cfg.extDegree = 3 ∧
  cfg.digestBytes = 48 ∧
  cfg.pinnedVkDigest.length = 48 ∧
  cfg.batching = .tensor ∧
  cfg.numCircuits = 1 ∧
  v6QueryFloorOk cfg.regime cfg.logBlowup cfg.numQueries cfg.queryPowBits ∧
  cfg.leafDomain = .merkleLeaf ∧
  cfg.compressDomain = .merkleCompress ∧
  (cfg.transcriptDomain = .transcriptSingle ∨ cfg.transcriptDomain = .transcriptBatch) ∧
  cfg.vkDomain = .verifyingKey

/-- Proximity agreement parameter `θ` associated with each 128-bit shrinker profile:
- UD (`lb = 2`): `θ = 5 / 8` (`(1 + 1/4) / 2`),
- Johnson (`lb = 2`): `θ = 65 / 128` (`> √(1/4) = 1/2`),
- Johnson (`lb = 3`): `θ = 46 / 128` (`> √(1/8)`),
- Johnson (`lb = 4`): `θ = 33 / 128` (`> √(1/16) = 1/4`). -/
noncomputable def shrinkerProximityTheta (regime : SoundnessRegime) (logBlowup : ℕ) : ℝ :=
  match regime, logBlowup with
  | .uniqueDecoding, 2 => 5 / 8
  | .johnson, 2        => 65 / 128
  | .johnson, 3        => 46 / 128
  | .johnson, 4        => 33 / 128
  | _, _               => 1

private theorem pow_div_pow_le_two_neg_128 {a b q powBits : ℕ}
    (hb : 0 < b) (_hq : 0 < q)
    (hfrac : a ≤ b)
    (hq_min : ∃ q₀, q₀ ≤ q ∧ a ^ q₀ * 2 ^ 128 ≤ b ^ q₀ * 2 ^ 20)
    (hpow : 20 ≤ powBits) :
    ((a : ℝ) / (b : ℝ)) ^ q / (2 : ℝ) ^ powBits ≤ 1 / (2 : ℝ) ^ 128 := by
  obtain ⟨q₀, hq₀, hnat⟩ := hq_min
  have hbpos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have h0 : (0 : ℝ) ≤ (a : ℝ) / (b : ℝ) := by positivity
  have hle1 : (a : ℝ) / (b : ℝ) ≤ 1 := (div_le_one hbpos).mpr (by exact_mod_cast hfrac)
  have hmono_q : ((a : ℝ) / (b : ℝ)) ^ q ≤ ((a : ℝ) / (b : ℝ)) ^ q₀ :=
    pow_le_pow_of_le_one h0 hle1 hq₀
  have hmono_p : (2 : ℝ) ^ (20 : ℕ) ≤ (2 : ℝ) ^ powBits :=
    pow_le_pow_right₀ (by norm_num) hpow
  have hstep1 : ((a : ℝ) / (b : ℝ)) ^ q / (2 : ℝ) ^ powBits ≤
      ((a : ℝ) / (b : ℝ)) ^ q₀ / (2 : ℝ) ^ (20 : ℕ) := by
    calc ((a : ℝ) / (b : ℝ)) ^ q / (2 : ℝ) ^ powBits
        ≤ ((a : ℝ) / (b : ℝ)) ^ q₀ / (2 : ℝ) ^ powBits :=
          div_le_div_of_nonneg_right hmono_q (by positivity)
      _ ≤ ((a : ℝ) / (b : ℝ)) ^ q₀ / (2 : ℝ) ^ (20 : ℕ) :=
          div_le_div_of_nonneg_left (pow_nonneg h0 _) (by positivity) hmono_p
  refine hstep1.trans ?_
  rw [div_pow, div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hnat

/-- **Kernel-Verified 128-Bit Query Soundness Across All Four `v6` Shrinker Regimes
(`starkShrinker_query_soundness_128`):**
For EVERY profile satisfying `v6QueryFloorOk`, the FRI query soundness error
`θ^numQueries / 2^queryPowBits` is strictly `≤ 1 / 2^128`! -/
theorem starkShrinker_query_soundness_128 {regime : SoundnessRegime}
    {logBlowup numQueries queryPowBits : ℕ}
    (hOk : v6QueryFloorOk regime logBlowup numQueries queryPowBits) :
    (shrinkerProximityTheta regime logBlowup) ^ numQueries / (2 : ℝ) ^ queryPowBits ≤
      1 / (2 : ℝ) ^ 128 := by
  obtain ⟨hpow, hreg⟩ := hOk
  cases regime with
  | uniqueDecoding =>
    obtain ⟨rfl, hq⟩ := hreg
    unfold shrinkerProximityTheta
    exact pow_div_pow_le_two_neg_128 (a := 5) (b := 8) (by decide) (by omega) (by decide)
      ⟨160, hq, by decide⟩ hpow
  | johnson =>
    rcases hreg with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ | ⟨rfl, hq⟩
    · unfold shrinkerProximityTheta
      exact pow_div_pow_le_two_neg_128 (a := 65) (b := 128) (by decide) (by omega) (by decide)
        ⟨118, hq, by decide⟩ hpow
    · unfold shrinkerProximityTheta
      exact pow_div_pow_le_two_neg_128 (a := 46) (b := 128) (by decide) (by omega) (by decide)
        ⟨78, hq, by decide⟩ hpow
    · unfold shrinkerProximityTheta
      exact pow_div_pow_le_two_neg_128 (a := 33) (b := 128) (by decide) (by omega) (by decide)
        ⟨58, hq, by decide⟩ hpow

/-! ### Canonical Endpoint 1a (`v6`) Shrinker Profiles (Positive Certificates) -/

def canonicalV6VkDigest : List UInt8 := List.replicate 48 0x6A

def v6ShrinkerUd128 : StarkShrinkerV6Config where
  version          := .v6
  extDegree        := 3
  digestBytes      := 48
  batching         := .tensor
  regime           := .uniqueDecoding
  logBlowup        := 2
  numQueries       := 160
  queryPowBits     := 20
  numCircuits      := 1
  leafDomain       := .merkleLeaf
  compressDomain   := .merkleCompress
  transcriptDomain := .transcriptSingle
  vkDomain         := .verifyingKey
  pinnedVkDigest   := canonicalV6VkDigest

def v6ShrinkerJohnsonLb2 : StarkShrinkerV6Config :=
  { v6ShrinkerUd128 with regime := .johnson, logBlowup := 2, numQueries := 118 }

def v6ShrinkerJohnsonLb3 : StarkShrinkerV6Config :=
  { v6ShrinkerUd128 with regime := .johnson, logBlowup := 3, numQueries := 78 }

def v6ShrinkerJohnsonLb4 : StarkShrinkerV6Config :=
  { v6ShrinkerUd128 with regime := .johnson, logBlowup := 4, numQueries := 58 }

theorem v6ShrinkerUd128_ok : StarkShrinkerV6ProfileOk v6ShrinkerUd128 :=
  ⟨rfl, rfl, rfl, by decide, rfl, rfl, ⟨by decide, rfl, by decide⟩, rfl, rfl, Or.inl rfl, rfl⟩

theorem v6ShrinkerJohnsonLb2_ok : StarkShrinkerV6ProfileOk v6ShrinkerJohnsonLb2 :=
  ⟨rfl, rfl, rfl, by decide, rfl, rfl, ⟨by decide, Or.inl ⟨rfl, by decide⟩⟩, rfl, rfl, Or.inl rfl, rfl⟩

theorem v6ShrinkerJohnsonLb3_ok : StarkShrinkerV6ProfileOk v6ShrinkerJohnsonLb3 :=
  ⟨rfl, rfl, rfl, by decide, rfl, rfl, ⟨by decide, Or.inr (Or.inl ⟨rfl, by decide⟩)⟩, rfl, rfl, Or.inl rfl, rfl⟩

theorem v6ShrinkerJohnsonLb4_ok : StarkShrinkerV6ProfileOk v6ShrinkerJohnsonLb4 :=
  ⟨rfl, rfl, rfl, by decide, rfl, rfl, ⟨by decide, Or.inr (Or.inr ⟨rfl, by decide⟩)⟩, rfl, rfl, Or.inl rfl, rfl⟩

/-! ## 3. Public-Input Digest Binding (`shrinkerVkDigest` + `shrinkerClaimDigest`) -/

/-- Public statement exposed by the 1-circuit STARK Shrinker verifier:
1. `vkDigest`: pinned 48-byte BLAKE3 `derive_key("multi-stark/v6/vk")` verifying-key digest,
2. `claimDigest`: 8-word Goldilocks claim digest matching the inner aggregated root. -/
structure StarkShrinkerPublicStatement where
  vkDigest    : List UInt8
  claimDigest : Fin 8 → GoldilocksF
  deriving DecidableEq

/-- Public-input binding connecting the outer shrinker statement `(vkDigest, claimDigest)` to
the inner Goldilocks `FriVerifier` public inputs `friPub` and inner `Aggr` root claim digest
`outClaimDig`. -/
structure StarkShrinkerPublicBinding (cfg : StarkShrinkerV6Config)
    (stmt : StarkShrinkerPublicStatement)
    (friPub : List GoldilocksF)
    (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp) : Prop where
  vkPinned       : stmt.vkDigest = cfg.pinnedVkDigest
  friBindsClaim  : ∀ i : Fin 8, friPub[i.val]? = some (stmt.claimDigest i)
  aggrBindsClaim : ∀ i : Fin 8, GoldilocksF.ofNat (ZMod.val (outClaimDig i)) = stmt.claimDigest i

/-- Exact public-input binding uniqueness: equal outer shrinker statements force equal
`vkDigest`, equal `friPub[0..7]`, and equal inner `Aggr` root claim digests `outClaimDig`. -/
theorem starkShrinker_publicBinding_injective {cfg : StarkShrinkerV6Config}
    {stmt : StarkShrinkerPublicStatement}
    {friPub₁ friPub₂ : List GoldilocksF}
    {dig₁ dig₂ : Fin 8 → Ix.Cert.MultiStark.Fp}
    (h₁ : StarkShrinkerPublicBinding cfg stmt friPub₁ dig₁)
    (h₂ : StarkShrinkerPublicBinding cfg stmt friPub₂ dig₂) :
    (∀ i : Fin 8, friPub₁[i.val]? = friPub₂[i.val]?) ∧ dig₁ = dig₂ := by
  refine ⟨fun i => (h₁.friBindsClaim i).trans (h₂.friBindsClaim i).symm, funext fun i => ?_⟩
  have hcast : GoldilocksF.ofNat (ZMod.val (dig₁ i)) = GoldilocksF.ofNat (ZMod.val (dig₂ i)) :=
    (h₁.aggrBindsClaim i).trans (h₂.aggrBindsClaim i).symm
  unfold GoldilocksF.ofNat at hcast
  have hval := congrArg ZMod.val hcast
  have h1lt : ZMod.val (dig₁ i) < goldilocksP := ZMod.val_lt (dig₁ i)
  have h2lt : ZMod.val (dig₂ i) < goldilocksP := ZMod.val_lt (dig₂ i)
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at hval
  exact ZMod.val_injective _ hval

/-! ## 4. Pure-ROM 128-Bit Native `Fp^3` `v6` STARK Shrinker Soundness -/

/-- **Endpoint 1a Pure-ROM 128-Bit Soundness (`starkShrinker_v6_sound_128`):**
Composes:
- Valid Endpoint 1a `v6` shrinker profile (`StarkShrinkerV6ProfileOk cfg`: `GoldilocksExt3`,
  48B BLAKE3 XOF, `FriBatching::Tensor`, 1-circuit fixed layout, `v6` `derive_key` domains,
  128-bit UD or Johnson query floor),
- Single shared random-oracle monolithic extraction (`monolithic_multiNode_rom_sound`) over
  ALL `1 + t.verificationCount` verifications (outer shrinker + inner `v6` aggregation tree)
  using 48-byte BLAKE3 XOF (`Fintype.card D = 2 ^ 384`) and incremental sponge `c = 3 / 2`,
- In-circuit Goldilocks FRI verifier (`FriVerifier.friVerifierCircuit_sound`),
- 19-shape inner aggregation tree (`AcceptedAggrTree` → `AggrNodeHolds sem rootStmt`),
- Explicit public-input digest binding (`StarkShrinkerPublicBinding`).

**ZERO elliptic curves, ZERO SRS, ZERO `gnark` assumptions!**
Proves:
1. Pure-ROM multi-node forgery probability is bounded by `((Q + M_verif : ℕ) : ℝ) / 2^128`
   (true 128-bit ROM security with ZERO `-log₂ M` union-bound penalty!),
2. Exact FRI query error `θ^q / 2^queryPowBits ≤ 1 / 2^128`,
3. `GoldilocksExt3` field size `≥ 2^191` and strict `v6` domain separation from `plain`/`v6-zk`,
4. Inner `FriVerifierSatisfied`, `AggrNodeHolds sem rootStmt`, pinned `vkDigest`, and bound
   `claimDigest`! -/
theorem starkShrinker_v6_sound_128
    (cfg : StarkShrinkerV6Config) (hCfg : StarkShrinkerV6ProfileOk cfg)
    -- Pure-ROM monolithic multi-node experiment (outer shrinker + inner v6 aggr root)
    {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type}
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X']
    [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)]
    {D : Type} [Fintype D] [Nonempty D]
    (hDigestCard : Fintype.card D = 2 ^ (8 * cfg.digestBytes))
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax)
    (hε128 : εmax ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ 128)
    (hashBad : Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') →
      (x : MultiQuery Inst Msg Chal X') → MultiAnswer Chal Y' x → Prop)
    (hHashBad : ∀ l x, l.dlookup x = none →
      FractionLE (hashBad l x) ((2 * (3 / 2 : ℝ)) * (l.length : ℝ) / (Fintype.card D : ℝ)))
    -- Inner FRI verifier + 19-shape aggregation tree + public-input binding
    (friBase : Circuit GoldilocksF) (friLayout : FriVerifierLayout)
    (hMerkleLen : ∀ s ∈ friLayout.merkleSteps, s.2.1.length = s.2.2.1.length)
    (friPub : List GoldilocksF) (wFri : Wire → GoldilocksF)
    (hFri : (buildFriVerifierCircuit friBase friLayout).Satisfies friPub wFri)
    {sem : _root_.Aggr.AggrSemantics _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    {batchClaim : Nat → _root_.Aggr.ValidatorMode _root_.Address → (_root_.Address → Prop) →
      (_root_.Address → Prop) → (_root_.Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
    {rootStmt : _root_.Aggr.AggrNodeStmt _root_.Address _root_.Address Ix.DynamicLink.EvalAssumption
      _root_.Address Ix.Cert.MultiStark.K Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
    (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt)
    (stmt : StarkShrinkerPublicStatement) (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp)
    (hBind : StarkShrinkerPublicBinding cfg stmt friPub outClaimDig)
    -- Shared single-oracle adversary + verifier over all `1 + t.verificationCount` nodes
    {A B : Type}
    (adv : OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') A)
    {Q M_verif : ℕ} (hadv : adv.QueryBound Q)
    (verifyAll : A → OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') B)
    (hver : ∀ a, (verifyAll a).QueryBound M_verif)
    (hM20 : M_verif ≤ 2 ^ 20)
    (hN128 : Q + M_verif ≤ 2 ^ 128)
    (NodeForges : B → Fin (1 + t.verificationCount) →
      Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop)
    (hExtract : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin (1 + t.verificationCount), NodeForges b k l') →
      ¬ HasBad hashBad l' →
      ∃ (inst : Inst) (tr : Transcript Msg Chal (r inst)),
        doomed inst 0 .nil ∧ MultiSupports inst tr l' ∧ ¬ doomed inst (r inst) tr) :
    prob (fun b l' => ∃ k : Fin (1 + t.verificationCount), NodeForges b k l')
        (adv.bind verifyAll) [] ≤ ((Q + M_verif : ℕ) : ℝ) / (2 : ℝ) ^ 128 ∧
    (shrinkerProximityTheta cfg.regime cfg.logBlowup) ^ cfg.numQueries /
        (2 : ℝ) ^ cfg.queryPowBits ≤ 1 / (2 : ℝ) ^ 128 ∧
    (2 : ℕ) ^ 191 ≤ CertiFri.P3.Goldilocks.order ^ cfg.extDegree ∧
    FriVerifierSatisfied friBase friLayout friPub wFri ∧
    _root_.Aggr.AggrNodeHolds sem rootStmt ∧
    stmt.vkDigest = cfg.pinnedVkDigest ∧
    (∀ i : Fin 8, GoldilocksF.ofNat (ZMod.val (outClaimDig i)) = stmt.claimDigest i) ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs, ∃ proofBytes,
        Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) := by
  have hProbRaw := monolithic_multiNode_rom_sound (D := D) (c := 3 / 2)
    hsound hε h0 (by norm_num) hashBad hHashBad adv hadv verifyAll hver NodeForges hExtract
  have hD384 : (Fintype.card D : ℝ) = (2 : ℝ) ^ 384 := by
    rw [hDigestCard, hCfg.2.2.1, show 8 * 48 = 384 by decide, Nat.cast_pow, Nat.cast_ofNat]
  rw [hD384] at hProbRaw
  have hRate := monolithic_goldilocksExt3_xof48_rate_128 Q M_verif hM20 hN128 hε128
  unfold monolithicRomBound at hRate
  have hProb : prob (fun b l' => ∃ k : Fin (1 + t.verificationCount), NodeForges b k l')
      (adv.bind verifyAll) [] ≤ ((Q + M_verif : ℕ) : ℝ) / (2 : ℝ) ^ 128 :=
    hProbRaw.trans hRate
  have hQuery := starkShrinker_query_soundness_128 hCfg.2.2.2.2.2.2.1
  have hExt : (2 : ℕ) ^ 191 ≤ CertiFri.P3.Goldilocks.order ^ cfg.extDegree := by
    rw [hCfg.2.1]
    exact goldilocksExt3_card_ge_two_pow_191
  have hFriSat := friVerifierCircuit_sound friBase friLayout hMerkleLen friPub wFri hFri
  obtain ⟨hDeriv, hChildOk⟩ := Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19 t
  exact ⟨hProb, hQuery, hExt, hFriSat, _root_.Aggr.aggrDerivation19_invariant hDeriv,
    hBind.vkPinned, hBind.aggrBindsClaim, hChildOk⟩

/-- **Endpoint 1a Concrete `≤ 1 / 2^128` Probability Corollary (`starkShrinker_v6_concrete_prob_128`):**
Under `Q + M_verif ≤ 2^127` and `((Q + M_verif : ℕ) : ℝ) * εmax ≤ (1 / 2) / 2^128` (zero
curve/SRS/gnark assumptions), the global pure-ROM forgery probability across the outer shrinker
and all `t.verificationCount` inner nodes is literally `≤ 1 / 2^128`! -/
theorem starkShrinker_v6_concrete_prob_128
    (cfg : StarkShrinkerV6Config) (hCfg : StarkShrinkerV6ProfileOk cfg)
    {Inst Msg : Type} {Chal : ℕ → Type} {X' : Type} {Y' : X' → Type}
    [DecidableEq Inst] [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X']
    [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)]
    {D : Type} [Fintype D] [Nonempty D]
    (hDigestCard : Fintype.card D = 2 ^ (8 * cfg.digestBytes))
    {r : Inst → ℕ} {doomed : Inst → ∀ i, Transcript Msg Chal i → Prop}
    {ε : Inst → ℕ → ℝ} {εmax : ℝ}
    (hsound : MultiRbrSound r doomed ε)
    (hε : ∀ inst, ∀ i < r inst, ε inst i ≤ εmax)
    (h0 : 0 ≤ εmax)
    (hashBad : Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') →
      (x : MultiQuery Inst Msg Chal X') → MultiAnswer Chal Y' x → Prop)
    (hHashBad : ∀ l x, l.dlookup x = none →
      FractionLE (hashBad l x) ((2 * (3 / 2 : ℝ)) * (l.length : ℝ) / (Fintype.card D : ℝ)))
    {A B : Type} {M : ℕ}
    (adv : OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') A)
    {Q M_verif : ℕ} (hadv : adv.QueryBound Q)
    (verifyAll : A → OracleComp (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') B)
    (hver : ∀ a, (verifyAll a).QueryBound M_verif)
    (hM20 : M_verif ≤ 2 ^ 20)
    (hN127 : Q + M_verif ≤ 2 ^ 127)
    (hBudget : ((Q + M_verif : ℕ) : ℝ) * εmax ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ 128)
    (NodeForges : B → Fin M → Log (MultiAnswer (Inst := Inst) (Msg := Msg) Chal Y') → Prop)
    (hExtract : ∀ b l', Outcome (adv.bind verifyAll) [] b l' →
      (∃ k : Fin M, NodeForges b k l') →
      ¬ HasBad hashBad l' →
      ∃ (inst : Inst) (tr : Transcript Msg Chal (r inst)),
        doomed inst 0 .nil ∧ MultiSupports inst tr l' ∧ ¬ doomed inst (r inst) tr) :
    prob (fun b l' => ∃ k : Fin M, NodeForges b k l') (adv.bind verifyAll) [] ≤
      1 / (2 : ℝ) ^ 128 := by
  have hProbRaw := monolithic_multiNode_rom_sound (D := D) (c := 3 / 2)
    hsound hε h0 (by norm_num) hashBad hHashBad adv hadv verifyAll hver NodeForges hExtract
  have hD384 : (Fintype.card D : ℝ) = (2 : ℝ) ^ 384 := by
    rw [hDigestCard, hCfg.2.2.1, show 8 * 48 = 384 by decide, Nat.cast_pow, Nat.cast_ofNat]
  rw [hD384] at hProbRaw
  exact hProbRaw.trans (monolithic_goldilocksExt3_xof48_concrete_prob_128 Q M_verif hM20 hN127 hBudget)

/-! ## 5. Constructive Negative Controls (`v5`, `Fp^2`, 32B Digest, `Powers`, Under-Queried, Mismatched Digests) -/

/-- Rejects legacy `v5` protocol version AND plain unkeyed BLAKE3 domain. -/
theorem negControl_shrinker_v6_rejects_v5 :
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with version := .v5 } ∧
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with leafDomain := .plain } := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h.1
  · cases h.2.2.2.2.2.2.2.1

/-- Rejects quadratic extension `Fp^2` (`extDegree = 2`, which fails 128-bit field soundness). -/
theorem negControl_shrinker_v6_rejects_fp2 :
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with extDegree := 2 } ∧
    CertiFri.P3.Goldilocks.order ^ 2 < 2 ^ 128 :=
  ⟨fun h => by have := h.2.1; simp at this, negControl_fp2_below_128.1⟩

/-- Rejects 32-byte digest (`digestBytes = 32`), `FriBatching::Powers`, and under-queried
profiles (`q = 159` UD, `q = 117` Johnson at `lb = 2`). -/
theorem negControl_shrinker_v6_rejects_weak_params :
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with digestBytes := 32 } ∧
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with batching := .powers } ∧
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerUd128 with numQueries := 159 } ∧
    ¬ StarkShrinkerV6ProfileOk { v6ShrinkerJohnsonLb2 with numQueries := 117 } := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; have := h.2.2.1; simp at this
  · intro h; cases h.2.2.2.2.1
  · intro h; have := h.2.2.2.2.2.2.1; simp [v6QueryFloorOk, v6ShrinkerUd128] at this
  · intro h; have := h.2.2.2.2.2.2.1; simp [v6QueryFloorOk, v6ShrinkerJohnsonLb2, v6ShrinkerUd128] at this

/-- Rejects mismatched `shrinkerVkDigest` (`vkDigest ≠ cfg.pinnedVkDigest`). -/
theorem negControl_shrinker_v6_rejects_vk_mismatch
    (cfg : StarkShrinkerV6Config) (badVk : List UInt8) (hne : badVk ≠ cfg.pinnedVkDigest)
    (claim : Fin 8 → GoldilocksF) (friPub : List GoldilocksF)
    (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp) :
    ¬ StarkShrinkerPublicBinding cfg ⟨badVk, claim⟩ friPub outClaimDig :=
  fun h => hne h.vkPinned

/-- Rejects mismatched `shrinkerClaimDigest` at any word index `i : Fin 8`. -/
theorem negControl_shrinker_v6_rejects_claim_mismatch
    (cfg : StarkShrinkerV6Config) (stmt : StarkShrinkerPublicStatement)
    (friPub : List GoldilocksF) (outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp)
    (i : Fin 8) (hne : GoldilocksF.ofNat (ZMod.val (outClaimDig i)) ≠ stmt.claimDigest i) :
    ¬ StarkShrinkerPublicBinding cfg stmt friPub outClaimDig :=
  fun h => hne (h.aggrBindsClaim i)

end Ix.Cert.Compression.StarkShrinker
