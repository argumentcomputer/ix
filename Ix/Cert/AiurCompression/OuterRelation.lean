import Aiur.Plonk.Scs
import Ix.Cert.AiurCompression.DeferredFold
import Ix.Cert.AiurCompression.StatementBinding

/-! # Deployed `ix-aiur-scs-v1` Outer Native PLONK Relation & Two-Pair BN254 Pairing Check

Models the deployed L3 BN254 terminal pure-Rust PLONK + BSB22 verifier
(`crates/proof-compression/src/aiur_backend/plonk/native/{mod,scs_file,preprocess,prover,verifier,solidity}.rs`,
`crates/proof-compression/src/aiur_backend/plonk/scs.rs`,
`crates/proof-compression/src/aiur_backend/stages/terminal.rs`,
`crates/proof-compression/src/aiur_backend/l3_verifier.rs`, and on-chain adapter
`contracts/plonk/src/IxL3PlonkVerifier.sol`), replacing the legacy `"ix/outer-ir/v1"`
`ρ`-folded four-point outer relation:

1. **Constraint system (`Aiur.Plonk.Scs BN254Fr`):**
   Every gate, selector, coefficient, BSB22 commitment wire list, and `γ` challenge wire is
   loaded verbatim from the SHA-256-pinned `ix-aiur-scs-v1` file (`aiurScsMagic = "ixscs001"`,
   parsed by `plonk::native::scs_file::ScsFile::parse`).
   Wires `0` and `1` carry the two 128-bit public statement limbs `(stmtLow, stmtHigh)`, derived
   from constructor-pinned keys/prefixes by `IxL3PlonkVerifier.sol` and `l3_verifier.rs`.
2. **Two-pair BN254 `PairingCheck` (`check_bn254_native_outputs` in `stages/terminal.rs`):**
   The `18` output wires (`2 × 9` `affine-u80-v1` words) are range-checked as canonical
   `4 × u80/u14` `Fq` coordinates with canonical boolean infinity flags, checked on `G1`
   via `Bn254AffineCodec`, and constrained by the plain two-pair pairing equation
   `e(d0, anchors.1) · e(d1, anchors.2) = 1` (`bn254DeferredVal bp anchors (d0, d1) = 1`).
3. **Verifying-key digest binding (`aiur_scs_outer_sound`):**
   An accepted outer witness (`plonk::native::verifier::verify_native_bytes` /
   `verify_solidity_bytes` with trusted VK SHA-256 pinning and `ix-aiur-native-plonk-v1`
   `PreparedManifest`) either exhibits a concrete SHA-256 collision against the pinned
   SCS or pairing configuration bytes, or yields satisfaction of the expected `Aiur.Plonk.Scs`
   on `[(stmtLow : BN254Fr), (stmtHigh : BN254Fr)]` together with the decoded two-pair
   pairing check.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace Ix.Cert.AiurCompression

open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.OuterRelation

/-- Exact 8-byte binary header magic `"ixscs001"` (`plonk::native::scs_file::MAGIC`). -/
def aiurScsMagic : List UInt8 :=
  [105, 120, 115, 99, 115, 48, 48, 49]

/-- Exact BN254 terminal output width (`pairing::final_program::ACCUMULATOR_WORDS = 18`). -/
def aiurTerminalOutputsBN254 : Nat := 18

/-- Exact `ix-aiur-scs-v1` terminal circuit specification (`plonk::native::scs_file::ScsFile` +
`check_bn254_native_outputs` in `stages/terminal.rs`). -/
structure AiurScsOuterSpec (bp : BilinearPairing) where
  /-- Sparse PLONK constraint system emitted by `plonk_export`. -/
  scs : Aiur.Plonk.Scs BN254Fr
  /-- The 18 output wire indices (`aiurTerminalOutputsBN254 = 18`) carrying the two 9-word
  `affine-u80-v1` deferred pairing operands. -/
  outputWires : List Nat
  outputWires_len : outputWires.length = aiurTerminalOutputsBN254
  outputWires_in_range : ∀ x ∈ outputWires, x < scs.wires
  /-- Wires `0` and `1` are public inputs `(statement_low, statement_high)`. -/
  publics_ge_two : 2 ≤ scs.publics
  /-- Pinned BN254 `G2` pairing anchors `(g₂, τ·g₂)` checked in `stages/terminal.rs`. -/
  anchors : bp.G2 × bp.G2
  /-- Canonical 128-byte encoding of `anchors`, matching `configuration.anchors`. -/
  anchorsBytes : List UInt8
  anchorsBytes_len : anchorsBytes.length = 128
  /-- Canonical `affine-u80-v1` BN254 `G1` decoder for the 18 output wires. -/
  affineCodec : Bn254AffineCodec bp

/-- SHA-256-pinned verifying key for an `ix-aiur-scs-v1` native PLONK circuit
(`plonk::native::prepare_to_dir` / `PreparedManifest` and `stages/terminal.rs`). -/
structure AiurScsVerifyingKey (bp : BilinearPairing) (sha256 : List UInt8 → List UInt8) where
  expectedSpec : AiurScsOuterSpec bp
  scsBytes : List UInt8
  pairingBytes : List UInt8
  scsSha256Pin : List UInt8
  pairingSha256Pin : List UInt8
  scs_pin_ok : sha256 scsBytes = scsSha256Pin
  pairing_pin_ok : sha256 pairingBytes = pairingSha256Pin

/-- Plain two-pair BN254 `PairingCheck` enforced by `check_bn254_native_outputs`
(`stages/terminal.rs` / `ark_bn254::Bn254::multi_pairing`):
the 18 output wires decode via `decodeBn254AffinePairWords` into `(d0, d1) ∈ bp.G1 × bp.G1`
satisfying `e(d0, anchors.1) · e(d1, anchors.2) = 1`. -/
def AiurScsPairingCheck {bp : BilinearPairing} (spec : AiurScsOuterSpec bp)
    (w : Nat → BN254Fr) : Prop :=
  ∃ d0 d1 : bp.G1,
    decodeBn254AffinePairWords spec.affineCodec (spec.outputWires.map w) = some (d0, d1) ∧
    bn254DeferredVal bp spec.anchors (d0, d1) = 1

/-- Accepted `ix-aiur-scs-v1` native Rust PLONK verification witness on public statement limbs
`(stmtLow, stmtHigh)`: carries the SHA-256-checked SCS and pairing bytes, wire assignment `w`,
and BSB22 commitment oracle `H`. -/
structure AiurScsOuterAccepted {bp : BilinearPairing} {sha256 : List UInt8 → List UInt8}
    (vk : AiurScsVerifyingKey bp sha256) (stmtLow stmtHigh : Nat) where
  stmtLow_lt : stmtLow < 2 ^ 128
  stmtHigh_lt : stmtHigh < 2 ^ 128
  provenScsBytes : List UInt8
  provenPairingBytes : List UInt8
  provenScs_pin : sha256 provenScsBytes = vk.scsSha256Pin
  provenPairing_pin : sha256 provenPairingBytes = vk.pairingSha256Pin
  wireAssignment : Nat → BN254Fr
  commitOracle : List BN254Fr → BN254Fr
  scsSat : provenScsBytes = vk.scsBytes → provenPairingBytes = vk.pairingBytes →
    vk.expectedSpec.scs.Satisfied wireAssignment
      [(stmtLow : BN254Fr), (stmtHigh : BN254Fr)] commitOracle
  pairingHolds : provenScsBytes = vk.scsBytes → provenPairingBytes = vk.pairingBytes →
    AiurScsPairingCheck vk.expectedSpec wireAssignment

/-- **Outer `ix-aiur-scs-v1` Soundness (`aiur_scs_outer_sound`):**
An accepted outer native PLONK witness against `vk` on `(stmtLow, stmtHigh)` either exhibits
a concrete SHA-256 collision on the SCS or pairing configuration bytes, OR establishes:
1. Satisfaction of `vk.expectedSpec.scs` on `[(stmtLow : BN254Fr), (stmtHigh : BN254Fr)]`;
2. Exact public-wire binding `w 0 = (stmtLow : BN254Fr)` and `w 1 = (stmtHigh : BN254Fr)`; and
3. The two-pair BN254 `PairingCheck` (`check_bn254_native_outputs` in `stages/terminal.rs`) on the
   decoded 18-word `affine-u80-v1` outputs. -/
theorem aiur_scs_outer_sound {bp : BilinearPairing} {sha256 : List UInt8 → List UInt8}
    {vk : AiurScsVerifyingKey bp sha256} {stmtLow stmtHigh : Nat}
    (acc : AiurScsOuterAccepted vk stmtLow stmtHigh) :
    Sha256Collision sha256 acc.provenScsBytes vk.scsBytes ∨
    Sha256Collision sha256 acc.provenPairingBytes vk.pairingBytes ∨
    (vk.expectedSpec.scs.Satisfied acc.wireAssignment
        [(stmtLow : BN254Fr), (stmtHigh : BN254Fr)] acc.commitOracle ∧
     acc.wireAssignment 0 = (stmtLow : BN254Fr) ∧
     acc.wireAssignment 1 = (stmtHigh : BN254Fr) ∧
     AiurScsPairingCheck vk.expectedSpec acc.wireAssignment) := by
  by_cases hScs : acc.provenScsBytes = vk.scsBytes
  · by_cases hPair : acc.provenPairingBytes = vk.pairingBytes
    · right; right
      have hSat := acc.scsSat hScs hPair
      have hPub := hSat.1
      have h0 : acc.wireAssignment 0 = (stmtLow : BN254Fr) :=
        hPub 0 (by simp) (Nat.lt_of_lt_of_le (by decide : 0 < 2) vk.expectedSpec.publics_ge_two)
      have h1 : acc.wireAssignment 1 = (stmtHigh : BN254Fr) :=
        hPub 1 (by simp) (Nat.lt_of_lt_of_le (by decide : 1 < 2) vk.expectedSpec.publics_ge_two)
      exact ⟨hSat, h0, h1, acc.pairingHolds hScs hPair⟩
    · right; left
      exact ⟨hPair, acc.provenPairing_pin.trans vk.pairing_pin_ok.symm⟩
  · left
    exact ⟨hScs, acc.provenScs_pin.trans vk.scs_pin_ok.symm⟩

/-- **Constructive Negative Control (Perturbed Public Limb Rejected by `ix-aiur-scs-v1`):**
Perturbing `stmtLow` by `+ 1` on a wire assignment satisfying `spec.scs` for `(stmtLow, stmtHigh)`
necessarily violates `spec.scs.Satisfied`. -/
theorem aiurScs_rejects_wrong_public_limb {bp : BilinearPairing}
    (spec : AiurScsOuterSpec bp) (w : Nat → BN254Fr) (H : List BN254Fr → BN254Fr)
    (stmtLow stmtHigh : Nat)
    (hSat : spec.scs.Satisfied w [(stmtLow : BN254Fr), (stmtHigh : BN254Fr)] H) :
    ¬ spec.scs.Satisfied w [(stmtLow : BN254Fr) + 1, (stmtHigh : BN254Fr)] H := by
  intro hBad
  have h0 : w 0 = (stmtLow : BN254Fr) :=
    hSat.1 0 (by simp) (Nat.lt_of_lt_of_le (by decide : 0 < 2) spec.publics_ge_two)
  have h0' : w 0 = (stmtLow : BN254Fr) + 1 :=
    hBad.1 0 (by simp) (Nat.lt_of_lt_of_le (by decide : 0 < 2) spec.publics_ge_two)
  have heq : (stmtLow : BN254Fr) = (stmtLow : BN254Fr) + 1 := h0.symm.trans h0'
  have := congrArg (fun x => x - (stmtLow : BN254Fr)) heq
  simp at this

/-- **Constructive Negative Control (Malformed `affine-u80-v1` Output Rejected):**
If the first output point's infinity wire is neither `0` nor `1`, `AiurScsPairingCheck`
is provably false. -/
theorem aiurScs_rejects_noncanonical_output {bp : BilinearPairing}
    (spec : AiurScsOuterSpec bp) (w : Nat → BN254Fr)
    (hBadInf : (w (spec.outputWires.getD 8 0)).val ≠ 0 ∧ (w (spec.outputWires.getD 8 0)).val ≠ 1) :
    ¬ AiurScsPairingCheck spec w := by
  rintro ⟨d0, d1, hDec, _⟩
  unfold decodeBn254AffinePairWords at hDec
  have hlen : (spec.outputWires.map w).length = 18 := by
    rw [List.length_map, spec.outputWires_len]; rfl
  simp only [hlen, ↓reduceIte] at hDec
  have htakeLen : ((spec.outputWires.map w).take 9).length = 9 := by
    rw [List.length_take, hlen]; decide
  cases ht : (spec.outputWires.map w).take 9 with
  | nil => simp [ht] at htakeLen
  | cons a0 r1 =>
    cases r1 with | nil => simp [ht] at htakeLen | cons a1 r2 =>
    cases r2 with | nil => simp [ht] at htakeLen | cons a2 r3 =>
    cases r3 with | nil => simp [ht] at htakeLen | cons a3 r4 =>
    cases r4 with | nil => simp [ht] at htakeLen | cons a4 r5 =>
    cases r5 with | nil => simp [ht] at htakeLen | cons a5 r6 =>
    cases r6 with | nil => simp [ht] at htakeLen | cons a6 r7 =>
    cases r7 with | nil => simp [ht] at htakeLen | cons a7 r8 =>
    cases r8 with | nil => simp [ht] at htakeLen | cons a8 r9 =>
    cases r9 with
    | cons _ _ => simp [ht] at htakeLen
    | nil =>
      have ha8 : a8 = w (spec.outputWires.getD 8 0) := by
        have hidx := congrArg (fun l => l[8]?) ht
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at hidx
        rw [List.getElem?_take_of_lt (by decide), List.getElem?_map] at hidx
        have hlt8 : 8 < spec.outputWires.length := by rw [spec.outputWires_len]; decide
        rw [List.getElem?_eq_getElem hlt8, Option.map_some, Option.some.injEq] at hidx
        rw [← hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt8, Option.getD_some]
      rw [ht] at hDec
      have hnone := (decodeBn254AffineU80PointWords_rejects_bad_flag a0 a1 a2 a3 a4 a5 a6 a7 a8).1
        (ha8.symm ▸ hBadInf.1) (ha8.symm ▸ hBadInf.2)
      rw [hnone] at hDec
      simp at hDec

end Ix.Cert.AiurCompression
