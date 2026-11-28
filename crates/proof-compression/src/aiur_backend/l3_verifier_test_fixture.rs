//! Test-only pure-Rust native PLONK fixture helper (`Bn254` and `Bls12381`,
//! domain 8, 1 BSB22 commitment, 2 public inputs).
//!
//! Used exclusively by `l3_verifier` unit tests to exercise real pure-Rust
//! native PLONK verification in milliseconds — including positive controls,
//! production ceremony anchor checks, and negative controls for foreign STARK
//! verifying keys under the exact same terminal PLONK verifying key.

use super::plonk::{
  native::{
    PlonkAccelerator, ProvingKey, ScsBuilder, ScsFile, VerifyingKey, WireHint,
    domain_size_for_scs, prove_with_seed,
    scs_file::{PackedGate, SEL_L, SEL_M, SEL_O, SEL_R},
    setup,
  },
  scs::Table,
};
use crate::kzg::{Srs, curve::KzgCurve};

pub(super) const CLAIM_BYTES: &[u8] = b"honest-l3-bn254-fixture-claim";
pub(super) const ROOT_VK_HEX: &str =
  "d3813ae554af0aa6a24c5c72c796e17403756aa1f9cabbb08519ed4d767c9f13";
pub(super) const WRAP_KEY_HEX: &str =
  "1bc0cd05e3d1ad8d0102030405060708090a0b0c0d0e0f101112131415161718";
pub(super) const ROGUE_WRAP_KEY_HEX: &str =
  "00000000000000000000000000000000000000000000000000000000deadbeef";
pub(super) const ROGUE_ROOT_KEY_HEX: &str =
  "00000000000000000000000000000000000000000000000000000000bad0c0de";

pub(super) struct NativeL3Fixture<C: KzgCurve> {
  pub(super) scs: ScsFile<C>,
  pub(super) pk: ProvingKey<C>,
  pub(super) vk: VerifyingKey<C>,
  pub(super) vk_bytes: Vec<u8>,
  pub(super) vk_sha256: [u8; 32],
  pub(super) anchors: Vec<u8>,
}

impl<C: KzgCurve> NativeL3Fixture<C> {
  /// Build a minimal domain-8 `ix-aiur-scs-v1` terminal circuit with 2 public
  /// inputs (`pub0`, `pub1`), 1 private witness wire (`sum = pub0 + pub1`),
  /// 1 BSB22 commitment, and a post-commit challenge gate, then run pure-Rust
  /// native PLONK setup under `srs`.
  pub(super) fn new(srs: &Srs<C>) -> Self {
    const C_POS1: u32 = 0;
    const C_NEG1: u32 = 1;
    let coeffs = vec![C::FR_ONE, C::FR_NEG_ONE];

    // Wires:
    //   0: pub0 (input)
    //   1: pub1 (input)
    //   2: sum = pub0 + pub1 (input)
    //   3: gamma (challenge)
    //   4: prod = gamma * sum (solve gate 1)
    let hints = vec![
      WireHint::Input,
      WireHint::Input,
      WireHint::Input,
      WireHint::Challenge,
      WireHint::Solve { gate: 1 },
    ];
    let gates = vec![
      // Gate 0 (pre-commit check): 1*pub0 + 1*pub1 + (-1)*sum = 0.
      PackedGate {
        a: 0,
        b: 1,
        c: 2,
        sel: SEL_L | SEL_R | SEL_O,
        alpha_id: C_POS1,
        beta_id: C_POS1,
        omega_id: C_NEG1,
        qc: 0,
      },
      // Gate 1 (post-commit solve): 1*gamma*sum + (-1)*prod = 0.
      PackedGate {
        a: 3,
        b: 2,
        c: 4,
        sel: SEL_M | SEL_O,
        alpha_id: C_POS1,
        beta_id: C_POS1,
        omega_id: C_NEG1,
        qc: 0,
      },
    ];
    let builder = ScsBuilder::<C> {
      publics: 2,
      wires: hints.len(),
      pre: 1,
      gamma: 3,
      beta: 4,
      outputs: vec![],
      coeffs,
      gates,
      commits: vec![2],
      hints,
      tables: vec![
        Table { name: "root".into(), cell_base: 0, rows: 1, width: 2 },
        Table { name: "witness".into(), cell_base: 2, rows: 1, width: 1 },
      ],
    };
    let scs =
      ScsFile::<C>::parse(&builder.encode()).expect("valid fixture SCS");
    assert_eq!(domain_size_for_scs(&scs).unwrap(), 8);
    let accel = PlonkAccelerator::<C>::cpu();
    let (pk, vk) = setup(&scs, srs, &accel).expect("native PLONK setup");
    let vk_bytes = vk.to_bytes().expect("serialize VK");
    let vk_sha256 = vk.sha256();
    let anchors = C::encode_plonk_anchors(&vk.g1, &vk.g2, &vk.tau_g2);
    Self { scs, pk, vk, vk_bytes, vk_sha256, anchors }
  }

  /// Produce a real native PLONK proof (`IXNPPR01`) for public inputs `[p0, p1]`.
  pub(super) fn prove(
    &self,
    public_inputs: [C::Fr; 2],
    seed: [u8; 32],
  ) -> Vec<u8> {
    let sum = public_inputs[0] + public_inputs[1];
    let input_wires = [public_inputs[0], public_inputs[1], sum];
    let accel = PlonkAccelerator::<C>::cpu();
    let (proof, _) = prove_with_seed(
      &self.scs,
      &self.pk,
      &input_wires,
      &public_inputs,
      &accel,
      seed,
    )
    .expect("native PLONK prove");
    proof.to_native_bytes().expect("serialize native proof")
  }
}
