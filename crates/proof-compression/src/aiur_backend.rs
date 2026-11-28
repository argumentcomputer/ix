//! Native pairing-curve scalar arithmetic (`Bn254` and `Bls12381`) for the
//! Aiur interpreter.
//!
//! Execution uses the same scalar representation as the KZG backend. Artifact
//! constants cross a canonical four-limb boundary; host indices must additionally
//! fit in a machine word. Trace population and proving are separate adapters.

use crate::kzg::{CurveScalar, KzgCurve, Scalar};
use aiur::{FieldWord, field::FieldBackend};
use ark_ff::{Field, PrimeField};

pub mod bls12_381;
pub mod chain;
pub mod compress_bn;
pub mod compress_gl;
pub mod fq;
pub mod fq_relation;
pub mod g1;
pub mod groth16;
pub mod kzg;
pub mod kzg_advice;
pub mod kzg_packed_advice;
pub mod l3_verifier;
#[cfg(test)]
mod l3_verifier_test_fixture;
pub mod pairing;
pub mod plonk;
pub mod stages;
pub mod template;
pub mod wide;

pub use bls12_381::Bls12381;

/// Pairing-curve [`FieldBackend`] (`Bn254` or `Bls12381`) linked back to its
/// [`AiurCurve`] so functions taking `TracePlan<'_, F>` or `Execution<F>` infer
/// the curve automatically without turbofish.
pub trait AiurField:
  FieldBackend<Element = CurveScalar<Self::Curve>, Word = FieldWord>
  + Copy
  + Default
  + std::fmt::Debug
  + Send
  + Sync
  + 'static
{
  type Curve: AiurCurve<Field = Self>;
}

/// Curve metadata binding a [`KzgCurve`] (`Bn254` or `Bls12381`) to its native
/// Aiur [`AiurField`], emulated `Fq` limb geometry (`4 × 80`-bit for BN254,
/// `5 × 80`-bit for BLS12-381), and serialized wire dimensions.
pub trait AiurCurve: KzgCurve {
  type Field: AiurField<Curve = Self>;

  const FIELD: Self::Field;
  const HINT_PREFIX: &'static str;
  const FQ_U80_LIMBS: usize;
  const G1_WORDS: usize;
  const ACCUMULATOR_CHUNKS: usize;
  const TERMINAL_OUTPUT_WORDS: usize;
  const G2_PAIR_COMPRESSED_BYTES: usize;
  const MAX_LOG_DOMAIN: u32;
}

fn curve_from_word<C: KzgCurve>(value: FieldWord) -> CurveScalar<C> {
  let mut bytes = [0u8; 32];
  for (chunk, limb) in
    bytes.as_chunks_mut::<8>().0.iter_mut().zip(value.limbs_le())
  {
    *chunk = limb.to_le_bytes();
  }
  CurveScalar::new(C::Fr::from_le_bytes_mod_order(&bytes))
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Bn254;

impl FieldBackend for Bn254 {
  type Element = Scalar;
  type Word = FieldWord;
  const ALL_ELEMENTS_VALID: bool = true;

  fn modulus(self) -> FieldWord {
    FieldWord::from_limbs_le(ark_bn254::Fr::MODULUS.0)
  }

  fn from_u64(self, value: u64) -> Scalar {
    Scalar::new(ark_bn254::Fr::from(value))
  }

  fn from_word(self, value: FieldWord) -> Scalar {
    curve_from_word::<crate::kzg::Bn254>(value)
  }

  fn to_word(self, value: Scalar) -> FieldWord {
    FieldWord::from_limbs_le(value.canonical_limbs_le())
  }

  fn add(self, a: Scalar, b: Scalar) -> Scalar {
    a + b
  }

  fn sub(self, a: Scalar, b: Scalar) -> Scalar {
    a - b
  }

  fn neg(self, a: Scalar) -> Scalar {
    -a
  }

  fn mul(self, a: Scalar, b: Scalar) -> Scalar {
    a * b
  }

  fn inverse(self, a: Scalar) -> Option<Scalar> {
    a.0.inverse().map(Scalar::new)
  }
}

impl AiurField for Bn254 {
  type Curve = crate::kzg::Bn254;
}

impl AiurField for Bls12381 {
  type Curve = crate::kzg::Bls12381;
}

impl AiurCurve for crate::kzg::Bn254 {
  type Field = Bn254;
  const FIELD: Self::Field = Bn254;
  const HINT_PREFIX: &'static str = "bn254";
  const FQ_U80_LIMBS: usize = 4;
  const G1_WORDS: usize = 9;
  const ACCUMULATOR_CHUNKS: usize = 4;
  const TERMINAL_OUTPUT_WORDS: usize = 18;
  const G2_PAIR_COMPRESSED_BYTES: usize = 128;
  const MAX_LOG_DOMAIN: u32 = 28;
}

impl AiurCurve for crate::kzg::Bls12381 {
  type Field = Bls12381;
  const FIELD: Self::Field = Bls12381;
  const HINT_PREFIX: &'static str = "bls12_381";
  const FQ_U80_LIMBS: usize = 5;
  const G1_WORDS: usize = 11;
  const ACCUMULATOR_CHUNKS: usize = 6;
  const TERMINAL_OUTPUT_WORDS: usize = 22;
  const G2_PAIR_COMPRESSED_BYTES: usize = 192;
  const MAX_LOG_DOMAIN: u32 = 32;
}

#[cfg(test)]
mod tests {
  use super::{
    AiurCurve, Bls12381, Bn254, compress_bn, fq, g1, kzg_advice, pairing,
    stages,
  };
  use crate::kzg::{
    Bls12381 as Bls12381Curve, Bn254 as Bn254Curve, Curve, CurveScalar,
    KzgCurve, Srs,
  };
  use aiur::field::FieldBackend;
  use ark_ec::{
    AffineRepr, CurveGroup,
    pairing::{MillerLoopOutput, Pairing},
  };
  use ark_ff::{Field, One};

  #[test]
  fn bls12_381_field_fq_g1_roundtrip_and_subgroup_rejection() {
    let a = Bls12381.from_u64(19);
    let b = Bls12381.from_u64(7);
    let inv_b = Bls12381.inverse(b).expect("invertible");
    assert_eq!(Bls12381.mul(b, inv_b), Bls12381.from_u64(1));
    assert_eq!(Bls12381.from_word(Bls12381.to_word(a)), a);

    // 5 x 80-bit canonical Fq encoding/decoding roundtrip.
    let fq_val = -ark_bls12_381::Fq::from(17u64);
    let limbs = fq::encode_for::<Bls12381Curve>(fq_val);
    assert_eq!(limbs.len(), Bls12381Curve::FQ_U80_LIMBS);
    assert_eq!(fq::decode_for::<Bls12381Curve>(&limbs).unwrap(), fq_val);

    // Noncanonical Fq (>= modulus) must be rejected.
    let mut bad_limbs =
      fq::encode_for::<Bls12381Curve>(ark_bls12_381::Fq::from(0u64));
    bad_limbs[4] = Bls12381.from_u64(1u64 << 62);
    assert!(fq::decode_for::<Bls12381Curve>(&bad_limbs).is_err());

    // G1 encoding/decoding roundtrip (generator + infinity + chunks).
    let g1_gen = ark_bls12_381::G1Affine::generator();
    let p = (g1_gen * ark_bls12_381::Fr::from(13u64)).into_affine();
    let encoded = g1::encode_for::<Bls12381Curve>(p);
    assert_eq!(encoded.len(), Bls12381Curve::G1_WORDS);
    assert_eq!(g1::decode_for::<Bls12381Curve>(&encoded).unwrap(), p);

    let inf = ark_bls12_381::G1Affine::zero();
    let inf_enc = g1::encode_for::<Bls12381Curve>(inf);
    assert!(g1::decode_for::<Bls12381Curve>(&inf_enc).unwrap().is_zero());

    let chunks = g1::encode_chunks_for::<Bls12381Curve>([p, inf]).unwrap();
    assert_eq!(chunks.len(), Bls12381Curve::ACCUMULATOR_CHUNKS);
    assert_eq!(
      g1::decode_chunks_for::<Bls12381Curve>(&chunks).unwrap(),
      [p, inf]
    );

    // Non-subgroup on-curve BLS12-381 G1 point MUST be rejected!
    let mut non_subgroup = None;
    for x_u64 in 1u64..1000 {
      let x = ark_bls12_381::Fq::from(x_u64);
      let rhs = x * x * x + ark_bls12_381::Fq::from(4u64);
      if let Some(y) = rhs.sqrt() {
        let cand = ark_bls12_381::G1Affine::new_unchecked(x, y);
        if cand.is_on_curve()
          && !cand.is_in_correct_subgroup_assuming_on_curve()
        {
          non_subgroup = Some(cand);
          break;
        }
      }
    }
    let bad_pt = non_subgroup.expect("non-subgroup BLS12-381 G1 point");
    let bad_words = g1::encode_for::<Bls12381Curve>(bad_pt);
    assert!(
      g1::decode_for::<Bls12381Curve>(&bad_words).is_err(),
      "non-subgroup BLS12-381 G1 point must be rejected"
    );

    // Hint registration for BLS12-381 succeeds cleanly without channel collision
    // (g1::register_for registers fq_relation channels internally).
    let mut hints = aiur::hints::HintChannels::default();
    fq::register_for::<Bls12381Curve>(&mut hints).unwrap();
    g1::register_for::<Bls12381Curve>(&mut hints).unwrap();
    pairing::register_for::<Bls12381Curve>(&mut hints).unwrap();
  }

  #[test]
  fn bls12_381_fixed_lines_match_multi_pairing() {
    let g1_gen = ark_bls12_381::G1Affine::generator();
    let g2_gen = ark_bls12_381::G2Affine::generator();
    let tau = ark_bls12_381::Fr::from(7u64);
    let anchors = [g2_gen, (g2_gen * tau).into_affine()];
    let rows = pairing::fixed_lines_bls12_381(anchors).unwrap();

    // Valid KZG-style pairing: e(7*G1, G2) * e(-G1, 7*G2) == 1.
    let p0 = (g1_gen * tau).into_affine();
    let p1 = -g1_gen;
    let miller =
      pairing::evaluate_fixed_lines_bls12_381(&rows, [p0, p1]).unwrap();
    let final_gt =
      ark_bls12_381::Bls12_381::final_exponentiation(MillerLoopOutput(miller))
        .expect("final exponentiation");
    let expected = ark_bls12_381::Bls12_381::multi_pairing([p0, p1], anchors);
    assert_eq!(final_gt, expected);
    assert!(final_gt.0.is_one());

    // Non-trivial pairing check: e(5*G1, G2) * e(3*G1, 7*G2) == e(26*G1, G2).
    let q0 = (g1_gen * ark_bls12_381::Fr::from(5u64)).into_affine();
    let q1 = (g1_gen * ark_bls12_381::Fr::from(3u64)).into_affine();
    let miller2 =
      pairing::evaluate_fixed_lines_bls12_381(&rows, [q0, q1]).unwrap();
    let gt2 =
      ark_bls12_381::Bls12_381::final_exponentiation(MillerLoopOutput(miller2))
        .expect("final exponentiation");
    let expected2 = ark_bls12_381::Bls12_381::multi_pairing([q0, q1], anchors);
    assert_eq!(gt2, expected2);
    assert!(!gt2.0.is_one());
  }

  #[test]
  fn bls12_381_accumulator_and_anchors_and_stages_manifest_curve() {
    let srs = Srs::<Bls12381Curve>::unsafe_dev_setup(8, b"bls12-381-aiur-test");
    let verifier = crate::kzg::VerifierParams::from_srs(&srs);
    let anchors = Bls12381Curve::encode_plonk_anchors(
      &verifier.g1[0],
      &verifier.g2,
      &verifier.tau_g2,
    );
    assert_eq!(anchors.len(), 240);
    let bn_srs = Srs::<Bn254Curve>::unsafe_dev_setup(8, b"bn254-aiur-test");
    let bn_v = crate::kzg::VerifierParams::from_srs(&bn_srs);
    assert_eq!(
      Bn254Curve::encode_plonk_anchors(&bn_v.g1[0], &bn_v.g2, &bn_v.tau_g2)
        .len(),
      320
    );

    let g1_gen = ark_bls12_381::G1Affine::generator();
    let p0 = (g1_gen * ark_bls12_381::Fr::from(11u64)).into_affine();
    let p1 = (g1_gen * ark_bls12_381::Fr::from(13u64)).into_affine();
    let acc_words =
      kzg_advice::accumulator_words_for::<Bls12381Curve>(&[p0, p1]).unwrap();
    assert_eq!(acc_words.len(), Bls12381Curve::ACCUMULATOR_CHUNKS);
    let zero_hash = [0u8; 32];
    let _fold = kzg_advice::fold_challenge_for::<Bls12381Curve>(
      &zero_hash,
      &zero_hash,
      1,
      &zero_hash,
      &zero_hash,
      &[p0, p1],
      &[p1, p0],
    )
    .unwrap();

    let tau_g1 = srs.g1[1];
    let ok_acc = compress_bn::Accumulator::<Bls12381Curve>::from_points(&[
      tau_g1, -g1_gen,
    ])
    .unwrap();
    assert!(ok_acc.check_pairing(&verifier).is_ok());
    let bad_acc =
      compress_bn::Accumulator::<Bls12381Curve>::from_points(&[g1_gen, g1_gen])
        .unwrap();
    assert!(bad_acc.check_pairing(&verifier).is_err());

    // stages::Manifest curve parsing (omitted -> Bn254, bls12-381 -> Bls12381, unknown -> Err).
    let base = std::path::Path::new(".");
    for (json, expected) in [
      (r#"{"format":"ix-aiur-stages-v1","stages":[]}"#, Some(Curve::Bn254)),
      (
        r#"{"format":"ix-aiur-stages-v1","curve":"bn254","stages":[]}"#,
        Some(Curve::Bn254),
      ),
      (
        r#"{"format":"ix-aiur-stages-v1","curve":"bls12-381","stages":[]}"#,
        Some(Curve::Bls12381),
      ),
      (
        r#"{"format":"ix-aiur-stages-v1","curve":"secp256k1","stages":[]}"#,
        None,
      ),
    ] {
      let pin = blake3::hash(json.as_bytes()).to_hex().to_string();
      let res = stages::Manifest::new(json.as_bytes(), &pin, base);
      match expected {
        Some(curve) => assert_eq!(res.unwrap().curve().unwrap(), curve),
        None => assert!(res.is_err()),
      }
    }

    let _ = Bn254.from_u64(1);
    let _: CurveScalar<Bls12381Curve> = Bls12381.from_u64(1);
  }
}
