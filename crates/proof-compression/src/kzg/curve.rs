//! Curve types, compile-time curve descriptors, and canonical encoding widths
//! for the supported KZG backends (BN254 and BLS12-381).
//!
//! Encodings are arkworks canonical encodings; these widths do not describe
//! in-memory or EVM representations.

use ark_ec::{
  pairing::Pairing,
  short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{
  AdditiveGroup, BigInt, BigInteger, FftField, Field, MontConfig, PrimeField,
};
use ark_serialize::{
  CanonicalDeserialize, CanonicalSerialize, Read, SerializationError,
};

pub use ark_bn254::{
  Bn254 as PairingCurve, Fq, Fr, G1Affine, G1Projective, G2Affine, G2Projective,
};

/// BLS12-381 arkworks curve types.
pub mod bls12_381 {
  pub use ark_bls12_381::{
    Bls12_381 as PairingCurve, Fq, Fr, G1Affine, G1Projective, G2Affine,
    G2Projective,
  };
}

pub const NAME: &str = "bn254";

pub const G1_COMPRESSED_BYTES: usize = 32;

pub const G1_UNCOMPRESSED_BYTES: usize = G1_COMPRESSED_BYTES * 2;
pub const G2_COMPRESSED_BYTES: usize = G1_COMPRESSED_BYTES * 2;
pub const G2_UNCOMPRESSED_BYTES: usize = G2_COMPRESSED_BYTES * 2;

/// Runtime selector for the pairing curve used in proof compression.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Curve {
  /// BN254 (~100b classical / 0b PQ, pre-Pectra EVM BN254 precompiles).
  #[default]
  Bn254,
  /// BLS12-381 (~126–128b classical / 0b PQ, Pectra EIP-2537 precompiles).
  Bls12381,
}

impl Curve {
  pub const ALL: &'static [Self] = &[Self::Bn254, Self::Bls12381];

  pub const fn as_str(self) -> &'static str {
    match self {
      Self::Bn254 => Bn254::NAME,
      Self::Bls12381 => Bls12381::NAME,
    }
  }

  pub fn parse(name: &str) -> Result<Self, String> {
    match name {
      "bn254" => Ok(Self::Bn254),
      "bls12-381" | "bls12_381" => Ok(Self::Bls12381),
      other => Err(format!(
        "unknown compression curve {other:?}; expected bn254 or bls12-381"
      )),
    }
  }

  /// Honest security, trust-assumption, and zero-knowledge summary for CLI and
  /// diagnostics output.
  pub const fn security_label(self) -> &'static str {
    match self {
      Self::Bls12381 => {
        "~126–128b classical / 0b PQ (EIP-2537, AGM/q-SDH + Filecoin challenge_19 SRS; gnark ZK vs non-ZK final-kzg)"
      },
      Self::Bn254 => {
        "~100b classical / 0b PQ (pre-Pectra EVM, AGM/q-SDH + Ignition SRS; gnark ZK vs non-ZK final-kzg)"
      },
    }
  }
}

impl core::fmt::Display for Curve {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.write_str(self.as_str())
  }
}

mod sealed {
  pub trait Sealed {}
  impl Sealed for super::Bn254 {}
  impl Sealed for super::Bls12381 {}
}

#[cfg(feature = "cuda")]
#[doc(hidden)]
pub trait CudaCurveSupport: super::cuda::CudaCurve {}
#[cfg(feature = "cuda")]
impl<T: super::cuda::CudaCurve> CudaCurveSupport for T {}

#[cfg(not(feature = "cuda"))]
#[doc(hidden)]
pub trait CudaCurveSupport {}
#[cfg(not(feature = "cuda"))]
impl<T> CudaCurveSupport for T {}

/// Compile-time curve marker for BN254.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bn254;

/// Compile-time curve marker for BLS12-381.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bls12381;

pub type G1AffineOf<C> = Affine<<C as KzgCurve>::G1Config>;
pub type G1ProjectiveOf<C> = Projective<<C as KzgCurve>::G1Config>;
pub type G2AffineOf<C> = Affine<<C as KzgCurve>::G2Config>;
pub type G2ProjectiveOf<C> = Projective<<C as KzgCurve>::G2Config>;

/// Sealed curve descriptor unifying BN254 and BLS12-381 across KZG, recursive
/// verification, and compression pipelines.
pub trait KzgCurve:
  sealed::Sealed
  + CudaCurveSupport
  + Clone
  + Copy
  + Debug
  + Default
  + PartialEq
  + Eq
  + PartialOrd
  + Ord
  + core::hash::Hash
  + Send
  + Sync
  + 'static
{
  type FqBigInt: BigInteger + Copy + Send + Sync + 'static;
  type Fq: PrimeField<BigInt = Self::FqBigInt>
    + CanonicalSerialize
    + CanonicalDeserialize
    + Copy
    + Send
    + Sync
    + 'static;
  type Fr: PrimeField<BigInt = BigInt<4>>
    + FftField
    + CanonicalSerialize
    + CanonicalDeserialize
    + Copy
    + Send
    + Sync
    + 'static;
  type G1Config: SWCurveConfig<BaseField = Self::Fq, ScalarField = Self::Fr>
    + Send
    + Sync
    + 'static;
  type G2Config: SWCurveConfig<ScalarField = Self::Fr> + Send + Sync + 'static;
  type PairingCurve: Pairing<
      ScalarField = Self::Fr,
      G1 = G1ProjectiveOf<Self>,
      G1Affine = G1AffineOf<Self>,
      G2 = G2ProjectiveOf<Self>,
      G2Affine = G2AffineOf<Self>,
    >;

  const CURVE: Curve;
  const NAME: &'static str;
  const G1_COMPRESSED_BYTES: usize;
  const G1_UNCOMPRESSED_BYTES: usize = Self::G1_COMPRESSED_BYTES * 2;
  const G2_COMPRESSED_BYTES: usize = Self::G1_COMPRESSED_BYTES * 2;
  const G2_UNCOMPRESSED_BYTES: usize = Self::G2_COMPRESSED_BYTES * 2;

  /// Scalar-field constants for compile-time trait impls.
  const FR_ZERO: Self::Fr;
  const FR_ONE: Self::Fr;
  const FR_TWO: Self::Fr;
  const FR_NEG_ONE: Self::Fr;
  const FR_GENERATOR: Self::Fr;
  const FR_TWO_ADICITY: usize;
  const FR_MONT_ONE: [u64; 4];
  const FR_MONT_R2: [u64; 4];

  /// Recursive native-field / curve / pairing geometry.
  const FQ_BYTES: usize = Self::G1_COMPRESSED_BYTES;
  const FQ_GADGET_LIMBS: usize;
  const POINT_LIMB_BYTES: usize;
  const CURVE_B: u64;
  const HAS_COFACTOR: bool;
  const SUBGROUP_CHECK_SEED: u64;
  const COMPRESSED_BIG_ENDIAN: bool;
  const COMPRESSED_SIGN_MASK: u8;
  const COMPRESSED_FLAG_MASK: u8;

  /// Domain separation and binary framing constants.
  const VERIFIER_PARAMS_VERSION: u64;
  const COMPACT_MAGIC: &'static [u8; 4];
  const CHECKPOINT_MAGIC: &'static [u8; 8];
  const DEV_SRS_CACHE_MAGIC: &'static [u8];
  const BLAKE3_SEED_DOMAIN: &'static [u8];
  const KECCAK256_SEED_DOMAIN: &'static [u8];
  const KECCAK256_TRANSCRIPT_DOMAIN: &'static [u8];
  const PUBLIC_SETUP_DOMAIN: &'static [u8];
  const DEV_TAU_DOMAIN: &'static [u8];
  const VALIDATION_DOMAIN: &'static [u8];
  const KZG_VERIFIER_MAGIC: &'static [u8; 8];
  const RECURSIVE_VERIFIER_MAGIC: &'static [u8; 8];
  const RECURSIVE_FRONTEND_VERSION: &'static [u8];
  const FIRST_VK_LABEL: &'static [u8];
  const FIXED_CACHE_DOMAIN: &'static [u8];
  const OUTER_SEED: &'static [u8];
  const OUTER_VK_VERSION: u32;
  const OUTER_VK_NAMESPACE: &'static str;
  const RECURSIVE_PROOF_TAG: &'static [u8; 8];
  const PLONK_PROOF_TAG: &'static [u8; 8];
  const GROTH16_PROOF_TAG: &'static [u8; 8];
  const PLONK_SRS_MAGIC: &'static [u8; 8];
  const PLONK_SRS_FORMAT: &'static str;
  const PLONK_VK_FORMAT: &'static str;
  const PLONK_ANCHOR_BYTES: usize;
  const GROTH16_PROOF_BYTES_NO_COMMIT: usize;
  const GROTH16_PROOF_BYTES_WITH_COMMIT: usize;

  /// Endomorphism cube root of unity `beta` in `Fq` when `HAS_COFACTOR` is true.
  fn endo_beta() -> Option<Self::Fq>;

  /// Encode a G1 point in EVM precompile format (64B BN254 / 128B EIP-2537 BLS12-381).
  fn encode_g1_evm(point: G1AffineOf<Self>) -> Vec<u8>;

  /// Encode a G2 point for gnark `vk.json` and PLONK SRS export
  /// (128B uncompressed BE for BN254 / 96B compressed for BLS12-381).
  fn encode_g2_vk(point: &G2AffineOf<Self>) -> Vec<u8>;

  /// Encode `(g1, g2, tau_g2)` anchors matching gnark's `anchorBytes`
  /// (320B for BN254 / 240B for BLS12-381).
  fn encode_plonk_anchors(
    g1: &G1AffineOf<Self>,
    g2: &G2AffineOf<Self>,
    tau_g2: &G2AffineOf<Self>,
  ) -> Vec<u8>;

  /// Direct access to arkworks' internal Montgomery representation of `Fr`.
  fn fr_mont_limbs(v: Self::Fr) -> [u64; 4];
  fn fr_mont_limbs_ref(v: &Self::Fr) -> &[u64; 4];
  fn fr_from_mont_limbs_unchecked(limbs: [u64; 4]) -> Self::Fr;

  /// Direct access to arkworks' internal Montgomery representation of `Fq`
  /// for CUDA ABI verification and projective point transport.
  #[cfg(feature = "cuda")]
  fn fq_to_mont_limbs(v: Self::Fq) -> Self::FqLimbs;
  #[cfg(feature = "cuda")]
  fn fq_from_mont_limbs_unchecked(limbs: Self::FqLimbs) -> Self::Fq;
  #[cfg(feature = "cuda")]
  fn fq_abi_triple() -> [Self::FqLimbs; 3];

  /// CPU multi-scalar multiplication in G1.
  fn cpu_msm(
    bases: &[G1AffineOf<Self>],
    scalars: &[Self::Fr],
  ) -> G1ProjectiveOf<Self>;
}

use core::fmt::Debug;

impl KzgCurve for Bn254 {
  type FqBigInt = BigInt<4>;
  type Fq = Fq;
  type Fr = Fr;
  type G1Config = ark_bn254::g1::Config;
  type G2Config = ark_bn254::g2::Config;
  type PairingCurve = PairingCurve;

  const CURVE: Curve = Curve::Bn254;
  const NAME: &'static str = "bn254";
  const G1_COMPRESSED_BYTES: usize = 32;

  const FR_ZERO: Self::Fr = <Fr as AdditiveGroup>::ZERO;
  const FR_ONE: Self::Fr = <Fr as Field>::ONE;
  const FR_TWO: Self::Fr = ark_ff::MontFp!("2");
  const FR_NEG_ONE: Self::Fr = ark_ff::MontFp!("-1");
  const FR_GENERATOR: Self::Fr = <Fr as FftField>::GENERATOR;
  const FR_TWO_ADICITY: usize = <Fr as FftField>::TWO_ADICITY as usize;
  const FR_MONT_ONE: [u64; 4] = <Fr as Field>::ONE.0.0;
  const FR_MONT_R2: [u64; 4] = <ark_bn254::FrConfig as MontConfig<4>>::R2.0;

  const FQ_GADGET_LIMBS: usize = 4;
  const POINT_LIMB_BYTES: usize = 16;
  const CURVE_B: u64 = 3;
  const HAS_COFACTOR: bool = false;
  const SUBGROUP_CHECK_SEED: u64 = 0;
  const COMPRESSED_BIG_ENDIAN: bool = false;
  const COMPRESSED_SIGN_MASK: u8 = 0x80;
  const COMPRESSED_FLAG_MASK: u8 = 0x00;

  const VERIFIER_PARAMS_VERSION: u64 = 0x424e0001;
  const COMPACT_MAGIC: &'static [u8; 4] = b"KBN1";
  const CHECKPOINT_MAGIC: &'static [u8; 8] = b"IXBNCP01";
  const DEV_SRS_CACHE_MAGIC: &'static [u8] = b"ix/bn254/dev-srs/v1\0";
  const BLAKE3_SEED_DOMAIN: &'static [u8] = b"multi-stark/kzg/bn254/blake3/v1";
  const KECCAK256_SEED_DOMAIN: &'static [u8] =
    b"multi-stark/kzg/bn254/keccak256/v1";
  const KECCAK256_TRANSCRIPT_DOMAIN: &'static [u8] =
    b"ix/kzg/bn254/keccak256/v1";
  const PUBLIC_SETUP_DOMAIN: &'static [u8] =
    b"multi-stark/kzg/bn254/known-trapdoor-public-degree/v1";
  const DEV_TAU_DOMAIN: &'static [u8] = b"multi-stark/kzg/bn254/dev-srs";
  const VALIDATION_DOMAIN: &'static [u8] =
    b"multi-stark/kzg/bn254/srs-validate/v4";
  const KZG_VERIFIER_MAGIC: &'static [u8; 8] = b"IXBNKV02";
  const RECURSIVE_VERIFIER_MAGIC: &'static [u8; 8] = b"IXBNRV02";
  const RECURSIVE_FRONTEND_VERSION: &'static [u8] =
    b"init-kzg-recursive/bn254/frontend/v1";
  const FIRST_VK_LABEL: &'static [u8] =
    b"init-fri-kzg-bn254/v1/development-srs/quotient2";
  const FIXED_CACHE_DOMAIN: &'static [u8] = b"ix/kzg-fixed-cache/bn254/v1";
  const OUTER_SEED: &'static [u8] = b"init-kzg-recursive-bn254-v1";
  const OUTER_VK_VERSION: u32 = 8;
  const OUTER_VK_NAMESPACE: &'static str = "init-kzg-recursive-bn254-profile";
  const RECURSIVE_PROOF_TAG: &'static [u8; 8] = b"IXBN\0\0\0\x01";
  const PLONK_PROOF_TAG: &'static [u8; 8] = b"IXBN\0\0\0\x02";
  const GROTH16_PROOF_TAG: &'static [u8; 8] = b"IXBN\0\0\0\x03";
  const PLONK_SRS_MAGIC: &'static [u8; 8] = b"IXBPSR01";
  const PLONK_SRS_FORMAT: &'static str = "ix-bn254-plonk-srs-export-v2";
  const PLONK_VK_FORMAT: &'static str = "ix-bn254-plonk-vk-v1";
  const PLONK_ANCHOR_BYTES: usize = 320;
  const GROTH16_PROOF_BYTES_NO_COMMIT: usize = 164;
  const GROTH16_PROOF_BYTES_WITH_COMMIT: usize = 196;

  fn endo_beta() -> Option<Self::Fq> {
    None
  }

  fn encode_g1_evm(point: G1AffineOf<Self>) -> Vec<u8> {
    use ark_ec::AffineRepr;
    if point.is_zero() {
      return vec![0; 64];
    }
    [point.x.into_bigint().to_bytes_be(), point.y.into_bigint().to_bytes_be()]
      .concat()
  }

  fn encode_g2_vk(point: &G2AffineOf<Self>) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(128);
    for value in [point.x.c0, point.x.c1, point.y.c0, point.y.c1] {
      bytes.extend(value.into_bigint().to_bytes_be());
    }
    bytes
  }

  fn encode_plonk_anchors(
    g1: &G1AffineOf<Self>,
    g2: &G2AffineOf<Self>,
    tau_g2: &G2AffineOf<Self>,
  ) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(Self::PLONK_ANCHOR_BYTES);
    bytes.extend(g1.x.into_bigint().to_bytes_be());
    bytes.extend(g1.y.into_bigint().to_bytes_be());
    bytes.extend(Self::encode_g2_vk(g2));
    bytes.extend(Self::encode_g2_vk(tau_g2));
    bytes
  }

  #[inline]
  fn fr_mont_limbs(v: Self::Fr) -> [u64; 4] {
    v.0.0
  }

  #[inline]
  fn fr_mont_limbs_ref(v: &Self::Fr) -> &[u64; 4] {
    &v.0.0
  }

  #[inline]
  fn fr_from_mont_limbs_unchecked(limbs: [u64; 4]) -> Self::Fr {
    Fr::new_unchecked(BigInt(limbs))
  }

  #[cfg(feature = "cuda")]
  #[inline]
  fn fq_to_mont_limbs(v: Self::Fq) -> Self::FqLimbs {
    v.0.0
  }

  #[cfg(feature = "cuda")]
  #[inline]
  fn fq_from_mont_limbs_unchecked(limbs: Self::FqLimbs) -> Self::Fq {
    Fq::new_unchecked(BigInt(limbs))
  }

  #[cfg(feature = "cuda")]
  #[inline]
  fn fq_abi_triple() -> [Self::FqLimbs; 3] {
    [Fq::MODULUS.0, Fq::ONE.0.0, <ark_bn254::FqConfig as MontConfig<4>>::R2.0]
  }

  fn cpu_msm(
    bases: &[G1AffineOf<Self>],
    scalars: &[Self::Fr],
  ) -> G1ProjectiveOf<Self> {
    super::msm_cpu::msm(bases, scalars)
  }
}

impl KzgCurve for Bls12381 {
  type FqBigInt = BigInt<6>;
  type Fq = ark_bls12_381::Fq;
  type Fr = ark_bls12_381::Fr;
  type G1Config = ark_bls12_381::g1::Config;
  type G2Config = ark_bls12_381::g2::Config;
  type PairingCurve = ark_bls12_381::Bls12_381;

  const CURVE: Curve = Curve::Bls12381;
  const NAME: &'static str = "bls12-381";
  const G1_COMPRESSED_BYTES: usize = 48;

  const FR_ZERO: Self::Fr = <ark_bls12_381::Fr as AdditiveGroup>::ZERO;
  const FR_ONE: Self::Fr = <ark_bls12_381::Fr as Field>::ONE;
  const FR_TWO: Self::Fr = ark_ff::MontFp!("2");
  const FR_NEG_ONE: Self::Fr = ark_ff::MontFp!("-1");
  const FR_GENERATOR: Self::Fr = <ark_bls12_381::Fr as FftField>::GENERATOR;
  const FR_TWO_ADICITY: usize =
    <ark_bls12_381::Fr as FftField>::TWO_ADICITY as usize;
  const FR_MONT_ONE: [u64; 4] = <ark_bls12_381::Fr as Field>::ONE.0.0;
  const FR_MONT_R2: [u64; 4] = <ark_bls12_381::FrConfig as MontConfig<4>>::R2.0;

  const FQ_GADGET_LIMBS: usize = 5;
  const POINT_LIMB_BYTES: usize = 24;
  const CURVE_B: u64 = 4;
  const HAS_COFACTOR: bool = true;
  const SUBGROUP_CHECK_SEED: u64 = 0xd201_0000_0001_0000;
  const COMPRESSED_BIG_ENDIAN: bool = true;
  const COMPRESSED_SIGN_MASK: u8 = 0x20;
  const COMPRESSED_FLAG_MASK: u8 = 0x80;

  const VERIFIER_PARAMS_VERSION: u64 = 4;
  const COMPACT_MAGIC: &'static [u8; 4] = b"KQP4";
  const CHECKPOINT_MAGIC: &'static [u8; 8] = b"IXKZGCP4";
  const DEV_SRS_CACHE_MAGIC: &'static [u8] = b"ix/bls12-381/dev-srs/v1\0";
  const BLAKE3_SEED_DOMAIN: &'static [u8] = b"multi-stark/kzg/v4";
  const KECCAK256_SEED_DOMAIN: &'static [u8] = b"multi-stark/kzg/keccak256/v1";
  const KECCAK256_TRANSCRIPT_DOMAIN: &'static [u8] =
    b"multi-stark/kzg/keccak256/v1";
  const PUBLIC_SETUP_DOMAIN: &'static [u8] =
    b"multi-stark/kzg/known-trapdoor-public-degree/v1";
  const DEV_TAU_DOMAIN: &'static [u8] = b"multi-stark/kzg/dev-srs";
  const VALIDATION_DOMAIN: &'static [u8] = b"multi-stark/kzg/srs-validate/v4";
  const KZG_VERIFIER_MAGIC: &'static [u8; 8] = b"IXKZGV02";
  const RECURSIVE_VERIFIER_MAGIC: &'static [u8; 8] = b"IXRECV02";
  const RECURSIVE_FRONTEND_VERSION: &'static [u8] =
    b"init-kzg-recursive/frontend/v1";
  const FIRST_VK_LABEL: &'static [u8] =
    b"init-fri-kzg-ordinary-v1/development-srs/quotient2";
  const FIXED_CACHE_DOMAIN: &'static [u8] = b"ix/kzg-fixed-cache/v5";
  const OUTER_SEED: &'static [u8] = b"init-kzg-recursive-v1";
  const OUTER_VK_VERSION: u32 = 7;
  const OUTER_VK_NAMESPACE: &'static str = "init-kzg-recursive-profile";
  const RECURSIVE_PROOF_TAG: &'static [u8; 8] = b"IXCMP\0\0\x04";
  const PLONK_PROOF_TAG: &'static [u8; 8] = b"IXCMP\0\0\x05";
  const GROTH16_PROOF_TAG: &'static [u8; 8] = b"IXCMP\0\0\x06";
  const PLONK_SRS_MAGIC: &'static [u8; 8] = b"IXPSRS01";
  const PLONK_SRS_FORMAT: &'static str = "ix-bls12-381-plonk-srs-export-v2";
  const PLONK_VK_FORMAT: &'static str = "ix-bls-plonk-vk-v1";
  const PLONK_ANCHOR_BYTES: usize = 240;
  const GROTH16_PROOF_BYTES_NO_COMMIT: usize = 244;
  const GROTH16_PROOF_BYTES_WITH_COMMIT: usize = 292;

  fn endo_beta() -> Option<Self::Fq> {
    Some(ark_bls12_381::g1::BETA)
  }

  fn encode_g1_evm(point: G1AffineOf<Self>) -> Vec<u8> {
    use ark_ec::AffineRepr;
    if point.is_zero() {
      return vec![0; 128];
    }
    [
      vec![0u8; 16],
      point.x.into_bigint().to_bytes_be(),
      vec![0u8; 16],
      point.y.into_bigint().to_bytes_be(),
    ]
    .concat()
  }

  fn encode_g2_vk(point: &G2AffineOf<Self>) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(Self::G2_COMPRESSED_BYTES);
    point.serialize_compressed(&mut bytes).expect("Vec serialization");
    bytes
  }

  fn encode_plonk_anchors(
    g1: &G1AffineOf<Self>,
    g2: &G2AffineOf<Self>,
    tau_g2: &G2AffineOf<Self>,
  ) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(Self::PLONK_ANCHOR_BYTES);
    g1.serialize_compressed(&mut bytes).expect("Vec serialization");
    bytes.extend(Self::encode_g2_vk(g2));
    bytes.extend(Self::encode_g2_vk(tau_g2));
    bytes
  }

  #[inline]
  fn fr_mont_limbs(v: Self::Fr) -> [u64; 4] {
    v.0.0
  }

  #[inline]
  fn fr_mont_limbs_ref(v: &Self::Fr) -> &[u64; 4] {
    &v.0.0
  }

  #[inline]
  fn fr_from_mont_limbs_unchecked(limbs: [u64; 4]) -> Self::Fr {
    ark_bls12_381::Fr::new_unchecked(BigInt(limbs))
  }

  #[cfg(feature = "cuda")]
  #[inline]
  fn fq_to_mont_limbs(v: Self::Fq) -> Self::FqLimbs {
    v.0.0
  }

  #[cfg(feature = "cuda")]
  #[inline]
  fn fq_from_mont_limbs_unchecked(limbs: Self::FqLimbs) -> Self::Fq {
    ark_bls12_381::Fq::new_unchecked(BigInt(limbs))
  }

  #[cfg(feature = "cuda")]
  #[inline]
  fn fq_abi_triple() -> [Self::FqLimbs; 3] {
    [
      ark_bls12_381::Fq::MODULUS.0,
      ark_bls12_381::Fq::ONE.0.0,
      <ark_bls12_381::FqConfig as MontConfig<6>>::R2.0,
    ]
  }

  fn cpu_msm(
    bases: &[G1AffineOf<Self>],
    scalars: &[Self::Fr],
  ) -> G1ProjectiveOf<Self> {
    use ark_ec::VariableBaseMSM;
    ark_bls12_381::G1Projective::msm(bases, scalars).expect("equal lengths")
  }
}

/// Decode one validated G1 point with a unique compressed representation for `C`.
/// Arkworks' generic short-Weierstrass decoder ignores the x-coordinate
/// when the infinity flag is set, so validation alone permits aliases.
pub(crate) fn read_g1_compressed_for<C: KzgCurve>(
  input: &mut &[u8],
) -> Result<G1AffineOf<C>, SerializationError> {
  let width = C::G1_COMPRESSED_BYTES;
  let mut buf = [0u8; 48];
  let bytes = &mut buf[..width];
  input.read_exact(bytes)?;
  let point = G1AffineOf::<C>::deserialize_compressed(&*bytes)?;
  let mut canonical_buf = [0u8; 48];
  let canonical = &mut canonical_buf[..width];
  point.serialize_compressed(&mut canonical[..])?;
  if bytes != canonical {
    return Err(SerializationError::InvalidData);
  }
  Ok(point)
}

/// Decode one validated BN254 G1 point with a unique compressed representation.
#[cfg(test)]
pub(crate) fn read_g1_compressed(
  input: &mut &[u8],
) -> Result<G1Affine, SerializationError> {
  read_g1_compressed_for::<Bn254>(input)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::AffineRepr;

  fn assert_curve_encodings<C: KzgCurve>() {
    for point in [G1AffineOf::<C>::identity(), G1AffineOf::<C>::generator()] {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), C::G1_COMPRESSED_BYTES);
      assert_eq!(
        G1AffineOf::<C>::deserialize_compressed(&*bytes).unwrap(),
        point
      );
      bytes.clear();
      point.serialize_uncompressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), C::G1_UNCOMPRESSED_BYTES);
      assert_eq!(
        G1AffineOf::<C>::deserialize_uncompressed(&*bytes).unwrap(),
        point
      );
    }
    for point in [G2AffineOf::<C>::identity(), G2AffineOf::<C>::generator()] {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), C::G2_COMPRESSED_BYTES);
      assert_eq!(
        G2AffineOf::<C>::deserialize_compressed(&*bytes).unwrap(),
        point
      );
      bytes.clear();
      point.serialize_uncompressed(&mut bytes).unwrap();
      assert_eq!(bytes.len(), C::G2_UNCOMPRESSED_BYTES);
      assert_eq!(
        G2AffineOf::<C>::deserialize_uncompressed(&*bytes).unwrap(),
        point
      );
    }
    for point in [
      G1AffineOf::<C>::identity(),
      G1AffineOf::<C>::generator(),
      -G1AffineOf::<C>::generator(),
    ] {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      bytes.extend([0x12, 0x34]);
      let mut input = bytes.as_slice();
      assert_eq!(read_g1_compressed_for::<C>(&mut input).unwrap(), point);
      assert_eq!(input, &[0x12, 0x34]);
    }
    let mut bytes = Vec::new();
    G1AffineOf::<C>::generator().serialize_compressed(&mut bytes).unwrap();
    assert!(
      read_g1_compressed_for::<C>(&mut &bytes[..C::G1_COMPRESSED_BYTES - 1])
        .is_err()
    );
    assert!(
      read_g1_compressed_for::<C>(
        &mut vec![0xff; C::G1_COMPRESSED_BYTES].as_slice()
      )
      .is_err()
    );
  }

  #[test]
  fn point_encodings_match_widths_and_vectors_for_both_curves() {
    assert_curve_encodings::<Bn254>();
    assert_curve_encodings::<Bls12381>();

    let mut positive = [0; 32];
    positive[0] = 1;
    let mut negative = positive;
    negative[31] = 0x80;
    let mut infinity = [0; 32];
    infinity[31] = 0x40;
    for (point, expected) in [
      (G1Affine::generator(), positive),
      (-G1Affine::generator(), negative),
      (G1Affine::identity(), infinity),
    ] {
      let mut bytes = Vec::new();
      point.serialize_compressed(&mut bytes).unwrap();
      assert_eq!(bytes.as_slice(), expected.as_slice());
      bytes.extend([0x12, 0x34]);
      let mut input = bytes.as_slice();
      assert_eq!(read_g1_compressed(&mut input).unwrap(), point);
      assert_eq!(input, &[0x12, 0x34]);
    }

    // BLS12-381 infinity alias rejection (flag 0xc0 with nonzero x-coordinate).
    let mut bls_alias = [0u8; 48];
    bls_alias[0] = 0xc0;
    bls_alias[47] = 1;
    assert!(
      read_g1_compressed_for::<Bls12381>(&mut bls_alias.as_slice()).is_err()
    );
    // BLS12-381 non-subgroup torsion point (0, 2) rejected.
    let torsion = bls12_381::G1Affine::new_unchecked(
      bls12_381::Fq::from(0u64),
      bls12_381::Fq::from(2u64),
    );
    let mut torsion_bytes = Vec::new();
    torsion.serialize_compressed(&mut torsion_bytes).unwrap();
    assert!(
      read_g1_compressed_for::<Bls12381>(&mut torsion_bytes.as_slice())
        .is_err()
    );
  }

  #[test]
  fn point_reader_rejects_truncated_invalid_aliased_and_noncanonical_points() {
    let mut alias = [0; 32];
    alias[0] = 1;
    alias[31] = 0x40;
    assert_eq!(
      G1Affine::deserialize_compressed(alias.as_slice()).unwrap(),
      G1Affine::identity()
    );
    assert!(read_g1_compressed(&mut alias.as_slice()).is_err());
    assert!(
      read_g1_compressed(&mut Fq::MODULUS.to_bytes_le().as_slice()).is_err()
    );
  }

  #[test]
  fn curve_selector_parsing_and_labels() {
    assert_eq!(Curve::parse("bn254").unwrap(), Curve::Bn254);
    assert_eq!(Curve::parse("bls12-381").unwrap(), Curve::Bls12381);
    assert_eq!(Curve::parse("bls12_381").unwrap(), Curve::Bls12381);
    assert!(Curve::parse("secp256k1").is_err());
    assert!(Curve::Bls12381.security_label().contains("EIP-2537"));
    assert!(Curve::Bls12381.security_label().contains("Filecoin challenge_19"));
    assert!(Curve::Bn254.security_label().contains("Ignition"));
  }
}
