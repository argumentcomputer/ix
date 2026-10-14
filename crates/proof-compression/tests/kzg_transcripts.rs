use std::sync::Arc;

use ix_proof_compression::kzg::compact::FixedProofCodec;
use ix_proof_compression::kzg::{KzgConfig, Scalar, Srs, TranscriptKind};
use multi_stark::config::ProofConfig;
use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::prover::Proof;
use multi_stark::system::{CircuitInputs, ProverKey, System, SystemWitness};
use multi_stark::traits::{Algebra, Field};
use p3_matrix::dense::RowMajorMatrix;

const HEIGHTS: [usize; 2] = [4, 8];
const MAX_QUOTIENT_DEGREE: usize = 4;

fn config() -> KzgConfig {
  KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(8, b"kzg-transcript-integration")),
    MAX_QUOTIENT_DEGREE,
  )
}

fn system(config: KzgConfig) -> (System<KzgConfig>, ProverKey<KzgConfig>) {
  System::new(
    config,
    HEIGHTS.map(|height| {
      let x = Expr::main(0);
      let square = Expr::main(1);
      CircuitInputs {
        main_width: 2,
        preprocessed: Some(RowMajorMatrix::new(
          (0..height)
            .flat_map(|row| {
              [
                Scalar::from_usize(row),
                if row + 1 == height { Scalar::ONE } else { Scalar::ZERO },
              ]
            })
            .collect(),
          2,
        )),
        constraints: vec![
          x.clone() - Expr::preprocessed(0),
          square.clone() - x.clone() * x.clone(),
          Expr::IsTransition
            * (Expr::main_next(0) - x.clone() - Expr::constant(Scalar::ONE)),
        ],
        // A fixed Boolean column gives the claim multiplicity one;
        // raw Lagrange boundary selectors are not normalized.
        lookups: vec![Lookup::pull(
          Expr::preprocessed(1),
          vec![Expr::constant(Scalar::from_usize(height)), x, square],
        )],
        ..Default::default()
      }
    }),
  )
}

fn claims() -> [[Scalar; 3]; 2] {
  HEIGHTS.map(|height| {
    let last = Scalar::from_usize(height - 1);
    [Scalar::from_usize(height), last, last * last]
  })
}

fn prove(
  system: &System<KzgConfig>,
  key: &ProverKey<KzgConfig>,
) -> Proof<KzgConfig> {
  let claims = claims();
  let refs: Vec<_> = claims.iter().map(|claim| claim.as_slice()).collect();
  let traces = HEIGHTS
    .map(|height| {
      RowMajorMatrix::new(
        (0..height)
          .flat_map(|row| {
            let x = Scalar::from_usize(row);
            [x, x * x]
          })
          .collect(),
        2,
      )
    })
    .to_vec();
  system.prove_multiple_claims(
    key,
    &refs,
    SystemWitness::from_stage_1(traces, system),
  )
}

#[test]
fn transcript_kinds_verify_compact_proofs_and_reject_tampering() {
  let base = config();
  let claims = claims();
  let refs: Vec<_> = claims.iter().map(|claim| claim.as_slice()).collect();
  let mut encodings = Vec::new();
  for kind in [TranscriptKind::Blake3, TranscriptKind::Keccak256] {
    let (mut system, key) = system(base.clone().with_transcript(kind));
    assert_eq!(system.config.transcript_kind(), kind);
    let proof = prove(&system, &key);
    assert_eq!(proof.log_degrees, [2, 3]);
    assert_eq!(proof.opening_proof.0.len(), 3);
    system.verify_multiple_claims(&refs, &proof).unwrap();

    let codec = FixedProofCodec::new(&system, &proof.log_degrees).unwrap();
    let compact = codec.encode(&proof).unwrap();
    let decoded = codec.decode(&compact).unwrap();
    assert_eq!(decoded.to_bytes().unwrap(), proof.to_bytes().unwrap());
    assert_eq!(codec.encode(&decoded).unwrap(), compact);
    system.verify_multiple_claims(&refs, &decoded).unwrap();
    encodings.push((proof.to_bytes().unwrap(), compact));

    let verifier = KzgConfig::verifier_only(
      system.config.pcs().verifier_params().clone(),
      MAX_QUOTIENT_DEGREE,
    )
    .with_transcript(kind);
    assert_eq!(verifier.transcript_seed(), system.config.transcript_seed());
    system.config = verifier.clone();
    system.verify_multiple_claims(&refs, &proof).unwrap();
    system.verify_multiple_claims(&refs, &decoded).unwrap();

    let mut wrong_claims = claims;
    wrong_claims[0][2] += Scalar::ONE;
    let wrong_refs: Vec<_> =
      wrong_claims.iter().map(|claim| claim.as_slice()).collect();
    assert!(
      system.verify_multiple_claims(&wrong_refs, &proof).is_err(),
      "{kind:?} accepted a changed public claim"
    );

    let mut wrong_evaluation = proof.clone();
    wrong_evaluation.stage_1_opened_values[0][0][0] += Scalar::ONE;
    assert!(
      system.verify_multiple_claims(&refs, &wrong_evaluation).is_err(),
      "{kind:?} accepted a changed opened value"
    );

    let mut wrong_opening = proof.clone();
    wrong_opening.opening_proof.0[0] = Default::default();
    assert_ne!(wrong_opening.opening_proof, proof.opening_proof);
    assert!(
      system.verify_multiple_claims(&refs, &wrong_opening).is_err(),
      "{kind:?} accepted a changed KZG opening witness"
    );

    let other = match kind {
      TranscriptKind::Blake3 => TranscriptKind::Keccak256,
      TranscriptKind::Keccak256 => TranscriptKind::Blake3,
    };
    system.config = verifier.with_transcript(other);
    assert!(
      system.verify_multiple_claims(&refs, &proof).is_err(),
      "{other:?} accepted a {kind:?} proof"
    );
    assert!(
      system.verify_multiple_claims(&refs, &decoded).is_err(),
      "{other:?} accepted a compact {kind:?} proof"
    );
  }
  assert_ne!(encodings[0].0, encodings[1].0);
  assert_ne!(encodings[0].1, encodings[1].1);
  assert_eq!(encodings[0].0.len(), encodings[1].0.len());
  assert_eq!(encodings[0].1.len(), encodings[1].1.len());
}

#[test]
fn default_transcript_preserves_explicit_blake3_proof_bytes() {
  let config = config();
  assert_eq!(config.transcript_kind(), TranscriptKind::Blake3);
  let (mut system, key) = system(config.clone());
  let claims = claims();
  let refs: Vec<_> = claims.iter().map(|claim| claim.as_slice()).collect();
  let default = prove(&system, &key);
  system.verify_multiple_claims(&refs, &default).unwrap();
  let codec = FixedProofCodec::new(&system, &default.log_degrees).unwrap();

  system.config = config.with_transcript(TranscriptKind::Blake3);
  let explicit = prove(&system, &key);
  system.verify_multiple_claims(&refs, &explicit).unwrap();
  assert_eq!(default.to_bytes().unwrap(), explicit.to_bytes().unwrap());
  assert_eq!(codec.encode(&default).unwrap(), codec.encode(&explicit).unwrap());
}

#[test]
#[ignore = "requires IX_KZG_FILECOIN_CACHE and IX_KZG_FILECOIN_MANIFEST"]
fn filecoin_keccak_proof_verifies_with_portable_authenticated_parameters() {
  use ix_proof_compression::kzg::VerifierParams;
  use ix_proof_compression::kzg::srs::filecoin::{
    filecoin_setup_id, load_filecoin_cache,
  };

  let path = std::path::PathBuf::from(
    std::env::var_os("IX_KZG_FILECOIN_CACHE")
      .expect("IX_KZG_FILECOIN_CACHE must name an authenticated prefix cache"),
  );
  let manifest = std::env::var("IX_KZG_FILECOIN_MANIFEST")
    .expect("IX_KZG_FILECOIN_MANIFEST must pin the cache's import receipt");
  let manifest = manifest.trim();
  assert!(
    manifest.len() == 64 && manifest.is_ascii(),
    "IX_KZG_FILECOIN_MANIFEST must be a 64-character BLAKE3 digest"
  );
  let mut receipt = [0; 32];
  for (i, byte) in receipt.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&manifest[2 * i..2 * i + 2], 16)
      .expect("IX_KZG_FILECOIN_MANIFEST must contain hexadecimal digits");
  }

  let srs = load_filecoin_cache(&path, receipt, 8).unwrap();
  assert_eq!(srs.public_setup.id, filecoin_setup_id());
  let config = KzgConfig::new(Arc::new(srs), MAX_QUOTIENT_DEGREE)
    .with_transcript(TranscriptKind::Keccak256);
  let (mut system, key) = system(config);
  let claims = claims();
  let refs: Vec<_> = claims.iter().map(|claim| claim.as_slice()).collect();
  let proof = prove(&system, &key);
  system.verify_multiple_claims(&refs, &proof).unwrap();

  let codec = FixedProofCodec::new(&system, &proof.log_degrees).unwrap();
  let compact = codec.encode(&proof).unwrap();
  let decoded = codec.decode(&compact).unwrap();
  assert_eq!(decoded.to_bytes().unwrap(), proof.to_bytes().unwrap());
  assert_eq!(codec.encode(&decoded).unwrap(), compact);

  let anchors = load_filecoin_cache(&path, receipt, 2).unwrap();
  let params = VerifierParams::with_max_trace_len(&anchors, 8);
  let params_bytes = params.to_bytes().unwrap();
  assert_eq!(
    params_bytes,
    system.config.pcs().verifier_params().to_bytes().unwrap()
  );
  let verifier = KzgConfig::verifier_only(
    VerifierParams::from_bytes(&params_bytes).unwrap(),
    MAX_QUOTIENT_DEGREE,
  )
  .with_transcript(TranscriptKind::Keccak256);
  assert_eq!(verifier.transcript_seed(), system.config.transcript_seed());
  system.config = verifier.clone();
  system.verify_multiple_claims(&refs, &proof).unwrap();
  system.verify_multiple_claims(&refs, &decoded).unwrap();

  system.config = verifier.with_transcript(TranscriptKind::Blake3);
  assert!(system.verify_multiple_claims(&refs, &proof).is_err());
  assert!(system.verify_multiple_claims(&refs, &decoded).is_err());

  let mut wrong_receipt = receipt;
  wrong_receipt[0] ^= 1;
  assert!(load_filecoin_cache(&path, wrong_receipt, 8).is_err());
}
