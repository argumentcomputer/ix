use super::*;
use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::system::{CircuitInputs, System, SystemWitness};
use multi_stark::traits::{Algebra, Field};
use p3_matrix::Matrix;

fn circuits() -> Vec<CircuitInputs<Scalar>> {
  let m = Expr::main;
  let f = Scalar::from_u8;
  vec![
    CircuitInputs {
      main_width: 3,
      constraints: vec![m(0) * m(1) - m(2)],
      lookups: vec![
        Lookup::push(Expr::constant(Scalar::ONE), vec![m(0), m(2)]),
        Lookup::pull(Expr::constant(Scalar::ONE), vec![m(0), m(2)]),
      ],
      ..Default::default()
    },
    // Reads next rows of both main and fixed columns.
    CircuitInputs {
      main_width: 2,
      preprocessed: Some(RowMajorMatrix::new_col(vec![f(7); 8])),
      constraints: vec![
        Expr::main_next(0) - Expr::preprocessed_next(0),
        m(1) - m(0) - Expr::constant(f(1)),
      ],
      ..Default::default()
    },
  ]
}

fn witness(system: &System<PackedShplonkConfig>) -> SystemWitness<Scalar> {
  let f = Scalar::from_u32;
  SystemWitness::from_stage_1(
    vec![
      RowMajorMatrix::new(
        [
          2, 3, 6, 4, 5, 20, 7, 8, 56, 1, 1, 1, 2, 3, 6, 4, 5, 20, 7, 8, 56, 1,
          1, 1,
        ]
        .map(f)
        .to_vec(),
        3,
      ),
      RowMajorMatrix::new((0..8).flat_map(|_| [f(7), f(8)]).collect(), 2),
    ],
    system,
  )
}

#[test]
fn multi_stark_proofs_verify_with_packed_shplonk_openings() {
  // Cap 16 packs height-8 columns in pairs: the second stage-1 pack mixes a
  // current-row-only column with a next-row reader.
  let srs = Arc::new(Srs::unsafe_dev_setup(16, b"packed-shplonk-system"));
  let (system, key) =
    System::new(PackedShplonkConfig::new(srs.clone(), 4), circuits());
  let proof = system.prove_multiple_claims(&key, &[], witness(&system));
  system.verify_multiple_claims(&[], &proof).unwrap();
  assert_eq!(proof.commitments.stage_1_trace.packs.len(), 3);
  assert_eq!(
    proof.stage_1_opened_values.iter().map(Vec::len).collect::<Vec<_>>(),
    [1, 2]
  );
  // Column 2 of the first circuit shares a pack with a next-row reader.
  assert!(!proof.opening_proof.extra_values.is_empty());

  let config = bincode::config::standard();
  let bytes = bincode::serde::encode_to_vec(&proof, config).unwrap();
  let (decoded, _): (multi_stark::prover::Proof<PackedShplonkConfig>, _) =
    bincode::serde::decode_from_slice(&bytes, config).unwrap();
  let prover_config = system.config.clone();
  let mut system = system;
  system.config =
    PackedShplonkConfig::verifier_only(VerifierParams::from_srs(&srs), 4);
  system.verify_multiple_claims(&[], &decoded).unwrap();
  system.config = prover_config;

  let mut bad = proof.clone();
  bad.stage_1_opened_values[1][1][0] += Scalar::ONE;
  assert!(system.verify_multiple_claims(&[], &bad).is_err());
  let mut bad = proof.clone();
  bad.opening_proof.extra_values[0] += Scalar::ONE;
  assert!(system.verify_multiple_claims(&[], &bad).is_err());
  let mut bad = proof.clone();
  bad.opening_proof.extra_values.push(Scalar::ZERO);
  assert!(system.verify_multiple_claims(&[], &bad).is_err());
  let mut bad = proof.clone();
  bad.quotient_opened_values[0][0][0] += Scalar::ONE;
  assert!(system.verify_multiple_claims(&[], &bad).is_err());
  let mut bad = proof.clone();
  bad.commitments.stage_2_trace.packs.swap(0, 1);
  assert!(system.verify_multiple_claims(&[], &bad).is_err());
  let mut bad = proof;
  bad.commitments.stage_1_trace.packs.pop();
  assert!(system.verify_multiple_claims(&[], &bad).is_err());
}

#[test]
fn next_row_classes_separate_packs_and_remove_extra_values() {
  let srs = Arc::new(Srs::unsafe_dev_setup(16, b"packed-shplonk-system"));
  let (system, key) = System::new(PackedShplonkConfig::new(srs, 4), circuits());
  // The first circuit reads only current rows, the second next rows.
  system.config.set_main_next_rows(vec![false, true]);
  let proof = system.prove_multiple_claims(&key, &[], witness(&system));
  system.verify_multiple_claims(&[], &proof).unwrap();
  let classes: Vec<_> = proof
    .commitments
    .stage_1_trace
    .matrices
    .iter()
    .map(|m| m.next_row)
    .collect();
  assert_eq!(classes, [false, true]);
  assert_eq!(proof.commitments.stage_1_trace.packs.len(), 3);
  assert!(proof.opening_proof.extra_values.is_empty());

  // A flipped class changes the transcript and the planned packs.
  let mut bad = proof.clone();
  bad.commitments.stage_1_trace.matrices[0].next_row = true;
  assert!(system.verify_multiple_claims(&[], &bad).is_err());
  // Classes steer planning only: any declaration yields a valid proof.
  system.config.set_main_next_rows(vec![true, false]);
  let proof = system.prove_multiple_claims(&key, &[], witness(&system));
  system.verify_multiple_claims(&[], &proof).unwrap();
}

#[test]
fn encodings_reject_trailing_and_truncated_bytes() {
  let commitment = Commitment {
    matrices: vec![MatrixShape { log_size: 2, width: 3, next_row: true }],
    packs: vec![G1Affine::default()],
  };
  let bytes = commitment.to_bytes().unwrap();
  assert_eq!(Commitment::from_bytes(&bytes).unwrap(), commitment);
  assert!(Commitment::from_bytes(&bytes[..bytes.len() - 1]).is_err());
  let mut long = bytes;
  long.push(0);
  assert!(Commitment::from_bytes(&long).is_err());
  let proof = Proof {
    extra_values: vec![Scalar::ONE],
    opening: shplonk::Proof {
      w1: G1Affine::default(),
      w2: G1Affine::default(),
    },
  };
  let bytes = proof.to_bytes().unwrap();
  assert_eq!(Proof::from_bytes(&bytes).unwrap(), proof);
  assert!(Proof::from_bytes(&bytes[..bytes.len() - 1]).is_err());
}

/// Heights and widths large enough that CUDA builds take the device
/// interpolation, MSM, lookup, quotient and opening-division paths.
fn wide_circuits(height: usize) -> Vec<CircuitInputs<Scalar>> {
  let m = Expr::main;
  let f = Scalar::from_u8;
  vec![
    CircuitInputs {
      main_width: 4,
      constraints: vec![m(0) * m(1) - m(2), m(3) - m(0) - m(1)],
      lookups: vec![
        Lookup::push(Expr::constant(Scalar::ONE), vec![m(0), m(2)]),
        Lookup::pull(Expr::constant(Scalar::ONE), vec![m(0), m(2)]),
      ],
      ..Default::default()
    },
    CircuitInputs {
      main_width: 2,
      preprocessed: Some(RowMajorMatrix::new_col(vec![f(7); height / 2])),
      constraints: vec![
        Expr::main_next(0) - Expr::preprocessed_next(0),
        m(1) - m(0) - Expr::constant(f(1)),
      ],
      lookups: vec![
        Lookup::push(Expr::constant(Scalar::ONE), vec![m(1)]),
        Lookup::pull(Expr::constant(Scalar::ONE), vec![m(1)]),
      ],
      ..Default::default()
    },
  ]
}

fn wide_traces(height: usize) -> Vec<RowMajorMatrix<Scalar>> {
  let f = Scalar::from_usize;
  vec![
    RowMajorMatrix::new(
      (0..height)
        .flat_map(|i| [f(i), f(i + 1), f(i) * f(i + 1), f(2 * i + 1)])
        .collect(),
      4,
    ),
    RowMajorMatrix::new(
      (0..height / 2).flat_map(|_| [f(7), f(8)]).collect(),
      2,
    ),
  ]
}

fn wide_proof(streaming: bool) -> Vec<u8> {
  const HEIGHT: usize = 1 << 14;
  let srs =
    Arc::new(Srs::unsafe_dev_setup(1 << 16, b"packed-shplonk-backends"));
  let mut config = PackedShplonkConfig::new(srs, 4);
  if streaming {
    config = config.with_streaming_lookups().with_streaming_quotient();
  }
  let (system, key) = System::new(config, wide_circuits(HEIGHT));
  let traces = wide_traces(HEIGHT);
  let witness = if streaming {
    let lookups = traces
      .iter()
      .zip(&system.circuits)
      .map(|(trace, circuit)| {
        let widths: Vec<_> =
          circuit.graph.lookups.iter().map(|l| l.args.len()).collect();
        multi_stark::lookup::LookupValues::shape_only(trace.height(), &widths)
      })
      .collect();
    SystemWitness { traces, lookups }
  } else {
    SystemWitness::from_stage_1(traces, &system)
  };
  let proof = system.prove_multiple_claims(&key, &[], witness);
  system.verify_multiple_claims(&[], &proof).unwrap();
  assert_eq!(proof.commitments.stage_1_trace.packs.len(), 2);
  bincode::serde::encode_to_vec(&proof, bincode::config::standard()).unwrap()
}

#[test]
fn streaming_proofs_match_portable_proofs() {
  assert_eq!(wide_proof(true), wide_proof(false));
}

/// The CPU and CUDA builds must produce this proof byte for byte.
#[test]
fn proofs_are_backend_independent() {
  assert_eq!(
    blake3::hash(&wide_proof(true)).to_hex().as_str(),
    "68ee5c03588dca49bf206e6319f2025dbbfeb4f7028f7d42046dd6f4767fb1ca"
  );
}
