//! Count the recursive frontend for a four-row development KZG proof.

use ix_proof_compression::{
  kzg::{KzgConfig, Scalar, Srs, compact::FixedProofCodec},
  recursive::native_verifier::{self, InnerVerifyingKey},
};
use multi_stark::{
  config::ProofConfig,
  expr::Expr,
  lookup::Lookup,
  plonkish::CircuitStats,
  system::{CircuitInputs, System, SystemWitness},
  traits::{Algebra, Field},
};
use p3_matrix::dense::RowMajorMatrix;
use serde_json::{Value, json};
use std::{io::Write, sync::Arc};

fn counters(stats: CircuitStats) -> [(&'static str, usize); 10] {
  [
    ("hash_calls", stats.hash_calls),
    ("hash_compressions", stats.hash_compressions),
    ("values", stats.values),
    ("inputs", stats.inputs),
    ("gates", stats.gates),
    ("lookups", stats.lookups),
    ("tables", stats.tables),
    ("publics", stats.publics),
    ("hint_calls", stats.hint_calls),
    ("hint_outputs", stats.hint_outputs),
  ]
}

fn stats_json(stats: CircuitStats, previous: CircuitStats) -> Value {
  Value::Object(
    counters(stats)
      .into_iter()
      .zip(counters(previous))
      .map(|((name, value), (_, before))| {
        (
          name.to_owned(),
          json!(value.checked_sub(before).expect("cumulative frontend count")),
        )
      })
      .collect(),
  )
}

fn opening_values(matrices: &[Vec<Vec<Scalar>>]) -> usize {
  matrices.iter().flatten().map(Vec::len).sum()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let srs =
    Arc::new(Srs::unsafe_dev_setup(4, b"recursive-size-development-only"));
  let trace = RowMajorMatrix::new(
    (2..=5u64)
      .flat_map(|x| [Scalar::from_u64(x), Scalar::from_u64(x * x)])
      .collect(),
    2,
  );
  let last_row = Expr::preprocessed(0);
  let x = Expr::main(0);
  let square = Expr::main(1);
  let one = Expr::constant(Scalar::ONE);
  let (system, key) = System::new(
    KzgConfig::new(srs.clone(), 2),
    [CircuitInputs {
      main_width: 2,
      preprocessed: Some(RowMajorMatrix::new_col(vec![
        Scalar::ZERO,
        Scalar::ZERO,
        Scalar::ZERO,
        Scalar::ONE,
      ])),
      constraints: vec![
        square.clone() - x.clone() * x.clone(),
        (one.clone() - last_row.clone())
          * (Expr::main_next(0) - x.clone() - one),
      ],
      lookups: vec![Lookup::pull(
        last_row,
        vec![Expr::constant(Scalar::from_u8(93)), x, square],
      )],
      ..Default::default()
    }],
  );
  let claims =
    vec![vec![Scalar::from_u8(93), Scalar::from_u8(5), Scalar::from_u8(25)]];
  let claim_refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  let proof = system.prove_multiple_claims(
    &key,
    &claim_refs,
    SystemWitness::from_stage_1(vec![trace], &system),
  );
  system
    .verify_multiple_claims(&claim_refs, &proof)
    .map_err(|error| format!("inner KZG verification failed: {error:?}"))?;
  let fixed =
    system.preprocessed_commit.as_ref().ok_or("missing fixed commitment")?;
  let vk = InnerVerifyingKey {
    circuits: &system.circuits,
    fixed,
    transcript_seed: system.config.transcript_seed(),
    transcript_kind: system.config.transcript_kind(),
    generator: srs.g1[0],
    g2: srs.g2,
    tau_g2: srs.tau_g2,
    max_log_degree: system.config.max_log_degree(),
  };
  let counts = native_verifier::count(&vk, &proof, &claims, &[(0, 1), (0, 2)])?;
  let compact =
    FixedProofCodec::new(&system, &proof.log_degrees)?.encode(&proof)?;
  let mut previous = CircuitStats::default();
  let phases: Vec<_> = counts
    .phases
    .iter()
    .map(|phase| {
      let result = json!({
        "name": phase.name,
        "incremental": stats_json(phase.stats, previous),
        "cumulative": stats_json(phase.stats, CircuitStats::default()),
      });
      previous = phase.stats;
      result
    })
    .collect();
  let tables: Vec<_> = counts
    .table_dimensions
    .iter()
    .map(|&(rows, width)| json!({ "rows": rows, "width": width }))
    .collect();
  let report = json!({
    "curve": if cfg!(feature = "bn254") { "bn254" } else { "bls12-381" },
    "scope": "Four-row development fixture; frontend gates and lookups, not gnark PLONK constraints or production performance.",
    "recursive_proof_generated": false,
    "frontend": {
      "total": stats_json(counts.stats, CircuitStats::default()),
      "phases": phases,
      "tables": tables,
      "msm_terms": counts.msm_terms,
    },
    "inner": {
      "rows": 4,
      "main_columns": 2,
      "fixed_columns": 1,
      "claims": [[93, 5, 25]],
      "public_locations": [[0, 1], [0, 2]],
      "max_quotient_degree": 2,
      "development_srs_powers": srs.g1.len(),
      "log_degrees": proof.log_degrees,
      "commitments": {
        "fixed": fixed.0.iter().map(Vec::len).sum::<usize>(),
        "main": proof.commitments.stage_1_trace.0.iter().map(Vec::len).sum::<usize>(),
        "stage2": proof.commitments.stage_2_trace.0.iter().map(Vec::len).sum::<usize>(),
        "quotient": proof.commitments.quotient_chunks.0.iter().map(Vec::len).sum::<usize>(),
      },
      "opening_values": {
        "fixed": opening_values(proof.preprocessed_opened_values.as_deref().unwrap_or_default()),
        "main": opening_values(&proof.stage_1_opened_values),
        "stage2": opening_values(&proof.stage_2_opened_values),
        "quotient": opening_values(&proof.quotient_opened_values),
      },
      "opening_proof_points": proof.opening_proof.0.len(),
      "compact_bytes": compact.len(),
      "native_verification_passed": true,
    },
  });
  let mut output = std::io::stdout().lock();
  serde_json::to_writer_pretty(&mut output, &report)?;
  writeln!(output)?;
  Ok(())
}
