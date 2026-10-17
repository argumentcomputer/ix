//! Deterministic development proofs for comparing independently built backends.

use ix_proof_compression::kzg::{
  KzgCommitment, KzgConfig, Scalar, Srs, VerifierParams,
  compact::FixedProofCodec, curve,
};
use multi_stark::{
  config::ProofConfig,
  expr::Expr,
  lookup::Lookup,
  system::{Circuit, CircuitInputs, System, SystemWitness},
  traits::{Algebra, Field},
};
use p3_matrix::dense::RowMajorMatrix;
use serde::{Deserialize, Serialize};
use std::{fs, path::Path, sync::Arc, time::Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const HEIGHTS: [usize; 2] = [4096, 8192];
const QUOTIENT: usize = 4;
const SEED: &[u8] = b"ix-kzg-backend-parity/development/v1";

#[derive(Serialize, Deserialize)]
struct Verifier {
  curve: String,
  parameters: Vec<u8>,
  circuits: Vec<Circuit<Scalar>>,
  fixed: Option<KzgCommitment>,
  indices: Vec<Option<usize>>,
}

fn claims() -> [[Scalar; 3]; 2] {
  HEIGHTS.map(|height| {
    let x = Scalar::from_usize(height - 1);
    [Scalar::from_usize(height), x, x * x]
  })
}

fn circuit(height: usize) -> CircuitInputs<Scalar> {
  let x = Expr::main(0);
  let square = Expr::main(1);
  let transition_message =
    vec![x.clone(), Expr::main_next(0), Expr::preprocessed_next(0)];
  let local_message = vec![Expr::preprocessed(0), square.clone()];
  // Lookup multiplicities need Boolean trace values; the transition selector
  // is not normalized to one away from the last row.
  let active = Expr::constant(Scalar::ONE) - Expr::preprocessed(1);
  CircuitInputs {
    main_width: 2,
    preprocessed: Some(RowMajorMatrix::new(
      (0..height)
        .flat_map(|row| {
          [Scalar::from_usize(row), Scalar::from_bool(row + 1 == height)]
        })
        .collect(),
      2,
    )),
    constraints: vec![
      x.clone() - Expr::preprocessed(0),
      square.clone() - x.clone() * x.clone(),
      x.clone()
        * x.clone()
        * x.clone()
        * (square.clone() - x.clone() * x.clone()),
      Expr::IsTransition
        * (Expr::main_next(0) - x.clone() - Expr::constant(Scalar::ONE)),
    ],
    lookups: vec![
      Lookup::pull(
        Expr::preprocessed(1),
        vec![Expr::constant(Scalar::from_usize(height)), x, square],
      ),
      Lookup::push(Expr::constant(Scalar::ONE), transition_message.clone()),
      Lookup::pull(Expr::constant(Scalar::ONE), transition_message),
      Lookup::push(active.clone(), local_message.clone()),
      Lookup::pull(active, local_message),
    ],
    lookup_group_size: 2,
    ..Default::default()
  }
}

fn configure(mode: &str) -> Result<()> {
  #[cfg(feature = "cuda")]
  {
    use ix_proof_compression::kzg::cuda::{self, PassMode, Settings};
    let (passes, srs_cache) = match mode {
      "dense" => (PassMode::Off, false),
      "passes" => (PassMode::Force, false),
      "cached" => (PassMode::Off, true),
      _ => {
        return Err("CUDA builds require dense, passes or cached mode".into());
      },
    };
    if !cuda::configure(Settings {
      devices: Some(vec![0]),
      msm_chunk_points: 2048,
      passes,
      srs_cache,
      ..Settings::default()
    }) {
      return Err("CUDA settings already installed".into());
    }
  }
  #[cfg(not(feature = "cuda"))]
  if mode != "cpu" {
    return Err("CPU builds require cpu mode".into());
  }
  Ok(())
}

fn prove(out: &Path, mode: &str) -> Result<()> {
  configure(mode)?;
  if out.exists() && fs::read_dir(out)?.next().is_some() {
    return Err("output directory must be empty".into());
  }
  let started = Instant::now();
  let srs = Arc::new(Srs::unsafe_dev_setup(HEIGHTS[1], SEED));
  let config = KzgConfig::new(srs, QUOTIENT)
    .with_streaming_lookups()
    .with_streaming_quotient();
  let (mut system, key) = System::new(config, HEIGHTS.map(circuit));
  let claims = claims();
  let refs: Vec<_> = claims.iter().map(|c| c.as_slice()).collect();
  let traces: Vec<_> = HEIGHTS
    .into_iter()
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
    .collect();
  let input = bincode::serde::encode_to_vec(
    (&claims, &traces),
    bincode::config::standard(),
  )?;
  let proof = system.prove_multiple_claims(
    &key,
    &refs,
    SystemWitness::from_stage_1(traces, &system),
  );
  system
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("new proof: {e:?}"))?;
  let parameters = system.config.pcs().verifier_params().to_bytes()?;
  system.config = KzgConfig::verifier_only(
    VerifierParams::from_bytes(&parameters)?,
    QUOTIENT,
  );
  let codec = FixedProofCodec::new(&system, &proof.log_degrees)?;
  let bytes = codec.encode(&proof)?;
  system
    .verify_multiple_claims(&refs, &codec.decode(&bytes)?)
    .map_err(|e| format!("compact proof: {e:?}"))?;
  for circuit in &mut system.circuits {
    circuit.preprocessed = None;
  }
  let verifier = bincode::serde::encode_to_vec(
    Verifier {
      curve: curve::NAME.to_owned(),
      parameters,
      circuits: system.circuits,
      fixed: system.preprocessed_commit,
      indices: system.preprocessed_indices,
    },
    bincode::config::standard(),
  )?;
  let report = serde_json::json!({
    "format": "ix-kzg-backend-parity/v1",
    "curve": curve::NAME,
    "mode": mode,
    "known_trapdoor": true,
    "cuda": cfg!(feature = "cuda"),
    "trace_heights": HEIGHTS,
    "quotient_factor_cap": QUOTIENT,
    "input_blake3": blake3::hash(&input).to_hex().as_str(),
    "proof_blake3": blake3::hash(&bytes).to_hex().as_str(),
    "verifier_blake3": blake3::hash(&verifier).to_hex().as_str(),
    "proof_bytes": bytes.len(),
    "opening_points": proof.opening_proof.0.len(),
    "native_verification_passed": true,
    "elapsed_seconds": started.elapsed().as_secs_f64(),
    "scope": "Two ordinary KZG circuits; excludes FRI compression and recursive KZG proving.",
  });
  fs::create_dir_all(out)?;
  fs::write(out.join("proof.bin"), &bytes)?;
  fs::write(out.join("verifier.bin"), &verifier)?;
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{}", serde_json::to_string(&report)?);
  Ok(())
}

fn verify(proof: &Path, verifier: &Path, trusted: &str) -> Result<()> {
  let verifier = fs::read(verifier)?;
  if blake3::hash(&verifier).to_hex().as_str() != trusted {
    return Err("verifier differs from the independently supplied pin".into());
  }
  let (key, used): (Verifier, usize) = bincode::serde::decode_from_slice(
    &verifier,
    bincode::config::standard().with_limit::<16777216>(),
  )?;
  if used != verifier.len() || key.curve != curve::NAME {
    return Err("invalid verifier curve or encoding".into());
  }
  let system = System {
    config: KzgConfig::verifier_only(
      VerifierParams::from_bytes(&key.parameters)?,
      QUOTIENT,
    ),
    circuits: key.circuits,
    preprocessed_commit: key.fixed,
    preprocessed_indices: key.indices,
  };
  let logs = HEIGHTS.map(|h| u8::try_from(h.ilog2()).expect("fixture height"));
  let codec = FixedProofCodec::new(&system, &logs)?;
  let bytes = fs::read(proof)?;
  let proof = codec.decode(&bytes)?;
  let claims = claims();
  let refs: Vec<_> = claims.iter().map(|c| c.as_slice()).collect();
  system
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("proof: {e:?}"))?;
  let mut wrong = claims;
  wrong[0][2] += Scalar::ONE;
  let wrong: Vec<_> = wrong.iter().map(|c| c.as_slice()).collect();
  if system.verify_multiple_claims(&wrong, &proof).is_ok() {
    return Err("changed claim accepted".into());
  }
  let mut changed = proof.clone();
  changed.stage_1_opened_values[0][0][0] += Scalar::ONE;
  if system.verify_multiple_claims(&refs, &changed).is_ok() {
    return Err("changed evaluation accepted".into());
  }
  println!(
    "{}",
    serde_json::json!({
      "curve": curve::NAME, "verified": true, "proof_blake3": blake3::hash(&bytes).to_hex().as_str(),
      "changed_claim_rejected": true, "changed_evaluation_rejected": true, "proving_srs_loaded": false,
    })
  );
  Ok(())
}

fn main() -> Result<()> {
  tracing_subscriber::fmt()
    .with_writer(std::io::stderr)
    .with_ansi(false)
    .with_env_filter(
      tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(
        |_| tracing_subscriber::EnvFilter::new("ix_proof_compression=debug"),
      ),
    )
    .init();
  let args: Vec<_> = std::env::args().skip(1).collect();
  match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
    ["prove", out, mode] => prove(Path::new(out), mode),
    ["verify", proof, verifier, trusted] => verify(Path::new(proof), Path::new(verifier), trusted),
    _ => Err("usage: kzg_backend_parity prove <empty-output-dir> <cpu|dense|passes|cached> | verify <proof.bin> <verifier.bin> <trusted-verifier-blake3>".into()),
  }
}
