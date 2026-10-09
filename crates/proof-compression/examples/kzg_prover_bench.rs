//! Reduced Plonkish workload for KZG performance comparisons, not an Init proof.
use ix_proof_compression::foreign::KzgCircuitExt;

use ix_proof_compression::kzg::KzgConfig;
use ix_proof_compression::kzg::Scalar;
use ix_proof_compression::kzg::Srs;
use ix_proof_compression::kzg::compact::FixedProofCodec;
use ix_proof_compression::kzg::pcs::KzgProverData;
use multi_stark::config::ProofConfig;
use multi_stark::lookup::LookupValues;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::prover::Stage1;
use multi_stark::system::System;
use multi_stark::traits::Algebra;
use multi_stark::traits::Field;
use multi_stark::traits::Pcs;
use p3_matrix::Matrix;
use serde_json::{Value, json};
use std::{collections::BTreeMap, sync::Arc, time::Instant};

fn measured<T>(
  phases: &mut BTreeMap<&'static str, Value>,
  name: &'static str,
  f: impl FnOnce() -> T,
) -> T {
  eprintln!("BENCH_PHASE {name}");
  let start = Instant::now();
  let result = f();
  let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
  let kib = |key: &str| {
    status
      .lines()
      .find_map(|line| {
        line.strip_prefix(key)?.split_whitespace().next()?.parse::<u64>().ok()
      })
      .map(|n| n * 1024)
  };
  phases.insert(
        name,
        json!({"seconds": start.elapsed().as_secs_f64(),
        "rss_bytes_after": kib("VmRSS:"), "peak_rss_bytes_so_far": kib("VmHWM:")}),
    );
  result
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if !(1..=2).contains(&args.len()) {
    return Err(
      "usage: prover_bench <log-rows: 12..22> [checkpoint-dir]".into(),
    );
  }
  let log: usize = args[0].parse()?;
  if !(12..=22).contains(&log) {
    return Err(
      "log-rows must be 12..22; use the full harness for larger jobs".into(),
    );
  }
  tracing_subscriber::fmt()
    .with_ansi(false)
    .with_writer(std::io::stderr)
    .init();
  let disk_dir = args.get(1).map(std::path::PathBuf::from);
  if let Some(dir) = &disk_dir {
    std::fs::create_dir(dir)?;
  }
  let checkpoint = |name: &str,
                    data: KzgProverData|
   -> Result<KzgProverData, Box<dyn std::error::Error>> {
    let Some(dir) = &disk_dir else {
      return Ok(data);
    };
    use std::io::Write;
    let path = dir.join(name);
    let mut writer = std::io::BufWriter::new(std::fs::File::create_new(&path)?);
    data.write_checkpoint(&mut writer)?;
    writer.flush()?;
    drop(writer);
    drop(data);
    Ok(KzgProverData::read_checkpoint_file(path)?)
  };
  let start = Instant::now();
  let mut phases = BTreeMap::new();
  let height = 1usize << log;
  let (lowered, assignment) = measured(&mut phases, "frontend", || {
    let mut b = CircuitBuilder::<Scalar>::new();
    let table_height = 1usize << (log - 2).min(16);
    let table = b.fixed_table(
      "range",
      (0..table_height).map(|i| vec![Scalar::from_usize(i)]).collect(),
    );
    let x = b.input("x");
    let mut state = x;
    // Dense, nonconstant scalar columns with arithmetic, wiring and lookups.
    // Leave enough padding to keep the requested power-of-two height.
    while b.stats().gates + b.stats().lookups < height * 7 / 8 {
      let square = b.mul(state, state);
      state = b.add(square, x);
      b.lookup(table, &[x]);
    }
    b.expose_public(state);
    let circuit = b.finish();
    let mut witness = circuit.witness();
    witness.set(x, Scalar::from_u8(17)).unwrap();
    let assignment = witness.generate().unwrap();
    let lowered = circuit
      .lower_to_multi_stark_sharded(Scalar::from_u8(94), height)
      .unwrap()
      .merge_table_traces(height)
      .unwrap();
    assert_eq!(lowered.main_heights(), [height]);
    (lowered, assignment)
  });
  let claims = lowered.claims(assignment.public_values())?;
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  let traces = measured(&mut phases, "trace_generation", || {
    lowered.traces(&assignment).unwrap()
  });
  let definitions = measured(&mut phases, "fixed_generation", || {
    lowered.kzg_circuit_inputs(height, 2).unwrap()
  });
  drop(assignment);
  drop(lowered);
  let srs = measured(&mut phases, "development_srs", || {
    Arc::new(match std::env::var_os("KZG_BENCH_SRS_CACHE") {
      Some(path) => {
        Srs::unsafe_dev_setup_cached(height, b"kzg-prover-bench-v1", path)
          .expect("development SRS cache")
      },
      None => Srs::unsafe_dev_setup(height, b"kzg-prover-bench-v1"),
    })
  });
  let config =
    KzgConfig::new(srs, 2).with_streaming_lookups().with_streaming_quotient();
  let (mut system, mut key) = measured(&mut phases, "fixed_commit", || {
    System::new_without_preprocessed(config, definitions)
  });
  key.preprocessed_data =
    Some(measured(&mut phases, "fixed_checkpoint", || {
      checkpoint("fixed.bin", key.preprocessed_data.take().unwrap())
    })?);
  let shape: Vec<_> = system
        .circuits
        .iter()
        .map(|c| {
            json!({
                "height": c.preprocessed_height, "fixed": c.preprocessed_width,
                "main": c.main_width, "lookup": c.stage_2_width, "quotient": c.quotient_degree(),
                "constraint_count": c.constraint_count(), "lookup_group_size": c.lookup_group_size,
            })
        })
        .collect();
  let main = &system.circuits[0];
  assert_eq!(
    (
      main.main_width,
      main.preprocessed_width,
      main.stage_2_width,
      main.quotient_degree()
    ),
    (3, 15, 4, 2)
  );
  assert_eq!(system.circuits.len(), 2);
  for circuit in &mut system.circuits {
    circuit.preprocessed = None;
  }
  let logs: Vec<_> =
    traces.iter().map(|m| m.height().ilog2() as usize).collect();
  let lookups = traces
    .iter()
    .zip(&system.circuits)
    .map(|(trace, c)| {
      LookupValues::shape_only(
        trace.height(),
        &c.graph.lookups.iter().map(|l| l.args.len()).collect::<Vec<_>>(),
      )
    })
    .collect();
  let (commitment, data) = measured(&mut phases, "main_commit", || {
    let parts: Vec<_> = traces
      .into_iter()
      .map(|m| {
        system
          .config
          .pcs()
          .commit(vec![(
            system.config.pcs().natural_domain_for_degree(m.height()),
            m,
          )])
          .1
      })
      .collect();
    KzgProverData::concatenate(parts)
  });
  let data =
    measured(&mut phases, "main_checkpoint", || checkpoint("main.bin", data))?;
  let count = system.circuits.len();
  let stage = Stage1 {
    active: vec![true; count],
    active_indices: (0..count).collect(),
    log_degrees: logs,
    stage_1_trace_commit: commitment,
    stage_1_trace_data: data,
    lookups,
  };
  let proof = measured(&mut phases, "prove", || {
    system.prove_committed(&key, &refs, stage)
  });
  measured(&mut phases, "verify", || {
    system.verify_multiple_claims(&refs, &proof)
  })
  .map_err(|e| format!("verify: {e:?}"))?;
  let mut wrong = claims.clone();
  wrong[1][3] += Scalar::ONE;
  assert!(
    system
      .verify_multiple_claims(
        &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        &proof
      )
      .is_err()
  );
  let bytes =
    FixedProofCodec::new(&system, &proof.log_degrees)?.encode(&proof)?;
  println!(
    "{}",
    serde_json::to_string(&json!({
        "scope": "synthetic KZG prover workload; not an Init proof", "storage": if disk_dir.is_some() { "disk" } else { "memory" }, "log_rows": log,
        "threads_requested": std::env::var("RAYON_NUM_THREADS").ok(), "shape": shape,
        "phases": phases, "total_seconds": start.elapsed().as_secs_f64(),
        "proof_bytes": bytes.len(), "proof_blake3": blake3::hash(&bytes).to_hex().to_string(),
        "verified": true, "wrong_claim_rejected": true, "development_srs": true,
    }))?
  );
  Ok(())
}
