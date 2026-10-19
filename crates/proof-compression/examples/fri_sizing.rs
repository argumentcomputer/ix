//! Size the first KZG stage's FRI verifier for alternative query counts
//! without a proof: the verifier relation depends only on the key, the
//! verifying key and the FRI parameters, so a saved key can be re-parameterized
//! and counted directly. Arity and cap changes are not supported by the
//! in-circuit verifier and cannot be sized this way.
//!
//! Usage: fri_sizing <saved-fri-dir> [queries,...] [log-height]

use ix_proof_compression::foreign::GoldilocksCircuit;
use ix_proof_compression::fri::{
  DEFAULT_FIELD_RETRIES, Envelope, ImplementationOptions, ProofProfile,
  Statement, StatementSlot, VerifierKey, VerifierLimits, VerifierPlan,
};
use multi_stark::config::StarkGenericConfig;
use multi_stark::system::{Circuit, System};
use multi_stark::traits::Field;
use multi_stark::types::{
  CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val,
};
use p3_field::PrimeField64;
use std::{fs, path::Path, time::Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn decode_claims(bytes: &[u8]) -> Result<Vec<Vec<Val>>> {
  let (words, remainder) = bytes.as_chunks::<8>();
  if !remainder.is_empty() {
    return Err("unaligned claims".into());
  }
  let mut words = words.iter().map(|w| u64::from_le_bytes(*w));
  let n = words.next().ok_or("missing claims count")?;
  let mut claims = Vec::new();
  for _ in 0..n {
    let len = words.next().ok_or("missing claim length")?;
    let mut claim = Vec::new();
    for _ in 0..len {
      let v = words.next().ok_or("missing claim value")?;
      if v >= Val::ORDER_U64 {
        return Err("noncanonical claim".into());
      }
      claim.push(Val::from_u64(v));
    }
    claims.push(claim);
  }
  Ok(claims)
}

/// Shape overrides for cost attribution: `FRI_SIZING_MAX_LOG` caps every
/// trace height, `FRI_SIZING_DROP` lists circuit indices to omit, and
/// `FRI_SIZING_SET` assigns `index:log_height:main_width` per circuit.
fn with_queries(key: &VerifierKey, queries: usize) -> VerifierKey {
  let system = key.system();
  let fri = system.config.fri_parameters();
  let max_log: Option<u32> = std::env::var("FRI_SIZING_MAX_LOG")
    .ok()
    .filter(|v| !v.is_empty())
    .map(|v| v.parse().unwrap());
  let drop: Vec<usize> = std::env::var("FRI_SIZING_DROP")
    .ok()
    .filter(|v| !v.is_empty())
    .map(|v| v.split(',').map(|i| i.parse().unwrap()).collect())
    .unwrap_or_default();
  let set: std::collections::HashMap<usize, (u32, usize)> =
    std::env::var("FRI_SIZING_SET")
      .ok()
      .filter(|v| !v.is_empty())
      .map(|v| {
        v.split(',')
          .map(|item| {
            let parts: Vec<usize> =
              item.split(':').map(|x| x.parse().unwrap()).collect();
            (parts[0], (u32::try_from(parts[1]).unwrap(), parts[2]))
          })
          .collect()
      })
      .unwrap_or_default();
  let circuits: Vec<_> = system
    .circuits
    .iter()
    .enumerate()
    .filter(|(i, _)| !drop.contains(i))
    .map(|(i, c)| Circuit {
      graph: c.graph.clone(),
      main_width: set.get(&i).map_or(c.main_width, |&(_, w)| w),
      preprocessed: None,
      preprocessed_width: c.preprocessed_width,
      preprocessed_height: set.get(&i).map_or_else(
        || {
          max_log.map_or(c.preprocessed_height, |m| {
            c.preprocessed_height.min(1 << m)
          })
        },
        |&(log, _)| 1 << log,
      ),
      num_lookups: c.num_lookups,
      stage_2_width: c.stage_2_width,
      num_publics: c.num_publics,
      lookup_group_size: c.lookup_group_size,
      constraint_count: c.constraint_count,
      max_constraint_degree: c.max_constraint_degree,
    })
    .collect();
  VerifierKey::new(System {
    config: GoldilocksBlake3Config::new(
      CommitmentParameters {
        log_blowup: system.config.log_blowup(),
        cap_height: system.config.cap_height(),
      },
      FriParameters { num_queries: queries, ..fri },
    ),
    preprocessed_indices: (0..circuits.len()).map(Some).collect(),
    circuits,
    preprocessed_commit: system.preprocessed_commit.clone(),
  })
}

fn main() -> Result<()> {
  let args: Vec<String> = std::env::args().collect();
  let dir = Path::new(
    args
      .get(1)
      .ok_or("usage: fri_sizing <saved-fri-dir> [queries,...] [log-height]")?,
  );
  let queries: Vec<usize> = args
    .get(2)
    .map(|s| s.split(',').map(str::parse).collect())
    .transpose()?
    .unwrap_or_else(|| vec![1, 2, 40, 60, 80, 100]);
  let log_height: u32 =
    args.get(3).map(|s| s.parse()).transpose()?.unwrap_or(24);
  let key = VerifierKey::from_bytes(&fs::read(dir.join("outer-vk.bin"))?)?;
  let claims = decode_claims(&fs::read(dir.join("outer-claims.bin"))?)?;
  // The saved statement exposes 18 public words at rows 1..=18, column 3;
  // every other claim value is a circuit constant.
  let schema = Statement {
    claims: claims
      .iter()
      .enumerate()
      .map(|(row, values)| {
        values
          .iter()
          .enumerate()
          .map(|(col, &v)| {
            if (1..=18).contains(&row) && col == 3 {
              StatementSlot::Public
            } else {
              StatementSlot::Constant(v)
            }
          })
          .collect()
      })
      .collect(),
    messages: vec![],
  };
  let base = key.system().config.fri_parameters();
  eprintln!(
    "key: {} circuits, log_blowup {}, queries {}, query_pow {}, arity {}",
    key.system().circuits.len(),
    key.system().config.log_blowup(),
    base.num_queries,
    base.query_proof_of_work_bits,
    base.max_log_arity
  );
  for &q in &queries {
    let start = Instant::now();
    let key = with_queries(&key, q);
    let vk = ProofProfile {
      envelope: Envelope::Ordinary,
      active: vec![true; key.system().circuits.len()],
      log_degrees: key
        .system()
        .circuits
        .iter()
        .map(|c| u8::try_from(c.preprocessed_height.ilog2()).unwrap())
        .collect(),
      claim_lengths: claims.iter().map(Vec::len).collect(),
      message_lengths: vec![],
      max_field_retries: DEFAULT_FIELD_RETRIES,
    };
    let plan = VerifierPlan::validate(&key, vk, VerifierLimits::default())?;
    let resources = plan.resources();
    let (circuit, _inputs) =
      plan.build(schema.clone(), ImplementationOptions::default())?;
    let source = circuit.stats();
    let layout = circuit.multi_stark_layout_with_max_height(1 << log_height)?;
    let scalar = GoldilocksCircuit::estimate(&circuit);
    let scalar_rows = scalar.gates + scalar.lookups + scalar.publics + 1;
    // `FRI_SIZING_LOWER` materializes the translated circuit and lays it
    // out as the first stage does, which costs tens of GiB at full size.
    let scalar_layout = if std::env::var_os("FRI_SIZING_LOWER").is_some() {
      let translated = GoldilocksCircuit::new_preallocated(&circuit);
      let layout = translated
        .circuit
        .multi_stark_layout_with_max_height(1 << log_height)?;
      Some(serde_json::json!({
        "used_rows": layout.used_rows,
        "main_heights": layout.main_heights,
        "main_width": layout.main_width,
        "preprocessed_width": layout.preprocessed_width,
        "table_heights": layout.table_heights,
        "custom_traces": layout.custom_traces,
        "advice_cells": layout.advice_cells,
        "preprocessed_cells": layout.preprocessed_cells,
        "trace_field_bytes": layout.trace_field_bytes,
      }))
    } else {
      None
    };
    let report = serde_json::json!({
      "queries": q,
      "proof_values": resources.proof_values,
      "source": {
        "gates": source.gates, "lookups": source.lookups, "values": source.values,
        "hash_calls": source.hash_calls, "hash_compressions": source.hash_compressions,
        "tables": source.tables,
      },
      "source_layout": {
        "used_rows": layout.used_rows,
        "main_heights": layout.main_heights,
        "main_width": layout.main_width,
        "table_heights": layout.table_heights,
        "custom_traces": layout.custom_traces,
      },
      "scalar": {
        "gates": scalar.gates, "lookups": scalar.lookups, "values": scalar.values,
        "hash_calls": scalar.hash_calls, "hash_compressions": scalar.hash_compressions,
        "generic_rows_without_hash_bridge": scalar_rows,
        "generic_partitions_lower_bound": scalar_rows.div_ceil(1 << log_height),
      },
      "scalar_layout": scalar_layout,
      "elapsed_seconds": start.elapsed().as_secs_f64(),
    });
    println!("{report}");
  }
  Ok(())
}
