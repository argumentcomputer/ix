//! Partitioned KZG commitment, proving and verification.
use super::{Result, storage};
use crate::{
  foreign::KzgCircuitExt,
  kzg::{
    KzgCommitment, KzgConfig, Scalar, compact::FixedProofCodec,
    pcs::KzgProverData,
  },
};
use multi_stark::{
  config::ProofConfig,
  lookup::LookupValues,
  plonkish::{MultiStarkCircuit, TraceShards},
  prover::{Proof, Stage1},
  system::{Circuit, ProverKey, System},
  traits::Pcs,
};
use p3_matrix::Matrix;
use std::{
  fs::{self, File},
  io::{BufReader, BufWriter, Write},
  path::Path,
  time::Instant,
};

/// Committed columns own their data, so the circuit and assignment can be
/// released before allocating lookup and quotient working sets.
pub(super) struct Committed {
  system: System<KzgConfig>,
  key: ProverKey<KzgConfig>,
  stage: Stage1<KzgConfig>,
}

pub(super) struct Proved {
  pub system: System<KzgConfig>,
  pub proof: Proof<KzgConfig>,
  pub codec: FixedProofCodec,
  pub bytes: Vec<u8>,
  pub verify_seconds: f64,
}

impl Committed {
  /// Commit one partition at a time. A trusted preprocessing directory holds
  /// only fixed columns and circuit metadata; witness columns stay in memory.
  /// Prefetch overlaps the next witness with the current partition's commits
  /// only when that witness fits within the byte budget.
  #[tracing::instrument(level = "info", skip_all, name = "compression/prepare")]
  pub(super) fn prepare(
    config: KzgConfig,
    traces: &TraceShards<'_, Scalar>,
    preprocessing: Option<&Path>,
    prefetch_bytes: usize,
  ) -> Result<Self> {
    let compiled = traces.compiled();
    let count = compiled.num_circuits();
    let dimensions = (0..count)
      .map(|i| compiled.trace_dimensions(i).ok_or("missing compiled trace"))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    if let Some(directory) = preprocessing {
      fs::create_dir_all(directory)?;
    }
    let mut circuits = Vec::with_capacity(count);
    let mut fixed = Vec::with_capacity(count);
    let mut main = Vec::with_capacity(count);
    let parent = tracing::Span::current();
    let dispatch = tracing::dispatcher::get_default(Clone::clone);
    let generate_witness = |i: usize| -> std::result::Result<_, String> {
      let _span =
        tracing::info_span!(parent: &parent, "compression/trace", circuit = i)
          .entered();
      let started = Instant::now();
      let trace = traces.trace(i).map_err(|error| error.to_string())?;
      if (trace.height(), trace.width()) != dimensions[i] {
        return Err(
          "generated trace dimensions differ from the compiled circuit".into(),
        );
      }
      tracing::info!(
        circuit = i,
        seconds = started.elapsed().as_secs_f64(),
        "KZG witness generated"
      );
      Ok(trace)
    };
    let mut prefetched = None;
    for i in 0..count {
      // Without prefetch, generate fixed columns before the witness so their
      // full evaluation matrices never need to coexist in memory.
      let witness = if prefetch_bytes == 0 {
        None
      } else {
        Some(prefetched.take().unwrap_or_else(|| generate_witness(i))?)
      };
      let prepare = || -> Result<()> {
        let started = Instant::now();
        let (circuit, data) = tracing::info_span!(parent: &parent, "compression/fixed", circuit = i)
          .in_scope(|| fixed_partition(&config, compiled, i, preprocessing))?;
        circuits.push(circuit);
        fixed.push(data);
        tracing::info!(
          circuit = i,
          seconds = started.elapsed().as_secs_f64(),
          "KZG fixed prepared"
        );
        let witness = witness.map_or_else(|| generate_witness(i), Ok)?;
        let started = Instant::now();
        let (_, data) = tracing::info_span!(parent: &parent, "compression/main_commit", circuit = i)
          .in_scope(|| config.pcs().commit(vec![(
            config.pcs().natural_domain_for_degree(dimensions[i].0), witness,
          )]));
        main.push(data);
        tracing::info!(
          circuit = i,
          seconds = started.elapsed().as_secs_f64(),
          "KZG main committed"
        );
        Ok(())
      };
      let can_prefetch =
        dimensions.get(i + 1).is_some_and(|&(height, width)| {
          height
            .checked_mul(width)
            .and_then(|values| values.checked_mul(size_of::<Scalar>()))
            .is_some_and(|bytes| bytes <= prefetch_bytes)
        });
      if can_prefetch {
        let (prepared, next) = p3_maybe_rayon::prelude::join(
          || {
            tracing::dispatcher::with_default(&dispatch, || {
              prepare().map_err(|error| error.to_string())
            })
          },
          || {
            tracing::dispatcher::with_default(&dispatch, || {
              generate_witness(i + 1)
            })
          },
        );
        prepared?;
        prefetched = Some(next);
      } else {
        prepare()?;
      }
    }
    let lookups = circuits
      .iter()
      .zip(&dimensions)
      .map(|(c, &(height, _))| {
        LookupValues::shape_only(
          height,
          &c.graph.lookups.iter().map(|l| l.args.len()).collect::<Vec<_>>(),
        )
      })
      .collect();
    let (fixed_commitment, fixed_data) = KzgProverData::concatenate(fixed);
    let (stage_1_trace_commit, stage_1_trace_data) =
      KzgProverData::concatenate(main);
    Ok(Self {
      system: System {
        config,
        circuits,
        preprocessed_commit: Some(fixed_commitment),
        preprocessed_indices: (0..count).map(Some).collect(),
      },
      key: ProverKey { preprocessed_data: Some(fixed_data) },
      stage: Stage1 {
        active: vec![true; count],
        active_indices: (0..count).collect(),
        log_degrees: dimensions
          .iter()
          .map(|&(height, _)| height.ilog2() as usize)
          .collect(),
        stage_1_trace_commit,
        stage_1_trace_data,
        lookups,
      },
    })
  }

  pub(super) fn prove(self, claims: &[Vec<Scalar>]) -> Result<Proved> {
    let Self { system, key, stage } = self;
    let logs = stage
      .log_degrees
      .iter()
      .map(|&log| u8::try_from(log))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    let codec = FixedProofCodec::new(&system, &logs)?;
    let refs = claims.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let started = Instant::now();
    let proof = tracing::info_span!("compression/prove")
      .in_scope(|| system.prove_committed(&key, &refs, stage));
    tracing::info!(
      seconds = started.elapsed().as_secs_f64(),
      "KZG proof computed"
    );
    let bytes = codec.encode(&proof)?;
    let proof = codec.decode(&bytes)?;
    let started = Instant::now();
    tracing::info_span!("compression/verify")
      .in_scope(|| system.verify_multiple_claims(&refs, &proof))
      .map_err(|error| format!("encoded KZG proof: {error:?}"))?;
    Ok(Proved {
      system,
      proof,
      codec,
      bytes,
      verify_seconds: started.elapsed().as_secs_f64(),
    })
  }
}

/// Commit each fixed partition without allocating a witness.
pub(super) fn setup(
  config: KzgConfig,
  compiled: &MultiStarkCircuit<Scalar>,
) -> Result<System<KzgConfig>> {
  let count = compiled.num_circuits();
  let mut circuits = Vec::with_capacity(count);
  let mut fixed = KzgCommitment(vec![]);
  for i in 0..count {
    let (circuit, data) = fixed_partition(&config, compiled, i, None)?;
    let (commitment, _data) = KzgProverData::concatenate([data]);
    fixed.0.extend(commitment.0);
    circuits.push(circuit);
  }
  Ok(System {
    config,
    circuits,
    preprocessed_commit: Some(fixed),
    preprocessed_indices: (0..count).map(Some).collect(),
  })
}

fn fixed_partition(
  config: &KzgConfig,
  compiled: &MultiStarkCircuit<Scalar>,
  index: usize,
  preprocessing: Option<&Path>,
) -> Result<(Circuit<Scalar>, KzgProverData)> {
  let paths = preprocessing.map(|dir| {
    (
      dir.join(format!("setup-{index}.bin")),
      dir.join(format!("fixed-{index}.bin")),
    )
  });
  if let Some((meta, fixed)) = &paths
    && meta.exists()
    && fixed.exists()
  {
    let (circuit, commitment): (Circuit<Scalar>, KzgCommitment) =
      storage::load(meta)?;
    if compiled.trace_dimensions(index)
      != Some((circuit.preprocessed_height, circuit.main_width))
    {
      return Err(
        "setup checkpoint dimensions differ from the compiled circuit".into(),
      );
    }
    let data = read_checkpoint(fixed)?;
    let (actual, data) = KzgProverData::concatenate([data]);
    if actual != commitment {
      return Err(
        "fixed checkpoint commitment differs from the setup metadata".into(),
      );
    }
    return Ok((circuit, data));
  }
  let definition = compiled
    .kzg_circuit_input(
      index,
      config.pcs().verifier_params().max_trace_len(),
      config.max_quotient_degree(),
    )?
    .ok_or("missing compiled fixed trace")?;
  validate_config(config, std::slice::from_ref(&definition))?;
  let (mut local, key) =
    System::new_without_preprocessed(config.clone(), [definition]);
  let mut circuit = local.circuits.remove(0);
  circuit.preprocessed = None;
  let mut data = key.preprocessed_data.ok_or("missing fixed columns")?;
  if let Some((meta, fixed)) = paths {
    let temp = storage::temporary_path(&fixed);
    let mut file = BufWriter::with_capacity(1 << 20, File::create(&temp)?);
    data.write_checkpoint(&mut file)?;
    file.flush()?;
    drop(file);
    storage::persist(&temp, &fixed)?;
    if !cfg!(feature = "cuda") {
      drop(data);
      data = read_checkpoint(&fixed)?;
    }
    storage::save(
      &meta,
      &(&circuit, local.preprocessed_commit.ok_or("missing fixed commitment")?),
    )?;
  }
  Ok((circuit, data))
}

/// CUDA needs host coefficients; CPU proving can stream them from disk.
fn read_checkpoint(path: &Path) -> Result<KzgProverData> {
  Ok(if cfg!(feature = "cuda") {
    KzgProverData::read_checkpoint(BufReader::with_capacity(
      1 << 20,
      File::open(path)?,
    ))?
  } else {
    KzgProverData::read_checkpoint_file(path)?
  })
}

// System::new asserts these conditions. Check caller-selected parameters
// before committing matrices so an unsupported configuration is an error.
pub(super) fn validate_config<SC: ProofConfig>(
  config: &SC,
  definitions: &[multi_stark::system::CircuitInputs<
    multi_stark::config::Val<SC>,
  >],
) -> Result<()> {
  let params = multi_stark::system::extension_params::<SC>();
  for definition in definitions {
    let graph = definition
      .compile_graph(&params)
      .map_err(|e| format!("compression circuit: {e:?}"))?;
    let degree =
      graph.max_constraint_degree.max(multi_stark::lookup::logup_max_degree(
        &graph,
        definition.lookup_group_size,
      )) as usize;
    let quotient = (degree.max(2) - 1).next_power_of_two();
    if quotient > config.max_quotient_degree() {
      return Err(format!("compression circuit requires quotient degree {quotient}; increase the PCS degree budget").into());
    }
    if let Some(fixed) = &definition.preprocessed {
      let height = fixed.height();
      if !height.is_power_of_two()
        || height.ilog2() as usize > config.max_log_degree()
        || height.ilog2() as usize + quotient.ilog2() as usize
          > config.max_log_quotient_domain()
      {
        return Err("compression trace exceeds the PCS domain".into());
      }
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::{Srs, TranscriptKind};
  use multi_stark::{
    plonkish::CircuitBuilder,
    system::SystemWitness,
    traits::{Algebra, Field},
  };
  use std::sync::Arc;

  #[derive(Clone, Default)]
  struct TraceOutput(Arc<std::sync::Mutex<Vec<u8>>>);

  impl Write for TraceOutput {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
      self.0.lock().unwrap().extend_from_slice(bytes);
      Ok(bytes.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
      Ok(())
    }
  }

  #[test]
  fn partitioned_proving_preserves_bytes_with_prefetch_and_checkpoints()
  -> Result<()> {
    use tracing_subscriber::layer::SubscriberExt;
    let output = TraceOutput::default();
    let subscriber = tracing_subscriber::registry().with(
      tracing_texray::TeXRayLayer::new().streaming().writer(output.clone()),
    );
    tracing::subscriber::set_global_default(subscriber)?;
    let partitions =
      tracing_texray::examine(tracing::info_span!("compression/test"))
        .in_scope(parity_fixture)?;
    let text = String::from_utf8(output.0.lock().unwrap().clone())?;
    for name in
      ["compression/trace", "compression/fixed", "compression/main_commit"]
    {
      assert_eq!(
        text.matches(&format!("[texray] {name}:")).count(),
        10 * partitions,
        "{text}"
      );
    }
    for name in [
      "compression/prove",
      "compression/verify",
      "stark/lookup_construction",
      "stark/quotient",
      "stark/fri_open",
    ] {
      assert!(text.contains(&format!("[texray] {name}:")), "{text}");
    }
    Ok(())
  }

  fn parity_fixture() -> Result<usize> {
    let mut builder = CircuitBuilder::new();
    let table =
      builder.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
    let input = builder.public_input("input");
    for _ in 0..50 {
      builder.lookup(table, &[input]);
    }
    let square = builder.mul(input, input);
    builder.expose_public(square);
    let compiled = builder
      .finish()
      .lower_to_multi_stark_sharded(Scalar::ONE, 32)?
      .merge_table_traces(32)?;
    assert!(compiled.num_circuits() > 2);
    let mut witness = compiled.witness();
    witness.set(input, Scalar::TWO)?;
    let assignment = witness.generate()?;
    let claims = compiled.claims(assignment.public_values())?;
    let refs = claims.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let srs = Arc::new(Srs::unsafe_dev_setup(64, b"partitioned-prover"));
    for kind in [TranscriptKind::Blake3, TranscriptKind::Keccak256] {
      let config = KzgConfig::new(srs.clone(), 2).with_transcript(kind);
      let (reference, key) =
        System::new(config.clone(), compiled.kzg_circuit_inputs(64, 2)?);
      let proof = reference.prove_multiple_claims(
        &key,
        &refs,
        SystemWitness::from_stage_1(compiled.traces(&assignment)?, &reference),
      );
      let expected =
        FixedProofCodec::new(&reference, &proof.log_degrees)?.encode(&proof)?;
      let directory =
        storage::temporary_path(&std::env::temp_dir().join("ix-kzg-prover"));
      let traces = compiled.trace_shards(&assignment)?;
      for (preprocessing, prefetch) in [
        (None, 0),
        (None, 1),
        (None, usize::MAX),
        (Some(directory.as_path()), 0),
        (Some(directory.as_path()), usize::MAX),
      ] {
        let result = Committed::prepare(
          config.clone().with_streaming_lookups().with_streaming_quotient(),
          &traces,
          preprocessing,
          prefetch,
        )?
        .prove(&claims)?;
        assert_eq!(result.bytes, expected);
        assert_eq!(result.system.config.transcript_kind(), kind);
        reference
          .verify_multiple_claims(&refs, &result.proof)
          .map_err(|error| format!("reference verification: {error:?}"))?;
      }
      fs::remove_dir_all(directory)?;
    }
    Ok(compiled.num_circuits())
  }
}
