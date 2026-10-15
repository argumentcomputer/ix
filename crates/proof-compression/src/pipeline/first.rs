//! KZG compression of the saved recursive FRI proof.
//!
//! `run` stages, proves and verifies in one process: the translated traces
//! feed commitment directly, and the loaded SRS, fixed preprocessing and
//! device residency are shared between the two halves. The stage writes its
//! proof and the metadata the recursive stage verifies it with, plus the
//! fixed-preprocessing checkpoints that populate the cross-run cache. `serve`
//! keeps a prepared worker resident across requests.
use crate::foreign::{GoldilocksCircuit, GoldilocksInputs, KzgCircuitExt};
use crate::fri::{
  ImplementationOptions, ProofEnvelope, Statement, VerifierInputs,
  VerifierLimits, VerifierPlan,
};
use crate::kzg::compact::FixedProofCodec;
use crate::kzg::pcs::{KzgPcs, KzgProverData};
use crate::kzg::{KzgCommitment, KzgConfig, Scalar};
use multi_stark::config::ProofConfig;
use multi_stark::lookup::LookupValues;
use multi_stark::plonkish::{
  Assignment, Circuit as PlonkishCircuit, MultiStarkCircuit, TraceShards,
};
use multi_stark::prover::Stage1;
use multi_stark::system::{Circuit, ProverKey, System};
use multi_stark::traits::{Algebra, Field, Pcs};
use multi_stark::types::Val;
use p3_field::PrimeField64;
use p3_matrix::Matrix;
use std::{
  fs::{self, File},
  io::{BufRead, BufReader, BufWriter, Write},
  path::Path,
  time::Instant,
};

#[cfg(test)]
use super::init_claim;
use super::init_fri;
use super::support::{
  kzg_fixed_cache::FixedCache,
  kzg_setup::{FIRST_SEED, SetupClass, SetupSource},
  kzg_storage as storage, kzg_worker_protocol as worker_protocol,
};

const TABLE_HEIGHT: usize = 1 << 22;
const DEFAULT_PREFETCH_GIB: usize = 32;
/// Partitions of the supported Init profile: ten carry the public words and
/// the rest are tables, which only exist above eleven partitions.
pub(super) const MIN_PARTITIONS: usize = 11;

/// The claims a first-stage proof of `count` partitions must expose, as the
/// lowering derives them: the statement words, one activation anchor per table
/// partition and the six fixed namespace anchors.
pub(super) fn expected_claims(
  count: usize,
  statement: &super::statement::Statement,
) -> Vec<Vec<Scalar>> {
  let namespace = Scalar::from_u8(93);
  let mut expected: Vec<_> = std::iter::once(0)
    .chain(statement.iter().copied())
    .enumerate()
    .map(|(i, word)| {
      vec![
        namespace,
        Scalar::ONE,
        Scalar::from_usize(i),
        Scalar::from_u64(word),
      ]
    })
    .collect();
  if count > MIN_PARTITIONS {
    expected.extend(
      (0..count - 10)
        .map(|i| vec![namespace, Scalar::from_u8(3), Scalar::from_usize(i)]),
    );
  }
  expected.extend((0..6).map(|i| {
    vec![
      namespace,
      Scalar::from_u8(4),
      Scalar::from_u8(3),
      Scalar::from_usize(i),
    ]
  }));
  expected
}

/// Runtime choices of one invocation, parsed from the command line.
#[derive(Clone, Copy)]
struct Options {
  /// Bytes of the next partition's witness that may be generated while the
  /// current one is committed; zero disables the overlap.
  prefetch_bytes: usize,
}

fn init_tracing() {
  let _ = tracing_subscriber::fmt()
    .with_writer(std::io::stderr)
    .with_max_level(tracing::Level::INFO)
    .try_init();
}

fn prefetch_bytes_from_env() -> storage::Result<usize> {
  let gib: usize = match std::env::var("IX_KZG_PREFETCH_GIB") {
    Ok(value) => value.parse()?,
    Err(std::env::VarError::NotPresent) => DEFAULT_PREFETCH_GIB,
    Err(error) => return Err(error.into()),
  };
  gib.checked_mul(1 << 30).ok_or_else(|| "prefetch budget overflow".into())
}

fn log_height_arg(arg: Option<&String>) -> storage::Result<usize> {
  let log_height = arg.map(|s| s.parse::<usize>()).transpose()?.unwrap_or(24);
  if !(24..=28).contains(&log_height) {
    return Err("log-height must be 24..28".into());
  }
  Ok(log_height)
}

pub(super) fn run(args: &[String]) -> storage::Result<()> {
  const USAGE: &str = "usage: ix-compression-worker kzg run <saved-fri-dir> <output-dir> [log-height: 24..28] | serve <new-response-jsonl-path> [log-height]";
  let args = crate::pipeline::setup::take_development_flag(args);
  let Some(command) = args.first() else {
    return Err(USAGE.into());
  };
  let rest = &args[1..];
  match command.as_str() {
    "run" if (2..=3).contains(&rest.len()) => {
      let log_height = log_height_arg(rest.get(2))?;
      init_tracing();
      stage_and_prove(
        Path::new(&rest[0]),
        Path::new(&rest[1]),
        log_height,
        Options { prefetch_bytes: prefetch_bytes_from_env()? },
      )
    },
    "serve" if (1..=2).contains(&rest.len()) => {
      let log_height = log_height_arg(rest.get(1))?;
      init_tracing();
      serve(
        Path::new(&rest[0]),
        log_height,
        Options { prefetch_bytes: prefetch_bytes_from_env()? },
      )
    },
    _ => Err(USAGE.into()),
  }
}

/// The source verifier circuit translated and lowered once, reusable across
/// proofs of the same key and profile.
struct Frontend {
  source: PlonkishCircuit<Val>,
  scalar_inputs: GoldilocksInputs,
  compiled: MultiStarkCircuit<Scalar>,
}

impl Frontend {
  fn compile(
    source: PlonkishCircuit<Val>,
    max_main_height: usize,
    max_table_height: usize,
  ) -> storage::Result<Self> {
    let translated = GoldilocksCircuit::new_preallocated(&source);
    let compiled = translated
      .circuit
      .lower_to_multi_stark_sharded(Scalar::from_u8(93), max_main_height)?
      .merge_table_traces(max_table_height)?;
    Ok(Self { source, scalar_inputs: translated.inputs, compiled })
  }

  fn assign(
    &self,
    source: &Assignment<Val>,
  ) -> storage::Result<Assignment<Scalar>> {
    let mut witness = self.compiled.witness();
    self.scalar_inputs.assign(source, &mut witness)?;
    Ok(witness.generate()?)
  }

  /// The largest partition height, which fixes the public degree.
  fn height(&self) -> storage::Result<usize> {
    max_height(&self.compiled)
  }
}

fn max_height(compiled: &MultiStarkCircuit<Scalar>) -> storage::Result<usize> {
  (0..compiled.num_circuits())
    .map(|i| compiled.trace_dimensions(i).map(|(height, _)| height))
    .max()
    .flatten()
    .ok_or_else(|| "empty compiled circuit".into())
}

fn public_scalars(public: &[Val; 18]) -> Vec<Scalar> {
  public.iter().map(|v| Scalar::from_u64(v.as_canonical_u64())).collect()
}

fn stage_and_prove(
  fri: &Path,
  out: &Path,
  log_height: usize,
  options: Options,
) -> storage::Result<()> {
  let max_height = 1usize << log_height;
  fs::create_dir_all(out)?;
  let fixture = init_fri::load(fri)?;
  let plan = VerifierPlan::validate(
    &fixture.key,
    fixture.profile,
    VerifierLimits::default(),
  )?;
  let plan_id = plan.identity(&fixture.schema)?;
  fs::write(out.join("plan-id.bin"), plan_id)?;
  fs::write(out.join("inner-vk.bin"), fixture.key.to_bytes()?)?;
  let start = Instant::now();
  let (source, inputs) = plan
    .build(fixture.schema, ImplementationOptions { compact_blake3: true })?;
  println!("Source circuit: {:?}; {:?}", start.elapsed(), source.stats());
  let expanded = plan.expand_witness(ProofEnvelope::Ordinary {
    proof: &fixture.proof,
    claims: &fixture.claims,
  })?;
  let mut witness = source.witness();
  inputs.assign_statement(
    &mut witness,
    &Statement { claims: fixture.claims, messages: vec![] },
  )?;
  expanded.assign_proof(&mut witness, &inputs)?;
  let assignment = witness.generate()?;
  assert_eq!(assignment.public_values(), fixture.public);
  drop(expanded);
  drop(inputs);
  println!("Source witness satisfied: {:?}", start.elapsed());
  let frontend = Frontend::compile(source, max_height, TABLE_HEIGHT)?;
  println!(
    "Scalar translation and lowering of {} circuits: {:?}; {:?}",
    frontend.compiled.num_circuits(),
    start.elapsed(),
    frontend.compiled.circuit().stats()
  );
  let scalar = frontend.assign(&assignment)?;
  let public = public_scalars(&fixture.public);
  assert_eq!(scalar.public_values(), public);
  drop(assignment);
  println!("Scalar witness satisfied: {:?}", start.elapsed());
  let height = frontend.height()?;
  let setup = SetupSource::for_stage(
    FIRST_SEED,
    height,
    crate::pipeline::setup::development_permitted(),
  )?;
  setup.bind_stage(out, height, 2)?;
  let setup_id = setup.identity(height, 2)?;
  let cache = FixedCache::for_stage(out, &[plan_id, setup_id].concat())?;
  let cached = cache.restore(out)?;
  let shards = frontend.compiled.trace_shards(&scalar)?;
  let manifest = storage::Manifest::for_compiled(
    &frontend.compiled,
    frontend.compiled.claims(&public)?,
    cached.as_ref(),
  )?;
  storage::save(&out.join("manifest.bin"), &manifest)?;
  println!("Generating fixed and witness traces directly into commitment");
  prove(out, &shards, &mut None, &cache, options)?;
  println!("RUN COMPLETE: {:?}", start.elapsed());
  Ok(())
}

/// Prover state retained across proofs of one profile in a worker process.
struct LoadedProver {
  system: System<KzgConfig>,
  key: ProverKey<KzgConfig>,
  codec: FixedProofCodec,
  widths: Vec<usize>,
  heights: Vec<usize>,
  logs: Vec<u8>,
  plan_id: [u8; 32],
  setup_id: [u8; 32],
  setup_bytes: Vec<Vec<u8>>,
}

pub(super) fn write_checkpoint(
  path: &Path,
  data: &KzgProverData,
) -> storage::Result<()> {
  let temp = storage::temporary_path(path);
  let mut file = BufWriter::with_capacity(1 << 20, File::create(&temp)?);
  data.write_checkpoint(&mut file)?;
  file.flush()?;
  drop(file);
  storage::persist(&temp, path)?;
  Ok(())
}

/// Load a fixed checkpoint. The device paths need host coefficients, so a
/// CUDA build keeps it resident; a CPU build serves columns from the file.
pub(super) fn read_checkpoint(path: &Path) -> storage::Result<KzgProverData> {
  Ok(if cfg!(feature = "cuda") {
    KzgProverData::read_checkpoint(BufReader::with_capacity(
      1 << 20,
      File::open(path)?,
    ))?
  } else {
    KzgProverData::read_checkpoint_file(path)?
  })
}

/// Commit the fixed and witness traces of every partition, prove them
/// together, verify the proof and write it with its packet. Fixed
/// preprocessing comes from the cache when it holds this profile and is
/// published to it after the proof verifies.
#[allow(clippy::too_many_lines)]
fn prove(
  dir: &Path,
  traces: &TraceShards<'_, Scalar>,
  retained: &mut Option<LoadedProver>,
  cache: &FixedCache,
  options: Options,
) -> storage::Result<()> {
  let cold = retained.is_none();
  let manifest: storage::Manifest = storage::load(&dir.join("manifest.bin"))?;
  let count = manifest.heights.len();
  if count < MIN_PARTITIONS
    || manifest.widths.len() != count
    || manifest.widths.contains(&0)
  {
    return Err("unexpected trace layout".into());
  }
  let height = *manifest.heights.iter().max().ok_or("empty manifest")?;
  if height > 1 << 28
    || manifest.heights.iter().any(|h| *h < 2 || !h.is_power_of_two())
  {
    return Err("unsupported trace height".into());
  }
  let compiled = traces.compiled();
  if compiled.num_circuits() != count
    || (0..count).any(|i| {
      compiled.trace_dimensions(i)
        != Some((manifest.heights[i], manifest.widths[i]))
    })
  {
    return Err(
      "generated trace dimensions differ from the staged manifest".into(),
    );
  }
  let statement = super::statement::from_rows(&manifest.claims)?;
  if manifest.claims != expected_claims(count, &statement) {
    return Err(
      "staged claims differ from the statement and activation anchors".into(),
    );
  }
  let setup = SetupSource::for_stage(
    FIRST_SEED,
    height,
    crate::pipeline::setup::development_permitted(),
  )?;
  setup.check_binding(dir, height, 2)?;
  let setup_id = setup.identity(height, 2)?;
  let plan_id: [u8; 32] = fs::read(dir.join("plan-id.bin"))?
    .try_into()
    .map_err(|bytes: Vec<u8>| {
      format!("invalid verifier plan identity: {} bytes", bytes.len())
    })?;
  if let Some(loaded) = retained
    && (loaded.plan_id != plan_id
      || loaded.setup_id != setup_id
      || loaded.widths != manifest.widths
      || loaded.heights != manifest.heights)
  {
    return Err("request differs from the loaded prover profile".into());
  }
  let out = dir.join("kzg");
  fs::create_dir_all(&out)?;
  fs::write(out.join("SECURITY.txt"), setup.security_description())?;
  let start = Instant::now();
  let config = if let Some(loaded) = retained {
    for (i, bytes) in loaded.setup_bytes.iter().enumerate() {
      fs::write(out.join(format!("setup-{i}.bin")), bytes)?;
    }
    println!("Reusing loaded SRS, fixed coefficients and compiled prover");
    loaded.system.config.clone()
  } else {
    let config = setup
      .config(height, 2, false)?
      .with_streaming_lookups()
      .with_streaming_quotient();
    println!("KZG parameters ready: {:?}", start.elapsed());
    config
  };
  println!("Partition prefetch budget: {} GiB", options.prefetch_bytes >> 30);
  let mut circuits = Vec::new();
  let mut fixed_parts = Vec::new();
  let mut main_parts = Vec::new();
  let mut commits = Vec::new();
  let mut setup_bytes = Vec::new();
  let generate_witness = |i: usize| -> Result<_, String> {
    let trace_started = Instant::now();
    let trace = traces.trace(i).map_err(|error| error.to_string())?;
    if trace.width() != manifest.widths[i]
      || trace.height() != manifest.heights[i]
    {
      return Err(
        "generated trace dimensions differ from the staged manifest".into(),
      );
    }
    println!(
      "KZG fresh trace generated circuit={i} seconds={:.9} overlap_possible=true",
      trace_started.elapsed().as_secs_f64()
    );
    Ok(trace)
  };
  let mut prefetched = None;
  for i in 0..count {
    let witness = prefetched.take().unwrap_or_else(|| generate_witness(i))?;
    let prepare = || -> storage::Result<()> {
      let meta = out.join(format!("setup-{i}.bin"));
      let fixed_path = out.join(format!("fixed-{i}.bin"));
      if cold {
        let fixed_started = Instant::now();
        let from_cache = meta.exists() && fixed_path.exists();
        let (circuit, commitment): (Circuit<Scalar>, KzgCommitment) =
          if from_cache {
            fixed_parts.push(read_checkpoint(&fixed_path)?);
            storage::load(&meta)?
          } else {
            let load_started = Instant::now();
            let definition = compiled
              .kzg_circuit_input(i, height, 2)?
              .ok_or("missing compiled fixed trace")?;
            let fixed = definition
              .preprocessed
              .as_ref()
              .ok_or("missing preprocessing")?;
            if definition.main_width != manifest.widths[i]
              || fixed.height() != manifest.heights[i]
            {
              return Err(
                "fixed trace dimensions differ from the staged manifest".into(),
              );
            }
            println!(
              "KZG fixed trace generated circuit={i} seconds={:.9} overlap_possible=true",
              load_started.elapsed().as_secs_f64()
            );
            let commit_started = Instant::now();
            let (mut local, key) =
              System::new_without_preprocessed(config.clone(), [definition]);
            println!(
              "KZG fixed committed circuit={i} seconds={:.9} overlap_possible=true",
              commit_started.elapsed().as_secs_f64()
            );
            let mut circuit = local.circuits.remove(0);
            circuit.preprocessed = None;
            let data = key.preprocessed_data.unwrap();
            write_checkpoint(&fixed_path, &data)?;
            fixed_parts.push(if cfg!(feature = "cuda") {
              data
            } else {
              drop(data);
              read_checkpoint(&fixed_path)?
            });
            let pair = (circuit, local.preprocessed_commit.unwrap());
            storage::save(&meta, &pair)?;
            pair
          };
        if circuit.main_width != manifest.widths[i]
          || circuit.preprocessed_height != manifest.heights[i]
        {
          return Err(
            "setup checkpoint dimensions differ from the staged manifest"
              .into(),
          );
        }
        circuits.push(circuit);
        commits.push(commitment);
        setup_bytes.push(fs::read(&meta)?);
        println!(
          "KZG fixed prepared circuit={i} seconds={:.9} source={} overlap_possible=true",
          fixed_started.elapsed().as_secs_f64(),
          if from_cache { "cache" } else { "generated" },
        );
      }
      let commit_started = Instant::now();
      let (_, data) = config.pcs().commit(vec![(
        config.pcs().natural_domain_for_degree(manifest.heights[i]),
        witness,
      )]);
      println!(
        "KZG main committed circuit={i} seconds={:.9} overlap_possible=true",
        commit_started.elapsed().as_secs_f64()
      );
      main_parts.push(data);
      println!("Prepared {i}/{count}: {:?}", start.elapsed());
      Ok(())
    };
    let can_prefetch = options.prefetch_bytes > 0
      && i + 1 < count
      && manifest.widths[i + 1]
        .checked_mul(manifest.heights[i + 1])
        .and_then(|values| values.checked_mul(size_of::<Scalar>()))
        .is_some_and(|bytes| bytes <= options.prefetch_bytes);
    if can_prefetch {
      let (prepared, next) = p3_maybe_rayon::prelude::join(
        || prepare().map_err(|error| error.to_string()),
        || generate_witness(i + 1),
      );
      prepared?;
      prefetched = Some(next);
    } else {
      prepare()?;
    }
  }
  if cold {
    let mut commitment = KzgCommitment(vec![]);
    for mut c in commits {
      commitment.0.append(&mut c.0);
    }
    let system = System {
      config,
      circuits,
      preprocessed_commit: Some(commitment),
      preprocessed_indices: (0..count).map(Some).collect(),
    };
    let (commitment, data) = KzgProverData::concatenate(fixed_parts);
    assert_eq!(Some(commitment), system.preprocessed_commit);
    let key = ProverKey { preprocessed_data: Some(data) };
    let logs: Vec<_> = manifest
      .heights
      .iter()
      .map(|h| u8::try_from(h.ilog2()).unwrap())
      .collect();
    let codec = FixedProofCodec::new(&system, &logs)?;
    *retained = Some(LoadedProver {
      system,
      key,
      codec,
      widths: manifest.widths.clone(),
      heights: manifest.heights.clone(),
      logs,
      plan_id,
      setup_id,
      setup_bytes,
    });
  }
  let loaded = retained.as_ref().unwrap();
  let system = &loaded.system;
  let codec = &loaded.codec;
  let logs = &loaded.logs;
  let refs: Vec<_> = manifest.claims.iter().map(Vec::as_slice).collect();
  let (main_commitment, main) = KzgProverData::concatenate(main_parts);
  let lookups = system
    .circuits
    .iter()
    .zip(&manifest.heights)
    .map(|(c, &h)| {
      LookupValues::shape_only(
        h,
        &c.graph.lookups.iter().map(|l| l.args.len()).collect::<Vec<_>>(),
      )
    })
    .collect();
  let stage = Stage1 {
    active: vec![true; count],
    active_indices: (0..count).collect(),
    log_degrees: logs.iter().map(|&l| usize::from(l)).collect(),
    stage_1_trace_commit: main_commitment,
    stage_1_trace_data: main,
    lookups,
  };
  println!("Proving all {count} partitions together: {:?}", start.elapsed());
  let proof_started = Instant::now();
  let proof = system.prove_committed(&loaded.key, &refs, stage);
  println!(
    "KZG proof computed seconds={:.9}",
    proof_started.elapsed().as_secs_f64()
  );
  let bytes = codec.encode(&proof)?;
  let proof = codec.decode(&bytes)?;
  let verify_start = Instant::now();
  system
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("encoded proof: {e:?}"))?;
  let verify_seconds = verify_start.elapsed().as_secs_f64();
  // The label is part of every published profile id and predates the
  // Filecoin setup; the setup class is bound through the transcript seed.
  let mut profile = blake3::Hasher::new();
  profile.update(b"init-fri-kzg-ordinary-v1/development-srs/quotient2");
  profile.update(system.config.transcript_seed());
  profile.update(&fs::read(dir.join("plan-id.bin"))?);
  profile.update(&fs::read(dir.join("manifest.bin"))?);
  for i in 0..count {
    profile.update(&fs::read(out.join(format!("setup-{i}.bin")))?);
  }
  let profile = *profile.finalize().as_bytes();
  let mut packet = profile.to_vec();
  for claim in &manifest.claims[1..19] {
    packet.extend_from_slice(&claim[3].canonical_limbs_le()[0].to_le_bytes());
  }
  packet.extend_from_slice(&bytes);
  storage::write_atomic(&out.join("proof.compact.bin"), &bytes)?;
  storage::write_atomic(&out.join("profile-id.bin"), &profile)?;
  storage::write_atomic(&out.join("packet.bin"), &packet)?;
  let development = setup.class() == SetupClass::Development;
  let public_setup = system.config.pcs().public_setup();
  let evidence = serde_json::json!({
    "proof_bytes": bytes.len(),
    "packet_bytes": packet.len(),
    "trace_heights": manifest.heights,
    "verify_seconds": verify_seconds,
    "total_seconds": start.elapsed().as_secs_f64(),
    "native_verification_passed": true,
    "development_srs": development,
    "known_trapdoor": development,
    "setup": setup.class().label(),
    "setup_id": blake3::Hash::from_bytes(setup_id).to_string(),
    "public_setup_id": blake3::Hash::from_bytes(public_setup.id).to_string(),
    "public_max_degree": public_setup.max_degree,
  });
  fs::write(out.join("prove-report.json"), format!("{evidence}\n"))?;
  if cold {
    cache.publish(dir)?;
  }
  println!(
    "VERIFIED: proof_bytes={} packet_bytes={} verify_seconds={verify_seconds} total_seconds={} development_srs={development}",
    bytes.len(),
    packet.len(),
    start.elapsed().as_secs_f64()
  );
  Ok(())
}

/// A prepared frontend serving several proofs of one verifier key.
struct Worker<'a> {
  plan: VerifierPlan<'a>,
  plan_id: [u8; 32],
  inputs: VerifierInputs,
  frontend: Frontend,
  key_bytes: Vec<u8>,
  loaded: Option<LoadedProver>,
  options: Options,
}

impl<'a> Worker<'a> {
  fn compile(
    fixture: &'a init_fri::Fixture,
    max_main_height: usize,
    max_table_height: usize,
    options: Options,
  ) -> storage::Result<Self> {
    let plan = VerifierPlan::validate(
      &fixture.key,
      fixture.profile.clone(),
      VerifierLimits::default(),
    )?;
    let plan_id = plan.identity(&fixture.schema)?;
    let (source, inputs) = plan.build(
      fixture.schema.clone(),
      ImplementationOptions { compact_blake3: true },
    )?;
    let frontend =
      Frontend::compile(source, max_main_height, max_table_height)?;
    Ok(Self {
      plan,
      plan_id,
      inputs,
      frontend,
      key_bytes: fixture.key.to_bytes()?,
      loaded: None,
      options,
    })
  }

  fn prove(
    &mut self,
    fixture: &init_fri::Fixture,
    output: &Path,
    expected: &[u64; 18],
  ) -> storage::Result<()> {
    if fixture.public.map(|value| value.as_canonical_u64()) != *expected {
      return Err(
        "request differs from the independently expected statement".into(),
      );
    }
    let candidate = VerifierPlan::validate(
      &fixture.key,
      fixture.profile.clone(),
      VerifierLimits::default(),
    )?;
    if candidate.identity(&fixture.schema)? != self.plan_id {
      return Err(
        "request uses a different verifier key, profile or constant statement"
          .into(),
      );
    }
    worker_protocol::ensure_empty_output(output)?;
    fs::create_dir_all(output)?;
    fs::write(output.join("plan-id.bin"), self.plan_id)?;
    fs::write(output.join("inner-vk.bin"), &self.key_bytes)?;
    let expanded = self.plan.expand_witness(ProofEnvelope::Ordinary {
      proof: &fixture.proof,
      claims: &fixture.claims,
    })?;
    let mut witness = self.frontend.source.witness();
    self.inputs.assign_statement(
      &mut witness,
      &Statement { claims: fixture.claims.clone(), messages: vec![] },
    )?;
    expanded.assign_proof(&mut witness, &self.inputs)?;
    let source = witness.generate()?;
    if source.public_values() != fixture.public {
      return Err(
        "source witness public values differ from the expected statement"
          .into(),
      );
    }
    drop(expanded);
    let assignment = self.frontend.assign(&source)?;
    drop(source);
    let public = public_scalars(&fixture.public);
    if assignment.public_values() != public {
      return Err(
        "scalar witness public values differ from the expected statement"
          .into(),
      );
    }
    let height = self.frontend.height()?;
    let setup = SetupSource::for_stage(
      FIRST_SEED,
      height,
      crate::pipeline::setup::development_permitted(),
    )?;
    setup.bind_stage(output, height, 2)?;
    let setup_id = setup.identity(height, 2)?;
    let claims = self.frontend.compiled.claims(&public)?;
    let cache =
      FixedCache::for_stage(output, &[self.plan_id, setup_id].concat())?;
    let manifest = if let Some(loaded) = &self.loaded {
      storage::Manifest {
        widths: loaded.widths.clone(),
        heights: loaded.heights.clone(),
        claims,
      }
    } else {
      let cached = cache.restore(output)?;
      storage::Manifest::for_compiled(
        &self.frontend.compiled,
        claims,
        cached.as_ref(),
      )?
    };
    storage::save(&output.join("manifest.bin"), &manifest)?;
    let traces = self.frontend.compiled.trace_shards(&assignment)?;
    prove(output, &traces, &mut self.loaded, &cache, self.options)
  }

  fn quiesce(&mut self) -> storage::Result<serde_json::Value> {
    if let Some(data) = self
      .loaded
      .as_mut()
      .and_then(|loaded| loaded.key.preprocessed_data.as_mut())
    {
      data.release_device_residency();
    }
    Ok(serde_json::to_value(KzgPcs::release_idle_device_memory())?)
  }
}

/// The statement a request expects, from a claims file in the root stage's
/// layout: one claim of 18 little-endian words.
fn expected_words_from_path(path: &Path) -> storage::Result<[u64; 18]> {
  super::statement::from_claims_bytes(&fs::read(path)?)
}

fn serve(
  path: &Path,
  log_height: usize,
  options: Options,
) -> storage::Result<()> {
  let mut protocol =
    worker_protocol::Protocol::open(path, super::WORKER_EXECUTABLE)?;
  serve_requests(
    &mut protocol,
    1 << log_height,
    TABLE_HEIGHT,
    options,
    |request| init_fri::load(&request.input),
  )
}

fn serve_requests<R: BufRead>(
  protocol: &mut worker_protocol::Protocol<R>,
  max_main_height: usize,
  max_table_height: usize,
  options: Options,
  mut load: impl FnMut(
    &worker_protocol::Request,
  ) -> storage::Result<init_fri::Fixture>,
) -> storage::Result<()> {
  let mut current = None;
  let result = (|| -> storage::Result<()> {
    let Some(request) = protocol.next_request()? else {
      return Ok(());
    };
    current = Some(request.id.clone());
    let started = Instant::now();
    worker_protocol::ensure_empty_output(&request.output)?;
    let expected = expected_words_from_path(&request.expected_claims)?;
    let first = load(&request)?;
    let preparing = Instant::now();
    let mut worker =
      Worker::compile(&first, max_main_height, max_table_height, options)?;
    let preparation_seconds = preparing.elapsed().as_secs_f64();
    worker.prove(&first, &request.output, &expected)?;
    let idle = worker.quiesce()?;
    protocol.proved(
      &request,
      false,
      false,
      preparation_seconds,
      started.elapsed().as_secs_f64(),
      &idle,
    )?;
    loop {
      current = None;
      let Some(request) = protocol.next_request()? else {
        break;
      };
      current = Some(request.id.clone());
      let started = Instant::now();
      worker_protocol::ensure_empty_output(&request.output)?;
      let expected = expected_words_from_path(&request.expected_claims)?;
      let fixture = load(&request)?;
      let loaded_key_reused = worker.loaded.is_some();
      worker.prove(&fixture, &request.output, &expected)?;
      drop(fixture);
      let idle = worker.quiesce()?;
      protocol.proved(
        &request,
        true,
        loaded_key_reused,
        0.0,
        started.elapsed().as_secs_f64(),
        &idle,
      )?;
    }
    Ok(())
  })();
  if let Err(error) = &result {
    protocol.failed(current.as_deref(), &error.to_string())?;
  }
  result
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::plonkish::gadgets::ByteGadgets;
  use multi_stark::plonkish::gadgets::blake3;
  use multi_stark::plonkish::{CircuitBuilder, Value};

  const OPTIONS: Options = Options { prefetch_bytes: 1 << 20 };

  fn artifacts(directory: &Path) -> storage::Result<Vec<Vec<u8>>> {
    Ok(
      ["proof.compact.bin", "packet.bin", "profile-id.bin"]
        .into_iter()
        .map(|name| fs::read(directory.join("kzg").join(name)))
        .collect::<Result<_, _>>()?,
    )
  }

  struct Fixture {
    compiled: MultiStarkCircuit<Scalar>,
    public: Vec<Scalar>,
    input: Value,
    private: Value,
  }

  impl Fixture {
    fn assign(&self, private_byte: u8) -> storage::Result<Assignment<Scalar>> {
      let mut witness = self.compiled.witness();
      witness.set(self.input, Scalar::from_u8(7))?;
      witness.set(self.private, Scalar::from_u8(private_byte))?;
      Ok(witness.generate()?)
    }
  }

  /// A small circuit whose lowering has the Init stage's partition layout.
  fn fixture(log_height: usize) -> storage::Result<Fixture> {
    let mut builder = CircuitBuilder::<Scalar>::new();
    builder.enable_compact_blake3();
    let bytes = ByteGadgets::new(&mut builder);
    let input = bytes.input(&mut builder, "byte");
    let private = bytes.input(&mut builder, "private byte");
    let _digest = blake3(&mut builder, &bytes, &[input, private]);
    let seven = builder.constant(Scalar::from_u8(7));
    for _ in 0..65540 {
      builder.assert_equal(input.value(), seven);
    }
    let public: Vec<_> =
      init_claim::INIT_PUBLIC_WORDS.into_iter().map(Scalar::from_u64).collect();
    for &word in &public {
      let value = builder.constant(word);
      builder.expose_public(value);
    }
    let compiled = builder
      .finish()
      .lower_to_multi_stark_sharded(Scalar::from_u8(93), 1 << log_height)?
      .merge_table_traces(1 << 22)?;
    Ok(Fixture {
      compiled,
      public,
      input: input.value(),
      private: private.value(),
    })
  }

  /// Write the metadata `stage_and_prove` produces before proving.
  fn stage(
    dir: &Path,
    compiled: &MultiStarkCircuit<Scalar>,
    public: &[Scalar],
    cache_root: &Path,
  ) -> storage::Result<FixedCache> {
    crate::pipeline::support::kzg_setup::permit_development();
    fs::create_dir_all(dir)?;
    let height = max_height(compiled)?;
    SetupSource::development(FIRST_SEED, height - 1)?
      .bind_stage(dir, height, 2)?;
    fs::write(dir.join("plan-id.bin"), [0u8; 32])?;
    let cache = FixedCache::from_profile(cache_root, b"fixture-v1")?;
    let cached = cache.restore(dir)?;
    let manifest = storage::Manifest::for_compiled(
      compiled,
      compiled.claims(public)?,
      cached.as_ref(),
    )?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    Ok(cache)
  }

  #[test]
  fn fused_fixture_proves_and_reuses_fixed_preprocessing() -> storage::Result<()>
  {
    let partitioned = prove_fixture(16)?;
    let single = prove_fixture(17)?;
    assert!(single < partitioned, "fewer partitions should reduce this proof");
    Ok(())
  }

  fn prove_fixture(log_height: usize) -> storage::Result<usize> {
    crate::pipeline::support::kzg_setup::permit_development();
    let root = std::env::temp_dir().join(format!(
      "init-fri-kzg-fixture-{}-{log_height}",
      std::process::id()
    ));
    fs::create_dir(&root)?;
    let fixture = fixture(log_height)?;
    let (compiled, public) = (&fixture.compiled, &fixture.public);
    assert_eq!(compiled.num_circuits(), if log_height == 16 { 12 } else { 11 });
    let assignment = fixture.assign(9)?;
    let traces = compiled.trace_shards(&assignment)?;
    let cache_root = root.join("cache");

    // A cold run commits the fixed traces, proves and publishes the cache.
    let dir = root.join("cold");
    let cache = stage(&dir, compiled, public, &cache_root)?;
    prove(&dir, &traces, &mut None, &cache, OPTIONS)?;
    let first = artifacts(&dir)?;
    let manifest: storage::Manifest = storage::load(&dir.join("manifest.bin"))?;
    for i in 0..manifest.heights.len() {
      assert!(dir.join(format!("kzg/fixed-{i}.bin")).exists());
      assert!(dir.join(format!("kzg/setup-{i}.bin")).exists());
      assert!(!dir.join(format!("kzg/main-{i}.bin")).exists());
    }
    let report: serde_json::Value =
      serde_json::from_slice(&fs::read(dir.join("kzg/prove-report.json"))?)?;
    assert_eq!(report["setup"], "development");
    assert_eq!(report["development_srs"], true);

    // A warm run restores the fixed preprocessing from the cache and
    // produces identical artifacts.
    let warm = root.join("warm");
    let cache = stage(&warm, compiled, public, &cache_root)?;
    for i in 0..manifest.heights.len() {
      assert!(warm.join(format!("kzg/fixed-{i}.bin")).exists());
    }
    prove(&warm, &traces, &mut None, &cache, OPTIONS)?;
    assert_eq!(first, artifacts(&warm)?);
    let different =
      FixedCache::from_profile(&cache_root, b"different-profile")?;
    assert!(different.restore(&root.join("miss"))?.is_none());

    // A different witness changes the proof but not the profile.
    let changed = root.join("changed");
    let cache = stage(&changed, compiled, public, &cache_root)?;
    let changed_assignment = fixture.assign(231)?;
    let changed_traces = compiled.trace_shards(&changed_assignment)?;
    prove(&changed, &changed_traces, &mut None, &cache, OPTIONS)?;
    let second = artifacts(&changed)?;
    assert_ne!(first[0], second[0]);
    assert_eq!(first[2], second[2]);

    // Manifests that disagree with the generated traces are rejected
    // before any parameters load.
    for case in 0..3 {
      let mut shape = storage::Manifest {
        widths: manifest.widths.clone(),
        heights: manifest.heights.clone(),
        claims: manifest.claims.clone(),
      };
      match case {
        0 => shape.widths[0] += 1,
        1 => shape.heights[0] *= 2,
        _ => {
          shape.widths.push(1);
          shape.heights.push(2);
        },
      }
      let malformed = root.join(format!("invalid-shape-{case}"));
      let cache = stage(&malformed, compiled, public, &cache_root)?;
      storage::save(&malformed.join("manifest.bin"), &shape)?;
      let error =
        prove(&malformed, &traces, &mut None, &cache, OPTIONS).unwrap_err();
      assert!(error.to_string().contains("trace dimensions differ"));
      assert!(!malformed.join("kzg/proof.compact.bin").exists());
    }
    let malformed = root.join("invalid-height");
    let cache = stage(&malformed, compiled, public, &cache_root)?;
    let mut shape = storage::Manifest {
      widths: manifest.widths.clone(),
      heights: manifest.heights.clone(),
      claims: manifest.claims.clone(),
    };
    shape.heights[1] = 3;
    storage::save(&malformed.join("manifest.bin"), &shape)?;
    let error =
      prove(&malformed, &traces, &mut None, &cache, OPTIONS).unwrap_err();
    assert!(error.to_string().contains("trace height"));
    shape.heights[1] = manifest.heights[1];
    shape.widths[1] = 0;
    storage::save(&malformed.join("manifest.bin"), &shape)?;
    let error =
      prove(&malformed, &traces, &mut None, &cache, OPTIONS).unwrap_err();
    assert!(error.to_string().contains("unexpected trace layout"));

    // Removing a claim invalidates the staged claims.
    let mut fewer = storage::Manifest {
      widths: manifest.widths.clone(),
      heights: manifest.heights.clone(),
      claims: manifest.claims.clone(),
    };
    fewer.claims.pop();
    storage::save(&malformed.join("manifest.bin"), &fewer)?;
    let error =
      prove(&malformed, &traces, &mut None, &cache, OPTIONS).unwrap_err();
    assert!(error.to_string().contains("staged claims differ"));

    // A damaged cache entry is rejected before anything is linked into a
    // stage, whether it is metadata or a fixed checkpoint whose interior
    // bytes still decode. Files are replaced rather than edited so the
    // hard links into the proved stages keep their contents.
    let entries = fs::read_dir(&cache_root)?
      .map(|entry| Ok(entry?.path()))
      .collect::<storage::Result<Vec<_>>>()?;
    let [entry] = entries.as_slice() else {
      panic!("expected one published entry, found {entries:?}");
    };
    let cache = FixedCache::from_profile(&cache_root, b"fixture-v1")?;
    let damaged = root.join("damaged");
    for name in ["kzg/fixed-0.bin", "kzg/setup-0.bin"] {
      let published = entry.join(name);
      let original = fs::read(&published)?;
      let mut bytes = original.clone();
      let middle = bytes.len() / 2;
      bytes[middle] ^= 1;
      fs::remove_file(&published)?;
      fs::write(&published, bytes)?;
      fs::create_dir(&damaged)?;
      let error =
        cache.restore(&damaged).err().ok_or("damaged cache was restored")?;
      assert!(error.to_string().contains("incomplete or damaged"));
      assert!(!damaged.join("kzg").exists());
      fs::remove_dir_all(&damaged)?;
      fs::remove_file(&published)?;
      fs::write(&published, original)?;
    }
    fs::create_dir(&damaged)?;
    assert!(cache.restore(&damaged)?.is_some());
    fs::remove_dir_all(root)?;
    Ok(first[0].len())
  }
}
