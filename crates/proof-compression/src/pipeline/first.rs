//! Checkpointed KZG compression of the saved recursive Init FRI proof.
//!
//! `run` performs staging, proving and verification in one process: the
//! translated traces feed commitment directly, and the loaded SRS, fixed
//! preprocessing and device residency are shared between the two halves.
//! `stage` and `prove` are the resumable two-step path writing and reading
//! `*.witness.zst`; both paths share the fixed-preprocessing cache and the
//! development SRS caches and produce the same output files.
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

use super::init_fri;
use super::support::{
  kzg_fixed_cache::FixedCache,
  kzg_setup::{FIRST_SEED, SetupClass, SetupSource},
  kzg_storage as storage, kzg_worker_protocol as worker_protocol,
};

const TABLE_HEIGHT: usize = 1 << 22;
const DEFAULT_PREFETCH_GIB: usize = 32;

/// Runtime choices of one invocation, parsed from the command line.
#[derive(Clone, Copy)]
struct Options {
  /// Keep coefficient checkpoints resident instead of reading them back
  /// from disk. Fixed checkpoints are written in both modes; main ones only
  /// from disk, so a resident run commits fresh witnesses every time.
  resident: bool,
  /// Bytes of the next partition's witness that may be loaded while the
  /// current one is prepared; zero disables the overlap.
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

/// Whether a staged directory holds the traces or main checkpoints that
/// `prove` resumes from.
pub(super) fn has_restartable_traces(dir: &Path) -> storage::Result<bool> {
  let witnesses = fs::read_dir(dir)?
    .filter_map(Result::ok)
    .any(|entry| entry.file_name().to_string_lossy().ends_with(".witness.zst"));
  let mains = fs::read_dir(dir.join("kzg")).is_ok_and(|entries| {
    entries.filter_map(Result::ok).any(|entry| {
      let name = entry.file_name();
      let name = name.to_string_lossy();
      name.starts_with("main-") && name.ends_with(".bin")
    })
  });
  Ok(witnesses || mains)
}

/// Remove the per-partition files of an earlier staging of `dir`. Fixed
/// preprocessing may only return through the cache, whose identity binds
/// the executable, so a rebuilt binary never proves on stale checkpoints.
pub(super) fn clear_partition_artifacts(dir: &Path) -> storage::Result<()> {
  let stale = |name: &str, directory: &Path| -> bool {
    if directory == dir {
      name.ends_with(".meta")
        || name.ends_with(".fixed.zst")
        || name.ends_with(".witness.zst")
    } else {
      name.ends_with(".bin")
        && ["setup-", "fixed-", "main-"]
          .iter()
          .any(|prefix| name.starts_with(prefix))
    }
  };
  for directory in [dir.to_path_buf(), dir.join("kzg")] {
    let entries = match fs::read_dir(&directory) {
      Ok(entries) => entries,
      Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
      Err(error) => return Err(error.into()),
    };
    for entry in entries {
      let entry = entry?;
      if stale(&entry.file_name().to_string_lossy(), &directory) {
        fs::remove_file(entry.path())?;
      }
    }
  }
  Ok(())
}

fn log_height_arg(arg: Option<&String>) -> storage::Result<usize> {
  let log_height = arg.map(|s| s.parse::<usize>()).transpose()?.unwrap_or(24);
  if !(24..=28).contains(&log_height) {
    return Err("log-height must be 24..28".into());
  }
  Ok(log_height)
}

pub(super) fn run(args: &[String]) -> storage::Result<()> {
  const USAGE: &str = "usage: init_fri_kzg stage <saved-fri-dir> <output-dir> [log-height: 24..28] | run <saved-fri-dir> <output-dir> [log-height] [--resident] | prove <dir> [--resident] | verify <dir> | serve <new-response-jsonl-path> [log-height] [--resident]";
  let Some(command) = args.first() else {
    return Err(USAGE.into());
  };
  let rest = &args[1..];
  let resident_flag =
    |rest: &[String], positional: usize| -> storage::Result<bool> {
      match rest.len().checked_sub(positional) {
        Some(0) => Ok(false),
        Some(1) if rest[positional] == "--resident" => Ok(true),
        _ => Err(USAGE.into()),
      }
    };
  match command.as_str() {
    "prove" | "verify" if (1..=2).contains(&rest.len()) => {
      let resident = rest.get(1).is_some_and(|arg| arg == "--resident");
      if rest.len() == 2 && (!resident || command != "prove") {
        return Err("only prove accepts --resident".into());
      }
      init_tracing();
      let mode = if command == "verify" {
        ProveMode::Verify
      } else {
        ProveMode::Checkpointed
      };
      prove_with_state(
        Path::new(&rest[0]),
        mode,
        &mut None,
        Options { resident, prefetch_bytes: prefetch_bytes_from_env()? },
      )
    },
    "stage" if (2..=3).contains(&rest.len()) => {
      let log_height = log_height_arg(rest.get(2))?;
      stage(Path::new(&rest[0]), Path::new(&rest[1]), log_height, None)
    },
    "run" if (2..=4).contains(&rest.len()) => {
      let has_height = rest.get(2).is_some_and(|arg| arg != "--resident");
      let log_height = log_height_arg(has_height.then(|| &rest[2]))?;
      let resident = resident_flag(rest, if has_height { 3 } else { 2 })?;
      init_tracing();
      stage(
        Path::new(&rest[0]),
        Path::new(&rest[1]),
        log_height,
        Some(Options { resident, prefetch_bytes: prefetch_bytes_from_env()? }),
      )
    },
    "serve" if (1..=3).contains(&rest.len()) => {
      let has_height = rest.get(1).is_some_and(|arg| arg != "--resident");
      let log_height = log_height_arg(has_height.then(|| &rest[1]))?;
      let resident = resident_flag(rest, if has_height { 2 } else { 1 })?;
      init_tracing();
      serve(
        Path::new(&rest[0]),
        log_height,
        Options { resident, prefetch_bytes: prefetch_bytes_from_env()? },
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
    (0..self.compiled.num_circuits())
      .map(|i| self.compiled.trace_dimensions(i).map(|(height, _)| height))
      .max()
      .flatten()
      .ok_or_else(|| "empty compiled circuit".into())
  }
}

fn public_scalars(public: &[Val; 18]) -> Vec<Scalar> {
  public.iter().map(|v| Scalar::from_u64(v.as_canonical_u64())).collect()
}

/// Shape the staged manifest, restoring fixed preprocessing from the cache
/// when the profile has been proved by this executable before. Without a
/// cache hit and outside the fused path, the fixed traces are staged to disk.
fn stage_manifest(
  out: &Path,
  frontend: &Frontend,
  max_height: usize,
  claims: Vec<Vec<Scalar>>,
  cached: Option<&super::support::kzg_fixed_cache::Shape>,
  fused: bool,
) -> storage::Result<storage::Manifest> {
  let compiled = &frontend.compiled;
  let mut manifest =
    storage::Manifest { widths: vec![], heights: vec![], claims };
  if cached.is_some_and(|shape| {
    shape.widths.len() != compiled.num_circuits()
      || shape.heights.len() != compiled.num_circuits()
  }) {
    return Err("cached trace count differs from the compiled circuit".into());
  }
  for i in 0..compiled.num_circuits() {
    let (trace_height, trace_width) =
      compiled.trace_dimensions(i).ok_or("missing compiled trace")?;
    if let Some(shape) = cached {
      if shape.widths[i] != trace_width || shape.heights[i] != trace_height {
        return Err(
          "cached fixed trace dimensions differ from the compiled circuit"
            .into(),
        );
      }
      manifest.widths.push(shape.widths[i]);
      manifest.heights.push(shape.heights[i]);
    } else if fused {
      manifest.widths.push(trace_width);
      manifest.heights.push(trace_height);
    } else {
      let fixed_started = Instant::now();
      let mut definition =
        compiled.kzg_circuit_input(i, max_height, 2)?.unwrap();
      let fixed = definition.preprocessed.take().unwrap();
      manifest.widths.push(definition.main_width);
      manifest.heights.push(fixed.height());
      storage::save(&out.join(format!("{i}.meta")), &definition)?;
      storage::write_matrix(&out.join(format!("{i}.fixed.zst")), &fixed)?;
      println!(
        "Fixed trace staged circuit={i} seconds={:.9}",
        fixed_started.elapsed().as_secs_f64()
      );
    }
  }
  Ok(manifest)
}

fn stage(
  fri: &Path,
  out: &Path,
  log_height: usize,
  fused: Option<Options>,
) -> storage::Result<()> {
  let max_height = 1usize << log_height;
  fs::create_dir_all(out)?;
  if out.join("manifest.bin").exists() {
    // A fused run writes its manifest before proving and keeps no witness
    // files, so a directory with a manifest but neither witnesses nor main
    // checkpoints is an interrupted fused run and is staged again.
    if fused.is_none() || has_restartable_traces(out)? {
      return Err("staging already complete".into());
    }
    fs::remove_file(out.join("manifest.bin"))?;
  }
  clear_partition_artifacts(out)?;
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
  let setup = SetupSource::for_stage(FIRST_SEED, height, None)?;
  setup.bind_stage(out, height, 2)?;
  let setup_id = setup.identity(height, 2)?;
  let cache = FixedCache::for_stage(out, &[plan_id, setup_id].concat())?;
  let cached = cache.restore(out)?;
  let shards = frontend.compiled.trace_shards(&scalar)?;
  let manifest = stage_manifest(
    out,
    &frontend,
    max_height,
    frontend.compiled.claims(&public)?,
    cached.as_ref(),
    fused.is_some(),
  )?;
  if fused.is_none() {
    for i in 0..frontend.compiled.num_circuits() {
      let trace = shards.trace(i)?;
      if trace.width() != manifest.widths[i]
        || trace.height() != manifest.heights[i]
      {
        return Err(
          "cached fixed trace and witness have different shapes".into(),
        );
      }
      storage::write_matrix(&out.join(format!("{i}.witness.zst")), &trace)?;
      println!(
        "Staged {i}/{}: {:?}",
        frontend.compiled.num_circuits(),
        start.elapsed()
      );
    }
  }
  storage::save(&out.join("manifest.bin"), &manifest)?;
  match fused {
    Some(options) => {
      println!(
        "Metadata staging complete; generating fixed and witness traces directly into commitment"
      );
      prove_with_state(out, ProveMode::Fresh(&shards), &mut None, options)?;
      println!("RUN COMPLETE: {:?}", start.elapsed());
    },
    None => println!("STAGING COMPLETE: {:?}", start.elapsed()),
  }
  Ok(())
}

#[derive(Clone, Copy)]
enum ProveMode<'a> {
  /// Fixed and main traces come from the staged files.
  Checkpointed,
  /// Traces are generated from the in-process assignment.
  Fresh(&'a TraceShards<'a, Scalar>),
  Verify,
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

fn expected_claims(count: usize) -> Vec<Vec<Scalar>> {
  let namespace = Scalar::from_u8(93);
  let mut expected: Vec<_> = std::iter::once(0)
    .chain(init_fri::INIT_PUBLIC_WORDS)
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
  if count > 11 {
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

fn setup_for(dir: &Path, height: usize) -> storage::Result<SetupSource> {
  SetupSource::for_stage(FIRST_SEED, height, Some(dir.join("kzg/dev-srs.bin")))
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

fn read_checkpoint(
  path: &Path,
  resident: bool,
) -> storage::Result<KzgProverData> {
  // The device paths need host coefficients, so a CUDA build keeps every
  // checkpoint resident as the original pipeline did.
  Ok(if resident || cfg!(feature = "cuda") {
    KzgProverData::read_checkpoint(BufReader::with_capacity(
      1 << 20,
      File::open(path)?,
    ))?
  } else {
    KzgProverData::read_checkpoint_file(path)?
  })
}

#[allow(clippy::too_many_lines)]
fn prove_with_state(
  dir: &Path,
  mode: ProveMode<'_>,
  retained: &mut Option<LoadedProver>,
  options: Options,
) -> storage::Result<()> {
  let verify_only = matches!(mode, ProveMode::Verify);
  let fresh = matches!(mode, ProveMode::Fresh(_));
  let resident = options.resident;
  let cold = retained.is_none();
  let manifest: storage::Manifest = storage::load(&dir.join("manifest.bin"))?;
  let count = manifest.heights.len();
  if count < 11
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
  if let ProveMode::Fresh(traces) = mode {
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
  }
  if manifest.claims != expected_claims(count) {
    return Err(
      "staged claims differ from expected Init statement and activation anchors"
        .into(),
    );
  }
  let setup = setup_for(dir, height)?;
  setup.check_binding(dir, height, 2)?;
  let setup_id = setup.identity(height, 2)?;
  let plan_id: [u8; 32] = fs::read(dir.join("plan-id.bin"))?
    .try_into()
    .map_err(|bytes: Vec<u8>| {
      format!("invalid verifier plan identity: {} bytes", bytes.len())
    })?;
  if let Some(loaded) = retained {
    if loaded.plan_id != plan_id
      || loaded.setup_id != setup_id
      || loaded.widths != manifest.widths
      || loaded.heights != manifest.heights
    {
      return Err("request differs from the loaded prover profile".into());
    }
    if !verify_only && loaded.key.preprocessed_data.is_none() {
      return Err("loaded verifier has no proving key".into());
    }
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
      .config(height, 2, verify_only)?
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
  let load_witness = |i: usize| -> Result<_, String> {
    if let ProveMode::Fresh(traces) = mode {
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
      Ok(Some(trace))
    } else if verify_only || out.join(format!("main-{i}.bin")).exists() {
      Ok(None)
    } else {
      storage::read_matrix_with_shape(
        &dir.join(format!("{i}.witness.zst")),
        manifest.widths[i],
        manifest.heights[i],
      )
      .map(Some)
      .map_err(|error| error.to_string())
    }
  };
  let mut prefetched = None;
  for i in 0..count {
    let witness = prefetched.take().unwrap_or_else(|| load_witness(i))?;
    let prepare = || -> storage::Result<()> {
      let meta = out.join(format!("setup-{i}.bin"));
      let fixed_path = out.join(format!("fixed-{i}.bin"));
      let main_path = out.join(format!("main-{i}.bin"));
      if cold {
        let fixed_started = Instant::now();
        let from_checkpoint =
          meta.exists() && (verify_only || fixed_path.exists());
        let (circuit, commitment): (Circuit<Scalar>, KzgCommitment) =
          if from_checkpoint {
            if !verify_only {
              fixed_parts.push(read_checkpoint(&fixed_path, resident)?);
            }
            storage::load(&meta)?
          } else {
            if verify_only {
              return Err("missing setup checkpoint".into());
            }
            let load_started = Instant::now();
            let mut definition = match mode {
              ProveMode::Fresh(traces) => traces
                .compiled()
                .kzg_circuit_input(i, height, 2)?
                .ok_or("missing compiled fixed trace")?,
              _ => storage::definition(dir, i, height)?,
            };
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
            if fresh {
              let fixed = definition.preprocessed.take();
              storage::save(&dir.join(format!("{i}.meta")), &definition)?;
              definition.preprocessed = fixed;
            }
            println!(
              "KZG fixed trace {} circuit={i} seconds={:.9} overlap_possible=true",
              if fresh { "generated" } else { "loaded" },
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
            fixed_parts.push(if resident {
              data
            } else {
              drop(data);
              read_checkpoint(&fixed_path, false)?
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
          if from_checkpoint { "checkpoint" } else { "generated" },
        );
      }
      if !verify_only {
        let main_started = Instant::now();
        let from_checkpoint = !fresh && main_path.exists();
        let data = if from_checkpoint {
          read_checkpoint(&main_path, resident)?
        } else {
          let main = witness.ok_or("missing prefetched witness")?;
          let commit_started = Instant::now();
          let (_, data) = config.pcs().commit(vec![(
            config.pcs().natural_domain_for_degree(manifest.heights[i]),
            main,
          )]);
          println!(
            "KZG main committed circuit={i} seconds={:.9} overlap_possible=true",
            commit_started.elapsed().as_secs_f64()
          );
          if fresh || resident {
            data
          } else {
            write_checkpoint(&main_path, &data)?;
            drop(data);
            read_checkpoint(&main_path, false)?
          }
        };
        main_parts.push(data);
        println!(
          "KZG main prepared circuit={i} seconds={:.9} source={} overlap_possible=true",
          main_started.elapsed().as_secs_f64(),
          if from_checkpoint { "checkpoint" } else { "generated" },
        );
      }
      println!("Prepared {i}/{count}: {:?}", start.elapsed());
      Ok(())
    };
    let can_prefetch = !verify_only
      && options.prefetch_bytes > 0
      && i + 1 < count
      && manifest.widths[i + 1]
        .checked_mul(manifest.heights[i + 1])
        .and_then(|values| values.checked_mul(size_of::<Scalar>()))
        .is_some_and(|bytes| bytes <= options.prefetch_bytes);
    if can_prefetch {
      let (prepared, next) = p3_maybe_rayon::prelude::join(
        || prepare().map_err(|error| error.to_string()),
        || load_witness(i + 1),
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
    let key = if verify_only {
      ProverKey { preprocessed_data: None }
    } else {
      let (commitment, data) = KzgProverData::concatenate(fixed_parts);
      assert_eq!(Some(commitment), system.preprocessed_commit);
      ProverKey { preprocessed_data: Some(data) }
    };
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
  let proof_path = out.join("proof.compact.bin");
  let bytes = if verify_only {
    fs::read(&proof_path)?
  } else {
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
    system
      .verify_multiple_claims(&refs, &proof)
      .map_err(|e| format!("proof: {e:?}"))?;
    let bytes = codec.encode(&proof)?;
    fs::write(&proof_path, &bytes)?;
    bytes
  };
  let proof = codec.decode(&bytes)?;
  let verify_start = Instant::now();
  system
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("decoded proof: {e:?}"))?;
  let verify_seconds = verify_start.elapsed().as_secs_f64();
  for i in 0..18 {
    let mut wrong = manifest.claims.clone();
    wrong[i + 1][3] += Scalar::ONE;
    assert!(
      system
        .verify_multiple_claims(
          &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
          &proof
        )
        .is_err()
    );
  }
  let mut corrupted = bytes.clone();
  let last = corrupted.len() - 1;
  corrupted[last] ^= 1;
  assert!(match codec.decode(&corrupted) {
    Err(_) => true,
    Ok(p) => system.verify_multiple_claims(&refs, &p).is_err(),
  });
  assert!(codec.decode(&bytes[..bytes.len() - 1]).is_err());
  let mut extended = bytes.clone();
  extended.push(0);
  assert!(codec.decode(&extended).is_err());
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
  if verify_only {
    if fs::read(out.join("profile-id.bin"))? != profile
      || fs::read(out.join("packet.bin"))? != packet
    {
      return Err("saved packet or profile differs".into());
    }
  } else {
    fs::write(out.join("profile-id.bin"), profile)?;
    fs::write(out.join("packet.bin"), &packet)?;
  }
  let development = setup.class() == SetupClass::Development;
  let report = format!(
    "VERIFIED: proof_bytes={} packet_bytes={} verify_seconds={verify_seconds} total_seconds={} altered_claims_rejected=18 development_srs={development}\n",
    bytes.len(),
    packet.len(),
    start.elapsed().as_secs_f64()
  );
  fs::write(out.join("VERIFIED.txt"), &report)?;
  let public_setup = system.config.pcs().public_setup();
  let evidence = serde_json::json!({
    "proof_bytes": bytes.len(),
    "packet_bytes": packet.len(),
    "trace_heights": manifest.heights,
    "verify_seconds": verify_seconds,
    "total_seconds": start.elapsed().as_secs_f64(),
    "native_verification_passed": true,
    "negative_tests_pass": true,
    "altered_claims_rejected": 18,
    "development_srs": development,
    "known_trapdoor": development,
    "setup": setup.class().label(),
    "setup_id": blake3::Hash::from_bytes(setup_id).to_string(),
    "public_setup_id": blake3::Hash::from_bytes(public_setup.id).to_string(),
    "public_max_degree": public_setup.max_degree,
    "resident": resident,
    "fresh_traces": fresh,
  });
  fs::write(
    out.join(if verify_only {
      "verify-report.json"
    } else {
      "prove-report.json"
    }),
    format!("{evidence}\n"),
  )?;
  if cold
    && !verify_only
    && let Some(cache) = FixedCache::for_prove(dir)?
  {
    cache.publish(dir)?;
  }
  print!("{report}");
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
    let setup = SetupSource::for_stage(FIRST_SEED, height, None)?;
    setup.bind_stage(output, height, 2)?;
    let setup_id = setup.identity(height, 2)?;
    let claims = self.frontend.compiled.claims(&public)?;
    let manifest = if let Some(loaded) = &self.loaded {
      storage::Manifest {
        widths: loaded.widths.clone(),
        heights: loaded.heights.clone(),
        claims,
      }
    } else {
      let cache =
        FixedCache::for_stage(output, &[self.plan_id, setup_id].concat())?;
      let cached = cache.restore(output)?;
      stage_manifest(
        output,
        &self.frontend,
        height,
        claims,
        cached.as_ref(),
        true,
      )?
    };
    storage::save(&output.join("manifest.bin"), &manifest)?;
    let traces = self.frontend.compiled.trace_shards(&assignment)?;
    prove_with_state(
      output,
      ProveMode::Fresh(&traces),
      &mut self.loaded,
      self.options,
    )
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

/// The independently expected Init statement words from a claims file in
/// the root stage's layout: one claim of 18 little-endian words.
fn expected_words_from_path(path: &Path) -> storage::Result<[u64; 18]> {
  let bytes = fs::read(path)?;
  let (words, remainder) = bytes.as_chunks::<8>();
  if !remainder.is_empty() || words.len() != 20 {
    return Err("expected claims must hold one claim of 18 words".into());
  }
  let words: Vec<_> = words.iter().map(|w| u64::from_le_bytes(*w)).collect();
  if words[0] != 1 || words[1] != 18 {
    return Err("expected claims must hold one claim of 18 words".into());
  }
  Ok(words[2..].try_into().unwrap())
}

fn serve(
  path: &Path,
  log_height: usize,
  options: Options,
) -> storage::Result<()> {
  let mut protocol = worker_protocol::Protocol::open(path, "init_fri_kzg")?;
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
  use multi_stark::plonkish::CircuitBuilder;
  use multi_stark::plonkish::gadgets::ByteGadgets;
  use multi_stark::plonkish::gadgets::blake3;

  const OPTIONS: Options = Options { resident: false, prefetch_bytes: 1 << 20 };

  fn prove(
    dir: &Path,
    mode: ProveMode<'_>,
    resident: bool,
  ) -> storage::Result<()> {
    prove_with_state(dir, mode, &mut None, Options { resident, ..OPTIONS })
  }

  #[test]
  fn staged_hash_fixture_proves_and_resumes_verification() -> storage::Result<()>
  {
    let partitioned = staged_fixture(16, false)?;
    let single = staged_fixture(17, true)?;
    assert!(single < partitioned, "fewer partitions should reduce this proof");
    Ok(())
  }

  #[test]
  fn malformed_stage_shapes_fail_before_loading_parameters()
  -> storage::Result<()> {
    let dir = std::env::temp_dir()
      .join(format!("init-fri-kzg-invalid-shape-{}", std::process::id()));
    fs::create_dir(&dir)?;
    let mut manifest = storage::Manifest {
      widths: vec![3; 12],
      heights: vec![1 << 24; 12],
      claims: vec![],
    };
    for invalid in [0, 1, 3] {
      manifest.heights[1] = invalid;
      storage::save(&dir.join("manifest.bin"), &manifest)?;
      let error = prove(&dir, ProveMode::Verify, false).unwrap_err();
      assert!(error.to_string().contains("trace height"));
    }
    manifest.heights[1] = 1 << 16;
    manifest.widths[1] = 0;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    let error = prove(&dir, ProveMode::Verify, false).unwrap_err();
    assert!(error.to_string().contains("unexpected trace layout"));
    fs::remove_dir_all(dir)?;
    Ok(())
  }

  fn artifacts(directory: &Path) -> storage::Result<Vec<Vec<u8>>> {
    Ok(
      ["proof.compact.bin", "packet.bin", "profile-id.bin"]
        .into_iter()
        .map(|name| fs::read(directory.join("kzg").join(name)))
        .collect::<Result<_, _>>()?,
    )
  }

  fn staged_fixture(
    log_height: usize,
    resident: bool,
  ) -> storage::Result<usize> {
    let dir = std::env::temp_dir().join(format!(
      "init-fri-kzg-fixture-{}-{log_height}",
      std::process::id()
    ));
    fs::create_dir(&dir)?;
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
      init_fri::INIT_PUBLIC_WORDS.into_iter().map(Scalar::from_u64).collect();
    for &word in &public {
      let value = builder.constant(word);
      builder.expose_public(value);
    }
    let compiled = builder
      .finish()
      .lower_to_multi_stark_sharded(Scalar::from_u8(93), 1 << log_height)?
      .merge_table_traces(1 << 22)?;
    let assign = |private_byte| -> storage::Result<_> {
      let mut witness = compiled.witness();
      witness.set(input.value(), Scalar::from_u8(7))?;
      witness.set(private.value(), Scalar::from_u8(private_byte))?;
      Ok(witness.generate()?)
    };
    let assignment = assign(9)?;
    let traces = compiled.trace_shards(&assignment)?;
    let height = compiled
      .circuit_inputs()
      .iter()
      .map(|c| c.preprocessed.as_ref().unwrap().height())
      .max()
      .unwrap();
    let mut manifest = storage::Manifest {
      widths: vec![],
      heights: vec![],
      claims: compiled.claims(&public)?,
    };
    for i in 0..compiled.num_circuits() {
      let mut input = compiled.kzg_circuit_input(i, height, 2)?.unwrap();
      let fixed = input.preprocessed.take().unwrap();
      manifest.widths.push(input.main_width);
      manifest.heights.push(fixed.height());
      storage::save(&dir.join(format!("{i}.meta")), &input)?;
      storage::write_matrix(&dir.join(format!("{i}.fixed.zst")), &fixed)?;
      storage::write_matrix(
        &dir.join(format!("{i}.witness.zst")),
        &traces.trace(i)?,
      )?;
    }
    SetupSource::development(FIRST_SEED, height - 1, None)?
      .bind_stage(&dir, height, 2)?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    fs::write(dir.join("plan-id.bin"), [0u8; 32])?;
    assert_eq!(compiled.num_circuits(), if log_height == 16 { 12 } else { 11 });
    prove(&dir, ProveMode::Checkpointed, resident)?;
    // Fixed checkpoints are written in both storage modes; main ones only
    // when proving from disk.
    assert!(dir.join("kzg/fixed-0.bin").exists());
    assert_eq!(dir.join("kzg/main-0.bin").exists(), !resident);
    let first = artifacts(&dir)?;
    // Both storage modes must produce identical bytes at the same layout.
    prove(&dir, ProveMode::Checkpointed, !resident)?;
    assert_eq!(first, artifacts(&dir)?);
    prove(&dir, ProveMode::Verify, false)?;

    // Fresh traces fed directly into commitment produce the same artifacts
    // and never touch the staged trace files.
    let direct = dir.join("direct-fixed");
    fs::create_dir(&direct)?;
    for name in ["manifest.bin", "plan-id.bin", "kzg-setup-id.bin"] {
      fs::copy(dir.join(name), direct.join(name))?;
    }
    fs::write(direct.join("0.meta"), b"invalid metadata")?;
    fs::write(direct.join("0.fixed.zst"), b"unused fixed trace")?;
    prove(&direct, ProveMode::Fresh(&traces), resident)?;
    assert_eq!(first, artifacts(&direct)?);
    for i in 0..compiled.num_circuits() {
      assert_eq!(
        fs::read(dir.join(format!("{i}.meta")))?,
        fs::read(direct.join(format!("{i}.meta")))?
      );
      assert_eq!(
        fs::read(dir.join(format!("kzg/setup-{i}.bin")))?,
        fs::read(direct.join(format!("kzg/setup-{i}.bin")))?
      );
      assert_eq!(
        fs::read(dir.join(format!("kzg/fixed-{i}.bin")))?,
        fs::read(direct.join(format!("kzg/fixed-{i}.bin")))?
      );
      assert!(!direct.join(format!("kzg/main-{i}.bin")).exists());
      assert!(!direct.join(format!("{i}.witness.zst")).exists());
    }
    assert_eq!(fs::read(direct.join("0.fixed.zst"))?, b"unused fixed trace");
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
      let malformed = dir.join(format!("invalid-fresh-shape-{case}"));
      fs::create_dir(&malformed)?;
      storage::save(&malformed.join("manifest.bin"), &shape)?;
      let error =
        prove(&malformed, ProveMode::Fresh(&traces), resident).unwrap_err();
      assert!(error.to_string().contains("trace dimensions differ"));
      assert!(!malformed.join("kzg").exists());
    }

    // A published fixed cache restores metadata and fixed checkpoints into
    // a new directory, which then proves without staging fixed traces.
    let cache = FixedCache::from_profile(&dir.join("cache"), b"fixture-v1")?;
    cache.publish(&direct)?;
    let reused = dir.join("reused");
    fs::create_dir(&reused)?;
    let shape = cache.restore(&reused)?.ok_or("missing populated cache")?;
    assert_eq!(shape.heights, manifest.heights);
    for name in ["manifest.bin", "plan-id.bin", "kzg-setup-id.bin"] {
      fs::copy(dir.join(name), reused.join(name))?;
    }
    for i in 0..manifest.heights.len() {
      assert!(!reused.join(format!("{i}.fixed.zst")).exists());
      assert!(!reused.join(format!("kzg/main-{i}.bin")).exists());
      fs::copy(
        dir.join(format!("{i}.witness.zst")),
        reused.join(format!("{i}.witness.zst")),
      )?;
    }
    prove(&reused, ProveMode::Checkpointed, resident)?;
    assert_eq!(first, artifacts(&reused)?);
    let different =
      FixedCache::from_profile(&dir.join("cache"), b"different-profile")?;
    assert!(different.restore(&dir.join("miss"))?.is_none());

    // A metadata file whose bytes no longer match the digest recorded at
    // publication is rejected before anything is linked into the stage;
    // checkpoint files verify their own digest on every read. The file is
    // replaced rather than edited so the hard links into `direct` and
    // `reused` keep their contents.
    let entries = fs::read_dir(dir.join("cache"))?
      .map(|entry| Ok(entry?.path()))
      .collect::<storage::Result<Vec<_>>>()?;
    let [entry] = entries.as_slice() else {
      panic!("expected one published entry, found {entries:?}");
    };
    let published = entry.join("kzg/setup-0.bin");
    let mut bytes = fs::read(&published)?;
    bytes[0] ^= 1;
    fs::remove_file(&published)?;
    fs::write(&published, bytes)?;
    let damaged = dir.join("damaged");
    fs::create_dir(&damaged)?;
    let error =
      cache.restore(&damaged).err().ok_or("damaged cache was restored")?;
    assert!(error.to_string().contains("incomplete or damaged"));
    assert!(!damaged.join("kzg").exists());

    // Saved packets and profiles are compared on verification.
    for name in ["packet.bin", "profile-id.bin"] {
      let path = dir.join("kzg").join(name);
      let original = fs::read(&path)?;
      let mut altered = original.clone();
      altered[0] ^= 1;
      fs::write(&path, &altered)?;
      let error = prove(&dir, ProveMode::Verify, false).unwrap_err();
      assert!(error.to_string().contains("saved packet or profile differs"));
      fs::write(path, original)?;
    }

    // A different witness through the fresh path changes the proof, and a
    // changed manifest is rejected before any parameters load.
    let changed = assign(231)?;
    let changed_traces = compiled.trace_shards(&changed)?;
    prove(&reused, ProveMode::Fresh(&changed_traces), resident)?;
    assert_ne!(first, artifacts(&reused)?);
    prove(&reused, ProveMode::Verify, false)?;
    manifest.widths[0] += 1;
    storage::save(&reused.join("manifest.bin"), &manifest)?;
    let error =
      prove(&reused, ProveMode::Fresh(&changed_traces), resident).unwrap_err();
    assert!(error.to_string().contains("trace dimensions differ"));
    manifest.widths[0] -= 1;

    // Removing a claim invalidates the setup binding and the staged claims.
    manifest.claims.pop();
    SetupSource::development(FIRST_SEED, height - 1, None)?
      .bind_stage(&dir, height, 2)?;
    storage::save(&dir.join("manifest.bin"), &manifest)?;
    assert!(prove(&dir, ProveMode::Verify, false).is_err());
    fs::remove_dir_all(dir)?;
    Ok(first[0].len())
  }
}
