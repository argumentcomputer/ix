//! A statement-bound Goldilocks verifier executed and proved over BN254.
//!
//! The compiler artifact and setup capacities are release inputs. Root keys
//! and claims enter the public statement as authenticated data, while trace
//! heights vary per execution beneath the same public capacity.
use super::{
  Bn254,
  kzg::{Backend, Compiler, MAX_TOTAL_ROWS, VerifyingKey},
};
use crate::{
  kzg::{KzgConfig, Scalar},
  pipeline::SetupConfig,
};
use aiur::{
  Execution,
  artifact::WidePackage,
  bytecode::CheckedProgram,
  field::FieldBackend,
  trace::{TracePlan, stark::planning},
};
use multi_stark::{lookup::logup_max_degree, system::extension_params};
use serde::Serialize;
use stark_verifier::compress_wrap::{Input, STATEMENT_BYTES, Statement};
use std::{sync::Arc, time::Instant};

pub const ENTRY: &str = "CompressGL::verify_root";
const DEVELOPMENT_SEED: &[u8] = b"ix/aiur-compress-gl/kzg/v1";

pub struct Wrapper {
  program: Arc<CheckedProgram<Bn254>>,
  plan: TracePlan<'static, Bn254>,
  artifact_digest: [u8; 32],
}

pub struct Executed<'a> {
  input: &'a Input,
  record: Execution<Bn254>,
  args: Vec<Scalar>,
  artifact_digest: [u8; 32],
  execution_seconds: f64,
}

impl Executed<'_> {
  pub const fn input(&self) -> &Input {
    self.input
  }
  pub const fn record(&self) -> &Execution<Bn254> {
    &self.record
  }
}

#[derive(Clone, Debug, Serialize)]
pub struct CircuitSize {
  pub name: String,
  pub height: usize,
  pub main_width: usize,
  pub fixed_width: usize,
  /// Stage-two accumulator columns, distinct from concrete lookup tuples.
  pub lookup_width: usize,
  pub concrete_lookup_width: usize,
  pub quotient_degree: usize,
}

#[derive(Clone, Debug, Serialize)]
pub struct Profile {
  pub artifact_blake3: String,
  pub root_key_blake3: String,
  pub root_claims_blake3: String,
  pub instructions: u64,
  pub record: aiur::execute::RecordStorage,
  pub circuits: Vec<CircuitSize>,
  pub max_height: usize,
  pub total_rows: usize,
  pub main_cells: usize,
  pub fixed_cells: usize,
  /// Stage-two accumulator cells, excluding concrete lookup tuple payloads.
  pub lookup_cells: usize,
  pub stage2_accumulator_cells: usize,
  pub stage2_accumulator_bytes: usize,
  /// The tuple payload a fully materialized lookup witness would allocate.
  pub concrete_lookup_cells: usize,
  pub concrete_lookup_bytes: usize,
  pub main_fixed_lookup_bytes: usize,
  pub quotient_degree: usize,
  pub execution_seconds: f64,
  pub planning_seconds: f64,
  pub resident_bytes: u64,
  pub peak_resident_bytes: u64,
}

/// Public limits belong to the verifier key. Loading a shorter SRS prefix for
/// a smaller execution must not change these values or the setup identity.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct Capacity {
  pub max_log_height: u8,
  pub quotient_degree: usize,
}

impl Capacity {
  fn height(self) -> Result<usize, String> {
    if self.max_log_height == 0
      || !self.quotient_degree.is_power_of_two()
      || u32::from(self.max_log_height) + self.quotient_degree.ilog2() > 28
    {
      return Err("invalid BN254 trace/quotient capacity".into());
    }
    1usize
      .checked_shl(u32::from(self.max_log_height))
      .ok_or_else(|| "trace capacity overflow".into())
  }

  fn config(
    self,
    setup: &SetupConfig,
    loaded_height: usize,
  ) -> Result<KzgConfig, String> {
    let cap = self.height()?;
    if loaded_height < 2
      || !loaded_height.is_power_of_two()
      || loaded_height > cap
    {
      return Err("execution exceeds the admitted trace capacity".into());
    }
    let source =
      setup.for_stage(DEVELOPMENT_SEED, cap).map_err(|e| e.to_string())?;
    let srs = source.srs(loaded_height, false).map_err(|e| e.to_string())?;
    Ok(
      KzgConfig::with_max_trace_len(Arc::new(srs), cap, self.quotient_degree)
        .with_streaming_lookups()
        .with_streaming_quotient(),
    )
  }
}

pub struct Proven {
  pub key: Vec<u8>,
  pub proof: Vec<u8>,
  pub claim: Vec<Scalar>,
  pub statement: [u8; STATEMENT_BYTES],
  pub profile: Profile,
  pub capacity: Capacity,
  pub setup: &'static str,
  pub setup_seconds: f64,
  pub trace_seconds: f64,
  pub proving_seconds: f64,
  pub verification_seconds: f64,
}

impl Wrapper {
  /// Authenticate bytes before parsing. A matching digest identifies trusted
  /// compiler output; structural validation alone cannot establish meaning.
  pub fn from_bytes(
    bytes: &[u8],
    expected_digest: &[u8; 32],
  ) -> Result<Self, String> {
    let artifact_digest = *blake3::hash(bytes).as_bytes();
    if &artifact_digest != expected_digest {
      return Err("CompressGL artifact differs from the trusted pin".into());
    }
    let package = WidePackage::decode(bytes)?;
    let trace =
      package.trace.ok_or("CompressGL needs a compiler trace artifact")?;
    let mut program = package.program.check_with(Bn254)?;
    program.track_depth(&trace)?;
    program.entry(ENTRY)?;
    let program = Arc::new(program);
    let plan = TracePlan::new(Arc::clone(&program), trace)?;
    if plan.public_claim(ENTRY, &[Bn254.zero(); 16], &[])?.len() != 18 {
      return Err(
        "CompressGL entry must have 16 arguments and unit output".into(),
      );
    }
    Ok(Self { program, plan, artifact_digest })
  }

  pub const fn artifact_digest(&self) -> &[u8; 32] {
    &self.artifact_digest
  }
  pub const fn plan(&self) -> &TracePlan<'static, Bn254> {
    &self.plan
  }

  pub fn claim(&self, statement: &Statement) -> Result<Vec<Scalar>, String> {
    self.plan.public_claim(ENTRY, &arguments(statement), &[])
  }

  /// Compile the release key with only the powers required by fixed tables.
  /// Execution-dependent trace heights do not enter this key.
  pub fn verifying_key(
    &self,
    setup: &SetupConfig,
    capacity: Capacity,
  ) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(&self.plan)?;
    let height = compiler
      .inputs()
      .iter()
      .filter_map(|input| input.preprocessed.as_ref())
      .map(|matrix| matrix.values.len() / matrix.width)
      .max()
      .unwrap_or(2)
      .max(2);
    Backend::new(&self.plan, capacity.config(setup, height)?)?
      .verifying_key()?
      .to_bytes()
  }

  pub fn execute<'a>(&self, input: &'a Input) -> Result<Executed<'a>, String> {
    let started = Instant::now();
    let advice = stark_verifier::advice(
      Bn254,
      input.key_bytes(),
      input.claims_bytes(),
      input.proof_bytes(),
    )?;
    let prepared =
      stark_verifier::prepare_compress_gl_advice(&self.program, &advice)?;
    let args = arguments(input.statement());
    let record =
      prepared.execute(ENTRY, args.clone()).map_err(|e| e.to_string())?;
    if !record.output.is_empty() {
      return Err("CompressGL returned non-unit output".into());
    }
    Ok(Executed {
      input,
      record,
      args,
      artifact_digest: self.artifact_digest,
      execution_seconds: started.elapsed().as_secs_f64(),
    })
  }

  fn check_execution(&self, execution: &Executed<'_>) -> Result<(), String> {
    if execution.artifact_digest != self.artifact_digest {
      return Err(
        "CompressGL execution belongs to another compiler artifact".into(),
      );
    }
    Ok(())
  }

  /// Exact padded trace cells without trace population. These figures exclude
  /// polynomial transforms, quotient workspaces, commitments and allocator slack.
  pub fn profile(&self, execution: &Executed<'_>) -> Result<Profile, String> {
    self.check_execution(execution)?;
    let started = Instant::now();
    let compiler = Compiler::new(&self.plan)?;
    let heights = compiler.row_counts(&execution.record)?;
    let params = extension_params::<KzgConfig>();
    let mut circuits = Vec::with_capacity(heights.len());
    let (mut main_cells, mut fixed_cells, mut lookup_cells, mut total_rows) =
      (0usize, 0usize, 0usize, 0usize);
    let mut max_height = 2;
    let mut quotient_degree = 1;
    let mut concrete_lookup_cells = 0usize;
    for ((input, name), height) in
      compiler.inputs().iter().zip(compiler.names()).zip(heights)
    {
      let graph =
        input.compile_graph(&params).map_err(|e| format!("{name}: {e:?}"))?;
      let degree = graph
        .max_constraint_degree
        .max(logup_max_degree(&graph, input.lookup_group_size))
        as usize;
      let quotient = (degree.max(2) - 1)
        .checked_next_power_of_two()
        .ok_or("quotient degree overflow")?;
      let fixed_width =
        input.preprocessed.as_ref().map_or(0, |matrix| matrix.width);
      let lookup_width =
        input.lookups.len().div_ceil(input.lookup_group_size) * params.degree;
      let concrete_lookup_width =
        graph.lookups.iter().map(|lookup| lookup.args.len() + 1).sum();
      add_cells(&mut main_cells, height, input.main_width)?;
      add_cells(&mut fixed_cells, height, fixed_width)?;
      add_cells(&mut lookup_cells, height, lookup_width)?;
      add_cells(&mut concrete_lookup_cells, height, concrete_lookup_width)?;
      total_rows =
        total_rows.checked_add(height).ok_or("row count overflow")?;
      max_height = max_height.max(height);
      quotient_degree = quotient_degree.max(quotient);
      circuits.push(CircuitSize {
        name: name.clone(),
        height,
        main_width: input.main_width,
        fixed_width,
        lookup_width,
        concrete_lookup_width,
        quotient_degree: quotient,
      });
    }
    let bytes = main_cells
      .checked_add(fixed_cells)
      .and_then(|n| n.checked_add(lookup_cells))
      .and_then(|n| n.checked_mul(size_of::<Scalar>()))
      .ok_or("trace byte count overflow")?;
    Ok(Profile {
      artifact_blake3: blake3::Hash::from_bytes(self.artifact_digest)
        .to_hex()
        .to_string(),
      root_key_blake3: blake3::Hash::from_bytes(
        execution.input.statement().key_digest,
      )
      .to_hex()
      .to_string(),
      root_claims_blake3: blake3::Hash::from_bytes(
        execution.input.statement().claims_digest,
      )
      .to_hex()
      .to_string(),
      instructions: execution.record.instructions,
      record: execution.record.storage_usage(),
      circuits,
      max_height,
      total_rows,
      main_cells,
      fixed_cells,
      lookup_cells,
      stage2_accumulator_cells: lookup_cells,
      stage2_accumulator_bytes: lookup_cells
        .checked_mul(size_of::<Scalar>())
        .ok_or("stage-two byte count overflow")?,
      concrete_lookup_cells,
      concrete_lookup_bytes: concrete_lookup_cells
        .checked_mul(size_of::<Scalar>())
        .ok_or("lookup tuple byte count overflow")?,
      main_fixed_lookup_bytes: bytes,
      quotient_degree,
      execution_seconds: execution.execution_seconds,
      planning_seconds: started.elapsed().as_secs_f64(),
      resident_bytes: planning::resident_memory(),
      peak_resident_bytes: planning::peak_resident_memory(),
    })
  }

  pub fn prove(
    &self,
    execution: &Executed<'_>,
    setup: &SetupConfig,
    capacity: Capacity,
  ) -> Result<Proven, String> {
    let profile = self.profile(execution)?;
    if profile.max_height > capacity.height()?
      || profile.quotient_degree > capacity.quotient_degree
      || u64::try_from(profile.total_rows)
        .map_err(|_error| "row count overflow")?
        > MAX_TOTAL_ROWS
    {
      return Err("CompressGL trace exceeds the admitted capacity".into());
    }
    let started = Instant::now();
    let config = capacity.config(setup, profile.max_height)?;
    let backend = Backend::new(&self.plan, config)?;
    let portable = backend.verifying_key()?;
    let key = portable.to_bytes()?;
    let setup_seconds = started.elapsed().as_secs_f64();
    let started = Instant::now();
    let witness =
      backend.generate(&execution.record, ENTRY, &execution.args)?;
    let trace_seconds = started.elapsed().as_secs_f64();
    let started = Instant::now();
    let proof = backend.prove(ENTRY, &execution.args, &[], witness)?;
    let proving_seconds = started.elapsed().as_secs_f64();
    let started = Instant::now();
    backend.verify(ENTRY, &execution.args, &[], &proof)?;
    let proof = portable.encode_proof(&proof)?;
    let claim = self.claim(execution.input.statement())?;
    VerifyingKey::from_bytes(&key, blake3::hash(&key).as_bytes())?
      .verify_bytes(&claim, &proof)?;
    Ok(Proven {
      key,
      proof,
      claim,
      statement: execution.input.statement().preimage(),
      profile,
      capacity,
      setup: setup.class().label(),
      setup_seconds,
      trace_seconds,
      proving_seconds,
      verification_seconds: started.elapsed().as_secs_f64(),
    })
  }
}

fn arguments(statement: &Statement) -> Vec<Scalar> {
  statement.arguments().into_iter().map(|word| Bn254.from_u64(word)).collect()
}

fn add_cells(
  total: &mut usize,
  height: usize,
  width: usize,
) -> Result<(), String> {
  *total = height
    .checked_mul(width)
    .and_then(|n| total.checked_add(n))
    .ok_or("trace cell count overflow")?;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::config::ProofConfig;
  #[test]
  fn setup_prefix_does_not_change_public_capacity_or_transcript() {
    let setup = SetupConfig::Development { cache_directory: None };
    let cap = Capacity { max_log_height: 6, quotient_degree: 8 };
    let a = cap.config(&setup, 16).unwrap();
    let b = cap.config(&setup, 64).unwrap();
    assert_eq!(a.transcript_seed(), b.transcript_seed());
    assert_eq!(
      a.pcs().verifier_params().to_bytes().unwrap(),
      b.pcs().verifier_params().to_bytes().unwrap()
    );
    assert!(cap.config(&setup, 128).is_err());
    assert!(
      Capacity { max_log_height: 27, quotient_degree: 4 }.height().is_err()
    );
  }
}
