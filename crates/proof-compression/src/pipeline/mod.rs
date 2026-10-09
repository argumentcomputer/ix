//! Compression stages for aggregated Ix certificates.
//!
//! The caller supplies the trusted aggregate key, expected outer claim and
//! proving parameters. No certificate, filesystem layout or development SRS
//! is built into these stages. Verifiers returned by local construction must
//! be authenticated before use elsewhere; a prover-supplied key is not trusted.
mod codec;
mod fixed;
mod root;
mod setup;
#[cfg(test)]
mod tests;
mod wrap;

pub use fixed::FixedRoot;
pub use root::prepare_root;
pub use setup::setup;
pub use wrap::{
  RecursiveProof, RecursiveStage, RecursiveVerifier, prepare_recursive,
};

use crate::foreign::{GoldilocksCircuit, KzgCircuitExt};
use crate::fri::{self, VerifierKey};
use crate::kzg::{KzgConfig, Scalar, Srs, VerifierParams};
use multi_stark::config::ProofConfig;
use multi_stark::lookup::LookupValues;
use multi_stark::plonkish::{Assignment, Circuit, MultiStarkCircuit};
use multi_stark::prover::{Proof, Stage1};
use multi_stark::system::{ProverKey, System, SystemWitness};
use multi_stark::traits::{Algebra, Field, Pcs};
use multi_stark::types::{GoldilocksBlake3Config, Val};
use p3_field::PrimeField64;
use p3_matrix::Matrix;
use std::sync::Arc;

pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

// System::new asserts these conditions. Check caller-selected parameters
// before committing matrices so an unsupported configuration is an error.
fn validate_config<SC: ProofConfig>(
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

/// A checked circuit and its witness, ready for lowering and proving.
/// Keeping preparation separate lets callers inspect costs and choose an SRS
/// and partition height before allocating prover data.
pub struct Prepared<F: Field> {
  circuit: Circuit<F>,
  assignment: Assignment<F>,
}

impl<F: Field> Prepared<F> {
  pub fn circuit(&self) -> &Circuit<F> {
    &self.circuit
  }

  pub fn public_values(&self) -> &[F] {
    self.assignment.public_values()
  }
}

/// The lowering's complete claim template, including all activation anchors.
/// Only public-value cells may be replaced during verification.
#[derive(serde::Serialize, serde::Deserialize)]
struct Statement<F> {
  template: Vec<Vec<F>>,
  locations: Vec<(usize, usize)>,
}

impl<F: Field> Statement<F> {
  fn from_lowered(
    circuit: &MultiStarkCircuit<F>,
    count: usize,
  ) -> Result<Self> {
    let template = circuit.claims(&vec![F::ZERO; count])?;
    // MultiStarkCircuit::claims places the anchor first, then public cells.
    // Obtain every other claim (partition/hash activation) from the lowering.
    let locations: Vec<_> = (1..=count).map(|i| (i, 3)).collect();
    if template.len() <= count
      || template[..=count].iter().any(|row| row.len() != 4)
    {
      return Err("unsupported lowering claim schema".into());
    }
    Ok(Self { template, locations })
  }

  fn claims(&self, public: &[F]) -> Result<Vec<Vec<F>>> {
    if public.len() != self.locations.len() {
      return Err("unexpected public statement length".into());
    }
    let mut claims = self.template.clone();
    for (&(row, col), &value) in self.locations.iter().zip(public) {
      claims[row][col] = value;
    }
    Ok(claims)
  }
}

/// Trusted verifier for the first, FRI-compressed stage.
pub struct FriVerifier {
  key: VerifierKey,
  statement: Statement<Val>,
}

impl FriVerifier {
  fn schema(&self) -> fri::Statement<fri::StatementSlot> {
    let mut schema = fri::Statement {
      claims: self
        .statement
        .template
        .iter()
        .map(|row| {
          row
            .iter()
            .copied()
            .map(fri::StatementSlot::Constant)
            .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>(),
      messages: vec![],
    };
    for &(row, col) in &self.statement.locations {
      schema.claims[row][col] = fri::StatementSlot::Public;
    }
    schema
  }

  pub fn verify(
    &self,
    proof: &Proof<GoldilocksBlake3Config>,
    expected: &[Val],
  ) -> Result<()> {
    let claims = self.statement.claims(expected)?;
    self
      .key
      .system()
      .verify_multiple_claims(
        &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        proof,
      )
      .map_err(|e| format!("FRI compression proof: {e:?}"))?;
    Ok(())
  }
}

impl Prepared<Val> {
  /// Prove the root-verifier circuit using caller-selected FRI parameters.
  pub fn prove_fri(
    self,
    config: GoldilocksBlake3Config,
    max_height: usize,
  ) -> Result<(FriVerifier, Proof<GoldilocksBlake3Config>)> {
    use multi_stark::config::StarkGenericConfig;
    fri::validate_parameters(
      multi_stark::types::CommitmentParameters {
        log_blowup: config.log_blowup(),
        cap_height: config.cap_height(),
      },
      config.fri_parameters(),
    )?;
    let compiled = self
      .circuit
      .lower_to_multi_stark_with_max_height(Val::ONE, max_height)?;
    let statement = Statement::from_lowered(
      &compiled,
      self.assignment.public_values().len(),
    )?;
    let claims = statement.claims(self.assignment.public_values())?;
    let definitions = compiled.circuit_inputs();
    validate_config(&config, &definitions)?;
    let traces = compiled.traces(&self.assignment)?;
    drop(compiled);
    drop(self.assignment);
    let (system, key) = System::new(config, definitions);
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(traces, &system),
    );
    system
      .verify_multiple_claims(&refs, &proof)
      .map_err(|e| format!("new FRI proof: {e:?}"))?;
    Ok((FriVerifier { key: VerifierKey::new(system), statement }, proof))
  }
}

/// Prepare a FRI verifier over the BLS12-381 scalar field. The statement and
/// all activation anchors come from the trusted previous stage's verifier.
pub fn prepare_kzg(
  verifier: &FriVerifier,
  proof: &Proof<GoldilocksBlake3Config>,
  expected: &[Val],
  limits: fri::VerifierLimits,
) -> Result<Prepared<Scalar>> {
  verifier.verify(proof, expected)?;
  let claims = verifier.statement.claims(expected)?;
  let profile = fri::ProofProfile {
    envelope: fri::Envelope::Ordinary,
    active: proof.active.clone(),
    log_degrees: proof.log_degrees.clone(),
    claim_lengths: claims.iter().map(Vec::len).collect(),
    message_lengths: vec![],
    max_field_retries: fri::DEFAULT_FIELD_RETRIES,
  };
  let plan = fri::VerifierPlan::validate(&verifier.key, profile, limits)?;
  let schema = verifier.schema();
  let (circuit, inputs) = plan.build(schema, Default::default())?;
  let expanded = plan
    .expand_witness(fri::ProofEnvelope::Ordinary { proof, claims: &claims })?;
  let mut witness = circuit.witness();
  inputs.assign_statement(
    &mut witness,
    &fri::Statement { claims, messages: vec![] },
  )?;
  expanded.assign_proof(&mut witness, &inputs)?;
  let assignment = witness.generate()?;
  let foreign = GoldilocksCircuit::new_preallocated(&circuit);
  let mut witness = foreign.circuit.witness();
  foreign.assign(&assignment, &mut witness)?;
  let assignment = witness.generate()?;
  Ok(Prepared { circuit: foreign.circuit, assignment })
}

/// Trusted verifier for a scalar-field compression stage. It retains only
/// verification parameters, never the SRS proving powers or fixed matrices.
pub struct KzgVerifier {
  system: System<KzgConfig>,
  params: VerifierParams,
  statement: Statement<Scalar>,
}

impl KzgVerifier {
  fn codec(&self) -> Result<crate::kzg::compact::FixedProofCodec> {
    let logs = self
      .system
      .circuits
      .iter()
      .map(|c| {
        u8::try_from(c.preprocessed_height.ilog2())
          .expect("validated trace height")
      })
      .collect::<Vec<_>>();
    Ok(crate::kzg::compact::FixedProofCodec::new(&self.system, &logs)?)
  }

  /// Fixed-shape transport under this trusted key; encoding is not verification.
  pub fn encode_proof(&self, proof: &Proof<KzgConfig>) -> Result<Vec<u8>> {
    Ok(self.codec()?.encode(proof)?)
  }

  pub fn verify_bytes(&self, bytes: &[u8], expected: &[Scalar]) -> Result<()> {
    self.verify(&self.codec()?.decode(bytes)?, expected)
  }

  pub fn verify(
    &self,
    proof: &Proof<KzgConfig>,
    expected: &[Scalar],
  ) -> Result<()> {
    let claims = self.statement.claims(expected)?;
    self
      .system
      .verify_multiple_claims(
        &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        proof,
      )
      .map_err(|e| format!("KZG compression proof: {e:?}"))?;
    Ok(())
  }
}

impl Prepared<Scalar> {
  /// Parameters must have trusted provenance and pass Srs::validate before
  /// use. Partitioning is bounded by both max_height and the supplied SRS.
  pub fn prove_kzg(
    self,
    srs: Arc<Srs>,
    max_height: usize,
  ) -> Result<(KzgVerifier, Proof<KzgConfig>)> {
    if srs.max_len() < 2
      || !srs.max_len().is_power_of_two()
      || srs.degree_keys.len() != srs.max_len().ilog2() as usize + 1
    {
      return Err("invalid SRS shape".into());
    }
    if max_height < 2
      || !max_height.is_power_of_two()
      || max_height > srs.max_len()
    {
      return Err(
        "partition height must be a power of two within the SRS range".into(),
      );
    }
    let compiled = self
      .circuit
      .lower_to_multi_stark_sharded(Scalar::ONE, max_height)?
      .merge_table_traces(max_height)?;
    let statement = Statement::from_lowered(
      &compiled,
      self.assignment.public_values().len(),
    )?;
    let claims = statement.claims(self.assignment.public_values())?;
    let params = VerifierParams::from_srs(&srs);
    let config =
      KzgConfig::new(srs, 2).with_streaming_lookups().with_streaming_quotient();
    // Commit one partition at a time. Lookup traces are reconstructed from
    // committed columns, so neither fixed evaluations nor expanded lookup
    // messages need to remain resident alongside all prover coefficients.
    let source = compiled.trace_shards(&self.assignment)?;
    let count = compiled.num_circuits();
    let mut circuits = Vec::with_capacity(count);
    let mut fixed = Vec::with_capacity(count);
    let mut main = Vec::with_capacity(count);
    let mut logs = Vec::with_capacity(count);
    let mut lookups = Vec::with_capacity(count);
    for i in 0..count {
      let definition = compiled
        .kzg_circuit_input(i, params.max_len(), 2)?
        .ok_or("missing compression circuit")?;
      validate_config(&config, std::slice::from_ref(&definition))?;
      let (mut local, key) =
        System::new_without_preprocessed(config.clone(), [definition]);
      let circuit = local.circuits.remove(0);
      fixed.push(key.preprocessed_data.ok_or("missing fixed columns")?);
      let trace = source.trace(i)?;
      let height = trace.height();
      logs.push(height.ilog2() as usize);
      lookups.push(LookupValues::shape_only(
        height,
        &circuit.graph.lookups.iter().map(|l| l.args.len()).collect::<Vec<_>>(),
      ));
      let (_, data) = config
        .pcs()
        .commit(vec![(config.pcs().natural_domain_for_degree(height), trace)]);
      main.push(data);
      circuits.push(circuit);
    }
    drop(compiled);
    drop(self.assignment);
    let (fixed_commitment, fixed_data) =
      crate::kzg::pcs::KzgProverData::concatenate(fixed);
    let (stage_1_trace_commit, stage_1_trace_data) =
      crate::kzg::pcs::KzgProverData::concatenate(main);
    let mut system = System {
      config,
      circuits,
      preprocessed_commit: Some(fixed_commitment),
      preprocessed_indices: (0..count).map(Some).collect(),
    };
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = system.prove_committed(
      &ProverKey { preprocessed_data: Some(fixed_data) },
      &refs,
      Stage1 {
        active: vec![true; count],
        active_indices: (0..count).collect(),
        log_degrees: logs,
        stage_1_trace_commit,
        stage_1_trace_data,
        lookups,
      },
    );
    system
      .verify_multiple_claims(&refs, &proof)
      .map_err(|e| format!("new KZG proof: {e:?}"))?;
    system.config = KzgConfig::verifier_only(params.clone(), 2);
    Ok((KzgVerifier { system, params, statement }, proof))
  }
}

fn scalar_statement(expected: &[Val]) -> Vec<Scalar> {
  expected.iter().map(|v| Scalar::from_u64(v.as_canonical_u64())).collect()
}
