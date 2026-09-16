use super::*;
use crate::ixby::{
  io::PublicLayout, ixbf_decode::paged::proof_support::Driver,
  memory_log::SwitchGate,
};
use crate::sizing::CountingEmitter;
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, CircuitWitness, ShapeBuilder},
  hash::HashKind,
  lincheck::{CscCircuit, LincheckCircuit},
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionElementSlotInput, UnionSlotProverInput},
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};
const MAGIC: [u8; 8] = *b"IXFPGX00";
const MAX_BYTES: u64 = 16 * 1024 * 1024;
#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}
fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_BYTES)
    .reject_trailing_bytes()
}
pub struct CompiledPagedExecution {
  pub(super) shape: CircuitShape,
  pub(super) emission: BatchEmission,
  pub(super) drivers: Vec<Box<dyn Driver>>,
  linchecks: Vec<CscCircuit>,
  params: PcsParams,
}
impl CompiledPagedExecution {
  pub fn compile(class: BatchClass) -> Result<Self> {
    let mut counter = CountingEmitter::new();
    let _ = emit_batch(&mut counter, class)?;
    ensure!(
      counter.required_nu(3)? <= class.nu(),
      "paged execution row capacity"
    );
    let mut b = ShapeBuilder::new(class.nu());
    let emission = emit_batch(&mut b, class)?;
    let shape = b
      .finish()
      .map_err(|e| anyhow::anyhow!("paged execution circuit: {e:?}"))?;
    counter.ensure_matches(&shape)?;
    ensure!(
      emission.public.outputs() == PUBLIC_WORDS,
      "paged execution public layout"
    );
    let drivers = proof_drivers::drivers(&emission, &shape)?;
    let linchecks = shape
      .registry
      .boolean_types()
      .iter()
      .map(|ty| {
        CscCircuit::from_matrices(&ty.a_0, &ty.b_0).with_const_pin(ty.const_pin)
      })
      .collect();
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    let m = union.dense_m();
    ensure!(
      union.has_element() && (22..=35).contains(&m),
      "paged execution PCS geometry"
    );
    let profile = LigeritoProfile::Fast128;
    let log_batch_size = embedded_initial_k_or_default(m, profile);
    let params = PcsParams {
      m,
      profile,
      log_batch_size,
      log_inv_rate: profile.log_inv_rate(),
      num_lanes: union.commit_lanes(log_batch_size),
      merkle_hash: HashKind::Blake3,
    };
    Ok(Self { shape, emission, drivers, linchecks, params })
  }
  pub fn class(&self) -> BatchClass {
    self.emission.class
  }
  pub fn verifier_shape(&self) -> &CircuitShape {
    &self.shape
  }
  pub fn public_template(&self) -> &PublicLayout {
    &self.emission.public
  }
  pub fn pcs_params(&self) -> &PcsParams {
    &self.params
  }
  pub fn transcript_domain(&self) -> &'static [u8] {
    self.emission.class.transcript_domain()
  }
  pub fn lincheck_circuits(&self) -> Vec<&dyn LincheckCircuit> {
    self.linchecks.iter().map(|c| c as &dyn LincheckCircuit).collect()
  }
  pub(super) fn witness(&self, advice: &BatchAdvice) -> Result<CircuitWitness> {
    let statement = ExecutionStatement::from_words(&advice.expected)?;
    let input = self.emission.inputs.assign(&advice.private)?;
    let witness =
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        self.shape.run(&input, &[])
      }))
      .map_err(|_| anyhow::anyhow!("paged execution advice rejected"))?;
    ensure!(
      witness.public
        == self.public_template().instantiate(statement.words())?,
      "paged execution advice statement"
    );
    Ok(witness)
  }
  pub fn check_advice(&self, advice: &BatchAdvice) -> Result<()> {
    self.witness(advice).map(|_| ())
  }
  pub fn prove(&self, advice: &BatchAdvice) -> Result<Vec<u8>> {
    let witness = self.witness(advice)?;
    self.prove_rows(
      &witness,
      self.drivers.iter().map(|d| d.prover(&witness)).collect(),
    )
  }
  pub(super) fn prove_rows(
    &self,
    witness: &CircuitWitness,
    boolean: Vec<UnionSlotProverInput<'_>>,
  ) -> Result<Vec<u8>> {
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut gates = vec![
      self.emission.order.permutation().gate(),
      self.emission.memory.log().permutation().gate(),
    ];
    if let Some(tree) = &self.emission.tree {
      gates.push(tree.permutation().gate());
    }
    let nu = self.emission.class.nu();
    gates.sort_by_key(|(slot, _)| self.shape.registry_slot(*slot));
    let elements = gates
      .into_iter()
      .map(|(slot, g)| {
        let rows = witness.rows::<SwitchGate>(slot);
        UnionElementSlotInput::new(move |dst| g.fill_witness(rows, nu, dst))
      })
      .collect();
    let mut ch = FsChallenger::with_chained_blake3(self.transcript_domain());
    let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &witness.public,
      &self.params,
      boolean,
      elements,
      &mut ch,
    );
    Ok(codec().serialize(&Bundle { magic: MAGIC, commitment, proof })?)
  }
  pub fn verify(
    &self,
    expected: &ExecutionStatement,
    bytes: &[u8],
  ) -> Result<()> {
    self.verify_for_replay(expected, bytes).map(|_| ())
  }
  pub fn verify_for_replay<'a>(
    &'a self,
    expected: &ExecutionStatement,
    bytes: &[u8],
  ) -> Result<VerifiedPagedExecution<'a>> {
    ensure!(bytes.len() as u64 <= MAX_BYTES, "paged execution proof size");
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC && codec().serialize(&bundle)? == bytes,
      "paged execution proof envelope"
    );
    let public = self.public_template().instantiate(expected.words())?;
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut ch = FsChallenger::with_chained_blake3(self.transcript_domain());
    verifier::verify_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &public,
      &self.lincheck_circuits(),
      &bundle.commitment,
      &bundle.proof,
      &self.params,
      &mut ch,
    )
    .map_err(|e| anyhow::anyhow!("paged execution proof rejected: {e:?}"))?;
    Ok(VerifiedPagedExecution {
      setup: self,
      expected: expected.clone(),
      public,
      bundle,
    })
  }
}
pub struct VerifiedPagedExecution<'a> {
  setup: &'a CompiledPagedExecution,
  expected: ExecutionStatement,
  public: Vec<F128>,
  bundle: Bundle,
}
impl VerifiedPagedExecution<'_> {
  pub fn setup(&self) -> &CompiledPagedExecution {
    self.setup
  }
  pub fn expected(&self) -> &ExecutionStatement {
    &self.expected
  }
  pub fn public_values(&self) -> &[F128] {
    &self.public
  }
  pub fn commitment(&self) -> &Commitment {
    &self.bundle.commitment
  }
  pub fn proof(&self) -> &R1csProofCircuitMerged {
    &self.bundle.proof
  }
}
