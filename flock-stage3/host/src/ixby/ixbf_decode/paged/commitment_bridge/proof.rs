use super::super::proof_support::{Driver, driver};
use super::{
  emission::{Emission, emit},
  *,
};
use crate::{
  hash::Blake3Gate,
  ixby::{
    io::PublicLayout,
    ixbf_decode::source::{SourceBlockGate, SourcePathGate, SourceWindowGate},
    select::SelectWordsGate,
  },
  sizing::CountingEmitter,
};
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
  prover::{self, UnionSlotProverInput},
  r1cs_hashes::blake3 as flock_blake3,
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};

const MAGIC: [u8; 8] = *b"IXFPCB00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;

#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  bank: u8,
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

/// The setup and all resource bounds are compiled before reading any advice,
/// statements or proof bytes. Verification needs no original source or trace.
pub struct CompiledCommitmentBridge {
  bank: ArtifactDomain,
  pub(super) shape: CircuitShape,
  pub(super) emission: Emission,
  pub(super) drivers: Vec<Box<dyn Driver>>,
  linchecks: Vec<CscCircuit>,
  params: PcsParams,
}
impl CompiledCommitmentBridge {
  pub fn compile(bank: ArtifactDomain) -> Result<Self> {
    let mut counter = CountingEmitter::new();
    let _ = emit(&mut counter, bank);
    ensure!(counter.required_nu(3)? <= NU, "commitment bridge row capacity");
    let mut b = ShapeBuilder::new(NU);
    let emission = emit(&mut b, bank);
    let shape = b
      .finish()
      .map_err(|e| anyhow::anyhow!("commitment bridge circuit: {e:?}"))?;
    counter.ensure_matches(&shape)?;
    ensure!(
      emission.public.outputs() == PUBLIC_WORDS,
      "commitment bridge public layout"
    );
    let mut drivers = Vec::new();
    for (slot, gate) in &emission.gates {
      drivers.push(driver(
        *slot,
        gate.clone(),
        gate.r1cs(),
        CommitmentBridgeGate::generate_witness_into,
      ));
    }
    for source in [&emission.source, &emission.prefixed] {
      let (slot, gate) = source.block_gate();
      drivers.push(driver(
        *slot,
        gate.clone(),
        gate.r1cs(),
        SourceBlockGate::generate_witness_into,
      ));
      let (slot, gate) = source.path_gate();
      drivers.push(driver(
        *slot,
        gate.clone(),
        gate.r1cs(),
        SourcePathGate::generate_witness_into,
      ));
      let (slot, gate) = source.window_gate();
      drivers.push(driver(
        *slot,
        gate.clone(),
        gate.r1cs(),
        SourceWindowGate::generate_witness_into,
      ));
      let (slot, gate) = source.select_gate();
      drivers.push(driver(
        slot,
        gate.clone(),
        gate.r1cs(),
        SelectWordsGate::generate_witness_into,
      ));
    }
    for (slot, table) in emission.source.compression().tables() {
      drivers.push(driver(
        slot,
        Blake3Gate { nu: NU },
        table,
        |_, rows, mut dst| {
          dst.elide_padding_writes = false;
          flock_blake3::generate_witness_batch_major_partial_into(rows, NU, dst)
        },
      ));
    }
    drivers.sort_by_key(|d| shape.registry_slot(d.slot()));
    drivers.dedup_by_key(|d| shape.registry_slot(d.slot()));
    ensure!(
      drivers.len() == shape.registry.boolean_types().len()
        && drivers
          .iter()
          .enumerate()
          .all(|(i, d)| shape.registry_slot(d.slot()) == i),
      "commitment bridge driver registry"
    );
    for driver in &drivers {
      driver.validate(&shape)?;
    }
    let linchecks = shape
      .registry
      .boolean_types()
      .iter()
      .map(|ty| {
        CscCircuit::from_matrices(&ty.a_0, &ty.b_0).with_const_pin(ty.const_pin)
      })
      .collect();
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    ensure!(
      !union.has_element() && union.dense_m() == 22,
      "commitment bridge PCS geometry"
    );
    let profile = LigeritoProfile::Fast128;
    let m = union.dense_m();
    let log_batch_size = embedded_initial_k_or_default(m, profile);
    let params = PcsParams {
      m,
      profile,
      log_batch_size,
      log_inv_rate: profile.log_inv_rate(),
      num_lanes: union.commit_lanes(log_batch_size),
      merkle_hash: HashKind::Blake3,
    };
    Ok(Self { bank, shape, emission, drivers, linchecks, params })
  }
  pub fn bank(&self) -> ArtifactDomain {
    self.bank
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
    self.bank.transcript_domain()
  }
  pub fn lincheck_circuits(&self) -> Vec<&dyn LincheckCircuit> {
    self.linchecks.iter().map(|c| c as &dyn LincheckCircuit).collect()
  }
  pub(super) fn witness(
    &self,
    advice: &CommitmentBridgeAdvice,
  ) -> Result<CircuitWitness> {
    let input = self.emission.inputs.assign(&advice.private)?;
    let witness =
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        self.shape.run(&input, &[])
      }))
      .map_err(|_| anyhow::anyhow!("commitment bridge advice rejected"))?;
    ensure!(
      witness.public
        == self.public_template().instantiate(advice.statement.words())?,
      "commitment bridge advice statement"
    );
    Ok(witness)
  }
  pub fn check_advice(&self, advice: &CommitmentBridgeAdvice) -> Result<()> {
    self.witness(advice).map(|_| ())
  }
  pub fn prove(&self, advice: &CommitmentBridgeAdvice) -> Result<Vec<u8>> {
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
    let mut ch = FsChallenger::with_chained_blake3(self.transcript_domain());
    let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &witness.public,
      &self.params,
      boolean,
      vec![],
      &mut ch,
    );
    Ok(codec().serialize(&Bundle {
      magic: MAGIC,
      bank: self.bank as u8,
      commitment,
      proof,
    })?)
  }
  pub fn verify(
    &self,
    expected: &CommitmentBridgeStatement,
    bytes: &[u8],
  ) -> Result<()> {
    self.verify_for_replay(expected, bytes).map(|_| ())
  }
  pub fn verify_for_replay<'a>(
    &'a self,
    expected: &CommitmentBridgeStatement,
    bytes: &[u8],
  ) -> Result<VerifiedCommitmentBridge<'a>> {
    ensure!(bytes.len() as u64 <= MAX_BYTES, "commitment bridge proof size");
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC
        && bundle.bank == self.bank as u8
        && codec().serialize(&bundle)? == bytes,
      "commitment bridge proof envelope"
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
    .map_err(|e| anyhow::anyhow!("commitment bridge proof rejected: {e:?}"))?;
    Ok(VerifiedCommitmentBridge {
      setup: self,
      expected: expected.clone(),
      public,
      bundle,
    })
  }
}
/// Verified native projection; recursion must constrain the complete verifier.
pub struct VerifiedCommitmentBridge<'a> {
  setup: &'a CompiledCommitmentBridge,
  expected: CommitmentBridgeStatement,
  public: Vec<F128>,
  bundle: Bundle,
}
impl VerifiedCommitmentBridge<'_> {
  pub fn setup(&self) -> &CompiledCommitmentBridge {
    self.setup
  }
  pub fn expected(&self) -> &CommitmentBridgeStatement {
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
