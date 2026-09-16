use super::super::proof_support::{Driver, driver};
use super::{
  slots::{Emission, emit},
  *,
};
use crate::{
  hash::Blake3Gate,
  ixby::{
    auth_memory::multi::MultiGate,
    io::PublicLayout,
    ixbf_decode::source::{SourceBlockGate, SourcePathGate, SourceWindowGate},
    memory_log::SwitchGate,
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
  prover::{self, UnionElementSlotInput, UnionSlotProverInput},
  r1cs_hashes::blake3 as flock_blake3,
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};

const MAGIC: [u8; 8] = *b"IXFPSB00";
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
pub struct CompiledSourceBytes {
  bank: SourceBank,
  pub(super) shape: CircuitShape,
  pub(super) emission: Emission,
  pub(super) drivers: Vec<Box<dyn Driver>>,
  linchecks: Vec<CscCircuit>,
  params: PcsParams,
}
impl CompiledSourceBytes {
  pub fn compile(bank: SourceBank) -> Result<Self> {
    let mut counter = CountingEmitter::new();
    let _ = emit(&mut counter, bank);
    ensure!(counter.required_nu(3)? <= NU, "source bytes row capacity");
    let mut b = ShapeBuilder::new(NU);
    let emission = emit(&mut b, bank);
    let shape =
      b.finish().map_err(|e| anyhow::anyhow!("source bytes circuit: {e:?}"))?;
    counter.ensure_matches(&shape)?;
    ensure!(
      emission.public.outputs() == PUBLIC_WORDS,
      "source bytes public layout"
    );
    let mut drivers = Vec::new();
    for (slot, gate) in &emission.gates {
      drivers.push(driver(
        *slot,
        gate.clone(),
        gate.r1cs(),
        SourceBytesGate::generate_witness_into,
      ));
    }
    for (slot, gate) in emission.memory.gates() {
      drivers.push(driver(
        slot,
        gate.clone(),
        gate.r1cs(),
        MultiGate::generate_witness_into,
      ));
    }
    let (slot, gate) = emission.source.block_gate();
    drivers.push(driver(
      *slot,
      gate.clone(),
      gate.r1cs(),
      SourceBlockGate::generate_witness_into,
    ));
    let (slot, gate) = emission.source.path_gate();
    drivers.push(driver(
      *slot,
      gate.clone(),
      gate.r1cs(),
      SourcePathGate::generate_witness_into,
    ));
    let (slot, gate) = emission.source.window_gate();
    drivers.push(driver(
      *slot,
      gate.clone(),
      gate.r1cs(),
      SourceWindowGate::generate_witness_into,
    ));
    let (slot, gate) = emission.source.select_gate();
    drivers.push(driver(
      slot,
      gate.clone(),
      gate.r1cs(),
      SelectWordsGate::generate_witness_into,
    ));
    for (slot, table) in emission.memory.compression().tables() {
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
    ensure!(
      drivers.len() == shape.registry.boolean_types().len()
        && drivers
          .iter()
          .enumerate()
          .all(|(i, d)| shape.registry_slot(d.slot()) == i),
      "source bytes driver registry"
    );
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
      union.has_element() && union.dense_m() == 24,
      "source bytes PCS geometry"
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
  pub fn bank(&self) -> SourceBank {
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
    self.bank.domain()
  }
  pub fn lincheck_circuits(&self) -> Vec<&dyn LincheckCircuit> {
    self.linchecks.iter().map(|c| c as &dyn LincheckCircuit).collect()
  }
  pub(super) fn witness(
    &self,
    advice: &SourceBytesAdvice,
  ) -> Result<CircuitWitness> {
    let input = self.emission.inputs.assign(&advice.private)?;
    let witness =
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        self.shape.run(&input, &[])
      }))
      .map_err(|_| anyhow::anyhow!("source bytes advice rejected"))?;
    ensure!(
      witness.public
        == self.public_template().instantiate(advice.statement.words())?,
      "source bytes advice statement"
    );
    Ok(witness)
  }
  pub fn check_advice(&self, advice: &SourceBytesAdvice) -> Result<()> {
    self.witness(advice).map(|_| ())
  }
  pub fn prove(&self, advice: &SourceBytesAdvice) -> Result<Vec<u8>> {
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
    let (slot, gate) = self.emission.memory.permutation().gate();
    let rows = witness.rows::<SwitchGate>(slot);
    let element =
      UnionElementSlotInput::new(move |dst| gate.fill_witness(rows, NU, dst));
    let mut ch = FsChallenger::with_chained_blake3(self.transcript_domain());
    let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &witness.public,
      &self.params,
      boolean,
      vec![element],
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
    expected: &SourceBytesStatement,
    bytes: &[u8],
  ) -> Result<()> {
    self.verify_for_replay(expected, bytes).map(|_| ())
  }
  pub fn verify_for_replay<'a>(
    &'a self,
    expected: &SourceBytesStatement,
    bytes: &[u8],
  ) -> Result<VerifiedSourceBytes<'a>> {
    ensure!(bytes.len() as u64 <= MAX_BYTES, "source bytes proof size");
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC
        && bundle.bank == self.bank as u8
        && codec().serialize(&bundle)? == bytes,
      "source bytes proof envelope"
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
    .map_err(|e| anyhow::anyhow!("source bytes proof rejected: {e:?}"))?;
    Ok(VerifiedSourceBytes {
      setup: self,
      expected: expected.clone(),
      public,
      bundle,
    })
  }
}
/// Verified native projection; recursion must constrain the complete verifier.
pub struct VerifiedSourceBytes<'a> {
  setup: &'a CompiledSourceBytes,
  expected: SourceBytesStatement,
  public: Vec<F128>,
  bundle: Bundle,
}
impl VerifiedSourceBytes<'_> {
  pub fn setup(&self) -> &CompiledSourceBytes {
    self.setup
  }
  pub fn expected(&self) -> &SourceBytesStatement {
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
