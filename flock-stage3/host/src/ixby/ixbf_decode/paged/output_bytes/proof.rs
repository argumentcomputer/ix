use super::{
  emission::{Emission, emit},
  *,
};
use crate::{
  equality::{
    F128EqualityGate, build_f128_equality_r1cs,
    generate_f128_equality_witness_into,
  },
  hash::Blake3Gate,
  ixby::{
    auth_memory::{MemoryGate, multi::MultiGate},
    io::PublicLayout,
    ixbf_decode::{
      paged::proof_support::{Driver, driver},
      source::{SourceBlockGate, SourcePathGate, SourceWindowGate},
      stream::StreamGate,
    },
    memory_log::{AuditGate, SwitchGate},
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
const MAGIC: [u8; 8] = *b"IXFPOB00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
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
pub struct CompiledOutputBytes {
  pub(super) shape: CircuitShape,
  pub(super) emission: Emission,
  pub(super) drivers: Vec<Box<dyn Driver>>,
  linchecks: Vec<CscCircuit>,
  params: PcsParams,
}
impl CompiledOutputBytes {
  pub fn compile() -> Result<Self> {
    let mut counter = CountingEmitter::new();
    let _ = emit(&mut counter);
    ensure!(counter.required_nu(3)? <= NU, "output bytes row capacity");
    let mut b = ShapeBuilder::new(NU);
    let emission = emit(&mut b);
    let shape =
      b.finish().map_err(|e| anyhow::anyhow!("output bytes circuit: {e:?}"))?;
    counter.ensure_matches(&shape)?;
    ensure!(
      emission.public.outputs() == PUBLIC_WORDS,
      "output bytes public layout"
    );
    let mut drivers = Vec::new();
    macro_rules! register {
      ($slot:expr,$gate:expr,$ty:ty) => {{
        let g = $gate;
        let t = g.r1cs();
        drivers.push(driver($slot, g, t, <$ty>::generate_witness_into));
      }};
    }
    for (slot, g) in &emission.gates {
      register!(*slot, g.clone(), OutputBytesGate);
    }
    for (slot, g) in &emission.controls {
      register!(*slot, g.clone(), StreamGate);
    }
    let (slot, g) = emission.source.block_gate();
    register!(*slot, g.clone(), SourceBlockGate);
    let (slot, g) = emission.source.path_gate();
    register!(*slot, g.clone(), SourcePathGate);
    let (slot, g) = emission.source.window_gate();
    register!(*slot, g.clone(), SourceWindowGate);
    let (slot, g) = emission.source.select_gate();
    register!(slot, g.clone(), SelectWordsGate);
    drivers.push(driver(
      emission.equal,
      F128EqualityGate { nu: NU },
      build_f128_equality_r1cs(NU),
      |_, rows, mut dst| {
        dst.elide_padding_writes = false;
        generate_f128_equality_witness_into(rows, NU, dst)
      },
    ));
    for (slot, g) in emission.tree.gates() {
      register!(slot, g.clone(), MultiGate);
    }
    for (slot, g) in emission.log.memory().gates() {
      register!(slot, g.clone(), MemoryGate);
    }
    let (slot, g) = emission.log.audit_gate();
    register!(slot, g.clone(), AuditGate);
    for (slot, table) in emission.log.memory().compression().tables() {
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
      "output bytes driver registry"
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
    let m = union.dense_m();
    ensure!(union.has_element() && m == 26, "output bytes PCS geometry");
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
    DOMAIN
  }
  pub fn lincheck_circuits(&self) -> Vec<&dyn LincheckCircuit> {
    self.linchecks.iter().map(|c| c as &dyn LincheckCircuit).collect()
  }
  pub(super) fn witness(
    &self,
    advice: &OutputBytesAdvice,
  ) -> Result<CircuitWitness> {
    let input = self.emission.inputs.assign(&advice.private)?;
    let witness =
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        self.shape.run(&input, &[])
      }))
      .map_err(|_| anyhow::anyhow!("output bytes advice rejected"))?;
    ensure!(
      witness.public
        == self.public_template().instantiate(advice.statement.words())?,
      "output bytes advice statement"
    );
    Ok(witness)
  }
  pub fn check_advice(&self, advice: &OutputBytesAdvice) -> Result<()> {
    self.witness(advice).map(|_| ())
  }
  pub fn prove(&self, advice: &OutputBytesAdvice) -> Result<Vec<u8>> {
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
    let mut gates = [
      self.emission.log.permutation().gate(),
      self.emission.tree.permutation().gate(),
    ];
    gates.sort_by_key(|(slot, _)| self.shape.registry_slot(*slot));
    let elements = gates
      .into_iter()
      .map(|(slot, g)| {
        let rows = witness.rows::<SwitchGate>(slot);
        UnionElementSlotInput::new(move |dst| g.fill_witness(rows, NU, dst))
      })
      .collect();
    let mut ch = FsChallenger::with_chained_blake3(DOMAIN);
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
    expected: &OutputBytesStatement,
    bytes: &[u8],
  ) -> Result<()> {
    self.verify_for_replay(expected, bytes).map(|_| ())
  }
  pub fn verify_for_replay<'a>(
    &'a self,
    expected: &OutputBytesStatement,
    bytes: &[u8],
  ) -> Result<VerifiedOutputBytes<'a>> {
    ensure!(bytes.len() as u64 <= MAX_BYTES, "output bytes proof size");
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC && codec().serialize(&bundle)? == bytes,
      "output bytes proof envelope"
    );
    let public = self.public_template().instantiate(expected.words())?;
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut ch = FsChallenger::with_chained_blake3(DOMAIN);
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
    .map_err(|e| anyhow::anyhow!("output bytes proof rejected: {e:?}"))?;
    Ok(VerifiedOutputBytes {
      setup: self,
      expected: expected.clone(),
      public,
      bundle,
    })
  }
}
pub struct VerifiedOutputBytes<'a> {
  setup: &'a CompiledOutputBytes,
  expected: OutputBytesStatement,
  public: Vec<F128>,
  bundle: Bundle,
}
impl VerifiedOutputBytes<'_> {
  pub fn setup(&self) -> &CompiledOutputBytes {
    self.setup
  }
  pub fn expected(&self) -> &OutputBytesStatement {
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
