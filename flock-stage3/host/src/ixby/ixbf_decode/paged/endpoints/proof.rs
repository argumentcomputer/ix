use super::{
  emission::{Emission, emit},
  *,
};
use crate::{
  hash::Blake3Gate,
  ixby::{
    io::PublicLayout,
    ixbf_decode::paged::{
      finalize::FinalizeGate,
      initialize::InitializeGate,
      proof_support::{Driver, driver},
    },
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
const MAGIC: [u8; 8] = *b"IXFPEP00";
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
pub struct CompiledEndpoints {
  profile: FunctionalProfile,
  pub(super) shape: CircuitShape,
  pub(super) emission: Emission,
  pub(super) drivers: Vec<Box<dyn Driver>>,
  linchecks: Vec<CscCircuit>,
  params: PcsParams,
}
impl CompiledEndpoints {
  pub fn compile(profile: FunctionalProfile) -> Result<Self> {
    let mut counter = CountingEmitter::new();
    let _ = emit(&mut counter, &profile)?;
    ensure!(counter.required_nu(3)? <= NU, "endpoint row capacity");
    let mut b = ShapeBuilder::new(NU);
    let emission = emit(&mut b, &profile)?;
    let shape =
      b.finish().map_err(|e| anyhow::anyhow!("endpoint circuit: {e:?}"))?;
    counter.ensure_matches(&shape)?;
    ensure!(
      emission.public.outputs() == PUBLIC_WORDS,
      "endpoint public layout"
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
      register!(*slot, g.clone(), EndpointGate);
    }
    let (slot, g) = emission.initialize.gate();
    register!(slot, g.clone(), InitializeGate);
    let (slot, g) = emission.finalize.gate();
    register!(slot, g.clone(), FinalizeGate);
    for hash in &emission.hashes {
      let gate = hash.block_gate().clone();
      drivers.push(driver(
        hash.block_slot(),
        gate.clone(),
        gate.r1cs(),
        |g, rows, mut dst| {
          dst.elide_padding_writes = false;
          g.generate_witness_into(rows, dst)
        },
      ));
    }
    let hash = &emission.hashes[0];
    let g = *hash.root_gate();
    drivers.push(driver(hash.root_slot(), g, g.r1cs(), |g, rows, mut dst| {
      dst.elide_padding_writes = false;
      g.generate_witness_into(rows, dst)
    }));
    register!(hash.select_slot(), hash.select_gate().clone(), SelectWordsGate);
    register!(
      emission.publish_gate.0,
      emission.publish_gate.1.clone(),
      SelectWordsGate
    );
    for (slot, table) in hash.compression().tables() {
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
    // Equal complete tables may share a registry entry, so register each
    // actual slot only once while validating every proposed driver below.
    for driver in &drivers {
      driver.validate(&shape)?;
    }
    drivers.dedup_by_key(|d| shape.registry_slot(d.slot()));
    ensure!(
      drivers.len() == shape.registry.boolean_types().len()
        && drivers
          .iter()
          .enumerate()
          .all(|(i, d)| shape.registry_slot(d.slot()) == i),
      "endpoint driver registry"
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
    ensure!(!union.has_element(), "endpoint Boolean registry");
    let m = union.dense_m();
    let pcs_profile = LigeritoProfile::Fast128;
    let log_batch_size = embedded_initial_k_or_default(m, pcs_profile);
    let params = PcsParams {
      m,
      profile: pcs_profile,
      log_batch_size,
      log_inv_rate: pcs_profile.log_inv_rate(),
      num_lanes: union.commit_lanes(log_batch_size),
      merkle_hash: HashKind::Blake3,
    };
    Ok(Self { profile, shape, emission, drivers, linchecks, params })
  }
  pub fn profile(&self) -> &FunctionalProfile {
    &self.profile
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
    advice: &EndpointAdvice,
  ) -> Result<CircuitWitness> {
    let input = self.emission.inputs.assign(advice.facts.words())?;
    let witness =
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        self.shape.run(&input, &[])
      }))
      .map_err(|_| anyhow::anyhow!("endpoint advice rejected"))?;
    ensure!(
      witness.public
        == self.public_template().instantiate(advice.statement.words())?,
      "endpoint advice statement"
    );
    Ok(witness)
  }
  pub fn check_advice(&self, advice: &EndpointAdvice) -> Result<()> {
    self.witness(advice).map(|_| ())
  }
  pub fn prove(&self, advice: &EndpointAdvice) -> Result<Vec<u8>> {
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
    let mut ch = FsChallenger::with_chained_blake3(DOMAIN);
    let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &witness.public,
      &self.params,
      boolean,
      vec![],
      &mut ch,
    );
    Ok(codec().serialize(&Bundle { magic: MAGIC, commitment, proof })?)
  }
  pub fn verify(
    &self,
    expected: &EndpointStatement,
    bytes: &[u8],
  ) -> Result<()> {
    self.verify_for_replay(expected, bytes).map(|_| ())
  }
  pub fn verify_for_replay<'a>(
    &'a self,
    expected: &EndpointStatement,
    bytes: &[u8],
  ) -> Result<VerifiedEndpoints<'a>> {
    ensure!(bytes.len() as u64 <= MAX_BYTES, "endpoint proof size");
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC && codec().serialize(&bundle)? == bytes,
      "endpoint proof envelope"
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
    .map_err(|e| anyhow::anyhow!("endpoint proof rejected: {e:?}"))?;
    Ok(VerifiedEndpoints {
      setup: self,
      expected: expected.clone(),
      public,
      bundle,
    })
  }
}
pub struct VerifiedEndpoints<'a> {
  setup: &'a CompiledEndpoints,
  expected: EndpointStatement,
  public: Vec<F128>,
  bundle: Bundle,
}
impl VerifiedEndpoints<'_> {
  pub fn setup(&self) -> &CompiledEndpoints {
    self.setup
  }
  pub fn expected(&self) -> &EndpointStatement {
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
