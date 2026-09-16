use super::{
  emission::{Emission, emit},
  *,
};
use crate::{
  hash::Blake3Gate,
  ixby::{
    auth_memory::multi::MultiGate,
    io::PublicLayout,
    ixbf_decode::paged::proof_support::{Driver, driver},
    memory_log::SwitchGate,
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
const MAGIC: [u8; 8] = *b"IXFPCI00";
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
pub struct CompiledConstructorIds {
  pub(super) shape: CircuitShape,
  pub(super) emission: Emission,
  pub(super) drivers: Vec<Box<dyn Driver>>,
  linchecks: Vec<CscCircuit>,
  params: PcsParams,
}
impl CompiledConstructorIds {
  pub fn compile() -> Result<Self> {
    let mut counter = CountingEmitter::new();
    let _ = emit(&mut counter);
    ensure!(counter.required_nu(3)? <= NU, "constructor IDs row capacity");
    let mut b = ShapeBuilder::new(NU);
    let emission = emit(&mut b);
    let shape = b
      .finish()
      .map_err(|e| anyhow::anyhow!("constructor IDs circuit: {e:?}"))?;
    counter.ensure_matches(&shape)?;
    ensure!(
      emission.public.outputs() == PUBLIC_WORDS,
      "constructor IDs public layout"
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
      register!(*slot, g.clone(), ConstructorIdGate);
    }
    for (slot, g) in emission.tree.gates() {
      register!(slot, g.clone(), MultiGate);
    }
    for (slot, table) in emission.tree.compression().tables() {
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
      "constructor IDs driver registry"
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
    let m = union.dense_m();
    ensure!(union.has_element() && m == 28, "constructor IDs PCS geometry");
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
    advice: &ConstructorIdsAdvice,
  ) -> Result<CircuitWitness> {
    let input = self.emission.inputs.assign(&advice.private)?;
    let witness =
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        self.shape.run(&input, &[])
      }))
      .map_err(|_| anyhow::anyhow!("constructor IDs advice rejected"))?;
    ensure!(
      witness.public
        == self.public_template().instantiate(advice.statement.words())?,
      "constructor IDs advice statement"
    );
    Ok(witness)
  }
  pub fn check_advice(&self, advice: &ConstructorIdsAdvice) -> Result<()> {
    self.witness(advice).map(|_| ())
  }
  pub fn prove(&self, advice: &ConstructorIdsAdvice) -> Result<Vec<u8>> {
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
      self.emission.permutation.gate(),
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
    expected: &ConstructorIdsStatement,
    bytes: &[u8],
  ) -> Result<()> {
    self.verify_for_replay(expected, bytes).map(|_| ())
  }
  pub fn verify_for_replay<'a>(
    &'a self,
    expected: &ConstructorIdsStatement,
    bytes: &[u8],
  ) -> Result<VerifiedConstructorIds<'a>> {
    ensure!(bytes.len() as u64 <= MAX_BYTES, "constructor IDs proof size");
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC && codec().serialize(&bundle)? == bytes,
      "constructor IDs proof envelope"
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
    .map_err(|e| anyhow::anyhow!("constructor IDs proof rejected: {e:?}"))?;
    Ok(VerifiedConstructorIds {
      setup: self,
      expected: expected.clone(),
      public,
      bundle,
    })
  }
}
pub struct VerifiedConstructorIds<'a> {
  setup: &'a CompiledConstructorIds,
  expected: ConstructorIdsStatement,
  public: Vec<F128>,
  bundle: Bundle,
}
impl VerifiedConstructorIds<'_> {
  pub fn setup(&self) -> &CompiledConstructorIds {
    self.setup
  }
  pub fn expected(&self) -> &ConstructorIdsStatement {
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
