//! Checked constants for the terminal Aiur program. The policy is finalized
//! after its authorized BN verifier key exists, avoiding a self-key cycle.

use super::{fixed_lines, verifier_anchors};
use crate::{
  aiur_backend::{Bn254, kzg_advice::Policy},
  kzg::{Scalar, VerifierParams},
  recursive::native_field::integer,
};
use aiur::{
  artifact::WidePackage, bytecode::Type, field::FieldBackend,
  hints::HintChannels, maps::MapOverrides, trace::TracePlan,
};
use ark_ec::AffineRepr;
use ark_serialize::CanonicalSerialize;
use std::sync::Arc;

pub const ENTRY: &str = "CompressFinal::verify_v1";

pub struct Program {
  plan: TracePlan<'static, Bn254>,
  maps: MapOverrides<Scalar>,
}

impl Program {
  /// The artifact pin authenticates the compiled policy, stage interval and
  /// pairing anchors. It must come from trusted compilation or configuration.
  pub fn from_bytes(bytes: &[u8], expected: &[u8; 32]) -> Result<Self, String> {
    if blake3::hash(bytes).as_bytes() != expected {
      return Err("terminal Aiur artifact digest mismatch".into());
    }
    let package =
      WidePackage::decode(bytes).map_err(|error| error.to_string())?;
    let trace =
      package.trace.ok_or("terminal artifact has no compiler trace")?;
    let mut program =
      package.program.check_with(Bn254).map_err(|error| error.to_string())?;
    program.track_depth(&trace).map_err(|error| error.to_string())?;
    let plan = TracePlan::new(Arc::new(program), trace)
      .map_err(|error| error.to_string())?;
    plan.program().entry(ENTRY).map_err(|error| error.to_string())?;
    let mut maps = MapOverrides::new();
    aiur::library::u8::register_maps(plan.program(), &mut maps)?;
    Ok(Self { plan, maps })
  }

  pub fn plan(&self) -> &TracePlan<'static, Bn254> {
    &self.plan
  }

  pub fn execute(
    &self,
    inputs: &crate::aiur_backend::kzg_advice::Inputs,
    statement: &[u8; 32],
    stage: u32,
  ) -> Result<aiur::Execution<Bn254>, String> {
    use crate::aiur_backend::{fq, g1, kzg_advice, pairing};
    let mut hints = HintChannels::new();
    aiur::library::u32::register(&mut hints, Bn254)?;
    aiur::library::u64::register(&mut hints, Bn254)?;
    fq::register(&mut hints)?;
    g1::register(&mut hints)?;
    pairing::register(&mut hints)?;
    kzg_advice::register(&mut hints)?;
    inputs.register(&mut hints)?;
    hints.insert_fixed::<0, 1>(
      "kzg.final.stage",
      Type::Tuple { items: vec![] },
      Type::Field,
      move |[]| Ok([Bn254.from_u64(u64::from(stage))]),
    )?;
    self
      .plan
      .program()
      .prepare_hint_channels(&[], &hints)
      .map_err(|error| error.to_string())?
      .with_map_overrides(&self.maps)
      .map_err(|error| error.to_string())?
      .execute(ENTRY, statement_arguments(statement).to_vec())
      .map_err(|error| error.to_string())
  }
}

pub struct Configuration {
  policy_digest: [u8; 32],
  anchors: [u8; 128],
  anchor_coordinates: [[String; 4]; 2],
  parameters_digest: [u8; 32],
  lines: Vec<[Scalar; 51]>,
  min_stage: u32,
  max_stage: u32,
}

impl Configuration {
  /// `parameters` must be independently authenticated. Both the policy and
  /// prepared-line table are checked against exactly those pairing anchors.
  pub fn new(
    policy: &Policy,
    parameters: &VerifierParams,
    max_stage: u32,
    allow_gl: bool,
  ) -> Result<Self, String> {
    let min_stage = if allow_gl { 1 } else { 2 };
    if max_stage < min_stage {
      return Err("invalid final stage interval".into());
    }
    let (_, points) = verifier_anchors(parameters);
    if points.iter().any(AffineRepr::is_zero) {
      return Err("final KZG pairing anchors must be nonzero".into());
    }
    let mut anchors = vec![];
    for point in points {
      point
        .serialize_compressed(&mut anchors)
        .map_err(|error| error.to_string())?;
    }
    let anchors: [u8; 128] = anchors
      .try_into()
      .map_err(|_error| "unexpected G2 anchor encoding width")?;
    if &anchors != policy.anchor_bytes() {
      return Err("final policy and pairing anchors differ".into());
    }
    let lines = fixed_lines(points)?;
    let anchor_coordinates = points.map(|point| {
      [
        point.x.c0.to_string(),
        point.x.c1.to_string(),
        point.y.c0.to_string(),
        point.y.c1.to_string(),
      ]
    });
    let parameters_digest =
      *blake3::hash(&parameters.to_bytes().map_err(|error| error.to_string())?)
        .as_bytes();
    Ok(Self {
      policy_digest: policy.digest(),
      anchors,
      anchor_coordinates,
      parameters_digest,
      lines,
      min_stage,
      max_stage,
    })
  }

  pub fn policy_digest(&self) -> [u8; 32] {
    self.policy_digest
  }

  /// Canonical JSON consumed by the Lean terminal-program exporter.
  pub fn to_json(&self) -> Result<Vec<u8>, String> {
    let words: Vec<_> = self
      .policy_digest
      .as_chunks::<4>()
      .0
      .iter()
      .map(|word| u32::from_le_bytes(*word))
      .collect();
    let lines: Vec<Vec<_>> = self
      .lines
      .iter()
      .map(|row| row.iter().map(|&value| integer(value).to_string()).collect())
      .collect();
    serde_json::to_vec_pretty(&serde_json::json!({
   "format":"ix-aiur-final-configuration-v1","policy_digest":words,
   "anchors":self.anchors.as_slice(),"anchor_coordinates":self.anchor_coordinates,
   "min_stage":self.min_stage,"max_stage":self.max_stage,
   "lines":lines,"policy_blake3":blake3::Hash::from_bytes(self.policy_digest).to_hex().as_str(),
   "parameters_blake3":blake3::Hash::from_bytes(self.parameters_digest).to_hex().as_str(),
   "anchors_blake3":blake3::hash(&self.anchors).to_hex().as_str(),
  })).map_err(|error|error.to_string())
  }

  /// Stage is private advice; the source independently enforces this interval
  /// and authenticates the predecessor's stage through its proven statement.
  pub fn register_stage(
    &self,
    hints: &mut HintChannels<Scalar>,
    stage: u32,
  ) -> Result<(), String> {
    if stage < self.min_stage || stage > self.max_stage {
      return Err("private final stage outside configured interval".into());
    }
    hints.insert_fixed::<0, 1>(
      "kzg.final.stage",
      Type::Tuple { items: vec![] },
      Type::Field,
      move |[]| Ok([Bn254.from_u64(u64::from(stage))]),
    )
  }
}

/// Full 256-bit statement digest, retaining both canonical little-endian halves.
pub fn statement_arguments(statement: &[u8; 32]) -> [Scalar; 2] {
  std::array::from_fn(|index| {
    Scalar(ark_bn254::Fr::from(u128::from_le_bytes(
      statement.as_chunks::<16>().0[index],
    )))
  })
}
