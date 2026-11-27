//! Checked constants for the terminal Aiur program. The policy is finalized
//! after its authorized BN verifier key exists, avoiding a self-key cycle.

use super::{fixed_lines, fixed_lines_bls12_381, verifier_anchors_for};
use crate::{
  aiur_backend::{AiurCurve, AiurField, Bn254, kzg_advice::Policy},
  kzg::{
    Curve, CurveScalar, KzgCurve, Scalar, VerifierParams,
    curve::{Bls12381 as Bls12381Curve, Bn254 as Bn254Curve},
  },
  recursive::native_field::integer,
};
use aiur::{
  artifact::WidePackage,
  budget::{RecordPool, RecordReservation},
  bytecode::Type,
  field::FieldBackend,
  hints::HintChannels,
  maps::MapOverrides,
  trace::TracePlan,
};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use std::sync::Arc;

pub const ENTRY: &str = "CompressFinal::verify_v1";
pub const ACCUMULATOR_ENTRY: &str = "CompressFinal::verify_accumulator_v1";
/// Terminal over the fixed-key narrow stage: one fixed predecessor key and
/// stage (`CompressFinalNarrow`).
pub const NARROW_ACCUMULATOR_ENTRY: &str =
  "CompressFinalNarrow::verify_accumulator_v1";
pub const ACCUMULATOR_WORDS: usize = 18;
pub const BLS12_381_ACCUMULATOR_WORDS: usize = 22;

pub struct Program<F: AiurField = Bn254> {
  plan: TracePlan<'static, F>,
  maps: MapOverrides<F::Element>,
  entry: &'static str,
}

impl Program<Bn254> {
  /// The artifact pin authenticates the compiled policy, stage interval and
  /// pairing anchors. It must come from trusted compilation or configuration.
  pub fn from_bytes(bytes: &[u8], expected: &[u8; 32]) -> Result<Self, String> {
    Self::from_bytes_for(bytes, expected)
  }
}

impl<F: AiurField> Program<F> {
  pub fn from_bytes_for(
    bytes: &[u8],
    expected: &[u8; 32],
  ) -> Result<Self, String> {
    Self::load(bytes, expected, ENTRY, 0)
  }

  fn load(
    bytes: &[u8],
    expected: &[u8; 32],
    entry: &'static str,
    outputs: usize,
  ) -> Result<Self, String> {
    if blake3::hash(bytes).as_bytes() != expected {
      return Err("terminal Aiur artifact digest mismatch".into());
    }
    let package = WidePackage::decode(bytes)?;
    let trace =
      package.trace.ok_or("terminal artifact has no compiler trace")?;
    let mut program = package.program.check_with(F::default())?;
    program.track_depth(&trace)?;
    let plan = TracePlan::new(Arc::new(program), trace)?;
    plan.program().entry(entry)?;
    let claim = plan.public_claim(
      entry,
      &[F::default().zero(); 2],
      &vec![F::default().zero(); outputs],
    )?;
    if claim.len() != 4 + outputs {
      return Err("terminal entry has an unexpected public-call schema".into());
    }
    let mut maps = MapOverrides::new();
    aiur::library::u8::register_maps(plan.program(), &mut maps)?;
    Ok(Self { plan, maps, entry })
  }

  pub fn plan(&self) -> &TracePlan<'static, F> {
    &self.plan
  }

  pub fn execute(
    &self,
    inputs: &crate::aiur_backend::kzg_advice::Inputs,
    statement: &[u8; 32],
    stage: u32,
  ) -> Result<aiur::Execution<F>, String> {
    self.execute_inner(inputs, statement, stage, None)
  }

  fn execute_inner(
    &self,
    inputs: &crate::aiur_backend::kzg_advice::Inputs,
    statement: &[u8; 32],
    stage: u32,
    reservation: Option<&RecordReservation>,
  ) -> Result<aiur::Execution<F>, String> {
    use crate::aiur_backend::{fq, g1, kzg_advice, pairing};
    let field = F::default();
    let mut hints = HintChannels::new();
    aiur::library::u32::register(&mut hints, field)?;
    aiur::library::u64::register(&mut hints, field)?;
    fq::register_for::<F::Curve>(&mut hints)?;
    g1::register_for::<F::Curve>(&mut hints)?;
    pairing::register_for::<F::Curve>(&mut hints)?;
    kzg_advice::register_for::<F::Curve>(&mut hints)?;
    inputs.register_for::<F::Curve>(&mut hints)?;
    hints.insert_fixed::<0, 1>(
      "kzg.final.stage",
      Type::Tuple { items: vec![] },
      Type::Field,
      move |[]| Ok([field.from_u64(u64::from(stage))]),
    )?;
    let prepared = self
      .plan
      .program()
      .prepare_hint_channels(&[], &hints)?
      .with_map_overrides(&self.maps)?;
    let args = statement_arguments_for::<F::Curve>(statement).to_vec();
    match reservation {
      Some(reservation) => {
        prepared.execute_reserved(self.entry, args, reservation)
      },
      None => prepared.execute(self.entry, args),
    }
    .map_err(|error| error.to_string())
  }
}

/// The Aiur relation returns two canonical affine points and defers their
/// pairing. Only the terminal PLONK schema adds the complete pairing assertion.
pub struct AccumulatorProgram<F: AiurField = Bn254>(Program<F>);

impl AccumulatorProgram<Bn254> {
  pub fn from_bytes(bytes: &[u8], expected: &[u8; 32]) -> Result<Self, String> {
    Self::from_bytes_for(bytes, expected)
  }
}

impl<F: AiurField> AccumulatorProgram<F> {
  pub fn from_bytes_for(
    bytes: &[u8],
    expected: &[u8; 32],
  ) -> Result<Self, String> {
    Ok(Self(Program::<F>::load(
      bytes,
      expected,
      ACCUMULATOR_ENTRY,
      F::Curve::TERMINAL_OUTPUT_WORDS,
    )?))
  }

  pub fn plan(&self) -> &TracePlan<'static, F> {
    self.0.plan()
  }

  pub fn execute(
    &self,
    inputs: &crate::aiur_backend::kzg_advice::Inputs,
    statement: &[u8; 32],
    stage: u32,
  ) -> Result<aiur::Execution<F>, String> {
    Self::checked(self.0.execute(inputs, statement, stage)?)
  }

  /// Bound the interpreter record before population; artifact, advice and
  /// later prover workspaces are separate allocations.
  pub fn execute_with_record_limit(
    &self,
    inputs: &crate::aiur_backend::kzg_advice::Inputs,
    statement: &[u8; 32],
    stage: u32,
    max_record_bytes: usize,
  ) -> Result<aiur::Execution<F>, String> {
    if max_record_bytes == 0 {
      return Err("terminal record limit must be positive".into());
    }
    let pool = RecordPool::new(max_record_bytes, max_record_bytes);
    let reservation = pool
      .try_admit()
      .map_err(|error| error.to_string())?
      .ok_or("terminal record reservation unavailable")?;
    let record =
      self.0.execute_inner(inputs, statement, stage, Some(&reservation))?;
    reservation.finish_execution();
    Self::checked(record)
  }

  fn checked(record: aiur::Execution<F>) -> Result<aiur::Execution<F>, String> {
    let words = F::Curve::TERMINAL_OUTPUT_WORDS;
    let half = F::Curve::G1_WORDS;
    if record.output.len() != words {
      return Err("terminal accumulator requires two affine points".into());
    }
    let _ =
      crate::aiur_backend::g1::decode_for::<F::Curve>(&record.output[..half])?;
    let _ =
      crate::aiur_backend::g1::decode_for::<F::Curve>(&record.output[half..])?;
    Ok(record)
  }
}

pub struct Configuration {
  curve: Curve,
  policy_digest: [u8; 32],
  anchors: Vec<u8>,
  anchor_coordinates: [[String; 4]; 2],
  parameters_digest: [u8; 32],
  lines: Vec<Vec<String>>,
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
    Self::new_for::<Bn254Curve>(policy, parameters, max_stage, allow_gl)
  }

  /// Curve-generic counterpart of [`Self::new`].
  pub fn new_for<C: AiurCurve>(
    policy: &Policy<C>,
    parameters: &VerifierParams<C>,
    max_stage: u32,
    allow_gl: bool,
  ) -> Result<Self, String> {
    let min_stage = if allow_gl { 1 } else { 2 };
    Self::from_policy_for::<C>(
      policy.digest(),
      policy.anchor_bytes_slice(),
      parameters,
      min_stage,
      max_stage,
    )
  }

  /// The narrow-stage terminal's configuration: its stage interval is the
  /// one terminal stage, after the narrow stage the predecessor key proves.
  pub fn narrow(
    policy: &crate::aiur_backend::compress_bn::PackedPolicy,
    parameters: &VerifierParams,
    terminal_stage: u32,
  ) -> Result<Self, String> {
    Self::narrow_for::<Bn254Curve>(policy, parameters, terminal_stage)
  }

  /// Curve-generic counterpart of [`Self::narrow`].
  pub fn narrow_for<C: AiurCurve>(
    policy: &crate::aiur_backend::compress_bn::PackedPolicy<C>,
    parameters: &VerifierParams<C>,
    terminal_stage: u32,
  ) -> Result<Self, String> {
    if terminal_stage < 2 {
      return Err("the narrow terminal follows a narrow stage".into());
    }
    Self::from_policy_for::<C>(
      policy.digest(),
      policy.anchor_bytes_slice(),
      parameters,
      terminal_stage,
      terminal_stage,
    )
  }

  fn from_policy_for<C: AiurCurve>(
    policy_digest: [u8; 32],
    policy_anchors: &[u8],
    parameters: &VerifierParams<C>,
    min_stage: u32,
    max_stage: u32,
  ) -> Result<Self, String> {
    if max_stage < min_stage {
      return Err("invalid final stage interval".into());
    }
    let (_, points) = verifier_anchors_for::<C>(parameters);
    if points.iter().any(|point| {
      point.is_zero()
        || !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
    }) {
      return Err(format!(
        "final {} KZG pairing anchors must be nonzero subgroup points",
        C::NAME
      ));
    }
    let mut anchors = Vec::with_capacity(C::G2_PAIR_COMPRESSED_BYTES);
    for point in points {
      point
        .serialize_compressed(&mut anchors)
        .map_err(|error| error.to_string())?;
    }
    if anchors.len() != C::G2_PAIR_COMPRESSED_BYTES {
      return Err("unexpected G2 anchor encoding width".into());
    }
    if anchors.as_slice() != policy_anchors {
      return Err("final policy and pairing anchors differ".into());
    }
    let (lines, anchor_coordinates) = match C::CURVE {
      Curve::Bn254 => {
        let g2_bn: [ark_bn254::G2Affine; 2] = [
          ark_bn254::G2Affine::deserialize_compressed(&anchors[..64])
            .map_err(|e| e.to_string())?,
          ark_bn254::G2Affine::deserialize_compressed(&anchors[64..])
            .map_err(|e| e.to_string())?,
        ];
        let lines = fixed_lines(g2_bn)?
          .into_iter()
          .map(|row| {
            row.iter().map(|&v| integer::<Bn254Curve>(v).to_string()).collect()
          })
          .collect();
        let coords = g2_bn.map(|point| {
          [
            point.x.c0.to_string(),
            point.x.c1.to_string(),
            point.y.c0.to_string(),
            point.y.c1.to_string(),
          ]
        });
        (lines, coords)
      },
      Curve::Bls12381 => {
        let g2_bls: [ark_bls12_381::G2Affine; 2] = [
          ark_bls12_381::G2Affine::deserialize_compressed(&anchors[..96])
            .map_err(|e| e.to_string())?,
          ark_bls12_381::G2Affine::deserialize_compressed(&anchors[96..])
            .map_err(|e| e.to_string())?,
        ];
        let lines = fixed_lines_bls12_381(g2_bls)?
          .into_iter()
          .map(|row| {
            row
              .iter()
              .map(|&v| integer::<Bls12381Curve>(v).to_string())
              .collect()
          })
          .collect();
        let coords = g2_bls.map(|point| {
          [
            point.x.c0.to_string(),
            point.x.c1.to_string(),
            point.y.c0.to_string(),
            point.y.c1.to_string(),
          ]
        });
        (lines, coords)
      },
    };
    let parameters_digest =
      *blake3::hash(&parameters.to_bytes().map_err(|error| error.to_string())?)
        .as_bytes();
    Ok(Self {
      curve: C::CURVE,
      policy_digest,
      anchors,
      anchor_coordinates,
      parameters_digest,
      lines,
      min_stage,
      max_stage,
    })
  }

  pub const fn curve(&self) -> Curve {
    self.curve
  }

  pub fn policy_digest(&self) -> [u8; 32] {
    self.policy_digest
  }

  /// `entry` is one of the two accumulator entries; its module's fixed
  /// configuration row must equal this configuration.
  pub(crate) fn terminal_coordinates_for<F: AiurField>(
    &self,
    plan: &TracePlan<'_, F>,
    entry: &str,
  ) -> Result<[[String; 4]; 2], String> {
    if F::Curve::CURVE != self.curve {
      return Err(
        "terminal configuration curve differs from program field".into(),
      );
    }
    let name = match entry {
      ACCUMULATOR_ENTRY => "CompressFinal::configuration_outputs",
      NARROW_ACCUMULATOR_ENTRY => "CompressFinalNarrow::configuration_outputs",
      _ => return Err("entry has no terminal pairing contract".into()),
    };
    let table = plan
      .program()
      .program()
      .tables
      .iter()
      .find(|table| table.name == name)
      .ok_or("terminal artifact has no fixed configuration")?;
    let field = F::default();
    let mut expected = crate::aiur_backend::kzg_advice::digest_words_for::<
      F::Curve,
    >(&self.policy_digest)
    .to_vec();
    expected
      .extend(self.anchors.iter().map(|&byte| field.from_u64(u64::from(byte))));
    expected.extend([
      field.from_u64(u64::from(self.min_stage)),
      field.from_u64(u64::from(self.max_stage)),
    ]);
    let expected: Vec<_> =
      expected.into_iter().map(|value| field.to_word(value)).collect();
    if table.rows.len() != 1 || table.rows[0] != expected {
      return Err("terminal artifact policy, anchors or stage interval differs from trusted configuration".into());
    }
    Ok(self.anchor_coordinates.clone())
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
    let mut value = serde_json::json!({
      "format":"ix-aiur-final-configuration-v1","policy_digest":words,
      "anchors":self.anchors.as_slice(),"anchor_coordinates":self.anchor_coordinates,
      "min_stage":self.min_stage,"max_stage":self.max_stage,
      "lines":self.lines,"policy_blake3":blake3::Hash::from_bytes(self.policy_digest).to_hex().as_str(),
      "parameters_blake3":blake3::Hash::from_bytes(self.parameters_digest).to_hex().as_str(),
      "anchors_blake3":blake3::hash(&self.anchors).to_hex().as_str(),
    });
    if self.curve != Curve::Bn254 {
      value["curve"] = serde_json::json!(self.curve.as_str());
    }
    serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())
  }

  /// Stage is private advice; the source independently enforces this interval
  /// and authenticates the predecessor's stage through its proven statement.
  pub fn register_stage_for<C: AiurCurve>(
    &self,
    hints: &mut HintChannels<CurveScalar<C>>,
    stage: u32,
  ) -> Result<(), String> {
    if C::CURVE != self.curve {
      return Err("final stage hint curve mismatch".into());
    }
    if stage < self.min_stage || stage > self.max_stage {
      return Err("private final stage outside configured interval".into());
    }
    hints.insert_fixed::<0, 1>(
      "kzg.final.stage",
      Type::Tuple { items: vec![] },
      Type::Field,
      move |[]| Ok([C::FIELD.from_u64(u64::from(stage))]),
    )
  }

  pub fn register_stage(
    &self,
    hints: &mut HintChannels<Scalar>,
    stage: u32,
  ) -> Result<(), String> {
    self.register_stage_for::<Bn254Curve>(hints, stage)
  }
}

/// Full 256-bit statement digest, retaining both canonical little-endian halves.
pub fn statement_arguments_for<C: AiurCurve>(
  statement: &[u8; 32],
) -> [CurveScalar<C>; 2] {
  std::array::from_fn(|index| {
    CurveScalar::<C>::new(C::Fr::from(u128::from_le_bytes(
      statement.as_chunks::<16>().0[index],
    )))
  })
}

/// Full 256-bit statement digest over BN254.
pub fn statement_arguments(statement: &[u8; 32]) -> [Scalar; 2] {
  statement_arguments_for::<Bn254Curve>(statement)
}
