//! Compiled Aiur AIR evaluation inside the Stage 3 Flock relation.
//!
//! The verifier evaluates every compiled base-polynomial node in the degree-2
//! challenge field. LogUp is then evaluated in coordinates: one logical
//! accumulator consists of two such challenge-field values. This mirrors
//! `multi_stark::verifier` rather than trusting a host-computed composition.

use aiur::vk_codec::{AiurAirCircuitMetadata, AiurVerifyingKey};
use anyhow::{Result, bail};
use flock_prover::{
  circuit::builder::{ShapeBuilder, SlotId, Wire},
  field::F128,
};
use ix_terminal::{
  STAGE2_ROOT_STATEMENT_BYTES, ValidatedStage2RootV1, fri_parameter_words,
};
use multi_stark::{
  expr::{RowOffset, Source},
  graph::Node,
  lookup::{Lookup, WidthBinding},
  p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64},
  types::{ExtVal, FriParameters, Val},
};

use crate::{
  Stage2PcsInstanceV1, Stage2TranscriptByteBindingV1, Stage2TranscriptReplayV1,
  Stage2TranscriptSegmentV1, Stage3TypedProofWitnessV1,
  binding::pack_bytes,
  extension::GoldilocksCircuitSlots,
  fri::{
    assert_f128_equal, bound_transcript_extension, bound_transcript_window,
    record_fixed,
  },
  goldilocks::GOLDILOCKS_MODULUS,
  transcript::TranscriptConstraintRegion,
  transcript::{constrain_hash, hash_trace},
};

const EXTENSION_DEGREE: usize = 2;
const STAGE2_STATEMENT_PREFIX_BYTES: usize = 80;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2ActiveAirCircuitV1 {
  pub circuit_index: usize,
  pub log_degree: u8,
  pub metadata: AiurAirCircuitMetadata,
  pub log_degree_binding: Stage2TranscriptByteBindingV1,
  pub accumulator_binding: Stage2TranscriptByteBindingV1,
}

/// Fixed compiled programs and transcript locations for one Stage 2 proof
/// shape. Claim values remain dynamic public transcript words.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2AirProgramV1 {
  pub active: Vec<bool>,
  pub activation_bindings: Vec<Stage2TranscriptByteBindingV1>,
  pub active_circuits: Vec<Stage2ActiveAirCircuitV1>,
  pub claim_bindings: Vec<Stage2TranscriptByteBindingV1>,
  pub width_binding: WidthBinding,
  pub statement_prefix: [u8; STAGE2_STATEMENT_PREFIX_BYTES],
  pub statement_digest: [u8; 32],
}

impl Stage2AirProgramV1 {
  pub fn from_prepared(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
    pcs: &Stage2PcsInstanceV1,
  ) -> Result<Self> {
    let typed = Stage3TypedProofWitnessV1::from_prepared(prepared, fri)?;
    Self::from_prepared_and_typed(prepared, fri, pcs, &typed)
  }

  pub fn from_prepared_and_typed(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
    pcs: &Stage2PcsInstanceV1,
    typed: &Stage3TypedProofWitnessV1,
  ) -> Result<Self> {
    typed.ensure_profile(prepared.advice_profile())?;
    let key = AiurVerifyingKey::from_bytes(prepared.verifying_key_bytes())
      .map_err(|error| anyhow::anyhow!("decode Aiur AIR key: {error}"))?;
    if key.to_bytes() != prepared.verifying_key_bytes() {
      bail!("Aiur AIR key is not canonically encoded");
    }
    if fri_parameter_words(&key.fri_parameters()) != fri_parameter_words(fri) {
      bail!("Stage 3 AIR lowering uses different FRI parameters");
    }
    if key.commitment_parameters().cap_height != 0 {
      bail!("Stage 3 AIR lowering currently requires cap height zero");
    }

    let metadata = key.air_circuit_metadata();
    if metadata.len() != typed.active.len() {
      bail!("Aiur AIR metadata and activation lengths disagree");
    }
    let active_indices: Vec<_> = typed
      .active
      .iter()
      .enumerate()
      .filter_map(|(index, &active)| active.then_some(index))
      .collect();
    if active_indices.len() != typed.log_degrees.len()
      || active_indices.len() != typed.intermediate_accumulators.len()
    {
      bail!("Aiur AIR active-circuit vectors disagree");
    }
    if typed.intermediate_accumulators.last() != Some(&[0, 0]) {
      bail!("Aiur AIR lookup accumulator is not balanced");
    }

    validate_pcs_geometry(pcs, &metadata, &active_indices, typed)?;

    let seed_bytes = key.transcript_seed_and_shape_bytes().len();
    let activation_base = seed_bytes;
    let preprocessed_bytes = key
      .preprocessed_commitment_roots()
      .as_ref()
      .map_or(0, |roots| roots.len() * 32);
    let stage_1_bytes = typed.commitments.stage_1_trace.len() * 32;
    let log_degree_base = activation_base
      .checked_add(typed.active.len() * 8)
      .and_then(|offset| offset.checked_add(preprocessed_bytes))
      .and_then(|offset| offset.checked_add(stage_1_bytes))
      .ok_or_else(|| anyhow::anyhow!("AIR transcript offset overflow"))?;
    let claims_base = log_degree_base
      .checked_add(typed.log_degrees.len() * 8)
      .ok_or_else(|| anyhow::anyhow!("AIR claim offset overflow"))?;

    let claim_words = prepared.statement().outer_claim_words().to_vec();
    if prepared.claims_bytes().len() != 16 + claim_words.len() * 8 {
      bail!("Stage 2 recursive claim transport has the wrong length");
    }
    let claim_bindings = (0..claim_words.len())
      .map(|word| {
        Stage2TranscriptByteBindingV1::new(
          Stage2TranscriptSegmentV1::Initial,
          claims_base + 16 + word * 8,
        )
      })
      .collect();
    let activation_bindings = (0..typed.active.len())
      .map(|circuit| {
        Stage2TranscriptByteBindingV1::new(
          Stage2TranscriptSegmentV1::Initial,
          activation_base + circuit * 8,
        )
      })
      .collect();

    let active_circuits = active_indices
      .iter()
      .enumerate()
      .map(|(position, &circuit_index)| Stage2ActiveAirCircuitV1 {
        circuit_index,
        log_degree: typed.log_degrees[position],
        metadata: metadata[circuit_index].clone(),
        log_degree_binding: Stage2TranscriptByteBindingV1::new(
          Stage2TranscriptSegmentV1::Initial,
          log_degree_base + position * 8,
        ),
        accumulator_binding: Stage2TranscriptByteBindingV1::new(
          Stage2TranscriptSegmentV1::Stage2AndAccumulator,
          typed.commitments.stage_2_trace.len() * 32 + position * 16,
        ),
      })
      .collect::<Vec<_>>();

    let height_weight =
      active_circuits.iter().try_fold(1u128, |total, circuit| {
        let per_row: u128 = circuit
          .metadata
          .graph
          .lookups
          .iter()
          .map(|lookup| u128::from(lookup.max_multiplicity))
          .sum();
        let height = 1u128 << circuit.log_degree;
        total
          .checked_add(per_row.saturating_mul(height))
          .ok_or_else(|| anyhow::anyhow!("AIR multiplicity bound overflow"))
      })?;
    if height_weight >= u128::from(GOLDILOCKS_MODULUS) {
      bail!("AIR multiplicity height bound exceeds Goldilocks");
    }

    let statement_bytes = prepared.statement().to_bytes();
    if statement_bytes.len() != STAGE2_ROOT_STATEMENT_BYTES {
      bail!("Stage 2 statement has the wrong length");
    }
    let mut statement_prefix = [0u8; STAGE2_STATEMENT_PREFIX_BYTES];
    statement_prefix
      .copy_from_slice(&statement_bytes[..STAGE2_STATEMENT_PREFIX_BYTES]);

    Ok(Self {
      active: typed.active.clone(),
      activation_bindings,
      active_circuits,
      claim_bindings,
      width_binding: key.width_binding(),
      statement_prefix,
      statement_digest: prepared.statement().digest(),
    })
  }

  pub(crate) fn row_budget(&self) -> usize {
    let graph_rows = self
      .active_circuits
      .iter()
      .map(|circuit| {
        let nodes = circuit.metadata.graph.nodes.len();
        let constraints = circuit.metadata.graph.zeros.len()
          + circuit
            .metadata
            .graph
            .lookups
            .len()
            .div_ceil(circuit.metadata.lookup_group_size)
            * EXTENSION_DEGREE;
        nodes
          .saturating_mul(96)
          .saturating_add(constraints.saturating_mul(192))
          .saturating_add(circuit.metadata.quotient_degree * 96)
          .saturating_add(2048)
      })
      .sum::<usize>();
    graph_rows
      .saturating_add(self.claim_bindings.len().saturating_mul(128))
      .max(1)
  }
}

fn validate_pcs_geometry(
  pcs: &Stage2PcsInstanceV1,
  metadata: &[AiurAirCircuitMetadata],
  active_indices: &[usize],
  typed: &Stage3TypedProofWitnessV1,
) -> Result<()> {
  let expected_batches =
    3 + usize::from(typed.preprocessed_opened_values.is_some());
  if pcs.batches.len() != expected_batches {
    bail!("AIR PCS batch count disagrees with the typed proof");
  }
  for batch in &pcs.batches[..3] {
    if batch.matrices.len() != active_indices.len() {
      bail!("AIR PCS active-matrix count disagrees with the typed proof");
    }
  }
  for (position, &circuit_index) in active_indices.iter().enumerate() {
    let circuit = &metadata[circuit_index];
    let expected = [
      (circuit.main_width, 2usize),
      (circuit.stage_2_width, 2),
      (circuit.quotient_degree * EXTENSION_DEGREE, 1),
    ];
    for (batch, (width, points)) in expected.into_iter().enumerate() {
      let matrix = &pcs.batches[batch].matrices[position];
      if matrix.width != width || matrix.opening_points.len() != points {
        bail!("AIR PCS matrix geometry disagrees with the verifier key");
      }
    }
  }
  Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn constrain_stage2_air(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  blake3: SlotId,
  equality: SlotId,
  equality_zero: Wire,
  window: SlotId,
  data_zero: Wire,
  one: Wire,
  iv: [Wire; 2],
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  prefix_region: &TranscriptConstraintRegion,
  prefix: &Stage2TranscriptReplayV1,
  pcs: &Stage2PcsInstanceV1,
  program: &Stage2AirProgramV1,
) -> Result<()> {
  let challenges = prefix.challenges()?;
  let lookup = prefix_region.challenges.lookup;
  let fingerprint = prefix_region.challenges.fingerprint;
  let alpha = prefix_region.challenges.constraint;
  let zeta = prefix_region.challenges.zeta;
  for wire in [lookup, fingerprint, alpha, zeta] {
    arithmetic.assert_canonical(builder, wire);
  }

  // Bind the specialised activation pattern and active trace heights to the
  // exact words already consumed by Fiat--Shamir.
  for (&active, &binding) in
    program.active.iter().zip(&program.activation_bindings)
  {
    let observed = bound_low_word(
      builder,
      arithmetic,
      window,
      data_zero,
      inputs,
      public,
      prefix_region,
      binding,
    );
    let expected =
      record_fixed(builder, inputs, public, F128::new(u64::from(active), 0));
    assert_f128_equal(builder, equality, equality_zero, observed, expected);
  }
  for circuit in &program.active_circuits {
    let observed = bound_low_word(
      builder,
      arithmetic,
      window,
      data_zero,
      inputs,
      public,
      prefix_region,
      circuit.log_degree_binding,
    );
    let expected = record_fixed(
      builder,
      inputs,
      public,
      F128::new(u64::from(circuit.log_degree), 0),
    );
    assert_f128_equal(builder, equality, equality_zero, observed, expected);
  }

  let claim_wires: Vec<_> = program
    .claim_bindings
    .iter()
    .map(|&binding| {
      let wire = bound_low_word(
        builder,
        arithmetic,
        window,
        data_zero,
        inputs,
        public,
        prefix_region,
        binding,
      );
      arithmetic.assert_canonical(builder, wire);
      wire
    })
    .collect();
  constrain_stage2_statement(
    builder,
    arithmetic,
    blake3,
    data_zero,
    iv,
    inputs,
    public,
    &claim_wires,
    program,
  )?;

  let native_lookup = native_extension(challenges.lookup);
  let native_fingerprint = native_extension(challenges.fingerprint);
  let mut native_message = ExtVal::ZERO;
  let native_claim_words = program
    .claim_bindings
    .iter()
    .map(|&binding| read_bound_u64(prefix, binding))
    .collect::<Result<Vec<_>>>()?;
  for &word in native_claim_words.iter().rev() {
    native_message = native_message * native_fingerprint + Val::from_u64(word);
  }
  native_message += native_lookup;
  let native_inverse = native_message
    .try_inverse()
    .ok_or_else(|| anyhow::anyhow!("Stage 2 claim lookup message is zero"))?;

  let mut claim_fingerprint = data_zero;
  for &word in claim_wires.iter().rev() {
    let scaled = arithmetic.ext2_mul(builder, claim_fingerprint, fingerprint);
    claim_fingerprint = arithmetic.add(builder, scaled, word);
  }
  let message = arithmetic.add(builder, lookup, claim_fingerprint);
  let inverse = record_private(
    builder,
    inputs,
    pack_extension(extension_words(native_inverse)),
  );
  arithmetic.assert_canonical(builder, inverse);
  let inverse_check = arithmetic.ext2_mul(builder, message, inverse);
  assert_f128_equal(builder, equality, equality_zero, inverse_check, one);
  let mut accumulator = inverse;

  let neg_one =
    record_fixed(builder, inputs, public, F128::new(GOLDILOCKS_MODULUS - 1, 0));
  let seven = record_fixed(builder, inputs, public, F128::new(7, 0));
  let basis_u = record_fixed(builder, inputs, public, F128::new(0, 1));

  for (position, circuit) in program.active_circuits.iter().enumerate() {
    let next_accumulator = bound_transcript_extension(
      builder,
      window,
      data_zero,
      inputs,
      public,
      prefix_region,
      circuit.accumulator_binding,
      0,
    );
    arithmetic.assert_canonical(builder, next_accumulator);
    if position + 1 == program.active_circuits.len() {
      assert_f128_equal(
        builder,
        equality,
        equality_zero,
        next_accumulator,
        data_zero,
      );
    }

    let lookup_coords = arithmetic.ext2_coordinates(builder, lookup);
    let fingerprint_coords = arithmetic.ext2_coordinates(builder, fingerprint);
    let accumulator_coords = arithmetic.ext2_coordinates(builder, accumulator);
    let next_accumulator_coords =
      arithmetic.ext2_coordinates(builder, next_accumulator);
    let publics = [
      lookup_coords[0],
      lookup_coords[1],
      fingerprint_coords[0],
      fingerprint_coords[1],
      accumulator_coords[0],
      accumulator_coords[1],
      next_accumulator_coords[0],
      next_accumulator_coords[1],
    ];

    let openings = bind_air_openings(
      builder,
      window,
      data_zero,
      inputs,
      public,
      prefix_region,
      pcs,
      circuit,
      position,
    )?;
    let selector_values =
      native_selectors(challenges.zeta, circuit.log_degree)?;
    let is_first =
      record_private(builder, inputs, pack_extension(selector_values.is_first));
    let is_last =
      record_private(builder, inputs, pack_extension(selector_values.is_last));
    let inv_vanishing = record_private(
      builder,
      inputs,
      pack_extension(selector_values.inv_vanishing),
    );
    for selector in [is_first, is_last, inv_vanishing] {
      arithmetic.assert_canonical(builder, selector);
    }

    let mut zeta_pow_n = zeta;
    for _ in 0..circuit.log_degree {
      zeta_pow_n = arithmetic.ext2_mul(builder, zeta_pow_n, zeta_pow_n);
    }
    let z_h = ext_sub(builder, arithmetic, neg_one, zeta_pow_n, one);
    let inv_check = arithmetic.ext2_mul(builder, inv_vanishing, z_h);
    assert_f128_equal(builder, equality, equality_zero, inv_check, one);
    let zeta_minus_one = ext_sub(builder, arithmetic, neg_one, zeta, one);
    let first_check = arithmetic.ext2_mul(builder, is_first, zeta_minus_one);
    assert_f128_equal(builder, equality, equality_zero, first_check, z_h);

    let generator = Val::TWO_ADIC_GENERATORS[usize::from(circuit.log_degree)];
    let generator_inverse = generator.inverse();
    let generator_inverse_wire = record_fixed(
      builder,
      inputs,
      public,
      F128::new(generator_inverse.as_canonical_u64(), 0),
    );
    let is_transition =
      ext_sub(builder, arithmetic, neg_one, zeta, generator_inverse_wire);
    let last_check = arithmetic.ext2_mul(builder, is_last, is_transition);
    assert_f128_equal(builder, equality, equality_zero, last_check, z_h);

    let n = Val::from_u64(1u64 << circuit.log_degree);
    let injection_scale = (n * generator).inverse();
    let injection_scale = record_fixed(
      builder,
      inputs,
      public,
      F128::new(injection_scale.as_canonical_u64(), 0),
    );
    let delta_scaled = std::array::from_fn(|coordinate| {
      let delta = ext_sub(
        builder,
        arithmetic,
        neg_one,
        next_accumulator_coords[coordinate],
        accumulator_coords[coordinate],
      );
      arithmetic.ext2_mul(builder, delta, injection_scale)
    });

    let node_values = constrain_graph(
      builder,
      arithmetic,
      neg_one,
      inputs,
      public,
      circuit,
      &openings,
      &publics,
      is_first,
      is_last,
      is_transition,
    )?;
    let mut constraints: Vec<_> = circuit
      .metadata
      .graph
      .zeros
      .iter()
      .map(|root| node_values[root.index()])
      .collect();
    constraints.extend(constrain_logup(
      builder,
      arithmetic,
      neg_one,
      seven,
      data_zero,
      one,
      &circuit.metadata.graph.lookups,
      circuit.metadata.lookup_group_size,
      program.width_binding,
      &node_values,
      &openings.stage2[0],
      &openings.stage2[1],
      &publics,
      &delta_scaled,
      is_last,
      inputs,
      public,
    ));

    let mut composition = data_zero;
    for constraint in constraints {
      let scaled = arithmetic.ext2_mul(builder, composition, alpha);
      composition = arithmetic.add(builder, scaled, constraint);
    }

    let mut quotient = data_zero;
    let mut power = one;
    for chunk in openings.quotient.as_chunks::<EXTENSION_DEGREE>().0 {
      let high = arithmetic.ext2_mul(builder, chunk[1], basis_u);
      let coefficient = arithmetic.add(builder, chunk[0], high);
      let term = arithmetic.ext2_mul(builder, power, coefficient);
      quotient = arithmetic.add(builder, quotient, term);
      power = arithmetic.ext2_mul(builder, power, zeta_pow_n);
    }
    let ood = arithmetic.ext2_mul(builder, composition, inv_vanishing);
    assert_f128_equal(builder, equality, equality_zero, ood, quotient);
    accumulator = next_accumulator;
  }
  Ok(())
}

#[allow(clippy::too_many_arguments)]
fn constrain_stage2_statement(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  blake3: SlotId,
  data_zero: Wire,
  iv: [Wire; 2],
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  claims: &[Wire],
  program: &Stage2AirProgramV1,
) -> Result<()> {
  if claims.len() != 18 {
    bail!("Stage 2 statement binding requires 18 claim words");
  }
  let mut message = program
    .statement_prefix
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| record_fixed(builder, inputs, public, pack_bytes(word)))
    .collect::<Vec<_>>();
  for pair in claims.as_chunks::<2>().0 {
    let high_lanes = builder.gate(arithmetic.repack, &[pair[1], data_zero]);
    let packed = builder.gate(arithmetic.repack, &[pair[0], high_lanes[0]])[3];
    message.push(packed);
  }
  let trace = hash_trace(STAGE2_ROOT_STATEMENT_BYTES);
  let parameters = trace
    .rows
    .iter()
    .map(|&(_cv, _message, counter, block_len, flags)| {
      record_fixed(
        builder,
        inputs,
        public,
        crate::binding::pack_params(counter, block_len, flags),
      )
    })
    .collect::<Vec<_>>();
  let root = constrain_hash(
    builder,
    blake3,
    &trace,
    &parameters,
    iv,
    data_zero,
    &message,
  )?;
  builder.publish(root[0]);
  builder.publish(root[1]);
  public.extend_from_slice(&[
    pack_bytes(&program.statement_digest[..16]),
    pack_bytes(&program.statement_digest[16..]),
  ]);
  Ok(())
}

struct BoundAirOpenings {
  preprocessed: [Vec<Wire>; 2],
  main: [Vec<Wire>; 2],
  stage2: [Vec<Wire>; 2],
  quotient: Vec<Wire>,
}

#[allow(clippy::too_many_arguments)]
fn bind_air_openings(
  builder: &mut ShapeBuilder,
  window: SlotId,
  data_zero: Wire,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  prefix_region: &TranscriptConstraintRegion,
  pcs: &Stage2PcsInstanceV1,
  circuit: &Stage2ActiveAirCircuitV1,
  position: usize,
) -> Result<BoundAirOpenings> {
  let main = bind_matrix(
    builder,
    window,
    data_zero,
    inputs,
    public,
    prefix_region,
    pcs,
    0,
    position,
  )?;
  let stage2 = bind_matrix(
    builder,
    window,
    data_zero,
    inputs,
    public,
    prefix_region,
    pcs,
    1,
    position,
  )?;
  let quotient = bind_matrix(
    builder,
    window,
    data_zero,
    inputs,
    public,
    prefix_region,
    pcs,
    2,
    position,
  )?;
  if main.len() != 2 || stage2.len() != 2 || quotient.len() != 1 {
    bail!("AIR opening-point geometry is invalid");
  }
  let preprocessed = if let Some(slot) = circuit.metadata.preprocessed_slot {
    let values = bind_matrix(
      builder,
      window,
      data_zero,
      inputs,
      public,
      prefix_region,
      pcs,
      3,
      slot,
    )?;
    if values.len() != 2 {
      bail!("active AIR preprocessed matrix has the wrong opening count");
    }
    [values[0].clone(), values[1].clone()]
  } else {
    [Vec::new(), Vec::new()]
  };
  Ok(BoundAirOpenings {
    preprocessed,
    main: [main[0].clone(), main[1].clone()],
    stage2: [stage2[0].clone(), stage2[1].clone()],
    quotient: quotient[0].clone(),
  })
}

#[allow(clippy::too_many_arguments)]
fn bind_matrix(
  builder: &mut ShapeBuilder,
  window: SlotId,
  data_zero: Wire,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  prefix_region: &TranscriptConstraintRegion,
  pcs: &Stage2PcsInstanceV1,
  batch: usize,
  matrix: usize,
) -> Result<Vec<Vec<Wire>>> {
  let matrix = pcs
    .batches
    .get(batch)
    .and_then(|batch| batch.matrices.get(matrix))
    .ok_or_else(|| anyhow::anyhow!("AIR PCS matrix is missing"))?;
  Ok(
    (0..matrix.opening_points.len())
      .map(|point| {
        (0..matrix.width)
          .map(|column| {
            bound_transcript_extension(
              builder,
              window,
              data_zero,
              inputs,
              public,
              prefix_region,
              matrix.opened_values,
              point * matrix.width + column,
            )
          })
          .collect()
      })
      .collect(),
  )
}

#[allow(clippy::too_many_arguments)]
fn constrain_graph(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  neg_one: Wire,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  circuit: &Stage2ActiveAirCircuitV1,
  openings: &BoundAirOpenings,
  publics: &[Wire; 8],
  is_first: Wire,
  is_last: Wire,
  is_transition: Wire,
) -> Result<Vec<Wire>> {
  let mut values = Vec::with_capacity(circuit.metadata.graph.nodes.len());
  for node in &circuit.metadata.graph.nodes {
    let value = match *node {
      Node::Const(value) => record_fixed(
        builder,
        inputs,
        public,
        F128::new(value.as_canonical_u64(), 0),
      ),
      Node::Var(column) => {
        let rows = match column.source {
          Source::Preprocessed => &openings.preprocessed,
          Source::Main => &openings.main,
          Source::Stage2 => &openings.stage2,
        };
        let row = match column.offset {
          RowOffset::Current => 0,
          RowOffset::Next => 1,
        };
        *rows[row]
          .get(usize::try_from(column.index).unwrap())
          .ok_or_else(|| anyhow::anyhow!("AIR graph column is out of range"))?
      },
      Node::Public(index) => *publics
        .get(usize::try_from(index).unwrap())
        .ok_or_else(|| anyhow::anyhow!("AIR graph public is out of range"))?,
      Node::IsFirstRow => is_first,
      Node::IsLastRow => is_last,
      Node::IsTransition => is_transition,
      Node::Add(left, right) => {
        arithmetic.add(builder, values[left.index()], values[right.index()])
      },
      Node::Sub(left, right) => ext_sub(
        builder,
        arithmetic,
        neg_one,
        values[left.index()],
        values[right.index()],
      ),
      Node::Mul(left, right) => arithmetic.ext2_mul(
        builder,
        values[left.index()],
        values[right.index()],
      ),
      Node::Neg(value) => {
        arithmetic.ext2_mul(builder, values[value.index()], neg_one)
      },
    };
    values.push(value);
  }
  Ok(values)
}

#[allow(clippy::too_many_arguments)]
fn constrain_logup(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  neg_one: Wire,
  seven: Wire,
  zero: Wire,
  one: Wire,
  lookups: &[Lookup<multi_stark::graph::NodeId>],
  group_size: usize,
  width_binding: WidthBinding,
  node_values: &[Wire],
  stage2: &[Wire],
  stage2_next: &[Wire],
  publics: &[Wire; 8],
  delta_scaled: &[Wire; 2],
  is_last: Wire,
  inputs: &mut Vec<F128>,
  public_inputs: &mut Vec<F128>,
) -> Vec<Wire> {
  let beta = [publics[0], publics[1]];
  let gamma = [publics[2], publics[3]];
  let injection = [
    arithmetic.ext2_mul(builder, is_last, delta_scaled[0]),
    arithmetic.ext2_mul(builder, is_last, delta_scaled[1]),
  ];
  if lookups.is_empty() {
    return (0..EXTENSION_DEGREE)
      .map(|coordinate| {
        let difference = ext_sub(
          builder,
          arithmetic,
          neg_one,
          stage2_next[coordinate],
          stage2[coordinate],
        );
        arithmetic.add(builder, difference, injection[coordinate])
      })
      .collect();
  }

  let group_size = group_size.max(1);
  let last_group = lookups.len().div_ceil(group_size) - 1;
  let mut constraints = Vec::new();
  for (group, chunk) in lookups.chunks(group_size).enumerate() {
    let source = [stage2[2 * group], stage2[2 * group + 1]];
    let target = if group < last_group {
      [stage2[2 * group + 2], stage2[2 * group + 3]]
    } else {
      [
        arithmetic.add(builder, stage2_next[0], injection[0]),
        arithmetic.add(builder, stage2_next[1], injection[1]),
      ]
    };
    let difference = [
      ext_sub(builder, arithmetic, neg_one, target[0], source[0]),
      ext_sub(builder, arithmetic, neg_one, target[1], source[1]),
    ];
    let messages: Vec<_> = chunk
      .iter()
      .map(|lookup| {
        let seed = match width_binding {
          WidthBinding::Fingerprint => lookup.args.len() as u64,
          WidthBinding::ByConstruction => 0,
        };
        let seed =
          record_fixed(builder, inputs, public_inputs, F128::new(seed, 0));
        let mut fingerprint = [seed, zero];
        for &argument in lookup.args.iter().rev() {
          fingerprint =
            coord_mul(builder, arithmetic, seven, fingerprint, gamma);
          fingerprint[0] = arithmetic.add(
            builder,
            fingerprint[0],
            node_values[argument.index()],
          );
        }
        [
          arithmetic.add(builder, fingerprint[0], beta[0]),
          arithmetic.add(builder, fingerprint[1], beta[1]),
        ]
      })
      .collect();
    let mut product = [one, zero];
    for &message in &messages {
      product = coord_mul(builder, arithmetic, seven, product, message);
    }
    let lhs = coord_mul(builder, arithmetic, seven, product, difference);
    let mut rhs = [zero, zero];
    for (excluded, lookup) in chunk.iter().enumerate() {
      let mut others = [one, zero];
      for (index, &message) in messages.iter().enumerate() {
        if index != excluded {
          others = coord_mul(builder, arithmetic, seven, others, message);
        }
      }
      for coordinate in 0..EXTENSION_DEGREE {
        let term = arithmetic.ext2_mul(
          builder,
          others[coordinate],
          node_values[lookup.multiplicity.index()],
        );
        rhs[coordinate] = arithmetic.add(builder, rhs[coordinate], term);
      }
    }
    constraints.extend((0..EXTENSION_DEGREE).map(|coordinate| {
      ext_sub(builder, arithmetic, neg_one, lhs[coordinate], rhs[coordinate])
    }));
  }
  constraints
}

fn coord_mul(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  seven: Wire,
  left: [Wire; 2],
  right: [Wire; 2],
) -> [Wire; 2] {
  let low = arithmetic.ext2_mul(builder, left[0], right[0]);
  let high_product = arithmetic.ext2_mul(builder, left[1], right[1]);
  let reduced_high = arithmetic.ext2_mul(builder, high_product, seven);
  let cross_0 = arithmetic.ext2_mul(builder, left[0], right[1]);
  let cross_1 = arithmetic.ext2_mul(builder, left[1], right[0]);
  [
    arithmetic.add(builder, low, reduced_high),
    arithmetic.add(builder, cross_0, cross_1),
  ]
}

fn ext_sub(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  neg_one: Wire,
  left: Wire,
  right: Wire,
) -> Wire {
  let negated = arithmetic.ext2_mul(builder, right, neg_one);
  arithmetic.add(builder, left, negated)
}

#[allow(clippy::too_many_arguments)]
fn bound_low_word(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  window: SlotId,
  data_zero: Wire,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  prefix_region: &TranscriptConstraintRegion,
  binding: Stage2TranscriptByteBindingV1,
) -> Wire {
  let word = bound_transcript_window(
    builder,
    window,
    data_zero,
    inputs,
    public,
    prefix_region,
    binding,
    0,
  );
  arithmetic.embed_low_lane(builder, word)
}

fn record_private(
  builder: &mut ShapeBuilder,
  inputs: &mut Vec<F128>,
  value: F128,
) -> Wire {
  inputs.push(value);
  builder.input()
}

struct NativeSelectors {
  is_first: [u64; 2],
  is_last: [u64; 2],
  inv_vanishing: [u64; 2],
}

fn native_selectors(zeta: [u64; 2], log_degree: u8) -> Result<NativeSelectors> {
  let zeta = native_extension(zeta);
  let z_h = zeta.exp_power_of_2(usize::from(log_degree)) - ExtVal::ONE;
  let generator = Val::TWO_ADIC_GENERATORS[usize::from(log_degree)];
  let generator_inverse = ExtVal::from(generator.inverse());
  let is_first = z_h
    * (zeta - ExtVal::ONE)
      .try_inverse()
      .ok_or_else(|| anyhow::anyhow!("OOD point is the first trace point"))?;
  let is_last = z_h
    * (zeta - generator_inverse)
      .try_inverse()
      .ok_or_else(|| anyhow::anyhow!("OOD point is the last trace point"))?;
  let inv_vanishing = z_h
    .try_inverse()
    .ok_or_else(|| anyhow::anyhow!("OOD point is inside the trace domain"))?;
  Ok(NativeSelectors {
    is_first: extension_words(is_first),
    is_last: extension_words(is_last),
    inv_vanishing: extension_words(inv_vanishing),
  })
}

fn native_extension(value: [u64; 2]) -> ExtVal {
  ExtVal::new([Val::from_u64(value[0]), Val::from_u64(value[1])])
}

fn extension_words(value: ExtVal) -> [u64; 2] {
  let values: &[Val] = value.as_basis_coefficients_slice();
  [values[0].as_canonical_u64(), values[1].as_canonical_u64()]
}

fn pack_extension(value: [u64; 2]) -> F128 {
  F128::new(value[0], value[1])
}

fn read_bound_u64(
  prefix: &Stage2TranscriptReplayV1,
  binding: Stage2TranscriptByteBindingV1,
) -> Result<u64> {
  let segment = match binding.segment {
    Stage2TranscriptSegmentV1::Initial => &prefix.initial_observations,
    Stage2TranscriptSegmentV1::Stage2AndAccumulator => {
      &prefix.stage2_and_accumulator_observations
    },
    Stage2TranscriptSegmentV1::QuotientCommitment => {
      &prefix.quotient_commitment_observations
    },
    Stage2TranscriptSegmentV1::PcsOpening => &prefix.pcs_opening_observations,
  };
  let bytes = segment
    .get(binding.byte_offset..binding.byte_offset + 8)
    .ok_or_else(|| anyhow::anyhow!("AIR transcript word is out of range"))?;
  Ok(u64::from_le_bytes(bytes.try_into().unwrap()))
}
