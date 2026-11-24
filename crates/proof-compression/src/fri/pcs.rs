use std::collections::BTreeMap;

use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};

use super::AlgebraicInputs;
use super::Blake3Challenger;
use super::Blake3Domain;
use super::ByteGadgets;
use super::ByteValue;
use super::CubicValue as E;
use super::TranscriptCommitments;
use super::algebra::EXTENSION_DEGREE;
use super::blake3_domain;
use super::constrain_algebraic_checks;
use super::transcript::DEFAULT_FIELD_RETRIES;
use super::transcript::constrain_active_transcript;
use multi_stark::config::StarkGenericConfig;
use multi_stark::p3_adapter::fri_batching::{
  FriBatching, tensor_num_challenges,
};
use multi_stark::plonkish::Bool;
use multi_stark::plonkish::Circuit;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;
use multi_stark::system::{System, compute_vk_digest};
use multi_stark::types::{ExtVal3, GoldilocksBlake3V6Config, Val};

pub(super) type Digest = [ByteValue; 32];

/// Fixed active bitmap and heterogeneous trace heights. Preprocessed tables
/// must be active. Requires Protocol v6 (`F_p^3`, `FriBatching::Tensor`),
/// some preprocessing, cap zero, binary FRI and a constant final polynomial.
/// Both grinding phases are supported.
#[derive(Clone, Debug)]
pub struct FixedPcsShape {
  pub log_trace: u8,
  pub log_lde: usize,
  pub queries: usize,
  pub active: Vec<bool>,
  pub log_degrees: Vec<u8>,
  /// Maximum rejected candidates per field sample; exhaustion is rejected.
  pub max_field_retries: usize,
  /// Active opening index for each preprocessed matrix.
  pub preprocessed: Vec<usize>,
  /// LDE log heights, in each commitment's original matrix order.
  pub heights: [Vec<usize>; 4],
  /// Canonical batches: main, stage 2, quotient, preprocessing.
  pub widths: [Vec<usize>; 4],
}

impl FixedPcsShape {
  pub fn new(system: &System<GoldilocksBlake3V6Config>, log_trace: u8) -> Self {
    Self::from_profile(
      system,
      &vec![true; system.circuits.len()],
      &vec![log_trace; system.circuits.len()],
    )
  }

  /// Heights are supplied in active-circuit order, not canonical order.
  pub fn from_profile(
    system: &System<GoldilocksBlake3V6Config>,
    active: &[bool],
    logs: &[u8],
  ) -> Self {
    let fri = system.config.fri_parameters();
    assert_eq!(system.config.cap_height(), 0);
    assert_eq!(
      system.config.fri_batching(),
      FriBatching::Tensor,
      "Protocol v6 requires FriBatching::Tensor"
    );
    assert_eq!(
      system.vk_digest,
      compute_vk_digest::<Val, ExtVal3>(&system.circuits),
      "system vk_digest does not match its circuits"
    );
    assert_eq!(fri.max_log_arity, 1, "binary FRI required");
    assert_eq!(fri.log_final_poly_len, 0, "constant final polynomial required");
    assert!(
      fri.commit_proof_of_work_bits < 64 && fri.query_proof_of_work_bits < 64
    );
    assert!(fri.num_queries > 0);
    assert_eq!(active.len(), system.circuits.len());
    let circuits: Vec<_> = system
      .circuits
      .iter()
      .zip(active)
      .filter_map(|(c, &a)| a.then_some(c))
      .collect();
    assert_eq!(circuits.len(), logs.len());
    let log_trace = *logs.iter().max().expect("at least one active circuit");
    let log_lde = usize::from(log_trace) + system.config.log_blowup();
    assert!(log_lde <= Val::TWO_ADICITY && log_lde < usize::BITS as usize);
    for (c, &enabled) in system.circuits.iter().zip(active) {
      assert!(
        c.preprocessed_width == 0 || enabled,
        "preprocessed tables must be active"
      );
    }
    let mut preprocessed = vec![];
    for (i, (c, &log)) in circuits.iter().zip(logs).enumerate() {
      assert!(
        c.quotient_degree() <= system.config.max_quotient_degree()
          && usize::from(log) <= system.config.max_log_degree()
          && usize::from(log) + c.quotient_degree().ilog2() as usize
            <= system.config.max_log_quotient_domain(),
        "trace/quotient domain exceeds PCS limits"
      );
      if c.preprocessed_width != 0 {
        assert_eq!(c.preprocessed_height, 1usize << log);
        preprocessed.push(i);
      }
    }
    assert!(!preprocessed.is_empty(), "this profile requires preprocessing");
    let heights: Vec<_> = logs
      .iter()
      .map(|&h| usize::from(h) + system.config.log_blowup())
      .collect();
    let prep_heights = preprocessed.iter().map(|&i| heights[i]).collect();
    let prep_widths =
      preprocessed.iter().map(|&i| circuits[i].preprocessed_width).collect();
    Self {
      log_trace,
      log_lde,
      queries: fri.num_queries,
      active: active.to_vec(),
      log_degrees: logs.to_vec(),
      max_field_retries: DEFAULT_FIELD_RETRIES,
      preprocessed,
      heights: [heights.clone(), heights.clone(), heights, prep_heights],
      widths: [
        circuits.iter().map(|c| c.main_width).collect(),
        circuits.iter().map(|c| c.stage_2_width).collect(),
        circuits
          .iter()
          .map(|c| EXTENSION_DEGREE * c.quotient_degree())
          .collect(),
        prep_widths,
      ],
    }
  }

  /// `(max_width, max_openings_per_height)` across all opened matrices, used
  /// by Protocol v6 `FriBatching::Tensor`.
  pub(super) fn tensor_dimensions(&self) -> (usize, usize) {
    let mut max_width = 0usize;
    let mut openings_per_height: BTreeMap<usize, usize> = BTreeMap::new();
    for batch in 0..4 {
      let points = if batch == 2 { 1 } else { 2 };
      for (&width, &height) in
        self.widths[batch].iter().zip(&self.heights[batch])
      {
        max_width = max_width.max(width);
        *openings_per_height.entry(height).or_insert(0) += points;
      }
    }
    let max_openings_per_height =
      openings_per_height.values().copied().max().unwrap_or(0);
    (max_width, max_openings_per_height)
  }
}

pub struct PcsQuery {
  pub input_rows: [Vec<Vec<Value>>; 4],
  pub input_paths: [Vec<Digest>; 4],
  pub fri_siblings: Vec<E>,
  pub fri_paths: Vec<Vec<Digest>>,
}

pub struct PcsInputs {
  pub roots: Vec<Digest>,
  pub commit_pow: Vec<Value>,
  pub query_pow: Value,
  pub final_poly: E,
  pub queries: Vec<PcsQuery>,
  pub(super) query_start: usize,
}

impl PcsInputs {
  pub(super) fn allocate_queries(
    b: &mut CircuitBuilder<Val>,
    bytes: &ByteGadgets,
    shape: &FixedPcsShape,
    queries: std::ops::Range<usize>,
  ) -> Self {
    assert!(queries.start <= queries.end && queries.end <= shape.queries);
    fn digest(b: &mut CircuitBuilder<Val>, bytes: &ByteGadgets) -> Digest {
      std::array::from_fn(|_| bytes.input(b, "Merkle digest byte"))
    }
    let rounds = usize::from(shape.log_trace);
    Self {
      roots: (0..rounds).map(|_| digest(b, bytes)).collect(),
      commit_pow: (0..rounds)
        .map(|_| b.input("commit grinding witness"))
        .collect(),
      query_pow: b.input("query grinding witness"),
      final_poly: E::input(b, "FRI final constant"),
      query_start: queries.start,
      queries: queries
        .map(|_| PcsQuery {
          input_rows: std::array::from_fn(|batch| {
            shape.widths[batch]
              .iter()
              .map(|&width| {
                (0..width).map(|_| b.input("queried column")).collect()
              })
              .collect()
          }),
          input_paths: std::array::from_fn(|batch| {
            (0..*shape.heights[batch].iter().max().unwrap())
              .map(|_| digest(b, bytes))
              .collect()
          }),
          fri_siblings: (0..rounds)
            .map(|_| E::input(b, "FRI sibling"))
            .collect(),
          fri_paths: (0..rounds)
            .map(|round| {
              (0..shape.log_lde - round - 1).map(|_| digest(b, bytes)).collect()
            })
            .collect(),
        })
        .collect(),
    }
  }
}

/// Private proof wires and the caller's claim interface. Shape and verifying
/// key are circuit constants; the enclosing builder controls public exposure.
pub struct FixedVerifierInputs {
  pub shape: FixedPcsShape,
  pub algebra: AlgebraicInputs,
  pub commitments: TranscriptCommitments,
  pub pcs: PcsInputs,
  /// Derived query bits, useful for differential diagnostics, not inputs.
  pub query_bits: Vec<Vec<Bool>>,
}

/// Complete fixed-profile verifier, including Fiat-Shamir, algebra, Merkle
/// authentication, multilinear tensor opening reduction, and every binary FRI
/// fold. The transcript rejects exhaustion of its fixed field-sampling retry
/// budget.
pub fn build_fixed_verifier(
  system: &System<GoldilocksBlake3V6Config>,
  log_trace: u8,
  claim_lengths: &[usize],
) -> (Circuit<Val>, FixedVerifierInputs) {
  let shape = FixedPcsShape::new(system, log_trace);
  build_profile_verifier(system, &shape, claim_lengths)
}

pub fn build_profile_verifier(
  system: &System<GoldilocksBlake3V6Config>,
  shape: &FixedPcsShape,
  claim_lengths: &[usize],
) -> (Circuit<Val>, FixedVerifierInputs) {
  let mut b = CircuitBuilder::new();
  let claims = claim_lengths
    .iter()
    .enumerate()
    .map(|(i, &len)| {
      (0..len).map(|j| b.public_input(format!("claim[{i}][{j}]"))).collect()
    })
    .collect();
  let bytes = ByteGadgets::new(&mut b);
  let inputs = constrain_fixed_verifier(&mut b, &bytes, system, shape, claims);
  (b.finish(), inputs)
}

/// Append verification using caller-owned claim wires and reusable byte tables.
pub fn constrain_fixed_verifier(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  system: &System<GoldilocksBlake3V6Config>,
  shape: &FixedPcsShape,
  claims: Vec<Vec<Value>>,
) -> FixedVerifierInputs {
  // The caller's redundant shape fields must never reduce authentication.
  let queries = system.config.fri_parameters().num_queries;
  constrain_fixed_queries(b, bytes, system, shape, claims, 0..queries, true)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn constrain_fixed_queries(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  system: &System<GoldilocksBlake3V6Config>,
  shape: &FixedPcsShape,
  claims: Vec<Vec<Value>>,
  queries: std::ops::Range<usize>,
  check_algebra: bool,
) -> FixedVerifierInputs {
  // Re-derive dimensions: callers cannot smuggle inconsistent public fields.
  let mut checked_shape =
    FixedPcsShape::from_profile(system, &shape.active, &shape.log_degrees);
  checked_shape.max_field_retries = shape.max_field_retries;
  let shape = checked_shape;
  let circuits: Vec<_> = system
    .circuits
    .iter()
    .zip(&shape.active)
    .filter_map(|(c, &a)| a.then_some(c))
    .collect();
  let algebra = AlgebraicInputs::with_claims(b, &circuits, claims);
  let commitments = TranscriptCommitments::allocate(b, bytes);
  let challenger = constrain_active_transcript(
    b,
    bytes,
    system,
    &shape.active,
    &shape.log_degrees,
    &algebra,
    &commitments,
    shape.max_field_retries,
  );
  if check_algebra {
    constrain_algebraic_checks(b, &circuits, &shape.log_degrees, &algebra);
  }
  let pcs = PcsInputs::allocate_queries(b, bytes, &shape, queries);
  let query_bits = constrain_pcs(
    b,
    bytes,
    system,
    &shape,
    &algebra,
    &commitments,
    &pcs,
    challenger,
  );
  FixedVerifierInputs { shape, algebra, commitments, pcs, query_bits }
}

fn opening_rows<'a>(
  algebra: &'a AlgebraicInputs,
  shape: &FixedPcsShape,
  batch: usize,
  matrix: usize,
) -> Vec<&'a [E]> {
  let matrix = if batch == 3 { shape.preprocessed[matrix] } else { matrix };
  let o = &algebra.openings[matrix];
  match batch {
    0 => o.main.iter().map(Vec::as_slice).collect(),
    1 => o.stage2.iter().map(Vec::as_slice).collect(),
    2 => vec![&o.quotient],
    3 => o.preprocessed.iter().map(Vec::as_slice).collect(),
    _ => unreachable!(),
  }
}

fn hash_fields(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  values: impl IntoIterator<Item = Value>,
) -> Digest {
  let encoded: Vec<_> =
    values.into_iter().flat_map(|v| bytes.encode_field64(b, v)).collect();
  blake3_domain(b, bytes, Blake3Domain::MerkleLeaf, &encoded)
}

#[allow(clippy::too_many_arguments)]
fn authenticate(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  root: &Digest,
  mut digest: Digest,
  bits: &[Bool],
  path: &[Digest],
  injections: &BTreeMap<usize, Digest>,
) {
  assert_eq!(bits.len(), path.len());
  for (level, (&bit, sibling)) in bits.iter().zip(path).enumerate() {
    let block: [_; 64] = std::array::from_fn(|i| {
      let (left, right) = if i < 32 {
        (sibling[i], digest[i])
      } else {
        (digest[i - 32], sibling[i - 32])
      };
      bytes.select(b, bit, left, right)
    });
    digest = blake3_domain(b, bytes, Blake3Domain::MerkleCompress, &block);
    if let Some(row_hash) = injections.get(&(bits.len() - level - 1)) {
      let block: Vec<_> = digest.into_iter().chain(*row_hash).collect();
      digest = blake3_domain(b, bytes, Blake3Domain::MerkleCompress, &block);
    }
  }
  for (actual, expected) in digest.into_iter().zip(root) {
    b.assert_equal(actual.value(), expected.value());
  }
}

/// g raised to the bit-reversal of a little-endian bit vector.
fn reversed_power(b: &mut CircuitBuilder<Val>, g: Val, bits: &[Bool]) -> Value {
  let one = b.constant(Val::ONE);
  let mut power = one;
  for (i, &bit) in bits.iter().enumerate() {
    let factor = b.constant(g.exp_power_of_2(bits.len() - 1 - i));
    let selected = b.select(bit, factor, one);
    power = b.mul(power, selected);
  }
  power
}

/// Expand multilinear tensor challenges into `len` weights matching
/// `multi_stark::p3_adapter::fri_batching::tensor_weights`.
fn expand_tensor_weights(
  b: &mut CircuitBuilder<Val>,
  challenges: &[E],
  len: usize,
) -> Vec<E> {
  if len == 0 {
    return Vec::new();
  }
  let one = E::constant(b, [Val::ONE, Val::ZERO, Val::ZERO]);
  let mut weights = Vec::with_capacity(len);
  weights.push(one);
  for &r in challenges {
    let prev_len = weights.len();
    for i in 0..prev_len {
      if weights.len() == len {
        break;
      }
      let w = weights[i].mul(b, r);
      weights.push(w);
    }
  }
  assert_eq!(weights.len(), len);
  weights
}

#[allow(clippy::too_many_arguments)]
pub(super) fn constrain_pcs(
  b: &mut CircuitBuilder<Val>,
  bytes: &ByteGadgets,
  system: &System<GoldilocksBlake3V6Config>,
  shape: &FixedPcsShape,
  algebra: &AlgebraicInputs,
  commitments: &TranscriptCommitments,
  pcs: &PcsInputs,
  mut challenger: Blake3Challenger,
) -> Vec<Vec<Bool>> {
  assert_eq!(
    system.config.fri_batching(),
    FriBatching::Tensor,
    "Protocol v6 verifier requires FriBatching::Tensor"
  );
  // PCS observes OOD evaluations in batch, matrix, point, column order.
  for batch in 0..4 {
    for matrix in 0..shape.widths[batch].len() {
      for row in opening_rows(algebra, shape, batch, matrix) {
        for &value in row {
          challenger.observe_extension(b, bytes, value);
        }
      }
    }
  }
  // Sample Protocol v6 multilinear tensor batching challenges in canonical order:
  // k_col column challenges, then k_open opening-pair challenges.
  let (max_width, max_openings_per_height) = shape.tensor_dimensions();
  let k_col = tensor_num_challenges(max_width);
  let col_challenges: Vec<_> =
    (0..k_col).map(|_| challenger.sample_extension(b, bytes)).collect();
  let k_open = tensor_num_challenges(max_openings_per_height);
  let open_challenges: Vec<_> =
    (0..k_open).map(|_| challenger.sample_extension(b, bytes)).collect();
  let col_weights = expand_tensor_weights(b, &col_challenges, max_width);
  let open_weights =
    expand_tensor_weights(b, &open_challenges, max_openings_per_height);

  let betas: Vec<_> = pcs
    .roots
    .iter()
    .zip(&pcs.commit_pow)
    .map(|(root, &pow)| {
      challenger.observe_bytes(root);
      challenger.check_witness(
        b,
        bytes,
        system.config.fri_parameters().commit_proof_of_work_bits,
        pow,
      );
      challenger.sample_extension(b, bytes)
    })
    .collect();
  challenger.observe_extension(b, bytes, pcs.final_poly);
  for _ in &betas {
    challenger.observe_constant(b, bytes, 1);
  }
  challenger.check_witness(
    b,
    bytes,
    system.config.fri_parameters().query_proof_of_work_bits,
    pcs.query_pow,
  );
  let queries: Vec<_> = (0..shape.queries)
    .map(|_| challenger.sample_bits(b, bytes, shape.log_lde))
    .collect();
  let preprocessed = system.preprocessed_commit.as_ref().unwrap().roots()[0]
    .map(|x| bytes.constant(b, x));
  let roots = [
    commitments.stage1,
    commitments.stage2,
    commitments.quotient,
    preprocessed,
  ];
  let zeta = algebra.challenges.zeta;
  let zero = E::constant(b, [Val::ZERO; EXTENSION_DEGREE]);

  // Hoist per-(batch, matrix, point) tensor-weighted OOD dot products and
  // per-height opening indices once outside the query loop. Because
  // `col_weights` is shared across both opening points of a matrix, each query
  // also computes `sum_j col_weights[j] * opened[j]` only once per matrix.
  let mut opening_cursors: BTreeMap<usize, usize> = BTreeMap::new();
  let mut ood_terms: Vec<Vec<Vec<(usize, E)>>> = Vec::new();
  for batch in 0..4 {
    let mut per_matrix = Vec::new();
    for matrix in 0..shape.widths[batch].len() {
      let height = shape.heights[batch][matrix];
      let mut per_point = Vec::new();
      for row in opening_rows(algebra, shape, batch, matrix) {
        let opening_idx = opening_cursors.entry(height).or_insert(0);
        let idx = *opening_idx;
        *opening_idx += 1;
        let mut weighted = zero;
        for (j, &at_z) in row.iter().enumerate() {
          let term = col_weights[j].mul(b, at_z);
          weighted = weighted.add(b, term);
        }
        per_point.push((idx, weighted));
      }
      per_matrix.push(per_point);
    }
    ood_terms.push(per_matrix);
  }
  for (offset, query) in pcs.queries.iter().enumerate() {
    let query_index = pcs.query_start + offset;
    let bits = &queries[query_index];
    let mut reductions = BTreeMap::new();
    let mut denominators = BTreeMap::new();
    for &height in &shape.heights[0] {
      denominators.entry(height).or_insert_with(|| {
        let point = reversed_power(
          b,
          Val::two_adic_generator(height),
          &bits[shape.log_lde - height..],
        );
        let point = b.scale(point, Val::GENERATOR);
        let x = E::from_base(b, point);
        let next = zeta.scale(
          b,
          Val::two_adic_generator(height - system.config.log_blowup()),
        );
        [zeta, next].map(|z| z.sub(b, x).inverse(b))
      });
    }
    for (batch, root) in roots.iter().enumerate() {
      let mut rows: BTreeMap<usize, Vec<Value>> = BTreeMap::new();
      for (&height, row) in
        shape.heights[batch].iter().zip(&query.input_rows[batch])
      {
        rows.entry(height).or_default().extend(row);
      }
      let mut hashes: BTreeMap<_, _> = rows
        .into_iter()
        .map(|(h, row)| (h, hash_fields(b, bytes, row)))
        .collect();
      let (height, leaf) = hashes.pop_last().unwrap();
      authenticate(
        b,
        bytes,
        root,
        leaf,
        &bits[shape.log_lde - height..],
        &query.input_paths[batch],
        &hashes,
      );
      for (matrix, opened) in query.input_rows[batch].iter().enumerate() {
        let height = shape.heights[batch][matrix];
        let reduced = reductions.entry(height).or_insert(zero);
        let mut at_x = zero;
        for (j, &x) in opened.iter().enumerate() {
          let term = col_weights[j].mul_base(b, x);
          at_x = at_x.add(b, term);
        }
        for (point, &(opening_idx, ood_weighted)) in
          ood_terms[batch][matrix].iter().enumerate()
        {
          let difference = ood_weighted.sub(b, at_x);
          let scaled = open_weights[opening_idx].mul(b, difference);
          let term = scaled.mul(b, denominators[&height][point]);
          *reduced = reduced.add(b, term);
        }
      }
    }
    if let Some(constant) = reductions.get(&system.config.log_blowup()) {
      constant.assert_equal(b, zero);
    }
    let mut folded = reductions[&shape.log_lde];
    for (round, &beta) in betas.iter().enumerate() {
      let sibling = query.fri_siblings[round];
      let lo = E::select(b, bits[round], sibling, folded);
      let hi = E::select(b, bits[round], folded, sibling);
      let leaf = hash_fields(b, bytes, lo.0.into_iter().chain(hi.0));
      authenticate(
        b,
        bytes,
        &pcs.roots[round],
        leaf,
        &bits[round + 1..],
        &query.fri_paths[round],
        &BTreeMap::new(),
      );
      let subgroup_x = reversed_power(
        b,
        Val::two_adic_generator(shape.log_lde - round),
        &bits[round + 1..],
      );
      let inv_x = b.inverse(subgroup_x);
      let sum = lo.add(b, hi).scale(b, Val::ONE.halve());
      let difference =
        lo.sub(b, hi).mul_base(b, inv_x).scale(b, Val::ONE.halve());
      let odd = difference.mul(b, beta);
      folded = sum.add(b, odd);
      if let Some(reduced) = reductions.get(&(shape.log_lde - round - 1)) {
        let beta_squared = beta.mul(b, beta);
        let injected = beta_squared.mul(b, *reduced);
        folded = folded.add(b, injected);
      }
    }
    folded.assert_equal(b, pcs.final_poly);
    tracing::info!(query = query_index + 1, total = shape.queries, stats = ?b.stats(), "Plonkish PCS query built");
  }
  queries
}
