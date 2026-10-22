//! Untrusted witness preparation for the fixed verifier. Decompression and
//! native arithmetic here supply hints only; all openings, paths, challenges,
//! and folds are independently constrained by the verifier circuit.

use std::collections::{BTreeMap, BTreeSet};

use p3_blake3::Blake3;
use p3_challenger::{
  CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger,
};
use p3_field::{
  BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField,
};
use p3_symmetric::CryptographicHasher;
use p3_util::reverse_bits_len;

use super::FixedPcsShape;
use super::FixedVerifierInputs;
use super::QuadraticValue;
use multi_stark::config::StarkGenericConfig;
use multi_stark::plonkish::Witness;
use multi_stark::prover::Proof;
use multi_stark::prover::observe_claims;
use multi_stark::prover::sample_lookup_challenges;
use multi_stark::system::System;
use multi_stark::types::ExtVal;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;

type Digest = [u8; 32];
type Path = Vec<Digest>;

#[derive(Clone)]
pub struct ExpandedPcsWitness {
  pub proof: Proof<GoldilocksBlake3Config>,
  pub claims: Vec<Vec<Val>>,
  pub challenges: [ExtVal; 4],
  /// Native diagnostic values only; the circuit derives its own PCS
  /// challenges and indices, and `assign` does not assign these fields.
  pub pcs_alpha: ExtVal,
  pub fri_betas: Vec<ExtVal>,
  pub query_indices: Vec<usize>,
  /// Query-major, then the four input batches.
  pub input_paths: Vec<[Path; 4]>,
  /// Query-major, then FRI round.
  pub fri_paths: Vec<Vec<Path>>,
}

fn validate(
  shape: &FixedPcsShape,
  proof: &Proof<GoldilocksBlake3Config>,
) -> Result<(), String> {
  let matrices = shape.widths[0].len();
  let rounds = usize::from(shape.log_trace);
  let p = &proof.opening_proof;
  if proof.active != shape.active
    || proof.log_degrees != shape.log_degrees
    || proof.intermediate_accumulators.len() != matrices
    || p.commit_phase_commits.len() != rounds
    || p.commit_phase_openings.len() != rounds
    || p.commit_pow_witnesses.len() != rounds
    || p.final_poly.len() != 1
    || p.input_openings.len() != 4
    || proof.stage_1_opened_values.len() != matrices
    || proof.stage_2_opened_values.len() != matrices
    || proof.quotient_opened_values.len() != matrices
    || proof.preprocessed_opened_values.as_ref().map(Vec::len)
      != Some(shape.preprocessed.len())
  {
    return Err("proof does not match fixed verifier shape".into());
  }
  for root in [
    &proof.commitments.stage_1_trace,
    &proof.commitments.stage_2_trace,
    &proof.commitments.quotient_chunks,
  ]
  .into_iter()
  .chain(&p.commit_phase_commits)
  {
    if root.roots().len() != 1 {
      return Err("cap height must be zero".into());
    }
  }
  for batch in 0..4 {
    let openings = &p.input_openings[batch].opened_values;
    if openings.len() != shape.queries {
      return Err("query count mismatch".into());
    }
    for query in openings {
      if query.len() != shape.widths[batch].len()
        || query
          .iter()
          .zip(&shape.widths[batch])
          .any(|(row, &width)| row.len() != width)
      {
        return Err("input row shape mismatch".into());
      }
    }
    for matrix in 0..shape.widths[batch].len() {
      let rows =
        native_rows(proof, batch, matrix).ok_or("OOD matrix shape mismatch")?;
      if rows.len() != if batch == 2 { 1 } else { 2 }
        || rows.iter().any(|row| row.len() != shape.widths[batch][matrix])
      {
        return Err("OOD row shape mismatch".into());
      }
    }
  }
  for opening in &p.commit_phase_openings {
    if opening.log_arity != 1
      || opening.sibling_values.len() != shape.queries
      || opening.sibling_values.iter().any(|row| row.len() != 1)
    {
      return Err("binary FRI opening shape mismatch".into());
    }
  }
  Ok(())
}

fn native_rows(
  proof: &Proof<GoldilocksBlake3Config>,
  batch: usize,
  matrix: usize,
) -> Option<&[Vec<ExtVal>]> {
  let matrices = match batch {
    0 => &proof.stage_1_opened_values,
    1 => &proof.stage_2_opened_values,
    2 => &proof.quotient_opened_values,
    3 => proof.preprocessed_opened_values.as_ref()?,
    _ => return None,
  };
  matrices.get(matrix).map(Vec::as_slice)
}

fn hash_fields(values: impl IntoIterator<Item = Val>) -> Digest {
  Blake3.hash_iter(
    values.into_iter().flat_map(|v| v.as_canonical_u64().to_le_bytes()),
  )
}

/// Expand the native binary frontier wire order. Shared children are
/// recomputed from queried leaves; every resulting full path is later
/// checked in-circuit. No serialized proof identity is claimed.
fn expand_paths(
  indices: &[usize],
  leaves: &[Digest],
  log_height: usize,
  supplied: &[Digest],
  injections: &BTreeMap<usize, Vec<Digest>>,
) -> Result<Vec<Path>, String> {
  let mut current = BTreeMap::new();
  for (&index, &leaf) in indices.iter().zip(leaves) {
    if index >= 1 << log_height {
      return Err("query index out of range".into());
    }
    if let Some(previous) = current.insert(index, leaf)
      && previous != leaf
    {
      return Err("inconsistent duplicate query".into());
    }
  }
  let mut levels = Vec::with_capacity(log_height);
  let mut cursor = 0;
  for level in 0..log_height {
    let parents: BTreeSet<_> = current.keys().map(|i| i >> 1).collect();
    let mut next = BTreeMap::new();
    for parent in parents {
      for child in [2 * parent, 2 * parent + 1] {
        if let std::collections::btree_map::Entry::Vacant(entry) =
          current.entry(child)
        {
          entry
            .insert(*supplied.get(cursor).ok_or("truncated Merkle frontier")?);
          cursor += 1;
        }
      }
      let left = current[&(2 * parent)];
      let right = current[&(2 * parent + 1)];
      next.insert(parent, Blake3.hash_iter(left.into_iter().chain(right)));
    }
    if let Some(rows) = injections.get(&(log_height - level - 1)) {
      let mut seen = BTreeMap::new();
      for (&index, &row) in indices.iter().zip(rows) {
        let parent = index >> (level + 1);
        if let Some(previous) = seen.insert(parent, row) {
          if previous != row {
            return Err("inconsistent injected row for shared query".into());
          }
        } else {
          let digest = next.get_mut(&parent).unwrap();
          *digest = Blake3.hash_iter(digest.iter().copied().chain(row));
        }
      }
    }
    levels.push(current);
    current = next;
  }
  if cursor != supplied.len() {
    return Err("extra Merkle frontier digests".into());
  }
  Ok(
    indices
      .iter()
      .map(|index| {
        levels
          .iter()
          .enumerate()
          .map(|(level, nodes)| nodes[&((index >> level) ^ 1)])
          .collect()
      })
      .collect(),
  )
}

/// Normalize an existing native proof without trusting native acceptance.
/// Invalid algebra/Merkle data may still produce an assignment; the circuit
/// must reject it. Malformed dimensions/frontiers return an error here.
pub fn expand_pcs_witness(
  system: &System<GoldilocksBlake3Config>,
  shape: &FixedPcsShape,
  proof: &Proof<GoldilocksBlake3Config>,
  claims: &[&[Val]],
) -> Result<ExpandedPcsWitness, String> {
  system
    .verify_shape(proof)
    .map_err(|e| format!("invalid native proof shape: {e:?}"))?;
  validate(shape, proof)?;
  let mut challenger = system.config.initialise_challenger();
  system.observe_shape(&mut challenger);
  for &active in &proof.active {
    challenger.observe(Val::from_bool(active));
  }
  if let Some(root) = &system.preprocessed_commit {
    challenger.observe(root.clone());
  }
  challenger.observe(proof.commitments.stage_1_trace.clone());
  for &height in &proof.log_degrees {
    challenger.observe(Val::from_u8(height));
  }
  observe_claims::<GoldilocksBlake3Config>(&mut challenger, claims);
  let (beta, gamma) =
    sample_lookup_challenges::<GoldilocksBlake3Config>(&mut challenger);
  expand_after_lookup(system, shape, proof, claims, challenger, beta, gamma)
}

/// Shared untrusted PCS normalization after the caller replays its protocol's
/// lookup transcript. Both single-proof and batch transcripts use this path.
pub(super) fn expand_after_lookup(
  system: &System<GoldilocksBlake3Config>,
  shape: &FixedPcsShape,
  proof: &Proof<GoldilocksBlake3Config>,
  claims: &[&[Val]],
  mut challenger: multi_stark::types::Challenger,
  beta: ExtVal,
  gamma: ExtVal,
) -> Result<ExpandedPcsWitness, String> {
  system
    .verify_shape(proof)
    .map_err(|e| format!("invalid proof shape: {e:?}"))?;
  validate(shape, proof)?;
  challenger.observe(proof.commitments.stage_2_trace.clone());
  for &acc in &proof.intermediate_accumulators {
    challenger.observe_algebra_element(acc);
  }
  let alpha = challenger.sample_algebra_element();
  challenger.observe(proof.commitments.quotient_chunks.clone());
  let zeta: ExtVal = challenger.sample_algebra_element();
  for batch in 0..4 {
    for matrix in 0..shape.widths[batch].len() {
      for row in native_rows(proof, batch, matrix).unwrap() {
        challenger.observe_algebra_slice(row);
      }
    }
  }
  let pcs_alpha: ExtVal = challenger.sample_algebra_element();
  let p = &proof.opening_proof;
  let fri_betas: Vec<ExtVal> = p
    .commit_phase_commits
    .iter()
    .zip(&p.commit_pow_witnesses)
    .map(|(root, &pow)| {
      challenger.observe(root.clone());
      // Ignore acceptance here: these computations are untrusted hints.
      let _ = challenger.check_witness(
        system.config.fri_parameters().commit_proof_of_work_bits,
        pow,
      );
      challenger.sample_algebra_element()
    })
    .collect();
  challenger.observe_algebra_slice(&p.final_poly);
  for _ in &fri_betas {
    challenger.observe(Val::ONE);
  }
  let _ = challenger.check_witness(
    system.config.fri_parameters().query_proof_of_work_bits,
    p.query_pow_witness,
  );
  let query_indices: Vec<_> =
    (0..shape.queries).map(|_| challenger.sample_bits(shape.log_lde)).collect();
  let mut input_paths: Vec<[Path; 4]> =
    (0..shape.queries).map(|_| std::array::from_fn(|_| vec![])).collect();
  for (batch, opening) in p.input_openings.iter().enumerate() {
    let mut hashes: BTreeMap<usize, Vec<Digest>> = BTreeMap::new();
    for matrices in &opening.opened_values {
      let mut rows: BTreeMap<usize, Vec<Val>> = BTreeMap::new();
      for (&height, row) in shape.heights[batch].iter().zip(matrices) {
        rows.entry(height).or_default().extend(row);
      }
      for (height, row) in rows {
        hashes.entry(height).or_default().push(hash_fields(row));
      }
    }
    let (height, leaves) = hashes.pop_last().unwrap();
    let indices: Vec<_> =
      query_indices.iter().map(|i| i >> (shape.log_lde - height)).collect();
    let paths = expand_paths(
      &indices,
      &leaves,
      height,
      &opening.opening_proof.sibling_hashes,
      &hashes,
    )?;
    for (query, path) in paths.into_iter().enumerate() {
      input_paths[query][batch] = path;
    }
  }
  let rounds = usize::from(shape.log_trace);
  let mut fri_paths: Vec<Vec<Path>> = vec![vec![vec![]; rounds]; shape.queries];
  let mut folded = Vec::new();
  let mut reductions = Vec::new();
  for (query, &index) in query_indices.iter().enumerate() {
    let mut reduced_by_height = BTreeMap::new();
    for batch in 0..4 {
      for (matrix, row) in
        p.input_openings[batch].opened_values[query].iter().enumerate()
      {
        let height = shape.heights[batch][matrix];
        let x = Val::GENERATOR
          * Val::two_adic_generator(height).exp_u64(
            u64::try_from(reverse_bits_len(
              index >> (shape.log_lde - height),
              height,
            ))
            .unwrap(),
          );
        let next =
          zeta * Val::two_adic_generator(height - system.config.log_blowup());
        let denominators: Vec<_> = [zeta, next]
          .into_iter()
          .map(|z| {
            (z - x).try_inverse().ok_or("opening point equals query point")
          })
          .collect::<Result<_, _>>()?;
        let (power, reduced) = reduced_by_height
          .entry(height)
          .or_insert((ExtVal::ONE, ExtVal::ZERO));
        for (point, opened) in
          native_rows(proof, batch, matrix).unwrap().iter().enumerate()
        {
          for (&at_x, &at_z) in row.iter().zip(opened) {
            *reduced += *power * (at_z - at_x) * denominators[point];
            *power *= pcs_alpha;
          }
        }
      }
    }
    folded.push(reduced_by_height[&shape.log_lde].1);
    reductions.push(reduced_by_height);
  }
  for (round, &beta) in fri_betas.iter().enumerate() {
    let log_height = shape.log_lde - round - 1;
    let indices: Vec<_> =
      query_indices.iter().map(|i| i >> (round + 1)).collect();
    let mut leaves = Vec::new();
    for query in 0..shape.queries {
      let sibling = p.commit_phase_openings[round].sibling_values[query][0];
      let pair = if (query_indices[query] >> round) & 1 == 0 {
        [folded[query], sibling]
      } else {
        [sibling, folded[query]]
      };
      leaves.push(hash_fields(
        pair
          .iter()
          .flat_map(
            <ExtVal as BasedVectorSpace<Val>>::as_basis_coefficients_slice,
          )
          .copied(),
      ));
      let x = Val::two_adic_generator(log_height + 1).exp_u64(
        u64::try_from(reverse_bits_len(indices[query], log_height)).unwrap(),
      );
      folded[query] = (pair[0] + pair[1]).halve()
        + (pair[0] - pair[1]) * beta * x.inverse().halve();
      if let Some((_, reduced)) = reductions[query].get(&log_height) {
        folded[query] += beta.square() * *reduced;
      }
    }
    let paths = expand_paths(
      &indices,
      &leaves,
      log_height,
      &p.commit_phase_openings[round].opening_proof.sibling_hashes,
      &BTreeMap::new(),
    )?;
    for (query, path) in paths.into_iter().enumerate() {
      fri_paths[query][round] = path;
    }
  }
  Ok(ExpandedPcsWitness {
    proof: proof.clone(),
    claims: claims.iter().map(|c| c.to_vec()).collect(),
    challenges: [beta, gamma, alpha, zeta],
    pcs_alpha,
    fri_betas,
    query_indices,
    input_paths,
    fri_paths,
  })
}

impl ExpandedPcsWitness {
  pub fn assign(
    &self,
    witness: &mut Witness<'_, Val>,
    inputs: &FixedVerifierInputs,
  ) -> Result<(), String> {
    self.assign_inner(witness, inputs, true)
  }

  /// Assign only proof wires. Caller-owned/derived claim wires must be
  /// supplied by the enclosing statement gadget, not by the adapter.
  pub fn assign_proof(
    &self,
    witness: &mut Witness<'_, Val>,
    inputs: &FixedVerifierInputs,
  ) -> Result<(), String> {
    self.assign_inner(witness, inputs, false)
  }

  fn assign_inner(
    &self,
    witness: &mut Witness<'_, Val>,
    inputs: &FixedVerifierInputs,
    assign_claims: bool,
  ) -> Result<(), String> {
    validate(&inputs.shape, &self.proof)?;
    let mut set =
      |wire, value| witness.set(wire, value).map_err(|e| e.to_string());
    fn extension(
      set: &mut impl FnMut(multi_stark::plonkish::Value, Val) -> Result<(), String>,
      wire: QuadraticValue,
      value: ExtVal,
    ) -> Result<(), String> {
      for (wire, &value) in wire.0.into_iter().zip(
        <ExtVal as BasedVectorSpace<Val>>::as_basis_coefficients_slice(&value),
      ) {
        set(wire, value)?;
      }
      Ok(())
    }
    fn digest(
      set: &mut impl FnMut(multi_stark::plonkish::Value, Val) -> Result<(), String>,
      wires: &super::pcs::Digest,
      values: Digest,
    ) -> Result<(), String> {
      for (wire, value) in wires.iter().zip(values) {
        set(wire.value(), Val::from_u8(value))?;
      }
      Ok(())
    }
    if inputs.algebra.claims.len() != self.claims.len() {
      return Err("claim count mismatch".into());
    }
    for (wires, claim) in inputs.algebra.claims.iter().zip(&self.claims) {
      if wires.len() != claim.len() {
        return Err("claim length mismatch".into());
      }
      if assign_claims {
        for (&wire, &value) in wires.iter().zip(claim) {
          set(wire, value)?;
        }
      }
    }
    let c = inputs.algebra.challenges;
    for (wire, value) in
      [c.beta, c.gamma, c.alpha, c.zeta].into_iter().zip(self.challenges)
    {
      extension(&mut set, wire, value)?;
    }
    for (matrix, o) in inputs.algebra.openings.iter().enumerate() {
      for (batch, wires) in [
        o.main.as_slice(),
        o.stage2.as_slice(),
        std::slice::from_ref(&o.quotient),
        o.preprocessed.as_slice(),
      ]
      .into_iter()
      .enumerate()
      {
        let matrix = if batch == 3 {
          match inputs.shape.preprocessed.iter().position(|&i| i == matrix) {
            Some(slot) => slot,
            None => continue,
          }
        } else {
          matrix
        };
        for (wires, values) in
          wires.iter().zip(native_rows(&self.proof, batch, matrix).unwrap())
        {
          for (&wire, &value) in wires.iter().zip(values) {
            extension(&mut set, wire, value)?;
          }
        }
      }
      extension(
        &mut set,
        o.accumulator,
        self.proof.intermediate_accumulators[matrix],
      )?;
    }
    for (wires, root) in [
      (&inputs.commitments.stage1, &self.proof.commitments.stage_1_trace),
      (&inputs.commitments.stage2, &self.proof.commitments.stage_2_trace),
      (&inputs.commitments.quotient, &self.proof.commitments.quotient_chunks),
    ] {
      digest(&mut set, wires, root.roots()[0])?;
    }
    let p = &self.proof.opening_proof;
    for (&wire, &value) in
      inputs.pcs.commit_pow.iter().zip(&p.commit_pow_witnesses)
    {
      set(wire, value)?;
    }
    set(inputs.pcs.query_pow, p.query_pow_witness)?;
    for (wires, root) in inputs.pcs.roots.iter().zip(&p.commit_phase_commits) {
      digest(&mut set, wires, root.roots()[0])?;
    }
    extension(&mut set, inputs.pcs.final_poly, p.final_poly[0])?;
    if self.input_paths.len() != inputs.shape.queries
      || self.fri_paths.len() != inputs.shape.queries
    {
      return Err("path query count mismatch".into());
    }
    for (offset, wires) in inputs.pcs.queries.iter().enumerate() {
      let query = inputs.pcs.query_start + offset;
      for batch in 0..4 {
        for (wires, values) in wires.input_rows[batch]
          .iter()
          .zip(&p.input_openings[batch].opened_values[query])
        {
          for (&wire, &value) in wires.iter().zip(values) {
            set(wire, value)?;
          }
        }
        if self.input_paths[query][batch].len()
          != wires.input_paths[batch].len()
        {
          return Err("input path length mismatch".into());
        }
        for (wires, &value) in
          wires.input_paths[batch].iter().zip(&self.input_paths[query][batch])
        {
          digest(&mut set, wires, value)?;
        }
      }
      if self.fri_paths[query].len() != wires.fri_paths.len() {
        return Err("FRI path round count mismatch".into());
      }
      for round in 0..wires.fri_siblings.len() {
        extension(
          &mut set,
          wires.fri_siblings[round],
          p.commit_phase_openings[round].sibling_values[query][0],
        )?;
        if self.fri_paths[query][round].len() != wires.fri_paths[round].len() {
          return Err("FRI path length mismatch".into());
        }
        for (wires, &value) in
          wires.fri_paths[round].iter().zip(&self.fri_paths[query][round])
        {
          digest(&mut set, wires, value)?;
        }
      }
    }
    Ok(())
  }
}
