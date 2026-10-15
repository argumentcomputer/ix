use super::*;
use multi_stark::plonkish::Assignment;
#[cfg(test)]
use multi_stark::plonkish::Witness;
use shape::{Round, Shape};

#[derive(Clone, Copy)]
pub(super) enum PointSource {
  Fixed(G1Affine),
  Commitment { round: Round, matrix: usize, column: usize },
  Witness(usize),
}

impl PointSource {
  fn value(self, proof: &Proof<KzgConfig>) -> G1Affine {
    match self {
      Self::Fixed(point) => point,
      Self::Commitment { round, matrix, column } => {
        round.commitment(proof).0[matrix][column]
      },
      Self::Witness(index) => proof.opening_proof.0[index],
    }
  }
}

pub(super) struct PointBinding {
  pub(super) source: PointSource,
  pub(super) point: PointInput,
}

pub(super) enum ScalarSource {
  Accumulator(usize),
  Opening { round: Round, matrix: usize, row: usize, column: usize },
  Claim { row: usize, column: usize },
}

impl ScalarSource {
  fn value(&self, proof: &Proof<KzgConfig>, claims: &[Vec<Scalar>]) -> Scalar {
    match *self {
      Self::Accumulator(index) => proof.intermediate_accumulators[index],
      Self::Opening { round, matrix, row, column } => {
        round.openings(proof).unwrap()[matrix][row][column]
      },
      Self::Claim { row, column } => claims[row][column],
    }
  }
}

pub(crate) struct Compiled {
  pub circuit: Circuit<Scalar>,
  pub bindings: Bindings,
}

pub(crate) struct Bindings {
  pub(super) identity: [u8; 32],
  pub(super) shape: Shape,
  pub(super) claims: ClaimSchema,
  pub(super) scalars: Vec<(Value, ScalarSource)>,
  pub(super) points: Vec<PointBinding>,
  pub(super) pairing_outputs: Vec<PointInput>,
  pub(super) pairing_keys: Vec<G2Affine>,
  pub(super) msm_terms: Vec<usize>,
  #[cfg(test)]
  pub(super) terms: Vec<Vec<(usize, Value)>>,
}

pub(super) struct RequestInputs {
  pub(super) inputs: Vec<(Value, Scalar)>,
  #[cfg(test)]
  pub(super) points: Vec<G1Affine>,
}

impl Bindings {
  pub(super) fn request_inputs(
    &self,
    candidate_id: [u8; 32],
    proof: &Proof<KzgConfig>,
    claims: &[Vec<Scalar>],
  ) -> Result<RequestInputs, String> {
    if candidate_id != self.identity {
      return Err("request uses a different recursive frontend profile".into());
    }
    self.shape.validate(proof)?;
    self.claims.validate(claims)?;
    let mut inputs = Vec::new();
    #[cfg(test)]
    let mut points = Vec::with_capacity(self.points.len());
    for binding in &self.points {
      let value = binding.source.value(proof);
      if !value.is_on_curve()
        || !value.is_in_correct_subgroup_assuming_on_curve()
      {
        return Err("invalid recursive proof point".into());
      }
      if !matches!(binding.source, PointSource::Fixed(_)) {
        inputs.extend(binding.point.inputs(value));
      }
      #[cfg(test)]
      points.push(value);
    }
    inputs.extend(
      self
        .scalars
        .iter()
        .map(|(handle, source)| (*handle, source.value(proof, claims))),
    );
    Ok(RequestInputs {
      inputs,
      #[cfg(test)]
      points,
    })
  }

  /// Assign one request to a circuit compiled once for its profile.
  #[cfg(test)]
  pub(crate) fn check(
    &self,
    candidate_id: [u8; 32],
    proof: &Proof<KzgConfig>,
    claims: &[Vec<Scalar>],
    mut witness: Witness<'_, Scalar>,
  ) -> Result<Assignment<Scalar>, Box<dyn std::error::Error>> {
    let request = self.request_inputs(candidate_id, proof, claims)?;
    for (handle, value) in request.inputs {
      witness.set(handle, value)?;
    }
    let assignment = witness.generate()?;
    let expected = self.claims.public_values(claims);
    if assignment.public_values().get(..expected.len())
      != Some(expected.as_slice())
    {
      return Err(
        "recursive assignment differs from the expected public statement"
          .into(),
      );
    }
    check_pairings(&assignment, &self.pairing_outputs, &self.pairing_keys)?;
    check_msm_outputs(
      &assignment,
      &request.points,
      &self.pairing_outputs,
      &self.terms,
    )?;
    Ok(assignment)
  }
}

fn pairing_points(
  assignment: &Assignment<Scalar>,
  pairing_outputs: &[PointInput],
) -> Result<Vec<G1Affine>, Box<dyn std::error::Error>> {
  let mut outputs = vec![];
  for point in pairing_outputs {
    let x = crate::recursive::native_field::fq_value(
      &point.point.x.0.map(|v| assignment.value(v).unwrap()),
    );
    let y = crate::recursive::native_field::fq_value(
      &point.point.y.0.map(|v| assignment.value(v).unwrap()),
    );
    let point = if assignment.value(point.infinity.value())? == Scalar::ONE {
      if !x.is_zero() || !y.is_zero() {
        return Err("noncanonical identity output".into());
      }
      G1Affine::identity()
    } else {
      G1Affine::new_unchecked(x, y)
    };
    if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err("invalid recursive pairing output".into());
    }
    outputs.push(point);
  }
  Ok(outputs)
}

pub(super) fn check_pairings(
  assignment: &Assignment<Scalar>,
  pairing_outputs: &[PointInput],
  pairing_keys: &[G2Affine],
) -> Result<(), Box<dyn std::error::Error>> {
  let outputs = pairing_points(assignment, pairing_outputs)?;
  if outputs.len() != 2
    || pairing_keys.len() != 2
    || !Bls12_381::multi_pairing(outputs, pairing_keys.iter().copied())
      .is_zero()
  {
    return Err("external opening pairing check failed".into());
  }
  Ok(())
}

#[cfg(test)]
pub(super) fn check_msm_outputs(
  assignment: &Assignment<Scalar>,
  points: &[G1Affine],
  pairing_outputs: &[PointInput],
  terms: &[Vec<(usize, Value)>],
) -> Result<(), Box<dyn std::error::Error>> {
  let outputs = pairing_points(assignment, pairing_outputs)?;
  assert_eq!(outputs.len(), terms.len());
  for (point, terms) in outputs.iter().zip(terms) {
    let expected = terms
      .iter()
      .map(|&(id, scalar)| points[id] * assignment.value(scalar).unwrap().0)
      .sum::<ark_bls12_381::G1Projective>()
      .into_affine();
    if *point != expected {
      return Err("MSM differs from native computation".into());
    }
  }
  Ok(())
}
