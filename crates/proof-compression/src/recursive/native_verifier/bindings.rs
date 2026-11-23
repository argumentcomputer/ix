use super::*;
use multi_stark::plonkish::Assignment;
#[cfg(test)]
use multi_stark::plonkish::Witness;
use shape::{Round, Shape};

pub(super) enum PointSource<C: KzgCurve> {
  Fixed(G1AffineOf<C>),
  Commitment { round: Round, matrix: usize, column: usize },
  Witness(usize),
}

impl<C: KzgCurve> Clone for PointSource<C> {
  fn clone(&self) -> Self {
    *self
  }
}

impl<C: KzgCurve> Copy for PointSource<C> {}

impl<C: KzgCurve> PointSource<C> {
  fn value(self, proof: &Proof<KzgConfig<C>>) -> G1AffineOf<C> {
    match self {
      Self::Fixed(point) => point,
      Self::Commitment { round, matrix, column } => {
        round.commitment(proof).0[matrix][column]
      },
      Self::Witness(index) => proof.opening_proof.0[index],
    }
  }
}

pub(super) struct PointBinding<C: KzgCurve> {
  pub(super) source: PointSource<C>,
  pub(super) point: PointInput<C>,
}

pub(super) enum ScalarSource {
  Accumulator(usize),
  Opening { round: Round, matrix: usize, row: usize, column: usize },
  Claim { row: usize, column: usize },
}

impl ScalarSource {
  fn value<C: KzgCurve>(
    &self,
    proof: &Proof<KzgConfig<C>>,
    claims: &[Vec<CurveScalar<C>>],
  ) -> CurveScalar<C> {
    match *self {
      Self::Accumulator(index) => proof.intermediate_accumulators[index],
      Self::Opening { round, matrix, row, column } => {
        round.openings(proof).unwrap()[matrix][row][column]
      },
      Self::Claim { row, column } => claims[row][column],
    }
  }
}

pub(crate) struct Compiled<C: KzgCurve = Bn254> {
  pub circuit: Circuit<CurveScalar<C>>,
  pub bindings: Bindings<C>,
}

pub(crate) struct Bindings<C: KzgCurve = Bn254> {
  pub(super) identity: [u8; 32],
  pub(super) shape: Shape<C>,
  pub(super) claims: ClaimSchema<C>,
  pub(super) scalars: Vec<(Value, ScalarSource)>,
  pub(super) points: Vec<PointBinding<C>>,
  pub(super) pairing_outputs: Vec<PointInput<C>>,
  pub(super) pairing_keys: Vec<G2AffineOf<C>>,
  pub(super) msm_terms: Vec<usize>,
  #[cfg(test)]
  pub(super) terms: Vec<Vec<(usize, Value)>>,
}

pub(super) struct RequestInputs<C: KzgCurve> {
  pub(super) inputs: Vec<(Value, CurveScalar<C>)>,
  #[cfg(test)]
  pub(super) points: Vec<G1AffineOf<C>>,
}

impl<C: KzgCurve> Bindings<C> {
  pub(super) fn request_inputs(
    &self,
    candidate_id: [u8; 32],
    proof: &Proof<KzgConfig<C>>,
    claims: &[Vec<CurveScalar<C>>],
  ) -> Result<RequestInputs<C>, String> {
    if candidate_id != self.identity {
      return Err(
        "request uses a different recursive frontend verifying key".into(),
      );
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

  /// Assign one request to a circuit compiled once for its verifying key.
  #[cfg(test)]
  pub(crate) fn check(
    &self,
    candidate_id: [u8; 32],
    proof: &Proof<KzgConfig<C>>,
    claims: &[Vec<CurveScalar<C>>],
    mut witness: Witness<'_, CurveScalar<C>>,
  ) -> Result<Assignment<CurveScalar<C>>, Box<dyn std::error::Error>> {
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

fn pairing_points<C: KzgCurve>(
  assignment: &Assignment<CurveScalar<C>>,
  pairing_outputs: &[PointInput<C>],
) -> Result<Vec<G1AffineOf<C>>, Box<dyn std::error::Error>> {
  let mut outputs = vec![];
  for point in pairing_outputs {
    let xs: Vec<_> = point
      .point
      .x
      .limbs()
      .iter()
      .map(|&v| assignment.value(v).unwrap())
      .collect();
    let ys: Vec<_> = point
      .point
      .y
      .limbs()
      .iter()
      .map(|&v| assignment.value(v).unwrap())
      .collect();
    let x = crate::recursive::native_field::fq_value::<C>(&xs);
    let y = crate::recursive::native_field::fq_value::<C>(&ys);
    let point =
      if assignment.value(point.infinity.value())? == CurveScalar::<C>::ONE {
        if !x.is_zero() || !y.is_zero() {
          return Err("noncanonical identity output".into());
        }
        G1AffineOf::<C>::identity()
      } else {
        G1AffineOf::<C>::new_unchecked(x, y)
      };
    if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err("invalid recursive pairing output".into());
    }
    outputs.push(point);
  }
  Ok(outputs)
}

pub(super) fn check_pairings<C: KzgCurve>(
  assignment: &Assignment<CurveScalar<C>>,
  pairing_outputs: &[PointInput<C>],
  pairing_keys: &[G2AffineOf<C>],
) -> Result<(), Box<dyn std::error::Error>> {
  let outputs = pairing_points(assignment, pairing_outputs)?;
  let public_values = assignment.public_values();
  let public_start = public_values
    .len()
    .checked_sub(pairing::PUBLIC_VALUES)
    .ok_or("missing public pairing operands")?;
  let public_outputs = pairing::decode::<C>(&public_values[public_start..])?;
  if outputs != public_outputs {
    return Err(
      "public pairing operands differ from the constrained points".into(),
    );
  }
  if outputs.len() != 2
    || pairing_keys.len() != 2
    || !C::PairingCurve::multi_pairing(outputs, pairing_keys.iter().copied())
      .is_zero()
  {
    return Err("external opening pairing check failed".into());
  }
  Ok(())
}

#[cfg(test)]
pub(super) fn check_msm_outputs<C: KzgCurve>(
  assignment: &Assignment<CurveScalar<C>>,
  points: &[G1AffineOf<C>],
  pairing_outputs: &[PointInput<C>],
  terms: &[Vec<(usize, Value)>],
) -> Result<(), Box<dyn std::error::Error>> {
  let outputs = pairing_points(assignment, pairing_outputs)?;
  assert_eq!(outputs.len(), terms.len());
  for (point, terms) in outputs.iter().zip(terms) {
    let expected = terms
      .iter()
      .map(|&(id, scalar)| points[id] * assignment.value(scalar).unwrap().0)
      .sum::<crate::kzg::curve::G1ProjectiveOf<C>>()
      .into_affine();
    if *point != expected {
      return Err("MSM differs from native computation".into());
    }
  }
  Ok(())
}
