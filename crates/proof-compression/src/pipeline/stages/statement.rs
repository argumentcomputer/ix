//! Public cells and fixed activation anchors of a lowered statement.
use super::Result;
use crate::kzg::Scalar;
use multi_stark::{
  plonkish::MultiStarkCircuit,
  traits::{Algebra, Field},
  types::Val,
};
use p3_field::PrimeField64;

/// The lowering's complete claim template, including all activation anchors.
/// Only public-value cells may be replaced during verification.
#[derive(serde::Serialize, serde::Deserialize)]
pub(in crate::pipeline) struct Statement<F> {
  pub(in crate::pipeline) template: Vec<Vec<F>>,
  pub(in crate::pipeline) locations: Vec<(usize, usize)>,
}

impl<F: Field> Statement<F> {
  pub(in crate::pipeline) fn from_lowered(
    circuit: &MultiStarkCircuit<F>,
    count: usize,
  ) -> Result<Self> {
    Self::from_claims(&circuit.claims(&vec![F::ZERO; count])?, count)
  }

  pub(in crate::pipeline) fn claims(
    &self,
    public: &[F],
  ) -> Result<Vec<Vec<F>>> {
    if public.len() != self.locations.len() {
      return Err("unexpected public statement length".into());
    }
    let mut claims = self.template.clone();
    for (&(row, col), &value) in self.locations.iter().zip(public) {
      claims[row][col] = value;
    }
    Ok(claims)
  }
}

impl<F: Field> Statement<F> {
  pub(super) fn validate(&self) -> Result<()> {
    let normalized = Self::from_claims(&self.template, self.locations.len())?;
    if self.locations != normalized.locations
      || self.template != normalized.template
    {
      return Err("invalid compression statement schema".into());
    }
    Ok(())
  }
}

impl<F: Field> Statement<F> {
  pub(in crate::pipeline) fn from_claims(
    claims: &[Vec<F>],
    count: usize,
  ) -> Result<Self> {
    if claims.len() <= count
      || claims[..=count].iter().any(|row| row.len() != 4)
    {
      return Err("unsupported lowering claim schema".into());
    }
    let namespace = claims[0][0];
    if claims[0][3] != F::ZERO
      || claims[..=count].iter().enumerate().any(|(i, row)| {
        row[0] != namespace || row[1] != F::ONE || row[2] != F::from_usize(i)
      })
    {
      return Err("invalid lowering claim schema".into());
    }
    let mut template = claims.to_vec();
    let locations: Vec<_> = (1..=count).map(|i| (i, 3)).collect();
    for &(row, col) in &locations {
      template[row][col] = F::ZERO;
    }
    Ok(Self { template, locations })
  }

  pub(in crate::pipeline) fn public_values(
    &self,
    claims: &[Vec<F>],
  ) -> Result<Vec<F>> {
    let public = self
      .locations
      .iter()
      .map(|&(row, col)| {
        claims
          .get(row)
          .and_then(|r| r.get(col))
          .copied()
          .ok_or("invalid statement dimensions")
      })
      .collect::<std::result::Result<Vec<_>, _>>()?;
    if self.claims(&public)? != claims {
      return Err("claim rows differ from the statement and anchors".into());
    }
    Ok(public)
  }
}

impl Statement<Val> {
  pub(in crate::pipeline) fn schema(
    &self,
  ) -> crate::fri::Statement<crate::fri::StatementSlot> {
    use crate::fri::{Statement, StatementSlot};
    let mut schema = Statement {
      claims: self
        .template
        .iter()
        .map(|row| row.iter().copied().map(StatementSlot::Constant).collect())
        .collect(),
      messages: vec![],
    };
    for &(row, col) in &self.locations {
      schema.claims[row][col] = StatementSlot::Public;
    }
    schema
  }
}

impl Statement<Scalar> {
  pub(in crate::pipeline) fn recursive(count: usize) -> Self {
    Self {
      template: (0..=count)
        .map(|i| {
          vec![
            Scalar::from_u8(super::construct::RECURSIVE_NAMESPACE),
            Scalar::ONE,
            Scalar::from_usize(i),
            Scalar::ZERO,
          ]
        })
        .collect(),
      locations: (1..=count).map(|i| (i, 3)).collect(),
    }
  }
}

pub(in crate::pipeline) fn encode_claims(claims: &[Vec<Val>]) -> Vec<u8> {
  let mut bytes = (claims.len() as u64).to_le_bytes().to_vec();
  for claim in claims {
    bytes.extend((claim.len() as u64).to_le_bytes());
    for value in claim {
      bytes.extend(value.as_canonical_u64().to_le_bytes());
    }
  }
  bytes
}

pub(in crate::pipeline) fn decode_claims(
  bytes: &[u8],
) -> std::result::Result<Vec<Vec<Val>>, String> {
  let (words, remainder) = bytes.as_chunks::<8>();
  if !remainder.is_empty() {
    return Err("unaligned claims".into());
  }
  let mut words = words.iter();
  let n = u64::from_le_bytes(*words.next().ok_or("missing claims count")?);
  let mut claims = Vec::new();
  for _ in 0..n {
    let len = u64::from_le_bytes(*words.next().ok_or("missing claim length")?);
    let mut claim = Vec::new();
    for _ in 0..len {
      let v = u64::from_le_bytes(*words.next().ok_or("missing claim value")?);
      if v >= Val::ORDER_U64 {
        return Err("noncanonical claim".into());
      }
      claim.push(Val::from_u64(v));
    }
    claims.push(claim);
  }
  if words.next().is_some() {
    return Err("trailing claims".into());
  }
  Ok(claims)
}

/// The claims a first-stage proof of `count` partitions must expose, as the
/// lowering derives them: the statement words, one activation anchor per table
/// partition and the six fixed namespace anchors.
pub(in crate::pipeline) fn first_claims(
  count: usize,
  statement: &super::super::statement::Statement,
) -> Vec<Vec<Scalar>> {
  let namespace = Scalar::from_u8(super::construct::FIRST_NAMESPACE);
  let mut expected: Vec<_> = std::iter::once(0)
    .chain(statement.iter().copied())
    .enumerate()
    .map(|(i, word)| {
      vec![
        namespace,
        Scalar::ONE,
        Scalar::from_usize(i),
        Scalar::from_u64(word),
      ]
    })
    .collect();
  if count > 11 {
    expected.extend(
      (0..count - 10)
        .map(|i| vec![namespace, Scalar::from_u8(3), Scalar::from_usize(i)]),
    );
  }
  expected.extend((0..6).map(|i| {
    vec![
      namespace,
      Scalar::from_u8(4),
      Scalar::from_u8(3),
      Scalar::from_usize(i),
    ]
  }));
  expected
}
