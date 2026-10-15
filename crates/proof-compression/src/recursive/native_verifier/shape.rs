use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub(super) enum Round {
  Fixed,
  Main,
  Stage2,
  Quotient,
}

impl Round {
  pub(super) const ALL: [Self; 4] =
    [Self::Fixed, Self::Main, Self::Stage2, Self::Quotient];
  pub(super) const PCS: [Self; 4] =
    [Self::Main, Self::Stage2, Self::Quotient, Self::Fixed];

  pub(super) fn index(self) -> usize {
    self as usize
  }

  pub(super) fn commitment(self, proof: &Proof<KzgConfig>) -> &KzgCommitment {
    match self {
      Self::Fixed => {
        unreachable!("fixed points belong to the authenticated profile")
      },
      Self::Main => &proof.commitments.stage_1_trace,
      Self::Stage2 => &proof.commitments.stage_2_trace,
      Self::Quotient => &proof.commitments.quotient_chunks,
    }
  }

  pub(super) fn openings(
    self,
    proof: &Proof<KzgConfig>,
  ) -> Option<&[Vec<Vec<Scalar>>]> {
    match self {
      Self::Fixed => proof.preprocessed_opened_values.as_deref(),
      Self::Main => Some(&proof.stage_1_opened_values),
      Self::Stage2 => Some(&proof.stage_2_opened_values),
      Self::Quotient => Some(&proof.quotient_opened_values),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub(super) struct MatrixShape {
  pub(super) widths: Vec<usize>,
  pub(super) opening_rows: Vec<usize>,
}

impl MatrixShape {
  pub(super) fn check_commitment(
    &self,
    commitment: &KzgCommitment,
  ) -> Result<(), String> {
    if commitment.0.len() != self.widths.len()
      || commitment
        .0
        .iter()
        .zip(&self.widths)
        .any(|(row, &width)| row.len() != width)
    {
      return Err(
        "commitment dimensions differ from the verifier profile".into(),
      );
    }
    Ok(())
  }

  fn check_openings(
    &self,
    openings: &[Vec<Vec<Scalar>>],
  ) -> Result<(), String> {
    if openings.len() != self.widths.len()
      || openings.iter().zip(&self.widths).zip(&self.opening_rows).any(
        |((rows, &width), &count)| {
          rows.len() != count || rows.iter().any(|row| row.len() != width)
        },
      )
    {
      return Err("opening dimensions differ from the verifier profile".into());
    }
    Ok(())
  }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub(super) struct Shape {
  pub(super) logs: Vec<u8>,
  pub(super) rounds: [MatrixShape; 4],
  pub(super) opening_generators: Vec<Scalar>,
}

impl Shape {
  pub(super) fn new(
    profile: &Profile<'_>,
    logs: &[u8],
  ) -> Result<Self, String> {
    if logs.is_empty() || logs.len() != profile.circuits.len() {
      return Err("trace logs must cover every circuit".into());
    }
    if profile.max_log_degree > Scalar::TWO_ADICITY
      || profile.max_log_degree >= usize::BITS as usize
    {
      return Err("invalid maximum trace degree".into());
    }
    let mut rounds: [MatrixShape; 4] = std::array::from_fn(|_| MatrixShape {
      widths: vec![],
      opening_rows: vec![],
    });
    for (circuit, &log) in profile.circuits.iter().zip(logs) {
      let height =
        1usize.checked_shl(u32::from(log)).ok_or("trace height overflow")?;
      if usize::from(log) > profile.max_log_degree
        || circuit.preprocessed_height != height
        || circuit.preprocessed_width == 0
        || circuit.main_width == 0
      {
        return Err("invalid fixed/main trace dimensions".into());
      }
      if [circuit.main_width, circuit.preprocessed_width, circuit.stage_2_width]
        .iter()
        .any(|&width| u32::try_from(width).is_err())
      {
        return Err("trace width exceeds the column-index range".into());
      }
      validate_graph(circuit)?;
      let quotient = (circuit.max_constraint_degree.max(2) - 1)
        .checked_next_power_of_two()
        .ok_or("quotient degree overflow")?;
      if usize::from(log) + quotient.ilog2() as usize > Scalar::TWO_ADICITY {
        return Err("quotient domain exceeds scalar two-adicity".into());
      }
      let opens_next = |source| {
        circuit.graph.nodes.iter().any(|node| {
          matches!(node, Node::Var(column) if column.source == source && column.offset == RowOffset::Next)
        })
      };
      for (round, width, rows) in [
        (
          Round::Fixed,
          circuit.preprocessed_width,
          1 + usize::from(opens_next(Source::Preprocessed)),
        ),
        (
          Round::Main,
          circuit.main_width,
          1 + usize::from(opens_next(Source::Main)),
        ),
        (Round::Stage2, circuit.stage_2_width, 2),
        (Round::Quotient, quotient, 1),
      ] {
        let shape = &mut rounds[round.index()];
        shape.widths.push(width);
        shape.opening_rows.push(rows);
      }
    }
    rounds[Round::Fixed.index()].check_commitment(profile.fixed)?;
    let mut opening_generators = vec![];
    for round in Round::PCS {
      for (&log, &rows) in logs.iter().zip(&rounds[round.index()].opening_rows)
      {
        for row in 0..rows {
          let g = if row == 0 {
            Scalar::ONE
          } else {
            Scalar::two_adic_generator(usize::from(log))
          };
          if !opening_generators.contains(&g) {
            opening_generators.push(g);
          }
        }
      }
    }
    Ok(Self { logs: logs.to_vec(), rounds, opening_generators })
  }

  pub(super) fn checked_compact_len(&self) -> Result<usize, String> {
    let overflow = || "compact proof shape size overflow".to_owned();
    let mut points = self.opening_generators.len();
    let mut fields = self.logs.len().checked_sub(1).ok_or_else(overflow)?;
    for round in Round::ALL {
      let shape = &self.rounds[round.index()];
      if round != Round::Fixed {
        for &width in &shape.widths {
          points = points.checked_add(width).ok_or_else(overflow)?;
        }
      }
      for (&width, &rows) in shape.widths.iter().zip(&shape.opening_rows) {
        fields = fields
          .checked_add(width.checked_mul(rows).ok_or_else(overflow)?)
          .ok_or_else(overflow)?;
      }
    }
    points
      .checked_mul(48)
      .and_then(|bytes| {
        fields.checked_mul(32).and_then(|fields| bytes.checked_add(fields))
      })
      .and_then(|bytes| bytes.checked_add(5))
      .ok_or_else(overflow)
  }

  pub(super) fn validate(
    &self,
    proof: &Proof<KzgConfig>,
  ) -> Result<(), String> {
    if proof.active.len() != self.logs.len()
      || proof.active.iter().any(|&active| !active)
      || proof.log_degrees != self.logs
      || proof.intermediate_accumulators.len() != self.logs.len()
      || proof.intermediate_accumulators.last() != Some(&Scalar::ZERO)
      || proof.opening_proof.0.len() != self.opening_generators.len()
    {
      return Err(
        "proof activation, degree, accumulator or witness shape differs from profile"
          .into(),
      );
    }
    for round in Round::ALL {
      let shape = &self.rounds[round.index()];
      if round != Round::Fixed {
        shape.check_commitment(round.commitment(proof))?;
      }
      shape.check_openings(
        round.openings(proof).ok_or("missing fixed openings")?,
      )?;
    }
    Ok(())
  }
}

pub(super) fn validate_graph(
  circuit: &multi_stark::system::Circuit<Scalar>,
) -> Result<(), String> {
  let graph = &circuit.graph;
  if !(1..=multi_stark::lookup::MAX_LOOKUP_GROUP)
    .contains(&circuit.lookup_group_size)
    || circuit.num_lookups != graph.lookups.len()
    || circuit.num_publics != 4
    || graph.degrees.len() != graph.nodes.len()
    || graph.lookup_prefix_len > graph.nodes.len()
  {
    return Err("invalid circuit graph metadata".into());
  }
  let groups = graph.lookups.len().div_ceil(circuit.lookup_group_size).max(1);
  if circuit.stage_2_width != groups
    || graph.zeros.len().checked_add(groups) != Some(circuit.constraint_count)
  {
    return Err("invalid lookup/constraint dimensions".into());
  }
  for (index, node) in graph.nodes.iter().enumerate() {
    let valid = match *node {
      Node::Var(column) => {
        (column.index as usize)
          < match column.source {
            Source::Preprocessed => circuit.preprocessed_width,
            Source::Main => circuit.main_width,
            Source::Stage2 => circuit.stage_2_width,
          }
      },
      Node::Public(index) => index < 4,
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        a.index() < index && b.index() < index
      },
      Node::Neg(a) => a.index() < index,
      _ => true,
    };
    if !valid {
      return Err("invalid circuit graph reference".into());
    }
  }
  if graph.zeros.iter().any(|id| id.index() >= graph.nodes.len())
    || graph.lookups.iter().any(|lookup| {
      std::iter::once(&lookup.multiplicity)
        .chain(&lookup.args)
        .any(|id| id.index() >= graph.lookup_prefix_len)
    })
  {
    return Err("invalid constraint or lookup graph root".into());
  }
  Ok(())
}
