use std::borrow::Borrow;

use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};

use super::CubicValue as E;
use multi_stark::eval::VarValues;
use multi_stark::expr::RowOffset;
use multi_stark::expr::Source;
use multi_stark::graph::ConstraintGraph;
use multi_stark::graph::Node;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;
use multi_stark::system::Circuit;

/// Extension degree of Protocol v6 (`F_p^3 = F_p[X] / (X^3 - X - 1)`).
pub(super) const EXTENSION_DEGREE: usize = 3;

/// Boundary wires that the transcript gadget binds. None of these values
/// is authenticated by the algebraic checks themselves.
#[derive(Clone, Copy, Debug)]
pub struct AlgebraicChallenges {
  pub beta: E,
  pub gamma: E,
  pub alpha: E,
  pub zeta: E,
}

/// Openings of one active circuit. Every entry is the evaluation of a
/// **base column** in the challenge field, including the stage-2 columns.
#[derive(Clone, Debug)]
pub struct CircuitOpenings {
  pub preprocessed: [Vec<E>; 2],
  pub main: [Vec<E>; 2],
  pub stage2: [Vec<E>; 2],
  pub quotient: Vec<E>,
  pub accumulator: E,
}

/// An explicitly unauthenticated algebraic-verifier input interface.
#[derive(Clone, Debug)]
pub struct AlgebraicInputs {
  pub claims: Vec<Vec<Value>>,
  pub challenges: AlgebraicChallenges,
  /// Active-circuit order (a fixed subset of canonical circuit order).
  pub openings: Vec<CircuitOpenings>,
}

impl AlgebraicInputs {
  /// Allocate inputs using only fixed circuit metadata and claim lengths.
  /// Claims are public. Openings and challenges are private boundary wires
  /// which a complete verifier MUST bind to its PCS and transcript gadgets.
  pub fn allocate<F: Field + multi_stark::traits::Field>(
    builder: &mut CircuitBuilder<F>,
    circuits: &[impl Borrow<Circuit<F>>],
    claim_lengths: &[usize],
  ) -> Self {
    let claims = claim_lengths
      .iter()
      .enumerate()
      .map(|(i, &len)| {
        (0..len)
          .map(|j| builder.public_input(format!("claim[{i}][{j}]")))
          .collect()
      })
      .collect();
    Self::with_claims(builder, circuits, claims)
  }

  /// Compose verification with caller-owned statement wires. Public exposure
  /// is the caller's choice; claims may be derived by other gadgets.
  pub fn with_claims<F: Field + multi_stark::traits::Field>(
    builder: &mut CircuitBuilder<F>,
    circuits: &[impl Borrow<Circuit<F>>],
    claims: Vec<Vec<Value>>,
  ) -> Self {
    let challenges = AlgebraicChallenges {
      beta: E::input(builder, "beta"),
      gamma: E::input(builder, "gamma"),
      alpha: E::input(builder, "alpha"),
      zeta: E::input(builder, "zeta"),
    };
    let openings = circuits
      .iter()
      .map(Borrow::borrow)
      .enumerate()
      .map(|(i, circuit)| {
        let mut row = |name, len| {
          (0..len)
            .map(|j| E::input(builder, &format!("circuit[{i}].{name}[{j}]")))
            .collect()
        };
        CircuitOpenings {
          preprocessed: [
            row("preprocessed", circuit.preprocessed_width),
            row("preprocessed_next", circuit.preprocessed_width),
          ],
          main: [
            row("main", circuit.main_width),
            row("main_next", circuit.main_width),
          ],
          stage2: [
            row("stage2", circuit.stage_2_width),
            row("stage2_next", circuit.stage_2_width),
          ],
          quotient: row(
            "quotient",
            circuit.quotient_degree() * EXTENSION_DEGREE,
          ),
          accumulator: E::input(builder, &format!("circuit[{i}].accumulator")),
        }
      })
      .collect();
    Self { claims, challenges, openings }
  }
}

/// Unnormalized selectors, matching the native two-adic subgroup verifier.
#[derive(Clone, Copy, Debug)]
pub struct Selectors {
  pub is_first_row: E,
  pub is_last_row: E,
  pub is_transition: E,
  pub inv_vanishing: E,
}

/// Intermediate wires for differential tests and subsequent PCS integration.
pub struct CircuitEvaluation {
  pub selectors: Selectors,
  pub zeta_next: E,
  pub nodes: Vec<E>,
  pub constraints: Vec<E>,
  pub composition: E,
  pub quotient: E,
}

pub struct AlgebraicOutputs {
  pub claims_accumulator: E,
  pub circuits: Vec<CircuitEvaluation>,
}

fn sweep<F: Field + multi_stark::traits::Field>(
  builder: &mut CircuitBuilder<F>,
  graph: &ConstraintGraph<F>,
  view: &VarValues<'_, E>,
) -> Vec<E> {
  let zero = <F as PrimeCharacteristicRing>::ZERO;
  let mut values: Vec<E> = Vec::with_capacity(graph.nodes.len());
  for node in &graph.nodes {
    let value = match *node {
      Node::Const(c) => E::constant(builder, [c, zero, zero]),
      Node::Var(col) => {
        let rows = match col.source {
          Source::Preprocessed => view.preprocessed,
          Source::Main => view.main,
          Source::Stage2 => view.stage2,
        };
        let row = match col.offset {
          RowOffset::Current => 0,
          RowOffset::Next => 1,
        };
        rows[row][col.index as usize]
      },
      Node::Public(i) => view.publics[i as usize],
      Node::IsFirstRow => view.is_first_row,
      Node::IsLastRow => view.is_last_row,
      Node::IsTransition => view.is_transition,
      Node::Add(a, b) => values[a.index()].add(builder, values[b.index()]),
      Node::Sub(a, b) => values[a.index()].sub(builder, values[b.index()]),
      Node::Mul(a, b) => values[a.index()].mul(builder, values[b.index()]),
      Node::Neg(a) => values[a.index()].neg(builder),
    };
    values.push(value);
  }
  values
}

/// Multiply triples of coordinate-polynomial evaluations in
/// `E[Y] / (Y^3 - Y - 1)` via Karatsuba (6 extension multiplications).
/// Each coordinate is itself in the OOD challenge field. This is NOT ordinary
/// multiplication after recombining the three stage-2 columns into one
/// extension value.
fn coordinate_mul<F: Field + multi_stark::traits::Field>(
  builder: &mut CircuitBuilder<F>,
  a: [E; EXTENSION_DEGREE],
  b: [E; EXTENSION_DEGREE],
) -> [E; EXTENSION_DEGREE] {
  let v0 = a[0].mul(builder, b[0]);
  let v1 = a[1].mul(builder, b[1]);
  let v2 = a[2].mul(builder, b[2]);
  let a01 = a[0].add(builder, a[1]);
  let b01 = b[0].add(builder, b[1]);
  let m01 = a01.mul(builder, b01).sub(builder, v0).sub(builder, v1);
  let a02 = a[0].add(builder, a[2]);
  let b02 = b[0].add(builder, b[2]);
  let m02 = a02.mul(builder, b02).sub(builder, v0).sub(builder, v2);
  let a12 = a[1].add(builder, a[2]);
  let b12 = b[1].add(builder, b[2]);
  let m12 = a12.mul(builder, b12).sub(builder, v1).sub(builder, v2);
  [
    v0.add(builder, m12),
    m01.add(builder, m12).add(builder, v2),
    m02.add(builder, v1).add(builder, v2),
  ]
}

/// Constrain the claim balance and all OOD/quotient identities.
///
/// Supported scope: Protocol v6 cubic trinomial challenge field
/// `F_p[X]/(X^3 - X - 1)`, two-adic *subgroup* trace domains, fixed active
/// circuits/heights, and grouped lookups.
/// Unsupported metadata or mismatched wire shapes are construction errors
/// and panic. No proof/witness values affect circuit construction.
///
/// This is NOT a proof verifier: callers must additionally constrain exact
/// Fiat-Shamir replay and PCS verification before making that claim.
pub fn constrain_algebraic_checks<
  F: TwoAdicField + multi_stark::traits::Field,
>(
  builder: &mut CircuitBuilder<F>,
  circuits: &[impl Borrow<Circuit<F>>],
  log_degrees: &[u8],
  inputs: &AlgebraicInputs,
) -> AlgebraicOutputs {
  let zero = E::constant(
    builder,
    [<F as PrimeCharacteristicRing>::ZERO; EXTENSION_DEGREE],
  );
  constrain_algebraic_checks_with_residual(
    builder,
    circuits,
    log_degrees,
    inputs,
    zero,
  )
}

/// Batch shards can end in a nonzero residual; the batch caller must constrain
/// its value against the verifier-side messages (and any other shard residuals).
pub(super) fn constrain_algebraic_checks_with_residual<
  F: TwoAdicField + multi_stark::traits::Field,
>(
  builder: &mut CircuitBuilder<F>,
  circuits: &[impl Borrow<Circuit<F>>],
  log_degrees: &[u8],
  inputs: &AlgebraicInputs,
  residual: E,
) -> AlgebraicOutputs {
  let circuits: Vec<&Circuit<F>> =
    circuits.iter().map(Borrow::borrow).collect();
  assert!(!circuits.is_empty(), "at least one active circuit is required");
  assert_eq!(circuits.len(), log_degrees.len());
  assert_eq!(circuits.len(), inputs.openings.len());
  for ((circuit, &log_degree), opening) in
    circuits.iter().zip(log_degrees).zip(&inputs.openings)
  {
    assert_eq!(
      circuit.num_publics,
      4 * EXTENSION_DEGREE,
      "cubic challenge field required"
    );
    assert!(
      (1..=multi_stark::lookup::MAX_LOOKUP_GROUP)
        .contains(&circuit.lookup_group_size)
    );
    assert!(usize::from(log_degree) <= F::TWO_ADICITY);
    let height =
      1usize.checked_shl(u32::from(log_degree)).expect("height overflow");
    if circuit.preprocessed_height != 0 {
      assert_eq!(circuit.preprocessed_height, height);
    }
    for row in 0..2 {
      assert_eq!(opening.preprocessed[row].len(), circuit.preprocessed_width);
      assert_eq!(opening.main[row].len(), circuit.main_width);
      assert_eq!(opening.stage2[row].len(), circuit.stage_2_width);
    }
    assert_eq!(
      opening.quotient.len(),
      circuit.quotient_degree() * EXTENSION_DEGREE
    );
  }
  let f_zero = <F as PrimeCharacteristicRing>::ZERO;
  let f_one = <F as PrimeCharacteristicRing>::ONE;
  let zero = E::constant(builder, [f_zero; EXTENSION_DEGREE]);
  let one = E::constant(builder, [f_one, f_zero, f_zero]);
  let AlgebraicChallenges { beta, gamma, alpha, zeta } = inputs.challenges;
  // Zero collapses current-row and next-row opening points.
  zeta.inverse(builder);
  let mut acc = zero;
  for claim in &inputs.claims {
    let mut fingerprint = zero;
    for &arg in claim.iter().rev() {
      let arg = E::from_base(builder, arg);
      fingerprint = fingerprint.mul(builder, gamma);
      fingerprint = fingerprint.add(builder, arg);
    }
    let message = beta.add(builder, fingerprint);
    let inverse = message.inverse(builder);
    acc = acc.add(builder, inverse);
  }
  let claims_accumulator = acc;
  inputs.openings.last().unwrap().accumulator.assert_equal(builder, residual);
  let mut evaluations = Vec::with_capacity(circuits.len());
  for ((circuit, &log_degree), opening) in
    circuits.iter().zip(log_degrees).zip(&inputs.openings)
  {
    let log_degree = usize::from(log_degree);
    let g = F::two_adic_generator(log_degree);
    let last = E::constant(builder, [Field::inverse(&g), f_zero, f_zero]);
    let zeta_pow_n = zeta.exp_power_of_2(builder, log_degree);
    let vanishing = zeta_pow_n.sub(builder, one);
    let inv_vanishing = vanishing.inverse(builder);
    let first_denominator = zeta.sub(builder, one);
    let first_inverse = first_denominator.inverse(builder);
    let is_transition = zeta.sub(builder, last);
    let last_inverse = is_transition.inverse(builder);
    let selectors = Selectors {
      is_first_row: vanishing.mul(builder, first_inverse),
      is_last_row: vanishing.mul(builder, last_inverse),
      is_transition,
      inv_vanishing,
    };
    let zeta_next = zeta.scale(builder, g);
    let next_acc = opening.accumulator;
    // The protocol's four extension publics are split into base
    // coordinates, each embedded separately into the OOD field.
    let publics: Vec<_> = [beta, gamma, acc, next_acc]
      .into_iter()
      .flat_map(|value| value.0)
      .map(|value| E::from_base(builder, value))
      .collect();
    let view = VarValues {
      preprocessed: [&opening.preprocessed[0], &opening.preprocessed[1]],
      main: [&opening.main[0], &opening.main[1]],
      stage2: [&opening.stage2[0], &opening.stage2[1]],
      publics: &publics,
      is_first_row: selectors.is_first_row,
      is_last_row: selectors.is_last_row,
      is_transition,
    };
    let nodes = sweep(builder, &circuit.graph, &view);
    let mut constraints: Vec<_> =
      circuit.graph.zeros.iter().map(|id| nodes[id.index()]).collect();
    let injection_norm = Field::inverse(
      &(<F as multi_stark::traits::Field>::from_usize(1 << log_degree) * g),
    );
    let injection: [E; EXTENSION_DEGREE] = std::array::from_fn(|k| {
      let delta = publics[3 * EXTENSION_DEGREE + k]
        .sub(builder, publics[2 * EXTENSION_DEGREE + k]);
      let delta = delta.scale(builder, injection_norm);
      selectors.is_last_row.mul(builder, delta)
    });
    if circuit.graph.lookups.is_empty() {
      for (k, inj) in injection.into_iter().enumerate() {
        let delta = opening.stage2[1][k].sub(builder, opening.stage2[0][k]);
        constraints.push(delta.add(builder, inj));
      }
    } else {
      let groups = circuit.graph.lookups.chunks(circuit.lookup_group_size);
      let count = groups.len();
      let gamma_coords = [
        publics[EXTENSION_DEGREE],
        publics[EXTENSION_DEGREE + 1],
        publics[EXTENSION_DEGREE + 2],
      ];
      for (i, group) in groups.enumerate() {
        let messages: Vec<_> = group
          .iter()
          .map(|lookup| {
            let mut message = [zero; EXTENSION_DEGREE];
            for arg in lookup.args.iter().rev() {
              message = coordinate_mul(builder, message, gamma_coords);
              message[0] = message[0].add(builder, nodes[arg.index()]);
            }
            for k in 0..EXTENSION_DEGREE {
              message[k] = message[k].add(builder, publics[k]);
            }
            message
          })
          .collect();
        let mut prefix = vec![[one, zero, zero]];
        for &message in &messages {
          prefix.push(coordinate_mul(
            builder,
            *prefix.last().unwrap(),
            message,
          ));
        }
        let mut suffix = vec![[one, zero, zero]; group.len() + 1];
        for j in (0..group.len()).rev() {
          suffix[j] = coordinate_mul(builder, messages[j], suffix[j + 1]);
        }
        let delta = std::array::from_fn(|k| {
          let target = if i + 1 < count {
            opening.stage2[0][EXTENSION_DEGREE * (i + 1) + k]
          } else {
            opening.stage2[1][k].add(builder, injection[k])
          };
          target.sub(builder, opening.stage2[0][EXTENSION_DEGREE * i + k])
        });
        let mut constraint =
          coordinate_mul(builder, *prefix.last().unwrap(), delta);
        for (j, lookup) in group.iter().enumerate() {
          let others = coordinate_mul(builder, prefix[j], suffix[j + 1]);
          for k in 0..EXTENSION_DEGREE {
            let term =
              others[k].mul(builder, nodes[lookup.multiplicity.index()]);
            constraint[k] = constraint[k].sub(builder, term);
          }
        }
        constraints.extend(constraint);
      }
    }
    assert_eq!(constraints.len(), circuit.constraint_count());
    let mut composition = zero;
    for &constraint in &constraints {
      composition = composition.mul(builder, alpha);
      composition = composition.add(builder, constraint);
    }
    // Unlike stage 2, quotient coefficient slices MUST be recombined
    // with the cubic extension basis [1, X, X^2] before summing powers of zeta^n.
    let mut quotient = zero;
    let mut power = one;
    for chunk in opening.quotient.as_chunks::<EXTENSION_DEGREE>().0 {
      let chunk = E::from_basis(builder, chunk[0], chunk[1], chunk[2]);
      let term = power.mul(builder, chunk);
      quotient = quotient.add(builder, term);
      power = power.mul(builder, zeta_pow_n);
    }
    let divided_composition = composition.mul(builder, inv_vanishing);
    divided_composition.assert_equal(builder, quotient);
    evaluations.push(CircuitEvaluation {
      selectors,
      zeta_next,
      nodes,
      constraints,
      composition,
      quotient,
    });
    acc = next_acc;
  }
  AlgebraicOutputs { claims_accumulator, circuits: evaluations }
}
