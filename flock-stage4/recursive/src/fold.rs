//! Keyed native accumulation. Every incoming claim is bound into a compiled
//! BLAKE3 transcript, then reduced by Flock's two sumchecks to one Eq/Eq claim.
//! Large static tables are read by the prover and final verifier only.
use crate::{backend::NativeBuilder, constrain_chained_blake3_transcript};
use anyhow::{Result, ensure};
use flock_prover::{
  challenger::{Challenger, FsChallenger},
  circuit::Circuit,
  field::F128,
  matrix_fold::{
    self, FoldGrinding, FoldMatrix, JaggedClaim, JaggedRowWeight, JaggedTable,
    MatrixClaim, Weight,
  },
  schedule::Registry,
  transcript_record::RecordingChallenger,
};
use ix_stage4_trace::F128MatrixSideV1;
use ixby_stage4_exec::{CompiledTranscriptPlan, TranscriptPlan};
use std::{collections::BTreeMap, sync::Arc};

const DOMAIN: &[u8] = b"IxBy/Flock/grammar-tree/folds/v0\0";
const GRINDING: FoldGrinding = FoldGrinding::per_challenge_128();
type Word = usize;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum TableKey {
  Boolean {
    registry: [u8; 32],
    table: u64,
    side: F128MatrixSideV1,
    variables: u32,
  },
  Structure {
    circuit: [u8; 32],
    rows: u32,
    columns: u32,
  },
  Jagged {
    circuit: [u8; 32],
    rows: u32,
    columns: u32,
  },
  /// Execution trees may share a complete identical Boolean matrix across
  /// distinct registries. The digest binds every sparse entry and dimension.
  Matrix {
    digest: [u8; 32],
    variables: u32,
  },
}
impl TableKey {
  pub(crate) fn dimensions(&self) -> (usize, usize) {
    match self {
      Self::Boolean { variables, .. } | Self::Matrix { variables, .. } => {
        (*variables as usize, *variables as usize)
      },
      Self::Structure { rows, columns, .. }
      | Self::Jagged { rows, columns, .. } => {
        (*rows as usize, *columns as usize)
      },
    }
  }
  fn jagged(&self) -> bool {
    matches!(self, Self::Jagged { .. })
  }
  pub(crate) fn encode(&self) -> Vec<u8> {
    let mut out = Vec::new();
    match self {
      Self::Boolean { registry, table, side, variables } => {
        out.push(0);
        out.extend(registry);
        out.extend(table.to_le_bytes());
        out.push(*side as u8);
        out.extend(variables.to_le_bytes());
      },
      Self::Structure { circuit, rows, columns }
      | Self::Jagged { circuit, rows, columns } => {
        out.push(if self.jagged() { 2 } else { 1 });
        out.extend(circuit);
        out.extend(rows.to_le_bytes());
        out.extend(columns.to_le_bytes());
      },
      Self::Matrix { digest, variables } => {
        out.push(3);
        out.extend(digest);
        out.extend(variables.to_le_bytes());
      },
    }
    out
  }
}

#[derive(Clone)]
pub(crate) enum StaticTable {
  Boolean { registry: Arc<Registry>, table: usize, side: F128MatrixSideV1 },
  Structure(Arc<Circuit>),
  Jagged(Arc<JaggedTable>),
}
impl StaticTable {
  fn with_dense<T>(&self, f: impl FnOnce(&dyn FoldMatrix) -> T) -> T {
    match self {
      Self::Boolean { registry, table, side } => {
        let ty = &registry.boolean_types()[*table];
        f(match side {
          F128MatrixSideV1::A => &ty.a_0,
          F128MatrixSideV1::B => &ty.b_0,
        })
      },
      Self::Structure(circuit) => {
        // Reproduction of the pre-optimization native evaluator is test-only.
        // Both paths expose the same complete fixed table to the same fold.
        #[cfg(test)]
        if std::env::var("IXBY_RECURSION_REFERENCE_STRUCTURE")
          .is_ok_and(|v| v == "1")
        {
          return f(&flock_prover::circuit::SigmaAssertion::matrix(circuit));
        }
        f(&crate::structure::StructureMatrix::new(circuit))
      },
      Self::Jagged(_) => {
        unreachable!("jagged tables use the sparse pair-space fold")
      },
    }
  }
  pub(crate) fn check(&self, claim: &MatrixClaim) -> bool {
    match self {
      Self::Jagged(table) => matrix_fold::discharge_jagged(claim, table),
      _ => self.with_dense(|table| claim.check_direct(table)),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Row {
  Tensor { low: Vec<Word>, point: Vec<Word> },
  Combo(Vec<(Word, u32)>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Claim {
  pub(crate) row: Row,
  pub(crate) column_low: Vec<Word>,
  pub(crate) column: Vec<Word>,
  pub(crate) value: Word,
}
impl Claim {
  pub(crate) fn plain(
    b: &mut NativeBuilder,
    row: Vec<Word>,
    column: Vec<Word>,
    value: Word,
  ) -> Self {
    let one = b.constant(F128::ONE);
    Self {
      row: Row::Tensor { low: vec![one], point: row },
      column_low: vec![one],
      column,
      value,
    }
  }
  fn matrix(&self, values: &[F128]) -> MatrixClaim {
    let Row::Tensor { low, point } = &self.row else {
      unreachable!("dense tensor row")
    };
    MatrixClaim {
      row: Weight::low_eq(words(values, low), words(values, point)),
      col: Weight::low_eq(
        words(values, &self.column_low),
        words(values, &self.column),
      ),
      value: values[self.value],
    }
  }
  fn jagged(&self, values: &[F128]) -> JaggedClaim {
    let row = match &self.row {
      Row::Tensor { low, point } => {
        JaggedRowWeight::Eq(values[low[0]], words(values, point))
      },
      Row::Combo(terms) => JaggedRowWeight::Combo(
        terms.iter().map(|&(v, a)| (values[v], a)).collect(),
      ),
    };
    JaggedClaim {
      row,
      col: words(values, &self.column),
      value: values[self.value],
    }
  }
}
fn words(values: &[F128], indices: &[usize]) -> Vec<F128> {
  indices.iter().map(|&i| values[i]).collect()
}

pub(crate) type Groups = BTreeMap<TableKey, (StaticTable, Vec<Claim>)>;
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClaimShape {
  low: usize,
  point: usize,
  combo: Option<Vec<u32>>,
  column_low: usize,
  column: usize,
}
impl From<&Claim> for ClaimShape {
  fn from(c: &Claim) -> Self {
    let (low, point, combo) = match &c.row {
      Row::Tensor { low, point } => (low.len(), point.len(), None),
      Row::Combo(terms) => (0, 0, Some(terms.iter().map(|t| t.1).collect())),
    };
    Self {
      low,
      point,
      combo,
      column_low: c.column_low.len(),
      column: c.column.len(),
    }
  }
}
#[derive(Clone, Copy)]
struct Round {
  one: usize,
  infinity: usize,
  challenge: usize,
}
struct GroupPlan {
  key: TableKey,
  table: StaticTable,
  shapes: Vec<ClaimShape>,
  payload: usize,
  /// All observed incoming words, including fixed headers and addresses.
  bindings: Vec<usize>,
  lambdas: Vec<usize>,
  columns: Vec<Round>,
  bridge: Vec<usize>,
  mus: Vec<usize>,
  rows: Vec<Round>,
  value: usize,
}
pub(crate) struct FoldPlan {
  transcript: CompiledTranscriptPlan,
  groups: Vec<GroupPlan>,
}
fn index(i: u64) -> usize {
  usize::try_from(i).expect("compiled transcript index")
}
fn indices(v: Vec<u64>) -> Vec<usize> {
  v.into_iter().map(index).collect()
}
fn rounds(tape: &mut TranscriptPlan, count: usize) -> Vec<Round> {
  (0..count)
    .map(|_| Round {
      one: index(tape.observe()),
      infinity: index(tape.observe()),
      challenge: index(tape.squeeze(Some(GRINDING.round_bits))),
    })
    .collect()
}
impl FoldPlan {
  pub(crate) fn compile(groups: &Groups) -> Result<Self> {
    ensure!(!groups.is_empty(), "empty recursive accumulator");
    let mut tape = TranscriptPlan::default();
    let mut plans = Vec::new();
    for (key, (table, claims)) in groups {
      let (rows, columns) = key.dimensions();
      ensure!(!claims.is_empty(), "empty recursive fold family");
      let payload = index(tape.bytes(key.encode().len()));
      let mut bindings = Vec::new();
      if key.jagged() {
        tape.label(b"flock-jagged-fold-v0");
        bindings.push(index(tape.observe()));
      } else {
        tape.label(b"flock-matrix-fold-v0");
      }
      for c in claims {
        match &c.row {
          Row::Tensor { low, point } => {
            ensure!(
              low.len().is_power_of_two()
                && low.len().ilog2() as usize + point.len() == rows,
              "fold row dimensions"
            );
            if key.jagged() {
              ensure!(low.len() == 1, "jagged Eq scale width");
              bindings.push(index(tape.observe())); // Eq header
              bindings.push(index(tape.observe())); // scale
            } else {
              bindings.extend(indices(tape.observe_slice(low.len())));
            }
            bindings.extend(indices(tape.observe_slice(point.len())));
          },
          Row::Combo(terms) => {
            ensure!(
              key.jagged()
                && terms.iter().all(|t| u64::from(t.1) < (1u64 << rows)),
              "jagged Combo dimensions"
            );
            bindings.push(index(tape.observe()));
            for _ in terms {
              bindings.push(index(tape.observe()));
              bindings.push(index(tape.observe()));
            }
          },
        }
        ensure!(
          c.column_low.len().is_power_of_two()
            && c.column_low.len().ilog2() as usize + c.column.len() == columns,
          "fold column dimensions"
        );
        if key.jagged() {
          ensure!(c.column_low.len() == 1, "jagged column scale width");
        } else {
          bindings.extend(indices(tape.observe_slice(c.column_low.len())));
        }
        bindings.extend(indices(tape.observe_slice(c.column.len())));
        bindings.push(index(tape.observe()));
      }
      plans.push(GroupPlan {
        key: key.clone(),
        table: table.clone(),
        shapes: claims.iter().map(ClaimShape::from).collect(),
        payload,
        bindings,
        lambdas: indices(
          tape.squeeze_slice(claims.len(), Some(GRINDING.combination_bits)),
        ),
        columns: rounds(&mut tape, columns),
        bridge: (0..claims.len()).map(|_| index(tape.observe())).collect(),
        mus: indices(
          tape.squeeze_slice(claims.len(), Some(GRINDING.combination_bits)),
        ),
        rows: rounds(&mut tape, rows),
        value: index(tape.observe()),
      });
    }
    Ok(Self { transcript: tape.compile(DOMAIN)?, groups: plans })
  }

  pub(crate) fn emit(
    &self,
    b: &mut NativeBuilder,
    inputs: &Groups,
  ) -> Result<Vec<(TableKey, Claim)>> {
    let mut profile = crate::profile::Profile::graph("fold", b);
    ensure!(
      inputs.len() == self.groups.len(),
      "recursive fold family coverage"
    );
    for ((key, (_, claims)), plan) in inputs.iter().zip(&self.groups) {
      ensure!(
        *key == plan.key
          && claims.iter().map(ClaimShape::from).collect::<Vec<_>>()
            == plan.shapes,
        "recursive fold claim coverage/shape"
      );
    }
    let witness = if b.is_shape_only() {
      None
    } else {
      let mut ch =
        RecordingChallenger::new(FsChallenger::with_chained_blake3(DOMAIN));
      for plan in &self.groups {
        let mut family_profile = crate::profile::Profile::new("fold_family");
        let claims = &inputs[&plan.key].1;
        ch.observe_bytes(&plan.key.encode());
        match &plan.table {
          StaticTable::Jagged(table) => {
            let claims =
              claims.iter().map(|c| c.jagged(&b.values)).collect::<Vec<_>>();
            matrix_fold::prove_fold_jagged_with_grinding(
              table, &claims, GRINDING, &mut ch,
            );
          },
          table => {
            let claims =
              claims.iter().map(|c| c.matrix(&b.values)).collect::<Vec<_>>();
            table.with_dense(|table| {
              let combs = claims
                .iter()
                .map(|c| {
                  table.col_marginal(
                    &c.row.materialize(),
                    1usize << plan.key.dimensions().1,
                  )
                })
                .collect::<Vec<_>>();
              matrix_fold::prove_fold_with_grinding(
                table, &combs, &claims, GRINDING, &mut ch,
              );
            });
          },
        }
        family_profile.mark(match &plan.table {
          StaticTable::Boolean { .. } => "boolean",
          StaticTable::Structure(_) => "structure",
          StaticTable::Jagged(_) => "jagged",
        });
      }
      Some(self.transcript.witness(&ch)?)
    };
    profile.stage("native_sumchecks", b);
    let observed = witness
      .as_ref()
      .map(|w| w.observed_values().to_vec())
      .unwrap_or_else(|| vec![[0; 16]; self.transcript.observed_values()]);
    let payloads = witness
      .as_ref()
      .map(|w| w.byte_payloads().to_vec())
      .unwrap_or_else(|| {
        self.transcript.payload_lengths().iter().map(|&n| vec![0; n]).collect()
      });
    let challenges = witness
      .as_ref()
      .map(|w| w.challenges().to_vec())
      .unwrap_or_else(|| vec![[0; 16]; self.transcript.challenges()]);
    let trace = witness
      .as_ref()
      .map(|w| w.chained_blake3())
      .unwrap_or(self.transcript.topology());
    let transcript = constrain_chained_blake3_transcript(
      b,
      trace,
      &observed,
      &payloads,
      &challenges,
    )?;
    profile.stage("transcript", b);
    let observed =
      transcript.observed_values.iter().map(|v| v.word(b)).collect::<Vec<_>>();
    let challenges =
      transcript.challenges.iter().map(|v| v.word(b)).collect::<Vec<_>>();
    let zero = b.constant(F128::ZERO);
    let one = b.constant(F128::ONE);
    let mut roots = Vec::new();
    for plan in &self.groups {
      crate::pair::bind_bytes(
        b,
        &transcript.byte_payloads[plan.payload],
        &plan.key.encode(),
      )?;
      let claims = &inputs[&plan.key].1;
      let mut binding_words = Vec::new();
      if plan.key.jagged() {
        binding_words.push(b.constant(F128::new(
          u64::try_from(plan.key.dimensions().0)?,
          u64::try_from(claims.len())?,
        )));
      }
      for c in claims {
        match &c.row {
          Row::Tensor { low, point } => {
            if plan.key.jagged() {
              binding_words
                .push(b.constant(F128::new(0, u64::try_from(point.len())?)));
            }
            binding_words.extend_from_slice(low);
            binding_words.extend_from_slice(point);
          },
          Row::Combo(terms) => {
            binding_words
              .push(b.constant(F128::new(1, u64::try_from(terms.len())?)));
            for &(coefficient, address) in terms {
              binding_words.push(coefficient);
              binding_words.push(b.constant(F128::new(u64::from(address), 0)));
            }
          },
        }
        if plan.key.jagged() {
          b.equal(c.column_low[0], one);
        } else {
          binding_words.extend_from_slice(&c.column_low);
        }
        binding_words.extend_from_slice(&c.column);
        binding_words.push(c.value);
      }
      ensure!(binding_words.len() == plan.bindings.len(), "fold binding width");
      for (&actual, &address) in binding_words.iter().zip(&plan.bindings) {
        b.equal(actual, observed[address]);
      }
      let lambdas =
        plan.lambdas.iter().map(|&i| challenges[i]).collect::<Vec<_>>();
      let values = claims.iter().map(|c| c.value).collect::<Vec<_>>();
      let target = dot(b, &lambdas, &values, zero);
      let (column_running, column) =
        replay_rounds(b, &plan.columns, target, &observed, &challenges);
      let bridge = plan.bridge.iter().map(|&i| observed[i]).collect::<Vec<_>>();
      let mut expected = zero;
      for ((c, &lambda), &bridge) in claims.iter().zip(&lambdas).zip(&bridge) {
        let evaluation =
          tensor(b, &c.column_low, &c.column, &column, one, zero);
        let scaled = b.multiply(lambda, evaluation);
        let term = b.multiply(scaled, bridge);
        expected = b.add(expected, term);
      }
      b.equal(column_running, expected);
      let mus = plan.mus.iter().map(|&i| challenges[i]).collect::<Vec<_>>();
      let target = dot(b, &mus, &bridge, zero);
      let (row_running, row) =
        replay_rounds(b, &plan.rows, target, &observed, &challenges);
      let mut weight = zero;
      for (c, &mu) in claims.iter().zip(&mus) {
        let evaluation = match &c.row {
          Row::Tensor { low, point } => tensor(b, low, point, &row, one, zero),
          Row::Combo(terms) => {
            let eq = eq_table(b, &row, one);
            let mut total = zero;
            for &(coefficient, address) in terms {
              let term = b.multiply(coefficient, eq[usize::try_from(address)?]);
              total = b.add(total, term);
            }
            total
          },
        };
        let term = b.multiply(mu, evaluation);
        weight = b.add(weight, term);
      }
      let value = observed[plan.value];
      let expected = b.multiply(weight, value);
      b.equal(row_running, expected);
      roots.push((plan.key.clone(), Claim::plain(b, row, column, value)));
    }
    profile.stage("algebra", b);
    Ok(roots)
  }
}
fn dot(b: &mut NativeBuilder, a: &[Word], c: &[Word], zero: Word) -> Word {
  let mut total = zero;
  for (&a, &c) in a.iter().zip(c) {
    let term = b.multiply(a, c);
    total = b.add(total, term);
  }
  total
}
fn eq_table(b: &mut NativeBuilder, point: &[Word], one: Word) -> Vec<Word> {
  let mut table = vec![one];
  for &r in point {
    let complement = b.add(one, r);
    let mut next = Vec::with_capacity(2 * table.len());
    for &v in &table {
      next.push(b.multiply(v, complement));
    }
    for &v in &table {
      next.push(b.multiply(v, r));
    }
    table = next;
  }
  table
}
fn tensor(
  b: &mut NativeBuilder,
  low: &[Word],
  point: &[Word],
  rho: &[Word],
  one: Word,
  zero: Word,
) -> Word {
  let n = low.len().ilog2() as usize;
  let eq = eq_table(b, &rho[..n], one);
  let mut result = dot(b, low, &eq, zero);
  for (&p, &r) in point.iter().zip(&rho[n..]) {
    let sum = b.add(p, r);
    let factor = b.add(one, sum);
    result = b.multiply(result, factor);
  }
  result
}
fn replay_rounds(
  b: &mut NativeBuilder,
  rounds: &[Round],
  mut running: Word,
  observed: &[Word],
  challenges: &[Word],
) -> (Word, Vec<Word>) {
  let mut point = Vec::with_capacity(rounds.len());
  for round in rounds {
    let (q1, inf, r) = (
      observed[round.one],
      observed[round.infinity],
      challenges[round.challenge],
    );
    let q0 = b.add(running, q1);
    let linear = b.add(running, inf);
    let ir = b.multiply(inf, r);
    let quadratic = b.multiply(ir, r);
    let linear = b.multiply(linear, r);
    let nonconstant = b.add(quadratic, linear);
    running = b.add(q0, nonconstant);
    point.push(r);
  }
  (running, point)
}
