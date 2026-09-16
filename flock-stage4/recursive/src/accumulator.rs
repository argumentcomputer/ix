//! Actual fixed-table claims shared by the grammar and execution trees.
//! Every inherited claim is read from the verified child's public wires and
//! included in the next fold; the final native verifier checks these tables.
use crate::{
  F128JaggedRowWeightVariablesV1,
  backend::NativeBuilder,
  fold::{Claim, Groups, Row, StaticTable, TableKey},
  pair::ChildWires,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::SigmaAssertion,
  field::F128,
  matrix_fold::{FoldMatrix, JaggedTable},
  pcs::jagged::JaggedParams,
  union::UnionInstance,
};
use ix_stage4_trace::F128MatrixSideV1;
use ixby_stage4_exec::FlockVerifierSetup;
use std::{
  collections::{BTreeMap, HashMap},
  sync::Arc,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PublishedRoot {
  pub(crate) key: TableKey,
  pub(crate) row: Vec<usize>,
  pub(crate) column: Vec<usize>,
  pub(crate) value: usize,
}
pub(crate) fn fresh_tables(
  setup: &dyn FlockVerifierSetup,
) -> Result<BTreeMap<TableKey, StaticTable>> {
  let shape = setup.verifier_shape();
  let registry = Arc::new(shape.registry.clone());
  let mut tables = BTreeMap::new();
  for (table, ty) in registry.boolean_types().iter().enumerate() {
    for side in [F128MatrixSideV1::A, F128MatrixSideV1::B] {
      let key = TableKey::Boolean {
        registry: registry.digest(),
        table: u64::try_from(table)?,
        side,
        variables: u32::try_from(ty.k_log)?,
      };
      tables.insert(
        key,
        StaticTable::Boolean { registry: registry.clone(), table, side },
      );
    }
  }
  let circuit = Arc::new(shape.circuit.clone());
  let structure = SigmaAssertion::matrix(&circuit);
  let key = TableKey::Structure {
    circuit: circuit.digest(),
    rows: structure.n_rows().ilog2(),
    columns: structure.n_cols().ilog2(),
  };
  tables.insert(key, StaticTable::Structure(circuit));
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = JaggedParams::from_heights(
    &union.jagged_heights(),
    union.n_log(),
    setup.pcs_params().m - 7,
  );
  let table = Arc::new(JaggedTable::from_params(&params));
  let key = TableKey::Jagged {
    circuit: shape.circuit.digest(),
    rows: u32::try_from(table.k)?,
    columns: u32::try_from(table.n_col_vars())?,
  };
  tables.insert(key, StaticTable::Jagged(table));
  Ok(tables)
}

fn add(
  groups: &mut Groups,
  tables: &BTreeMap<TableKey, StaticTable>,
  key: TableKey,
  claim: Claim,
) -> Result<()> {
  let table = tables
    .get(&key)
    .ok_or_else(|| anyhow::anyhow!("unknown recursive claim family"))?;
  groups
    .entry(key)
    .or_insert_with(|| (table.clone(), Vec::new()))
    .1
    .push(claim);
  Ok(())
}
pub(crate) fn collect_claims(
  b: &mut NativeBuilder,
  fresh: &BTreeMap<TableKey, StaticTable>,
  child: &ChildWires,
  groups: &mut Groups,
  inherited: Option<(
    &[PublishedRoot],
    &BTreeMap<TableKey, StaticTable>,
    usize,
  )>,
) -> Result<()> {
  let one = b.constant(F128::ONE);
  for claim in &child.algebra.deferred_matrix_claims {
    let id = claim.matrix;
    let key = TableKey::Boolean {
      registry: id.registry_digest,
      table: id.table,
      side: id.side,
      variables: id.variables,
    };
    let row = Row::Tensor {
      low: claim.row.low.iter().map(|v| v.word(b)).collect(),
      point: claim.row.point.iter().map(|v| v.word(b)).collect(),
    };
    let c = Claim {
      row,
      column_low: claim.column.low.iter().map(|v| v.word(b)).collect(),
      column: claim.column.point.iter().map(|v| v.word(b)).collect(),
      value: claim.value.word(b),
    };
    add(groups, fresh, key, c)?;
  }
  for claim in &child.wiring.circuit_structure_claims {
    let id = claim.matrix;
    let key = TableKey::Structure {
      circuit: id.circuit_digest,
      rows: id.row_variables,
      columns: id.column_variables,
    };
    let row = claim.row_point.iter().map(|v| v.word(b)).collect();
    let column = claim.column_point.iter().map(|v| v.word(b)).collect();
    let value = claim.value.word(b);
    let c = Claim::plain(b, row, column, value);
    add(groups, fresh, key, c)?;
  }
  let id = child.multipoint.jagged_assertion.matrix;
  let key = TableKey::Jagged {
    circuit: id.circuit_digest,
    rows: id.row_variables,
    columns: id.column_variables,
  };
  for claim in &child.multipoint.jagged_assertion.claims {
    let row = match &claim.row {
      F128JaggedRowWeightVariablesV1::Eq { scale, point } => Row::Tensor {
        low: vec![scale.word(b)],
        point: point.iter().map(|v| v.word(b)).collect(),
      },
      F128JaggedRowWeightVariablesV1::Combo { terms } => Row::Combo(
        terms.iter().map(|t| (t.coefficient.word(b), t.address)).collect(),
      ),
    };
    let c = Claim {
      row,
      column_low: vec![one],
      column: claim.column_point.iter().map(|v| v.word(b)).collect(),
      value: claim.value.word(b),
    };
    add(groups, fresh, key.clone(), c)?;
  }
  if let Some((roots, tables, outputs)) = inherited {
    ensure!(child.application.len() == outputs, "inherited accumulator width");
    for root in roots {
      let row =
        root.row.iter().map(|&i| child.application[i].word(b)).collect();
      let column =
        root.column.iter().map(|&i| child.application[i].word(b)).collect();
      let value = child.application[root.value].word(b);
      let c = Claim::plain(b, row, column, value);
      add(groups, tables, root.key.clone(), c)?;
    }
  }
  Ok(())
}
pub(crate) fn publish_roots(
  b: &mut NativeBuilder,
  application: Vec<usize>,
  roots: Vec<(TableKey, Claim)>,
) -> Result<Vec<PublishedRoot>> {
  b.graph.published = application;
  let mut indices = b
    .graph
    .published
    .iter()
    .enumerate()
    .map(|(i, &w)| (w, i))
    .collect::<HashMap<_, _>>();
  let mut publish = |word: usize| {
    *indices.entry(word).or_insert_with(|| {
      let i = b.graph.published.len();
      b.graph.published.push(word);
      i
    })
  };
  roots
    .into_iter()
    .map(|(key, c)| {
      let Row::Tensor { point, .. } = c.row else {
        unreachable!("folded row is Eq")
      };
      Ok(PublishedRoot {
        key,
        row: point.into_iter().map(&mut publish).collect(),
        column: c.column.into_iter().map(&mut publish).collect(),
        value: publish(c.value),
      })
    })
    .collect()
}
