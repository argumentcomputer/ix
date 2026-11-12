//! Fixed-capacity PLONK export of the compiler's native BN254 circuits.
//!
//! The schema contains trusted constraints and fixed tables; witnesses contain
//! only main trace cells and the public call. Capacities are part of the key.

use super::{Bn254, kzg::Compiler};
use crate::kzg::Scalar;
use aiur::{Execution, field::FieldBackend, trace::TracePlan};
use multi_stark::{
  expr::{Expr, RowOffset, Source},
  system::CircuitInputs,
};
use p3_matrix::Matrix;
use serde::Serialize;
use std::collections::HashMap;

#[cfg(feature = "plonk")]
pub mod gnark;

pub const FORMAT: &str = "ix-aiur-plonk-v1";
/// The retained Ignition prefix currently admits at most this PLONK domain.
pub const MAX_DOMAIN: usize = 1 << 25;

#[derive(Clone, Debug, Serialize, PartialEq, Eq, Hash)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Node {
  Constant { value: String },
  Main { column: usize, next: bool },
  Fixed { column: usize, next: bool },
  First,
  Last,
  Transition,
  Add { a: usize, b: usize },
  Sub { a: usize, b: usize },
  Mul { a: usize, b: usize },
  Neg { a: usize },
}

#[derive(Clone, Debug, Serialize)]
pub struct Lookup {
  pub negative: bool,
  pub count: usize,
  pub args: Vec<usize>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Circuit {
  pub name: String,
  pub rows: usize,
  pub main_width: usize,
  pub fixed_width: usize,
  pub fixed: Vec<String>,
  pub nodes: Vec<Node>,
  pub constraints: Vec<usize>,
  pub lookups: Vec<Lookup>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Schema {
  pub format: &'static str,
  pub callable: usize,
  pub public_inputs: usize,
  /// Aiur call and ROM requests have boolean enables. Weighted schemas must
  /// leave this false so their integer multiplicities retain their meaning.
  pub boolean_requests: bool,
  pub circuits: Vec<Circuit>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Witness {
  pub public: Vec<String>,
  pub main: Vec<Vec<String>>,
}

fn scalar(value: Scalar) -> String {
  format!(
    "0x{:064x}",
    num_bigint::BigUint::from_bytes_le(
      &value
        .canonical_limbs_le()
        .into_iter()
        .flat_map(u64::to_le_bytes)
        .collect::<Vec<_>>()
    )
  )
}

#[derive(Default)]
struct Nodes {
  nodes: Vec<Node>,
  ids: HashMap<Node, usize>,
}

impl Nodes {
  fn insert(&mut self, expr: &Expr<Scalar>) -> Result<usize, String> {
    let node = match expr {
      Expr::Const(value) => Node::Constant { value: scalar(*value) },
      Expr::Var(reference) => {
        let column = reference.index as usize;
        let next = reference.offset == RowOffset::Next;
        match reference.source {
          Source::Main => Node::Main { column, next },
          Source::Preprocessed => Node::Fixed { column, next },
          Source::Stage2 => {
            return Err(
              "compiler input contains protocol-stage variables".into(),
            );
          },
        }
      },
      Expr::Public(_) => {
        return Err("compiler input contains protocol public variables".into());
      },
      Expr::IsFirstRow => Node::First,
      Expr::IsLastRow => Node::Last,
      Expr::IsTransition => Node::Transition,
      Expr::Add(a, b) => Node::Add { a: self.insert(a)?, b: self.insert(b)? },
      Expr::Sub(a, b) => Node::Sub { a: self.insert(a)?, b: self.insert(b)? },
      Expr::Mul(a, b) => Node::Mul { a: self.insert(a)?, b: self.insert(b)? },
      Expr::Neg(a) => Node::Neg { a: self.insert(a)? },
    };
    if let Some(&id) = self.ids.get(&node) {
      return Ok(id);
    }
    let id = self.nodes.len();
    self.ids.insert(node.clone(), id);
    self.nodes.push(node);
    Ok(id)
  }
}

fn circuit(
  input: &CircuitInputs<Scalar>,
  name: &str,
  rows: usize,
  pulls: impl ExactSizeIterator<Item = bool>,
) -> Result<Circuit, String> {
  if pulls.len() != input.lookups.len() {
    return Err("lookup direction count mismatch".into());
  }
  if rows == 0 || !rows.is_power_of_two() || rows > MAX_DOMAIN {
    return Err("PLONK row capacity must be a power of two in 1..=2^25".into());
  }
  if !input.ext_constraints.is_empty() {
    return Err("compiler input contains extension constraints".into());
  }
  let (fixed_width, fixed) = if let Some(fixed) = &input.preprocessed {
    if fixed.height() != rows {
      return Err(
        "fixed table capacity must equal its authenticated height".into(),
      );
    }
    (fixed.width, fixed.values.iter().copied().map(scalar).collect())
  } else {
    (0, vec![])
  };
  let mut nodes = Nodes::default();
  let constraints = input
    .constraints
    .iter()
    .map(|expr| nodes.insert(expr))
    .collect::<Result<_, _>>()?;
  let lookups = input
    .lookups
    .iter()
    .zip(pulls)
    .map(|(lookup, negative)| {
      let count = if negative {
        let Expr::Neg(count) = &lookup.multiplicity else {
          return Err("compiler pull is not a negated count".into());
        };
        count.as_ref()
      } else {
        &lookup.multiplicity
      };
      Ok(Lookup {
        negative,
        count: nodes.insert(count)?,
        args: lookup
          .args
          .iter()
          .map(|expr| nodes.insert(expr))
          .collect::<Result<_, String>>()?,
      })
    })
    .collect::<Result<_, String>>()?;
  Ok(Circuit {
    name: name.into(),
    rows,
    main_width: input.main_width,
    fixed_width,
    fixed,
    nodes: nodes.nodes,
    constraints,
    lookups,
  })
}

pub struct Exporter<'p, 'a> {
  plan: &'p TracePlan<'a, Bn254>,
  compiler: Compiler<'p, 'a>,
  entry: String,
  schema: Schema,
}

impl<'p, 'a> Exporter<'p, 'a> {
  /// Validate a typed public call to select the entry and public width. Its
  /// values do not affect the schema or key. Recursive inputs include depth.
  pub fn new(
    plan: &'p TracePlan<'a, Bn254>,
    capacities: &[usize],
    entry: &str,
    public_args: &[Scalar],
    output: &[Scalar],
  ) -> Result<Self, String> {
    let claim = plan.public_claim(entry, public_args, output)?;
    let compiler = Compiler::new(plan)?;
    if capacities.len() != compiler.inputs().len() {
      return Err("wrong PLONK circuit capacity count".into());
    }
    let mut rows = 0usize;
    let mut cells = 0usize;
    let mut lookup_slots = 1u64;
    let circuits = compiler
      .inputs()
      .iter()
      .zip(compiler.names())
      .zip(capacities)
      .enumerate()
      .map(|(index, ((input, name), &capacity))| {
        rows = rows
          .checked_add(capacity)
          .filter(|&rows| rows <= MAX_DOMAIN)
          .ok_or("PLONK capacity exceeds 2^25 total rows")?;
        cells = capacity
          .checked_mul(input.main_width)
          .and_then(|size| cells.checked_add(size))
          .filter(|&cells| cells <= MAX_DOMAIN)
          .ok_or("PLONK trace cells exceed 2^25")?;
        lookup_slots = u64::try_from(capacity)
          .ok()
          .and_then(|height| {
            height.checked_mul(u64::try_from(input.lookups.len()).ok()?)
          })
          .and_then(|slots| slots.checked_add(lookup_slots))
          .ok_or("PLONK lookup budget overflow")?;
        circuit(
          input,
          name,
          capacity,
          compiler.lookup_pulls(index).ok_or("missing lookup directions")?,
        )
      })
      .collect::<Result<_, String>>()?;
    let callable = usize::try_from(Bn254.try_to_u64(claim[1])?)
      .map_err(|_error| "callable index overflow")?;
    let schema = Schema {
      format: FORMAT,
      callable,
      public_inputs: claim.len() - 2,
      boolean_requests: true,
      circuits,
    };
    Ok(Self { plan, compiler, entry: entry.into(), schema })
  }

  pub fn schema(&self) -> &Schema {
    &self.schema
  }

  pub fn witness(
    &self,
    record: &Execution<Bn254>,
    args: &[Scalar],
  ) -> Result<Witness, String> {
    let public_args = self.plan.public_args(record, &self.entry, args)?;
    let claim =
      self.plan.public_claim(&self.entry, &public_args, &record.output)?;
    if claim.len() != self.schema.public_inputs + 2 {
      return Err("public claim width changed".into());
    }
    let traces = self.compiler.generate(record, &self.entry, args)?;
    let main = traces
      .into_iter()
      .zip(&self.schema.circuits)
      .map(|(mut trace, circuit)| {
        if trace.width != circuit.main_width || trace.height() > circuit.rows {
          return Err("execution exceeds PLONK capacity".into());
        }
        let cells = circuit
          .rows
          .checked_mul(circuit.main_width)
          .ok_or("PLONK witness size overflow")?;
        trace.values.resize(cells, Bn254.zero());
        Ok(trace.values.into_iter().map(scalar).collect())
      })
      .collect::<Result<_, String>>()?;
    Ok(Witness {
      public: claim[2..].iter().copied().map(scalar).collect(),
      main,
    })
  }
}
