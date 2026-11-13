//! Fixed-capacity PLONK export of the compiler's native BN254 circuits.
//!
//! The schema contains trusted constraints and fixed tables. Root-call outputs
//! are public in the generic format; the terminal contract binds private affine
//! outputs to a constrained pairing assertion. Capacities are part of the key.

use super::{Bn254, kzg::Compiler};
use crate::kzg::Scalar;
use aiur::{Execution, field::FieldBackend, trace::TracePlan};
use multi_stark::{
  expr::{Expr, RowOffset, Source},
  system::CircuitInputs,
};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde::Serialize;
use std::collections::HashMap;

#[cfg(feature = "plonk")]
pub mod gnark;

pub const FORMAT: &str = "ix-aiur-plonk-v1";
pub const TERMINAL_FORMAT: &str = "ix-aiur-plonk-terminal-v1";
/// Largest power-of-two PLONK domain within the Ignition ceremony. Setup also
/// requires an authenticated file containing the actual `domain + 3` powers.
pub const MAX_DOMAIN: usize = crate::pipeline::plonk_limits::MAX_DOMAIN;
pub const MAX_PUBLIC_INPUTS: usize = 1 << 15;

/// Canonical big-endian field words, in typed public-call order.
pub fn public_bytes(values: &[Scalar]) -> Result<Vec<u8>, String> {
  if values.len() > MAX_PUBLIC_INPUTS {
    return Err("too many Aiur PLONK public fields".into());
  }
  let mut out = Vec::with_capacity(32 * values.len());
  for value in values {
    put_scalar(&mut out, *value);
  }
  Ok(out)
}

fn put_scalar(out: &mut Vec<u8>, value: Scalar) {
  for limb in value.canonical_limbs_le().into_iter().rev() {
    out.extend(limb.to_be_bytes());
  }
}

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
pub struct Pairing {
  pub curve: &'static str,
  pub encoding: &'static str,
  pub g2: [[String; 4]; 2],
}

fn no_private_outputs(count: &usize) -> bool {
  *count == 0
}

#[derive(Clone, Debug, Serialize)]
pub struct Schema {
  pub format: &'static str,
  pub callable: usize,
  pub public_inputs: usize,
  #[serde(skip_serializing_if = "no_private_outputs")]
  pub private_outputs: usize,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub pairing: Option<Pairing>,
  /// Aiur call and ROM requests have boolean enables. Weighted schemas must
  /// leave this false so their integer multiplicities retain their meaning.
  pub boolean_requests: bool,
  pub circuits: Vec<Circuit>,
}

#[derive(Clone, Debug, Serialize)]
pub struct Witness {
  pub public: Vec<String>,
  pub main: Vec<Vec<String>>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  pub private_outputs: Vec<String>,
}

fn scalar(value: Scalar) -> String {
  format!(
    "0x{:x}",
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
    return Err("PLONK row capacity must be a power of two in 1..=2^26".into());
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
          .ok_or("PLONK capacity exceeds 2^26 total rows")?;
        cells = capacity
          .checked_mul(input.main_width)
          .and_then(|size| cells.checked_add(size))
          .filter(|&cells| cells <= MAX_DOMAIN)
          .ok_or("PLONK trace cells exceed 2^26")?;
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
      private_outputs: 0,
      pairing: None,
      boolean_requests: true,
      circuits,
    };
    Ok(Self { plan, compiler, entry: entry.into(), schema })
  }

  /// Bind the deferred source relation to the terminal backend's pairing
  /// assertion. Its affine outputs are private, but remain part of the root
  /// call and challenge commitment. The fixed policy and anchors must match
  /// the independently trusted configuration used for compilation.
  pub fn terminal(
    plan: &'p TracePlan<'a, Bn254>,
    capacities: &[usize],
    public_args: &[Scalar],
    output: &[Scalar],
    configuration: &super::pairing::final_program::Configuration,
  ) -> Result<Self, String> {
    use super::pairing::final_program::{ACCUMULATOR_ENTRY, ACCUMULATOR_WORDS};
    if output.len() != ACCUMULATOR_WORDS {
      return Err("terminal pairing requires 18 private affine words".into());
    }
    let _ = super::g1::decode(&output[..9])?;
    let _ = super::g1::decode(&output[9..])?;
    let coordinates = configuration.terminal_coordinates(plan)?;
    let mut exporter =
      Self::new(plan, capacities, ACCUMULATOR_ENTRY, public_args, output)?;
    if exporter.schema.public_inputs != 2 + ACCUMULATOR_WORDS {
      return Err(
        "terminal pairing requires two public statement limbs".into(),
      );
    }
    let cells = exporter.schema.circuits.iter().try_fold(
      ACCUMULATOR_WORDS,
      |sum, circuit| {
        circuit
          .rows
          .checked_mul(circuit.main_width)
          .and_then(|n| sum.checked_add(n))
          .filter(|&n| n <= MAX_DOMAIN)
          .ok_or("terminal private cells exceed PLONK capacity")
      },
    )?;
    let _ = cells;
    exporter.schema.format = TERMINAL_FORMAT;
    exporter.schema.public_inputs = 2;
    exporter.schema.private_outputs = ACCUMULATOR_WORDS;
    exporter.schema.pairing = Some(Pairing {
      curve: "bn254",
      encoding: "affine-u80-v1",
      g2: coordinates,
    });
    Ok(exporter)
  }

  pub fn schema(&self) -> &Schema {
    &self.schema
  }

  pub fn witness(
    &self,
    record: &Execution<Bn254>,
    args: &[Scalar],
  ) -> Result<Witness, String> {
    let (mut public, traces) = self.populated(record, args)?;
    let private_outputs = public.split_off(self.schema.public_inputs);
    Ok(Witness {
      public: public.into_iter().map(scalar).collect(),
      main: traces
        .into_iter()
        .map(|trace| trace.values.into_iter().map(scalar).collect())
        .collect(),
      private_outputs: private_outputs.into_iter().map(scalar).collect(),
    })
  }

  /// Gnark's binary witness: three big-endian u32 counts followed by public
  /// then private canonical field words. Matrix order is fixed by the schema.
  pub fn binary_witness(
    &self,
    record: &Execution<Bn254>,
    args: &[Scalar],
  ) -> Result<Vec<u8>, String> {
    if self.schema.public_inputs > MAX_PUBLIC_INPUTS {
      return Err("too many Aiur PLONK public fields".into());
    }
    let (mut public, traces) = self.populated(record, args)?;
    let private_outputs = public.split_off(self.schema.public_inputs);
    let secret: usize = traces
      .iter()
      .map(|trace| trace.values.len())
      .sum::<usize>()
      .checked_add(private_outputs.len())
      .ok_or("PLONK witness size overflow")?;
    let total =
      public.len().checked_add(secret).ok_or("PLONK witness size overflow")?;
    let mut out = Vec::with_capacity(12 + 32 * total);
    for count in [public.len(), secret, total] {
      out.extend(
        u32::try_from(count).map_err(|error| error.to_string())?.to_be_bytes(),
      );
    }
    for value in public
      .into_iter()
      .chain(traces.into_iter().flat_map(|trace| trace.values))
      .chain(private_outputs)
    {
      put_scalar(&mut out, value);
    }
    Ok(out)
  }

  fn populated(
    &self,
    record: &Execution<Bn254>,
    args: &[Scalar],
  ) -> Result<(Vec<Scalar>, Vec<RowMajorMatrix<Scalar>>), String> {
    let public_args = self.plan.public_args(record, &self.entry, args)?;
    let claim =
      self.plan.public_claim(&self.entry, &public_args, &record.output)?;
    if claim.len()
      != self.schema.public_inputs + self.schema.private_outputs + 2
    {
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
        Ok(trace)
      })
      .collect::<Result<_, String>>()?;
    Ok((claim[2..].to_vec(), main))
  }
}
