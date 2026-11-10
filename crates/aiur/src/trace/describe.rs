//! A stable, serializable description of the population plans and their
//! certified placements, for generators of row writers outside this crate.
//!
//! The description is derived from the compiled [`FillPlan`]s after
//! [`TracePlan::new`] has pruned dead steps, so it is exactly the dataflow
//! graph the host writer runs. External reads are named by their semantic
//! identity rather than by process-local indices: calls by callee name, maps by
//! name and a digest of their table contents, hints by their instruction site
//! and types, and memory accesses by width.
//!
//! [`FunctionDescription::evaluate`] is an independent reference evaluator of
//! one row; [`MemberDescription::finish`] applies the placement.
//!
//! [`FillPlan`]: super::plan::FillPlan
use super::*;
use crate::{artifact::put_type, ixon::Writer};

/// Increment whenever the meaning of a described plan changes.
pub const DESCRIPTION_VERSION: u32 = 1;

/// Version of the encoding hashed by [`PopulationDescription::fingerprint`].
/// Bumping it invalidates every compiled trace bundle.
pub const DESCRIPTION_FINGERPRINT_SCHEME: u32 = 2;

/// The whole population plan of a program's function circuits.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PopulationDescription {
  pub version: u32,
  pub modulus: u64,
  /// By function index.
  pub functions: Vec<FunctionDescription>,
  /// Every map of the program, by map index.
  pub maps: Vec<MapDescription>,
  /// Function circuits in physical circuit order.
  pub circuits: Vec<CircuitDescription>,
}

/// A value read by a kernel or write: a canonical constant or a slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Operand {
  Const(u64),
  Slot(usize),
}

/// One population function. Slots `0..inputs` hold the recorded query
/// inputs and the next `outputs` slots its recorded outputs; each kernel
/// defines `start..start + width`, and the slots are otherwise unused.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionDescription {
  pub name: String,
  pub inputs: usize,
  pub outputs: usize,
  pub slots: usize,
  pub kernels: Vec<KernelDescription>,
  /// Logical column writes, applied in order after every kernel.
  pub writes: Vec<WriteDescription>,
}

/// A kernel runs only when `guard` is one. Otherwise its slots are zero.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KernelDescription {
  pub guard: Operand,
  pub start: usize,
  pub width: usize,
  pub node: NodeDescription,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum NodeDescription {
  Add {
    a: Operand,
    b: Operand,
  },
  Sub {
    a: Operand,
    b: Operand,
  },
  Mul {
    a: Operand,
    b: Operand,
  },
  /// `a` when `guard` is one, else `b`.
  Select {
    guard: Operand,
    a: Operand,
    b: Operand,
  },
  /// The inverse of a nonzero `value`; zero is an error.
  Inverse {
    value: Operand,
  },
  /// One-hot over the first test whose operands are all zero.
  Choice {
    tests: Vec<Vec<Operand>>,
  },
  /// The inverse of the first nonzero difference at its position, zero
  /// elsewhere; all-zero differences are an error.
  Failure {
    differences: Vec<Operand>,
  },
  /// The recorded output of `callee`'s query on `args`.
  Call {
    callee: String,
    args: Vec<Operand>,
  },
  /// The fixed-table output of map `map` (an index into
  /// [`PopulationDescription::maps`]) for `args`.
  Map {
    map: usize,
    args: Vec<Operand>,
  },
  /// The width-local ROM address of the interned `values`.
  Store {
    width: usize,
    values: Vec<Operand>,
  },
  /// The `width` words of the ROM cell at `address`.
  Load {
    width: usize,
    address: Operand,
  },
  /// The bound provider's answer at the hint site for `key`.
  Hint {
    site: HintSite,
    key: Vec<Operand>,
  },
}

/// A hint instruction site and its nominal types.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HintSite {
  pub function: String,
  pub instruction: usize,
  pub channel: String,
  pub r#type: Type,
  pub key_type: Type,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WriteDescription {
  pub guard: Operand,
  pub column: usize,
  pub value: Operand,
}

/// A fixed-table map. `digest` is BLAKE3 over its input and output rows.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MapDescription {
  pub name: String,
  pub inputs: usize,
  pub outputs: usize,
  pub rows: usize,
  pub digest: String,
}

/// A physical function circuit: `width` columns, the last of which is the
/// multiplicity, filled by its members' rows in member order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CircuitDescription {
  pub name: String,
  pub width: usize,
  pub members: Vec<MemberDescription>,
}

/// One function's placement in its circuit; see [`Placement`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberDescription {
  /// An index into [`PopulationDescription::functions`].
  pub function: usize,
  pub columns: Vec<usize>,
  pub selector: usize,
  pub writes: Vec<GroupWrite>,
}

impl PopulationDescription {
  /// BLAKE3 over the domain, [`DESCRIPTION_FINGERPRINT_SCHEME`] and the
  /// canonical binary encoding of every field, as lowercase hex.
  pub fn fingerprint(&self) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"aiur-population-description\0");
    hasher.update(&DESCRIPTION_FINGERPRINT_SCHEME.to_le_bytes());
    hasher.update(&self.canonical_bytes());
    hasher.finalize().to_hex().to_string()
  }

  fn canonical_bytes(&self) -> Vec<u8> {
    fn operand(w: &mut Writer, value: Operand) {
      match value {
        Operand::Const(v) => {
          w.u8(0);
          w.nat(v);
        },
        Operand::Slot(s) => {
          w.u8(1);
          w.usize(s);
        },
      }
    }
    fn operands(w: &mut Writer, values: &[Operand]) {
      w.usize(values.len());
      for &v in values {
        operand(w, v);
      }
    }
    // A tree in pre-order: 0 const, 1 var, 2 add, 3 sub, 4 mul.
    fn polynomial(w: &mut Writer, p: &Polynomial) {
      let mut stack = vec![p];
      while let Some(p) = stack.pop() {
        let (tag, children) = match p {
          Polynomial::Const(v) => {
            w.u8(0);
            w.nat(*v);
            continue;
          },
          Polynomial::Var(i) => {
            w.u8(1);
            w.usize(*i);
            continue;
          },
          Polynomial::Add(xs) => (2, xs),
          Polynomial::Sub(xs) => (3, xs),
          Polynomial::Mul(xs) => (4, xs),
        };
        w.u8(tag);
        stack.push(&children[1]);
        stack.push(&children[0]);
      }
    }
    fn node(w: &mut Writer, node: &NodeDescription) {
      use NodeDescription as N;
      match node {
        N::Add { a, b } | N::Sub { a, b } | N::Mul { a, b } => {
          w.u8(match node {
            N::Add { .. } => 0,
            N::Sub { .. } => 1,
            _ => 2,
          });
          operand(w, *a);
          operand(w, *b);
        },
        N::Select { guard, a, b } => {
          w.u8(3);
          operand(w, *guard);
          operand(w, *a);
          operand(w, *b);
        },
        N::Inverse { value } => {
          w.u8(4);
          operand(w, *value);
        },
        N::Choice { tests } => {
          w.u8(5);
          w.usize(tests.len());
          for t in tests {
            operands(w, t);
          }
        },
        N::Failure { differences } => {
          w.u8(6);
          operands(w, differences);
        },
        N::Call { callee, args } => {
          w.u8(7);
          w.str(callee);
          operands(w, args);
        },
        N::Map { map, args } => {
          w.u8(8);
          w.usize(*map);
          operands(w, args);
        },
        N::Store { width, values } => {
          w.u8(9);
          w.usize(*width);
          operands(w, values);
        },
        N::Load { width, address } => {
          w.u8(10);
          w.usize(*width);
          operand(w, *address);
        },
        N::Hint { site, key } => {
          w.u8(11);
          w.str(&site.function);
          w.usize(site.instruction);
          w.str(&site.channel);
          put_type(w, &site.r#type);
          put_type(w, &site.key_type);
          operands(w, key);
        },
      }
    }
    let mut w = Writer::new();
    w.nat(u64::from(self.version));
    w.nat(self.modulus);
    w.usize(self.functions.len());
    for function in &self.functions {
      w.str(&function.name);
      w.usize(function.inputs);
      w.usize(function.outputs);
      w.usize(function.slots);
      w.usize(function.kernels.len());
      for kernel in &function.kernels {
        operand(&mut w, kernel.guard);
        w.usize(kernel.start);
        w.usize(kernel.width);
        node(&mut w, &kernel.node);
      }
      w.usize(function.writes.len());
      for write in &function.writes {
        operand(&mut w, write.guard);
        w.usize(write.column);
        operand(&mut w, write.value);
      }
    }
    w.usize(self.maps.len());
    for map in &self.maps {
      w.str(&map.name);
      w.usize(map.inputs);
      w.usize(map.outputs);
      w.usize(map.rows);
      w.str(&map.digest);
    }
    w.usize(self.circuits.len());
    for circuit in &self.circuits {
      w.str(&circuit.name);
      w.usize(circuit.width);
      w.usize(circuit.members.len());
      for member in &circuit.members {
        w.usize(member.function);
        w.usizes(&member.columns);
        w.usize(member.selector);
        w.usize(member.writes.len());
        for write in &member.writes {
          w.usize(write.column);
          polynomial(&mut w, &write.value);
        }
      }
    }
    w.into_bytes()
  }

  pub fn function(&self, name: &str) -> Option<usize> {
    self.functions.iter().position(|f| f.name == name)
  }
}

impl<B: FieldBackend> TracePlan<'_, B> {
  /// The population description of this plan and its certified layout.
  pub fn describe(&self) -> Result<PopulationDescription, String> {
    let layout = self.layout()?;
    let program = self.program.program();
    let field = self.program.field;
    let maps = program
      .maps
      .iter()
      .enumerate()
      .map(|(index, map)| {
        let input =
          &program.tables.get(map.input).ok_or("unknown map table")?;
        let output =
          &program.tables.get(map.output).ok_or("unknown map table")?;
        let mut hasher = blake3::Hasher::new();
        for rows in [&input.rows, &output.rows] {
          hasher.update(&(rows.len() as u64).to_le_bytes());
          for row in rows {
            hasher.update(&(row.len() as u64).to_le_bytes());
            for &v in row {
              hasher.update(&v.to_le_bytes());
            }
          }
        }
        let id = program.functions.len() + index;
        Ok(MapDescription {
          name: map.name.clone(),
          inputs: self.program.inputs[id].width(),
          outputs: self.program.outputs[id].width(),
          rows: input.rows.len(),
          digest: hasher.finalize().to_hex().to_string(),
        })
      })
      .collect::<Result<Vec<_>, String>>()?;
    let functions = self
      .fills
      .iter()
      .zip(&self.artifact.functions)
      .map(|(fill, plan)| fill.describe(&self.program, plan))
      .collect();
    let mut circuits: Vec<CircuitDescription> = layout
      .circuits
      .iter()
      .map(|circuit| match *circuit {
        FunctionCircuit::Group(gi) => {
          let group = &self.artifact.groups[gi];
          CircuitDescription {
            name: group.name.clone(),
            width: group.width + 1,
            members: vec![],
          }
        },
        FunctionCircuit::Chip(ci) => {
          let chip = &self.artifact.chips[ci];
          CircuitDescription {
            name: chip.name.clone(),
            width: chip.width + 1,
            members: vec![],
          }
        },
      })
      .collect();
    for (function, &chip) in self.members.iter().enumerate() {
      let placement = &layout.placements[chip];
      circuits[placement.circuit].members.push(MemberDescription {
        function,
        columns: placement.columns.clone(),
        selector: placement.selector,
        writes: placement.writes.clone(),
      });
    }
    Ok(PopulationDescription {
      version: DESCRIPTION_VERSION,
      modulus: field.modulus(),
      functions,
      maps,
      circuits,
    })
  }
}

/// Reads of state outside a row: recorded callee queries, fixed maps, the
/// ROM and hint providers. Values are canonical words.
pub trait ExternalReads {
  fn call(
    &mut self,
    callee: &str,
    args: &[u64],
    output: &mut [u64],
  ) -> Result<(), String>;
  fn map(
    &mut self,
    map: usize,
    args: &[u64],
    output: &mut [u64],
  ) -> Result<(), String>;
  fn store(&mut self, width: usize, values: &[u64]) -> Result<u64, String>;
  fn load(
    &mut self,
    width: usize,
    address: u64,
    output: &mut [u64],
  ) -> Result<(), String>;
  fn hint(
    &mut self,
    site: &HintSite,
    key: &[u64],
    output: &mut [u64],
  ) -> Result<(), String>;
}

/// Arithmetic modulo a prime below 2^64 on canonical words.
#[derive(Clone, Copy, Debug)]
pub struct Modulus(pub u64);
// Each result is reduced below the modulus, a `u64`.
#[allow(clippy::cast_possible_truncation)]
impl Modulus {
  pub fn add(self, a: u64, b: u64) -> u64 {
    ((u128::from(a) + u128::from(b)) % u128::from(self.0)) as u64
  }
  pub fn sub(self, a: u64, b: u64) -> u64 {
    ((u128::from(a) + u128::from(self.0) - u128::from(b)) % u128::from(self.0))
      as u64
  }
  pub fn mul(self, a: u64, b: u64) -> u64 {
    ((u128::from(a) * u128::from(b)) % u128::from(self.0)) as u64
  }
  pub fn inverse(self, a: u64) -> Option<u64> {
    if a == 0 {
      return None;
    }
    let (mut result, mut base, mut exponent) = (1, a, self.0 - 2);
    while exponent != 0 {
      if exponent & 1 == 1 {
        result = self.mul(result, base);
      }
      base = self.mul(base, base);
      exponent >>= 1;
    }
    Some(result)
  }
  pub fn eval(self, p: &Polynomial, row: &[u64]) -> u64 {
    match p {
      Polynomial::Const(v) => *v % self.0,
      Polynomial::Var(v) => row[*v],
      Polynomial::Add(xs) => {
        self.add(self.eval(&xs[0], row), self.eval(&xs[1], row))
      },
      Polynomial::Sub(xs) => {
        self.sub(self.eval(&xs[0], row), self.eval(&xs[1], row))
      },
      Polynomial::Mul(xs) => {
        self.mul(self.eval(&xs[0], row), self.eval(&xs[1], row))
      },
    }
  }
}

impl FunctionDescription {
  /// Evaluates one query's row, calling `write(column, value)` for each
  /// active logical column write, as [`TracePlan::generate`] does.
  pub fn evaluate(
    &self,
    modulus: u64,
    input: &[u64],
    output: &[u64],
    reads: &mut impl ExternalReads,
    mut write: impl FnMut(usize, u64),
  ) -> Result<(), String> {
    let m = Modulus(modulus);
    if input.len() != self.inputs || output.len() != self.outputs {
      return Err("query width mismatch".into());
    }
    let mut s = vec![0u64; self.slots];
    s[..self.inputs].copy_from_slice(input);
    s[self.inputs..self.inputs + self.outputs].copy_from_slice(output);
    let get = |s: &[u64], v: Operand| match v {
      Operand::Const(c) => c,
      Operand::Slot(i) => s[i],
    };
    let mut args = vec![];
    for k in &self.kernels {
      let span = k.start..k.start + k.width;
      if get(&s, k.guard) != 1 {
        s[span].fill(0);
        continue;
      }
      args.clear();
      match &k.node {
        NodeDescription::Add { a, b } => {
          s[k.start] = m.add(get(&s, *a), get(&s, *b))
        },
        NodeDescription::Sub { a, b } => {
          s[k.start] = m.sub(get(&s, *a), get(&s, *b))
        },
        NodeDescription::Mul { a, b } => {
          s[k.start] = m.mul(get(&s, *a), get(&s, *b))
        },
        NodeDescription::Select { guard, a, b } => {
          s[k.start] =
            if get(&s, *guard) == 1 { get(&s, *a) } else { get(&s, *b) }
        },
        NodeDescription::Inverse { value } => {
          s[k.start] =
            m.inverse(get(&s, *value)).ok_or("active zero denominator")?
        },
        NodeDescription::Choice { tests } => {
          let selected = tests
            .iter()
            .position(|xs| xs.iter().all(|&v| get(&s, v) == 0))
            .ok_or("no matching trace arm")?;
          s[span].fill(0);
          s[k.start + selected] = 1;
        },
        NodeDescription::Failure { differences } => {
          let (i, x) = differences
            .iter()
            .enumerate()
            .find_map(|(i, &v)| {
              let x = get(&s, v);
              (x != 0).then_some((i, x))
            })
            .ok_or("rejected pattern actually matches")?;
          s[span].fill(0);
          s[k.start + i] = m.inverse(x).ok_or("zero failure witness")?;
        },
        NodeDescription::Call { callee, args: xs } => {
          args.extend(xs.iter().map(|&v| get(&s, v)));
          reads.call(callee, &args, &mut s[span])?;
        },
        NodeDescription::Map { map, args: xs } => {
          args.extend(xs.iter().map(|&v| get(&s, v)));
          reads.map(*map, &args, &mut s[span])?;
        },
        NodeDescription::Store { width, values } => {
          args.extend(values.iter().map(|&v| get(&s, v)));
          s[k.start] = reads.store(*width, &args)?;
        },
        NodeDescription::Load { width, address } => {
          let address = get(&s, *address);
          reads.load(*width, address, &mut s[span])?;
        },
        NodeDescription::Hint { site, key } => {
          args.extend(key.iter().map(|&v| get(&s, v)));
          reads.hint(site, &args, &mut s[span])?;
        },
      }
    }
    for w in &self.writes {
      if get(&s, w.guard) == 1 {
        write(w.column, get(&s, w.value));
      }
    }
    Ok(())
  }
}

impl MemberDescription {
  /// Completes a physical row after its column writes, as `Placement`
  /// does in the prover: selector, group writes, then the multiplicity.
  pub fn finish(&self, modulus: u64, row: &mut [u64], multiplicity: u64) {
    let m = Modulus(modulus);
    row[self.selector] = 1;
    for write in &self.writes {
      row[write.column] = m.eval(&write.value, row);
    }
    *row.last_mut().unwrap() = multiplicity;
  }
}

/// Version of the interface between compiled row writers and the device
/// record: the `AiurCircuit`, `AiurFunction`, `AiurCallee` and
/// `AiurPopulationError` layouts, the callee index hash, the launch
/// signature and the error codes of `cuda/population.cu`.
pub const COMPILED_ABI_VERSION: u32 = 3;

/// What a compiled writer reads per row: the member's recorded query row of
/// canonical words (inputs, then outputs) and its full-width multiplicity.
pub const SEED_SCHEMA: &str = "query-rows/canonical-u64/1";

/// Hint channels a compiled writer may evaluate itself: the providers that
/// `aiur::library::u32::register` and `aiur::library::u64::register` bind,
/// with their registered key and output types. Registering a bundle that
/// inlines them asserts that the record binds exactly those providers.
pub const WORD_HINT_CONTRACT: &str = "aiur-library-word-hints/1";

/// The identity a compiled bundle generated from `description` carries.
pub fn compiled_fingerprint(description: &PopulationDescription) -> String {
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"aiur-compiled-trace\0");
  hasher.update(&COMPILED_ABI_VERSION.to_le_bytes());
  for part in [SEED_SCHEMA, WORD_HINT_CONTRACT] {
    hasher.update(part.as_bytes());
    hasher.update(&[0]);
  }
  hasher.update(description.fingerprint().as_bytes());
  hasher.finalize().to_hex().to_string()
}

/// Which program a compiled bundle is for, independent of its version: the
/// names of its entry points. A bundle for the same program whose
/// [`compiled_fingerprint`] differs is stale; a bundle for another program
/// does not apply.
pub fn program_identity(program: &crate::Program) -> String {
  let mut names: Vec<&str> =
    program.entries.iter().map(|e| e.name.as_str()).collect();
  names.sort_unstable();
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"aiur-program-entries\0");
  for name in names {
    hasher.update(name.as_bytes());
    hasher.update(&[0]);
  }
  hasher.finalize().to_hex().to_string()
}

#[cfg(test)]
mod fingerprint_tests {
  use super::*;

  fn sample() -> PopulationDescription {
    let site = HintSite {
      function: "main".into(),
      instruction: 3,
      channel: "u32".into(),
      r#type: Type::Field,
      key_type: Type::Tuple { items: vec![Type::Field] },
    };
    let s = Operand::Slot;
    let c = Operand::Const;
    let nodes = vec![
      NodeDescription::Add { a: s(0), b: c(1) },
      NodeDescription::Sub { a: s(0), b: c(1) },
      NodeDescription::Mul { a: s(0), b: c(1) },
      NodeDescription::Select { guard: s(1), a: s(0), b: c(2) },
      NodeDescription::Inverse { value: s(0) },
      NodeDescription::Choice { tests: vec![vec![s(0)], vec![]] },
      NodeDescription::Failure { differences: vec![s(0), s(1)] },
      NodeDescription::Call { callee: "f".into(), args: vec![s(0)] },
      NodeDescription::Map { map: 0, args: vec![s(0)] },
      NodeDescription::Store { width: 2, values: vec![s(0), s(1)] },
      NodeDescription::Load { width: 2, address: s(2) },
      NodeDescription::Hint { site, key: vec![s(0)] },
    ];
    let kernels = nodes
      .into_iter()
      .enumerate()
      .map(|(i, node)| KernelDescription {
        guard: c(1),
        start: 2 + i,
        width: 1,
        node,
      })
      .collect();
    PopulationDescription {
      version: DESCRIPTION_VERSION,
      modulus: 0xffff_ffff_0000_0001,
      functions: vec![FunctionDescription {
        name: "main".into(),
        inputs: 1,
        outputs: 1,
        slots: 14,
        kernels,
        writes: vec![WriteDescription { guard: c(1), column: 0, value: s(2) }],
      }],
      maps: vec![MapDescription {
        name: "m".into(),
        inputs: 1,
        outputs: 1,
        rows: 4,
        digest: "00".into(),
      }],
      circuits: vec![CircuitDescription {
        name: "main".into(),
        width: 3,
        members: vec![MemberDescription {
          function: 0,
          columns: vec![0, 1],
          selector: 2,
          writes: vec![GroupWrite {
            column: 1,
            value: Polynomial::Add(Box::new([
              Polynomial::Var(0),
              Polynomial::Const(3),
            ])),
          }],
        }],
      }],
    }
  }

  #[test]
  fn fingerprint_is_deterministic_and_covers_every_field() {
    let base = sample().fingerprint();
    assert_eq!(base.len(), 64);
    assert_eq!(sample().fingerprint(), base);
    let changed = |edit: &dyn Fn(&mut PopulationDescription)| {
      let mut d = sample();
      edit(&mut d);
      d.fingerprint()
    };
    type Edit = Box<dyn Fn(&mut PopulationDescription)>;
    let edits: Vec<Edit> = vec![
      Box::new(|d| d.version += 1),
      Box::new(|d| d.functions[0].slots += 1),
      Box::new(|d| {
        d.functions[0].kernels[0].node =
          NodeDescription::Add { a: Operand::Slot(0), b: Operand::Const(2) }
      }),
      Box::new(|d| {
        d.functions[0].kernels[0].node =
          NodeDescription::Add { a: Operand::Const(0), b: Operand::Const(1) }
      }),
      Box::new(|d| d.functions[0].kernels[1].guard = Operand::Slot(1)),
      Box::new(|d| d.functions[0].kernels.swap(0, 1)),
      Box::new(|d| {
        if let NodeDescription::Hint { site, .. } =
          &mut d.functions[0].kernels[11].node
        {
          site.channel = "u64".into();
        }
      }),
      Box::new(|d| {
        if let NodeDescription::Hint { site, .. } =
          &mut d.functions[0].kernels[11].node
        {
          site.key_type = Type::Field;
        }
      }),
      Box::new(|d| d.functions[0].writes[0].column = 1),
      Box::new(|d| d.maps[0].digest = "01".into()),
      Box::new(|d| d.circuits[0].members[0].selector = 1),
      Box::new(|d| {
        d.circuits[0].members[0].writes[0].value = Polynomial::Const(3);
      }),
    ];
    let mut seen = std::collections::HashSet::from([base.clone()]);
    for edit in &edits {
      assert!(seen.insert(changed(edit.as_ref())));
    }
  }

  #[test]
  fn fingerprint_hashes_the_versioned_domain() {
    let description = sample();
    let hash = |scheme: u32| {
      let mut hasher = blake3::Hasher::new();
      hasher.update(b"aiur-population-description\0");
      hasher.update(&scheme.to_le_bytes());
      hasher.update(&description.canonical_bytes());
      hasher.finalize().to_hex().to_string()
    };
    assert_eq!(hash(DESCRIPTION_FINGERPRINT_SCHEME), description.fingerprint());
    assert_ne!(hash(1), description.fingerprint());
  }
}
