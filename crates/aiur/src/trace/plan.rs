//! Compile logical recipes into a live dataflow graph with fixed destinations.
//! Logical witness overwrites become selections; record inputs/outputs are
//! immutable sources. Pure arithmetic is shared across recipes. Runtime code
//! has no polynomial trees, degree tracking, or column allocation decisions.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Value<F> {
  Constant(F),
  Slot(usize),
}
impl<F: Copy> Value<F> {
  #[inline]
  fn get(self, scratch: &[F]) -> F {
    match self {
      Self::Constant(v) => v,
      Self::Slot(i) => scratch[i],
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Arithmetic<F> {
  Add(Value<F>, Value<F>),
  Sub(Value<F>, Value<F>),
  Mul(Value<F>, Value<F>),
  Select(Value<F>, Value<F>, Value<F>),
}
impl<F: Copy + Eq> Arithmetic<F> {
  fn sources(self) -> Vec<Value<F>> {
    match self {
      Self::Add(a, b) | Self::Sub(a, b) | Self::Mul(a, b) => vec![a, b],
      Self::Select(g, a, b) => vec![g, a, b],
    }
  }
  #[inline]
  fn eval<B: FieldBackend<Element = F>>(self, s: &[F], f: B) -> F {
    match self {
      Self::Add(a, b) => f.add(a.get(s), b.get(s)),
      Self::Sub(a, b) => f.sub(a.get(s), b.get(s)),
      Self::Mul(a, b) => f.mul(a.get(s), b.get(s)),
      Self::Select(g, a, b) => {
        if g.get(s) == f.one() {
          a.get(s)
        } else {
          b.get(s)
        }
      },
    }
  }
}

enum Node<F> {
  Arithmetic(Arithmetic<F>),
  Inverse(Value<F>),
  Choice(Vec<Vec<Value<F>>>),
  Failure(Vec<Value<F>>),
  Call { callable: usize, args: Vec<Value<F>> },
  Store { values: Vec<Value<F>> },
  Load { address: Value<F> },
  Hint { instruction: usize, key: Vec<Value<F>> },
}
impl<F: Copy + Eq> Node<F> {
  fn sources(&self) -> Vec<Value<F>> {
    match self {
      Self::Arithmetic(a) => a.sources(),
      Self::Inverse(a) => vec![*a],
      Self::Choice(xs) => xs.iter().flatten().copied().collect(),
      Self::Failure(xs)
      | Self::Call { args: xs, .. }
      | Self::Store { values: xs, .. }
      | Self::Hint { key: xs, .. } => xs.clone(),
      Self::Load { address, .. } => vec![*address],
    }
  }
}
struct Kernel<F> {
  guard: Value<F>,
  start: usize,
  width: usize,
  node: Node<F>,
}
struct Write<F> {
  guard: Value<F>,
  column: usize,
  value: Value<F>,
}

pub(super) struct FillPlan<B: FieldBackend> {
  function: usize,
  field: B,
  inputs: usize,
  output: usize,
  scratch: usize,
  kernels: Vec<Kernel<B::Element>>,
  writes: Vec<Write<B::Element>>,
}

struct Builder<B: FieldBackend> {
  logical: Vec<Value<B::Element>>,
  immutable: FxHashSet<usize>,
  shared: FxHashMap<Arithmetic<B::Element>, Value<B::Element>>,
  plan: FillPlan<B>,
  field: B,
}

impl<B: FieldBackend> Builder<B> {
  fn emit(
    &mut self,
    guard: Value<B::Element>,
    width: usize,
    node: Node<B::Element>,
  ) -> Vec<Value<B::Element>> {
    let start = self.plan.scratch;
    self.plan.scratch += width;
    self.plan.kernels.push(Kernel { guard, start, width, node });
    (start..start + width).map(Value::Slot).collect()
  }
  fn arithmetic(&mut self, op: Arithmetic<B::Element>) -> Value<B::Element> {
    use Arithmetic::*;
    use Value::Constant as C;
    let zero = Value::Constant(self.field.zero());
    let one = Value::Constant(self.field.one());
    match op {
      Add(C(a), C(b)) => return C(self.field.add(a, b)),
      Sub(C(a), C(b)) => return C(self.field.sub(a, b)),
      Mul(C(a), C(b)) => return C(self.field.mul(a, b)),
      Add(a, b) if a == zero => return b,
      Add(b, a) | Sub(b, a) if a == zero => return b,
      Mul(a, b) if a == one => return b,
      Mul(b, a) if a == one => return b,
      Sub(a, b) if a == b => return zero,
      Mul(a, b) if a == zero || b == zero => return zero,
      Select(C(g), a, b) => return if g == self.field.one() { a } else { b },
      Select(_, a, b) if a == b => return a,
      _ => (),
    }
    if let Some(v) = self.shared.get(&op) {
      return *v;
    }
    let value = self.emit(one, 1, Node::Arithmetic(op))[0];
    self.shared.insert(op, value);
    value
  }
  fn expr(&mut self, p: &Polynomial) -> Value<B::Element> {
    match p {
      Polynomial::Const(v) => Value::Constant(self.field.from_u64(*v)),
      Polynomial::Var(i) => self.logical[*i],
      Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) => {
        let a = self.expr(&xs[0]);
        let b = self.expr(&xs[1]);
        self.arithmetic(match p {
          Polynomial::Add(_) => Arithmetic::Add(a, b),
          Polynomial::Sub(_) => Arithmetic::Sub(a, b),
          _ => Arithmetic::Mul(a, b),
        })
      },
    }
  }
  fn exprs(&mut self, ps: &[Polynomial]) -> Vec<Value<B::Element>> {
    ps.iter().map(|p| self.expr(p)).collect()
  }
  fn assign(
    &mut self,
    guard: Value<B::Element>,
    dest: &[usize],
    values: Vec<Value<B::Element>>,
  ) {
    for (&d, v) in dest.iter().zip(values) {
      if !self.immutable.contains(&d) {
        self.logical[d] =
          self.arithmetic(Arithmetic::Select(guard, v, self.logical[d]));
      }
    }
  }
}

impl<B: FieldBackend> FillPlan<B> {
  pub(super) fn compile(
    plan: &FunctionPlan,
    callables: &FxHashMap<String, usize>,
    program: &CheckedProgram<B>,
  ) -> Self {
    let field = program.field;
    let zero = Value::Constant(field.zero());
    let initial = plan.inputs.len() + plan.output.len();
    let mut b = Builder {
      logical: vec![zero; plan.witnesses],
      immutable: plan.inputs.iter().chain(&plan.output).copied().collect(),
      shared: FxHashMap::default(),
      field,
      plan: Self {
        function: callables[&plan.name],
        field,
        inputs: plan.inputs.len(),
        output: plan.output.len(),
        scratch: initial,
        kernels: vec![],
        writes: vec![],
      },
    };
    for (i, &logical) in plan.inputs.iter().chain(&plan.output).enumerate() {
      b.logical[logical] = Value::Slot(i);
    }
    for step in &plan.steps {
      if step.action.dest().iter().all(|d| b.immutable.contains(d)) {
        continue;
      }
      let guard = b.expr(&step.guard);
      if guard == zero {
        continue;
      }
      let width = step.action.dest().len();
      let values = match &step.action {
        Action::Assign { values, .. } => b.exprs(values),
        Action::Inverse { value, .. } => {
          let value = b.expr(value);
          b.emit(guard, width, Node::Inverse(value))
        },
        Action::Choose { tests, .. } => {
          let tests = tests.iter().map(|ps| b.exprs(ps)).collect();
          b.emit(guard, width, Node::Choice(tests))
        },
        Action::Failure { differences, .. } => {
          let values = b.exprs(differences);
          b.emit(guard, width, Node::Failure(values))
        },
        Action::Call { name, args, .. } => {
          let args = b.exprs(args);
          b.emit(guard, width, Node::Call { callable: callables[name], args })
        },
        Action::Store { values, .. } => {
          let values = b.exprs(values);
          b.emit(guard, width, Node::Store { values })
        },
        Action::Load { address, .. } => {
          let address = b.expr(address);
          b.emit(guard, width, Node::Load { address })
        },
        Action::Hint { instruction, key, .. } => {
          let key = b.exprs(key);
          b.emit(guard, width, Node::Hint { instruction: *instruction, key })
        },
      };
      b.assign(guard, step.action.dest(), values);
    }
    for write in &plan.writes {
      let guard = b.expr(&write.guard);
      b.plan.writes.push(Write {
        guard,
        column: write.column,
        value: b.logical[write.source],
      });
    }
    // Every node refers only to earlier slots: one reverse pass suffices.
    let mut live = vec![false; b.plan.scratch];
    for w in &b.plan.writes {
      for v in [w.guard, w.value] {
        if let Value::Slot(i) = v {
          live[i] = true;
        }
      }
    }
    for k in b.plan.kernels.iter().rev() {
      if live[k.start..k.start + k.width].iter().any(|v| *v) {
        for v in k.node.sources().into_iter().chain([k.guard]) {
          if let Value::Slot(i) = v {
            live[i] = true;
          }
        }
      }
    }
    b.plan
      .kernels
      .retain(|k| live[k.start..k.start + k.width].iter().any(|v| *v));
    b.plan
  }

  pub(super) fn fill(
    &self,
    record: &Execution<B>,
    query: (&[B::Element], crate::query::QueryOutputRef<'_, B::Element>),
    scratch: &mut Vec<B::Element>,
    buffer: &mut Vec<B::Element>,
    row: &mut [B::Element],
  ) -> Result<(), String> {
    self.fill_into(record, query, scratch, buffer, |column, value| {
      row[column] = value;
    })
  }

  /// The same population graph can write either generic field words or the
  /// backend's field matrix directly, without an intermediate whole trace.
  pub(super) fn fill_into(
    &self,
    record: &Execution<B>,
    query: (&[B::Element], crate::query::QueryOutputRef<'_, B::Element>),
    scratch: &mut Vec<B::Element>,
    buffer: &mut Vec<B::Element>,
    mut write: impl FnMut(usize, B::Element),
  ) -> Result<(), String> {
    let field = self.field;
    scratch.resize(self.scratch, self.field.zero());
    // Every retained slot is an input/output or has one earlier producer.
    // Producers overwrite their spans; only inactive/partial producers
    // need zeroing. Unused scratch slots are never read by the live graph.
    let (input, output) = query;
    scratch[..self.inputs].copy_from_slice(input);
    scratch[self.inputs..self.inputs + self.output]
      .copy_from_slice(output.output);
    for k in &self.kernels {
      if k.guard.get(scratch) != field.one() {
        scratch[k.start..k.start + k.width].fill(field.zero());
        continue;
      }
      match &k.node {
        Node::Arithmetic(op) => scratch[k.start] = op.eval(scratch, field),
        Node::Inverse(v) => {
          scratch[k.start] =
            field.inverse(v.get(scratch)).ok_or("active zero denominator")?
        },
        Node::Choice(tests) => {
          scratch[k.start..k.start + k.width].fill(field.zero());
          let selected = tests
            .iter()
            .position(|xs| xs.iter().all(|v| v.get(scratch) == field.zero()))
            .ok_or("no matching trace arm")?;
          scratch[k.start + selected] = field.one();
        },
        Node::Failure(xs) => {
          scratch[k.start..k.start + k.width].fill(field.zero());
          let (i, v) = xs
            .iter()
            .enumerate()
            .find_map(|(i, v)| {
              let x = v.get(scratch);
              (x != field.zero()).then_some((i, x))
            })
            .ok_or("rejected pattern actually matches")?;
          scratch[k.start + i] =
            field.inverse(v).ok_or("zero failure witness")?;
        },
        Node::Call { callable, args } => {
          buffer.clear();
          buffer.extend(args.iter().map(|v| v.get(scratch)));
          let table = &record.queries.tables[*callable];
          if let Some(map) = &table.static_map {
            map
              .binding
              .evaluate(buffer, &mut scratch[k.start..k.start + k.width])?;
          } else {
            if let Some(id) = table.lookup(buffer).1 {
              scratch[k.start..k.start + k.width]
                .copy_from_slice(table.output(id).output);
            } else {
              return Err("missing recorded callee".into());
            }
          }
        },
        Node::Store { values, .. } => {
          buffer.clear();
          buffer.extend(values.iter().map(|v| v.get(scratch)));
          scratch[k.start] = field.from_u64(
            record.memory.address_of(buffer).ok_or("missing recorded store")?
              as u64,
          );
        },
        Node::Load { address, .. } => {
          let address = usize::try_from(field.to_u64(address.get(scratch)))
            .map_err(|_| "ROM address overflow")?;
          let cell = &record
            .memory
            .get_by_width(k.width, address)
            .ok_or("missing recorded load")?
            .cell;
          if cell.value.len() != k.width {
            return Err("ROM load shape mismatch".into());
          }
          scratch[k.start..k.start + k.width].copy_from_slice(cell.value);
        },
        Node::Hint { instruction, key } => {
          buffer.clear();
          buffer.extend(key.iter().map(|v| v.get(scratch)));
          record.hints.sites[self.function][*instruction]
            .as_ref()
            .ok_or("missing hint site")?
            .evaluate(
              buffer,
              &mut scratch[k.start..k.start + k.width],
              field,
            )?;
        },
      }
    }
    for w in &self.writes {
      if w.guard.get(scratch) == field.one() {
        write(w.column, w.value.get(scratch));
      }
    }
    Ok(())
  }
}

impl<B: FieldBackend> FillPlan<B> {
  /// This plan in the stable description schema; `plan` is the function's
  /// artifact plan, which names its hint sites.
  pub(super) fn describe(
    &self,
    program: &CheckedProgram<B>,
    plan: &FunctionPlan,
  ) -> super::describe::FunctionDescription {
    use super::describe::{
      FunctionDescription, HintSite, KernelDescription, NodeDescription as N,
      Operand, WriteDescription,
    };
    let field = self.field;
    let op = |v: &Value<B::Element>| match v {
      Value::Constant(c) => Operand::Const(field.to_u64(*c)),
      Value::Slot(i) => Operand::Slot(*i),
    };
    let ops = |vs: &[Value<B::Element>]| vs.iter().map(op).collect::<Vec<_>>();
    let functions = program.program.functions.len();
    let kernels = self
      .kernels
      .iter()
      .map(|k| {
        let node = match &k.node {
          Node::Arithmetic(Arithmetic::Add(a, b)) => {
            N::Add { a: op(a), b: op(b) }
          },
          Node::Arithmetic(Arithmetic::Sub(a, b)) => {
            N::Sub { a: op(a), b: op(b) }
          },
          Node::Arithmetic(Arithmetic::Mul(a, b)) => {
            N::Mul { a: op(a), b: op(b) }
          },
          Node::Arithmetic(Arithmetic::Select(g, a, b)) => {
            N::Select { guard: op(g), a: op(a), b: op(b) }
          },
          Node::Inverse(v) => N::Inverse { value: op(v) },
          Node::Choice(tests) => {
            N::Choice { tests: tests.iter().map(|t| ops(t)).collect() }
          },
          Node::Failure(xs) => N::Failure { differences: ops(xs) },
          Node::Call { callable, args } if *callable >= functions => {
            N::Map { map: callable - functions, args: ops(args) }
          },
          Node::Call { callable, args } => N::Call {
            callee: program.program.functions[*callable].name.clone(),
            args: ops(args),
          },
          Node::Store { values } => {
            N::Store { width: values.len(), values: ops(values) }
          },
          Node::Load { address } => {
            N::Load { width: k.width, address: op(address) }
          },
          Node::Hint { instruction, key } => {
            let (channel, r#type, key_type) = plan
              .steps
              .iter()
              .find_map(|step| match &step.action {
                Action::Hint {
                  instruction: i,
                  channel,
                  r#type,
                  key_type,
                  ..
                } if i == instruction => {
                  Some((channel.clone(), r#type.clone(), key_type.clone()))
                },
                _ => None,
              })
              .expect("a hint kernel comes from a hint step");
            N::Hint {
              site: HintSite {
                function: plan.name.clone(),
                instruction: *instruction,
                channel,
                r#type,
                key_type,
              },
              key: ops(key),
            }
          },
        };
        KernelDescription {
          guard: op(&k.guard),
          start: k.start,
          width: k.width,
          node,
        }
      })
      .collect();
    FunctionDescription {
      name: plan.name.clone(),
      inputs: self.inputs,
      outputs: self.output,
      slots: self.scratch,
      kernels,
      writes: self
        .writes
        .iter()
        .map(|w| WriteDescription {
          guard: op(&w.guard),
          column: w.column,
          value: op(&w.value),
        })
        .collect(),
    }
  }
}

/// Device encoding of population plans for `stark::gpu`, whose CUDA
/// interpreter (`cuda/population.cu`) mirrors [`FillPlan::fill_into`].
#[cfg(feature = "cuda")]
pub(super) mod device {
  use super::*;

  pub const OP_ADD: u32 = 0;
  pub const OP_SUB: u32 = 1;
  pub const OP_MUL: u32 = 2;
  pub const OP_SELECT: u32 = 3;
  pub const OP_INVERSE: u32 = 4;
  pub const OP_CHOICE: u32 = 5;
  pub const OP_FAILURE: u32 = 6;
  pub const OP_MAP: u32 = 7;
  pub const OP_CALL: u32 = 8;
  pub const OP_HINT: u32 = 9;
  const CONSTANT: u32 = 0x8000_0000;

  /// Canonical field constants shared by every encoded plan of a program.
  #[derive(Default)]
  pub struct Constants {
    pub values: Vec<u64>,
    index: FxHashMap<u64, u32>,
  }
  impl Constants {
    pub fn word(&mut self, value: u64) -> Option<u32> {
      if let Some(&i) = self.index.get(&value) {
        return Some(i | CONSTANT);
      }
      let i =
        u32::try_from(self.values.len()).ok().filter(|i| i & CONSTANT == 0)?;
      self.values.push(value);
      self.index.insert(value, i);
      Some(i | CONSTANT)
    }
  }

  /// How a callable or hint site runs on the device.
  #[derive(Clone, Copy)]
  pub enum Target {
    Map(u32),
    Call(u32),
  }

  pub struct Encoded {
    pub code: Vec<u32>,
    pub scratch: u32,
    pub inputs: u32,
    pub outputs: u32,
  }

  impl<B: FieldBackend> FillPlan<B> {
    /// The plan's kernels and column writes, writing physical `column`s, or
    /// `None` when a kernel needs host-only state: memory, or a callable or
    /// hint site without a device implementation.
    pub fn encode(
      &self,
      call: &mut impl FnMut(usize) -> Option<Target>,
      hint: &mut impl FnMut(usize) -> Option<u32>,
      column: &impl Fn(usize) -> usize,
      constants: &mut Constants,
    ) -> Option<Encoded> {
      let field = self.field;
      let mut word = |v: &Value<B::Element>| -> Option<u32> {
        match v {
          Value::Constant(c) => constants.word(field.to_u64(*c)),
          Value::Slot(i) => {
            u32::try_from(*i).ok().filter(|i| i & CONSTANT == 0)
          },
        }
      };
      let mut code = vec![u32::try_from(self.kernels.len()).ok()?];
      for k in &self.kernels {
        let mut body = vec![];
        let op = match &k.node {
          Node::Arithmetic(a) => match a {
            Arithmetic::Add(x, y)
            | Arithmetic::Sub(x, y)
            | Arithmetic::Mul(x, y) => {
              body.extend([word(x)?, word(y)?]);
              match a {
                Arithmetic::Add(..) => OP_ADD,
                Arithmetic::Sub(..) => OP_SUB,
                _ => OP_MUL,
              }
            },
            Arithmetic::Select(g, x, y) => {
              body.extend([word(g)?, word(x)?, word(y)?]);
              OP_SELECT
            },
          },
          Node::Inverse(x) => {
            body.push(word(x)?);
            OP_INVERSE
          },
          Node::Choice(tests) => {
            body.push(u32::try_from(tests.len()).ok()?);
            for test in tests {
              body.push(u32::try_from(test.len()).ok()?);
              for v in test {
                body.push(word(v)?);
              }
            }
            OP_CHOICE
          },
          Node::Failure(xs) => {
            body.push(u32::try_from(xs.len()).ok()?);
            for v in xs {
              body.push(word(v)?);
            }
            OP_FAILURE
          },
          Node::Call { callable, args } => {
            let (op, target) = match call(*callable)? {
              Target::Map(kind) => (OP_MAP, kind),
              Target::Call(slot) => (OP_CALL, slot),
            };
            body.extend([target, u32::try_from(args.len()).ok()?]);
            for v in args {
              body.push(word(v)?);
            }
            op
          },
          Node::Hint { instruction, key } => {
            body.extend([hint(*instruction)?, u32::try_from(key.len()).ok()?]);
            for v in key {
              body.push(word(v)?);
            }
            OP_HINT
          },
          Node::Store { .. } | Node::Load { .. } => return None,
        };
        code.extend([
          op,
          word(&k.guard)?,
          u32::try_from(k.start).ok()?,
          u32::try_from(k.width).ok()?,
          u32::try_from(body.len()).ok()?,
        ]);
        code.extend(body);
      }
      code.push(u32::try_from(self.writes.len()).ok()?);
      for w in &self.writes {
        code.extend([
          word(&w.guard)?,
          u32::try_from(column(w.column)).ok()?,
          word(&w.value)?,
        ]);
      }
      Some(Encoded {
        code,
        scratch: u32::try_from(self.scratch).ok()?,
        inputs: u32::try_from(self.inputs).ok()?,
        outputs: u32::try_from(self.output).ok()?,
      })
    }
  }
}
