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
    memory: &FxHashMap<&[B::Element], usize>,
    scratch: &mut Vec<B::Element>,
    buffer: &mut Vec<B::Element>,
    row: &mut [B::Element],
  ) -> Result<(), String> {
    self.fill_into(record, query, memory, scratch, buffer, |column, value| {
      row[column] = value;
    })
  }

  /// The same population graph can write either generic field words or the
  /// backend's field matrix directly, without an intermediate whole trace.
  pub(super) fn fill_into(
    &self,
    record: &Execution<B>,
    query: (&[B::Element], crate::query::QueryOutputRef<'_, B::Element>),
    memory: &FxHashMap<&[B::Element], usize>,
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
            let id = table.lookup(buffer).1.ok_or("missing recorded callee")?;
            scratch[k.start..k.start + k.width]
              .copy_from_slice(table.output(id).output);
          }
        },
        Node::Store { values, .. } => {
          buffer.clear();
          buffer.extend(values.iter().map(|v| v.get(scratch)));
          scratch[k.start] = field.from_u64(
            *memory.get(buffer.as_slice()).ok_or("missing recorded store")?
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
