//! Execution-only interchange format and its one-time validation/linking pass.
use crate::{
  field::{FieldBackend, NativeField, PrimeField, PrimeField64},
  value::IoType,
};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

mod dead_code;

pub const VERSION: u32 = 2;

fn default_runtime_check() -> bool {
  true
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Type {
  Field,
  Tuple { items: Vec<Type> },
  Ptr { target: Box<Type> },
  Enum { name: String },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Constructor {
  pub name: String,
  pub fields: Vec<Type>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Enum {
  pub name: String,
  pub constructors: Vec<Constructor>,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Binary {
  Add,
  Sub,
  Mul,
  Div,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum Instruction<F = u64> {
  Literal {
    dest: usize,
    value: F,
  },
  Copy {
    dest: Vec<usize>,
    source: Vec<usize>,
  },
  Neg {
    dest: usize,
    source: usize,
  },
  Binary {
    dest: usize,
    operator: Binary,
    left: usize,
    right: usize,
  },
  Guard {
    tests: Vec<(usize, F)>,
    message: String,
  },
  Branch {
    tests: Vec<(usize, F)>,
    otherwise: usize,
  },
  Jump {
    target: usize,
  },
  Call {
    function: usize,
    args: Vec<usize>,
    dest: Vec<usize>,
  },
  Store {
    r#type: Type,
    value: Vec<usize>,
    dest: usize,
  },
  Load {
    r#type: Type,
    pointer: usize,
    dest: Vec<usize>,
  },
  Hint {
    #[serde(default)]
    channel: String,
    r#type: Type,
    key_type: Type,
    key: Vec<usize>,
    dest: Vec<usize>,
  },
  AssertEq {
    left: Vec<usize>,
    right: Vec<usize>,
    message: Option<String>,
    #[serde(default = "default_runtime_check")]
    runtime_check: bool,
  },
  Ret {
    value: Vec<usize>,
  },
  Fail {
    message: String,
  },
}

impl Instruction {
  fn map_constants<F>(self, f: impl Fn(u64) -> F) -> Instruction<F> {
    match self {
      Self::Literal { dest, value } => {
        Instruction::Literal { dest, value: f(value) }
      },
      Self::Copy { dest, source } => Instruction::Copy { dest, source },
      Self::Neg { dest, source } => Instruction::Neg { dest, source },
      Self::Binary { dest, operator, left, right } => {
        Instruction::Binary { dest, operator, left, right }
      },
      Self::Guard { tests, message } => Instruction::Guard {
        tests: tests.into_iter().map(|(r, v)| (r, f(v))).collect(),
        message,
      },
      Self::Branch { tests, otherwise } => Instruction::Branch {
        tests: tests.into_iter().map(|(r, v)| (r, f(v))).collect(),
        otherwise,
      },
      Self::Jump { target } => Instruction::Jump { target },
      Self::Call { function, args, dest } => {
        Instruction::Call { function, args, dest }
      },
      Self::Store { r#type, value, dest } => {
        Instruction::Store { r#type, value, dest }
      },
      Self::Load { r#type, pointer, dest } => {
        Instruction::Load { r#type, pointer, dest }
      },
      Self::Hint { channel, r#type, key_type, key, dest } => {
        Instruction::Hint { channel, r#type, key_type, key, dest }
      },
      Self::AssertEq { left, right, message, runtime_check } => {
        Instruction::AssertEq { left, right, message, runtime_check }
      },
      Self::Ret { value } => Instruction::Ret { value },
      Self::Fail { message } => Instruction::Fail { message },
    }
  }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Function<F = u64> {
  pub name: String,
  pub params: Vec<Type>,
  pub result: Type,
  pub registers: usize,
  pub code: Vec<Instruction<F>>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Table {
  pub name: String,
  pub r#type: Type,
  pub rows: Vec<Vec<u64>>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Map {
  pub name: String,
  pub params: Vec<Type>,
  pub result: Type,
  pub input: usize,
  pub output: usize,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Entry {
  pub name: String,
  pub function: usize,
  /// Only entrypoints retain source IO descriptions.
  pub inputs: Vec<IoType>,
  /// None means the result contains a pointer or opaque type.
  pub output: Option<IoType>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Program {
  pub version: u32,
  pub modulus: u64,
  pub functions: Vec<Function>,
  pub enums: Vec<Enum>,
  pub tables: Vec<Table>,
  pub maps: Vec<Map>,
  pub entries: Vec<Entry>,
}

#[derive(Clone, Debug)]
pub(crate) enum Layout {
  Field,
  Pointer,
  Tuple { items: Vec<Layout>, width: usize, shape_checks: bool },
  Enum { constructors: Vec<Layout>, payload: usize, shape_checks: bool },
}
impl Layout {
  pub(crate) fn width(&self) -> usize {
    match self {
      Self::Field | Self::Pointer => 1,
      Self::Tuple { width, .. } => *width,
      Self::Enum { constructors, payload, .. } => {
        payload + usize::from(constructors.len() > 1)
      },
    }
  }
  pub(crate) fn pointer_free(&self) -> bool {
    match self {
      Self::Field => true,
      Self::Pointer => false,
      Self::Tuple { items, .. } => items.iter().all(Self::pointer_free),
      Self::Enum { constructors, .. } => {
        constructors.iter().all(Self::pointer_free)
      },
    }
  }
  pub(crate) fn has_shape_checks(&self) -> bool {
    match self {
      Self::Field | Self::Pointer => false,
      Self::Tuple { shape_checks, .. } => *shape_checks,
      Self::Enum { shape_checks, .. } => *shape_checks,
    }
  }
  pub(crate) fn validate<B: FieldBackend>(
    &self,
    words: &[B::Element],
    field: B,
  ) -> Result<(), String> {
    if words.len() != self.width() || words.iter().any(|v| !field.valid(*v)) {
      return Err("incorrect value width or noncanonical field element".into());
    }
    self.validate_shape(words, field)
  }

  // Width and canonicality were checked once over the whole value. Recursion
  // only checks constructor tags and padding; it must not rescan every word.
  fn validate_shape<B: FieldBackend>(
    &self,
    words: &[B::Element],
    field: B,
  ) -> Result<(), String> {
    match self {
      Self::Field | Self::Pointer => Ok(()),
      Self::Tuple { shape_checks: false, .. }
      | Self::Enum { shape_checks: false, .. } => Ok(()),
      Self::Tuple { items, .. } => {
        let mut offset = 0;
        for item in items {
          item.validate_shape(&words[offset..offset + item.width()], field)?;
          offset += item.width();
        }
        Ok(())
      },
      Self::Enum { constructors, .. } => {
        let (tag, payload) = if constructors.len() > 1 {
          (
            usize::try_from(field.to_u64(words[0]))
              .map_err(|_| "enum tag too large")?,
            &words[1..],
          )
        } else {
          (0, words)
        };
        let ctor = constructors.get(tag).ok_or("invalid enum tag")?;
        ctor.validate_shape(&payload[..ctor.width()], field)?;
        if payload[ctor.width()..].iter().any(|v| *v != field.zero()) {
          return Err("nonzero enum padding".into());
        }
        Ok(())
      },
    }
  }

  /// Register values are valid field elements by construction: checked wire
  /// values, native field arithmetic and bounded ROM addresses preserve this
  /// invariant. Native elements need not have a canonical in-memory encoding.
  /// The bytecode checker establishes operand widths.
  /// Stores/returns still need dynamic constructor and zero-padding checks.
  #[inline]
  pub(crate) fn validate_registers<B: FieldBackend>(
    &self,
    words: &[B::Element],
    field: B,
  ) -> Result<(), String> {
    debug_assert_eq!(words.len(), self.width());
    debug_assert!(words.iter().all(|v| field.valid(*v)));
    self.validate_shape(words, field)
  }
}

impl Type {
  pub(crate) fn layout(
    &self,
    enums: &[Enum],
    path: &mut Vec<String>,
  ) -> Result<Layout, String> {
    match self {
      Self::Field => Ok(Layout::Field),
      Self::Ptr { .. } => Ok(Layout::Pointer),
      Self::Tuple { items } => {
        let items = items
          .iter()
          .map(|t| t.layout(enums, path))
          .collect::<Result<Vec<_>, _>>()?;
        let width = items.iter().map(Layout::width).sum();
        let shape_checks = items.iter().any(Layout::has_shape_checks);
        Ok(Layout::Tuple { items, width, shape_checks })
      },
      Self::Enum { name } => {
        if path.contains(name) {
          return Err(format!("recursive inline layout {name}"));
        }
        let decl = enums
          .iter()
          .find(|e| e.name == *name)
          .ok_or_else(|| format!("unknown enum {name}"))?;
        path.push(name.clone());
        let constructors = decl
          .constructors
          .iter()
          .map(|c| Type::Tuple { items: c.fields.clone() }.layout(enums, path))
          .collect::<Result<Vec<_>, _>>()?;
        path.pop();
        let payload = constructors.iter().map(Layout::width).max().unwrap_or(0);
        // A one-constructor wrapper has neither a tag nor padding.
        // Opaque aliases use this representation; only their payload
        // can require shape checks. Keep checks for empty enums and
        // for multi-constructor enums nested inside a wrapper.
        let shape_checks =
          constructors.len() != 1 || constructors[0].has_shape_checks();
        Ok(Layout::Enum { constructors, payload, shape_checks })
      },
    }
  }
}

#[cfg(test)]
mod layout_tests {
  use super::*;

  #[test]
  fn tagless_wrappers_preserve_nested_validation() {
    let named = |name: &str| Type::Enum { name: name.into() };
    let wrapped = |name: &str, inner: Type| Enum {
      name: name.into(),
      constructors: vec![Constructor {
        name: "Wrap".into(),
        fields: vec![inner],
      }],
    };
    let enums = vec![
      Enum {
        name: "Choice".into(),
        constructors: vec![
          Constructor { name: "None".into(), fields: vec![] },
          Constructor { name: "Some".into(), fields: vec![Type::Field] },
        ],
      },
      wrapped("Outer", named("Choice")),
      wrapped("Twice", named("Outer")),
      wrapped("Scalar", Type::Field),
      Enum { name: "Empty".into(), constructors: vec![] },
      wrapped("Impossible", named("Empty")),
    ];
    let field = PrimeField::new(97).unwrap();
    for name in ["Choice", "Outer", "Twice"] {
      let layout = named(name).layout(&enums, &mut vec![]).unwrap();
      assert!(layout.validate(&[0, 0], field).is_ok());
      assert!(layout.validate(&[1, 96], field).is_ok());
      for bad in [[2, 0], [0, 1], [1, 97]] {
        assert!(layout.validate(&bad, field).is_err(), "{name}: {bad:?}");
      }
    }
    let scalar = named("Scalar").layout(&enums, &mut vec![]).unwrap();
    assert!(scalar.validate(&[96], field).is_ok());
    assert!(scalar.validate(&[97], field).is_err());
    assert!(scalar.validate(&[], field).is_err());
    for name in ["Empty", "Impossible"] {
      assert!(
        named(name)
          .layout(&enums, &mut vec![])
          .unwrap()
          .validate(&[], field)
          .is_err()
      );
    }
  }
}

/// Validated bytecode plus prebuilt indexes shared by all maps using a table.
#[derive(Debug)]
pub struct CheckedProgram<B: FieldBackend = PrimeField> {
  pub(crate) program: std::sync::Arc<Program>,
  pub(crate) field: B,
  pub(crate) inputs: Vec<Layout>,
  pub(crate) outputs: Vec<Layout>,
  pub(crate) memory_layouts: HashMap<Type, Layout>,
  pub(crate) memory_types: Vec<(Type, Layout)>,
  pub(crate) map_indexes:
    Vec<Option<std::sync::Arc<crate::table::TableIndex<B>>>>,
  pub(crate) tables: std::sync::Arc<Vec<Vec<Vec<B::Element>>>>,
  pub(crate) division_inverses: Vec<Vec<Option<B::Element>>>,
  pub(crate) steps: Vec<Vec<Step>>,
  pub(crate) returns: Vec<Vec<Option<ReturnPlan>>>,
  pub(crate) execution_functions: Vec<Function<B::Element>>,
  pub(crate) initial_registers: Vec<Vec<(usize, B::Element)>>,
}

// Only globally immutable registers may be aliased. Inputs count as writes;
// overwritten parameters, branch joins and simultaneous swaps stay explicit.
// PCs and operation counts are retained in the linked interpreter bytecode.
fn link_registers(
  function: &Function,
  input: usize,
  field: PrimeField,
) -> (Function, Vec<(usize, u64)>) {
  let mut writes = vec![0usize; function.registers];
  writes[..input].fill(1);
  for op in &function.code {
    use Instruction::*;
    let dest: &[usize] = match op {
      Literal { dest, .. }
      | Neg { dest, .. }
      | Binary { dest, .. }
      | Store { dest, .. } => std::slice::from_ref(dest),
      Copy { dest, .. }
      | Call { dest, .. }
      | Load { dest, .. }
      | Hint { dest, .. } => dest,
      _ => &[],
    };
    for &reg in dest {
      if let Some(count) = writes.get_mut(reg) {
        *count = count.saturating_add(1);
      }
    }
  }
  let mut aliases: Vec<_> = (0..function.registers).collect();
  for op in &function.code {
    if let Instruction::Copy { dest, source } = op {
      for (&dest, &source) in dest.iter().zip(source) {
        if writes.get(dest) == Some(&1)
          && writes.get(source) == Some(&1)
          && dest >= input
        {
          aliases[dest] = aliases[source];
        }
      }
    }
  }
  let initial: Vec<_> = function
    .code
    .iter()
    .filter_map(|op| match op {
      Instruction::Literal { dest, value }
        if writes.get(*dest) == Some(&1)
          && *dest >= input
          && field.contains(*value) =>
      {
        Some((*dest, *value))
      },
      _ => None,
    })
    .collect();
  let mut linked = function.clone();
  let read = |reg: &mut usize| {
    *reg = aliases.get(*reg).copied().unwrap_or(*reg);
  };
  for op in &mut linked.code {
    use Instruction::*;
    match op {
      Copy { dest, source } => {
        dest.iter_mut().for_each(read);
        source.iter_mut().for_each(read);
      },
      Neg { source, .. } => read(source),
      Binary { left, right, .. } => {
        read(left);
        read(right);
      },
      Guard { tests, .. } | Branch { tests, .. } => {
        tests.iter_mut().for_each(|(reg, _)| read(reg))
      },
      Call { args, .. } => args.iter_mut().for_each(read),
      Store { value, .. } | Ret { value } => value.iter_mut().for_each(read),
      Load { pointer, .. } => read(pointer),
      Hint { key, .. } => key.iter_mut().for_each(read),
      AssertEq { left, right, .. } => {
        left.iter_mut().for_each(read);
        right.iter_mut().for_each(read);
      },
      _ => {},
    }
  }
  (linked, initial)
}

#[derive(Clone, Debug)]
pub(crate) struct ReturnPlan {
  pub(crate) values: Vec<usize>,
  pub(crate) pc: usize,
  pub(crate) instructions: u64,
}

// A copy/jump-only suffix has no observable work except its returned values.
// Compose simultaneous copies backwards, retaining the original return PC and
// logical instruction count. The serialized bytecode and hint PCs stay intact.
fn return_plans(function: &Function) -> Vec<Option<ReturnPlan>> {
  let mut plans: Vec<Option<ReturnPlan>> = vec![None; function.code.len()];
  for (pc, op) in function.code.iter().enumerate().rev() {
    let next = match op {
      Instruction::Ret { value } => {
        plans[pc] =
          Some(ReturnPlan { values: value.clone(), pc, instructions: 1 });
        continue;
      },
      Instruction::Copy { .. } => pc + 1,
      Instruction::Jump { target } => *target,
      Instruction::Guard { tests, .. } | Instruction::Branch { tests, .. }
        if tests.is_empty() =>
      {
        pc + 1
      },
      _ => continue,
    };
    if let Some(Some(plan)) = plans.get(next) {
      let mut plan = plan.clone();
      if let Instruction::Copy { dest, source } = op {
        // Unreachable instructions need not have a valid interface.
        if dest.len() != source.len() {
          continue;
        }
        for value in &mut plan.values {
          if let Some(i) = dest.iter().rposition(|d| d == value) {
            *value = source[i];
          }
        }
      }
      plan.instructions += 1;
      plans[pc] = Some(plan);
    }
  }
  plans
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct Step {
  pub(crate) pc: usize,
  pub(crate) skipped: u64,
  pub(crate) memory_type: usize,
}

fn execution_steps(
  function: &Function,
  memory_ids: &HashMap<Type, usize>,
  initial: &[(usize, u64)],
) -> Vec<Step> {
  let mut steps: Vec<_> = (0..function.code.len())
    .map(|pc| Step {
      pc,
      skipped: 0,
      memory_type: match &function.code[pc] {
        Instruction::Store { r#type, .. }
        | Instruction::Load { r#type, .. } => {
          memory_ids.get(r#type).copied().unwrap_or(usize::MAX)
        },
        _ => usize::MAX,
      },
    })
    .collect();
  for (pc, op) in function.code.iter().enumerate().rev() {
    let next = match op {
      Instruction::Literal { dest, value }
        if initial.contains(&(*dest, *value)) =>
      {
        Some(pc + 1)
      },
      Instruction::Guard { tests, .. } | Instruction::Branch { tests, .. }
        if tests.is_empty() =>
      {
        Some(pc + 1)
      },
      Instruction::Copy { dest, source } if dest == source => Some(pc + 1),
      Instruction::AssertEq { left, right, .. } if left == right => {
        Some(pc + 1)
      },
      Instruction::Jump { target } => Some(*target),
      _ => None,
    };
    if let Some(next) = next.filter(|&next| next > pc && next < steps.len()) {
      steps[pc] = Step {
        pc: steps[next].pc,
        skipped: steps[next].skipped + 1,
        memory_type: steps[next].memory_type,
      };
    }
  }
  steps
}
impl<B: FieldBackend> CheckedProgram<B> {
  pub fn program(&self) -> &Program {
    &self.program
  }
  pub fn field(&self) -> B {
    self.field
  }
  pub fn entry(&self, name: &str) -> Result<&Entry, String> {
    self
      .program
      .entries
      .iter()
      .find(|e| e.name == name)
      .ok_or_else(|| format!("unselected entrypoint {name}"))
  }
  pub fn callable_name(&self, id: usize) -> Option<&str> {
    if let Some(f) = self.program.functions.get(id) {
      Some(&f.name)
    } else {
      self
        .program
        .maps
        .get(id.checked_sub(self.program.functions.len())?)
        .map(|m| m.name.as_str())
    }
  }
}

fn unique<'a>(names: impl Iterator<Item = &'a str>) -> Result<(), String> {
  let mut seen = HashSet::new();
  for name in names {
    if !seen.insert(name) {
      return Err(format!("duplicate name {name}"));
    }
  }
  Ok(())
}
impl Program {
  pub fn check(self) -> Result<CheckedProgram, String> {
    let field = PrimeField::new(self.modulus)?;
    self.check_with(field)
  }

  /// Select the native field once. All prepared values and host callbacks
  /// then use F directly; interchange integers are checked before conversion.
  pub fn check_field<F: PrimeField64>(
    self,
  ) -> Result<CheckedProgram<NativeField<F>>, String> {
    self.check_with(NativeField::<F>::new())
  }

  pub fn check_with<B: FieldBackend>(
    self,
    backend: B,
  ) -> Result<CheckedProgram<B>, String> {
    if self.modulus != backend.modulus() {
      return Err("execution package / field mismatch".into());
    }
    // Version 1 has only the default channel. New exporters use version 2 so
    // an old runtime cannot silently ignore named-channel metadata.
    if self.version != 1 && self.version != VERSION {
      return Err(format!(
        "unsupported execution bytecode version {}",
        self.version
      ));
    }
    let field = PrimeField::new(self.modulus)?;
    unique(
      self
        .functions
        .iter()
        .map(|f| f.name.as_str())
        .chain(self.maps.iter().map(|m| m.name.as_str())),
    )?;
    unique(self.enums.iter().map(|e| e.name.as_str()))?;
    unique(self.tables.iter().map(|t| t.name.as_str()))?;
    unique(self.entries.iter().map(|e| e.name.as_str()))?;
    for decl in &self.enums {
      unique(decl.constructors.iter().map(|c| c.name.as_str()))?;
      if decl.constructors.len() as u128 > u128::from(field.modulus()) {
        return Err("enum tags do not fit in the field".into());
      }
      Type::Enum { name: decl.name.clone() }
        .layout(&self.enums, &mut vec![])?;
    }
    let signatures = self
      .functions
      .iter()
      .map(|f| (&f.params, &f.result))
      .chain(self.maps.iter().map(|m| (&m.params, &m.result)));
    let mut inputs = vec![];
    let mut outputs = vec![];
    for (params, result) in signatures {
      inputs.push(
        Type::Tuple { items: params.clone() }
          .layout(&self.enums, &mut vec![])?,
      );
      outputs.push(result.layout(&self.enums, &mut vec![])?);
    }
    for entry in &self.entries {
      let input =
        inputs.get(entry.function).ok_or("invalid entry function ID")?;
      if !input.pointer_free() {
        return Err("entry arguments contain pointers".into());
      }
      let input_width = entry
        .inputs
        .iter()
        .map(IoType::checked_width)
        .collect::<Result<Vec<_>, _>>()?
        .iter()
        .sum::<usize>();
      if input_width != input.width() {
        return Err("entry input description width mismatch".into());
      }
      if let Some(output) = &entry.output
        && (output.checked_width()? != outputs[entry.function].width()
          || !outputs[entry.function].pointer_free())
      {
        return Err("entry output description mismatch".into());
      }
    }
    for table in &self.tables {
      let layout = table.r#type.layout(&self.enums, &mut vec![])?;
      if !layout.pointer_free() {
        return Err("table contains pointers".into());
      }
      for row in &table.rows {
        layout.validate(row, field)?;
      }
    }
    let tables = std::sync::Arc::new(
      self
        .tables
        .iter()
        .map(|table| {
          table
            .rows
            .iter()
            .map(|row| backend.decode(row))
            .collect::<Result<Vec<_>, _>>()
        })
        .collect::<Result<Vec<_>, _>>()?,
    );
    let mut map_indexes = vec![None; self.tables.len()];
    for map in &self.maps {
      let input = self.tables.get(map.input).ok_or("invalid input table ID")?;
      let output =
        self.tables.get(map.output).ok_or("invalid output table ID")?;
      if input.r#type != (Type::Tuple { items: map.params.clone() })
        || output.r#type != map.result
        || input.rows.len() != output.rows.len()
      {
        return Err(format!("table/map interface mismatch for {}", map.name));
      }
      if map_indexes[map.input].is_none() {
        map_indexes[map.input] = Some(std::sync::Arc::new(
          crate::table::TableIndex::new(&tables[map.input], backend)?,
        ));
      }
    }
    let mut memory_layouts = HashMap::new();
    for (id, function) in self.functions.iter().enumerate() {
      check_function(
        function,
        inputs[id].width(),
        outputs[id].width(),
        &inputs,
        &outputs,
        &self.enums,
        field,
        &mut memory_layouts,
      )
      .map_err(|e| format!("{}: {e}", function.name))?;
    }
    let division_inverses: Vec<_> =
      self.functions.iter().map(|f| constant_divisions(f, backend)).collect();
    // Resolve structural memory types and layouts once. Type IDs are local
    // to this checked program; the public record retains the full types.
    let memory_types: Vec<_> = memory_layouts
      .iter()
      .map(|(ty, layout)| (ty.clone(), layout.clone()))
      .collect();
    let memory_ids = memory_types
      .iter()
      .enumerate()
      .map(|(i, (ty, _))| (ty.clone(), i))
      .collect();
    let (execution_functions, initial_registers): (Vec<_>, Vec<_>) = self
      .functions
      .iter()
      .zip(&inputs)
      .zip(&division_inverses)
      .map(|((f, input), inverses)| {
        let mut f = f.clone();
        dead_code::eliminate(&mut f, inverses);
        link_registers(&f, input.width(), field)
      })
      .unzip();
    let steps = execution_functions
      .iter()
      .zip(&initial_registers)
      .map(|(f, initial)| execution_steps(f, &memory_ids, initial))
      .collect();
    let returns = execution_functions.iter().map(return_plans).collect();
    let initial_registers = initial_registers
      .into_iter()
      .map(|row| {
        row
          .into_iter()
          .map(|(reg, value)| (reg, backend.from_u64(value)))
          .collect()
      })
      .collect();
    let execution_functions = execution_functions
      .into_iter()
      .map(|f| Function {
        name: f.name,
        params: f.params,
        result: f.result,
        registers: f.registers,
        code: f
          .code
          .into_iter()
          .map(|op| op.map_constants(|v| backend.from_u64(v)))
          .collect(),
      })
      .collect();
    Ok(CheckedProgram {
      program: std::sync::Arc::new(self),
      field: backend,
      inputs,
      outputs,
      memory_layouts,
      memory_types,
      map_indexes,
      tables,
      division_inverses,
      steps,
      returns,
      execution_functions,
      initial_registers,
    })
  }
}

/// Cache inverses of literal denominators within a basic block. Keep the wire
/// bytecode and instruction sites intact for diagnostics and saved hint answers.
/// Forget facts at every join; a zero denominator still fails only if executed.
fn constant_divisions<B: FieldBackend>(
  function: &Function,
  field: B,
) -> Vec<Option<B::Element>> {
  let mut targets = vec![false; function.code.len()];
  for op in &function.code {
    let target = match op {
      Instruction::Branch { otherwise, .. } => Some(*otherwise),
      Instruction::Jump { target } => Some(*target),
      _ => None,
    };
    if let Some(target) = target.and_then(|i| targets.get_mut(i)) {
      *target = true;
    }
  }
  let mut constants = vec![None; function.registers];
  let mut inverses = vec![None; function.code.len()];
  for (pc, op) in function.code.iter().enumerate() {
    if targets[pc] {
      constants.fill(None);
    }
    // Validation permits unreachable instructions to be arbitrary. Facts
    // are a performance aid, so an out-of-range register simply has none.
    let mut writes = vec![];
    match op {
      Instruction::Literal { dest, value } => {
        writes.push((*dest, Some(*value)))
      },
      Instruction::Copy { dest, source } => {
        for (dest, source) in dest.iter().zip(source) {
          writes.push((*dest, constants.get(*source).copied().flatten()));
        }
      },
      Instruction::Binary { dest, operator, right, .. } => {
        if matches!(operator, Binary::Div) {
          inverses[pc] = constants
            .get(*right)
            .copied()
            .flatten()
            .filter(|&x| field.contains(x))
            .and_then(|x| field.inverse(field.from_u64(x)));
        }
        writes.push((*dest, None));
      },
      Instruction::Neg { dest, .. } | Instruction::Store { dest, .. } => {
        writes.push((*dest, None))
      },
      Instruction::Call { dest, .. }
      | Instruction::Load { dest, .. }
      | Instruction::Hint { dest, .. } => {
        writes.extend(dest.iter().map(|dest| (*dest, None)));
      },
      Instruction::Jump { .. }
      | Instruction::Ret { .. }
      | Instruction::Fail { .. } => constants.fill(None),
      _ => {},
    }
    for (dest, value) in writes {
      if let Some(slot) = constants.get_mut(dest) {
        *slot = value;
      }
    }
  }
  inverses
}

// Intra-function control flow is forward-only; recursion uses an explicit VM
// call stack. A forward dataflow pass checks initialization on every path.
#[allow(clippy::too_many_arguments)]
fn check_function(
  f: &Function,
  input: usize,
  output: usize,
  inputs: &[Layout],
  outputs: &[Layout],
  enums: &[Enum],
  field: PrimeField,
  layouts: &mut HashMap<Type, Layout>,
) -> Result<(), String> {
  if input > f.registers || f.code.is_empty() {
    return Err("missing input registers or empty code".into());
  }
  let mut states: Vec<Option<Vec<bool>>> = vec![None; f.code.len()];
  let mut initial = vec![false; f.registers];
  initial[..input].fill(true);
  states[0] = Some(initial);
  for (pc, instruction) in f.code.iter().enumerate() {
    let Some(mut initialized) = states[pc].take() else {
      continue;
    };
    let mut reads = vec![];
    let mut writes = vec![];
    let mut successors = vec![pc + 1];
    use Instruction::*;
    match instruction {
      Literal { dest, value } => {
        if !field.contains(*value) {
          return Err("noncanonical literal".into());
        }
        writes.push(*dest);
      },
      Copy { dest, source } => {
        if dest.len() != source.len() {
          return Err("copy width mismatch".into());
        }
        reads.extend(source);
        writes.extend(dest);
      },
      Neg { dest, source } => {
        reads.push(*source);
        writes.push(*dest);
      },
      Binary { dest, left, right, .. } => {
        reads.extend([left, right]);
        writes.push(*dest);
      },
      Guard { tests, .. } | Branch { tests, .. } => {
        for (reg, value) in tests {
          if !field.contains(*value) {
            return Err("noncanonical pattern literal".into());
          }
          reads.push(*reg);
        }
        if let Branch { otherwise, tests } = instruction
          && !tests.is_empty()
        {
          successors.push(*otherwise);
        }
      },
      Jump { target } => {
        successors = vec![*target];
      },
      Call { function, args, dest } => {
        if inputs.get(*function).is_none_or(|l| l.width() != args.len())
          || outputs.get(*function).is_none_or(|l| l.width() != dest.len())
        {
          return Err("call interface mismatch".into());
        }
        reads.extend(args);
        writes.extend(dest);
      },
      Store { r#type, value, dest } => {
        let layout = r#type.layout(enums, &mut vec![])?;
        if layout.width() != value.len() {
          return Err("store width mismatch".into());
        }
        layouts.insert(r#type.clone(), layout);
        reads.extend(value);
        writes.push(*dest);
      },
      Load { r#type, pointer, dest } => {
        let layout = r#type.layout(enums, &mut vec![])?;
        if layout.width() != dest.len() {
          return Err("load width mismatch".into());
        }
        layouts.insert(r#type.clone(), layout);
        reads.push(*pointer);
        writes.extend(dest);
      },
      Hint { r#type, key_type, key, dest, .. } => {
        let layout = r#type.layout(enums, &mut vec![])?;
        let key_layout = key_type.layout(enums, &mut vec![])?;
        if !layout.pointer_free()
          || !key_layout.pointer_free()
          || layout.width() != dest.len()
          || key_layout.width() != key.len()
        {
          return Err("invalid hint type or width".into());
        }
        reads.extend(key);
        writes.extend(dest);
      },
      AssertEq { left, right, .. } => {
        if left.len() != right.len() {
          return Err("assertion width mismatch".into());
        }
        reads.extend(left);
        reads.extend(right);
      },
      Ret { value } => {
        if value.len() != output {
          return Err("return width mismatch".into());
        }
        reads.extend(value);
        successors.clear();
      },
      Fail { .. } => {
        successors.clear();
      },
    }
    for reg in reads {
      if initialized.get(reg) != Some(&true) {
        return Err(format!("instruction {pc} reads undefined register {reg}"));
      }
    }
    for reg in writes {
      *initialized
        .get_mut(reg)
        .ok_or("destination register out of bounds")? = true;
    }
    for next in successors {
      if next <= pc || next >= f.code.len() {
        return Err(format!(
          "invalid forward jump/fallthrough from {pc} to {next}"
        ));
      }
      match &mut states[next] {
        None => states[next] = Some(initialized.clone()),
        Some(state) => {
          for (old, new) in state.iter_mut().zip(&initialized) {
            *old &= new;
          }
        },
      }
    }
  }
  Ok(())
}
