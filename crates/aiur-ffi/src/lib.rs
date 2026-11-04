//! Reads an Aiur runtime image (`Aiur.Image.RuntimeImage`, in
//! `Aiur/Aiur/Image.lean`) directly from Lean objects into the runtime's
//! owned [`aiur::Program`] and [`TraceArtifact`].
//!
//! The image is borrowed for the duration of one call and copied once; no
//! JSON or intermediate encoding is built. Every constructor's tag and
//! object-field count is checked against its declared layout, every natural
//! must be a scalar below `2^63`, every field element must be canonical, and
//! every node of the trace's polynomial pool must reference only earlier
//! nodes; polynomials are expanded from the pool without recursion and
//! within [`aiur::artifact::pool::MAX_EXPANDED_NODES`]. Semantic
//! validation (register bounds, layouts, hint sites, group placements) stays
//! in `Program::check_field` and `TracePlan::new`.
//!
//! Each Lean type is declared with `lean_inductive!` and its per-constructor
//! layout; fields are read through the generated accessors.
use aiur::{
  Program,
  artifact::pool::{Node, Pool},
  bytecode::{
    Binary, Constructor, Entry, Enum, Function, Instruction, Map, Table, Type,
  },
  trace::{
    Action, Chip, ColumnWrite, FunctionGroup, FunctionPlan, GroupLookup,
    GroupMember, GroupWrite, MemoryLookup, Polynomial, PopulationStep, Send,
    TraceArtifact,
  },
  value::IoType,
};
use lean_ffi::object::{
  LeanBorrowed, LeanCtorLayout, LeanRef, SingleCtorLayout,
};

const MAX_NESTING: usize = 256;

type Result<T> = std::result::Result<T, String>;

lean_ffi::lean_inductive! {
  LeanTy [
    { },             // field
    { num_obj: 1 },  // tuple
    { num_obj: 1 },  // ptr
    { num_obj: 1 },  // enum
  ];
  LeanIoType [
    { },             // field
    { num_obj: 1 },  // tuple
    { num_obj: 2 },  // array
    { num_obj: 2 },  // record
    { num_obj: 2 },  // enum
  ];
  LeanTests [ { num_obj: 2 } ];
  LeanInstruction [
    { num_obj: 1, num_64: 1 },  // literal: dest; value
    { num_obj: 2 },             // copy
    { num_obj: 2 },             // neg
    { num_obj: 3, num_8: 1 },   // binary: dest left right; op
    { num_obj: 2 },             // guard
    { num_obj: 2 },             // branch
    { num_obj: 1 },             // jump
    { num_obj: 3 },             // call
    { num_obj: 3 },             // store
    { num_obj: 3 },             // load
    { num_obj: 5 },             // hint
    { num_obj: 3, num_8: 1 },   // assertEq: left right message; runtimeCheck
    { num_obj: 1 },             // ret
    { num_obj: 1 },             // fail
  ];
  LeanFunction [ { num_obj: 5 } ];
  LeanEnum [ { num_obj: 2 } ];
  LeanTable [ { num_obj: 3 } ];
  LeanMap [ { num_obj: 5 } ];
  LeanEntry [ { num_obj: 4 } ];
  /// Six object fields, then `modulus : UInt64`.
  LeanProgram [ { num_obj: 6, num_64: 1 } ];
  LeanAction [
    { num_obj: 2 },  // assign
    { num_obj: 2 },  // inverse
    { num_obj: 2 },  // choose
    { num_obj: 2 },  // failure
    { num_obj: 3 },  // call
    { num_obj: 3 },  // store
    { num_obj: 3 },  // load
    { num_obj: 6 },  // hint
  ];
  LeanStep [ { num_obj: 2 } ];
  LeanColumnWrite [ { num_obj: 3 } ];
  LeanFunctionPlan [ { num_obj: 7 } ];
  LeanSend [ { num_obj: 4 } ];
  LeanMemoryLookup [ { num_obj: 4 } ];
  LeanChip [ { num_obj: 8 } ];
  LeanGroupLookup [ { num_obj: 2 } ];
  LeanGroupWrite [ { num_obj: 2 } ];
  LeanGroupMember [ { num_obj: 4 } ];
  LeanGroup [ { num_obj: 7 } ];
  /// Five object fields, then `modulus : UInt64`.
  LeanTrace [ { num_obj: 5, num_64: 1 } ];
  LeanRuntimeImage [ { num_obj: 2 } ];
  /// `α × β` stored in a field or an array.
  LeanPair [ { num_obj: 2 } ];
  /// `Option α` stored in a field. `LeanOption` can only wrap an owned
  /// reference or an FFI argument, so a borrowed field is read through this
  /// layout instead.
  LeanOptionField [
    { },             // none
    { num_obj: 1 },  // some
  ];
}

/// The constructor tag of `object`, checked against the layouts of `T`
/// before it is wrapped: a boxed scalar must name a constructor without
/// fields, and a constructor object must have its variant's object fields.
/// The generated accessors are only used after this check, so a malformed
/// value is an error rather than an out-of-bounds read or an abort.
fn variant<'a, T: LeanCtorLayout>(
  object: LeanBorrowed<'a>,
  wrap: fn(LeanBorrowed<'a>) -> T,
  name: &str,
) -> Result<(usize, T)> {
  let (tag, objects) = if object.is_scalar() {
    (object.unbox_usize(), None)
  } else {
    (usize::from(object.tag()), Some(object.as_ctor().num_objs()))
  };
  let layout =
    T::LAYOUTS.get(tag).ok_or_else(|| format!("invalid {name} tag {tag}"))?;
  match objects {
    None if *layout == SingleCtorLayout::ZERO => {},
    None => return Err(format!("{name}: expected a constructor object")),
    Some(found) if found == layout.num_obj => {},
    Some(found) => {
      return Err(format!(
        "{name}: expected {} object fields, found {found}",
        layout.num_obj
      ));
    },
  }
  Ok((tag, wrap(object)))
}

/// A structure value, checked as [`variant`] checks it.
fn record<'a, T: LeanCtorLayout>(
  object: LeanBorrowed<'a>,
  wrap: fn(LeanBorrowed<'a>) -> T,
  name: &str,
) -> Result<T> {
  Ok(variant(object, wrap, name)?.1)
}

fn nat(object: LeanBorrowed<'_>) -> Result<usize> {
  if object.is_scalar() {
    Ok(object.unbox_usize())
  } else {
    Err("natural number exceeds the scalar range".into())
  }
}

fn string(object: LeanBorrowed<'_>) -> String {
  object.as_string().as_str().to_owned()
}

fn array<T>(
  object: LeanBorrowed<'_>,
  f: impl FnMut(LeanBorrowed<'_>) -> Result<T>,
) -> Result<Vec<T>> {
  object.as_array().iter().map(f).collect()
}

fn nats(object: LeanBorrowed<'_>) -> Result<Vec<usize>> {
  array(object, nat)
}

fn option<T>(
  object: LeanBorrowed<'_>,
  f: impl FnOnce(LeanBorrowed<'_>) -> Result<T>,
) -> Result<Option<T>> {
  match variant(object, LeanOptionField, "Option")? {
    (0, _) => Ok(None),
    (_, some) => f(some.get_obj(0)).map(Some),
  }
}

fn pair<T>(
  object: LeanBorrowed<'_>,
  f: impl FnOnce(LeanBorrowed<'_>, LeanBorrowed<'_>) -> Result<T>,
) -> Result<T> {
  let p = record(object, LeanPair, "Prod")?;
  f(p.get_obj(0), p.get_obj(1))
}

fn flag(byte: u8) -> Result<bool> {
  match byte {
    0 => Ok(false),
    1 => Ok(true),
    other => Err(format!("invalid Bool {other}")),
  }
}

/// Reads field elements against the image's modulus.
#[derive(Clone, Copy)]
struct Field(u64);

impl Field {
  fn canonical(self, value: u64) -> Result<u64> {
    if value < self.0 {
      Ok(value)
    } else {
      Err(format!("noncanonical field element {value}"))
    }
  }

  /// A boxed `UInt64` array element.
  fn element(self, object: LeanBorrowed<'_>) -> Result<u64> {
    if object.is_scalar() {
      return Err("expected a boxed UInt64".into());
    }
    self.canonical(object.unbox_u64())
  }
}

fn ty(object: LeanBorrowed<'_>, depth: usize) -> Result<Type> {
  if depth > MAX_NESTING {
    return Err("type nesting too deep".into());
  }
  let (tag, t) = variant(object, LeanTy, "Ty")?;
  Ok(match tag {
    0 => Type::Field,
    1 => Type::Tuple { items: array(t.get_obj(0), |t| ty(t, depth + 1))? },
    2 => Type::Ptr { target: Box::new(ty(t.get_obj(0), depth + 1)?) },
    _ => Type::Enum { name: string(t.get_obj(0)) },
  })
}

fn tys(object: LeanBorrowed<'_>) -> Result<Vec<Type>> {
  array(object, |t| ty(t, 0))
}

fn io_type(object: LeanBorrowed<'_>, depth: usize) -> Result<IoType> {
  if depth > MAX_NESTING {
    return Err("IO type nesting too deep".into());
  }
  let next = |t: LeanBorrowed<'_>| io_type(t, depth + 1);
  let (tag, t) = variant(object, LeanIoType, "IOType")?;
  Ok(match tag {
    0 => IoType::Field,
    1 => IoType::Tuple { items: array(t.get_obj(0), next)? },
    2 => IoType::Array {
      element: Box::new(next(t.get_obj(0))?),
      length: nat(t.get_obj(1))?,
    },
    3 => IoType::Struct {
      name: string(t.get_obj(0)),
      fields: array(t.get_obj(1), |entry| {
        pair(entry, |name, t| Ok((string(name), next(t)?)))
      })?,
    },
    _ => IoType::Enum {
      name: string(t.get_obj(0)),
      constructors: array(t.get_obj(1), |entry| {
        pair(entry, |name, fields| Ok((string(name), array(fields, next)?)))
      })?,
    },
  })
}

fn tests(object: LeanBorrowed<'_>, field: Field) -> Result<Vec<(usize, u64)>> {
  let t = record(object, LeanTests, "Tests")?;
  let registers = nats(t.get_obj(0))?;
  let values = array(t.get_obj(1), |v| field.element(v))?;
  if registers.len() != values.len() {
    return Err("test registers and values differ in length".into());
  }
  Ok(registers.into_iter().zip(values).collect())
}

fn instruction(object: LeanBorrowed<'_>, field: Field) -> Result<Instruction> {
  let (tag, i) = variant(object, LeanInstruction, "Instruction")?;
  Ok(match tag {
    0 => Instruction::Literal {
      dest: nat(i.get_obj(0))?,
      value: field.canonical(i.get_num_64(0))?,
    },
    1 => Instruction::Copy {
      dest: nats(i.get_obj(0))?,
      source: nats(i.get_obj(1))?,
    },
    2 => {
      Instruction::Neg { dest: nat(i.get_obj(0))?, source: nat(i.get_obj(1))? }
    },
    3 => {
      let operator = match i.get_num_8(0) {
        0 => Binary::Add,
        1 => Binary::Sub,
        2 => Binary::Mul,
        3 => Binary::Div,
        other => return Err(format!("invalid binary operator {other}")),
      };
      Instruction::Binary {
        dest: nat(i.get_obj(0))?,
        operator,
        left: nat(i.get_obj(1))?,
        right: nat(i.get_obj(2))?,
      }
    },
    4 => Instruction::Guard {
      tests: tests(i.get_obj(0), field)?,
      message: string(i.get_obj(1)),
    },
    5 => Instruction::Branch {
      tests: tests(i.get_obj(0), field)?,
      otherwise: nat(i.get_obj(1))?,
    },
    6 => Instruction::Jump { target: nat(i.get_obj(0))? },
    7 => Instruction::Call {
      function: nat(i.get_obj(0))?,
      args: nats(i.get_obj(1))?,
      dest: nats(i.get_obj(2))?,
    },
    8 => Instruction::Store {
      r#type: ty(i.get_obj(0), 0)?,
      value: nats(i.get_obj(1))?,
      dest: nat(i.get_obj(2))?,
    },
    9 => Instruction::Load {
      r#type: ty(i.get_obj(0), 0)?,
      pointer: nat(i.get_obj(1))?,
      dest: nats(i.get_obj(2))?,
    },
    10 => Instruction::Hint {
      channel: string(i.get_obj(0)),
      r#type: ty(i.get_obj(1), 0)?,
      key_type: ty(i.get_obj(2), 0)?,
      key: nats(i.get_obj(3))?,
      dest: nats(i.get_obj(4))?,
    },
    11 => Instruction::AssertEq {
      left: nats(i.get_obj(0))?,
      right: nats(i.get_obj(1))?,
      message: option(i.get_obj(2), |m| Ok(string(m)))?,
      runtime_check: flag(i.get_num_8(0))?,
    },
    12 => Instruction::Ret { value: nats(i.get_obj(0))? },
    _ => Instruction::Fail { message: string(i.get_obj(0)) },
  })
}

/// The bytecode of an `Aiur.Image.Program`.
pub fn program(object: LeanBorrowed<'_>) -> Result<Program> {
  let p = record(object, LeanProgram, "Program")?;
  let modulus = p.get_num_64(0);
  if modulus < 2 {
    return Err("invalid modulus".into());
  }
  let field = Field(modulus);
  let version = u32::try_from(nat(p.get_obj(0))?).map_err(|e| e.to_string())?;
  let functions = array(p.get_obj(1), |f| {
    let f = record(f, LeanFunction, "Function")?;
    Ok(Function {
      name: string(f.get_obj(0)),
      params: tys(f.get_obj(1))?,
      result: ty(f.get_obj(2), 0)?,
      registers: nat(f.get_obj(3))?,
      code: array(f.get_obj(4), |i| instruction(i, field))?,
    })
  })?;
  let enums = array(p.get_obj(2), |e| {
    let e = record(e, LeanEnum, "Enum")?;
    Ok(Enum {
      name: string(e.get_obj(0)),
      constructors: array(e.get_obj(1), |entry| {
        pair(entry, |name, fields| {
          Ok(Constructor { name: string(name), fields: tys(fields)? })
        })
      })?,
    })
  })?;
  let tables = array(p.get_obj(3), |t| {
    let t = record(t, LeanTable, "Table")?;
    Ok(Table {
      name: string(t.get_obj(0)),
      r#type: ty(t.get_obj(1), 0)?,
      rows: array(t.get_obj(2), |row| array(row, |v| field.element(v)))?,
    })
  })?;
  let maps = array(p.get_obj(4), |m| {
    let m = record(m, LeanMap, "Map")?;
    Ok(Map {
      name: string(m.get_obj(0)),
      params: tys(m.get_obj(1))?,
      result: ty(m.get_obj(2), 0)?,
      input: nat(m.get_obj(3))?,
      output: nat(m.get_obj(4))?,
    })
  })?;
  let entries = array(p.get_obj(5), |e| {
    let e = record(e, LeanEntry, "Entry")?;
    Ok(Entry {
      name: string(e.get_obj(0)),
      function: nat(e.get_obj(1))?,
      inputs: array(e.get_obj(2), |t| io_type(t, 0))?,
      output: option(e.get_obj(3), |t| io_type(t, 0))?,
    })
  })?;
  Ok(Program { version, modulus, functions, enums, tables, maps, entries })
}

fn word(bytes: &[u8], at: usize) -> u64 {
  u64::from_le_bytes(bytes[at..at + 8].try_into().expect("eight bytes"))
}

/// The polynomial pool of a node buffer: three words (tag, a, b) per node,
/// every operand an earlier node.
pub fn pool(bytes: &[u8], modulus: u64) -> Result<Pool> {
  let (nodes, []) = bytes.as_chunks::<24>() else {
    return Err("malformed polynomial nodes".into());
  };
  let mut pool = Pool::new(modulus, false);
  for node in nodes {
    let (tag, a, b) = (word(node, 0), word(node, 8), word(node, 16));
    let index = |w: u64| usize::try_from(w).map_err(|e| e.to_string());
    let node = match tag {
      0 | 1 if b != 0 => {
        return Err("leaf polynomial node with a second operand".into());
      },
      0 => Node::Const(a),
      _ => {
        let tag = u8::try_from(tag)
          .map_err(|e| format!("invalid polynomial node tag {tag}: {e}"))?;
        Node::from_parts(tag, index(a)?, index(b)?)?
      },
    };
    pool.push(node)?;
  }
  Ok(pool)
}

fn poly(object: LeanBorrowed<'_>, pool: &mut Pool) -> Result<Polynomial> {
  pool.expand(nat(object)?)
}

fn polys(object: LeanBorrowed<'_>, pool: &mut Pool) -> Result<Vec<Polynomial>> {
  array(object, |p| poly(p, pool))
}

fn action(object: LeanBorrowed<'_>, m: &mut Pool) -> Result<Action> {
  let (tag, a) = variant(object, LeanAction, "Action")?;
  Ok(match tag {
    0 => Action::Assign {
      dest: nats(a.get_obj(0))?,
      values: polys(a.get_obj(1), m)?,
    },
    1 => Action::Inverse {
      dest: nat(a.get_obj(0))?,
      value: poly(a.get_obj(1), m)?,
    },
    2 => Action::Choose {
      dest: nats(a.get_obj(0))?,
      tests: array(a.get_obj(1), |t| polys(t, m))?,
    },
    3 => Action::Failure {
      dest: nats(a.get_obj(0))?,
      differences: polys(a.get_obj(1), m)?,
    },
    4 => Action::Call {
      name: string(a.get_obj(0)),
      args: polys(a.get_obj(1), m)?,
      dest: nats(a.get_obj(2))?,
    },
    5 => Action::Store {
      r#type: ty(a.get_obj(0), 0)?,
      values: polys(a.get_obj(1), m)?,
      dest: nat(a.get_obj(2))?,
    },
    6 => Action::Load {
      r#type: ty(a.get_obj(0), 0)?,
      address: poly(a.get_obj(1), m)?,
      dest: nats(a.get_obj(2))?,
    },
    _ => Action::Hint {
      channel: string(a.get_obj(0)),
      instruction: nat(a.get_obj(1))?,
      r#type: ty(a.get_obj(2), 0)?,
      key_type: ty(a.get_obj(3), 0)?,
      key: polys(a.get_obj(4), m)?,
      dest: nats(a.get_obj(5))?,
    },
  })
}

fn function_plan(
  object: LeanBorrowed<'_>,
  m: &mut Pool,
) -> Result<FunctionPlan> {
  let f = record(object, LeanFunctionPlan, "FunctionPlan")?;
  Ok(FunctionPlan {
    name: string(f.get_obj(0)),
    chip: string(f.get_obj(1)),
    witnesses: nat(f.get_obj(2))?,
    inputs: nats(f.get_obj(3))?,
    output: nats(f.get_obj(4))?,
    steps: array(f.get_obj(5), |s| {
      let s = record(s, LeanStep, "Step")?;
      Ok(PopulationStep {
        guard: poly(s.get_obj(0), m)?,
        action: action(s.get_obj(1), m)?,
      })
    })?,
    writes: array(f.get_obj(6), |w| {
      let w = record(w, LeanColumnWrite, "ColumnWrite")?;
      Ok(ColumnWrite {
        column: nat(w.get_obj(0))?,
        source: nat(w.get_obj(1))?,
        guard: poly(w.get_obj(2), m)?,
      })
    })?,
  })
}

fn chip(object: LeanBorrowed<'_>, m: &mut Pool) -> Result<Chip> {
  let c = record(object, LeanChip, "Chip")?;
  Ok(Chip {
    name: string(c.get_obj(0)),
    width: nat(c.get_obj(1))?,
    activation: nat(c.get_obj(2))?,
    inputs: nats(c.get_obj(3))?,
    output: polys(c.get_obj(4), m)?,
    constraints: polys(c.get_obj(5), m)?,
    sends: array(c.get_obj(6), |s| {
      let s = record(s, LeanSend, "Send")?;
      Ok(Send {
        channel: string(s.get_obj(0)),
        args: polys(s.get_obj(1), m)?,
        result: nats(s.get_obj(2))?,
        enable: poly(s.get_obj(3), m)?,
      })
    })?,
    memory: array(c.get_obj(7), |l| {
      let l = record(l, LeanMemoryLookup, "MemoryLookup")?;
      Ok(MemoryLookup {
        r#type: ty(l.get_obj(0), 0)?,
        address: poly(l.get_obj(1), m)?,
        values: polys(l.get_obj(2), m)?,
        enable: poly(l.get_obj(3), m)?,
      })
    })?,
  })
}

fn group(object: LeanBorrowed<'_>, m: &mut Pool) -> Result<FunctionGroup> {
  let g = record(object, LeanGroup, "Group")?;
  Ok(FunctionGroup {
    name: string(g.get_obj(0)),
    width: nat(g.get_obj(1))?,
    activation: poly(g.get_obj(2), m)?,
    constraints: polys(g.get_obj(3), m)?,
    receive: polys(g.get_obj(4), m)?,
    sends: array(g.get_obj(5), |s| {
      let s = record(s, LeanGroupLookup, "GroupLookup")?;
      Ok(GroupLookup {
        enable: poly(s.get_obj(0), m)?,
        args: polys(s.get_obj(1), m)?,
      })
    })?,
    members: array(g.get_obj(6), |member| {
      let member = record(member, LeanGroupMember, "GroupMember")?;
      Ok(GroupMember {
        name: string(member.get_obj(0)),
        columns: nats(member.get_obj(1))?,
        selector: nat(member.get_obj(2))?,
        writes: array(member.get_obj(3), |w| {
          let w = record(w, LeanGroupWrite, "GroupWrite")?;
          Ok(GroupWrite {
            column: nat(w.get_obj(0))?,
            value: poly(w.get_obj(1), m)?,
          })
        })?,
      })
    })?,
  })
}

/// The trace artifact of an `Aiur.Image.Trace`.
pub fn trace(object: LeanBorrowed<'_>) -> Result<TraceArtifact> {
  let t = record(object, LeanTrace, "Trace")?;
  let modulus = t.get_num_64(0);
  if modulus < 2 {
    return Err("invalid modulus".into());
  }
  let mut nodes = pool(t.get_obj(4).as_byte_array().as_bytes(), modulus)?;
  let m = &mut nodes;
  Ok(TraceArtifact {
    version: u32::try_from(nat(t.get_obj(0))?).map_err(|e| e.to_string())?,
    modulus,
    functions: array(t.get_obj(1), |f| function_plan(f, m))?,
    chips: array(t.get_obj(2), |x| chip(x, m))?,
    groups: array(t.get_obj(3), |g| group(g, m))?,
  })
}

/// The program and trace artifact of an `Aiur.Image.RuntimeImage`. Both
/// must name the same field.
pub fn runtime_image(
  image: LeanRuntimeImage<LeanBorrowed<'_>>,
) -> Result<(Program, TraceArtifact)> {
  let image = record(*image.inner(), LeanRuntimeImage, "RuntimeImage")?;
  let program = program(image.get_obj(0))?;
  let trace = trace(image.get_obj(1))?;
  if program.modulus != trace.modulus {
    return Err("the program and trace artifact name different fields".into());
  }
  Ok((program, trace))
}

#[cfg(test)]
mod tests {
  use super::*;

  fn node(tag: u64, a: u64, b: u64) -> Vec<u8> {
    [tag, a, b].iter().flat_map(|w| w.to_le_bytes()).collect()
  }

  #[test]
  fn polynomial_nodes_form_a_dag() {
    let bytes =
      [node(1, 3, 0), node(0, 5, 0), node(4, 0, 1), node(2, 2, 2)].concat();
    let mut nodes = pool(&bytes, 7).unwrap();
    let product =
      Polynomial::Mul(Box::new([Polynomial::Var(3), Polynomial::Const(5)]));
    assert_eq!(nodes.expand(2).unwrap(), product);
    assert_eq!(
      nodes.expand(3).unwrap(),
      Polynomial::Add(Box::new([product.clone(), product]))
    );
    assert!(nodes.expand(4).is_err());
    let forward = [node(2, 1, 2), node(1, 0, 0), node(1, 1, 0)].concat();
    assert!(pool(&forward, 7).is_err());
    let own = [node(1, 0, 0), node(2, 0, 1)].concat();
    assert!(pool(&own, 7).is_err());
    assert!(pool(&node(0, 7, 0), 7).is_err());
    assert!(pool(&node(1, 0, 1), 7).is_err());
    assert!(pool(&node(9, 0, 0), 7).is_err());
    assert!(pool(&node(1 << 40, 0, 0), 7).is_err());
    assert!(pool(&[], 7).unwrap().is_empty());
    assert!(pool(&[0; 23], 7).is_err());
  }

  #[test]
  fn deep_polynomials_need_no_recursion() {
    let depth = 200_000;
    let mut bytes = node(1, 0, 0);
    for i in 0..depth {
      bytes.extend(node(1, 1, 0));
      bytes.extend(node(2, 2 * i, 2 * i + 1));
    }
    // Building is iterative; only dropping the tree recurses, so drop it on
    // a thread with room for that.
    let root = usize::try_from(2 * depth).unwrap();
    let p = pool(&bytes, 7).unwrap().expand(root).unwrap();
    std::thread::Builder::new()
      .stack_size(1 << 30)
      .spawn(move || drop(p))
      .unwrap()
      .join()
      .unwrap();
  }
}
