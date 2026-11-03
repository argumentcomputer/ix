//! Rust source for a native kernel.
//!
//! Each function becomes a Rust function over a local register array, so
//! registers written on several paths (match arms joining into shared result
//! registers, overwrites, simultaneous copies) keep their bytecode semantics
//! without SSA conversion. Control flow is forward-only, which the checker
//! enforces; it is emitted as a dispatch loop over basic blocks. A block
//! starts at entry 0, at every branch or jump target and at every entry with
//! several predecessors; every other entry has exactly one predecessor, the
//! fall-through of the entry before it, and is emitted inline after it. No
//! block is duplicated.
use aiur::bytecode::Binary;
use aiur::native::{NativeFunction, NativeOp, NativePlan};
use std::fmt::Write;

pub(crate) struct Kernel<'a> {
  pub(crate) program: &'a aiur::Program,
  pub(crate) public: bool,
  pub(crate) name: &'a str,
  pub(crate) artifact: &'a str,
  /// The environment variable that named the artifact, if any.
  pub(crate) variable: Option<&'a str>,
  pub(crate) fingerprint: &'a str,
  pub(crate) plan: &'a NativePlan,
}

pub(crate) fn kernel(k: &Kernel<'_>) -> String {
  let mut s = String::new();
  let vis = if k.public { "pub " } else { "" };
  let name = k.name;
  let _ = writeln!(
    s,
    "#[doc = \"Generated native executor (fingerprint {fp}).\"]\n\
     #[derive(Clone, Copy, Debug, Default)]\n{vis}struct {name};",
    fp = k.fingerprint
  );
  s.push_str("const _: () = {\n");
  s.push_str(
    "use ::aiur::native::{Begin, Failed, Kernel, Runtime, grow};\n\
     use ::aiur::field::FieldBackend;\n\
",
  );
  let _ =
    writeln!(s, "const _ARTIFACT: &[u8] = include_bytes!({:?});", k.artifact);
  // `include_bytes!` tracks the file's contents, `env!` the variable that
  // chose it: Cargo regenerates the kernel when either changes.
  if let Some(variable) = k.variable {
    let _ = writeln!(s, "const _VARIABLE: &str = env!({variable:?});");
  }
  let _ = writeln!(s, "impl Kernel for {name} {{");
  let _ = writeln!(s, "const FINGERPRINT: &'static str = {:?};", k.fingerprint);
  s.push_str(
    "fn run<B: FieldBackend>(rt: &mut Runtime<'_, B>, function: usize, row: usize, \
     args: &[B::Element], output: &mut Vec<B::Element>) -> Result<(), Failed> {\n\
     match function {\n",
  );
  for (id, f) in k.plan.functions.iter().enumerate() {
    let _ = writeln!(
      s,
      "{id} => {{ let a: [B::Element; {n}] = args.try_into().expect(\"argument width\"); \
       let o = f_{id}::<B>(rt, row, a)?; output.extend_from_slice(&o); }}",
      n = f.inputs
    );
  }
  s.push_str("_ => unreachable!(\"unknown function\"),\n}\nOk(())\n}\n}\n");
  let closed = closed_forms(k.program);
  for (id, f) in k.plan.functions.iter().enumerate() {
    call_wrapper(&mut s, id, f);
    body(&mut s, k.plan, &closed, id, f);
  }
  s.push_str("};\n");
  s
}

fn call_wrapper(s: &mut String, id: usize, f: &NativeFunction) {
  let (n, m) = (f.inputs, f.outputs);
  let _ = writeln!(
    s,
    "#[inline(never)]\n#[allow(non_snake_case, clippy::all)]\n\
     fn c_{id}<B: FieldBackend>(rt: &mut Runtime<'_, B>, caller: usize, pc: usize, \
     a: [B::Element; {n}]) -> Result<[B::Element; {m}], Failed> {{\n\
     match rt.begin(caller, pc, {id}, &a)? {{\n\
     Begin::Cached(row) => {{ let mut o = [rt.field().zero(); {m}]; \
     o.copy_from_slice(rt.output({id}, row)); Ok(o) }}\n\
     Begin::Started(row) => grow(65536 + 2 * {regs} * ::core::mem::size_of::<B::Element>(), \
     || f_{id}::<B>(rt, row, a)),\n}}\n}}",
    regs = f.registers
  );
}

fn regs(list: &[usize]) -> String {
  list.iter().map(|r| format!("r[{r}]")).collect::<Vec<_>>().join(", ")
}

fn tests(list: &[(usize, u64)]) -> String {
  if list.is_empty() {
    return "true".into();
  }
  list
    .iter()
    .map(|(r, v)| format!("r[{r}] == fd.from_u64({v})"))
    .collect::<Vec<_>>()
    .join(" && ")
}

fn writes(dest: &[usize], source: &str) -> String {
  dest
    .iter()
    .enumerate()
    .map(|(i, d)| format!("r[{d}] = {source}[{i}];"))
    .collect::<Vec<_>>()
    .join(" ")
}

/// A fixed table whose rows the generated code can compute: the input table
/// lists every argument tuple once in mixed-radix order (first argument most
/// significant) and each output column equals one of [`CANDIDATES`] on every
/// row. Calls then cost arithmetic and one counter increment.
struct ClosedForm {
  radix: Vec<u64>,
  outputs: Vec<&'static str>,
}

type Candidate = (&'static str, fn(u64, u64) -> u64);

/// Expressions over the arguments `a` and `b` (`b` is 0 for unary maps).
const CANDIDATES: &[Candidate] = &[
  ("a", |a, _| a),
  ("b", |_, b| b),
  ("a ^ b", |a, b| a ^ b),
  ("a & b", |a, b| a & b),
  ("a | b", |a, b| a | b),
  ("(a + b) & 255", |a, b| (a + b) & 255),
  ("(a + b) >> 8", |a, b| (a + b) >> 8),
  ("a.wrapping_sub(b) & 255", |a, b| a.wrapping_sub(b) & 255),
  ("u64::from(a < b)", |a, b| u64::from(a < b)),
  ("(a * b) & 255", |a, b| (a * b) & 255),
  ("(a * b) >> 8", |a, b| (a * b) >> 8),
  ("(a ^ b) >> 4", |a, b| (a ^ b) >> 4),
  ("((a ^ b) & 15) << 4", |a, b| ((a ^ b) & 15) << 4),
  ("(a ^ b) >> 7", |a, b| (a ^ b) >> 7),
  ("((a ^ b) & 127) << 1", |a, b| ((a ^ b) & 127) << 1),
  ("a & 255", |a, _| a & 255),
  ("a >> 8", |a, _| a >> 8),
  ("a & 1", |a, _| a & 1),
  ("(a >> 1) & 1", |a, _| (a >> 1) & 1),
  ("(a >> 2) & 1", |a, _| (a >> 2) & 1),
  ("(a >> 3) & 1", |a, _| (a >> 3) & 1),
  ("(a >> 4) & 1", |a, _| (a >> 4) & 1),
  ("(a >> 5) & 1", |a, _| (a >> 5) & 1),
  ("(a >> 6) & 1", |a, _| (a >> 6) & 1),
  ("(a >> 7) & 1", |a, _| (a >> 7) & 1),
];

fn closed_forms(program: &aiur::Program) -> Vec<Option<ClosedForm>> {
  program
    .maps
    .iter()
    .map(|map| {
      let inputs = &program.tables.get(map.input)?.rows;
      let outputs = &program.tables.get(map.output)?.rows;
      let width = inputs.first()?.len();
      if !(1..=2).contains(&width) || outputs.len() != inputs.len() {
        return None;
      }
      let radix: Vec<u64> = (0..width)
        .map(|c| inputs.iter().map(|r| r[c]).max().unwrap_or(0) + 1)
        .collect();
      let total = radix.iter().try_fold(1u64, |n, &d| n.checked_mul(d))?;
      if total != inputs.len() as u64 || radix.iter().any(|&d| d > 1 << 16) {
        return None;
      }
      for (i, row) in inputs.iter().enumerate() {
        let mut rest = i as u64;
        for c in (0..width).rev() {
          if row[c] != rest % radix[c] {
            return None;
          }
          rest /= radix[c];
        }
      }
      let columns = outputs.first().map_or(0, Vec::len);
      let mut forms = vec![];
      for c in 0..columns {
        let (name, _) = CANDIDATES.iter().find(|(_, f)| {
          inputs.iter().zip(outputs).all(|(input, output)| {
            output.len() == columns
              && f(input[0], input.get(1).copied().unwrap_or(0)) == output[c]
          })
        })?;
        forms.push(*name);
      }
      Some(ClosedForm { radix, outputs: forms })
    })
    .collect()
}

fn body(
  s: &mut String,
  plan: &NativePlan,
  closed: &[Option<ClosedForm>],
  id: usize,
  f: &NativeFunction,
) {
  let functions = plan.functions.len();
  let entries = &f.entries;
  let mut preds = vec![0usize; entries.len()];
  let mut targets = vec![false; entries.len()];
  for e in entries {
    if let Some(n) = e.next {
      preds[n] += 1;
    }
    match &e.op {
      NativeOp::Branch { target, .. } | NativeOp::Jump { target } => {
        preds[*target] += 1;
        targets[*target] = true;
      },
      _ => {},
    }
  }
  let leader = |i: usize| i == 0 || targets[i] || preds[i] != 1;
  let _ = writeln!(
    s,
    "#[inline(never)]\n\
     #[allow(non_snake_case, unused_mut, unused_variables, unused_assignments, \
     unreachable_code, clippy::all)]\n\
     fn f_{id}<B: FieldBackend>(rt: &mut Runtime<'_, B>, row: usize, a: [B::Element; {n}]) \
     -> Result<[B::Element; {m}], Failed> {{\n\
     let fd = rt.field();\n\
     let mut r = [fd.zero(); {regs}];\n\
     let mut ic: u64 = 0;",
    n = f.inputs,
    m = f.outputs,
    regs = f.registers.max(f.inputs)
  );
  for i in 0..f.inputs {
    let _ = writeln!(s, "r[{i}] = a[{i}];");
  }
  for (r, v) in &f.initial {
    let _ = writeln!(s, "r[{r}] = fd.from_u64({v});");
  }
  s.push_str("let mut s: usize = 0;\nloop {\nmatch s {\n");
  for start in (0..entries.len()).filter(|&i| leader(i)) {
    let _ = writeln!(s, "{start} => {{");
    let mut i = start;
    loop {
      let e = &entries[i];
      let pc = e.pc;
      let _ = writeln!(s, "ic += {};", e.instructions);
      let mut terminated = false;
      match &e.op {
        NativeOp::Literal { dest, value } => {
          let _ = writeln!(s, "r[{dest}] = fd.from_u64({value});");
        },
        NativeOp::Copy { dest, source } => {
          if let ([d], [src]) = (dest.as_slice(), source.as_slice()) {
            let _ = writeln!(s, "r[{d}] = r[{src}];");
          } else {
            let _ = writeln!(
              s,
              "{{ let t = [{}]; {} }}",
              regs(source),
              writes(dest, "t")
            );
          }
        },
        NativeOp::Neg { dest, source } => {
          let _ = writeln!(s, "r[{dest}] = fd.neg(r[{source}]);");
        },
        NativeOp::Binary { dest, operator, left, right } => {
          let _ = match operator {
            Binary::Add => {
              writeln!(s, "r[{dest}] = fd.add(r[{left}], r[{right}]);")
            },
            Binary::Sub => {
              writeln!(s, "r[{dest}] = fd.sub(r[{left}], r[{right}]);")
            },
            Binary::Mul => {
              writeln!(s, "r[{dest}] = fd.mul(r[{left}], r[{right}]);")
            },
            Binary::Div => writeln!(
              s,
              "r[{dest}] = rt.divide({id}, {pc}, r[{left}], r[{right}])?;"
            ),
          };
        },
        NativeOp::Guard { tests: t, message } => {
          if !t.is_empty() {
            let _ = writeln!(
              s,
              "if !({}) {{ return Err(rt.fail({id}, {pc}, {message:?})); }}",
              tests(t)
            );
          }
        },
        NativeOp::Branch { tests: t, target } => {
          let _ =
            writeln!(s, "if !({}) {{ s = {target}; continue; }}", tests(t));
        },
        NativeOp::Jump { target } => {
          let _ = writeln!(s, "s = {target}; continue;");
          terminated = true;
        },
        NativeOp::Call { function, args, dest } => {
          debug_assert!(*function < functions);
          let _ = writeln!(
            s,
            "{{ let o = c_{function}::<B>(rt, {id}, {pc}, [{}])?; {} }}",
            regs(args),
            writes(dest, "o")
          );
        },
        NativeOp::Map { function, args, dest }
          if closed[*function - functions].is_some() =>
        {
          let form = closed[*function - functions].as_ref().unwrap();
          let names = ["a", "b"];
          let mut code = String::from("{ ");
          for (name, arg) in names.iter().zip(args) {
            let _ = write!(code, "let {name} = fd.to_u64(r[{arg}]); ");
          }
          let bounds = names
            .iter()
            .zip(&form.radix)
            .map(|(n, d)| format!("{n} < {d}"))
            .collect::<Vec<_>>()
            .join(" && ");
          let row = names
            .iter()
            .zip(&form.radix)
            .skip(1)
            .fold(String::from("a"), |row, (n, d)| {
              format!("({row}) * {d} + {n}")
            });
          let _ = write!(
            code,
            "if {bounds} {{ rt.count_map({id}, {pc}, {function}, ({row}) as usize)?; "
          );
          if args.len() == 1 {
            code.push_str("let b = 0u64; ");
          }
          for (d, expr) in dest.iter().zip(&form.outputs) {
            let _ = write!(code, "r[{d}] = fd.from_u64({expr}); ");
          }
          let _ = write!(
            code,
            "}} else {{ let mut o = [fd.zero(); {}]; rt.map({id}, {pc}, {function}, &[{}], &mut o)?; {} }} }}",
            dest.len(),
            regs(args),
            writes(dest, "o")
          );
          let _ = writeln!(s, "{code}");
        },
        NativeOp::Map { function, args, dest } => {
          let _ = writeln!(
            s,
            "{{ let mut o = [fd.zero(); {}]; rt.map({id}, {pc}, {function}, &[{}], &mut o)?; {} }}",
            dest.len(),
            regs(args),
            writes(dest, "o")
          );
        },
        NativeOp::Store { value, dest } => {
          let _ = writeln!(
            s,
            "r[{dest}] = rt.store({id}, {pc}, &[{}])?;",
            regs(value)
          );
        },
        NativeOp::Load { pointer, dest } => {
          let _ = writeln!(
            s,
            "{{ let mut o = [fd.zero(); {}]; rt.load({id}, {pc}, r[{pointer}], &mut o)?; {} }}",
            dest.len(),
            writes(dest, "o")
          );
        },
        NativeOp::Hint { key, dest } => {
          let _ = writeln!(
            s,
            "{{ let mut o = [fd.zero(); {}]; rt.hint({id}, {pc}, &[{}], &mut o)?; {} }}",
            dest.len(),
            regs(key),
            writes(dest, "o")
          );
        },
        NativeOp::Assert { left, right, message } => {
          let differs = left
            .iter()
            .zip(right)
            .map(|(a, b)| format!("r[{a}] != r[{b}]"))
            .collect::<Vec<_>>()
            .join(" || ");
          if !differs.is_empty() {
            let _ = writeln!(
              s,
              "if {differs} {{ return Err(rt.fail({id}, {pc}, {message:?})); }}"
            );
          }
        },
        NativeOp::Nop => {},
        NativeOp::Return { values } => {
          let _ = writeln!(
            s,
            "{{ let o = [{}]; rt.count(ic)?; rt.finish({id}, row, {pc}, &o)?; return Ok(o); }}",
            regs(values)
          );
          terminated = true;
        },
        NativeOp::Fail { message } => {
          let _ = writeln!(s, "return Err(rt.fail({id}, {pc}, {message:?}));");
          terminated = true;
        },
      }
      if terminated {
        break;
      }
      match e.next {
        Some(n) if !leader(n) => i = n,
        Some(n) => {
          let _ = writeln!(s, "s = {n}; continue;");
          break;
        },
        None => {
          let _ = writeln!(
            s,
            "return Err(rt.fail({id}, {pc}, \"control reached the end of the function\"));"
          );
          break;
        },
      }
    }
    s.push_str("}\n");
  }
  s.push_str("_ => unreachable!(\"invalid block\"),\n}\n}\n}\n");
}
