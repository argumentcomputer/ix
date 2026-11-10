//! CUDA source for compiled row writers.
//!
//! Each compiled circuit becomes one compilation unit with a kernel and an
//! `extern "C"` launcher. A kernel thread fills whole rows, exactly as the
//! interpreter's `populate_kernel` does: output row `r` is circuit row
//! `base + (first + r) % height`, left zero (the launcher clears the tile
//! first) at or beyond the record's real rows; otherwise the member owning that row is selected by
//! its `first` row and its function's straight-line body runs over its
//! recorded query. Slots are local variables; a guarded kernel defines its
//! slots as zero and assigns them only when its guard is one. Writes go
//! through the member's placement, followed by the selector, the group
//! writes in order and the multiplicity.
//!
//! The launcher's arguments are those of `aiur_gpu_populate` with the
//! interpreter's scratch replaced by the circuit's callee slots, and it
//! likewise resets `error`, copies it to the page-locked `status` and
//! synchronizes the calling thread's default stream. `callees[j]`
//! indexes `circuit->callees` for the `j`th name in
//! [`CompiledCircuit::callees`].
use crate::{ClosedForm, Described, closed::closed_forms, hints::WordHint};
use aiur::trace::{
  Polynomial,
  describe::{
    FunctionDescription, NodeDescription, Operand, PopulationDescription,
  },
};
use std::fmt::Write;

/// One compiled circuit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledCircuit {
  /// The physical circuit's name.
  pub name: String,
  /// Member function names, in row order.
  pub members: Vec<String>,
  /// Callee function names, in launcher slot order.
  pub callees: Vec<String>,
  /// The launcher's symbol.
  pub symbol: String,
  /// The unit's file name and source.
  pub file: String,
  pub source: String,
}

/// The circuits compiled from a description, and why the others were not.
#[derive(Clone, Debug, Default)]
pub struct Emitted {
  pub circuits: Vec<CompiledCircuit>,
  pub skipped: Vec<(String, String)>,
}

/// Which function circuits to compile.
#[derive(Clone, Debug)]
pub enum Selection {
  /// Every circuit that the emitter supports.
  All,
  /// These circuits by name; each must be supported.
  Named(Vec<String>),
}

/// Prepended to every launcher symbol.
pub const SYMBOL_PREFIX: &str = "aiur_tracegen";

/// Emits the selected circuits. `tag` distinguishes the launcher symbols of
/// bundles linked into one binary.
pub fn emit(
  described: &Described,
  selection: &Selection,
  tag: &str,
) -> Result<Emitted, String> {
  if !tag.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
    return Err("bundle tag must be an identifier".into());
  }
  let d = &described.description;
  if d.modulus != 0xffff_ffff_0000_0001 {
    return Err("compiled writers require the Goldilocks field".into());
  }
  let closed = closed_forms(&described.program);
  for (map, description) in d.maps.iter().enumerate() {
    if described.program.maps.get(map).map(|m| &m.name)
      != Some(&description.name)
    {
      return Err("map description does not match the program".into());
    }
  }
  if let Selection::Named(names) = selection {
    for name in names {
      if !d.circuits.iter().any(|c| &c.name == name) {
        return Err(format!("no function circuit named {name:?}"));
      }
    }
  }
  let mut emitted = Emitted::default();
  for (ci, circuit) in d.circuits.iter().enumerate() {
    let wanted = match selection {
      Selection::All => true,
      Selection::Named(names) => names.contains(&circuit.name),
    };
    if !wanted {
      continue;
    }
    let symbol = format!("{SYMBOL_PREFIX}_{tag}_{ci}");
    let unit = if described.depth.get(ci).copied().unwrap_or(false) {
      Err("fills depth columns (interpreted on the device)".to_owned())
    } else {
      Unit::circuit(d, &closed, ci, &symbol)
    };
    match unit {
      Ok(unit) => emitted.circuits.push(unit),
      Err(reason) => {
        if matches!(selection, Selection::Named(_)) {
          return Err(format!("{}: {reason}", circuit.name));
        }
        emitted.skipped.push((circuit.name.clone(), reason));
      },
    }
  }
  Ok(emitted)
}

const PRELUDE: &str = r#"#include <cuda_runtime.h>
#include <goldilocks.cuh>

#include <cstdint>

using namespace multi_stark_cuda;

// Layouts shared with `crates/aiur/src/trace/stark/gpu.rs` and
// `crates/aiur/cuda/population.cu` (compiled ABI version 3).
struct AiurFunction {
    const uint32_t* code;
    const uint64_t* constants;
    const uint64_t* rows;
    const uint64_t* multiplicities;
    const uint64_t* depths;
    uint64_t count;
    uint64_t first;
    uint32_t code_len;
    uint32_t scratch;
    uint32_t inputs;
    uint32_t outputs;
    uint32_t stride;
    uint32_t pad;
};
struct AiurCallee {
    const uint64_t* rows;
    const uint32_t* index;
    const uint64_t* multiplicities;
    const uint64_t* depths;
    uint64_t count;
    uint32_t mask;
    uint32_t inputs;
    uint32_t outputs;
    uint32_t stride;
};
struct AiurCircuit {
    const AiurFunction* members;
    const AiurCallee* callees;
    uint64_t real;
    uint32_t member_count;
    uint32_t width;
    uint32_t scratch;
    uint32_t pad;
};
struct AiurPopulationError {
    int32_t code;
    uint32_t op;
    uint64_t row;
};

namespace {

constexpr int32_t ERROR_ZERO_INVERSE = 1, ERROR_NO_ARM = 2, ERROR_NO_FAILURE = 3,
                  ERROR_MAP_DOMAIN = 4, ERROR_MISSING_CALLEE = 5, ERROR_HINT_DOMAIN = 6,
                  ERROR_ENCODING = 7;
constexpr unsigned BLOCK = 128;

__device__ __noinline__ void fail(AiurPopulationError* error, int32_t code, uint32_t op,
                                  uint64_t row) {
    if (atomicCAS(&error->code, 0, code) == 0) {
        error->op = op;
        error->row = row;
    }
}

__device__ __noinline__ uint64_t inverse(uint64_t value) {
    return goldilocks_pow(value, GOLDILOCKS_P - 2);
}

// The callee index hash of `population.cu`'s `index_kernel`.
__device__ __noinline__ int64_t find_query(const AiurCallee& callee, const uint64_t* key,
                                           uint32_t inputs) {
    if (inputs != callee.inputs) return -1;
    uint64_t h = 0x9e3779b97f4a7c15ULL ^ inputs;
    for (uint32_t i = 0; i < inputs; ++i) {
        h ^= key[i];
        h *= 0x100000001b3ULL;
        h ^= h >> 29;
    }
    h ^= h >> 32;
    h *= 0xd6e8feb86659fd93ULL;
    h ^= h >> 32;
    uint64_t slot = h & callee.mask;
    for (uint64_t probe = 0; probe <= callee.mask; ++probe) {
        const uint32_t entry = callee.index[slot];
        if (entry == 0) return -1;
        const uint64_t query = entry - 1;
        const uint64_t* stored = callee.rows + query * callee.stride;
        bool equal = true;
        for (uint32_t i = 0; i < inputs && equal; ++i) equal = stored[i] == key[i];
        if (equal) return int64_t(query);
        slot = (slot + 1) & callee.mask;
    }
    return -1;
}

"#;

struct Unit<'a> {
  d: &'a PopulationDescription,
  closed: &'a [Option<ClosedForm>],
  callees: Vec<String>,
  s: String,
}

fn operand(v: Operand) -> String {
  match v {
    Operand::Const(c) => format!("0x{c:x}ull"),
    Operand::Slot(i) => format!("s{i}"),
  }
}

fn polynomial(p: &Polynomial) -> String {
  match p {
    Polynomial::Const(c) => format!("0x{c:x}ull"),
    Polynomial::Var(v) => format!("row[{v}]"),
    Polynomial::Add(xs) => {
      format!("goldilocks_add({}, {})", polynomial(&xs[0]), polynomial(&xs[1]))
    },
    Polynomial::Sub(xs) => {
      format!("goldilocks_sub({}, {})", polynomial(&xs[0]), polynomial(&xs[1]))
    },
    Polynomial::Mul(xs) => {
      format!("goldilocks_mul({}, {})", polynomial(&xs[0]), polynomial(&xs[1]))
    },
  }
}

fn bounded(p: &Polynomial, width: usize, modulus: u64) -> bool {
  match p {
    Polynomial::Const(c) => *c < modulus,
    Polynomial::Var(v) => *v < width,
    Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) => {
      bounded(&xs[0], width, modulus) && bounded(&xs[1], width, modulus)
    },
  }
}

impl Unit<'_> {
  fn circuit(
    d: &PopulationDescription,
    closed: &[Option<ClosedForm>],
    ci: usize,
    symbol: &str,
  ) -> Result<CompiledCircuit, String> {
    let circuit = &d.circuits[ci];
    if circuit.members.is_empty() {
      return Err("no members".into());
    }
    let mut unit = Unit { d, closed, callees: vec![], s: String::new() };
    let width = circuit.width;
    for (m, member) in circuit.members.iter().enumerate() {
      let function = &d.functions[member.function];
      if member.columns.iter().any(|&c| c + 1 >= width)
        || member.selector + 1 >= width
        || member.writes.iter().any(|w| {
          w.column + 1 >= width || !bounded(&w.value, width, d.modulus)
        })
      {
        return Err("placement outside the circuit".into());
      }
      unit.function(m, function, member, width)?;
    }
    let mut s = String::new();
    let _ = writeln!(
      s,
      "// Generated by aiur-tracegen for circuit {:?}. Do not edit.",
      circuit.name
    );
    s.push_str(PRELUDE);
    let callees = unit.callees.len().max(1);
    let _ = writeln!(s, "struct Slots {{ uint32_t v[{callees}]; }};\n");
    s.push_str(&unit.s);
    let _ = writeln!(
      s,
      "__global__ void __launch_bounds__(BLOCK) circuit_kernel(AiurCircuit circuit, Slots slots,\n\
       uint64_t* output, uint64_t base, uint64_t first, uint64_t rows, uint64_t height,\n\
       AiurPopulationError* error) {{\n\
       const uint64_t threads = uint64_t(gridDim.x) * blockDim.x;\n\
       for (uint64_t r = uint64_t(blockIdx.x) * blockDim.x + threadIdx.x; r < rows; r += threads) {{\n\
       uint64_t* row = output + r * {width}u;\n\
       const uint64_t index = base + (first + r) % height;\n\
       if (index >= circuit.real) continue;\n\
       uint32_t member = 0;\n\
       while (member + 1 < circuit.member_count && circuit.members[member + 1].first <= index) ++member;\n\
       const AiurFunction& f = circuit.members[member];\n\
       switch (member) {{"
    );
    for m in 0..circuit.members.len() {
      let _ = writeln!(
        s,
        "case {m}: fill_{m}(f, circuit.callees, slots, index - f.first, index, row, error); break;"
      );
    }
    let _ = writeln!(
      s,
      "default: fail(error, ERROR_ENCODING, 0, index); break;\n}}\n}}\n}}\n\n}}  // namespace\n"
    );
    let _ = writeln!(
      s,
      "extern \"C\" int {symbol}(int device, const AiurCircuit* circuit, const uint32_t* callees,\n\
       uint32_t callee_count, uint64_t* output, uint64_t base, uint64_t first, uint64_t rows,\n\
       uint64_t height, AiurPopulationError* error, AiurPopulationError* status) {{\n\
       *status = AiurPopulationError{{}};\n\
       if (callee_count != {count}u || circuit->width != {width}u\n\
           || circuit->member_count != {members}u || height == 0)\n\
           return int(cudaErrorInvalidValue);\n\
       cudaError_t result = cudaSetDevice(device);\n\
       if (result != cudaSuccess || rows == 0) return int(result);\n\
       const cudaStream_t stream = cudaStreamPerThread;\n\
       result = cudaMemsetAsync(output, 0, rows * {width}u * sizeof(uint64_t), stream);\n\
       if (result != cudaSuccess) return int(result);\n\
       result = cudaMemsetAsync(error, 0, sizeof(AiurPopulationError), stream);\n\
       if (result != cudaSuccess) return int(result);\n\
       Slots slots{{}};\n\
       for (uint32_t i = 0; i < callee_count; ++i) slots.v[i] = callees[i];\n\
       const uint64_t wanted = (rows + BLOCK - 1) / BLOCK;\n\
       const unsigned blocks = unsigned(wanted < 65536 ? wanted : 65536);\n\
       circuit_kernel<<<blocks, BLOCK, 0, stream>>>(*circuit, slots, output, base, first, rows,\n\
                                                    height, error);\n\
       result = cudaGetLastError();\n\
       if (result != cudaSuccess) return int(result);\n\
       result = cudaMemcpyAsync(status, error, sizeof(AiurPopulationError),\n\
                                cudaMemcpyDeviceToHost, stream);\n\
       if (result != cudaSuccess) return int(result);\n\
       return int(cudaStreamSynchronize(stream));\n\
       }}",
      count = unit.callees.len(),
      members = circuit.members.len(),
    );
    Ok(CompiledCircuit {
      name: circuit.name.clone(),
      members: circuit
        .members
        .iter()
        .map(|m| d.functions[m.function].name.clone())
        .collect(),
      callees: unit.callees,
      symbol: symbol.to_owned(),
      file: format!("{symbol}.cu"),
      source: s,
    })
  }

  fn callee_slot(&mut self, name: &str) -> usize {
    if let Some(i) = self.callees.iter().position(|c| c == name) {
      return i;
    }
    self.callees.push(name.to_owned());
    self.callees.len() - 1
  }

  /// `fill_{m}`: one member's row. Kernel indices in errors are the
  /// function's kernel positions, as in the interpreter.
  fn function(
    &mut self,
    m: usize,
    f: &FunctionDescription,
    member: &aiur::trace::describe::MemberDescription,
    width: usize,
  ) -> Result<(), String> {
    let mut b = String::new();
    let _ = writeln!(
      b,
      "// {}\n__device__ __noinline__ void fill_{m}(const AiurFunction& f, const AiurCallee* callees,\n\
       const Slots& slots, uint64_t query, uint64_t row_index, uint64_t* __restrict__ row,\n\
       AiurPopulationError* error) {{\n\
       const uint64_t* __restrict__ recorded = f.rows + query * f.stride;",
      f.name.replace('\n', " ")
    );
    for i in 0..f.inputs + f.outputs {
      let _ = writeln!(b, "const uint64_t s{i} = recorded[{i}];");
    }
    // Each column write is emitted as soon as its guard and value exist,
    // after any earlier write to the same column, so values need not stay
    // live until the end of the body. Writes to distinct columns commute.
    let mut defined = vec![None; f.slots];
    for (k, kernel) in f.kernels.iter().enumerate() {
      for slot in &mut defined[kernel.start..kernel.start + kernel.width] {
        *slot = Some(k);
      }
    }
    let ready = |v: Operand| match v {
      Operand::Slot(i) => defined.get(i).copied().flatten(),
      Operand::Const(_) => None,
    };
    let mut after: Vec<Vec<usize>> = vec![vec![]; f.kernels.len() + 1];
    let mut last: std::collections::HashMap<usize, Option<usize>> =
      Default::default();
    for (i, w) in f.writes.iter().enumerate() {
      let mut at = ready(w.guard).max(ready(w.value));
      if let Some(&previous) = last.get(&w.column) {
        at = at.max(previous);
      }
      last.insert(w.column, at);
      after[at.map_or(0, |k| k + 1)].push(i);
    }
    let emit_writes = |b: &mut String, list: &[usize]| -> Result<(), String> {
      for &i in list {
        let w = &f.writes[i];
        let column =
          *member.columns.get(w.column).ok_or("write outside the placement")?;
        match w.guard {
          Operand::Const(1) => {
            let _ = writeln!(b, "row[{column}] = {};", operand(w.value));
          },
          Operand::Const(_) => {},
          guard => {
            let _ = writeln!(
              b,
              "if ({} == 1u) row[{column}] = {};",
              operand(guard),
              operand(w.value)
            );
          },
        }
      }
      Ok(())
    };
    emit_writes(&mut b, &after[0])?;
    for (k, kernel) in f.kernels.iter().enumerate() {
      let slots: Vec<String> = (kernel.start..kernel.start + kernel.width)
        .map(|i| format!("s{i}"))
        .collect();
      let fail =
        |code: &str| format!("fail(error, {code}, {k}u, row_index); return;");
      for slot in &slots {
        let _ = writeln!(b, "uint64_t {slot} = 0;");
      }
      let mut body = String::new();
      match &kernel.node {
        NodeDescription::Add { a, b: y } => {
          let _ = writeln!(
            body,
            "{} = goldilocks_add({}, {});",
            slots[0],
            operand(*a),
            operand(*y)
          );
        },
        NodeDescription::Sub { a, b: y } => {
          let _ = writeln!(
            body,
            "{} = goldilocks_sub({}, {});",
            slots[0],
            operand(*a),
            operand(*y)
          );
        },
        NodeDescription::Mul { a, b: y } => {
          let _ = writeln!(
            body,
            "{} = goldilocks_mul({}, {});",
            slots[0],
            operand(*a),
            operand(*y)
          );
        },
        NodeDescription::Select { guard, a, b: y } => {
          let _ = writeln!(
            body,
            "{} = {} == 1u ? {} : {};",
            slots[0],
            operand(*guard),
            operand(*a),
            operand(*y)
          );
        },
        NodeDescription::Inverse { value } => {
          let v = operand(*value);
          let _ = writeln!(
            body,
            "if ({v} == 0u) {{ {} }}\n{} = inverse({v});",
            fail("ERROR_ZERO_INVERSE"),
            slots[0]
          );
        },
        NodeDescription::Choice { tests } => {
          if tests.len() != kernel.width {
            return Err("choice shape mismatch".into());
          }
          for (t, test) in tests.iter().enumerate() {
            let condition = if test.is_empty() {
              "true".to_owned()
            } else {
              test
                .iter()
                .map(|v| format!("{} == 0u", operand(*v)))
                .collect::<Vec<_>>()
                .join(" && ")
            };
            let keyword = if t == 0 { "if" } else { "else if" };
            let _ =
              writeln!(body, "{keyword} ({condition}) {} = 1u;", slots[t]);
          }
          let _ = writeln!(body, "else {{ {} }}", fail("ERROR_NO_ARM"));
        },
        NodeDescription::Failure { differences } => {
          if differences.len() != kernel.width {
            return Err("failure shape mismatch".into());
          }
          for (i, v) in differences.iter().enumerate() {
            let v = operand(*v);
            let keyword = if i == 0 { "if" } else { "else if" };
            let _ = writeln!(
              body,
              "{keyword} ({v} != 0u) {} = inverse({v});",
              slots[i]
            );
          }
          let _ = writeln!(body, "else {{ {} }}", fail("ERROR_NO_FAILURE"));
        },
        NodeDescription::Call { callee, args } => {
          let slot = self.callee_slot(callee);
          let key: Vec<String> = args.iter().map(|v| operand(*v)).collect();
          let _ = writeln!(
            body,
            "const uint64_t key[{n}] = {{{keys}}};\n\
             const AiurCallee& callee = callees[slots.v[{slot}]];\n\
             const int64_t found = find_query(callee, key, {inputs}u);\n\
             if (found < 0 || callee.outputs != {width}u) {{ {missing} }}\n\
             const uint64_t* values = callee.rows + uint64_t(found) * callee.stride + callee.inputs;",
            n = key.len().max(1),
            keys = if key.is_empty() { "0".to_owned() } else { key.join(", ") },
            inputs = key.len(),
            width = kernel.width,
            missing = fail("ERROR_MISSING_CALLEE"),
          );
          for (i, slot) in slots.iter().enumerate() {
            let _ = writeln!(body, "{slot} = values[{i}];");
          }
        },
        NodeDescription::Map { map, args } => {
          let description = self.d.maps.get(*map).ok_or("unknown map")?;
          let form = self
            .closed
            .get(*map)
            .and_then(Option::as_ref)
            .ok_or_else(|| {
              format!("map {:?} has no verified closed form", description.name)
            })?;
          if args.len() != form.radix.len()
            || kernel.width != form.outputs.len()
          {
            return Err(format!("map {:?} shape mismatch", description.name));
          }
          let a = operand(args[0]);
          let y =
            args.get(1).map_or_else(|| "0ull".to_owned(), |v| operand(*v));
          let domain: Vec<String> = args
            .iter()
            .zip(&form.radix)
            .map(|(v, r)| format!("{} < {r}u", operand(*v)))
            .collect();
          let _ = writeln!(
            body,
            "if (!({})) {{ {} }}\nconst uint64_t a = {a}, b = {y};\n(void)a; (void)b;",
            domain.join(" && "),
            fail("ERROR_MAP_DOMAIN")
          );
          for (slot, expression) in slots.iter().zip(&form.outputs) {
            let _ = writeln!(body, "{slot} = {expression};");
          }
        },
        NodeDescription::Hint { site, key } => {
          let hint = WordHint::of(site).ok_or_else(|| {
            format!(
              "hint channel {:?} is outside the word hint contract",
              site.channel
            )
          })?;
          if key.len() != hint.key_width()
            || kernel.width != hint.output_width()
          {
            return Err(format!("hint {:?} shape mismatch", site.channel));
          }
          let key: Vec<String> = key.iter().map(|v| operand(*v)).collect();
          hint.emit(&key, &slots, &mut body, &fail("ERROR_HINT_DOMAIN"));
        },
        NodeDescription::Store { .. } => {
          return Err("reads the ROM (store)".into());
        },
        NodeDescription::Load { .. } => {
          return Err("reads the ROM (load)".into());
        },
      }
      match kernel.guard {
        Operand::Const(1) => {
          let _ = writeln!(b, "{{\n{body}}}");
        },
        Operand::Const(_) => {},
        guard => {
          let _ = writeln!(b, "if ({} == 1u) {{\n{body}}}", operand(guard));
        },
      }
      emit_writes(&mut b, &after[k + 1])?;
    }
    let _ = writeln!(b, "row[{}] = 1u;", member.selector);
    for w in &member.writes {
      let _ = writeln!(b, "row[{}] = {};", w.column, polynomial(&w.value));
    }
    let _ = writeln!(b, "row[{}] = f.multiplicities[query];\n}}\n", width - 1);
    self.s.push_str(&b);
    Ok(())
  }
}
