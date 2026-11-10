//! Arithmetic replacements for fixed-table maps.
//!
//! As in the native executor generator (`aiur-codegen`), a map has a closed
//! form when its input table lists every argument tuple exactly once in
//! mixed-radix order (first argument most significant) and each output column
//! equals one candidate expression on every row. Agreement is checked
//! exhaustively against the actual tables, never inferred from a map's name.
//! Arguments outside the radix have no table row and remain errors.
use aiur::Program;

/// A verified closed form: per-argument exclusive bounds and one CUDA
/// expression over `a` and `b` per output column.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosedForm {
  pub radix: Vec<u64>,
  pub outputs: Vec<&'static str>,
}

type Candidate = (&'static str, fn(u64, u64) -> u64);

/// CUDA expressions over the `uint64_t` arguments `a` and `b` (`b` is 0
/// for unary maps), with their host meaning.
const CANDIDATES: &[Candidate] = &[
  ("a", |a, _| a),
  ("b", |_, b| b),
  ("a ^ b", |a, b| a ^ b),
  ("a & b", |a, b| a & b),
  ("a | b", |a, b| a | b),
  ("(a + b) & 255", |a, b| (a + b) & 255),
  ("(a + b) >> 8", |a, b| (a + b) >> 8),
  ("(a - b) & 255", |a, b| a.wrapping_sub(b) & 255),
  ("(uint64_t)(a < b)", |a, b| u64::from(a < b)),
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

/// The closed form of each map of `program`, by map index.
pub(crate) fn closed_forms(program: &Program) -> Vec<Option<ClosedForm>> {
  program.maps.iter().map(|map| closed_form(program, map)).collect()
}

fn closed_form(
  program: &Program,
  map: &aiur::bytecode::Map,
) -> Option<ClosedForm> {
  let inputs = &program.tables.get(map.input)?.rows;
  let outputs = &program.tables.get(map.output)?.rows;
  let width = inputs.first()?.len();
  if !(1..=2).contains(&width) || outputs.len() != inputs.len() {
    return None;
  }
  let radix: Vec<u64> = (0..width)
    .map(|c| {
      inputs
        .iter()
        .map(|r| r.get(c).copied().unwrap_or(u64::MAX))
        .max()
        .unwrap_or(0)
        + 1
    })
    .collect();
  let total = radix.iter().try_fold(1u64, |n, &d| n.checked_mul(d))?;
  if total != inputs.len() as u64 || radix.iter().any(|&d| d > 1 << 16) {
    return None;
  }
  for (i, row) in inputs.iter().enumerate() {
    if row.len() != width {
      return None;
    }
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
    let (expression, _) = CANDIDATES.iter().find(|(_, f)| {
      inputs.iter().zip(outputs).all(|(input, output)| {
        output.len() == columns
          && f(input[0], input.get(1).copied().unwrap_or(0)) == output[c]
      })
    })?;
    forms.push(*expression);
  }
  Some(ClosedForm { radix, outputs: forms })
}

#[cfg(test)]
mod tests {
  use super::*;

  #[allow(clippy::needless_pass_by_value)]
  fn program(maps: serde_json::Value, tables: serde_json::Value) -> Program {
    serde_json::from_value(serde_json::json!({
      "version":1,"modulus":18446744069414584321u64,"enums":[],"functions":[],
      "entries":[],"maps":maps,"tables":tables
    }))
    .unwrap()
  }

  #[test]
  fn derives_forms_only_from_complete_tables() {
    let f = serde_json::json!({"kind":"field"});
    let pair = serde_json::json!({"kind":"tuple","items":[f, f]});
    let inputs: Vec<_> =
      (0..16u64).flat_map(|a| (0..16u64).map(move |b| vec![a, b])).collect();
    let xor: Vec<_> = inputs
      .iter()
      .map(|r| vec![r[0] ^ r[1], u64::from(r[0] < r[1])])
      .collect();
    let mut wrong = xor.clone();
    wrong[17][0] += 1;
    let map = |output: usize| serde_json::json!({"name":"m","params":[f, f],"result":pair,"input":0,"output":output});
    let tables = serde_json::json!([
      {"name":"in","type":pair,"rows":inputs},
      {"name":"xor","type":pair,"rows":xor},
      {"name":"wrong","type":pair,"rows":wrong},
      {"name":"partial","type":pair,"rows":inputs[..255].to_vec()},
    ]);
    let complete = program(serde_json::json!([map(1), map(2)]), tables.clone());
    let forms = closed_forms(&complete);
    assert_eq!(
      forms[0],
      Some(ClosedForm {
        radix: vec![16, 16],
        outputs: vec!["a ^ b", "(uint64_t)(a < b)"]
      })
    );
    assert_eq!(forms[1], None);
    let partial = program(
      serde_json::json!([{"name":"m","params":[f, f],"result":pair,"input":3,"output":1}]),
      tables,
    );
    assert_eq!(closed_forms(&partial)[0], None);
  }
}
