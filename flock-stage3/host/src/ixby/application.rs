//! Immutable PAP creation and bounded application resolution. All function
//! headers and arena entries are circuit wires from authenticated producers.
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{
    bits::{add, evaluate_words, fill_words, subtract},
    control::ControlCapacities,
    object_value::{ObjectLayout, bits::Synthesis},
    value::{ERASED_TAG, PAP_TAG},
  },
  sizing::CountedGate,
};
use flock_prover::{
  circuit::builder::{GateType, SlotWitness},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

#[cfg(test)]
#[path = "application_tests.rs"]
mod tests;

#[derive(Clone, Debug)]
pub(crate) struct PapDispatchGate {
  nu: usize,
  pub layout: ObjectLayout,
  control: ControlCapacities,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub(crate) struct PapDispatchRow(pub Vec<F128>);

impl PapDispatchGate {
  pub(crate) fn new(
    nu: usize,
    layout: ObjectLayout,
    control: ControlCapacities,
  ) -> Self {
    assert!(layout.applications && layout.fields == control.arguments);
    Self { nu, layout, control, plan: Arc::new(OnceLock::new()) }
  }
  pub(crate) fn normalized_words(&self) -> usize {
    5 + 2 * self.layout.operand_slots() + 1 + 2 * self.layout.fields
  }
  pub(crate) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub(crate) fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub(crate) fn generate_witness_into(
    &self,
    rows: &[PapDispatchRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| fill_words(&row.0, bits),
    )
  }
}
impl CountedGate for PapDispatchGate {
  fn input_count(&self) -> usize {
    1 + self.control.state_words()
      + 5
      + 2 * self.layout.operand_slots()
      + 1
      + self.layout.functions
      + self.layout.entries() * self.layout.record_words()
  }
  fn output_count(&self) -> usize {
    self.normalized_words() + self.layout.record_words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for PapDispatchGate {
  type Row = PapDispatchRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let mut schema: Vec<_> =
      (0..self.input_count()).map(IoWord::input).collect();
    schema.extend(
      (self.input_count()..self.input_count() + self.output_count())
        .map(IoWord::output),
    );
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.input_count());
    output.extend(evaluate_words(self.plan(), input, self.output_count()));
    PapDispatchRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn build(gate: &PapDispatchGate) -> BooleanR1csPlan {
  let l = gate.layout;
  let a = l.fields;
  let w = 128 * l.record_words();
  let mut s = Synthesis::new(
    gate.input_count(),
    gate.output_count(),
    65536 + 2048 * (gate.input_count() + a * a + gate.control.locals),
    l,
  );
  let allocation: Vec<_> = (0..32).collect();
  s.require_zero(s.one, &(32..128).collect::<Vec<_>>());
  s.bounded_constant(&allocation, l.entries() - 1, s.one);
  let first = s.constant(32, l.input_slots() as u64);
  let before = s.less(&allocation, &first);
  s.violations.push(before);
  let state: Vec<_> = (128..128 * (1 + gate.control.state_words())).collect();
  let base = 128 * (1 + gate.control.state_words());
  let headers: Vec<_> = (base..base + 256).collect();
  let callee: Vec<_> = (base + 256..base + 384).collect();
  let primitive: Vec<_> = (base + 384..base + 640).collect();
  let args: Vec<_> =
    (base + 640..base + 640 + 256 * l.operand_slots()).collect();
  let functions = base + 640 + args.len();
  let arena = functions + 128 * (1 + l.functions);
  let applying = s.eq_const(&state[..32], 3);
  let eval = s.eq_const(&state[..32], 0);
  let closure = s.eq_const(&headers[32..64], 11);
  s.require(closure, eval);
  let function_base = 128 * (1 + gate.control.frame_words());
  let function = s.mask(applying, &state[function_base..function_base + 256]);
  let flags = s.cell(applying, &function);
  let pap_value = s.mask(flags[8], &function);
  let (record, pap_function) =
    s.pap_record(&pap_value, flags[8], arena, functions);
  let arg_count = s.mask(applying, &state[192..224]);
  let arg_live = s.prefix(&arg_count, a);
  let empty = s.eq_const(&arg_count, 0);
  let identity = s.and(applying, empty);
  let nonempty = s.not(empty);
  let pap_apply = s.and(flags[8], nonempty);
  let erased = s.and(flags[4], nonempty);
  let callable = s.sum(&[flags[4], flags[8]]);
  let noncallable = s.not(callable);
  let bad = s.and(applying, nonempty);
  let bad = s.and(bad, noncallable);
  s.violations.push(bad);
  for (index, enabled) in arg_live.into_iter().enumerate() {
    let value = s.mask(applying, &state[256 + 256 * index..512 + 256 * index]);
    s.cell(enabled, &value);
  }
  let (total, carry) =
    add(&mut s.b, s.one, s.zero, &record[32..64], &arg_count);
  s.violations.push(carry);
  s.bounded_constant(&total, 2 * a, s.one);
  let short = s.less(&total, &pap_function[..32]);
  let under = s.and(pap_apply, short);
  let saturated = s.not(short);
  let entering = s.and(pap_apply, saturated);
  let (rest, borrow) =
    subtract(&mut s.b, s.one, s.zero, &total, &pap_function[..32]);
  let bad = s.and(entering, borrow);
  s.violations.push(bad);
  let rest = s.mask(entering, &rest);
  let rest_live = s.prefix(&rest, a);

  let mut combined = Vec::new();
  for index in 0..2 * a {
    let mut sources = Vec::new();
    if index < a {
      sources.push((s.one, &record[128 + 256 * index..384 + 256 * index]));
    }
    for arg in 0..a.min(index + 1) {
      let at = s.eq_const(&record[32..64], (index - arg) as u64);
      let selected = s.and(pap_apply, at);
      sources.push((selected, &state[256 + 256 * arg..512 + 256 * arg]));
    }
    combined.extend(s.choose(&sources));
  }
  let closure_index = s.mask(closure, &headers[128..160]);
  let closure_function = s.function(&closure_index, closure, functions);
  let closure_count = s.mask(closure, &headers[192..224]);
  let fits = s.less(&closure_count, &closure_function[..32]);
  s.require(closure, fits);
  let stored = s.sum(&[closure, under]);
  let fields = s.choose(&[(s.one, &closure_count), (under, &total)]);
  let live = s.prefix(&fields, a);
  let index = s.choose(&[(s.one, &closure_index), (under, &record[..32])]);
  let mut allocated = vec![s.zero; w];
  allocated[..32].copy_from_slice(&index);
  allocated[32..64].copy_from_slice(&fields);
  allocated[64] = stored;
  allocated[65] = stored;
  for (index, enabled) in live.into_iter().enumerate() {
    let value = s.choose(&[
      (closure, &args[256 * index..256 * (index + 1)]),
      (under, &combined[256 * index..256 * (index + 1)]),
    ]);
    let types = s.cell(enabled, &value);
    let earlier = s.less(&value[128..160], &allocation);
    s.require(types[6], earlier);
    s.require(types[8], earlier);
    allocated[128 + 256 * index..384 + 256 * index].copy_from_slice(&value);
  }
  let mut pap = s.constant(128, PAP_TAG);
  let mut handle = allocation.clone();
  handle.resize(128, s.zero);
  pap.extend(handle);
  let erased_value = {
    let mut value = s.constant(128, ERASED_TAG);
    value.resize(256, s.zero);
    value
  };
  let returning = s.sum(&[identity, erased, under]);
  let handled = s.sum(&[closure, applying]);
  let ordinary = s.not(handled);
  let mut normalized_headers = s.mask(ordinary, &headers);
  let kind = s.choose(&[
    (closure, &s.constant(32, 2)),
    (returning, &s.constant(32, 14)),
    (entering, &s.constant(32, 15)),
  ]);
  for bit in 0..32 {
    let local = s.and(closure, headers[bit]);
    normalized_headers[bit] = s.sum(&[normalized_headers[bit], local]);
    normalized_headers[32 + bit] =
      s.sum(&[normalized_headers[32 + bit], kind[bit]]);
    let target = s.and(closure, headers[64 + bit]);
    normalized_headers[64 + bit] =
      s.sum(&[normalized_headers[64 + bit], target]);
    let callee = s.and(entering, record[bit]);
    normalized_headers[128 + bit] =
      s.sum(&[normalized_headers[128 + bit], callee]);
    let count = s.and(entering, pap_function[bit]);
    normalized_headers[192 + bit] =
      s.sum(&[normalized_headers[192 + bit], count]);
  }
  let normalized_callee =
    s.choose(&[(ordinary, &callee), (entering, &pap_function)]);
  let normalized_result = s.choose(&[
    (ordinary, &primitive),
    (stored, &pap),
    (identity, &function),
    (erased, &erased_value),
  ]);
  let call_count = s.mask(entering, &pap_function[..32]);
  let call_live = s.prefix(&call_count, a);
  let mut normalized_args = s.mask(ordinary, &args);
  for (index, enabled) in call_live.into_iter().enumerate() {
    for bit in 0..256 {
      let value = s.and(enabled, combined[256 * index + bit]);
      let position = 256 * index + bit;
      normalized_args[position] = s.sum(&[normalized_args[position], value]);
    }
  }
  let mut output = normalized_headers;
  output.extend(normalized_callee);
  output.extend(normalized_result);
  output.extend(normalized_args);
  let mut rest_word = rest;
  rest_word.resize(128, s.zero);
  output.extend(rest_word);
  for (index, enabled) in rest_live.into_iter().enumerate() {
    let sources: Vec<_> = (0..=a)
      .map(|arity| {
        let at = s.eq_const(&pap_function[..32], arity as u64);
        (
          s.and(enabled, at),
          &combined[256 * (arity + index)..256 * (arity + index + 1)],
        )
      })
      .collect();
    output.extend(s.choose(&sources));
  }
  let keep = s.not(stored);
  let sources: Vec<_> = (0..l.entries())
    .map(|index| {
      let at = s.eq_const(&allocation, index as u64);
      (s.and(keep, at), arena + w * index)
    })
    .collect();
  let previous = s.select(&sources, w);
  output.extend(s.choose(&[(s.one, &allocated), (s.one, &previous)]));
  s.write(128 * gate.input_count(), &output);
  s.finish(128 * (gate.input_count() + gate.output_count() - 1))
}
