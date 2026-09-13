use super::{ObjectLayout, bits::Synthesis};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{
    bits::{add, evaluate_words, fill_words},
    control::ControlCapacities,
    value::{BOOL_TAG, CTOR_TAG, ERASED_TAG},
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

#[derive(Clone, Debug)]
pub(crate) struct ObjectDispatchGate {
  nu: usize,
  pub(super) layout: ObjectLayout,
  control: ControlCapacities,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub(crate) struct ObjectDispatchRow(pub(super) Vec<F128>);
impl ObjectDispatchGate {
  pub(crate) fn new(
    nu: usize,
    layout: ObjectLayout,
    control: ControlCapacities,
  ) -> Self {
    Self { nu, layout, control, plan: Arc::new(OnceLock::new()) }
  }
  /// Frame, normalized fetched headers/callee/result/arguments.
  pub(crate) fn normalized_words(&self) -> usize {
    self.control.frame_words() + 5 + 2 * self.layout.fields
  }
  pub(crate) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub(crate) fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub(crate) fn generate_witness_into(
    &self,
    rows: &[ObjectDispatchRow],
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
#[cfg(test)]
impl ObjectDispatchRow {
  pub(crate) fn inputs(&self) -> &[F128] {
    &self.0
  }
}
impl CountedGate for ObjectDispatchGate {
  fn input_count(&self) -> usize {
    1 + self.normalized_words()
      + self.layout.program_words()
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
impl GateType for ObjectDispatchGate {
  type Row = ObjectDispatchRow;
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
    ObjectDispatchRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

fn build(gate: &ObjectDispatchGate) -> BooleanR1csPlan {
  let layout = gate.layout;
  let frame_words = gate.control.frame_words();
  let normal = gate.normalized_words();
  let mut s = Synthesis::new(
    gate.input_count(),
    gate.output_count(),
    32768
      + 1024
        * (normal
          + layout.entries() * layout.record_words()
          + gate.control.locals * layout.fields
          + layout.program_words()),
    layout,
  );
  let frame: Vec<_> = (128..128 * (1 + frame_words)).collect();
  let header = 128 * (1 + frame_words);
  let headers: Vec<_> = (header..header + 256).collect();
  let callee: Vec<_> = (header + 256..header + 384).collect();
  let primitive: Vec<_> = (header + 384..header + 640).collect();
  let args: Vec<_> = (header + 640..128 * (1 + normal)).collect();
  let declarations = 128 * (1 + normal);
  let arena = declarations + 128 * layout.program_words();
  let construct = s.eq_const(&headers[32..64], 7);
  let project = s.eq_const(&headers[32..64], 8);
  let case = s.eq_const(&headers[32..64], 9);
  let bind = s.sum(&[construct, project]);
  let object = s.sum(&[bind, case]);
  let ordinary = s.not(object);
  let erased_tag = s.eq_const(&args[..64], ERASED_TAG);
  let erased = s.and(project, erased_tag);
  let project_ctor = s.sum(&[project, erased]);
  let erased_value = s.mask(erased, &args[..256]);
  s.cell(erased, &erased_value);
  let read = s.sum(&[project_ctor, case]);
  let value = s.mask(read, &args[..256]);
  let record = s.record(&value, read, arena, declarations);
  let ctor_index = s.mask(construct, &headers[128..160]);
  let decl = s.declaration(&ctor_index, construct, declarations);
  let same = s.equal(&headers[192..224], &decl[384..416]);
  s.require(construct, same);
  let one_arg = s.eq_const(&headers[192..224], 1);
  let single = s.sum(&[project, case]);
  s.require(single, one_arg);
  s.require_zero(s.one, &(32..128).collect::<Vec<_>>());
  s.bounded_constant(&(0..32).collect::<Vec<_>>(), layout.entries() - 1, s.one);
  let input_limit = s.constant(32, layout.input_slots() as u64);
  let before_input = s.less(&(0..32).collect::<Vec<_>>(), &input_limit);
  let after_input = s.not(before_input);
  s.require(s.one, after_input);
  let fields = s.mask(construct, &headers[192..224]);
  let used = s.prefix(&fields, layout.fields);
  let mut allocation = vec![s.zero; 128 * layout.record_words()];
  allocation[..32].copy_from_slice(&ctor_index);
  allocation[32..64].copy_from_slice(&fields);
  allocation[64] = construct;
  for (index, enabled) in used.iter().enumerate() {
    let value = s.mask(construct, &args[256 * index..256 * (index + 1)]);
    let types = s.cell(*enabled, &value);
    // Runtime allocations may only point backward. Input trees are derived
    // recursively by their own decoder, so no cycle can enter the arena.
    let earlier = s.less(&value[128..160], &(0..32).collect::<Vec<_>>());
    s.require(types[6], earlier);
    allocation[128 + 256 * index..384 + 256 * index].copy_from_slice(&value);
  }
  let in_range = s.less(&headers[128..160], &record[32..64]);
  s.require(project_ctor, in_range);
  let projected: Vec<_> = (0..layout.fields)
    .map(|index| {
      let equal = s.eq_const(&headers[128..160], index as u64);
      (
        s.and(project_ctor, equal),
        &record[128 + 256 * index..384 + 256 * index],
      )
    })
    .collect();
  let projected = s.choose(&projected);
  let mut constructed = vec![s.zero; 256];
  constructed[..128].copy_from_slice(&s.constant(128, CTOR_TAG));
  constructed[128..160].copy_from_slice(&(0..32).collect::<Vec<_>>());
  let result = s.choose(&[
    (ordinary, &primitive),
    (construct, &constructed),
    (s.one, &projected),
    (s.one, &erased_value),
  ]);

  let mut case_sources = Vec::new();
  for function in 0..layout.functions {
    let matched = s.eq_const(&frame[..32], function as u64);
    let function = s.and(case, matched);
    for block in 0..layout.blocks {
      let matched = s.eq_const(&frame[32..64], block as u64);
      // The field named function above is a constrained flag, not an index.
      let selected = s.and(function, matched);
      case_sources.push(selected);
    }
  }
  let case_sources: Vec<_> = case_sources
    .into_iter()
    .enumerate()
    .map(|(index, flag)| {
      (
        flag,
        declarations
          + 128 * (layout.declaration_words() + index * layout.case_words()),
      )
    })
    .collect();
  let alternatives = s.select(&case_sources, 128 * layout.case_words());
  let live = s.prefix(&alternatives[..32], layout.capacity.constructors());
  let mut choices = Vec::new();
  for (index, enabled) in live.iter().enumerate() {
    let alt = &alternatives[128 * (1 + index)..128 * (2 + index)];
    let same = s.equal(&alt[..32], &record[..32]);
    let flag = s.and(*enabled, same);
    choices.push((flag, &alt[32..64]));
  }
  let found = s.sum(&choices.iter().map(|(flag, _)| *flag).collect::<Vec<_>>());
  s.require(case, found);
  let target = s.choose(&choices);
  let (length, carry) =
    add(&mut s.b, s.one, s.zero, &frame[64..96], &record[32..64]);
  let overflow = s.and(case, carry);
  s.violations.push(overflow);
  s.bounded_constant(&length, gate.control.locals, case);
  let not_case = s.not(case);
  let mut next_frame = frame.clone();
  let next_length = s.choose(&[(not_case, &frame[64..96]), (case, &length)]);
  next_frame[64..96].copy_from_slice(&next_length);
  let field_live = s.prefix(&record[32..64], layout.fields);
  for local in 0..gate.control.locals {
    let mut append = Vec::new();
    for (field, live) in field_live.iter().enumerate().take(local + 1) {
      let matched = s.eq_const(&frame[64..96], (local - field) as u64);
      let selected = s.and(case, *live);
      let selected = s.and(selected, matched);
      append.push((selected, &record[128 + 256 * field..384 + 256 * field]));
    }
    let added = s.choose(&append);
    for (bit, source) in added.into_iter().enumerate() {
      let position = 128 + 256 * local + bit;
      next_frame[position] = s.sum(&[next_frame[position], source]);
    }
  }
  let mut normalized_headers = s.mask(ordinary, &headers);
  let new_kind =
    s.choose(&[(bind, &s.constant(32, 2)), (case, &s.constant(32, 6))]);
  for bit in 0..32 {
    normalized_headers[bit] = headers[bit];
    normalized_headers[32 + bit] =
      s.sum(&[normalized_headers[32 + bit], new_kind[bit]]);
    let binding_target = s.and(bind, headers[64 + bit]);
    normalized_headers[64 + bit] =
      s.sum(&[normalized_headers[64 + bit], binding_target, target[bit]]);
    normalized_headers[96 + bit] =
      s.sum(&[normalized_headers[96 + bit], target[bit]]);
  }
  let mut boolean = vec![s.zero; args.len()];
  boolean[..128].copy_from_slice(&s.constant(128, BOOL_TAG));
  boolean[128] = s.one;
  let normalized_args = s.choose(&[(not_case, &args), (case, &boolean)]);
  let mut output = next_frame;
  output.extend(normalized_headers);
  output.extend(callee);
  output.extend(result);
  output.extend(normalized_args);
  output.extend(allocation);
  s.write(128 * gate.input_count(), &output);
  s.finish(128 * (gate.input_count() + gate.output_count() - 1))
}
