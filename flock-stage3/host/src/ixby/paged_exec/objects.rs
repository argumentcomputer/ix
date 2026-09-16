//! Instruction-derived immutable vectors and application microcontinuations.
//! A reservation exposes no result until every copied field has been checked.
use super::*;
use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::{
    bits,
    paged_frame::{ActionKind, HEAP, Phase, SCRATCH},
    paged_value,
  },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectKind {
  Reference,
  Construct,
  Closure,
  OperandRequest,
  ApplyInstruction,
  ProjectRequest,
  ProjectAction,
  CaseAction,
  ApplyRequest,
  ApplyStart,
  StoreRequest,
  StoreCopy,
  StoreFinish,
}
impl ObjectKind {
  pub(super) fn extra_inputs(self) -> usize {
    match self {
      Self::Construct
      | Self::Closure
      | Self::ApplyInstruction
      | Self::ProjectRequest
      | Self::ApplyStart
      | Self::StoreCopy => 2,
      Self::ProjectAction | Self::CaseAction => 4,
      _ => 0,
    }
  }
  pub(super) fn outputs(self) -> usize {
    match self {
      Self::Reference | Self::ProjectRequest | Self::StoreRequest => 1,
      Self::OperandRequest | Self::ApplyRequest => 2,
      Self::Construct
      | Self::Closure
      | Self::ApplyInstruction
      | Self::ApplyStart => STATE_WORDS,
      Self::ProjectAction | Self::CaseAction | Self::StoreFinish => 5,
      Self::StoreCopy => STATE_WORDS + 8,
    }
  }
}
pub(super) type Bits = Vec<usize>;
fn word(at: usize) -> Bits {
  (128 * at..128 * (at + 1)).collect()
}
pub(super) struct S {
  pub(super) b: BooleanR1csBuilder,
  pub(super) one: usize,
  pub(super) zero: usize,
  pub(super) bad: Bits,
}
impl S {
  pub(super) fn c(&self, n: usize, v: u64) -> Bits {
    (0..n)
      .map(|i| if i < 64 && v & (1 << i) != 0 { self.one } else { self.zero })
      .collect()
  }
  pub(super) fn wide(&self, a: &[usize], n: usize) -> Bits {
    let mut a = a.to_vec();
    a.resize(n, self.zero);
    a
  }
  pub(super) fn eqc(&mut self, a: &[usize], v: u64) -> usize {
    let low =
      bits::equal_constant(&mut self.b, self.one, &a[..64.min(a.len())], v);
    if a.len() <= 64 {
      return low;
    }
    let high = bits::equal_constant(&mut self.b, self.one, &a[64..], 0);
    self.and(low, high)
  }
  pub(super) fn eq(&mut self, a: &[usize], b: &[usize]) -> usize {
    bits::equal(&mut self.b, self.one, a, b)
  }
  pub(super) fn and(&mut self, a: usize, b: usize) -> usize {
    self.b.and(a, b)
  }
  pub(super) fn inv(&mut self, a: usize) -> usize {
    bits::not(&mut self.b, self.one, a)
  }
  pub(super) fn any(&mut self, a: &[usize]) -> usize {
    bits::any(&mut self.b, self.one, a)
  }
  pub(super) fn need(&mut self, f: usize, good: usize) {
    bits::require(&mut self.b, self.one, &mut self.bad, f, good);
  }
  pub(super) fn zeros(&mut self, f: usize, a: &[usize]) {
    bits::require_zero(&mut self.b, self.one, &mut self.bad, f, a);
  }
  pub(super) fn same(&mut self, f: usize, a: &[usize], b: &[usize]) {
    let good = self.eq(a, b);
    self.need(f, good);
  }
  pub(super) fn is(&mut self, f: usize, a: &[usize], v: u64) {
    let good = self.eqc(a, v);
    self.need(f, good);
  }
  pub(super) fn mask(&mut self, f: usize, a: &[usize]) -> Bits {
    a.iter().map(|&x| self.and(f, x)).collect()
  }
  pub(super) fn choose(&mut self, f: usize, a: &[usize], b: &[usize]) -> Bits {
    assert_eq!(a.len(), b.len());
    let no = self.inv(f);
    a.iter()
      .zip(b)
      .map(|(&a, &b)| {
        let a = self.and(f, a);
        let b = self.and(no, b);
        self.b.xor(&[a, b], self.one)
      })
      .collect()
  }
  pub(super) fn add(&mut self, a: &[usize], b: &[usize]) -> Bits {
    bits::add(&mut self.b, self.one, self.zero, a, b).0
  }
  pub(super) fn sub(&mut self, a: &[usize], b: &[usize]) -> Bits {
    bits::subtract(&mut self.b, self.one, self.zero, a, b).0
  }
  pub(super) fn lt(&mut self, a: &[usize], b: &[usize]) -> usize {
    bits::subtract(&mut self.b, self.one, self.zero, a, b).1
  }
  pub(super) fn le(&mut self, f: usize, a: &[usize], b: &[usize]) {
    let over = self.lt(b, a);
    let good = self.inv(over);
    self.need(f, good);
  }
  pub(super) fn bound(&mut self, f: usize, a: &[usize], max: u64) {
    self.le(f, a, &self.c(a.len(), max));
  }
  pub(super) fn value(&mut self, f: usize, a: &[usize]) -> [usize; 10] {
    paged_value::cell(&mut self.b, self.one, &mut self.bad, f, a, false)
  }
  pub(super) fn vector(&mut self, pointer: &[usize], count: &[usize]) -> Bits {
    let empty = self.eqc(count, 0);
    let live = self.inv(empty);
    let mut out = self.c(128, 0);
    out[..64].copy_from_slice(&self.mask(live, &self.wide(pointer, 64)));
    out[64..72].copy_from_slice(count);
    out
  }
  /// Check a complete vector against the previously allocated heap prefix.
  /// Scratch is only allowed as a source of a heap allocation.
  pub(super) fn span(
    &mut self,
    f: usize,
    vector: &[usize],
    heap: &[usize],
    scratch: usize,
  ) {
    self.zeros(f, &vector[40..64]);
    self.zeros(f, &vector[72..]);
    let count = &vector[64..72];
    self.bound(f, count, 64);
    let empty = self.eqc(count, 0);
    let empty_f = self.and(f, empty);
    self.zeros(empty_f, &vector[..64]);
    let nonempty = self.inv(empty);
    let live = self.and(f, nonempty);
    let is_heap = self.eqc(&vector[36..40], HEAP >> 36);
    let is_scratch = self.eqc(&vector[36..40], SCRATCH >> 36);
    let allowed_scratch = self.and(scratch, is_scratch);
    let allowed = self.any(&[is_heap, allowed_scratch]);
    self.need(live, allowed);
    let end = self.add(&self.wide(&vector[..36], 37), &self.wide(count, 37));
    let heap_live = self.and(live, is_heap);
    self.le(heap_live, &end, heap);
    let scratch_live = self.and(live, is_scratch);
    self.bound(scratch_live, &end, 65);
  }
  pub(super) fn action(&self, kind: ActionKind, target: &[usize]) -> Vec<Bits> {
    let mut out = vec![self.c(128, 0); 5];
    out[0] = self.c(128, kind as u64);
    out[0][8..16].copy_from_slice(target);
    out
  }
  pub(super) fn phase(
    &mut self,
    e: usize,
    state: &[Bits],
    micro: u64,
    frame: Phase,
  ) {
    self.is(e, &state[CONTROL], micro);
    self.is(e, &state[0][..8], frame as u64);
  }
  pub(super) fn instruction(
    &mut self,
    e: usize,
    state: &[Bits],
    instruction: u64,
    operation: u64,
  ) {
    self.phase(e, state, EXECUTE, Phase::Eval);
    self.is(e, &state[HEADER][8..16], instruction);
    self.is(e, &state[HEADER][16..24], operation);
  }
  pub(super) fn start_store(
    &mut self,
    e: usize,
    state: &[Bits],
    action: Vec<Bits>,
    a: Bits,
    b: Bits,
    heap: usize,
  ) -> Vec<Bits> {
    let total = self.add(&self.wide(&a[64..72], 9), &self.wide(&b[64..72], 9));
    self.bound(e, &total, 64);
    self.span(e, &a, &state[HEAP_COUNT][..37], heap);
    self.span(e, &b, &state[HEAP_COUNT][..37], heap);
    let count = &total[..8];
    let reserved = self.add(&state[HEAP_COUNT][..37], &self.wide(count, 37));
    let heap_live = self.and(e, heap);
    self.bound(heap_live, &reserved, 1 << 36);
    let hp = self.add(&state[HEAP_COUNT][..64], &self.c(64, HEAP));
    let destination = self.choose(heap, &hp, &self.c(64, SCRATCH));
    let destination = self.vector(&destination, count);
    let mut after = state.to_vec();
    let allocated = self.choose(heap, &reserved, &state[HEAP_COUNT][..37]);
    after[HEAP_COUNT] = self.wide(&allocated, 128);
    after[CONTROL] = self.c(128, STORE);
    after[CONTROL][16..24].copy_from_slice(count);
    after[CONTROL][24] = heap;
    after[PENDING..PENDING + 5].clone_from_slice(&action);
    after[SOURCE_A] = a;
    after[SOURCE_B] = b;
    after[DESTINATION] = self.wide(&destination[..64], 128);
    after[OLD_HEAP] = self.mask(heap, &state[HEAP_COUNT]);
    after
  }
  pub(super) fn store(
    &mut self,
    e: usize,
    state: &[Bits],
    finish: bool,
  ) -> Bits {
    self.is(e, &state[CONTROL][..8], STORE);
    self.zeros(e, &state[CONTROL][25..]);
    self.zeros(e, &state[19..].concat());
    let eval = self.eqc(&state[0][..8], Phase::Eval as u64);
    let apply = self.eqc(&state[0][..8], Phase::Apply as u64);
    let allowed = self.any(&[eval, apply]);
    self.need(e, allowed);
    let index = &state[CONTROL][8..16];
    let count = &state[CONTROL][16..24];
    self.bound(e, count, 64);
    if finish {
      self.same(e, index, count);
    } else {
      let good = self.lt(index, count);
      self.need(e, good);
    }
    let heap = state[CONTROL][24];
    let scratch = self.inv(heap);
    let scratch_e = self.and(e, scratch);
    self.zeros(scratch_e, &state[OLD_HEAP]);
    self.bound(e, &state[OLD_HEAP], 1 << 36);
    let previous =
      self.choose(heap, &state[OLD_HEAP][..37], &state[HEAP_COUNT][..37]);
    let a = &state[SOURCE_A];
    let b = &state[SOURCE_B];
    self.span(e, a, &previous, heap);
    self.span(e, b, &previous, heap);
    let total = self.add(&self.wide(&a[64..72], 9), &self.wide(&b[64..72], 9));
    self.same(e, &total, &self.wide(count, 9));
    let reserved = self.add(&previous, &self.wide(count, 37));
    let heap_e = self.and(e, heap);
    self.same(heap_e, &state[HEAP_COUNT][..37], &reserved);
    let hp = self.add(&state[OLD_HEAP][..64], &self.c(64, HEAP));
    let dp = self.choose(heap, &hp, &self.c(64, SCRATCH));
    let expected = self.vector(&dp, count);
    self.same(e, &state[DESTINATION], &self.wide(&expected[..64], 128));
    let use_a = self.lt(index, &a[64..72]);
    let b_index = self.sub(index, &a[64..72]);
    let a_address = self.add(&a[..64], &self.wide(index, 64));
    let b_address = self.add(&b[..64], &self.wide(&b_index, 64));
    let source = self.choose(use_a, &a_address, &b_address);
    self.wide(&source, 128)
  }
}

pub(super) fn build(kind: ObjectKind) -> BooleanR1csPlan {
  let ni = 1 + STATE_WORDS + kind.extra_inputs();
  let no = kind.outputs() + 1;
  let mut b = BooleanR1csBuilder::new(16, (ni + no) * 128);
  for i in 0..ni * 128 {
    b.free_boolean_at(i);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut s = S { b, one, zero, bad: Vec::new() };
  let e = 0;
  s.zeros(one, &(1..128).collect::<Bits>());
  let state = (1..1 + STATE_WORDS).map(word).collect::<Vec<_>>();
  let extra = (1 + STATE_WORDS..ni).map(word).collect::<Vec<_>>();
  let h = &state[HEADER];
  let target = &h[80..88];
  let args = &h[40..48];
  let storing = matches!(
    kind,
    ObjectKind::StoreRequest | ObjectKind::StoreCopy | ObjectKind::StoreFinish
  );
  if !storing {
    s.zeros(e, &state[10..].concat());
  }
  for at in [HEAP_COUNT, BYTE_COUNT] {
    s.bound(e, &state[at], 1 << 36);
  }
  let mut out = match kind {
    ObjectKind::Reference => {
      s.phase(e, &state, EXECUTE, Phase::Eval);
      s.is(e, &h[8..16], 0);
      let ctor = s.eqc(&h[16..24], 2);
      let closure = s.eqc(&h[16..24], 4);
      let allowed = s.any(&[ctor, closure]);
      s.need(e, allowed);
      vec![s.wide(&h[64..80], 128)]
    },
    ObjectKind::OperandRequest => {
      s.phase(e, &state, EXECUTE, Phase::Eval);
      let empty = s.eqc(&h[32..40], 0);
      let nonempty = s.inv(empty);
      s.need(e, nonempty);
      s.bound(e, &h[32..40], 65);
      vec![s.c(128, SCRATCH), s.wide(&h[48..56], 128)]
    },
    ObjectKind::Construct | ObjectKind::Closure => {
      let constructor = kind == ObjectKind::Construct;
      s.instruction(e, &state, 0, if constructor { 2 } else { 4 });
      let arity = &extra[0][..8];
      if constructor {
        s.same(e, args, arity);
      } else {
        let under = s.lt(args, arity);
        s.need(e, under);
      }
      let pointer = s.add(&state[HEAP_COUNT][..64], &s.c(64, HEAP));
      let vector = s.vector(&pointer, args);
      let mut action = s.action(ActionKind::Bind, target);
      action[2] = s.c(128, if constructor { 7 } else { 9 });
      action[2][64..80].copy_from_slice(&h[64..80]);
      action[3] = vector;
      let source = s.vector(&s.c(64, SCRATCH), args);
      s.start_store(e, &state, action, source, s.c(128, 0), one)
    },
    ObjectKind::ApplyInstruction => {
      s.phase(e, &state, EXECUTE, Phase::Eval);
      let is_let = s.eqc(&h[8..16], 0);
      let op = s.eqc(&h[16..24], 7);
      let regular = s.and(is_let, op);
      let tail = s.eqc(&h[8..16], 4);
      let allowed = s.any(&[regular, tail]);
      s.need(e, allowed);
      let value = extra.concat();
      s.value(e, &value);
      let pointer = s.add(&state[HEAP_COUNT][..64], &s.c(64, HEAP));
      let vector = s.vector(&pointer, args);
      let regular_action = s.action(ActionKind::Apply, target);
      let tail_action = s.action(ActionKind::TailApply, &s.c(8, 0));
      let mut action = regular_action
        .iter()
        .zip(&tail_action)
        .map(|(a, b)| s.choose(regular, a, b))
        .collect::<Vec<_>>();
      action[1] = vector;
      action[2] = extra[0].clone();
      action[3] = extra[1].clone();
      let source = s.vector(&s.c(64, SCRATCH + 1), args);
      s.start_store(e, &state, action, source, s.c(128, 0), one)
    },
    ObjectKind::ProjectRequest | ObjectKind::ProjectAction => {
      s.instruction(e, &state, 0, 3);
      let value = extra[..2].concat();
      let tags = s.value(e, &value);
      let ctor = tags[6];
      let erased = tags[4];
      let allowed = s.any(&[ctor, erased]);
      s.need(e, allowed);
      let vector = s.mask(ctor, &extra[1]);
      s.span(ctor, &vector, &state[HEAP_COUNT][..37], zero);
      let index = &h[96..112];
      let valid = s.lt(index, &s.wide(&extra[1][64..72], 16));
      s.need(ctor, valid);
      let address = s.add(&extra[1][..64], &s.wide(index, 64));
      if kind == ObjectKind::ProjectRequest {
        vec![s.mask(ctor, &s.wide(&address, 128))]
      } else {
        let field = extra[2..].concat();
        s.value(ctor, &field);
        let mut action = s.action(ActionKind::Bind, target);
        action[2] = s.choose(ctor, &extra[2], &s.c(128, 5));
        action[3] = s.mask(ctor, &extra[3]);
        action
      }
    },
    ObjectKind::CaseAction => {
      s.instruction(e, &state, 5, 0);
      let tags = s.value(e, &extra[..2].concat());
      s.need(e, tags[6]);
      s.span(e, &extra[1], &state[HEAP_COUNT][..37], zero);
      s.same(e, &extra[0][64..128], &s.wide(&extra[2][..8], 64));
      let mut action = s.action(ActionKind::Append, &extra[2][8..16]);
      action[1] = extra[1].clone();
      action
    },
    ObjectKind::ApplyRequest | ObjectKind::ApplyStart => {
      s.phase(e, &state, READY, Phase::Apply);
      s.zeros(e, h);
      let tags = s.value(e, &state[2..4].concat());
      s.span(e, &state[4], &state[HEAP_COUNT][..37], zero);
      let empty = s.eqc(&state[4][64..72], 0);
      let nonempty = s.inv(empty);
      let erased_or_empty = s.any(&[tags[4], empty]);
      let pap_required = s.inv(erased_or_empty);
      let pap_required = s.and(e, pap_required);
      s.need(pap_required, tags[8]);
      let pap = s.and(tags[8], nonempty);
      let need_decl = s.and(e, pap);
      let captures = s.mask(need_decl, &state[3]);
      s.span(need_decl, &captures, &state[HEAP_COUNT][..37], zero);
      if kind == ObjectKind::ApplyRequest {
        vec![
          vec![need_decl],
          s.mask(need_decl, &s.wide(&state[2][64..128], 128)),
        ]
      } else {
        let unused = s.inv(need_decl);
        s.zeros(unused, &extra.concat());
        let arity = &extra[0][..8];
        let entry = &extra[0][8..16];
        let captured = &captures[64..72];
        let valid = s.lt(captured, arity);
        s.need(need_decl, valid);
        let count = &state[4][64..72];
        let total = s.add(&s.wide(captured, 9), &s.wide(count, 9));
        let under = s.lt(&total, &s.wide(arity, 9));
        let partial = s.and(need_decl, under);
        let enough = s.inv(under);
        let enter = s.and(need_decl, enough);
        let needed = s.sub(arity, captured);
        let take = s.choose(under, count, &needed);
        let take = s.mask(need_decl, &take);
        let source_b = s.vector(&state[4][..64], &take);
        let pointer = s.add(&state[HEAP_COUNT][..64], &s.c(64, HEAP));
        let result_vector = s.vector(&pointer, &total[..8]);
        let mut result_header = s.c(128, 9);
        result_header[64..128].copy_from_slice(&state[2][64..128]);
        let mut returned = s.action(ActionKind::ApplyReturn, &s.c(8, 0));
        returned[2] = s.choose(partial, &result_header, &state[2]);
        returned[3] = s.choose(partial, &result_vector, &state[3]);
        let mut entered = s.action(ActionKind::ApplyEnter, &s.c(8, 0));
        entered[0][16..32].copy_from_slice(&state[2][64..80]);
        entered[0][32..40].copy_from_slice(entry);
        entered[0][40..48].copy_from_slice(arity);
        entered[1] = s.vector(&s.c(64, SCRATCH), arity);
        let remaining = s.sub(count, &needed);
        let rest_pointer = s.add(&state[4][..64], &s.wide(&needed, 64));
        entered[4] = s.vector(&rest_pointer, &remaining);
        let action = entered
          .iter()
          .zip(&returned)
          .map(|(a, b)| s.choose(enter, a, b))
          .collect();
        s.start_store(e, &state, action, captures, source_b, partial)
      }
    },
    ObjectKind::StoreRequest
    | ObjectKind::StoreCopy
    | ObjectKind::StoreFinish => {
      let source = s.store(e, &state, kind == ObjectKind::StoreFinish);
      if kind == ObjectKind::StoreRequest {
        vec![source]
      } else if kind == ObjectKind::StoreFinish {
        state[PENDING..PENDING + 5].to_vec()
      } else {
        s.value(e, &extra.concat());
        let mut after = state.clone();
        let next = s.add(&state[CONTROL][8..16], &s.c(8, 1));
        after[CONTROL][8..16].copy_from_slice(&next);
        let address =
          s.add(&state[DESTINATION][..64], &s.wide(&state[CONTROL][8..16], 64));
        after.extend([
          source,
          s.c(128, 0),
          extra[0].clone(),
          extra[1].clone(),
          s.wide(&address, 128),
          s.c(128, 1),
          extra[0].clone(),
          extra[1].clone(),
        ]);
        after
      }
    },
  };
  assert_eq!(out.len(), kind.outputs());
  for value in &mut out {
    *value = s.mask(e, &s.wide(value, 128));
  }
  let bad = s.any(&s.bad.clone());
  out.push(s.wide(&[bad], 128));
  for (i, value) in out.iter().enumerate() {
    for (j, &bit) in value.iter().enumerate() {
      s.b.write_xor((ni + i) * 128 + j, &[bit], one);
    }
  }
  s.b.finish()
}
