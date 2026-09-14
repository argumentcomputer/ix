use super::super::{source::SourceReadWires, *};
use super::*;
use crate::sizing::CircuitEmitter;
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

#[derive(Clone, Copy, Debug)]
pub struct DispatchState(pub [Wire; DISPATCH_STATE_WORDS]);

#[derive(Clone, Debug)]
pub struct DispatchStepWires {
  pub state: DispatchState,
  /// Exactly one for a complete non-padding event. String intermediate rows
  /// and Done padding must not be materialized as additional grammar events.
  pub committed: Wire,
  pub tag: Wire,
  pub cursor: Wire,
  pub bounds: [Wire; 3],
  pub fields: [Wire; GRAMMAR_EVENT_FIELDS],
  pub next: Wire,
  /// Actual NaturalDecodeGate limbs, zero outside a Nat event.
  pub natural_magnitude: Vec<Wire>,
  pub natural_range: Wire,
  /// Actual checked String/ByteArray span, NOT a hash or copied payload.
  pub payload_range: Wire,
}

/// Universal fixed-topology dispatcher. A row domain must fit twice the
/// dispatch step count (two payload-cursor rows per step), and the grammar
/// slot needs one extra explicit final Done row. CountingEmitter records the
/// actual requirements; declaring this component does not choose a profile.
#[derive(Clone, Debug)]
pub struct DispatchSlots {
  config: DispatchConfig,
  controls: [SlotId; 6],
  header: HeaderDecodeSlot,
  records: [RecordDecodeSlot; 13],
  natural: NaturalDecodeSlot,
  limit: NaturalLimitSlot,
  payload: PayloadCursorSlot,
  utf8: Utf8ChunkSlot,
  grammar: GrammarStepSlot,
  zero: Wire,
  done: Wire,
}
impl DispatchSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    config: DispatchConfig,
  ) -> Result<Self> {
    let controls = DispatchOp::ALL
      .into_iter()
      .map(|op| Ok(b.slot(DispatchGate::new(nu, config, op)?)))
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .unwrap();
    let records = RecordKind::ALL
      .into_iter()
      .map(|kind| {
        Ok(RecordDecodeSlot::declare(b, RecordDecodeGate::new(nu, kind)?))
      })
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .unwrap();
    Ok(Self {
      config,
      controls,
      records,
      header: HeaderDecodeSlot::declare(b, HeaderDecodeGate::new(nu)?),
      natural: NaturalDecodeSlot::declare(
        b,
        NaturalDecodeGate::new(nu, config.natural)?,
      ),
      limit: NaturalLimitSlot::declare(
        b,
        NaturalLimitGate::new(nu, config.natural)?,
      ),
      payload: PayloadCursorSlot::declare(b, PayloadCursorGate::new(nu)?),
      utf8: Utf8ChunkSlot::declare(b, Utf8ChunkGate::new(nu)?),
      grammar: GrammarStepSlot::declare(
        b,
        GrammarStepGate::new(nu, config.kind)?,
      ),
      zero: b.fixed_public_input(F128::ZERO),
      done: b.fixed_public_input(F128::new(17, 0)),
    })
  }
  pub fn config(&self) -> DispatchConfig {
    self.config
  }
  pub fn control_slot(&self, op: DispatchOp) -> SlotId {
    self.controls[op as usize]
  }
  pub fn record_slot(&self, kind: RecordKind) -> SlotId {
    self.records[kind as usize].slot()
  }
  pub fn header_slot(&self) -> SlotId {
    self.header.slot()
  }
  pub fn natural_slot(&self) -> SlotId {
    self.natural.slot()
  }
  pub fn natural_limit_slot(&self) -> SlotId {
    self.limit.slot()
  }
  pub fn payload_slot(&self) -> SlotId {
    self.payload.slot()
  }
  pub fn utf8_slot(&self) -> SlotId {
    self.utf8.slot()
  }
  pub fn grammar_slot(&self) -> SlotId {
    self.grammar.slot()
  }

  fn control(
    &self,
    b: &mut impl CircuitEmitter,
    op: DispatchOp,
    input: &[Wire],
  ) -> Vec<Wire> {
    let mut out = b.gate(self.control_slot(op), input);
    b.connect(out.pop().unwrap(), self.zero);
    out
  }
  /// Program context must be all zero. Transport context must be the actual
  /// admitted program metadata or an explicitly expected public statement.
  pub fn initialize(
    &self,
    b: &mut impl CircuitEmitter,
    file_length: Wire,
    context: [Wire; DISPATCH_CONTEXT_WORDS],
  ) -> DispatchState {
    let mut input = vec![file_length];
    input.extend(context);
    DispatchState(
      self.control(b, DispatchOp::Initialize, &input).try_into().unwrap(),
    )
  }

  /// `read` must authenticate these exact cursor/take wires to the caller's
  /// fixed expected artifact. It must return `config.window_words()` words,
  /// zero after take and EOF. The file-length wire is linked here as well.
  /// For shared authenticated buffers this need not repeat the file hash.
  pub fn step<B: CircuitEmitter>(
    &self,
    b: &mut B,
    old: DispatchState,
    read: impl FnOnce(&mut B, Wire, Wire) -> SourceReadWires,
  ) -> DispatchStepWires {
    let req = self.control(b, DispatchOp::Request, &old.0);
    let source = read(b, req[4], req[5]);
    assert_eq!(source.words.len(), self.config.window_words());
    b.connect(source.file_length, req[6]);
    let mut input = req.clone();
    input.extend(source.words);
    let route = self.control(b, DispatchOp::Route, &input);
    let header = self.header.decode(
      b,
      route[HEADER_PORT],
      &route[HEADER_PORT + 1..NATURAL_PORT],
    );
    let mut merge = vec![req[0], old.0[0]];
    merge.extend(header.limits);
    merge.extend([
      header.max_steps,
      header.entry,
      header.constructor_count,
      header.constructors_offset,
    ]);
    for (kind, decoder) in self.records.iter().enumerate() {
      let start = RECORD_PORTS + kind * 9;
      let record = decoder.decode(
        b,
        old.0[0],
        route[kind],
        route[start..start + 3].try_into().unwrap(),
        route[start + 3..start + 9].try_into().unwrap(),
      );
      merge.extend(record.fields);
      merge.push(record.next);
    }
    let n = self.config.natural.encoded_words();
    let mut input = vec![route[14]];
    input.extend_from_slice(&route[NATURAL_PORT..NATURAL_PORT + n]);
    let nat = self.control(b, DispatchOp::NaturalLookahead, &input);
    let nat_cursor = self.payload.advance(b, old.0[0], nat[0], route[14]);
    let magnitude =
      self.natural.decode(b, nat_cursor.natural_control, &nat[1..]);
    self.limit.check(b, old.0[grammar::LIMITS + 7], route[14], &magnitude);
    let payload =
      self.payload.advance(b, old.0[0], req[8], route[NATURAL_PORT + n + 2]);
    let utf8 = self.utf8.check(
      b,
      req[4],
      req[7],
      route[15],
      route[NATURAL_PORT + n..NATURAL_PORT + n + 2].try_into().unwrap(),
    );
    merge.extend([nat[0], nat_cursor.next, payload.next]);
    let event = self.control(b, DispatchOp::Merge, &merge);
    let fields = event[..GRAMMAR_EVENT_FIELDS].try_into().unwrap();
    let bounds = req[1..4].try_into().unwrap();
    let next = event[GRAMMAR_EVENT_FIELDS];
    let state = self.grammar.step(
      b,
      GrammarState(old.0[..28].try_into().unwrap()),
      req[0],
      bounds,
      fields,
      next,
    );
    let mut finish = old.0.to_vec();
    finish.extend(state.0);
    finish.extend([utf8.next, utf8.state, payload.next, req[0]]);
    let finish = self.control(b, DispatchOp::Finish, &finish);
    DispatchStepWires {
      state: DispatchState(finish[..30].try_into().unwrap()),
      committed: finish[30],
      tag: req[0],
      cursor: old.0[0],
      bounds,
      fields,
      next,
      natural_magnitude: magnitude,
      natural_range: nat_cursor.range,
      payload_range: payload.range,
    }
  }

  /// Requires actual Done phase, EOF, exhausted grammar obligations, and no
  /// unfinished string. Padding alone is not a substitute for this final row.
  pub fn finish(
    &self,
    b: &mut impl CircuitEmitter,
    state: DispatchState,
  ) -> GrammarState {
    b.connect(state.0[28], self.zero);
    b.connect(state.0[29], self.zero);
    self.grammar.step(
      b,
      GrammarState(state.0[..28].try_into().unwrap()),
      self.done,
      [self.zero; 3],
      [self.zero; 13],
      state.0[0],
    )
  }
}
