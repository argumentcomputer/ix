//! AST-free untrusted witness model and independent grammar differential.
//! Large-source tests here use actual source slices, NOT a full-file proof.
use super::super::*;
use super::*;
use crate::{boolean::BooleanR1csPlan, hash::pack_bytes, sizing::CountedGate};
use anyhow::{Result, ensure};
use flock_prover::{circuit::builder::GateType, field::F128, r1cs::BlockR1cs};

type Table<G> = (G, BlockR1cs);
pub(super) struct Model {
  pub config: DispatchConfig,
  controls: Vec<Table<DispatchGate>>,
  records: Vec<Table<RecordDecodeGate>>,
  header: Table<HeaderDecodeGate>,
  nat: Table<NaturalDecodeGate>,
  limit: Table<NaturalLimitGate>,
  payload: Table<PayloadCursorGate>,
  utf8: Table<Utf8ChunkGate>,
  grammar: Table<GrammarStepGate>,
  checked: bool,
}

fn eval<G: GateType<Hint = ()> + CountedGate>(
  table: &Table<G>,
  plan: &BooleanR1csPlan,
  input: &[F128],
  checked: bool,
) -> Result<Vec<F128>> {
  let mut out = Vec::new();
  table.0.eval(input, &(), &mut out);
  if checked {
    scalar_payload_tests::checked(plan, &table.1, input, &out);
  }
  ensure!(
    out.last() == Some(&F128::ZERO),
    "decoder residual at input {input:?}"
  );
  out.pop();
  Ok(out)
}

#[derive(Debug)]
pub(super) struct Parsed {
  pub state: [F128; 28],
  pub events: [usize; 18],
  pub steps: usize,
}
impl Model {
  pub(super) fn new(config: DispatchConfig, checked: bool) -> Self {
    macro_rules! table {
      ($gate:expr) => {{
        let g = $gate.unwrap();
        let r = g.r1cs();
        (g, r)
      }};
    }
    Self {
      config,
      checked,
      controls: DispatchOp::ALL
        .into_iter()
        .map(|op| table!(DispatchGate::new(3, config, op)))
        .collect(),
      records: RecordKind::ALL
        .into_iter()
        .map(|k| table!(RecordDecodeGate::new(3, k)))
        .collect(),
      header: table!(HeaderDecodeGate::new(3)),
      nat: table!(NaturalDecodeGate::new(3, config.natural)),
      limit: table!(NaturalLimitGate::new(3, config.natural)),
      payload: table!(PayloadCursorGate::new(3)),
      utf8: table!(Utf8ChunkGate::new(3)),
      grammar: table!(GrammarStepGate::new(3, config.kind)),
    }
  }
  fn control(&self, op: DispatchOp, input: &[F128]) -> Result<Vec<F128>> {
    let t = &self.controls[op as usize];
    eval(t, t.0.plan(), input, self.checked)
  }
  pub(super) fn parse(
    &self,
    bytes: &[u8],
    context: [F128; 15],
    maximum_steps: usize,
  ) -> Result<Parsed> {
    let mut init = vec![F128::new(bytes.len() as u64, 0)];
    init.extend(context);
    let mut state = self.control(DispatchOp::Initialize, &init)?;
    let mut events = [0; 18];
    let mut steps = 0;
    while state[1].lo as u8 != grammar::Phase::Done as u8
      || state[29] != F128::ZERO
    {
      ensure!(steps < maximum_steps, "dispatch step capacity");
      let req = self.control(DispatchOp::Request, &state)?;
      let at = usize::try_from(req[4].lo)?;
      ensure!(at <= bytes.len(), "read cursor");
      let count = (req[5].lo as usize).min(bytes.len() - at);
      let mut window = vec![0; self.config.window_bytes()];
      window[..count].copy_from_slice(&bytes[at..at + count]);
      let mut input = req.clone();
      input.extend(window.as_chunks::<16>().0.iter().map(|w| pack_bytes(w)));
      let route = self.control(DispatchOp::Route, &input)?;
      let header = eval(
        &self.header,
        self.header.0.plan(),
        &route[HEADER_PORT..NATURAL_PORT],
        self.checked && req[0].lo == 13,
      )?;
      let mut merge = vec![req[0], state[0]];
      merge.extend(header);
      for (index, t) in self.records.iter().enumerate() {
        let start = RECORD_PORTS + index * 9;
        let mut input = vec![state[0], route[index]];
        input.extend_from_slice(&route[start..start + 9]);
        merge.extend(eval(
          t,
          t.0.plan(),
          &input,
          self.checked && req[0].lo == index as u64,
        )?);
      }
      let n = self.config.natural.encoded_words();
      let mut input = vec![route[14]];
      input.extend_from_slice(&route[NATURAL_PORT..NATURAL_PORT + n]);
      let nat = self.control(DispatchOp::NaturalLookahead, &input)?;
      let nat_cursor = eval(
        &self.payload,
        self.payload.0.plan(),
        &[state[0], nat[0], route[14]],
        self.checked && req[0].lo == 14,
      )?;
      let mut input = vec![nat_cursor[0]];
      input.extend_from_slice(&nat[1..]);
      let magnitude = eval(
        &self.nat,
        self.nat.0.plan(),
        &input,
        self.checked && req[0].lo == 14,
      )?;
      let mut input = vec![state[grammar::LIMITS + 7], route[14]];
      input.extend(magnitude);
      eval(
        &self.limit,
        self.limit.0.plan(),
        &input,
        self.checked && req[0].lo == 14,
      )?;
      let payload = eval(
        &self.payload,
        self.payload.0.plan(),
        &[state[0], req[8], route[NATURAL_PORT + n + 2]],
        self.checked && (15..=16).contains(&req[0].lo),
      )?;
      let utf8 = eval(
        &self.utf8,
        self.utf8.0.plan(),
        &[
          req[4],
          req[7],
          route[15],
          route[NATURAL_PORT + n],
          route[NATURAL_PORT + n + 1],
        ],
        self.checked && req[0].lo == 15,
      )?;
      merge.extend([nat[0], nat_cursor[2], payload[2]]);
      let event = self.control(DispatchOp::Merge, &merge)?;
      let mut input = state[..28].to_vec();
      input.extend_from_slice(&req[..4]);
      input.extend(event);
      let expected = grammar_reference_tests::step(
        self.config.kind,
        &input.clone().try_into().unwrap(),
      )?;
      let actual =
        eval(&self.grammar, self.grammar.0.plan(), &input, self.checked)?;
      ensure!(
        actual == expected,
        "independent complete-state grammar differential"
      );
      let mut finish = state.clone();
      finish.extend(actual);
      finish.extend([utf8[0], utf8[1], payload[2], req[0]]);
      let mut out = self.control(DispatchOp::Finish, &finish)?;
      let commit = out.pop().unwrap();
      if commit == F128::ONE {
        events[req[0].lo as usize] += 1;
      }
      state = out;
      steps += 1;
    }
    ensure!(state[28..] == [F128::ZERO; 2], "unfinished string");
    let mut input = state[..28].to_vec();
    input.push(F128::new(17, 0));
    input.extend([F128::ZERO; 16]);
    input.push(state[0]);
    let expected = grammar_reference_tests::step(
      self.config.kind,
      &input.clone().try_into().unwrap(),
    )?;
    let actual =
      eval(&self.grammar, self.grammar.0.plan(), &input, self.checked)?;
    ensure!(
      actual == expected && actual == state[..28],
      "explicit Done preserves complete state"
    );
    events[17] += 1;
    Ok(Parsed { state: actual.try_into().unwrap(), events, steps: steps + 1 })
  }
}

pub(super) fn config(kind: GrammarKind) -> DispatchConfig {
  DispatchConfig { kind, natural: NaturalCapacity::new(4096).unwrap() }
}
pub(super) fn nat(bytes: &mut Vec<u8>, mut n: u128) {
  loop {
    let digit = (n & 127) as u8;
    n >>= 7;
    bytes.push(digit | if n == 0 { 0 } else { 128 });
    if n == 0 {
      break;
    }
  }
}
pub(super) fn program(scalar: Option<&[u8]>, arity: u128) -> Vec<u8> {
  let mut bytes = b"IXBF\x01\0\0\0\x01\0\0\0".to_vec();
  for value in [
    8,
    8,
    8,
    8,
    8,
    8,
    32,
    4096,
    900,
    900,
    1u128 << 100,
    0,
    0,
    1,
    arity,
    0,
    1,
    arity,
    1,
  ] {
    nat(&mut bytes, value);
  }
  if let Some(scalar) = scalar {
    bytes.push(1);
    bytes.extend_from_slice(scalar);
  } else {
    bytes.push(2);
  }
  bytes
}
pub(super) fn transport(kind: GrammarKind, scalar: &[u8]) -> Vec<u8> {
  let mut bytes =
    if kind == GrammarKind::Input { b"IXFI" } else { b"IXFO" }.to_vec();
  bytes.extend_from_slice(b"\x01\0\0\0\0\0\0\0");
  if kind == GrammarKind::Input {
    bytes.push(1);
  }
  bytes.push(0);
  bytes.extend_from_slice(scalar);
  bytes
}

/// Independently encoded declaration, Let/Copy, target, constructor-case
/// alternative and return; every successor has the correct local frame.
pub(super) fn branching_program() -> Vec<u8> {
  let mut bytes = b"IXBF\x01\0\0\0\x01\0\0\0".to_vec();
  for value in [8, 8, 8, 8, 8, 8, 32, 4096, 900, 900, 1u128 << 100, 0, 1] {
    nat(&mut bytes, value);
  }
  bytes.extend([0; 35]); // constructor identity and zero fields
  bytes.extend([1, 0, 0, 3]); // one function: arity/entry zero, three blocks
  bytes.extend([0, 0, 0, 2, 1]); // let copy erased, then block one
  bytes.extend([1, 5, 0, 0, 1, 0, 2]); // case local zero; constructor zero -> block two
  bytes.extend([1, 1, 0, 0]); // return local zero
  bytes
}
pub(super) fn context(state: &[F128; 28]) -> [F128; 15] {
  DISPATCH_CONTEXT_INDICES.map(|i| state[i])
}
pub(super) fn strings(length: usize) -> Vec<u8> {
  let mut bytes = vec![1];
  nat(&mut bytes, length as u128);
  bytes.extend(vec![b'a'; length]);
  if length >= 35 {
    let at = bytes.len() - length + 31;
    bytes[at..at + 4].copy_from_slice("𐀀".as_bytes());
  }
  bytes
}

#[test]
fn state_selected_whole_grammars_cover_scalars_streaming_and_exact_completion()
{
  let models = [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output]
    .map(|kind| Model::new(config(kind), true));
  let empty = program(None, 1);
  let parsed = models[0].parse(&empty, [F128::ZERO; 15], 32).unwrap();
  assert_eq!(parsed.steps, 6);
  assert_eq!(parsed.events[13], 1);
  let context = context(&parsed.state);
  let branching = branching_program();
  let branch = models[0].parse(&branching, [F128::ZERO; 15], 32).unwrap();
  assert_eq!(branch.events[3], 1);
  assert_eq!(branch.events[12], 1);
  assert_eq!(branch.events[6], 1);
  assert_eq!(branch.events[2], 1);
  crate::ixby::ixbf::decode_program(
    &branching,
    crate::ixby::ixbf::DecodeLimits::default(),
  )
  .unwrap();
  let mut scalars = vec![
    vec![0, 0],
    vec![0, 255, 1],
    vec![2, 1],
    vec![3, 255, 0, 0, 128],
    vec![4, 0, 0, 0, 0, 0, 0, 0, 0],
    vec![5; 1].into_iter().chain([0; 16]).collect(),
  ];
  let mut wide = vec![0];
  wide.extend(vec![255; 585]);
  wide.push(1);
  scalars.push(wide);
  for length in [0, 1, 31, 32, 33, 35, 64, 65, 512] {
    scalars.push(strings(length));
  }
  let mut bytes = vec![6];
  nat(&mut bytes, 800);
  bytes.extend((0..800).map(|i| i as u8));
  scalars.push(bytes);
  for scalar in &scalars {
    for (index, model) in models.iter().enumerate() {
      let bytes = if index == 0 {
        program(Some(scalar), 1)
      } else {
        transport(model.config.kind, scalar)
      };
      let parsed = model
        .parse(&bytes, if index == 0 { [F128::ZERO; 15] } else { context }, 32)
        .unwrap();
      assert_eq!(
        parsed.state[0],
        F128::new(bytes.len() as u64, bytes.len() as u64)
      );
      assert_eq!(parsed.events[11], 1);
      if scalar[0] == 1 && scalar.len() > 2 {
        assert_eq!(parsed.events[15], 1);
      }
      if scalar[0] == 0 {
        assert_eq!(parsed.events[14], 1);
      }
      assert_eq!(parsed.events[17], 1);
    }
  }
  // A parser that speculatively advances on the first UTF-8 chunk would miss
  // the bad trailing byte in each of these otherwise complete wire images.
  for index in [31, 32, 63, 64] {
    let mut scalar = strings(65);
    scalar[2 + index] = 255;
    let bytes = transport(GrammarKind::Output, &scalar);
    assert!(models[2].parse(&bytes, context, 32).is_err());
  }
  for scalar in [
    vec![0, 128, 0],
    vec![0, 128],
    vec![1, 1, 192],
    vec![1, 2, 224, 160],
    vec![6, 2, 0],
  ] {
    assert!(
      models[2]
        .parse(&transport(GrammarKind::Output, &scalar), context, 32)
        .is_err()
    );
  }
  let bytes = program(Some(&strings(512)), 1);
  assert!(models[0].parse(&bytes, [F128::ZERO; 15], 8).is_err());
  for end in 0..empty.len() {
    assert!(models[0].parse(&empty[..end], [F128::ZERO; 15], 32).is_err());
  }
  let mut trailing = empty.clone();
  trailing.push(0);
  assert!(models[0].parse(&trailing, [F128::ZERO; 15], 32).is_err());
  let mut narrow = config(GrammarKind::Program);
  narrow.natural = NaturalCapacity::new(127).unwrap();
  assert!(
    Model::new(narrow, true)
      .parse(&program(Some(&scalars[6]), 1), [F128::ZERO; 15], 32)
      .is_err()
  );
}
