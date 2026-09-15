//! Untrusted native evaluation of the actual dispatcher tables. No AST or
//! separately supplied decoder schedule is used. This prepares witnesses;
//! it is never called by proof verification.
use super::super::*;
use super::*;
use anyhow::{Result, ensure};
use flock_prover::{circuit::builder::GateType, field::F128};

fn eval<G: GateType<Hint = ()>>(gate: &G, input: &[F128]) -> Result<Vec<F128>> {
  let mut output = Vec::new();
  gate.eval(input, &(), &mut output);
  ensure!(
    output.pop() == Some(F128::ZERO),
    "dispatcher witness rejected a row"
  );
  Ok(output)
}

pub struct DispatchEvaluator {
  config: DispatchConfig,
  controls: Vec<DispatchGate>,
  records: Vec<RecordDecodeGate>,
  header: HeaderDecodeGate,
  natural: NaturalDecodeGate,
  limit: NaturalLimitGate,
  payload: PayloadCursorGate,
  utf8: Utf8ChunkGate,
  grammar: GrammarStepGate,
}
pub struct EvaluatedStep {
  pub state: [F128; 30],
  pub tag: u8,
  pub committed: bool,
}
impl DispatchEvaluator {
  pub fn new(config: DispatchConfig) -> Result<Self> {
    Ok(Self {
      config,
      controls: DispatchOp::ALL
        .into_iter()
        .map(|op| DispatchGate::new(3, config, op))
        .collect::<Result<_>>()?,
      records: RecordKind::ALL
        .into_iter()
        .map(|kind| RecordDecodeGate::new(3, kind))
        .collect::<Result<_>>()?,
      header: HeaderDecodeGate::new(3)?,
      natural: NaturalDecodeGate::new(3, config.natural)?,
      limit: NaturalLimitGate::new(3, config.natural)?,
      payload: PayloadCursorGate::new(3)?,
      utf8: Utf8ChunkGate::new(3)?,
      grammar: GrammarStepGate::new(3, config.kind)?,
    })
  }
  pub fn config(&self) -> DispatchConfig {
    self.config
  }
  fn control(&self, op: DispatchOp, input: &[F128]) -> Result<Vec<F128>> {
    eval(&self.controls[op as usize], input)
  }
  pub fn initialize(
    &self,
    length: u64,
    context: [F128; 15],
  ) -> Result<[F128; 30]> {
    let mut input = vec![F128::new(length, 0)];
    input.extend(context);
    Ok(self.control(DispatchOp::Initialize, &input)?.try_into().unwrap())
  }
  pub fn request(&self, state: &[F128; 30]) -> Result<[F128; 9]> {
    Ok(self.control(DispatchOp::Request, state)?.try_into().unwrap())
  }
  pub fn step(
    &self,
    state: &[F128; 30],
    window: &[F128],
  ) -> Result<EvaluatedStep> {
    ensure!(
      window.len() == self.config.window_words(),
      "dispatcher window width"
    );
    let req = self.request(state)?;
    let mut input = req.to_vec();
    input.extend_from_slice(window);
    let route = self.control(DispatchOp::Route, &input)?;
    let header = eval(&self.header, &route[HEADER_PORT..NATURAL_PORT])?;
    let mut merge = vec![req[0], state[0]];
    merge.extend(header);
    for (index, decoder) in self.records.iter().enumerate() {
      let at = RECORD_PORTS + 9 * index;
      let mut input = vec![state[0], route[index]];
      input.extend_from_slice(&route[at..at + 9]);
      merge.extend(eval(decoder, &input)?);
    }
    let n = self.config.natural.encoded_words();
    let mut input = vec![route[14]];
    input.extend_from_slice(&route[NATURAL_PORT..NATURAL_PORT + n]);
    let nat = self.control(DispatchOp::NaturalLookahead, &input)?;
    let nat_cursor = eval(&self.payload, &[state[0], nat[0], route[14]])?;
    let mut input = vec![nat_cursor[0]];
    input.extend_from_slice(&nat[1..]);
    let magnitude = eval(&self.natural, &input)?;
    let mut input = vec![state[grammar::LIMITS + 7], route[14]];
    input.extend(magnitude);
    eval(&self.limit, &input)?;
    let payload =
      eval(&self.payload, &[state[0], req[8], route[NATURAL_PORT + n + 2]])?;
    let utf8 = eval(
      &self.utf8,
      &[
        req[4],
        req[7],
        route[15],
        route[NATURAL_PORT + n],
        route[NATURAL_PORT + n + 1],
      ],
    )?;
    merge.extend([nat[0], nat_cursor[2], payload[2]]);
    let event = self.control(DispatchOp::Merge, &merge)?;
    let mut input = state[..28].to_vec();
    input.extend_from_slice(&req[..4]);
    input.extend(event);
    let next = eval(&self.grammar, &input)?;
    let mut input = state.to_vec();
    input.extend(next);
    input.extend([utf8[0], utf8[1], payload[2], req[0]]);
    let mut next = self.control(DispatchOp::Finish, &input)?;
    let committed = next.pop().unwrap() == F128::ONE;
    Ok(EvaluatedStep {
      state: next.try_into().unwrap(),
      tag: req[0].lo as u8,
      committed,
    })
  }
}
