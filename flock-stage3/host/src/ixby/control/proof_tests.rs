//! Real control-component proofs, NOT generic Exec. Resolved actions are
//! private advice here and are not authenticated instructions. This tests
//! fixed wiring between successive states, exact fuel, calls/returns and
//! absorbing padding. Verification uses only externally expected endpoints
//! and a proof, never the action list or a native execution.

use super::*;
use crate::ixby::{
  io::{InputLayout, LayoutEmitter, PublicLayout},
  value::{bool_words, word32_words},
};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder},
  hash::HashKind,
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

const NU: usize = 8;
const STEPS: usize = 8;
const CAPACITY: ControlCapacities =
  ControlCapacities { locals: 3, continuations: 2, arguments: 1 };
const DOMAIN: &[u8] = b"ix:ixby:control-trace-conformance:v0";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD_ENV: &str = "IXBY_FLOCK_CONTROL_VERIFY_CHILD";
const TEST: &str = "ixby::control::proof_tests::different_control_traces_share_setup_with_fresh_endpoint_only_verification";

#[derive(Serialize, Deserialize)]
struct Bundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_BYTES)
    .reject_trailing_bytes()
}

fn setup()
-> (ControlStepGate, ControlStepSlot, InputLayout, PublicLayout, CircuitShape) {
  let gate = ControlStepGate::new(NU, CAPACITY).unwrap();
  let mut builder = ShapeBuilder::new(NU);
  let mut b = LayoutEmitter::new(&mut builder);
  let slot = ControlStepSlot::declare(&mut b, gate.clone());
  let mut state: Vec<_> =
    (0..CAPACITY.state_words()).map(|_| b.input()).collect();
  for word in &state {
    b.publish(*word);
  }
  for _ in 0..STEPS {
    let action: Vec<_> =
      (0..CAPACITY.action_words()).map(|_| b.input()).collect();
    state = slot.step(&mut b, &state, &action);
  }
  for word in state {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  (gate, slot, inputs, public, builder.finish().unwrap())
}

fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert!((22..=35).contains(&m), "pinned baseline PCS geometry");
  let profile = LigeritoProfile::Fast128;
  let log_batch_size = embedded_initial_k_or_default(m, profile);
  PcsParams {
    m,
    profile,
    log_batch_size,
    log_inv_rate: profile.log_inv_rate(),
    num_lanes: union.commit_lanes(log_batch_size),
    merkle_hash: HashKind::Blake3,
  }
}

fn prove(
  private: &[F128],
  expected: &[F128],
  corrupt_state_wiring: bool,
) -> Vec<u8> {
  let (gate, slot, inputs, public, shape) = setup();
  let witness = shape.run(&inputs.assign(private).unwrap(), &[]);
  assert_eq!(witness.public, public.instantiate(expected).unwrap());
  let mut rows = witness.rows::<ControlStepGate>(slot.slot()).to_vec();
  assert_eq!(rows.len(), STEPS);
  if corrupt_state_wiring {
    // Change the second step's current function and recompute the entire
    // locally valid table row. Only the fixed inter-step wiring can reject
    // this splice; it is not a stale-output or host-admission test.
    rows[1].0[1].lo ^= 1;
    assert_eq!(
      evaluate(CAPACITY, &rows[1].0)[CAPACITY.state_words()],
      F128::ZERO
    );
  }
  assert_eq!(shape.registry_slot(slot.slot()), 0);
  let r1cs = gate.r1cs();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params,
    vec![UnionSlotProverInput::in_place(
      |dst| gate.generate_witness_into(&rows, dst),
      r1cs.csc_lincheck_circuit(),
    )],
    Vec::new(),
    &mut challenger,
  );
  codec().serialize(&Bundle { commitment, proof }).unwrap()
}

fn verify(expected: &[F128], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(
    expected.len() == 2 * CAPACITY.state_words(),
    "control endpoint width"
  );
  ensure!(bytes.len() as u64 <= MAX_BYTES, "control proof byte admission");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    codec().serialize(&bundle)? == bytes,
    "canonical control proof encoding"
  );
  let (gate, _, _, public, shape) = setup();
  let public = public.instantiate(expected)?;
  let r1cs = gate.r1cs();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &public,
    &[r1cs.csc_lincheck_circuit()],
    &bundle.commitment,
    &bundle.proof,
    &params,
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("control trace proof rejected: {error:?}")
  })?;
  Ok(())
}

fn isolated_verify(expected: &[F128], bytes: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD_ENV, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut input = child.stdin.take().unwrap();
  for word in expected {
    input.write_all(&word.lo.to_le_bytes()).unwrap();
    input.write_all(&word.hi.to_le_bytes()).unwrap();
  }
  input.write_all(bytes).unwrap();
  drop(input);
  let output = child.wait_with_output().unwrap();
  if !output.status.success() {
    eprintln!(
      "fresh control verifier rejected: {}",
      String::from_utf8_lossy(&output.stderr)
    );
  }
  output.status.success()
}

fn child() {
  let endpoint_bytes = 2 * CAPACITY.state_words() * 16;
  let mut bytes = Vec::new();
  std::io::stdin()
    .take(MAX_BYTES + endpoint_bytes as u64 + 1)
    .read_to_end(&mut bytes)
    .unwrap();
  assert!(
    (endpoint_bytes..=endpoint_bytes + MAX_BYTES as usize)
      .contains(&bytes.len())
  );
  let expected: Vec<_> = bytes[..endpoint_bytes]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| {
      F128::new(
        u64::from_le_bytes(word[..8].try_into().unwrap()),
        u64::from_le_bytes(word[8..].try_into().unwrap()),
      )
    })
    .collect();
  verify(&expected, &bytes[endpoint_bytes..], DOMAIN).unwrap();
}

fn call(function: u32, target: u32, arg: u32) -> ResolvedAction {
  ResolvedAction::Call {
    target,
    callee: CallTarget { function, entry: 0, arity: 1 },
    args: vec![word32_words(arg)],
  }
}

fn ret(value: u32) -> ResolvedAction {
  ResolvedAction::Return { value: word32_words(value) }
}

// Endpoints are hand-specified reference examples, not outputs accepted from
// the untrusted trace builder. Only actions are hidden by this component test.
fn cases() -> Vec<(Vec<F128>, Vec<F128>)> {
  let mut traces = Vec::new();
  for condition in [false, true] {
    traces.push((
      vec![
        ResolvedAction::Branch {
          condition: bool_words(condition),
          yes: 1,
          no: 2,
        },
        ret(if condition { 11 } else { 13 }),
        ResolvedAction::Idle,
      ],
      if condition { 11 } else { 13 },
      5,
    ));
  }
  traces.push((
    vec![
      call(1, 3, 17),
      ResolvedAction::Bind { target: 1, value: word32_words(19) },
      ret(19),
      ResolvedAction::Idle,
      ret(19),
      ResolvedAction::Idle,
    ],
    19,
    2,
  ));
  traces.push((
    vec![
      call(1, 3, 23),
      call(2, 1, 29),
      ret(31),
      ResolvedAction::Idle,
      ret(31),
      ResolvedAction::Idle,
      ret(31),
      ResolvedAction::Idle,
    ],
    31,
    0,
  ));
  traces.push((
    vec![
      ResolvedAction::TailCall {
        callee: CallTarget { function: 3, entry: 4, arity: 1 },
        args: vec![word32_words(37)],
      },
      ret(37),
      ResolvedAction::Idle,
    ],
    37,
    5,
  ));
  traces
    .into_iter()
    .enumerate()
    .map(|(index, (mut actions, result, remaining))| {
      let initial = ControlState {
        control: Control::Eval(ControlFrame {
          function: index as u32,
          block: 0,
          locals: vec![word32_words(index as u32 + 41)],
        }),
        continuation: vec![],
        remaining: STEPS as u32,
      };
      let terminal = ControlState {
        control: Control::Halted(word32_words(result)),
        continuation: vec![],
        remaining,
      };
      let mut expected = initial.words(CAPACITY).unwrap();
      expected.extend(terminal.words(CAPACITY).unwrap());
      let mut private = initial.words(CAPACITY).unwrap();
      actions.resize(STEPS, ResolvedAction::Idle);
      for action in actions {
        private.extend(action.words(CAPACITY).unwrap());
      }
      (private, expected)
    })
    .collect()
}

#[test]
#[ignore = "real fixed-capacity control traces, fresh verification and corrupted inter-step wiring"]
fn different_control_traces_share_setup_with_fresh_endpoint_only_verification()
{
  if std::env::var_os(CHILD_ENV).is_some() {
    child();
    return;
  }
  let identity = setup().4.circuit.digest();
  let cases = cases();
  for (private, expected) in &cases {
    let bytes = prove(private, expected, false);
    eprintln!(
      "Flock control-component conformance: {} bytes; fixed {STEPS} transitions",
      bytes.len()
    );
    assert!(isolated_verify(expected, &bytes));
    assert_eq!(setup().4.circuit.digest(), identity);
    for (word, bit) in [
      (0, 32),                      // initial fuel
      (1, 0),                       // initial function
      (3, 64),                      // initial local payload
      (CAPACITY.state_words(), 0),  // terminal kind
      (CAPACITY.state_words(), 32), // terminal fuel
      (CAPACITY.state_words(), 64), // terminal continuation depth
      (CAPACITY.state_words() + CAPACITY.value_word() + 1, 0),
    ] {
      let mut wrong = expected.clone();
      wrong[word] = xor(
        wrong[word],
        if bit < 64 {
          F128::new(1 << bit, 0)
        } else {
          F128::new(0, 1 << (bit - 64))
        },
      );
      assert!(verify(&wrong, &bytes, DOMAIN).is_err());
    }
    assert!(verify(&expected[..expected.len() - 1], &bytes, DOMAIN).is_err());
    let mut wrong = bytes.clone();
    wrong[0] ^= 1;
    assert!(verify(expected, &wrong, DOMAIN).is_err());
    wrong = bytes.clone();
    wrong.push(0);
    assert!(verify(expected, &wrong, DOMAIN).is_err());
    assert!(verify(expected, &bytes[..bytes.len() - 1], DOMAIN).is_err());
    assert!(
      verify(expected, &bytes, b"ix:ixby:bank-read-conformance:v0").is_err()
    );
  }
  let (private, expected) = &cases[2];
  let forged = prove(private, expected, true);
  assert!(!isolated_verify(expected, &forged));
}
