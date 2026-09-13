// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Record the actual generic native verifier's transcript, including its
//! PCS continuation. The wrapper delegates every operation to the pinned
//! challenger. Separate mock-hash cases force rejection sampling boundaries.

use super::*;
use multi_stark::{
  config::StarkGenericConfig,
  p3_field::PrimeField64,
  types::{Challenger, ExtVal, Pcs},
};
use p3_blake3::Blake3;
use p3_challenger::{
  CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger,
  HashChallenger, SerializingChallenger64,
};
use p3_symmetric::{CryptographicHasher, MerkleCap};
use std::sync::{Arc, Mutex};

#[derive(Clone, Debug)]
enum Event {
  Observe(Vec<u8>),
  Field(G),
  Bits(usize, usize),
}

type Events = Arc<Mutex<Vec<Event>>>;
type Dft = <AiurConfig as StarkGenericConfig>::Dft;
type Commitment = MerkleCap<G, [u8; 32]>;

#[derive(Clone)]
struct RecordingChallenger {
  inner: Challenger,
  events: Events,
}

impl CanObserve<G> for RecordingChallenger {
  fn observe(&mut self, value: G) {
    self.inner.observe(value);
    self
      .events
      .lock()
      .unwrap()
      .push(Event::Observe(value.as_canonical_u64().to_le_bytes().to_vec()));
  }
}

impl CanObserve<Commitment> for RecordingChallenger {
  fn observe(&mut self, value: Commitment) {
    self.inner.observe(value.clone());
    self
      .events
      .lock()
      .unwrap()
      .push(Event::Observe(value.roots().iter().flatten().copied().collect()));
  }
}

impl CanSample<G> for RecordingChallenger {
  fn sample(&mut self) -> G {
    let value = self.inner.sample();
    self.events.lock().unwrap().push(Event::Field(value));
    value
  }
}

impl CanSample<ExtVal> for RecordingChallenger {
  fn sample(&mut self) -> ExtVal {
    self.sample_algebra_element()
  }
}

impl CanSampleBits<usize> for RecordingChallenger {
  fn sample_bits(&mut self, bits: usize) -> usize {
    let value = self.inner.sample_bits(bits);
    self.events.lock().unwrap().push(Event::Bits(bits, value));
    value
  }
}

impl FieldChallenger<G> for RecordingChallenger {}

impl GrindingChallenger for RecordingChallenger {
  type Witness = G;

  fn grind(&mut self, bits: usize) -> G {
    self.inner.grind(bits)
  }
  // The trait's check_witness calls our observed-field and sampled-bit
  // methods, and consumes nothing at zero bits, just like the native type.
}

struct RecordingConfig {
  inner: AiurConfig,
  events: Events,
}

impl StarkGenericConfig for RecordingConfig {
  type Pcs = Pcs;
  type Dft = Dft;
  type Challenge = ExtVal;
  type Challenger = RecordingChallenger;

  fn pcs(&self) -> &Pcs {
    self.inner.pcs()
  }
  fn dft(&self) -> &Dft {
    self.inner.dft()
  }
  fn initialise_challenger(&self) -> RecordingChallenger {
    RecordingChallenger {
      inner: self.inner.initialise_challenger(),
      events: self.events.clone(),
    }
  }
  fn max_log_degree(&self) -> usize {
    self.inner.max_log_degree()
  }
  fn max_quotient_degree(&self) -> usize {
    self.inner.max_quotient_degree()
  }
  fn log_blowup(&self) -> usize {
    self.inner.log_blowup()
  }
}

fn number(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn bytes(out: &mut Vec<u8>, value: &[u8]) {
  number(out, value.len());
  out.extend(value);
}

fn field(out: &mut Vec<u8>, value: G) {
  out.extend(value.as_canonical_u64().to_le_bytes());
}

fn event(out: &mut Vec<u8>, event: &Event) {
  match event {
    Event::Observe(value) => {
      out.push(0);
      bytes(out, value);
    },
    Event::Field(value) => {
      out.push(1);
      field(out, *value);
    },
    Event::Bits(bits, value) => {
      out.push(2);
      number(out, *bits);
      number(out, *value);
    },
  }
}

fn record(
  out: &mut Vec<u8>,
  system: &AiurSystem,
  proof: &AiurProof,
  claims: &[Vec<G>],
  expected: bool,
) {
  let cp = system.commitment_parameters;
  let fp = system.fri_parameters;
  let events = Events::default();
  let key_bytes = crate::vk_codec::to_bytes(&system.system, cp, fp);
  let (decoded, _, _) = crate::vk_codec::from_bytes(&key_bytes).unwrap();
  let instrumented = System {
    config: RecordingConfig {
      inner: AiurConfig::new(cp, fp),
      events: events.clone(),
    },
    circuits: decoded.circuits,
    preprocessed_commit: decoded.preprocessed_commit,
    preprocessed_indices: decoded.preprocessed_indices,
  };
  let proof_bytes = proof.to_bytes().unwrap();
  let copied = Proof::<RecordingConfig>::from_bytes(&proof_bytes).unwrap();
  let claim_slices: Vec<&[G]> = claims.iter().map(Vec::as_slice).collect();
  let accepted = instrumented.verify_multiple_claims(&claim_slices, &copied);
  assert_eq!(accepted.is_ok(), expected);
  // Compare with the original concrete native configuration as well.
  assert_eq!(
    system.system.verify_multiple_claims(&claim_slices, proof).is_ok(),
    expected
  );
  let events = events.lock().unwrap();
  assert!(events.iter().filter(|e| matches!(e, Event::Field(_))).count() >= 8);
  bytes(out, &key_bytes);
  bytes(out, &proof_bytes);
  number(out, claims.len());
  for claim in claims {
    number(out, claim.len());
    for value in claim {
      field(out, *value);
    }
  }
  out.push(u8::from(expected));
  number(out, events.len());
  for value in events.iter() {
    event(out, value);
  }
}

#[derive(Clone)]
struct ScriptHasher {
  first: [u8; 32],
  later: [u8; 32],
}

impl CryptographicHasher<u8, [u8; 32]> for ScriptHasher {
  fn hash_iter<I: IntoIterator<Item = u8>>(&self, input: I) -> [u8; 32] {
    if input.into_iter().count() == 1 { self.first } else { self.later }
  }
}

#[derive(Clone)]
struct CountedBytes<C> {
  inner: C,
  consumed: Arc<Mutex<usize>>,
}

impl<C: CanSample<u8>> CanSample<u8> for CountedBytes<C> {
  fn sample(&mut self) -> u8 {
    *self.consumed.lock().unwrap() += 1;
    self.inner.sample()
  }
}

impl<C: CanObserve<u8>> CanObserve<u8> for CountedBytes<C> {
  fn observe(&mut self, value: u8) {
    self.inner.observe(value);
  }
}

fn digest(words: [u64; 4]) -> [u8; 32] {
  let mut value: Vec<u8> =
    words.iter().flat_map(|word| word.to_le_bytes()).collect();
  value.reverse();
  value.try_into().unwrap()
}

fn rejections(out: &mut Vec<u8>) {
  number(out, 16);
  for mask in 0..16 {
    let first = digest(std::array::from_fn(|i| {
      if mask & (1 << i) == 0 {
        [G::ORDER_U64, G::ORDER_U64 + 1, u64::MAX, G::ORDER_U64 + 3][i]
      } else {
        [0, G::ORDER_U64 - 1, 1 << 32, u64::MAX - (1 << 32)][i]
      }
    }));
    let later = digest([11, 12, 13, 14]);
    let consumed = Arc::new(Mutex::new(0));
    let inner = HashChallenger::new(vec![mask], ScriptHasher { first, later });
    let mut native = SerializingChallenger64::<G, _>::new(CountedBytes {
      inner,
      consumed: consumed.clone(),
    });
    let c0: G = native.sample();
    let first_attempts = *consumed.lock().unwrap() / 8;
    let c1: G = native.sample();
    let second_attempts = *consumed.lock().unwrap() / 8 - first_attempts;
    assert!((1..=5).contains(&first_attempts));
    assert!((1..=4).contains(&second_attempts));
    out.push(mask);
    out.extend(first);
    out.extend(later);
    field(out, c0);
    field(out, c1);
    number(out, first_attempts);
    number(out, second_attempts);
    // Raw bit samples also verify where both rejection loops left the stream.
    for bits in [0, 1, 7, 31, 32, 63] {
      number(out, native.sample_bits(bits));
    }
  }
}

fn byte_streams(out: &mut Vec<u8>) {
  number(out, 16);
  for seed in 0..16usize {
    let initial: Vec<u8> =
      (0..seed * 17).map(|i| u8::try_from(i * 73 % 256).unwrap()).collect();
    bytes(out, &initial);
    let mut native = HashChallenger::new(initial, Blake3);
    number(out, 80);
    for step in 0..80 {
      if step % 7 == 0 {
        let values: Vec<u8> = (0..(step + seed) % 5)
          .map(|i| u8::try_from((i + step * 31) % 256).unwrap())
          .collect();
        native.observe_slice(&values);
        event(out, &Event::Observe(values));
      } else {
        let value: u8 = native.sample();
        out.push(3);
        out.push(value);
      }
    }
  }
}

fn witnesses(out: &mut Vec<u8>) {
  number(out, 48);
  for seed in 0..8 {
    for bits in [0, 1, 2, 3, 7, 12] {
      let initial = vec![seed, 93, bits];
      bytes(out, &initial);
      let mut native = Challenger::from_hasher(initial, Blake3);
      // Populate pending output first to distinguish an empty observation
      // from an output reset, including the zero-bit witness branch.
      field(out, native.sample());
      number(out, usize::from(bits));
      let witness = G::from_u8(seed) - G::ONE;
      field(out, witness);
      out.push(u8::from(native.check_witness(usize::from(bits), witness)));
      field(out, native.sample());
    }
  }
}

#[test]
fn transcript_snapshot() -> std::io::Result<()> {
  let mut out = b"Aiur transcript v1\n".to_vec();
  byte_streams(&mut out);
  rejections(&mut out);
  witnesses(&mut out);
  number(&mut out, 40);
  for seed in 0..4 {
    let (mut cp, mut fp) = test_parameters();
    cp.cap_height = seed % 2 * 2;
    fp.max_log_arity = seed % 2 + 1;
    fp.num_queries = 8;
    fp.commit_proof_of_work_bits = if seed == 2 { 3 } else { 0 };
    fp.query_proof_of_work_bits = if seed == 2 { 3 } else { 0 };
    let top = match seed {
      0 => mul_toplevel(),
      1 => call_and_memory_toplevel(),
      2 => xor_splits_toplevel(),
      _ => unconstrained_call_promotion_toplevel(),
    };
    let input = if seed == 3 {
      vec![G::from_u8(7)]
    } else {
      vec![G::from_u8(3), G::from_u8(5)]
    };
    let system = AiurSystem::build(top, cp, fp);
    let (claim, proof) = system.prove(0, &input, &mut empty_io_buffer());
    for variant in 0..10 {
      let mut proof = proof.clone();
      let mut claims = vec![claim.clone()];
      match variant {
        0 => {},
        1 => claims[0][0] += G::ONE,
        2 => claims = vec![claim[..1].to_vec(), claim[1..].to_vec()],
        3 => claims.clear(),
        4 => claims = vec![vec![], vec![]],
        5 => claims[0].push(G::ZERO),
        6 => claims.insert(0, vec![]),
        7 => {
          proof.commitments.stage_1_trace =
            proof.commitments.stage_2_trace.clone()
        },
        8 => proof.stage_1_opened_values[0][0][0] += ExtVal::ONE,
        _ => proof.log_degrees[0] += 1,
      }
      record(&mut out, &system, &proof, &claims, variant == 0);
    }
  }
  if let Some(path) = std::env::var_os("IX_TRANSCRIPT_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  Ok(())
}
