//! Private component envelope, not a new Exec profile. A fresh verifier has
//! only the externally expected raw digest, query/metadata and proof. Native
//! bytes, path preparation and header evaluation are exclusively prover/test
//! helpers. No existing proof format or transcript has a fallback to this one.
use super::super::{HEADER_PREFIX_BYTES, HeaderDecodeGate, HeaderDecodeSlot};
use super::{
  SourceBlockGate, SourceCapacity, SourcePathGate, SourceReadSlots,
  SourceWindowGate,
  tests::{ChunkAdvice, NativeTree, digest, pattern, proof_wires, words},
};
use crate::{
  blake3_backend::Blake3CompressionSlots,
  hash::Blake3Gate,
  ixby::{
    io::{InputLayout, LayoutEmitter, PublicLayout},
    select::SelectWordsGate,
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{
    CircuitShape, CircuitWitness, GateType, ShapeBuilder, SlotId,
  },
  field::F128,
  hash::HashKind,
  lincheck::LincheckCircuit,
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  r1cs::BlockR1cs,
  r1cs_hashes::blake3 as flock_blake3,
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

const NU: usize = 7;
const DEPTH: usize = 14;
const MAGIC: [u8; 8] = *b"IXFSRC00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD: &str = "IXBY_SOURCE_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::source::proof_tests::source_proofs_verify_without_source_and_reject_recomputed_substitutions";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Component {
  Read32,
  Header,
}
impl Component {
  fn tag(self) -> u8 {
    match self {
      Self::Read32 => 0,
      Self::Header => 1,
    }
  }
  fn from_tag(tag: u8) -> Result<Self> {
    match tag {
      0 => Ok(Self::Read32),
      1 => Ok(Self::Header),
      _ => anyhow::bail!("unknown source component"),
    }
  }
  fn window(self) -> usize {
    match self {
      Self::Read32 => 32,
      Self::Header => HEADER_PREFIX_BYTES,
    }
  }
  fn outputs(self) -> usize {
    match self {
      Self::Read32 => 6,
      Self::Header => 18,
    }
  }
  fn domain(self) -> &'static [u8] {
    match self {
      Self::Read32 => b"ix:ixby:ixbf-source-read32:d14:v0",
      Self::Header => b"ix:ixby:ixbf-source-header:d14:v0",
    }
  }
}

struct Setup {
  shape: CircuitShape,
  inputs: InputLayout,
  public: PublicLayout,
  drivers: Vec<Driver>,
  tables: Vec<BlockR1cs>,
}
enum Driver {
  Window(SlotId, SourceWindowGate),
  Block(SlotId, SourceBlockGate),
  Path(SlotId, SourcePathGate),
  Select(SlotId, SelectWordsGate),
  Compression(SlotId),
  Header(SlotId, HeaderDecodeGate),
}
impl Driver {
  fn slot(&self) -> SlotId {
    match self {
      Self::Window(s, _)
      | Self::Block(s, _)
      | Self::Path(s, _)
      | Self::Select(s, _)
      | Self::Compression(s)
      | Self::Header(s, _) => *s,
    }
  }
  fn r1cs(&self) -> BlockR1cs {
    match self {
      Self::Window(_, g) => g.r1cs(),
      Self::Block(_, g) => g.r1cs(),
      Self::Path(_, g) => g.r1cs(),
      Self::Select(_, g) => g.r1cs(),
      Self::Compression(_) => flock_blake3::build_block_r1cs(NU),
      Self::Header(_, g) => g.r1cs(),
    }
  }
  fn prover<'a>(
    &'a self,
    witness: &'a CircuitWitness,
    circuit: &'a dyn LincheckCircuit,
    attack: Attack,
    compression_slot: SlotId,
  ) -> UnionSlotProverInput<'a> {
    match self {
      Self::Window(slot, gate) => {
        let mut rows = witness.rows::<SourceWindowGate>(*slot).to_vec();
        if attack == Attack::WindowByte {
          let old = super::window::evaluate(gate.capacity(), &rows[0].0);
          // Offset 1023: byte zero is outside the requested window. Public
          // output and all metadata remain unchanged; only shared hash inputs
          // distinguish this locally valid source substitution.
          assert_eq!(rows[0].0[0].lo, 1023);
          rows[0].0[2].lo ^= 1;
          assert_eq!(super::window::evaluate(gate.capacity(), &rows[0].0), old);
          assert_eq!(old.last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Block(slot, gate) => {
        let mut rows = witness.rows::<SourceBlockGate>(*slot).to_vec();
        if attack == Attack::BlockLength {
          let old = super::block::evaluate(DEPTH, &rows[0].0);
          rows[0].0[0].lo += 1;
          assert_eq!(super::block::evaluate(DEPTH, &rows[0].0), old);
          assert_eq!(old.last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Path(slot, gate) => {
        let mut rows = witness.rows::<SourcePathGate>(*slot).to_vec();
        if attack == Attack::PathSibling {
          rows[0].0[5].lo ^= 1;
          assert_eq!(
            super::path::evaluate(DEPTH, &rows[0].0).last(),
            Some(&F128::ZERO)
          );
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Select(slot, gate) => {
        let mut rows = witness.rows::<SelectWordsGate>(*slot).to_vec();
        if attack == Attack::SkipChunkBlock {
          let compression = witness.rows::<Blake3Gate>(compression_slot);
          let (cv, message, counter, len, flags) = compression[0];
          let output =
            flock_blake3::blake3_compress(&cv, &message, counter, len, flags);
          let mut input = vec![F128::ZERO];
          input.extend(crate::hash::pack8(&output[..8].try_into().unwrap()));
          input.extend(crate::hash::pack8(&cv));
          let mut out = Vec::new();
          rows[0] = gate.eval(&input, &(), &mut out);
          assert_eq!(out.last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
      Self::Compression(slot) => {
        let mut rows = witness.rows::<Blake3Gate>(*slot).to_vec();
        if attack == Attack::CompressionCounter {
          rows[0].2 += 1;
        }
        if attack == Attack::CompressionRootFlag {
          rows[0].4 ^= crate::hash::ROOT;
        }
        UnionSlotProverInput::in_place(
          move |mut dst| {
            dst.elide_padding_writes = false;
            flock_blake3::generate_witness_batch_major_partial_into(
              &rows, NU, dst,
            )
          },
          circuit,
        )
      },
      Self::Header(slot, gate) => {
        let mut rows = witness.rows::<HeaderDecodeGate>(*slot).to_vec();
        if attack == Attack::HeaderBodyByte {
          let old = super::super::header::evaluate(&rows[0].0);
          let byte = old[13].lo as usize;
          assert!(
            byte < HEADER_PREFIX_BYTES && (byte as u64) < rows[0].0[0].lo
          );
          let word = &mut rows[0].0[1 + byte / 16];
          if byte % 16 < 8 {
            word.lo ^= 1 << (8 * (byte % 8));
          } else {
            word.hi ^= 1 << (8 * (byte % 8));
          }
          assert_eq!(super::super::header::evaluate(&rows[0].0), old);
          assert_eq!(old.last(), Some(&F128::ZERO));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          circuit,
        )
      },
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  WindowByte,
  BlockLength,
  PathSibling,
  SkipChunkBlock,
  CompressionCounter,
  CompressionRootFlag,
  HeaderBodyByte,
}

fn setup(component: Component) -> Setup {
  let mut builder = ShapeBuilder::new(NU);
  let mut b = LayoutEmitter::new(&mut builder);
  let slots = SourceReadSlots::declare(
    &mut b,
    NU,
    SourceCapacity::new(DEPTH, component.window()).unwrap(),
  )
  .unwrap();
  let root = [b.input(), b.input()];
  let cursor = b.input();
  let take = b.input();
  let proofs: [_; 3] = std::array::from_fn(|_| proof_wires(&mut b, DEPTH));
  let out = slots.read(&mut b, cursor, take, root, &proofs);
  for wire in [root[0], root[1], cursor, take] {
    b.publish(wire);
  }
  let mut drivers = vec![
    Driver::Window(slots.window_gate().0, slots.window_gate().1.clone()),
    Driver::Block(slots.block_gate().0, slots.block_gate().1.clone()),
    Driver::Path(slots.path_gate().0, slots.path_gate().1.clone()),
  ];
  let (slot, gate) = slots.select_gate();
  drivers.push(Driver::Select(slot, gate.clone()));
  let Blake3CompressionSlots::LegacyOptionF { slot, .. } = slots.compression()
  else {
    panic!("explicit legacy source proof backend")
  };
  drivers.push(Driver::Compression(*slot));
  match component {
    Component::Read32 => {
      for word in out.words {
        b.publish(word);
      }
    },
    Component::Header => {
      let gate = HeaderDecodeGate::new(NU).unwrap();
      let slot = HeaderDecodeSlot::declare(&mut b, gate.clone());
      let header = slot.decode(&mut b, out.file_length, &out.words);
      for limit in header.limits {
        b.publish(limit);
      }
      for word in [
        header.max_steps,
        header.entry,
        header.constructor_count,
        header.constructors_offset,
      ] {
        b.publish(word);
      }
      drivers.push(Driver::Header(slot.slot(), gate));
    },
  }
  let (inputs, public) = b.finish();
  let shape = builder.finish().unwrap();
  assert_eq!(public.outputs(), component.outputs());
  drivers.sort_by_key(|driver| shape.registry_slot(driver.slot()));
  for (index, driver) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(driver.slot()), index);
  }
  let tables = drivers.iter().map(Driver::r1cs).collect();
  Setup { shape, inputs, public, drivers, tables }
}

#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  component: u8,
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
fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert!((22..=35).contains(&m), "unchanged pinned PCS geometry");
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
  component: Component,
  setup: &Setup,
  witness: &CircuitWitness,
  expected: &[F128],
  attack: Attack,
) -> Vec<u8> {
  let compression_slot = setup
    .drivers
    .iter()
    .find_map(|driver| match driver {
      Driver::Compression(slot) => Some(*slot),
      _ => None,
    })
    .unwrap();
  let slots = setup
    .drivers
    .iter()
    .zip(&setup.tables)
    .map(|(driver, table)| {
      driver.prover(
        witness,
        table.csc_lincheck_circuit(),
        attack,
        compression_slot,
      )
    })
    .collect();
  prove_rows(component, setup, expected, slots)
}

fn prove_rows(
  component: Component,
  setup: &Setup,
  expected: &[F128],
  slots: Vec<UnionSlotProverInput<'_>>,
) -> Vec<u8> {
  let public = setup.public.instantiate(expected).unwrap();
  let union =
    UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
  let mut challenger = FsChallenger::with_chained_blake3(component.domain());
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &setup.shape.circuit,
    &public,
    &params(&union),
    slots,
    Vec::new(),
    &mut challenger,
  );
  codec()
    .serialize(&Bundle {
      magic: MAGIC,
      component: component.tag(),
      commitment,
      proof,
    })
    .unwrap()
}
fn verify(
  component: Component,
  expected: &[F128],
  bytes: &[u8],
  domain: &[u8],
) -> Result<()> {
  ensure!(expected.len() == component.outputs(), "source public ABI length");
  if component == Component::Header {
    ensure!(
      expected[2].lo == 0
        && expected[3] == F128::new(HEADER_PREFIX_BYTES as u64, 0),
      "header query must cover the original file prefix"
    );
  }
  ensure!(bytes.len() as u64 <= MAX_BYTES, "source proof byte limit");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.component == component.tag(),
    "source proof kind or revision"
  );
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical source proof");
  let setup = setup(component);
  let public = setup.public.instantiate(expected)?;
  let union =
    UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
  let circuits: Vec<&dyn LincheckCircuit> = setup
    .tables
    .iter()
    .map(|t| t.csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect();
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &setup.shape.circuit,
    &public,
    &circuits,
    &bundle.commitment,
    &bundle.proof,
    &params(&union),
    &mut challenger,
  )
  .map_err(|error| anyhow::anyhow!("source proof rejected: {error:?}"))?;
  Ok(())
}

fn isolated(component: Component, expected: &[F128], proof: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut input = child.stdin.take().unwrap();
  input.write_all(&[component.tag()]).unwrap();
  for word in expected {
    input.write_all(&word.lo.to_le_bytes()).unwrap();
    input.write_all(&word.hi.to_le_bytes()).unwrap();
  }
  input.write_all(proof).unwrap();
  drop(input);
  let output = child.wait_with_output().unwrap();
  if !output.status.success() {
    eprintln!(
      "fresh source verifier rejected: {}",
      String::from_utf8_lossy(&output.stderr)
    );
  }
  output.status.success()
}
fn child() -> Result<()> {
  let mut input = Vec::new();
  std::io::stdin().take(MAX_BYTES + 4097).read_to_end(&mut input)?;
  let component = Component::from_tag(
    *input
      .first()
      .ok_or_else(|| anyhow::anyhow!("missing source component"))?,
  )?;
  let prefix = 1 + 16 * component.outputs();
  ensure!(
    (prefix..=prefix + MAX_BYTES as usize).contains(&input.len()),
    "source verifier input length"
  );
  let expected = words(&input[1..prefix]);
  verify(component, &expected, &input[prefix..], component.domain())
}

fn private(
  root: [F128; 2],
  offset: u64,
  length: u64,
  take: usize,
  proofs: &[ChunkAdvice; 3],
) -> Vec<F128> {
  let mut input = root.to_vec();
  input.extend([F128::new(offset, length), F128::new(take as u64, 0)]);
  for proof in proofs {
    input.extend(proof.inputs());
  }
  input
}

/// Malicious advice must also be tested below the honest runner, which
/// correctly refuses contradictory root equalities before proving. These
/// rows recompute every local output, with no inconsistent local relation.
fn false_length_proof(
  setup: &Setup,
  expected: &[F128],
  proofs: &[ChunkAdvice; 3],
) -> Vec<u8> {
  fn record<G: GateType<Hint = ()>>(
    gate: &G,
    rows: &mut Vec<G::Row>,
    input: &[F128],
  ) -> Vec<F128> {
    let mut output = Vec::new();
    rows.push(gate.eval(input, &(), &mut output));
    output
  }
  use crate::hash::{IV, pack8};
  let window =
    SourceWindowGate::new(NU, SourceCapacity::new(DEPTH, 32).unwrap()).unwrap();
  let block = SourceBlockGate::new(NU, DEPTH).unwrap();
  let path = SourcePathGate::new(NU, DEPTH).unwrap();
  let select = SelectWordsGate::new(NU, 2).unwrap();
  let compression = Blake3Gate { nu: NU };
  let mut windows = Vec::new();
  let mut blocks = Vec::new();
  let mut paths = Vec::new();
  let mut selects = Vec::new();
  let mut compressions = Vec::new();
  let mut input = vec![expected[2], expected[3]];
  input.extend(proofs[0].bytes);
  input.extend(proofs[1].bytes);
  let metadata = record(&window, &mut windows, &input);
  assert_eq!(metadata.last(), Some(&F128::ZERO));
  assert_eq!(&metadata[4..6], &expected[4..6]);
  let mut roots = Vec::new();
  for (index, proof) in metadata[1..4].iter().zip(proofs) {
    let mut cv = pack8(&IV);
    for position in 0..16 {
      let message = &proof.bytes[4 * position..4 * position + 4];
      let mut input = vec![metadata[0], *index, F128::new(position as u64, 0)];
      input.extend_from_slice(message);
      let control = record(&block, &mut blocks, &input);
      assert_eq!(control[2], F128::ZERO);
      let mut input = cv.to_vec();
      input.extend_from_slice(message);
      input.push(control[0]);
      let candidate = record(&compression, &mut compressions, &input);
      let output = record(
        &select,
        &mut selects,
        &[control[1], candidate[0], candidate[1], cv[0], cv[1]],
      );
      assert_eq!(output[2], F128::ZERO);
      cv.copy_from_slice(&output[..2]);
    }
    for level in 0..DEPTH {
      let control = record(
        &path,
        &mut paths,
        &[
          metadata[0],
          *index,
          F128::new(level as u64, 0),
          cv[0],
          cv[1],
          proof.siblings[level][0],
          proof.siblings[level][1],
        ],
      );
      assert_eq!(control[6], F128::ZERO);
      let mut input = pack8(&IV).to_vec();
      input.extend_from_slice(&control[..5]);
      let candidate = record(&compression, &mut compressions, &input);
      let output = record(
        &select,
        &mut selects,
        &[control[5], candidate[0], candidate[1], cv[0], cv[1]],
      );
      assert_eq!(output[2], F128::ZERO);
      cv.copy_from_slice(&output[..2]);
    }
    roots.push(cv);
  }
  assert_eq!(roots[0], expected[..2]);
  assert_eq!(roots[1], expected[..2]);
  assert_ne!(roots[2], expected[..2]);
  let slots = setup
    .drivers
    .iter()
    .zip(&setup.tables)
    .map(|(driver, table)| {
      let circuit = table.csc_lincheck_circuit();
      match driver {
        Driver::Window(_, gate) => UnionSlotProverInput::in_place(
          |dst| gate.generate_witness_into(&windows, dst),
          circuit,
        ),
        Driver::Block(_, gate) => UnionSlotProverInput::in_place(
          |dst| gate.generate_witness_into(&blocks, dst),
          circuit,
        ),
        Driver::Path(_, gate) => UnionSlotProverInput::in_place(
          |dst| gate.generate_witness_into(&paths, dst),
          circuit,
        ),
        Driver::Select(_, gate) => UnionSlotProverInput::in_place(
          |dst| gate.generate_witness_into(&selects, dst),
          circuit,
        ),
        Driver::Compression(_) => UnionSlotProverInput::in_place(
          |mut dst| {
            dst.elide_padding_writes = false;
            flock_blake3::generate_witness_batch_major_partial_into(
              &compressions,
              NU,
              dst,
            )
          },
          circuit,
        ),
        Driver::Header(_, _) => {
          panic!("false-length test uses the read-only component")
        },
      }
    })
    .collect();
  prove_rows(Component::Read32, setup, expected, slots)
}

fn expected(
  component: Component,
  bytes: &[u8],
  offset: u64,
  take: usize,
) -> Vec<F128> {
  let mut output = digest(bytes).to_vec();
  output
    .extend([F128::new(offset, bytes.len() as u64), F128::new(take as u64, 0)]);
  match component {
    Component::Read32 => {
      let mut window = [0; 32];
      let count = take.min(bytes.len() - offset as usize);
      window[..count]
        .copy_from_slice(&bytes[offset as usize..offset as usize + count]);
      output.extend(words(&window));
    },
    Component::Header => {
      assert_eq!(offset, 0);
      assert_eq!(take, HEADER_PREFIX_BYTES);
      // Independent native fixture preparation, not a verifier acceptance gate.
      let input = super::super::header_tests::input(bytes, bytes.len() as u64);
      let fields = super::super::header::evaluate(&input);
      assert_eq!(fields.last(), Some(&F128::ZERO));
      output.extend_from_slice(&fields[..14]);
    },
  }
  output
}
fn check_fixture(
  component: Component,
  bytes: Vec<u8>,
  offset: u64,
  take: usize,
  attacks: &[Attack],
) {
  let setup = setup(component);
  let expected = expected(component, &bytes, offset, take);
  let tree = NativeTree::new(bytes);
  let proofs = tree.read_advice(DEPTH, offset);
  let input = private(
    digest(&tree.bytes),
    offset,
    tree.bytes.len() as u64,
    take,
    &proofs,
  );
  let witness = setup.shape.run(&setup.inputs.assign(&input).unwrap(), &[]);
  assert_eq!(witness.public, setup.public.instantiate(&expected).unwrap());
  let proof = prove(component, &setup, &witness, &expected, Attack::None);
  assert!(isolated(component, &expected, &proof));
  eprintln!(
    "source component {component:?}: {} proof bytes; source_bytes={}; offset={offset}; take={take}; public_words={}; m={}",
    proof.len(),
    tree.bytes.len(),
    expected.len(),
    params(&UnionInstance::new(
      &setup.shape.registry,
      setup.shape.counts.clone()
    ))
    .m
  );
  for &attack in attacks {
    let forged = prove(component, &setup, &witness, &expected, attack);
    assert!(!isolated(component, &expected, &forged), "accepted {attack:?}");
    eprintln!("source rejected recomputed {attack:?}");
  }
  // Exercise the complete public/envelope mutation matrix on one fixture
  // per component; the remaining fixtures test independent honest paths.
  if attacks.is_empty() {
    return;
  }
  for index in [0, 1, 2, 3, expected.len() - 1] {
    for high in [false, true] {
      let mut changed = expected.clone();
      if high {
        changed[index].hi ^= 1 << 63;
      } else {
        changed[index].lo ^= 1;
      }
      assert!(verify(component, &changed, &proof, component.domain()).is_err());
    }
  }
  let mut changed = proof.clone();
  changed[0] ^= 1;
  assert!(verify(component, &expected, &changed, component.domain()).is_err());
  changed = proof.clone();
  changed[8] ^= 1;
  assert!(verify(component, &expected, &changed, component.domain()).is_err());
  changed = proof.clone();
  changed.push(0);
  assert!(verify(component, &expected, &changed, component.domain()).is_err());
  assert!(
    verify(component, &expected, &proof[..proof.len() - 1], component.domain())
      .is_err()
  );
  assert!(
    verify(component, &expected, &proof, b"ix:ixby:ixbf-header-codec:v0")
      .is_err()
  );
}

#[test]
fn source_expected_layout_and_header_consumer_are_image_independent() {
  for component in [Component::Read32, Component::Header] {
    let setup = setup(component);
    assert_eq!(setup.inputs.private_words(), 4 + 3 * (64 + 2 * DEPTH));
    let template = setup.public.digest();
    let identity = setup.shape.circuit.digest();
    let (_, header) = super::super::header_tests::fixture();
    let mut extended = header.clone();
    extended.resize(4097, 0x59);
    let images = if component == Component::Read32 {
      vec![vec![], pattern(2049)]
    } else {
      vec![header, extended]
    };
    for bytes in images {
      let offset = if component == Component::Read32 && !bytes.is_empty() {
        1023
      } else {
        0
      };
      let take = component.window();
      let expected = expected(component, &bytes, offset, take);
      let tree = NativeTree::new(bytes);
      let proofs = tree.read_advice(DEPTH, offset);
      let input = private(
        digest(&tree.bytes),
        offset,
        tree.bytes.len() as u64,
        take,
        &proofs,
      );
      let witness = setup.shape.run(&setup.inputs.assign(&input).unwrap(), &[]);
      assert_eq!(witness.public, setup.public.instantiate(&expected).unwrap());
      assert_eq!(setup.public.digest(), template);
      assert_eq!(setup.shape.circuit.digest(), identity);
    }
  }
}

#[test]
#[ignore = "real source proofs and fresh no-source verifier with adversarial recomputation"]
fn source_proofs_verify_without_source_and_reject_recomputed_substitutions() {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  for (length, offset, take) in [
    (0, 0, 32),
    (1, 0, 1),
    (1024, 1024, 32),
    (1025, 1023, 32),
    (5121, 4095, 32),
    (8192, 1023, 32),
  ] {
    let attacks: &[Attack] = if length == 8192 {
      &[
        Attack::WindowByte,
        Attack::BlockLength,
        Attack::PathSibling,
        Attack::SkipChunkBlock,
        Attack::CompressionCounter,
        Attack::CompressionRootFlag,
      ]
    } else {
      &[]
    };
    check_fixture(Component::Read32, pattern(length), offset, take, attacks);
  }
  let (_, header) = super::super::header_tests::fixture();
  check_fixture(
    Component::Header,
    header.clone(),
    0,
    HEADER_PREFIX_BYTES,
    &[Attack::HeaderBodyByte],
  );
  let mut multi = header;
  multi.resize(5121, 0x5a);
  check_fixture(Component::Header, multi, 0, HEADER_PREFIX_BYTES, &[]);

  let tree = NativeTree::new(pattern(8192));
  let root = digest(&tree.bytes);
  let mut proofs =
    [tree.proof(0, DEPTH), tree.proof(1, DEPTH), tree.proof(4, DEPTH)];
  proofs[2].siblings[0] = [F128::ZERO; 2];
  proofs[2].siblings[1] = [F128::ZERO; 2];
  for (index, p) in [0, 1, 4].into_iter().zip(&proofs) {
    let (candidate, valid) = super::tests::chunk_root(DEPTH, 5120, index, p);
    assert!(valid);
    if index != 4 {
      assert_eq!(candidate, root);
    } else {
      assert_ne!(candidate, root);
    }
  }
  let setup = setup(Component::Read32);
  let mut expected = expected(Component::Read32, &tree.bytes, 0, 32);
  expected[2].hi = 5120;
  let proof = false_length_proof(&setup, &expected, &proofs);
  assert!(!isolated(Component::Read32, &expected, &proof));
  eprintln!(
    "source rejected recomputed false file length: first and next paths valid, final-root binding fails"
  );
}

#[test]
#[ignore = "retained original Init/program/transport source membership proofs"]
fn original_init_header_and_transport_windows_authenticate_to_original_digests()
{
  use super::super::external_tests::{expected_header, path, read};
  let program = read(&path("IXBY_IXBF_STAGE2_IMAGE"));
  let artifact = crate::ixby::ixbf::decode_program(
    &program,
    crate::ixby::ixbf::DecodeLimits::default(),
  )
  .unwrap();
  assert_eq!(
    &expected(Component::Header, &program, 0, HEADER_PREFIX_BYTES)[4..],
    expected_header(&artifact)
  );
  eprintln!(
    "original authenticated Init program: {} bytes; BLAKE3={}",
    program.len(),
    blake3::hash(&program)
  );
  check_fixture(
    Component::Header,
    program.clone(),
    0,
    HEADER_PREFIX_BYTES,
    &[],
  );
  let end = program.len() as u64;
  check_fixture(Component::Read32, program, end - 17, 32, &[]);
  for variable in ["IXBY_IXBF_INIT_INPUT", "IXBY_IXBF_INIT_OUTPUT"] {
    let bytes = read(&path(variable));
    eprintln!(
      "original authenticated {variable}: {} bytes; BLAKE3={}",
      bytes.len(),
      blake3::hash(&bytes)
    );
    check_fixture(Component::Read32, bytes, 0, 32, &[]);
  }
}
