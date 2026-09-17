//! A single Flock proof for the two-child relation plus explicit root claims.
//! Verification compiles the approved setup and reads no child proof or source.
use crate::{
  GrammarPairRelation, NativePairCensus,
  backend::NativeGraph,
  gates::{MACS_PER_ROW, MacGate, PackGate},
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder, SlotId},
  field::F128,
  hash::HashKind,
  lincheck::CscCircuit,
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionElementSlotInput, UnionSlotProverInput},
  r1cs_hashes::blake3 as flock_blake3,
  union::UnionInstance,
  verifier,
};
use ixby_flock::{
  hash::Blake3Gate,
  ixby::{
    io::{LayoutEmitter, PublicLayout},
    ixbf_decode::stream::batch::{CompiledGrammarBatch, GrammarBatchStatement},
  },
  sizing::{CircuitEmitter, CountingEmitter},
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

const DOMAIN: &[u8] = b"IxBy/Flock/grammar-pair/native/v0\0";
const MAGIC: [u8; 8] = *b"IXFSPR00";
const MAX_BYTES: u64 = 16 * 1024 * 1024;
#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  identity: [u8; 32],
  root_advice: Vec<F128>,
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
pub(crate) struct Slots {
  blake: SlotId,
  mac: SlotId,
  pack: SlotId,
}

#[derive(Clone, Debug)]
pub struct GrammarPairGeometry {
  pub native: NativePairCensus,
  pub row_variables: usize,
  pub dense_variables: usize,
  pub committed_lanes: Option<usize>,
  pub log_batch_size: usize,
}

pub struct CompiledGrammarPair<'a> {
  relation: GrammarPairRelation<'a>,
  shape: CircuitShape,
  slots: Slots,
  public: PublicLayout,
  params: PcsParams,
  nu: usize,
  identity: [u8; 32],
  domain: Vec<u8>,
  lincheck: CscCircuit,
}

impl ixby_stage4_exec::FlockVerifierSetup for CompiledGrammarPair<'_> {
  fn verifier_shape(&self) -> &CircuitShape {
    &self.shape
  }
  fn pcs_params(&self) -> &PcsParams {
    &self.params
  }
  fn public_template(&self) -> &PublicLayout {
    &self.public
  }
  fn transcript_domain(&self) -> Vec<u8> {
    self.domain.clone()
  }
  fn registry_digest(&self) -> [u8; 32] {
    self.shape.registry.digest()
  }
  fn circuit_digest(&self) -> [u8; 32] {
    self.shape.circuit.digest()
  }
}
impl GrammarPairRelation<'_> {
  /// Counts exactly the same emission before any permutation/witness allocation.
  pub fn geometry(&self) -> Result<GrammarPairGeometry> {
    let (_, nu, params) = count(&self.graph)?;
    Ok(GrammarPairGeometry {
      native: self.census(),
      row_variables: nu,
      dense_variables: params.m,
      committed_lanes: params.num_lanes,
      log_batch_size: params.log_batch_size,
    })
  }
}
impl<'a> CompiledGrammarPair<'a> {
  pub fn compile(child: &'a CompiledGrammarBatch) -> Result<Self> {
    let relation = GrammarPairRelation::compile(child)?;
    let (count, nu, params) = count(&relation.graph)?;
    let mut b = ShapeBuilder::new(nu);
    let (slots, public) = emit(&mut b, &relation.graph, nu)?;
    let shape =
      b.finish().map_err(|e| anyhow::anyhow!("recursive shape: {e:?}"))?;
    count.ensure_matches(&shape)?;
    let (registry, counts) = count.registry(nu);
    ensure!(
      registry.digest() == shape.registry.digest() && counts == shape.counts,
      "recursive count/shape identity"
    );
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    ensure!(
      union.dense_m() == params.m
        && union.commit_lanes(params.log_batch_size) == params.num_lanes,
      "recursive count/shape PCS"
    );
    let mut h = ::blake3::Hasher::new();
    h.update(DOMAIN);
    h.update(&relation.replay.identity());
    h.update(&shape.registry.digest());
    h.update(&shape.circuit.digest());
    h.update(&public.digest());
    h.update(&(params.m as u64).to_le_bytes());
    h.update(&(params.log_batch_size as u64).to_le_bytes());
    h.update(&[u8::from(params.num_lanes.is_some())]);
    h.update(&(params.num_lanes.unwrap_or(0) as u64).to_le_bytes());
    h.update(b"Slim128/Blake3");
    let identity = *h.finalize().as_bytes();
    let mut domain = DOMAIN.to_vec();
    domain.extend(identity);
    let ty = &shape.registry.boolean_types()[0];
    let lincheck =
      CscCircuit::from_matrices(&ty.a_0, &ty.b_0).with_const_pin(ty.const_pin);
    Ok(Self {
      relation,
      shape,
      slots,
      public,
      params,
      nu,
      identity,
      domain,
      lincheck,
    })
  }
  pub fn geometry(&self) -> GrammarPairGeometry {
    GrammarPairGeometry {
      native: self.relation.census(),
      row_variables: self.nu,
      dense_variables: self.params.m,
      committed_lanes: self.params.num_lanes,
      log_batch_size: self.params.log_batch_size,
    }
  }
  pub fn identity(&self) -> [u8; 32] {
    self.identity
  }
  /// Child proofs and endpoints are private witness inputs to the parent.
  pub fn prove(
    &self,
    statements: [&GrammarBatchStatement; 2],
    proofs: [&[u8]; 2],
  ) -> Result<Vec<u8>> {
    let left = self.relation.replay.replay(statements[0], proofs[0])?;
    let right = self.relation.replay.replay(statements[1], proofs[1])?;
    let advice = self.relation.advice([&left, &right])?;
    let (proof, commitment, outputs) = prove_native(
      &self.shape,
      &self.slots,
      &self.public,
      self.nu,
      &self.params,
      &self.lincheck,
      advice,
      &self.domain,
    )?;
    let bundle = Bundle {
      magic: MAGIC,
      identity: self.identity,
      root_advice: outputs[63..].to_vec(),
      commitment,
      proof,
    };
    let encoded = codec().serialize(&bundle)?;
    ensure!(encoded.len() as u64 <= MAX_BYTES, "recursive proof size");
    Ok(encoded)
  }
  /// Full root verification: expected source/endpoints, one parent proof and
  /// direct discharge of every child matrix/wiring/layout claim. No leaf files.
  pub fn verify(
    &self,
    expected: &GrammarBatchStatement,
    bytes: &[u8],
  ) -> Result<()> {
    ensure!(bytes.len() as u64 <= MAX_BYTES, "recursive proof size");
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC && bundle.identity == self.identity,
      "recursive proof setup/revision"
    );
    ensure!(
      bundle.root_advice.len() == self.relation.graph.published.len() - 63,
      "recursive root advice width"
    );
    ensure!(
      codec().serialize(&bundle)? == bytes,
      "noncanonical recursive proof"
    );
    let mut outputs = expected.words().to_vec();
    outputs.extend(bundle.root_advice);
    let public = self.public.instantiate(&outputs)?;
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut ch = FsChallenger::with_chained_blake3(&self.domain);
    verifier::verify_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &public,
      &[&self.lincheck],
      &bundle.commitment,
      &bundle.proof,
      &self.params,
      &mut ch,
    )
    .map_err(|e| anyhow::anyhow!("recursive Flock proof rejected: {e:?}"))?;
    self.relation.check_roots(&outputs)
  }
}

/// Shared Flock proving kernel for native recursion graphs.
#[allow(clippy::too_many_arguments)]
pub(crate) fn prove_native(
  shape: &CircuitShape,
  slots: &Slots,
  public: &PublicLayout,
  nu: usize,
  params: &PcsParams,
  lincheck: &CscCircuit,
  advice: crate::backend::NativeBuilder,
  domain: &[u8],
) -> Result<(R1csProofCircuitMerged, Commitment, Vec<F128>)> {
  let outputs = advice
    .graph
    .published
    .iter()
    .map(|&i| advice.values[i])
    .collect::<Vec<_>>();
  let expected = public.instantiate(&outputs)?;
  let witness = shape.run(&advice.values, &[]);
  ensure!(witness.public == expected, "recursive witness public vector");
  drop(advice);
  let rows = witness.rows::<Blake3Gate>(slots.blake);
  let boolean = UnionSlotProverInput::in_place(
    move |mut dst| {
      dst.elide_padding_writes = false;
      flock_blake3::generate_witness_batch_major_partial_into(rows, nu, dst)
    },
    lincheck,
  );
  let mut element = vec![
    (shape.registry_slot(slots.mac), witness.rows::<MacGate>(slots.mac)),
    (shape.registry_slot(slots.pack), witness.rows::<PackGate>(slots.pack)),
  ];
  element.sort_by_key(|(index, _)| *index);
  let element = element
    .into_iter()
    .map(|(_, rows)| {
      UnionElementSlotInput::new(move |dst| {
        dst.fill(F128::ZERO);
        for (j, row) in rows.iter().enumerate() {
          for (i, &value) in row.iter().enumerate() {
            dst[(i << nu) + j] = value;
          }
        }
      })
    })
    .collect();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let mut ch = FsChallenger::with_chained_blake3(domain);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    params,
    vec![boolean],
    element,
    &mut ch,
  );
  Ok((proof, commitment, outputs))
}

pub(crate) fn count(
  graph: &NativeGraph,
) -> Result<(CountingEmitter, usize, PcsParams)> {
  let mut count = CountingEmitter::new();
  emit(&mut count, graph, CountingEmitter::COUNT_NU)?;
  let nu = count.required_nu(1)?;
  ensure!(nu <= 18, "recursive row geometry exceeds admitted prototype");
  let (registry, counts) = count.registry(nu);
  let union = UnionInstance::new(&registry, counts);
  let m = union.dense_m();
  ensure!((22..=35).contains(&m), "recursive PCS outside pinned profiles");
  let profile = LigeritoProfile::Slim128;
  let log_batch_size = embedded_initial_k_or_default(m, profile);
  let params = PcsParams {
    m,
    profile,
    log_batch_size,
    log_inv_rate: profile.log_inv_rate(),
    num_lanes: union.commit_lanes(log_batch_size),
    merkle_hash: HashKind::Blake3,
  };
  Ok((count, nu, params))
}

pub(crate) fn emit(
  b: &mut impl CircuitEmitter,
  graph: &NativeGraph,
  nu: usize,
) -> Result<(Slots, PublicLayout)> {
  emit_inner(b, graph, nu, false)
}

/// Keep shared wire classes as union roots. Moving a growing cell list into
/// each new equality makes setup quadratic in its fanout.
/// The original pair emitter retains its established permutation identity.
pub(crate) fn emit_stable(
  b: &mut impl CircuitEmitter,
  graph: &NativeGraph,
  nu: usize,
) -> Result<(Slots, PublicLayout)> {
  emit_inner(b, graph, nu, true)
}

fn emit_inner(
  b: &mut impl CircuitEmitter,
  graph: &NativeGraph,
  nu: usize,
  stable_roots: bool,
) -> Result<(Slots, PublicLayout)> {
  let mut b = LayoutEmitter::new(b);
  let slots = Slots {
    blake: b.slot(Blake3Gate { nu }),
    mac: b.slot(MacGate),
    pack: b.slot(PackGate),
  };
  let constants = graph.constants.iter().copied().collect::<HashMap<_, _>>();
  let wires = (0..graph.variables)
    .map(|i| {
      if let Some(&value) = constants.get(&i) {
        b.fixed_public_input(value)
      } else {
        b.input()
      }
    })
    .collect::<Vec<_>>();
  let zero = graph
    .constants
    .iter()
    .find(|(_, value)| *value == F128::ZERO)
    .map(|(i, _)| wires[*i])
    .expect("native zero wire");
  for chunk in graph.macs.chunks(MACS_PER_ROW) {
    let mut row = vec![zero; 4 * MACS_PER_ROW];
    for (target, equation) in row.as_chunks_mut::<4>().0.iter_mut().zip(chunk) {
      for (target, &source) in target.iter_mut().zip(equation) {
        *target = wires[source];
      }
    }
    b.gate(slots.mac, &row);
  }
  for row in &graph.packs {
    b.gate(slots.pack, &row.iter().map(|&i| wires[i]).collect::<Vec<_>>());
  }
  for (input, expected) in &graph.compressions {
    let actual = b.gate(slots.blake, &input.map(|i| wires[i]));
    for (&actual, &expected) in actual.iter().zip(expected) {
      if stable_roots {
        b.connect(wires[expected], actual);
      } else {
        b.connect(actual, wires[expected]);
      }
    }
  }
  if stable_roots {
    // ShapeBuilder's connect moves the second class into the first without
    // union by size. Track class sizes here so each cell moves O(log N)
    // times, including the heavily shared zero and one classes.
    let mut parents = (0..graph.variables).collect::<Vec<_>>();
    let mut sizes = vec![1usize; graph.variables];
    fn root(parents: &mut [usize], mut i: usize) -> usize {
      while parents[i] != i {
        parents[i] = parents[parents[i]];
        i = parents[i];
      }
      i
    }
    for &(a, c) in &graph.equalities {
      let mut a = root(&mut parents, a);
      let mut c = root(&mut parents, c);
      if a == c {
        continue;
      }
      if sizes[a] < sizes[c] {
        std::mem::swap(&mut a, &mut c);
      }
      b.connect(wires[a], wires[c]);
      parents[c] = a;
      sizes[a] += sizes[c];
    }
  } else {
    for &(a, c) in &graph.equalities {
      b.connect(wires[a], wires[c]);
    }
  }
  for &i in &graph.published {
    b.publish(wires[i]);
  }
  let (_, public) = b.finish();
  Ok((slots, public))
}

#[cfg(test)]
mod tests {
  use super::*;
  use ixby_flock::ixby::ixbf_decode::GrammarKind;
  use std::{
    io::{Read, Write},
    path::PathBuf,
    time::Instant,
  };

  fn read_bounded(path: &std::path::Path, limit: u64) -> Vec<u8> {
    let mut bytes = Vec::new();
    std::fs::File::open(path)
      .unwrap()
      .take(limit + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(bytes.len() as u64 <= limit);
    bytes
  }
  fn write_new(path: &std::path::Path, bytes: &[u8]) {
    std::fs::OpenOptions::new()
      .create_new(true)
      .write(true)
      .open(path)
      .unwrap()
      .write_all(bytes)
      .unwrap();
  }
  fn expected(path: &std::path::Path) -> GrammarBatchStatement {
    let bytes = read_bounded(path, 63 * 16);
    assert_eq!(bytes.len(), 63 * 16);
    let words = bytes
      .as_chunks::<16>()
      .0
      .iter()
      .map(|word| ixby_flock::hash::pack_bytes(word))
      .collect::<Vec<_>>();
    GrammarBatchStatement::from_words(&words).unwrap()
  }

  #[test]
  #[ignore = "requires IXBY_PAIR_ROOT and IXBY_PAIR_EXPECTED retained artifacts"]
  fn retained_parent_has_proof_free_mixed_replay() {
    let child = CompiledGrammarBatch::compile(GrammarKind::Program).unwrap();
    let compiled = CompiledGrammarPair::compile(&child).unwrap();
    let replay = ixby_stage4_exec::compile_flock_replay(&compiled).unwrap();
    let mut empty = crate::backend::NativeBuilder::new(true);
    crate::pair::emit_child(&mut empty, &replay, None).unwrap();
    eprintln!(
      "mixed proof-free verifier: identity={} variables={} macs={} packs={} compressions={}",
      ::blake3::Hash::from(replay.identity()),
      empty.graph.variables,
      empty.graph.macs.len(),
      empty.graph.packs.len(),
      empty.graph.compressions.len()
    );
    // The compiled topology above precedes all proof and statement reads.
    let path = PathBuf::from(std::env::var_os("IXBY_PAIR_ROOT").unwrap());
    let statement =
      PathBuf::from(std::env::var_os("IXBY_PAIR_EXPECTED").unwrap());
    let statement = expected(&statement);
    let bytes = read_bounded(&path, MAX_BYTES);
    compiled.verify(&statement, &bytes).unwrap();
    let bundle: Bundle = codec().deserialize(&bytes).unwrap();
    let mut outputs = statement.words().to_vec();
    outputs.extend(bundle.root_advice);
    let public = compiled.public.instantiate(&outputs).unwrap();
    let witness =
      replay.replay_proof(&public, &bundle.commitment, &bundle.proof).unwrap();
    let mut actual = crate::backend::NativeBuilder::new(false);
    let wires =
      crate::pair::emit_child(&mut actual, &replay, Some(&witness)).unwrap();
    assert_eq!(actual.graph, empty.graph);
    actual.check().unwrap();
    assert_eq!(wires.application.len(), outputs.len());
    for (wire, value) in wires.application.iter().zip(&outputs) {
      let index = wire.word(&mut actual);
      assert_eq!(actual.values[index], *value);
    }
    assert_eq!(wires.multipoint.jagged_assertion.claims.len(), 5);
    eprintln!("retained mixed parent replay: all native constraints satisfied");
  }

  #[test]
  #[ignore = "requires retained CSLib frames and IXBY_PAIR_PROOF_OUT"]
  fn retained_pair_proves_one_flock_root() {
    let child = CompiledGrammarBatch::compile(GrammarKind::Program).unwrap();
    let started = Instant::now();
    let compiled = CompiledGrammarPair::compile(&child).unwrap();
    eprintln!(
      "pair compiled in {:?}; geometry {:?}; identity {}",
      started.elapsed(),
      compiled.geometry(),
      ::blake3::Hash::from(compiled.identity())
    );
    let directory =
      PathBuf::from(std::env::var_os("IXBY_CSLIB_FRAME_DIR").unwrap());
    let root = ::blake3::Hash::from_hex(
      "f2f6da19991985ba4575773a62943b213d94f3678c5b95f85fb9af1025fd26d1",
    )
    .unwrap();
    let length = 1_016_587;
    let mut state = [F128::ZERO; 30];
    state[0] = F128::new(0, length);
    let mut statements = Vec::new();
    let mut proofs = Vec::new();
    for i in 0..2 {
      let frame = read_bounded(
        &directory.join(format!("program-{i:06}.frame")),
        8 * 1024 * 1024,
      );
      let size = u32::from_le_bytes(frame[..4].try_into().unwrap()) as usize;
      assert_eq!(frame.len(), 4 + 480 + size);
      let end = std::array::from_fn(|i| {
        ixby_flock::hash::pack_bytes(&frame[4 + 16 * i..4 + 16 * i + 16])
      });
      statements.push(
        GrammarBatchStatement::new(length, *root.as_bytes(), state, end)
          .unwrap(),
      );
      proofs.push(frame[484..].to_vec());
      state = end;
    }
    let expected = GrammarBatchStatement::new(
      length,
      *root.as_bytes(),
      *statements[0].initial(),
      *statements[1].final_state(),
    )
    .unwrap();
    let started = Instant::now();
    let proof = compiled
      .prove([&statements[0], &statements[1]], [&proofs[0], &proofs[1]])
      .unwrap();
    eprintln!(
      "pair proved one Flock root in {:?}; {} bytes including root advice",
      started.elapsed(),
      proof.len()
    );
    let output =
      PathBuf::from(std::env::var_os("IXBY_PAIR_PROOF_OUT").unwrap());
    let expected_path = output.with_extension("statement");
    let statement = expected
      .words()
      .iter()
      .flat_map(|&v| crate::f128::bytes(v))
      .collect::<Vec<_>>();
    write_new(&output, &proof);
    write_new(&expected_path, &statement);
    drop(compiled);
    drop(child);
    drop(proofs);
    drop(statements);
    let receiver = std::process::Command::new(std::env::current_exe().unwrap())
      .arg("--exact")
      .arg("proof::tests::root_receiver")
      .arg("--ignored")
      .arg("--nocapture")
      .env_clear()
      .env("RAYON_NUM_THREADS", "4")
      .env("IXBY_PAIR_ROOT", &output)
      .env("IXBY_PAIR_EXPECTED", &expected_path)
      .output()
      .unwrap();
    eprintln!("{}", String::from_utf8_lossy(&receiver.stdout));
    eprintln!("{}", String::from_utf8_lossy(&receiver.stderr));
    assert!(receiver.status.success(), "fresh root verifier rejected");
  }

  #[test]
  #[ignore = "fresh process receiver: only root proof and externally expected statement"]
  fn root_receiver() {
    let output = PathBuf::from(std::env::var_os("IXBY_PAIR_ROOT").unwrap());
    let expected_path =
      PathBuf::from(std::env::var_os("IXBY_PAIR_EXPECTED").unwrap());
    let expected = expected(&expected_path);
    let proof = read_bounded(&output, MAX_BYTES);
    let child = CompiledGrammarBatch::compile(GrammarKind::Program).unwrap();
    let compiled = CompiledGrammarPair::compile(&child).unwrap();
    let started = Instant::now();
    compiled.verify(&expected, &proof).unwrap();
    eprintln!(
      "fresh single-root verification {:?}; no leaf proofs supplied",
      started.elapsed()
    );
    let mut words = *expected.words();
    words[1] += F128::ONE;
    assert!(
      compiled
        .verify(&GrammarBatchStatement::from_words(&words).unwrap(), &proof)
        .is_err()
    );
    let mut words = *expected.words();
    words[3 + 29] += F128::ONE;
    assert!(
      compiled
        .verify(&GrammarBatchStatement::from_words(&words).unwrap(), &proof)
        .is_err()
    );
    let mut bundle: Bundle = codec().deserialize(&proof).unwrap();
    bundle.root_advice[0] += F128::ONE;
    assert!(
      compiled.verify(&expected, &codec().serialize(&bundle).unwrap()).is_err()
    );
    let mut damaged = proof.clone();
    let last = damaged.len() - 1;
    damaged[last] ^= 1;
    assert!(compiled.verify(&expected, &damaged).is_err());
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(compiled.verify(&expected, &trailing).is_err());
    assert!(compiled.verify(&expected, &proof[..proof.len() - 1]).is_err());
  }
}
