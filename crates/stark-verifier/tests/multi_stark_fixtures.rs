//! Cross-language Multi-STARK verification fixture generator and wire-format
//! parity suite (`Ix/Cert/MultiStark/Wire.lean` vs `stark-key` + `multi-stark`).
//!
//! Generates deterministic, natively verified fixtures under
//! `Tests/Fixtures/MultiStark/` and parses every byte of `system.bin`,
//! `proof.bin`, and `claims.bin` with a strict line-by-line mirror of
//! `Ix/Cert/MultiStark/Wire.lean` to catch any wire-format divergence.

use multi_stark::{
  batch::{BatchMessage, BatchProof, ShardInput},
  expr::{ColRef, Expr, RowOffset, Source},
  graph::Node,
  lookup::Lookup,
  p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, System, SystemWitness},
  types::{
    CommitmentParameters, ExtVal3, FriParameters, GoldilocksBlake3V6Config, Val,
  },
};
use serde_json::json;
use std::path::{Path, PathBuf};

const GOLDILOCKS_P: u64 = 0xFFFF_FFFF_0000_0001;

// ---------------------------------------------------------------------------
// Strict mirror of `Ix/Cert/MultiStark/Wire.lean`
// ---------------------------------------------------------------------------

struct WireCursor<'a> {
  bytes: &'a [u8],
  pos: usize,
}

impl<'a> WireCursor<'a> {
  fn new(bytes: &'a [u8]) -> Self {
    Self { bytes, pos: 0 }
  }

  fn read_u8(&mut self) -> Result<u8, String> {
    if self.pos < self.bytes.len() {
      let b = self.bytes[self.pos];
      self.pos += 1;
      Ok(b)
    } else {
      Err(format!("eof: need 1 byte at offset {}", self.pos))
    }
  }

  fn read_bool(&mut self) -> Result<bool, String> {
    match self.read_u8()? {
      0 => Ok(false),
      1 => Ok(true),
      b => Err(format!("invalid bool byte {b}")),
    }
  }

  fn read_u16_le(&mut self) -> Result<usize, String> {
    let b0 = usize::from(self.read_u8()?);
    let b1 = usize::from(self.read_u8()?);
    Ok(b0 + (b1 << 8))
  }

  fn read_u32_le(&mut self) -> Result<usize, String> {
    let b0 = usize::from(self.read_u8()?);
    let b1 = usize::from(self.read_u8()?);
    let b2 = usize::from(self.read_u8()?);
    let b3 = usize::from(self.read_u8()?);
    Ok(b0 + (b1 << 8) + (b2 << 16) + (b3 << 24))
  }

  fn read_u64_le(&mut self) -> Result<u64, String> {
    let lo = u64::try_from(self.read_u32_le()?).unwrap();
    let hi = u64::try_from(self.read_u32_le()?).unwrap();
    Ok(lo + (hi << 32))
  }

  fn read_len(&mut self) -> Result<usize, String> {
    let n = self.read_u64_le()?;
    usize::try_from(n).map_err(|e| format!("length overflow {n}: {e}"))
  }

  fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], String> {
    let end = self.pos.checked_add(n).ok_or("offset overflow")?;
    if end <= self.bytes.len() {
      let slice = &self.bytes[self.pos..end];
      self.pos = end;
      Ok(slice)
    } else {
      Err(format!("eof: need {n} bytes at offset {}", self.pos))
    }
  }

  fn read_digest(&mut self) -> Result<[u8; 32], String> {
    let bs = self.read_bytes(32)?;
    let mut out = [0u8; 32];
    out.copy_from_slice(bs);
    Ok(out)
  }

  fn read_canonical_f(&mut self) -> Result<u64, String> {
    let w = self.read_u64_le()?;
    if w < GOLDILOCKS_P {
      Ok(w)
    } else {
      Err(format!("non-canonical Goldilocks element {w}"))
    }
  }

  fn read_ef(&mut self) -> Result<[u64; 3], String> {
    let c0 = self.read_canonical_f()?;
    let c1 = self.read_canonical_f()?;
    let c2 = self.read_canonical_f()?;
    Ok([c0, c1, c2])
  }

  fn read_array<T>(
    &mut self,
    n: usize,
    mut f: impl FnMut(&mut Self) -> Result<T, String>,
  ) -> Result<Vec<T>, String> {
    let mut out = Vec::with_capacity(n.min(1 << 16));
    for _ in 0..n {
      out.push(f(self)?);
    }
    Ok(out)
  }

  fn read_vec<T>(
    &mut self,
    f: impl FnMut(&mut Self) -> Result<T, String>,
  ) -> Result<Vec<T>, String> {
    let n = self.read_len()?;
    self.read_array(n, f)
  }

  fn read_option<T>(
    &mut self,
    mut f: impl FnMut(&mut Self) -> Result<T, String>,
  ) -> Result<Option<T>, String> {
    match self.read_u8()? {
      0 => Ok(None),
      1 => Ok(Some(f(self)?)),
      b => Err(format!("invalid option tag {b}")),
    }
  }

  fn ensure_eof(&self) -> Result<(), String> {
    if self.pos == self.bytes.len() {
      Ok(())
    } else {
      Err(format!(
        "trailing bytes: {} unread at offset {}",
        self.bytes.len() - self.pos,
        self.pos
      ))
    }
  }
}

/// Mirror of Protocol v6 `stark-key` system wire layout (`SystemDeserialize.lean`).
fn wire_verify_system(
  bytes: &[u8],
  expected_system: &System<GoldilocksBlake3V6Config>,
  expected_cp: CommitmentParameters,
  expected_fp: FriParameters,
) -> Result<(), String> {
  let mut c = WireCursor::new(bytes);
  assert_eq!(c.read_u16_le()?, usize::from(stark_key::PROTOCOL_VERSION));
  assert_eq!(c.read_u16_le()?, usize::from(stark_key::EXTENSION_DEGREE));
  assert_eq!(c.read_u16_le()?, usize::from(stark_key::FRI_BATCHING_TENSOR));
  assert_eq!(c.read_digest()?, expected_system.vk_digest);
  assert_eq!(c.read_u16_le()?, expected_cp.log_blowup);
  assert_eq!(c.read_u16_le()?, expected_cp.cap_height);
  assert_eq!(c.read_u16_le()?, expected_fp.log_final_poly_len);
  assert_eq!(c.read_u16_le()?, expected_fp.max_log_arity);
  assert_eq!(c.read_u16_le()?, expected_fp.num_queries);
  assert_eq!(c.read_u16_le()?, expected_fp.commit_proof_of_work_bits);
  assert_eq!(c.read_u16_le()?, expected_fp.query_proof_of_work_bits);

  let circuit_count = c.read_u16_le()?;
  assert_eq!(circuit_count, expected_system.circuits.len());

  for circ in &expected_system.circuits {
    assert_eq!(c.read_u16_le()?, circ.main_width);
    assert_eq!(c.read_u16_le()?, circ.preprocessed_width);
    assert_eq!(c.read_u32_le()?, circ.preprocessed_height);
    assert_eq!(c.read_u16_le()?, circ.max_constraint_degree);
    assert_eq!(usize::from(c.read_u8()?), circ.lookup_group_size);

    let node_count = c.read_u16_le()?;
    assert_eq!(node_count, circ.graph.nodes.len());
    let lookup_prefix_len = c.read_u16_le()?;
    assert_eq!(lookup_prefix_len, circ.graph.lookup_prefix_len);
    for expected_node in &circ.graph.nodes {
      let tag = c.read_u8()?;
      let decoded = match tag {
        0 => {
          let v = u64::try_from(c.read_u16_le()?).unwrap();
          Node::Const(Val::from_u64(v))
        },
        1 => Node::Const(Val::from_u64(c.read_u64_le()?)),
        2 => Node::Public(u32::from(c.read_u8()?)),
        3 => Node::IsFirstRow,
        4 => Node::IsLastRow,
        5 => Node::IsTransition,
        6 => Node::Add(
          multi_stark::graph::NodeId(u32::try_from(c.read_u16_le()?).unwrap()),
          multi_stark::graph::NodeId(u32::try_from(c.read_u16_le()?).unwrap()),
        ),
        7 => Node::Sub(
          multi_stark::graph::NodeId(u32::try_from(c.read_u16_le()?).unwrap()),
          multi_stark::graph::NodeId(u32::try_from(c.read_u16_le()?).unwrap()),
        ),
        8 => Node::Mul(
          multi_stark::graph::NodeId(u32::try_from(c.read_u16_le()?).unwrap()),
          multi_stark::graph::NodeId(u32::try_from(c.read_u16_le()?).unwrap()),
        ),
        9 => Node::Neg(multi_stark::graph::NodeId(
          u32::try_from(c.read_u16_le()?).unwrap(),
        )),
        10..=15 => {
          let code = tag - 10;
          let source = match code / 2 {
            0 => Source::Preprocessed,
            1 => Source::Main,
            _ => Source::Stage2,
          };
          let offset =
            if code % 2 == 0 { RowOffset::Current } else { RowOffset::Next };
          let index = u32::try_from(c.read_u16_le()?).unwrap();
          Node::Var(ColRef { source, offset, index })
        },
        t => return Err(format!("unknown GraphNode tag {t}")),
      };
      assert_eq!(&decoded, expected_node);
    }

    let zero_count = c.read_u16_le()?;
    assert_eq!(zero_count, circ.graph.zeros.len());
    for z in &circ.graph.zeros {
      assert_eq!(c.read_u16_le()?, z.0 as usize);
    }

    let lookup_count = c.read_u16_le()?;
    assert_eq!(lookup_count, circ.graph.lookups.len());
    for lk in &circ.graph.lookups {
      assert_eq!(c.read_u16_le()?, lk.multiplicity.0 as usize);
      let arg_count = c.read_u16_le()?;
      assert_eq!(arg_count, lk.args.len());
      for arg in &lk.args {
        assert_eq!(c.read_u16_le()?, arg.0 as usize);
      }
    }
  }

  let prep_commit = match c.read_u8()? {
    0 => None,
    1 => {
      let cap_len = c.read_u16_le()?;
      Some(c.read_array(cap_len, WireCursor::read_digest)?)
    },
    b => return Err(format!("invalid preprocessed commit flag {b}")),
  };
  match (&prep_commit, &expected_system.preprocessed_commit) {
    (None, None) => {},
    (Some(got), Some(exp)) => assert_eq!(got.as_slice(), exp.roots()),
    _ => return Err("preprocessed_commit presence mismatch".into()),
  }

  let prep_indices = c.read_array(circuit_count, |cur| {
    let idx = cur.read_u16_le()?;
    Ok(if idx == 0xFFFF { None } else { Some(idx) })
  })?;
  assert_eq!(prep_indices, expected_system.preprocessed_indices);
  c.ensure_eof()?;
  Ok(())
}

fn ef_to_triple(e: ExtVal3) -> [u64; 3] {
  let coeffs: &[Val] = e.as_basis_coefficients_slice();
  [
    coeffs[0].as_canonical_u64(),
    coeffs[1].as_canonical_u64(),
    coeffs[2].as_canonical_u64(),
  ]
}

fn read_opened_round(
  c: &mut WireCursor<'_>,
) -> Result<Vec<Vec<Vec<[u64; 3]>>>, String> {
  c.read_vec(|c1| c1.read_vec(|c2| c2.read_vec(WireCursor::read_ef)))
}

fn assert_opened_round_eq(
  got: &[Vec<Vec<[u64; 3]>>],
  expected: &[Vec<Vec<ExtVal3>>],
) {
  let exp: Vec<Vec<Vec<[u64; 3]>>> = expected
    .iter()
    .map(|m| {
      m.iter().map(|p| p.iter().copied().map(ef_to_triple).collect()).collect()
    })
    .collect();
  assert_eq!(got, exp.as_slice());
}

/// Mirror of Protocol v6 `BatchProof` wire layout (`ProofDeserialize.lean`).
fn wire_verify_batch_proof(
  bytes: &[u8],
  expected: &BatchProof<GoldilocksBlake3V6Config>,
) -> Result<(), String> {
  let mut c = WireCursor::new(bytes);

  // Preamble: headers
  let headers_len = c.read_len()?;
  assert_eq!(headers_len, expected.preamble.headers.len());
  for exp_h in &expected.preamble.headers {
    let active = c.read_vec(WireCursor::read_bool)?;
    assert_eq!(active, exp_h.active);
    let stage1 = c.read_vec(WireCursor::read_digest)?;
    assert_eq!(stage1.as_slice(), exp_h.stage_1_trace.roots());
    let log_degrees = c.read_vec(WireCursor::read_u8)?;
    assert_eq!(log_degrees, exp_h.log_degrees);
    let claims =
      c.read_vec(|cur| cur.read_vec(WireCursor::read_canonical_f))?;
    let exp_claims: Vec<Vec<u64>> = exp_h
      .claims
      .iter()
      .map(|cl| cl.iter().map(PrimeField64::as_canonical_u64).collect())
      .collect();
    assert_eq!(claims, exp_claims);
  }

  // Preamble: messages
  let msg_len = c.read_len()?;
  assert_eq!(msg_len, expected.preamble.messages.len());
  for exp_m in &expected.preamble.messages {
    let args = c.read_vec(WireCursor::read_canonical_f)?;
    let mult = c.read_canonical_f()?;
    let exp_args: Vec<u64> =
      exp_m.args.iter().map(PrimeField64::as_canonical_u64).collect();
    assert_eq!(args, exp_args);
    assert_eq!(mult, exp_m.multiplicity.as_canonical_u64());
  }

  // Proofs
  let proofs_len = c.read_len()?;
  assert_eq!(proofs_len, expected.proofs.len());
  for exp_p in &expected.proofs {
    assert_eq!(c.read_vec(WireCursor::read_bool)?, exp_p.active);
    assert_eq!(
      c.read_vec(WireCursor::read_digest)?.as_slice(),
      exp_p.commitments.stage_1_trace.roots()
    );
    assert_eq!(
      c.read_vec(WireCursor::read_digest)?.as_slice(),
      exp_p.commitments.stage_2_trace.roots()
    );
    assert_eq!(
      c.read_vec(WireCursor::read_digest)?.as_slice(),
      exp_p.commitments.quotient_chunks.roots()
    );
    let accs = c.read_vec(WireCursor::read_ef)?;
    let exp_accs: Vec<[u64; 3]> = exp_p
      .intermediate_accumulators
      .iter()
      .copied()
      .map(ef_to_triple)
      .collect();
    assert_eq!(accs, exp_accs);
    assert_eq!(c.read_vec(WireCursor::read_u8)?, exp_p.log_degrees);

    // FRI proof (`Wire.lean:210-231`)
    let fri = &exp_p.opening_proof;
    let commit_caps =
      c.read_vec(|cur| cur.read_vec(WireCursor::read_digest))?;
    assert_eq!(commit_caps.len(), fri.commit_phase_commits.len());
    for (cap, exp_cap) in commit_caps.iter().zip(&fri.commit_phase_commits) {
      if cap.len() != 1 {
        return Err(format!(
          "expected cap length 1 in FRI commit phase, got {}",
          cap.len()
        ));
      }
      assert_eq!(cap.as_slice(), exp_cap.roots());
    }
    let commit_pows = c.read_vec(WireCursor::read_canonical_f)?;
    let exp_commit_pows: Vec<u64> = fri
      .commit_pow_witnesses
      .iter()
      .map(PrimeField64::as_canonical_u64)
      .collect();
    assert_eq!(commit_pows, exp_commit_pows);

    let input_openings_len = c.read_len()?;
    assert_eq!(input_openings_len, fri.input_openings.len());
    for exp_io in &fri.input_openings {
      let opened = c.read_vec(|c1| {
        c1.read_vec(|c2| c2.read_vec(WireCursor::read_canonical_f))
      })?;
      let exp_opened: Vec<Vec<Vec<u64>>> = exp_io
        .opened_values
        .iter()
        .map(|q| {
          q.iter()
            .map(|r| r.iter().map(PrimeField64::as_canonical_u64).collect())
            .collect()
        })
        .collect();
      assert_eq!(opened, exp_opened);
      let siblings = c.read_vec(WireCursor::read_digest)?;
      assert_eq!(siblings, exp_io.opening_proof.sibling_hashes);
    }

    let cpo_len = c.read_len()?;
    assert_eq!(cpo_len, fri.commit_phase_openings.len());
    for exp_cpo in &fri.commit_phase_openings {
      assert_eq!(c.read_u8()?, exp_cpo.log_arity);
      let sib_vals = c.read_vec(|cur| cur.read_vec(WireCursor::read_ef))?;
      let exp_sib_vals: Vec<Vec<[u64; 3]>> = exp_cpo
        .sibling_values
        .iter()
        .map(|row| row.iter().copied().map(ef_to_triple).collect())
        .collect();
      assert_eq!(sib_vals, exp_sib_vals);
      let siblings = c.read_vec(WireCursor::read_digest)?;
      assert_eq!(siblings, exp_cpo.opening_proof.sibling_hashes);
    }

    let final_poly = c.read_vec(WireCursor::read_ef)?;
    let exp_final_poly: Vec<[u64; 3]> =
      fri.final_poly.iter().copied().map(ef_to_triple).collect();
    assert_eq!(final_poly, exp_final_poly);
    assert_eq!(c.read_canonical_f()?, fri.query_pow_witness.as_canonical_u64());

    // Opened rounds
    let q_opened = read_opened_round(&mut c)?;
    assert_opened_round_eq(&q_opened, &exp_p.quotient_opened_values);
    let prep_opened = c.read_option(read_opened_round)?;
    match (&prep_opened, &exp_p.preprocessed_opened_values) {
      (None, None) => {},
      (Some(got), Some(exp)) => assert_opened_round_eq(got, exp),
      _ => return Err("preprocessed_opened_values presence mismatch".into()),
    }
    let s1_opened = read_opened_round(&mut c)?;
    assert_opened_round_eq(&s1_opened, &exp_p.stage_1_opened_values);
    let s2_opened = read_opened_round(&mut c)?;
    assert_opened_round_eq(&s2_opened, &exp_p.stage_2_opened_values);
  }

  c.ensure_eof()?;
  Ok(())
}

/// Mirror of `Ix.Cert.MultiStark.decodeClaims` (`Wire.lean:276-282`).
fn wire_verify_claims(
  bytes: &[u8],
  expected: &[Vec<Val>],
) -> Result<(), String> {
  let mut c = WireCursor::new(bytes);
  let claims = c.read_vec(|cur| cur.read_vec(WireCursor::read_canonical_f))?;
  let exp: Vec<Vec<u64>> = expected
    .iter()
    .map(|cl| cl.iter().map(PrimeField64::as_canonical_u64).collect())
    .collect();
  assert_eq!(claims, exp);
  c.ensure_eof()?;
  Ok(())
}

// ---------------------------------------------------------------------------
// Fixture builders
// ---------------------------------------------------------------------------

fn fixture_params() -> (CommitmentParameters, FriParameters) {
  // Meets the full Protocol v6 security floor:
  //   1 <= log_blowup (4) <= 4, num_queries (77) >= 53,
  //   conjectured = 4*77 + 10 = 318 >= 220,
  //   provable UD = 912*77 + 10_000 = 80_224 >= 80_000 (80.224 bits),
  //   finite-m Johnson = 1955*77 + 10_000 = 160_535 >= 128_000 (160.535 bits).
  // Uses commit_pow_bits = 0 to exercise zero-bit PoW canonicalization and
  // query_pow_bits = 10 to exercise nonzero PoW verification.
  let cp = CommitmentParameters { log_blowup: 4, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 77,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 10,
  };
  (cp, fp)
}

/// Two-circuit system exercising:
/// - Circuit 0 (`main_width = 3`, `lookup_group_size = 2`):
///   - `ConstSmall`, `ConstBig` (`100_000`), `Neg`, `Add`, `Sub`, `Mul`,
///     `IsFirstRow`, `IsLastRow`, `IsTransition`, `Var(Main, Current)`,
///     `Var(Main, Next)`.
///   - 3 lookups grouped by 2 (`logupGroupCount = 2`, `stage2Width = 4`),
///     covering both intermediate and final chained LogUp groups.
/// - Circuit 1 (`main_width = 2`, `preprocessed` 4×2, `lookup_group_size = 1`):
///   - `Var(Preprocessed, Current)` in both user constraint and lookups.
///   - 2 lookups cancelling Circuit 0's channel-2 and channel-3 pushes.
fn two_circuit_system(
  cp: CommitmentParameters,
  fp: FriParameters,
) -> (
  System<GoldilocksBlake3V6Config>,
  multi_stark::system::ProverKey<GoldilocksBlake3V6Config>,
) {
  two_circuit_system_ordered(cp, fp, false)
}

/// The same two circuits, with the fixed-table circuit (Circuit 1 above) first
/// when `prep_first`.
fn two_circuit_system_ordered(
  cp: CommitmentParameters,
  fp: FriParameters,
  prep_first: bool,
) -> (
  System<GoldilocksBlake3V6Config>,
  multi_stark::system::ProverKey<GoldilocksBlake3V6Config>,
) {
  let x = Expr::main(0);
  let y = Expr::main(1);
  let sel = Expr::main(2);
  let x_next = Expr::main_next(0);
  let sel_next = Expr::main_next(2);
  let one = Expr::constant(Val::ONE);
  let two = Expr::constant(Val::from_u64(2));
  let three = Expr::constant(Val::from_u64(3));
  let four = Expr::constant(Val::from_u64(4));
  let big_a = Expr::constant(Val::from_u64(100_000));
  let big_b = Expr::constant(Val::from_u64(100_001));

  let c0 = CircuitInputs {
    main_width: 3,
    constraints: vec![
      // -y + x * x = 0  (exercises Neg, Mul, Add)
      -y.clone() + x.clone() * x.clone(),
      // is_first_row * ((x + 100_000) - 100_001) = 0  (exercises ConstBig + IsFirstRow)
      Expr::IsFirstRow * ((x.clone() + big_a) - big_b),
      // is_last_row * (x - 4) = 0  (exercises IsLastRow)
      Expr::IsLastRow * (x.clone() - four),
      // is_transition * (next(x) - x - 1) = 0  (exercises IsTransition + Main Next)
      Expr::IsTransition * (x_next - x.clone() - one.clone()),
      // sel * (sel - 1) = 0
      sel.clone() * (sel.clone() - one.clone()),
      // is_first_row * (sel - 1) = 0
      Expr::IsFirstRow * (sel.clone() - one.clone()),
      // is_transition * next(sel) = 0
      Expr::IsTransition * sel_next,
    ],
    lookups: vec![
      // Pull public claim (1, 1, 1) on row 0
      Lookup::pull(sel.clone(), vec![one.clone(), x.clone(), y.clone()]),
      // Push (2, x, y) on all 4 rows to Circuit 1
      Lookup::push(one, vec![two, x.clone(), y.clone()]),
      // Push (3, 1, 1) on row 0 to Circuit 1
      Lookup::push(sel, vec![three, x, y]),
    ],
    lookup_group_size: 2,
    ..Default::default()
  };

  let p0 = Expr::preprocessed(0);
  let p1 = Expr::preprocessed(1);
  let prep_rows = vec![
    Val::from_u64(1),
    Val::from_u64(1),
    Val::from_u64(2),
    Val::from_u64(4),
    Val::from_u64(3),
    Val::from_u64(9),
    Val::from_u64(4),
    Val::from_u64(16),
  ];
  let c1 = CircuitInputs {
    main_width: 2,
    preprocessed: Some(RowMajorMatrix::new(prep_rows, 2)),
    constraints: vec![p0.clone() * p0.clone() - p1.clone()],
    lookups: vec![
      Lookup::pull(
        Expr::main(0),
        vec![Expr::constant(Val::from_u64(2)), p0.clone(), p1.clone()],
      ),
      Lookup::pull(
        Expr::main(1),
        vec![Expr::constant(Val::from_u64(3)), p0, p1],
      ),
    ],
    lookup_group_size: 1,
    ..Default::default()
  };

  let circuits = if prep_first { vec![c1, c0] } else { vec![c0, c1] };
  System::new(GoldilocksBlake3V6Config::new(cp, fp), circuits)
}

fn c0_trace() -> RowMajorMatrix<Val> {
  RowMajorMatrix::new(
    vec![
      Val::from_u64(1),
      Val::from_u64(1),
      Val::ONE,
      Val::from_u64(2),
      Val::from_u64(4),
      Val::ZERO,
      Val::from_u64(3),
      Val::from_u64(9),
      Val::ZERO,
      Val::from_u64(4),
      Val::from_u64(16),
      Val::ZERO,
    ],
    3,
  )
}

fn c1_trace() -> RowMajorMatrix<Val> {
  RowMajorMatrix::new(
    vec![
      Val::ONE,
      Val::ONE,
      Val::ONE,
      Val::ZERO,
      Val::ONE,
      Val::ZERO,
      Val::ONE,
      Val::ZERO,
    ],
    2,
  )
}

fn empty_trace(width: usize) -> RowMajorMatrix<Val> {
  RowMajorMatrix::new(Vec::new(), width)
}

fn repo_root() -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .parent()
    .and_then(Path::parent)
    .expect("workspace root")
    .to_path_buf()
}

fn dump_and_verify_fixture(
  dir: &Path,
  description: &str,
  system: &System<GoldilocksBlake3V6Config>,
  cp: CommitmentParameters,
  fp: FriParameters,
  proof: &BatchProof<GoldilocksBlake3V6Config>,
  all_claims: &[Vec<Val>],
) {
  system.verify_batch(proof).unwrap_or_else(|e| {
    panic!("{description}: native verify_batch failed: {e:?}")
  });

  let system_bytes = stark_key::to_bytes(system, cp, fp);
  let proof_bytes = proof.to_bytes().expect("proof to_bytes");
  let claims_bytes = stark_verifier::claims_bytes(all_claims);

  // Round-trip via Rust decoders (enforcing the production security floor).
  let (decoded_sys, decoded_cp, decoded_fp) =
    stark_key::from_bytes(&system_bytes)
      .expect("stark_key::from_bytes (at-floor fixture)");
  assert_eq!(
    stark_key::to_bytes(&decoded_sys, decoded_cp, decoded_fp),
    system_bytes
  );
  let decoded_proof =
    BatchProof::<GoldilocksBlake3V6Config>::from_bytes(&proof_bytes)
      .expect("BatchProof::from_bytes");
  assert_eq!(decoded_proof.to_bytes().unwrap(), proof_bytes);
  decoded_sys
    .verify_batch(&decoded_proof)
    .expect("decoded system verifies decoded proof");

  // Strict byte-for-byte mirror of `Ix/Cert/MultiStark/Wire.lean`
  wire_verify_system(&system_bytes, system, cp, fp).unwrap_or_else(|e| {
    panic!("{description}: Wire.lean system mirror failed: {e}")
  });
  wire_verify_batch_proof(&proof_bytes, proof).unwrap_or_else(|e| {
    panic!("{description}: Wire.lean proof mirror failed: {e}")
  });
  wire_verify_claims(&claims_bytes, all_claims).unwrap_or_else(|e| {
    panic!("{description}: Wire.lean claims mirror failed: {e}")
  });

  // Negative checks on Wire.lean mirror: truncation and trailing bytes must fail.
  assert!(
    wire_verify_system(&system_bytes[..system_bytes.len() - 1], system, cp, fp)
      .is_err()
  );
  let mut trailing_sys = system_bytes.clone();
  trailing_sys.push(0);
  assert!(wire_verify_system(&trailing_sys, system, cp, fp).is_err());

  assert!(
    wire_verify_batch_proof(&proof_bytes[..proof_bytes.len() - 1], proof)
      .is_err()
  );
  let mut trailing_proof = proof_bytes.clone();
  trailing_proof.push(0);
  assert!(wire_verify_batch_proof(&trailing_proof, proof).is_err());

  // Negative check: mutating an opened value must fail native verification.
  let mut bad_proof = proof.clone();
  bad_proof.proofs[0].stage_1_opened_values[0][0][0] += ExtVal3::ONE;
  assert!(system.verify_batch(&bad_proof).is_err());

  let claims_u64: Vec<Vec<u64>> = all_claims
    .iter()
    .map(|cl| cl.iter().map(PrimeField64::as_canonical_u64).collect())
    .collect();
  let vk_digest = blake3::hash(&system_bytes).to_hex().to_string();
  let proof_digest = blake3::hash(&proof_bytes).to_hex().to_string();
  let claims_digest = blake3::hash(&claims_bytes).to_hex().to_string();

  let meta = json!({
    "description": description,
    "claims": claims_u64,
    "log_blowup": cp.log_blowup,
    "cap_height": cp.cap_height,
    "log_final_poly_len": fp.log_final_poly_len,
    "max_log_arity": fp.max_log_arity,
    "num_queries": fp.num_queries,
    "proof_of_work_bits": fp.query_proof_of_work_bits,
    "commit_proof_of_work_bits": fp.commit_proof_of_work_bits,
    "query_proof_of_work_bits": fp.query_proof_of_work_bits,
    "num_shards": proof.proofs.len(),
    "num_circuits": system.circuits.len(),
    "num_messages": proof.preamble.messages.len(),
    "vk_digest": vk_digest,
    "proof_digest": proof_digest,
    "claims_digest": claims_digest,
    "system_bytes_len": system_bytes.len(),
    "proof_bytes_len": proof_bytes.len(),
    "claims_bytes_len": claims_bytes.len(),
  });
  let meta_json = format!("{}\n", serde_json::to_string_pretty(&meta).unwrap());

  for (name, bytes) in [
    ("system.bin", system_bytes.as_slice()),
    ("proof.bin", proof_bytes.as_slice()),
    ("claims.bin", claims_bytes.as_slice()),
    ("claims.json", meta_json.as_bytes()),
  ] {
    write_or_compare_fixture(&dir.join(name), bytes);
  }
}

/// Write a fixture file or, when it exists and `IX_REGEN_FIXTURES` is unset,
/// require the deterministic output to equal it.
fn write_or_compare_fixture(path: &Path, bytes: &[u8]) {
  let regen = std::env::var_os("IX_REGEN_FIXTURES").is_some();
  if let Some(parent) = path.parent() {
    std::fs::create_dir_all(parent).expect("create fixture dir");
  }
  if !regen && path.exists() {
    let existing = std::fs::read(path).expect("read existing fixture");
    assert_eq!(
      existing,
      bytes,
      "fixture {} drifted from deterministic Rust output (re-run with IX_REGEN_FIXTURES=1 to update)",
      path.display()
    );
  } else {
    std::fs::write(path, bytes).expect("write fixture file");
  }
}

#[test]
fn generate_and_verify_multi_stark_fixtures() {
  let root = repo_root().join("Tests/Fixtures/MultiStark");
  let (cp, fp) = fixture_params();

  // -------------------------------------------------------------------------
  // 1. Top-level fixture: 2-circuit system (preprocessed + cross-circuit
  //    grouped lookups), 1-shard BatchProof.
  // -------------------------------------------------------------------------
  let (sys, pk) = two_circuit_system(cp, fp);
  // Sanity-check that ConstBig and Neg nodes survived compilation.
  assert!(
    sys.circuits[0]
      .graph
      .nodes
      .iter()
      .any(|n| matches!(n, Node::Const(v) if v.as_canonical_u64() == 100_000)),
    "expected ConstBig node in circuit 0"
  );
  assert!(
    sys.circuits[0].graph.nodes.iter().any(|n| matches!(n, Node::Neg(_))),
    "expected Neg node in circuit 0"
  );

  let claims = vec![vec![Val::ONE, Val::ONE, Val::ONE]];
  let witness_all =
    SystemWitness::from_stage_1(vec![c0_trace(), c1_trace()], &sys);
  let proof_1 = sys.prove_batch(
    &pk,
    vec![ShardInput { claims: claims.clone(), witness: witness_all.clone() }],
    vec![],
  );
  // Determinism check
  let proof_1_repeat = sys.prove_batch(
    &pk,
    vec![ShardInput { claims: claims.clone(), witness: witness_all }],
    vec![],
  );
  assert_eq!(proof_1.to_bytes().unwrap(), proof_1_repeat.to_bytes().unwrap());

  dump_and_verify_fixture(
    &root,
    "2 circuits (with preprocessed table + cross-circuit grouped lookups), 1 shard",
    &sys,
    cp,
    fp,
    &proof_1,
    &claims,
  );

  // -------------------------------------------------------------------------
  // 2. Two-shard fixture (`two_shard/`): same 2-circuit system split across
  //    2 shards, exercising cross-shard non-zero residuals + inactive
  //    preprocessed 1-point opening in Shard 0 and active 2-point opening in
  //    Shard 1.
  // -------------------------------------------------------------------------
  let w_shard0 =
    SystemWitness::from_stage_1(vec![c0_trace(), empty_trace(2)], &sys);
  let w_shard1 =
    SystemWitness::from_stage_1(vec![empty_trace(3), c1_trace()], &sys);
  let proof_2 = sys.prove_batch(
    &pk,
    vec![
      ShardInput { claims: claims.clone(), witness: w_shard0 },
      ShardInput { claims: vec![], witness: w_shard1 },
    ],
    vec![],
  );
  assert_eq!(proof_2.proofs.len(), 2);
  assert_eq!(proof_2.proofs[0].active, vec![true, false]);
  assert_eq!(proof_2.proofs[1].active, vec![false, true]);
  assert_ne!(
    *proof_2.proofs[0].intermediate_accumulators.last().unwrap(),
    ExtVal3::ZERO,
    "shard 0 should have non-zero LogUp residual"
  );
  assert_ne!(
    *proof_2.proofs[1].intermediate_accumulators.last().unwrap(),
    ExtVal3::ZERO,
    "shard 1 should have non-zero LogUp residual"
  );
  dump_and_verify_fixture(
    &root.join("two_shard"),
    "2 circuits (with preprocessed table + cross-circuit grouped lookups), 2 shards",
    &sys,
    cp,
    fp,
    &proof_2,
    &claims,
  );

  // -------------------------------------------------------------------------
  // 3. Single-circuit no-preprocessed fixture (`single_no_prep/`): exercises
  //    `preprocessedCommit = none` and `preprocessedOpenedValues = none`.
  // -------------------------------------------------------------------------
  let x = Expr::main(0);
  let y = Expr::main(1);
  let sel = Expr::main(2);
  let one = Expr::constant(Val::ONE);
  let (sys_np, pk_np) = System::new(
    GoldilocksBlake3V6Config::new(cp, fp),
    vec![CircuitInputs {
      main_width: 3,
      constraints: vec![
        x.clone() * x.clone() - y.clone(),
        sel.clone() * (sel.clone() - one.clone()),
      ],
      lookups: vec![Lookup::pull(
        sel,
        vec![one, Expr::constant(Val::ZERO), x, y],
      )],
      lookup_group_size: 1,
      ..Default::default()
    }],
  );
  let claims_np =
    vec![vec![Val::ONE, Val::ZERO, Val::from_u64(3), Val::from_u64(9)]];
  let witness_np = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(
      vec![
        Val::from_u64(3),
        Val::from_u64(9),
        Val::ONE,
        Val::from_u64(4),
        Val::from_u64(16),
        Val::ZERO,
        Val::from_u64(5),
        Val::from_u64(25),
        Val::ZERO,
        Val::from_u64(6),
        Val::from_u64(36),
        Val::ZERO,
      ],
      3,
    )],
    &sys_np,
  );
  let proof_np = sys_np.prove_batch(
    &pk_np,
    vec![ShardInput { claims: claims_np.clone(), witness: witness_np }],
    vec![],
  );
  assert!(sys_np.preprocessed_commit.is_none());
  assert!(proof_np.proofs[0].preprocessed_opened_values.is_none());
  dump_and_verify_fixture(
    &root.join("single_no_prep"),
    "1 circuit (no preprocessed table), 1 lookup, 1 shard",
    &sys_np,
    cp,
    fp,
    &proof_np,
    &claims_np,
  );
  // Negative-control mutant: non-zero commit PoW witness when commit_pow_bits == 0.
  let mut bad_cpow = proof_np.clone();
  assert!(!bad_cpow.proofs[0].opening_proof.commit_pow_witnesses.is_empty());
  bad_cpow.proofs[0].opening_proof.commit_pow_witnesses[0] = Val::ONE;
  write_or_compare_fixture(
    &root.join("single_no_prep/nonzero_cpow/proof.bin"),
    &bad_cpow.to_bytes().expect("nonzero_cpow to_bytes"),
  );
  // Negative-control fixture: natively valid proof under below-floor parameters
  // `(2, 0, 0, 1, 4, 1, 2)`. Both `stark_key::from_bytes` and the in-circuit
  // verifier must reject it.
  let cp_low = CommitmentParameters { log_blowup: 2, cap_height: 0 };
  let fp_low = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 4,
    commit_proof_of_work_bits: 1,
    query_proof_of_work_bits: 2,
  };
  let x_low = Expr::main(0);
  let y_low = Expr::main(1);
  let sel_low = Expr::main(2);
  let one_low = Expr::constant(Val::ONE);
  let (sys_low, pk_low) = System::new(
    GoldilocksBlake3V6Config::new(cp_low, fp_low),
    vec![CircuitInputs {
      main_width: 3,
      constraints: vec![
        x_low.clone() * x_low.clone() - y_low.clone(),
        sel_low.clone() * (sel_low.clone() - one_low.clone()),
      ],
      lookups: vec![Lookup::pull(
        sel_low,
        vec![one_low, Expr::constant(Val::ZERO), x_low, y_low],
      )],
      lookup_group_size: 1,
      ..Default::default()
    }],
  );
  let witness_low = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(
      vec![
        Val::from_u64(3),
        Val::from_u64(9),
        Val::ONE,
        Val::from_u64(4),
        Val::from_u64(16),
        Val::ZERO,
        Val::from_u64(5),
        Val::from_u64(25),
        Val::ZERO,
        Val::from_u64(6),
        Val::from_u64(36),
        Val::ZERO,
      ],
      3,
    )],
    &sys_low,
  );
  let proof_low = sys_low.prove_batch(
    &pk_low,
    vec![ShardInput { claims: claims_np.clone(), witness: witness_low }],
    vec![],
  );
  sys_low.verify_batch(&proof_low).expect("native verify below-floor proof");
  let low_sys_bytes = stark_key::to_bytes(&sys_low, cp_low, fp_low);
  assert!(
    stark_key::from_bytes(&low_sys_bytes).is_err(),
    "stark_key::from_bytes must reject below-floor key"
  );
  let low_dir = root.join("single_no_prep/below_floor");
  write_or_compare_fixture(&low_dir.join("system.bin"), &low_sys_bytes);
  write_or_compare_fixture(
    &low_dir.join("proof.bin"),
    &proof_low.to_bytes().expect("below-floor proof to_bytes"),
  );
  write_or_compare_fixture(
    &low_dir.join("claims.bin"),
    &stark_verifier::claims_bytes(&claims_np),
  );

  // -------------------------------------------------------------------------
  // 4. Two-shard MEMSEG=16 closure-pair fixture (`memseg_two_shard/`):
  //    exercises non-empty `BatchMessage`s passing `Preamble.checkClosurePairs`
  //    with a telescoping memory segment across two shards:
  //      preamble: pull [16, 1, 0], push [16, 1, 4]
  //      shard 0:  push [16, 1, 0], pull [16, 1, 2]
  //      shard 1:  push [16, 1, 2], pull [16, 1, 4]
  // -------------------------------------------------------------------------
  let start_col = Expr::main(0);
  let end_col = Expr::main(1);
  let active_col = Expr::main(2);
  let memseg = Expr::constant(Val::from_u64(16));
  let width_one = Expr::constant(Val::ONE);
  let (sys_ms, pk_ms) = System::new(
    GoldilocksBlake3V6Config::new(cp, fp),
    vec![CircuitInputs {
      main_width: 3,
      constraints: vec![
        active_col.clone() * (active_col.clone() - Expr::constant(Val::ONE)),
        active_col.clone()
          * (end_col.clone()
            - start_col.clone()
            - Expr::constant(Val::from_u64(2))),
      ],
      lookups: vec![
        Lookup::push(
          active_col.clone(),
          vec![memseg.clone(), width_one.clone(), start_col],
        ),
        Lookup::pull(active_col, vec![memseg, width_one, end_col]),
      ],
      lookup_group_size: 2,
      ..Default::default()
    }],
  );
  let w_ms0 = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(
      vec![
        Val::from_u64(0),
        Val::from_u64(2),
        Val::ONE,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
      ],
      3,
    )],
    &sys_ms,
  );
  let w_ms1 = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(
      vec![
        Val::from_u64(2),
        Val::from_u64(4),
        Val::ONE,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
        Val::ZERO,
      ],
      3,
    )],
    &sys_ms,
  );
  let messages = vec![
    BatchMessage::pull(vec![Val::from_u64(16), Val::ONE, Val::ZERO]),
    BatchMessage::push(vec![Val::from_u64(16), Val::ONE, Val::from_u64(4)]),
  ];
  let proof_ms = sys_ms.prove_batch(
    &pk_ms,
    vec![
      ShardInput { claims: vec![], witness: w_ms0 },
      ShardInput { claims: vec![], witness: w_ms1 },
    ],
    messages,
  );
  dump_and_verify_fixture(
    &root.join("memseg_two_shard"),
    "1 circuit, 2 shards with valid MEMSEG=16 closure-pair BatchMessages",
    &sys_ms,
    cp,
    fp,
    &proof_ms,
    &[],
  );

  // -------------------------------------------------------------------------
  // 5. Fixed-table circuit first (`prep_first/`) and its height mutants
  //    (`prep_first/logdeg_<k>/proof.bin`, under the same `system.bin` and
  //    `claims.bin`): the fixed-table circuit's log degree changed from 2 to k
  //    in the preamble header and the shard proof together. A fixed table must
  //    be bound to its height (a historical soundness bug of the in-circuit
  //    verifier); with the fixed-table circuit first, the in-circuit verifier
  //    meets its height assertion (`StarkVerifier::ood_loop`) before any other
  //    circuit's out-of-domain check. Native verification rejects every mutant.
  // -------------------------------------------------------------------------
  let (sys_pf, pk_pf) = two_circuit_system_ordered(cp, fp, true);
  let witness_pf =
    SystemWitness::from_stage_1(vec![c1_trace(), c0_trace()], &sys_pf);
  let proof_pf = sys_pf.prove_batch(
    &pk_pf,
    vec![ShardInput { claims: claims.clone(), witness: witness_pf }],
    vec![],
  );
  let pf_dir = root.join("prep_first");
  dump_and_verify_fixture(
    &pf_dir,
    "2 circuits, the fixed-table circuit first, 1 shard",
    &sys_pf,
    cp,
    fp,
    &proof_pf,
    &claims,
  );
  assert_eq!(proof_pf.proofs[0].active, vec![true, true]);
  assert_eq!(proof_pf.proofs[0].log_degrees[0], 2, "a fixed table of 4 rows");
  for ld in [0u8, 1, 3, 4] {
    let mut bad = proof_pf.clone();
    bad.proofs[0].log_degrees[0] = ld;
    bad.preamble.headers[0].log_degrees[0] = ld;
    assert!(
      sys_pf.verify_batch(&bad).is_err(),
      "prep_first: native verify_batch accepted the fixed table at log degree {ld}"
    );
    let bytes = bad.to_bytes().expect("height mutant to_bytes");
    write_or_compare_fixture(
      &pf_dir.join(format!("logdeg_{ld}")).join("proof.bin"),
      &bytes,
    );
  }
}
