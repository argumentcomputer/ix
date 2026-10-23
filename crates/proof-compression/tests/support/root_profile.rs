//! Synthetic aggregation-root profile for exercising the Plonkish builder.
//! The root consumes an 18-word receipt and calls mutually recursive parity,
//! two fixed tables, and a small memory-like counter circuit. Inactive functions
//! are interspersed so canonical, active, and preprocessed indices all differ.
//! The receipt binds a fixed tag, format, validator, subject and assumptions marker.
//! Keys and circuit semantics are synthetic, not an application implementation.

use ix_proof_compression::fri::ByteGadgets;
use ix_proof_compression::fri::ByteValue;
use ix_proof_compression::fri::FixedPcsShape;
use ix_proof_compression::fri::FixedVerifierInputs;
use ix_proof_compression::fri::blake3;
use ix_proof_compression::fri::constrain_fixed_verifier;
use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_field::PrimeField64;
use multi_stark::p3_matrix::dense::RowMajorMatrix;
use multi_stark::plonkish::Circuit;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;
use multi_stark::system::CircuitInputs;
use multi_stark::system::System;
use multi_stark::types::CommitmentParameters;
use multi_stark::types::FriParameters;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;
use p3_blake3::Blake3;
use p3_symmetric::CryptographicHasher;

pub(crate) const ACTIVE: [bool; 9] =
  [true, false, true, true, true, false, true, true, true];
pub(crate) const AGGR_INDEX: u64 = 17;
// Fixture receipt: claim tag = e5, format = 3, validator identifier = 1.
const RECEIPT_PREFIX: [u8; 3] = [0xe5, 3, 1];

#[derive(Clone, Copy, Debug)]
pub(crate) enum Profile {
  /// Four queries, small grinding and small fixed tables; same algorithms.
  Smoke,
  /// Larger fixed tables, 100 queries and 20-bit query grinding.
  FullSize,
}

impl Profile {
  pub(crate) fn logs(self) -> Vec<u8> {
    let tables = match self {
      Self::Smoke => [4, 5],
      Self::FullSize => [8, 16],
    };
    vec![7, 7, tables[0], 7, tables[1], 6, 0]
  }

  pub(crate) fn config(self) -> GoldilocksBlake3Config {
    let (queries, commit_pow, query_pow) = match self {
      Self::Smoke => (4, 3, 4),
      Self::FullSize => (100, 0, 20),
    };
    GoldilocksBlake3Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: queries,
        commit_proof_of_work_bits: commit_pow,
        query_proof_of_work_bits: query_pow,
      },
    )
  }

  pub(crate) fn shape(
    self,
    system: &System<GoldilocksBlake3Config>,
  ) -> FixedPcsShape {
    // This fixture has unit consumers. Count ALL slots (even
    // providers) conservatively; fixed metadata makes this a build-time
    // policy check, not a prover-supplied claim about multiplicities.
    assert!(
      unit_lookup_bound(
        system.circuits.iter().map(|c| c.graph.lookups.len()),
        &ACTIVE,
        &self.logs(),
        1
      )
      .is_some(),
      "unit lookup count reaches the field characteristic"
    );
    FixedPcsShape::from_profile(system, &ACTIVE, &self.logs())
  }
}

/// Conservatively bounds the lookup budget. This assumption is specific to unit
/// consumers; it must NOT be applied to arbitrary user lookup multiplicities.
pub(crate) fn unit_lookup_bound(
  slots: impl ExactSizeIterator<Item = usize>,
  active: &[bool],
  logs: &[u8],
  claims: u64,
) -> Option<u64> {
  if slots.len() != active.len()
    || !active.contains(&true)
    || claims >= Val::ORDER_U64
  {
    return None;
  }
  let mut logs = logs.iter();
  let mut total = claims;
  for (slots, &enabled) in slots.zip(active) {
    if enabled {
      let height = 1u64.checked_shl(u32::from(*logs.next()?))?;
      total =
        total.checked_add(height.checked_mul(u64::try_from(slots).ok()?)?)?;
      if total >= Val::ORDER_U64 {
        return None;
      }
    }
  }
  logs.next().is_none().then_some(total)
}

fn words(digest: [u8; 32]) -> [Val; 8] {
  std::array::from_fn(|i| {
    Val::from_u32(u32::from_le_bytes(
      digest[4 * i..4 * i + 4].try_into().unwrap(),
    ))
  })
}

/// An 80-byte allow-list blob of two synthetic VK digests and entrypoint indices.
pub(crate) fn allowed_blob() -> Vec<u8> {
  [0x11; 32]
    .into_iter()
    .chain(23u64.to_le_bytes())
    .chain([0x22; 32])
    .chain(AGGR_INDEX.to_le_bytes())
    .collect()
}

pub(crate) fn allowed_digest() -> [Val; 8] {
  words(Blake3.hash_iter(allowed_blob()))
}

pub(crate) fn claim(subject: [u8; 32]) -> Vec<Val> {
  let output = words(Blake3.hash_iter(receipt_bytes(subject)));
  [Val::ZERO, Val::from_u64(AGGR_INDEX)]
    .into_iter()
    .chain(allowed_digest())
    .chain(output)
    .collect()
}

pub(crate) fn receipt_bytes(subject: [u8; 32]) -> Vec<u8> {
  RECEIPT_PREFIX.into_iter().chain(subject).chain([0]).collect()
}

fn c(n: usize) -> Expr<Val> {
  Expr::constant(Val::from_usize(n))
}

fn inactive() -> CircuitInputs<Val> {
  CircuitInputs {
    main_width: 1,
    constraints: vec![Expr::main(0)],
    ..Default::default()
  }
}

fn parity(function: usize) -> CircuitInputs<Val> {
  // Unlike the original parity fixture, functions have NO preprocessing.
  // Main columns: live, result, n, is_base. All 128 rows retain their n.
  let live = Expr::main(0);
  let result = Expr::main(1);
  let n = Expr::main(2);
  let base = Expr::main(3);
  CircuitInputs {
    main_width: 4,
    constraints: vec![
      live.clone() * (live.clone() - c(1)),
      result.clone() * (result.clone() - c(1)),
      base.clone() * (base.clone() - c(1)),
      (c(1) - live.clone()) * result.clone(),
      base.clone() * (result.clone() - c(1 - function) * live.clone()),
      n.clone() * base.clone(),
      Expr::IsFirstRow * n.clone(),
      Expr::IsFirstRow * (base.clone() - c(1)),
      Expr::IsTransition * (Expr::main_next(2) - n.clone() - c(1)),
      Expr::IsTransition * Expr::main_next(3),
      Expr::IsLastRow * (n.clone() - c(127)),
    ],
    lookups: vec![
      Lookup::pull(live.clone(), vec![c(function), n.clone(), result.clone()]),
      Lookup::push(
        live * (c(1) - base),
        vec![c(1 - function), n - c(1), result],
      ),
    ],
    lookup_group_size: 2,
    ..Default::default()
  }
}

fn table(height: usize, tag: usize) -> CircuitInputs<Val> {
  // Eleven preprocessed columns stress wide fixed tables. This toy relation
  // uses all columns, with two message widths and next-row preprocessing.
  let preprocessed = RowMajorMatrix::new(
    (0..height)
      .flat_map(|row| (0..11).map(move |col| Val::from_usize(row + col)))
      .collect(),
    11,
  );
  let mut args = vec![c(tag)];
  args.extend((0..if tag == 3 { 1 } else { 11 }).map(Expr::preprocessed));
  CircuitInputs {
    main_width: 1,
    preprocessed: Some(preprocessed),
    constraints: vec![
      Expr::main(0) * (Expr::main(0) - c(1)),
      Expr::IsTransition
        * (Expr::preprocessed_next(0) - Expr::preprocessed(0) - c(1)),
    ],
    lookups: vec![Lookup::pull(Expr::main(0), args)],
    lookup_group_size: 2,
    ..Default::default()
  }
}

pub(crate) fn circuit_inputs(profile: Profile) -> Vec<CircuitInputs<Val>> {
  let live = Expr::main(0);
  let mut root_claim = vec![c(0), Expr::constant(Val::from_u64(AGGR_INDEX))];
  root_claim.extend(allowed_digest().map(Expr::constant));
  root_claim.extend((1..=8).map(Expr::main));
  let mut root_constraints = vec![
    live.clone() * (live.clone() - c(1)),
    Expr::IsFirstRow * (live.clone() - c(1)),
    Expr::IsTransition * Expr::main_next(0),
  ];
  root_constraints
    .extend((1..=8).map(|i| (c(1) - live.clone()) * Expr::main(i)));
  root_constraints.extend(
    [(9, 100), (10, 7), (11, 9)]
      .map(|(i, value)| Expr::main(i) - live.clone() * c(value)),
  );
  let root = CircuitInputs {
    main_width: 12,
    constraints: root_constraints,
    lookups: vec![
      Lookup::pull(live.clone(), root_claim),
      Lookup::push(live.clone(), vec![c(0), Expr::main(9), c(1)]),
      Lookup::push(live.clone(), vec![c(3), Expr::main(10)]),
      Lookup::push(
        live.clone(),
        std::iter::once(c(6))
          .chain((0..11).map(|i| Expr::main(11) + c(i)))
          .collect(),
      ),
      Lookup::push(live, vec![c(7), c(42)]),
    ],
    // Five messages: one full group plus a partial final group.
    lookup_group_size: 3,
    ..Default::default()
  };
  let memory = CircuitInputs {
    main_width: 2,
    constraints: vec![
      Expr::IsFirstRow * Expr::main(0),
      Expr::IsTransition * (Expr::main_next(0) - Expr::main(0) - c(1)),
      Expr::IsLastRow * (Expr::main(0) - c(63)),
      Expr::IsFirstRow * (Expr::main(1) - c(1)),
      Expr::IsTransition * Expr::main_next(1),
    ],
    lookups: vec![Lookup::pull(Expr::main(1), vec![c(7), c(42)])],
    ..Default::default()
  };
  let singleton = CircuitInputs {
    main_width: 1,
    constraints: vec![Expr::main(0) - c(17)],
    ..Default::default()
  };
  let logs = profile.logs();
  vec![
    root,
    inactive(),
    parity(0),
    table(1 << logs[2], 3),
    parity(1),
    inactive(),
    table(1 << logs[4], 6),
    memory,
    singleton,
  ]
}

pub(crate) fn traces(
  profile: Profile,
  subject: [u8; 32],
) -> Vec<RowMajorMatrix<Val>> {
  let mut root = RowMajorMatrix::new(vec![Val::ZERO; 128 * 12], 12);
  root.values[0] = Val::ONE;
  root.values[1..9].copy_from_slice(&claim(subject)[10..18]);
  root.values[9..12].copy_from_slice(&[
    Val::from_u8(100),
    Val::from_u8(7),
    Val::from_u8(9),
  ]);
  let mut functions: Vec<_> = (0..2)
    .map(|_| {
      RowMajorMatrix::new(
        (0..128)
          .flat_map(|n| {
            [Val::ZERO, Val::ZERO, Val::from_usize(n), Val::from_bool(n == 0)]
          })
          .collect(),
        4,
      )
    })
    .collect();
  for n in 0..=100 {
    let row = &mut functions[n % 2].values[n * 4..][..4];
    row[0] = Val::ONE;
    row[1] = Val::ONE;
  }
  let logs = profile.logs();
  let mut small = RowMajorMatrix::new(vec![Val::ZERO; 1 << logs[2]], 1);
  small.values[7] = Val::ONE;
  let mut large = RowMajorMatrix::new(vec![Val::ZERO; 1 << logs[4]], 1);
  large.values[9] = Val::ONE;
  let memory = RowMajorMatrix::new(
    (0..64)
      .flat_map(|n| [Val::from_usize(n), Val::from_bool(n == 0)])
      .collect(),
    2,
  );
  let odd = functions.pop().unwrap();
  let even = functions.pop().unwrap();
  vec![
    root,
    RowMajorMatrix::new(vec![], 1),
    even,
    small,
    odd,
    RowMajorMatrix::new(vec![], 1),
    large,
    memory,
    RowMajorMatrix::new(vec![Val::from_u8(17)], 1),
  ]
}

pub(crate) struct StatementVerifier {
  pub circuit: Circuit<Val>,
  pub inputs: FixedVerifierInputs,
  pub subject: [ByteValue; 32],
}

fn pack_words(
  b: &mut CircuitBuilder<Val>,
  digest: &[ByteValue; 32],
) -> Vec<Value> {
  digest
    .as_chunks::<4>()
    .0
    .iter()
    .map(|chunk| {
      let terms: Vec<_> = chunk
        .iter()
        .enumerate()
        .map(|(i, byte)| (Val::from_u64(1u64 << (8 * i)), byte.value()))
        .collect();
      b.linear_combination(&terms, Val::ZERO)
    })
    .collect()
}

pub(crate) fn build_statement_verifier(
  system: &System<GoldilocksBlake3Config>,
  profile: Profile,
) -> StatementVerifier {
  let mut b = CircuitBuilder::new();
  let bytes = ByteGadgets::new(&mut b);
  let subject = std::array::from_fn(|_| {
    let value = bytes.input(&mut b, "public subject digest byte");
    b.expose_public(value.value());
    value
  });
  let mut encoded: Vec<_> =
    RECEIPT_PREFIX.iter().map(|&v| bytes.constant(&mut b, v)).collect();
  encoded.extend(subject);
  encoded.push(bytes.constant(&mut b, 0));
  let output = blake3(&mut b, &bytes, &encoded);
  let allowed: Vec<_> =
    allowed_blob().into_iter().map(|v| bytes.constant(&mut b, v)).collect();
  let allowed = blake3(&mut b, &bytes, &allowed);
  let mut claim =
    vec![b.constant(Val::ZERO), b.constant(Val::from_u64(AGGR_INDEX))];
  claim.extend(pack_words(&mut b, &allowed));
  claim.extend(pack_words(&mut b, &output));
  let inputs = constrain_fixed_verifier(
    &mut b,
    &bytes,
    system,
    &profile.shape(system),
    vec![claim],
  );
  StatementVerifier { circuit: b.finish(), inputs, subject }
}
