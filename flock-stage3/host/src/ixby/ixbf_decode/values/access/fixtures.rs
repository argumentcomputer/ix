use super::super::super::{
  bodies::{BodyCapacity, fixtures as bodies},
  dispatch::{test_parse_program, test_parse_transport},
  registry::RegistryOp,
  source::{SourceChunkProofWires, test_chunk_advice},
};
use super::super::{fixtures as forest, *};
use super::*;
use crate::{
  hash::pack_bytes, ixby::bounded_hash::tests as hash_tests,
  sizing::CircuitEmitter,
};
use flock_prover::{circuit::builder::Wire, field::F128};

pub(super) fn proof_wires(
  b: &mut impl CircuitEmitter,
  depth: usize,
) -> SourceChunkProofWires {
  SourceChunkProofWires {
    bytes: std::array::from_fn(|_| b.input()),
    siblings: (0..depth).map(|_| [b.input(), b.input()]).collect(),
  }
}
pub(super) fn query_wires(
  query: &[Wire; 7],
  hints: [Wire; 2],
  one: Wire,
  zero: Wire,
) -> [[Wire; 4]; 4] {
  [
    [one, zero, zero, zero],
    [query[0], query[1], zero, zero],
    [query[2], query[3], query[4], hints[0]],
    [query[5], zero, query[6], hints[1]],
  ]
}
fn bytes(words: &[F128]) -> Vec<u8> {
  words
    .iter()
    .flat_map(|w| w.lo.to_le_bytes().into_iter().chain(w.hi.to_le_bytes()))
    .collect()
}
pub(super) struct Fixture {
  pub name: String,
  pub forest: forest::Fixture,
  pub code_image: Vec<u8>,
  pub image: Vec<u8>,
  pub query: [F128; 7],
  pub hints: [F128; 2],
  pub requests: [[F128; 4]; 4],
  pub records: Vec<Vec<F128>>,
}
impl Fixture {
  pub(super) fn new(
    c: ValueConfig,
    body: BodyCapacity,
    name: &str,
    f: forest::Fixture,
  ) -> Self {
    f.check_native(c.arena);
    let b = bodies::from_source(body, name, f.program.clone(), true);
    let program = test_parse_program(&f.program.bytes, 32).unwrap();
    let grammar = test_parse_transport(c.kind, &f.bytes, &program, 32).unwrap();
    let mut code = vec![pack_bytes(b"IxBy/code/v0\0\0\0\0")];
    for n in [
      c.registry.constructors(),
      c.registry.functions(),
      c.registry.blocks_per_function(),
      body.operands(),
      body.natural().bits(),
    ] {
      code.push(F128::new(n as u64, 0));
    }
    code.extend(hash_tests::expected(&f.program.bytes));
    code.extend(program);
    let mut constructors = vec![F128::ZERO; 7 * c.registry.constructors()];
    for h in
      f.program.headers.iter().filter(|h| h.kind == RegistryOp::Constructor)
    {
      let at = h.index * 7;
      constructors[at] = F128::ONE;
      constructors[at + 1..at + 6].copy_from_slice(&h.fields);
      constructors[at + 6] = h.span;
    }
    code.extend(constructors);
    code.extend(b.bank);
    let code_image = bytes(&code);
    let mut manifest = hash_tests::expected(&code_image).to_vec();
    manifest.extend(hash_tests::expected(&f.bytes));
    manifest.extend(grammar);
    manifest.extend(f.summary);
    // Independent canonical value image: five schema words, then the exact
    // code/source digests, completed grammar/summary and native-checked nodes.
    let mut image = vec![pack_bytes(b"IxBy/values/v0\0\0")];
    for n in [
      c.kind as usize,
      c.arena.nodes(),
      c.arena.depth(),
      c.arena.natural().bits(),
    ] {
      image.push(F128::new(n as u64, 0));
    }
    image.extend(&manifest);
    for r in &f.records {
      image.extend(r);
    }
    image.resize(40 + c.arena.finished_bank_words(), F128::ZERO);
    let query = f.requests();
    let results = f.results(c.arena, &query);
    let width = 1 + c.arena.finished_record_words();
    let hints = [results[width], results[2 * width]];
    let requests = [
      [F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO],
      [query[0], query[1], F128::ZERO, F128::ZERO],
      [query[2], query[3], query[4], hints[0]],
      [query[5], F128::ZERO, query[6], hints[1]],
    ];
    let mut records =
      vec![std::iter::once(F128::ZERO).chain(manifest).collect()];
    records.extend(results.chunks_exact(width).map(<[F128]>::to_vec));
    Self {
      name: name.to_owned(),
      forest: f,
      code_image,
      image: bytes(&image),
      query,
      hints,
      requests,
      records,
    }
  }
  pub(super) fn proofs(&self, c: ValueLayout) -> Vec<F128> {
    let mut out = Vec::new();
    // Manifest and the first root share the first authenticated chunk pair.
    for i in 0..3 {
      let first = offset(c, ValueKind::ALL[i], &self.requests[i]) / 1024;
      let next = (first + 1).min((c.bytes() - 1) / 1024);
      for index in [first, next] {
        out.extend(test_chunk_advice(&self.image, index as usize, c.depth()));
      }
    }
    out
  }
}
pub(super) fn offset(
  c: ValueLayout,
  kind: ValueKind,
  query: &[F128; 4],
) -> u64 {
  if query[0] == F128::ZERO {
    0
  } else if kind == ValueKind::Manifest {
    80
  } else {
    let index = query[if kind == ValueKind::Node { 1 } else { 3 }].lo;
    16 * (40 + index * (13 + c.natural().magnitude_words() as u64))
  }
}
pub(super) fn corpus(c: ValueConfig, body: BodyCapacity) -> Vec<Fixture> {
  let mut out: Vec<_> = forest::corpus(c.kind, c.arena)
    .into_iter()
    .map(|(name, f)| Fixture::new(c, body, name, f))
    .collect();
  for string in [true, false] {
    for byte in *b"ab" {
      let scalar = if string {
        forest::Scalar::String(vec![byte])
      } else {
        forest::Scalar::Bytes(vec![byte])
      };
      let f = forest::encode(
        c.kind,
        c.arena,
        &forest::spec(1),
        &[forest::Value::Scalar(scalar)],
      );
      out.push(Fixture::new(
        c,
        body,
        &format!(
          "payload-{}-{}",
          if string { "string" } else { "bytes" },
          byte as char
        ),
        f,
      ));
    }
  }
  for (name, bit) in [("code-a", 0), ("code-b", 1)] {
    let mut spec = forest::spec(1);
    spec.constructors[0][0] ^= bit;
    let f = forest::encode(c.kind, c.arena, &spec, &[forest::Value::Erased]);
    out.push(Fixture::new(c, body, name, f));
  }
  out
}
