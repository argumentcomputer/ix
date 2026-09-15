use super::super::{
  bodies::{BodyCapacity, fixtures as body},
  dispatch::test_parse_program,
  registry::RegistryOp,
  source::*,
};
use super::*;
use crate::{hash::pack_bytes, sizing::CircuitEmitter};
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
  query: &[Wire; 15],
  one: Wire,
  zero: Wire,
) -> [[Wire; 4]; 7] {
  [
    [one, zero, zero, zero],
    [query[13], query[14], zero, zero],
    [query[0], query[1], zero, zero],
    [one, zero, zero, zero],
    [query[2], query[3], query[4], zero],
    query[5..9].try_into().unwrap(),
    query[9..13].try_into().unwrap(),
  ]
}
pub(super) const KINDS: [CodeKind; 7] = [
  CodeKind::Program,
  CodeKind::Constructor,
  CodeKind::Function,
  CodeKind::Function,
  CodeKind::Block,
  CodeKind::Operand,
  CodeKind::Alternative,
];

pub(super) struct Fixture {
  pub name: String,
  pub original: Vec<u8>,
  pub image: Vec<u8>,
  pub query: [F128; 15],
  pub results: Vec<F128>,
  pub records: Vec<Vec<F128>>,
  pub requests: [[F128; 4]; 7],
  pub prove: bool,
}
impl Fixture {
  pub(super) fn new(c: BodyCapacity, f: body::Fixture) -> Self {
    let layout = CodeLayout::from_bodies(c);
    let state = test_parse_program(&f.source.bytes, 32).unwrap();
    // Separate canonical serialization from the compiler-side wire packing.
    let mut words = vec![pack_bytes(b"IxBy/code/v0\0\0\0\0")];
    for n in [
      c.registry().constructors(),
      c.registry().functions(),
      c.registry().blocks_per_function(),
      c.operands(),
      c.natural().bits(),
    ] {
      words.push(F128::new(n as u64, 0));
    }
    let root = crate::ixby::bounded_hash::tests::expected(&f.source.bytes);
    words.extend(root);
    words.extend(state);
    let mut constructors = vec![F128::ZERO; c.registry().constructors() * 7];
    let mut query = [F128::ZERO; 15];
    query[..13].copy_from_slice(&f.queries(c));
    for h in
      f.source.headers.iter().filter(|h| h.kind == RegistryOp::Constructor)
    {
      let at = h.index * 7;
      constructors[at] = F128::ONE;
      constructors[at + 1..at + 6].copy_from_slice(&h.fields);
      constructors[at + 6] = h.span;
      query[13] = F128::ONE;
      query[14] = F128::new(h.index as u64, 0);
    }
    words.extend(&constructors);
    words.extend(&f.bank);
    assert_eq!(words.len() as u64, layout.words());
    let image = words
      .iter()
      .flat_map(|w| w.lo.to_le_bytes().into_iter().chain(w.hi.to_le_bytes()))
      .collect();
    let old = f.results(c, query[..13].try_into().unwrap());
    let ctor = if query[13] == F128::ZERO {
      vec![F128::ZERO; 7]
    } else {
      constructors[query[14].lo as usize * 7..(query[14].lo as usize + 1) * 7]
        .to_vec()
    };
    let records = vec![
      root.into_iter().chain(state).collect(),
      ctor,
      old[..5].to_vec(),
      f.bank[..5].to_vec(),
      old[5..19].to_vec(),
      old[19..19 + c.operand_words()].to_vec(),
      old[19 + c.operand_words()..].to_vec(),
    ];
    let requests = [
      [F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO],
      [query[13], query[14], F128::ZERO, F128::ZERO],
      [query[0], query[1], F128::ZERO, F128::ZERO],
      [F128::ONE, F128::ZERO, F128::ZERO, F128::ZERO],
      [query[2], query[3], query[4], F128::ZERO],
      query[5..9].try_into().unwrap(),
      query[9..13].try_into().unwrap(),
    ];
    Self {
      name: f.name,
      original: f.source.bytes,
      image,
      query,
      results: records.iter().flatten().copied().collect(),
      records,
      requests,
      prove: f.prove,
    }
  }
  pub(super) fn proofs(&self, layout: CodeLayout) -> Vec<F128> {
    let mut out = Vec::new();
    // The first pair serves Program, Constructor, and two Function reads.
    // Three further pairs serve Block, Operand, and Alternative respectively.
    for i in [0, 4, 5, 6] {
      let offset = offset(layout, KINDS[i], &self.requests[i]);
      let first = (offset / 1024).min((layout.bytes() - 1) / 1024);
      let next = (first + 1).min((layout.bytes() - 1) / 1024);
      for index in [first, next] {
        out.extend(test_chunk_advice(
          &self.image,
          index as usize,
          layout.depth(),
        ));
      }
    }
    out
  }
}
/// Independent checked-integer address calculation for honest requests.
pub(super) fn offset(c: CodeLayout, kind: CodeKind, q: &[F128; 4]) -> u64 {
  if q[0] == F128::ZERO {
    return 0;
  }
  let owner = q[1].lo;
  let block = q[2].lo;
  let ordinal = q[3].lo;
  let ctor = 6 + 30;
  let functions = ctor + c.constructors() * 7;
  let body = functions + c.functions() * 5;
  let operand = 7 + c.natural().magnitude_words() as u64;
  let stride = 14 + c.operands_per_block() * operand + c.constructors() * 4;
  let record = body + (owner * c.blocks_per_function() + block) * stride;
  16 * match kind {
    CodeKind::Program => 6,
    CodeKind::Constructor => ctor + 7 * owner,
    CodeKind::Function => functions + 5 * owner,
    CodeKind::Block => record,
    CodeKind::Operand => record + 14 + ordinal * operand,
    CodeKind::Alternative => {
      record + 14 + c.operands_per_block() * operand + ordinal * 4
    },
  }
}
pub(super) fn corpus(c: BodyCapacity) -> Vec<Fixture> {
  let mut out: Vec<_> =
    body::corpus(c).into_iter().map(|f| Fixture::new(c, f)).collect();
  for (tag, name) in [(1, "string"), (6, "bytes")] {
    for value in *b"ab" {
      let mut spec = body::base();
      spec.functions[0].blocks[0].1 = vec![1, 1, tag, 1, value];
      out.push(Fixture::new(
        c,
        body::encode(
          c,
          &format!("payload-{name}-{}", value as char),
          &spec,
          true,
        ),
      ));
    }
  }
  let mut spec = body::base();
  spec.functions.push(body::Function {
    arity: 1,
    entry: 0,
    blocks: vec![(1, vec![1, 0, 0]), (0, vec![0, 1, 42, 3, 2, 2, 2, 0])],
  });
  out.push(Fixture::new(c, body::encode(c, "tail-chunk", &spec, true)));
  out
}
