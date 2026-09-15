//! Independent encodings and expected preorder records. They never select
//! circuit events, parentage, references, insertion addresses, or read answers.
use super::super::registry::fixtures as program;
pub(super) use super::super::registry::fixtures::{
  Function, Spec, base, nat, word,
};
use super::*;
use crate::ixby::ixbf;
use flock_prover::field::F128;

#[derive(Clone, Debug)]
pub(super) enum Scalar {
  Nat(Vec<u8>),
  String(Vec<u8>),
  Bool(bool),
  Word(u32),
  Gold(u64),
  Extension([u64; 2]),
  Bytes(Vec<u8>),
}
#[derive(Clone, Debug)]
pub(super) enum Value {
  Scalar(Scalar),
  Constructor(usize, Vec<Value>),
  Pap(usize, Vec<Value>),
  Erased,
}
#[derive(Clone)]
pub(super) struct Fixture {
  pub program: program::Fixture,
  pub bytes: Vec<u8>,
  pub records: Vec<Vec<F128>>,
  pub summary: [F128; 3],
  pub kind: GrammarKind,
}
impl Fixture {
  pub(super) fn requests(&self) -> [F128; 7] {
    let node = self.records.last().map(|_| self.records.len() - 1);
    let child = self.records.iter().position(|r| r[CHILDREN] != F128::ZERO);
    [
      word(u128::from(node.is_some())),
      word(node.unwrap_or(0) as u128),
      word(u128::from(child.is_some())),
      word(child.unwrap_or(0) as u128),
      F128::ZERO,
      word(u128::from(node.is_some())),
      F128::ZERO,
    ]
  }
  pub(super) fn results(
    &self,
    a: ValueCapacity,
    request: &[F128; 7],
  ) -> Vec<F128> {
    let mut out = Vec::new();
    let r = a.record_words();
    for (op, enabled, index, owner) in [
      (ValueOp::ReadNode, request[0], request[1], F128::ZERO),
      (ValueOp::ReadChild, request[2], request[4], request[3]),
      (ValueOp::ReadRoot, request[5], request[6], F128::ZERO),
    ] {
      if enabled == F128::ZERO {
        out.extend(vec![F128::ZERO; 1 + a.finished_record_words()]);
        continue;
      }
      let (i, record) = self
        .records
        .iter()
        .enumerate()
        .find(|(i, rec)| {
          if op == ValueOp::ReadNode {
            word(*i as u128) == index
          } else {
            rec[r]
              == if op == ValueOp::ReadRoot {
                F128::ZERO
              } else {
                F128::new(owner.lo + 1, 0)
              }
              && rec[r + 1] == index
          }
        })
        .unwrap();
      out.push(word(i as u128));
      out.extend(record);
    }
    out
  }
  pub(super) fn check_native(&self, a: ValueCapacity) {
    let artifact =
      ixbf::decode_program(&self.program.bytes, ixbf::DecodeLimits::default())
        .unwrap();
    assert_eq!(artifact.encode(), self.program.bytes);
    if self.kind == GrammarKind::Input {
      let input = ixbf::decode_input(
        &artifact,
        &self.bytes,
        ixbf::DecodeLimits::default(),
      )
      .unwrap();
      assert_eq!(input.encode(), self.bytes);
      self.check_forest(a, &artifact, input.values());
    } else {
      let output = ixbf::decode_output(
        &artifact,
        &self.bytes,
        ixbf::DecodeLimits::default(),
      )
      .unwrap();
      assert_eq!(output.encode(), self.bytes);
      self.check_forest(a, &artifact, output.values());
    }
  }
  fn check_forest(
    &self,
    a: ValueCapacity,
    artifact: &ixbf::Artifact<'_>,
    forest: &ixbf::ValueForest<'_>,
  ) {
    let r = a.record_words();
    assert_eq!(
      self.summary,
      [
        word(forest.nodes().len() as u128),
        word(forest.roots().len() as u128),
        word(forest.depth() as u128)
      ]
    );
    for (i, (node, rec)) in forest.nodes().iter().zip(&self.records).enumerate()
    {
      let children: Vec<_> = self
        .records
        .iter()
        .enumerate()
        .filter_map(|(j, v)| (v[r] == word((i + 1) as u128)).then_some(j))
        .collect();
      assert_eq!(node.children, children);
      assert_eq!(rec[CHILDREN], word(children.len() as u128));
      match &node.kind {
        ixbf::ValueKind::Erased => assert_eq!(rec[KIND], word(3)),
        ixbf::ValueKind::Constructor(id) => {
          assert_eq!(rec[KIND], word(1));
          assert_eq!(
            *id,
            artifact.constructors()[rec[REFERENCE].lo as usize].id
          );
        },
        ixbf::ValueKind::PartialApplication(f) => {
          assert_eq!(rec[KIND], word(2));
          assert_eq!(rec[REFERENCE], word(*f as u128));
        },
        ixbf::ValueKind::Scalar(s) => {
          assert_eq!(rec[KIND], F128::ZERO);
          let range = rec[PAYLOAD];
          let payload =
            &self.bytes[range.lo as usize..(range.lo + range.hi) as usize];
          let tag = match s {
            ixbf::Scalar::Nat(n) => {
              let mut bytes = Vec::new();
              for w in &rec[MAGNITUDE..r] {
                bytes.extend(w.lo.to_le_bytes());
                bytes.extend(w.hi.to_le_bytes());
              }
              assert_eq!(*n, num_bigint::BigUint::from_bytes_le(&bytes));
              0
            },
            ixbf::Scalar::String(s) => {
              assert_eq!(s.as_bytes(), payload);
              1
            },
            ixbf::Scalar::Bool(v) => {
              assert_eq!(rec[FIXED], word(u128::from(*v)));
              2
            },
            ixbf::Scalar::Word32(v) => {
              assert_eq!(rec[FIXED], word(*v as u128));
              3
            },
            ixbf::Scalar::Goldilocks(v) => {
              assert_eq!(rec[FIXED], word(*v as u128));
              4
            },
            ixbf::Scalar::Extension(v) => {
              assert_eq!(rec[FIXED], F128::new(v[0], v[1]));
              5
            },
            ixbf::Scalar::Bytes(v) => {
              assert_eq!(*v, payload);
              6
            },
          };
          assert_eq!(rec[SCALAR], word(tag));
        },
      }
    }
    let roots: Vec<_> = self
      .records
      .iter()
      .enumerate()
      .filter_map(|(i, rec)| (rec[r] == F128::ZERO).then_some(i))
      .collect();
    assert_eq!(roots, forest.roots());
  }
}
pub(super) fn encode(
  kind: GrammarKind,
  a: ValueCapacity,
  spec: &Spec,
  values: &[Value],
) -> Fixture {
  let mut bytes =
    if kind == GrammarKind::Input { b"IXFI" } else { b"IXFO" }.to_vec();
  bytes.extend(b"\x01\0\0\0\0\0\0\0");
  if kind == GrammarKind::Input {
    nat(&mut bytes, values.len() as u128);
  }
  let mut records = Vec::new();
  for (ordinal, value) in values.iter().enumerate() {
    encode_value(a, spec, value, &mut bytes, &mut records, [0, ordinal, 1]);
  }
  let depth =
    records.iter().map(|r| r[a.record_words() + 3].lo).max().unwrap_or(0);
  let summary = [
    word(records.len() as u128),
    word(values.len() as u128),
    word(depth as u128),
  ];
  Fixture { program: program::encode(spec), bytes, records, summary, kind }
}
fn encode_value(
  a: ValueCapacity,
  spec: &Spec,
  v: &Value,
  bytes: &mut Vec<u8>,
  records: &mut Vec<Vec<F128>>,
  tree: [usize; 3],
) {
  let r = a.record_words();
  let index = records.len();
  let start = bytes.len();
  let mut record = vec![F128::ZERO; a.finished_record_words()];
  record[PRESENT] = F128::ONE;
  let children = match v {
    Value::Erased => {
      bytes.push(3);
      record[KIND] = word(3);
      None
    },
    Value::Constructor(i, children) => {
      bytes.push(1);
      record[KIND] = word(1);
      record[REFERENCE] = word(*i as u128);
      let id = spec.constructors[*i];
      for v in &id[..2] {
        bytes.extend(v.to_le_bytes());
      }
      for v in &id[2..4] {
        nat(bytes, *v);
      }
      Some(children)
    },
    Value::Pap(i, children) => {
      bytes.push(2);
      nat(bytes, *i as u128);
      record[KIND] = word(2);
      record[REFERENCE] = word(*i as u128);
      Some(children)
    },
    Value::Scalar(s) => {
      bytes.push(0);
      match s {
        Scalar::Nat(digits) => {
          bytes.push(0);
          let at = bytes.len();
          bytes.extend(digits);
          record[PAYLOAD] = F128::new(at as u64, digits.len() as u64);
          for (i, digit) in digits.iter().enumerate() {
            for bit in 0..7 {
              if digit & (1 << bit) != 0 {
                let pos = i * 7 + bit;
                let w = &mut record[MAGNITUDE + pos / 128];
                if pos % 128 < 64 {
                  w.lo |= 1 << (pos % 128);
                } else {
                  w.hi |= 1 << (pos % 128 - 64);
                }
              }
            }
          }
        },
        Scalar::String(payload) | Scalar::Bytes(payload) => {
          let tag = if matches!(s, Scalar::String(_)) { 1 } else { 6 };
          bytes.push(tag);
          nat(bytes, payload.len() as u128);
          record[SCALAR] = word(tag as u128);
          record[PAYLOAD] = F128::new(bytes.len() as u64, payload.len() as u64);
          bytes.extend(payload);
        },
        Scalar::Bool(v) => {
          bytes.extend([2, u8::from(*v)]);
          record[SCALAR] = word(2);
          record[FIXED] = word(u128::from(*v));
        },
        Scalar::Word(v) => {
          bytes.push(3);
          bytes.extend(v.to_le_bytes());
          record[SCALAR] = word(3);
          record[FIXED] = word(*v as u128);
        },
        Scalar::Gold(v) => {
          bytes.push(4);
          bytes.extend(v.to_le_bytes());
          record[SCALAR] = word(4);
          record[FIXED] = word(*v as u128);
        },
        Scalar::Extension(v) => {
          bytes.push(5);
          for w in v {
            bytes.extend(w.to_le_bytes());
          }
          record[SCALAR] = word(5);
          record[FIXED] = F128::new(v[0], v[1]);
        },
      };
      None
    },
  };
  if let Some(children) = children {
    nat(bytes, children.len() as u128);
    record[CHILDREN] = word(children.len() as u128);
  }
  record[SPAN] = F128::new(start as u64, bytes.len() as u64);
  for (j, v) in tree.into_iter().enumerate() {
    record[r + if j == 2 { 3 } else { j }] = word(v as u128);
  }
  records.push(record);
  if let Some(children) = children {
    for (ordinal, child) in children.iter().enumerate() {
      encode_value(
        a,
        spec,
        child,
        bytes,
        records,
        [index + 1, ordinal, tree[2] + 1],
      );
    }
  }
  records[index][r + 2] = word(records.len() as u128);
  records[index][r + 4] = F128::new(start as u64, bytes.len() as u64);
}
pub(super) fn spec(roots: usize) -> Spec {
  let mut s = base();
  s.entry = 1;
  s.constructors = vec![
    [1u128 << 127, 3, 1u128 << 100, u128::MAX, 1],
    [1u128 << 127, 3, 1u128 << 100, u128::MAX - 1, 2],
  ];
  s.functions.push(Function {
    arity: roots as u128,
    entry: 0,
    blocks: vec![(roots as u128, vec![1, 2])],
  });
  s.functions[0].arity = 3;
  s.functions[0].blocks[0].0 = 3;
  s
}
pub(super) fn corpus(
  kind: GrammarKind,
  a: ValueCapacity,
) -> Vec<(&'static str, Fixture)> {
  use self::Scalar as S;
  use Value::*;
  let mut string = vec![b'a'; 65];
  string[31..35].copy_from_slice("𐀀".as_bytes());
  let mut large = vec![255; 585];
  large.push(1);
  let values = vec![
    ("erased", Erased),
    ("zero", Scalar(S::Nat(vec![0]))),
    ("nat4096", Scalar(S::Nat(large))),
    ("string", Scalar(S::String(string))),
    ("empty-string", Scalar(S::String(vec![]))),
    ("bool", Scalar(S::Bool(true))),
    ("word", Scalar(S::Word(0x8000_00ff))),
    ("gold", Scalar(S::Gold(0xffff_ffff_0000_0000))),
    ("extension", Scalar(S::Extension([0xffff_ffff_0000_0000, 7]))),
    ("bytes", Scalar(S::Bytes((0..800).map(|i| i as u8).collect()))),
    ("empty-bytes", Scalar(S::Bytes(vec![]))),
    (
      "nested",
      Constructor(1, vec![Pap(0, vec![Scalar(S::Nat(vec![255, 1]))]), Erased]),
    ),
    ("chain", Constructor(0, vec![Constructor(0, vec![Pap(0, vec![Erased])])])),
    ("pap", Pap(1, vec![])),
  ];
  let mut out: Vec<_> = values
    .into_iter()
    .map(|(name, v)| (name, encode(kind, a, &spec(1), &[v])))
    .collect();
  let mut swapped = spec(1);
  swapped.constructors.swap(0, 1);
  out.push((
    "reordered",
    encode(kind, a, &swapped, &[Constructor(1, vec![Erased])]),
  ));
  if kind == GrammarKind::Input {
    out.push(("empty-input", encode(kind, a, &spec(0), &[])));
    out.push((
      "multiple-roots",
      encode(
        kind,
        a,
        &spec(2),
        &[Constructor(0, vec![Erased]), Pap(0, vec![Scalar(S::Bool(false))])],
      ),
    ));
  }
  out
}
