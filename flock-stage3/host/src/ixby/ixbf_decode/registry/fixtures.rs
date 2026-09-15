//! Independently encoded original-wire fixtures and header spans. These data
//! never choose the circuit's dispatch schedule or insertion/read selectors.
use super::*;
use flock_prover::field::F128;

#[derive(Clone)]
pub(in crate::ixby::ixbf_decode) struct Function {
  pub arity: u128,
  pub entry: usize,
  pub blocks: Vec<(u128, Vec<u8>)>,
}
#[derive(Clone)]
pub(in crate::ixby::ixbf_decode) struct Spec {
  pub constructors: Vec<[u128; 5]>,
  pub functions: Vec<Function>,
  pub entry: usize,
  pub wide_limits: bool,
}
#[derive(Clone, Debug)]
pub(in crate::ixby::ixbf_decode) struct Header {
  pub kind: RegistryOp,
  pub owner: usize,
  pub index: usize,
  pub fields: [F128; 5],
  pub span: F128,
}
#[derive(Clone)]
pub(in crate::ixby::ixbf_decode) struct Fixture {
  pub bytes: Vec<u8>,
  pub headers: Vec<Header>,
}
pub(in crate::ixby::ixbf_decode) fn word(value: u128) -> F128 {
  F128::new(value as u64, (value >> 64) as u64)
}
pub(in crate::ixby::ixbf_decode) fn nat(bytes: &mut Vec<u8>, mut n: u128) {
  loop {
    let digit = (n & 127) as u8;
    n >>= 7;
    bytes.push(digit | if n == 0 { 0 } else { 128 });
    if n == 0 {
      break;
    }
  }
}
fn record(
  headers: &mut Vec<Header>,
  kind: RegistryOp,
  owner: usize,
  index: usize,
  fields: &[u128],
  start: usize,
  end: usize,
) {
  let mut words = [F128::ZERO; 5];
  for (out, value) in words.iter_mut().zip(fields) {
    *out = word(*value);
  }
  headers.push(Header {
    kind,
    owner,
    index,
    fields: words,
    span: F128::new(start as u64, end as u64),
  });
}
pub(in crate::ixby::ixbf_decode) fn encode(spec: &Spec) -> Fixture {
  let mut bytes = b"IXBF\x01\0\0\0\0\0\0\0".to_vec();
  let mut limits = [8u128, 8, 8, 8, 8, 8, 32, 4096, 900, 900];
  if spec.wide_limits {
    limits[3] = u128::MAX;
    limits[4] = u128::MAX;
  }
  for value in limits.into_iter().chain([
    1u128 << 100,
    spec.entry as u128,
    spec.constructors.len() as u128,
  ]) {
    nat(&mut bytes, value);
  }
  let mut headers = Vec::new();
  for (index, fields) in spec.constructors.iter().enumerate() {
    let start = bytes.len();
    for value in &fields[..2] {
      bytes.extend(value.to_le_bytes());
    }
    for value in &fields[2..] {
      nat(&mut bytes, *value);
    }
    record(
      &mut headers,
      RegistryOp::Constructor,
      0,
      index,
      fields,
      start,
      bytes.len(),
    );
  }
  nat(&mut bytes, spec.functions.len() as u128);
  for (index, function) in spec.functions.iter().enumerate() {
    let start = bytes.len();
    let fields =
      [function.arity, function.entry as u128, function.blocks.len() as u128];
    for value in fields {
      nat(&mut bytes, value);
    }
    record(
      &mut headers,
      RegistryOp::Function,
      0,
      index,
      &fields,
      start,
      bytes.len(),
    );
    for (block, (locals, instruction)) in function.blocks.iter().enumerate() {
      let start = bytes.len();
      nat(&mut bytes, *locals);
      bytes.push(instruction[0]);
      record(
        &mut headers,
        RegistryOp::Block,
        index,
        block,
        &[*locals, instruction[0] as u128],
        start,
        bytes.len(),
      );
      bytes.extend_from_slice(&instruction[1..]);
    }
  }
  Fixture { bytes, headers }
}
pub(in crate::ixby::ixbf_decode) fn base() -> Spec {
  Spec {
    constructors: vec![],
    functions: vec![Function {
      arity: 0,
      entry: 0,
      blocks: vec![(0, vec![1, 2])],
    }],
    entry: 0,
    wide_limits: false,
  }
}
pub(in crate::ixby::ixbf_decode) fn multi() -> Spec {
  Spec {
    constructors: vec![
      [1u128 << 127, 3, 1u128 << 100, u128::MAX, 0],
      [1u128 << 127, 3, 1u128 << 100, u128::MAX - 1, 1],
    ],
    functions: vec![
      Function {
        arity: 0,
        entry: 1,
        blocks: vec![(1, vec![1, 0, 0]), (0, vec![1, 2])],
      },
      Function {
        arity: 2,
        entry: 0,
        blocks: vec![(2, vec![1, 0, 1]), (3, vec![1, 0, 2])],
      },
    ],
    entry: 1,
    wide_limits: false,
  }
}
pub(in crate::ixby::ixbf_decode) fn corpus() -> Vec<Spec> {
  let one = {
    let mut spec = base();
    spec.constructors = vec![[1, 2, 3, 4, 1]];
    spec.functions[0] =
      Function { arity: 1, entry: 0, blocks: vec![(1, vec![1, 0, 0])] };
    spec
  };
  let changed = {
    let mut spec = multi();
    spec.constructors[0][0] ^= 1;
    spec.constructors[1][2] ^= 1 << 126;
    spec.functions[0] = Function {
      arity: 1,
      entry: 1,
      blocks: vec![(2, vec![1, 0, 1]), (1, vec![1, 0, 0])],
    };
    spec.functions[1] = Function {
      arity: 3,
      entry: 0,
      blocks: vec![(3, vec![1, 0, 2]), (4, vec![1, 0, 3])],
    };
    spec
  };
  let forward = {
    let mut spec = base();
    spec.functions.push(spec.functions[0].clone());
    spec.functions[0].blocks[0].1 = vec![2, 1, 0]; // tail-call function 1, zero arguments
    spec
  };
  let string = {
    let mut spec = base();
    let mut instruction = vec![1, 1, 1]; // return literal String
    nat(&mut instruction, 512);
    let mut string = vec![b'a'; 512];
    string[31..35].copy_from_slice("𐀀".as_bytes());
    instruction.extend(string);
    spec.functions[0].blocks[0].1 = instruction;
    spec
  };
  let natural = {
    let mut spec = base();
    let mut instruction = vec![1, 1, 0]; // return literal Nat, bit 4095 set
    instruction.extend(vec![255; 585]);
    instruction.push(1);
    spec.functions[0].blocks[0].1 = instruction;
    spec
  };
  let wide = {
    let mut spec = base();
    spec.wide_limits = true;
    spec.constructors = vec![[5, 6, u128::MAX, u128::MAX, u128::MAX]];
    spec.functions[0].arity = 1u128 << 100;
    spec.functions[0].blocks[0].0 = 1u128 << 100;
    spec
  };
  vec![base(), one, multi(), changed, forward, string, natural, wide]
}

impl Fixture {
  /// These requests are independently expected public query parameters,
  /// not instruction/reference semantics or a prover-chosen approval policy.
  pub(in crate::ixby::ixbf_decode) fn requests(&self, last: bool) -> [F128; 7] {
    let select = |kind| {
      let mut entries = self.headers.iter().filter(|h| h.kind == kind);
      if last { entries.next_back() } else { entries.next() }
    };
    let constructor = select(RegistryOp::Constructor);
    let function = select(RegistryOp::Function).unwrap();
    let block = select(RegistryOp::Block).unwrap();
    [
      word(u128::from(constructor.is_some())),
      word(constructor.map_or(0, |h| h.index) as u128),
      F128::ONE,
      word(function.index as u128),
      F128::ONE,
      word(block.owner as u128),
      word(block.index as u128),
    ]
  }
  pub(in crate::ixby::ixbf_decode) fn results(
    &self,
    request: &[F128; 7],
  ) -> Vec<F128> {
    let mut output = Vec::new();
    for (kind, enabled, index, owner) in [
      (RegistryOp::Constructor, request[0], request[1], F128::ZERO),
      (RegistryOp::Function, request[2], request[3], F128::ZERO),
      (RegistryOp::Block, request[4], request[6], request[5]),
    ] {
      if enabled == F128::ZERO {
        assert_eq!([index, owner], [F128::ZERO; 2]);
        output.extend([F128::ZERO; 6]);
      } else {
        assert_eq!(enabled, F128::ONE);
        let header = self
          .headers
          .iter()
          .find(|h| {
            h.kind == kind
              && word(h.index as u128) == index
              && word(h.owner as u128) == owner
          })
          .unwrap();
        output.extend(header.fields);
        output.push(header.span);
      }
    }
    output
  }
}
