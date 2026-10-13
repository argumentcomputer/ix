//! Decode the same trusted benchmark wire format as tools/ixvm-bench, including
//! the compiler's circuit partition (required for proving, unlike execution).
use aiur::{
  G,
  bytecode::{Block, Circuit, Ctrl, Function, FunctionLayout, Op, Toplevel},
  execute::{IOBuffer, IOKeyInfo},
};
use multi_stark::p3_field::PrimeCharacteristicRing;
use serde_json::Value;

pub fn n(v: &Value) -> usize {
  usize::try_from(v.as_u64().unwrap()).unwrap()
}
fn ns(v: &Value) -> Vec<usize> {
  v.as_array().unwrap().iter().map(n).collect()
}
pub fn gs(v: &Value) -> Vec<G> {
  v.as_array()
    .unwrap()
    .iter()
    .map(|v| G::from_u64(v.as_u64().unwrap()))
    .collect()
}
fn tagged(v: &Value) -> (&str, &Value) {
  let map = v.as_object().unwrap();
  assert_eq!(map.len(), 1);
  let (k, v) = map.iter().next().unwrap();
  (k, v)
}
fn op(v: &Value) -> Op {
  let (kind, a) = tagged(v);
  match kind {
    "const" => Op::Const(G::from_u64(a.as_u64().unwrap())),
    "add" => Op::Add(n(&a[0]), n(&a[1])),
    "sub" => Op::Sub(n(&a[0]), n(&a[1])),
    "mul" => Op::Mul(n(&a[0]), n(&a[1])),
    "eqZero" => Op::EqZero(n(a)),
    "call" => Op::Call(n(&a[0]), ns(&a[1]), n(&a[2]), a[3].as_bool().unwrap()),
    "store" => Op::Store(ns(a)),
    "load" => Op::Load(n(&a[0]), n(&a[1])),
    "assertEq" => {
      Op::AssertEq(ns(&a[0]), ns(&a[1]), a[2].as_str().map(str::to_owned))
    },
    "ioGetInfo" => Op::IOGetInfo(n(&a[0]), ns(&a[1])),
    "ioRead" => Op::IORead(n(&a[0]), n(&a[1]), n(&a[2])),
    // This benchmark reuses read-only input arenas between fresh executions.
    "ioWrite" | "ioSetInfo" => panic!("benchmark requires read-only IO"),
    "u8BitDecomposition" => Op::U8BitDecomposition(n(a)),
    "u8ShiftLeft" => Op::U8ShiftLeft(n(a)),
    "u8ShiftRight" => Op::U8ShiftRight(n(a)),
    "u8Xor" => Op::U8Xor(n(&a[0]), n(&a[1])),
    "u8Add" => Op::U8Add(n(&a[0]), n(&a[1])),
    "u8Mul" => Op::U8Mul(n(&a[0]), n(&a[1])),
    "u8Sub" => Op::U8Sub(n(&a[0]), n(&a[1])),
    "u8And" => Op::U8And(n(&a[0]), n(&a[1])),
    "u8Or" => Op::U8Or(n(&a[0]), n(&a[1])),
    "u8LessThan" => Op::U8LessThan(n(&a[0]), n(&a[1])),
    "u32LessThan" => Op::U32LessThan(n(&a[0]), n(&a[1])),
    "u8XorSplit7" => Op::U8XorSplit7(n(&a[0]), n(&a[1])),
    "u8XorSplit4" => Op::U8XorSplit4(n(&a[0]), n(&a[1])),
    "u8RangeCheck" => Op::U8RangeCheck(n(&a[0]), n(&a[1])),
    "unconstrainedBigUintDivMod" => {
      Op::UnconstrainedBigUintDivMod(n(&a[0]), n(&a[1]))
    },
    "unconstrainedGToBytes" => Op::UnconstrainedGToBytes(n(a)),
    "unconstrainedGInverse" => Op::UnconstrainedGInverse(n(a)),
    "unconstrainedU32Add" => Op::UnconstrainedU32Add(ns(&a[0]), ns(&a[1])),
    "unconstrainedU32Add3" => {
      Op::UnconstrainedU32Add3(ns(&a[0]), ns(&a[1]), ns(&a[2]))
    },
    "u32ToField" => Op::U32ToField(ns(a)),
    other => panic!("unsupported benchmark operation: {other}"),
  }
}
fn block(v: &Value) -> Block {
  let (kind, a) = tagged(&v["ctrl"]);
  let ctrl = match kind {
    "return" => Ctrl::Return(n(&a[0]), ns(&a[1])),
    "yield" => Ctrl::Yield(n(&a[0]), ns(&a[1])),
    "match" | "matchContinue" => {
      let cases = a[1]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| (G::from_u64(v[0].as_u64().unwrap()), block(&v[1])))
        .collect();
      let default = (!a[2].is_null()).then(|| Box::new(block(&a[2])));
      if kind == "match" {
        Ctrl::Match(n(&a[0]), cases, default)
      } else {
        Ctrl::MatchContinue(
          n(&a[0]),
          cases,
          default,
          n(&a[3]),
          n(&a[4]),
          n(&a[5]),
          Box::new(block(&a[6])),
        )
      }
    },
    other => panic!("unsupported control: {other}"),
  };
  Block { ops: v["ops"].as_array().unwrap().iter().map(op).collect(), ctrl }
}
pub fn program(v: &Value) -> Toplevel {
  let functions: Vec<Function> = v["functions"]
    .as_array()
    .unwrap()
    .iter()
    .map(|f| {
      let l = &f["layout"];
      Function {
        body: block(&f["body"]),
        layout: FunctionLayout {
          input_size: n(&l["inputSize"]),
          selectors: n(&l["selectors"]),
          auxiliaries: n(&l["auxiliaries"]),
          lookups: n(&l["lookups"]),
        },
        entry: f["entry"].as_bool().unwrap(),
        constrained: f["constrained"].as_bool().unwrap(),
      }
    })
    .collect();
  Toplevel {
    functions,
    memory_sizes: ns(&v["memory_sizes"]),
    circuits: v["circuits"]
      .as_array()
      .expect("export must include the circuit partition")
      .iter()
      .map(|c| {
        let l = &c["layout"];
        Circuit {
          members: ns(&c["members"]),
          layout: FunctionLayout {
            input_size: n(&l["inputSize"]),
            selectors: n(&l["selectors"]),
            auxiliaries: n(&l["auxiliaries"]),
            lookups: n(&l["lookups"]),
          },
        }
      })
      .collect(),
  }
}
fn extend(io: &mut IOBuffer, channel: u8, key: Vec<G>, value: Vec<G>) {
  let ch = G::from_u8(channel);
  let arena = io.data.entry(ch).or_default();
  let info = IOKeyInfo { idx: arena.len(), len: value.len() };
  arena.extend(value);
  assert!(io.map.insert((ch, key), info).is_none());
}
pub fn witness(fixture: &Value) -> IOBuffer {
  let mut io = IOBuffer { data: Default::default(), map: Default::default() };
  for row in fixture["constants"]
    .as_array()
    .unwrap()
    .iter()
    .chain(fixture.get("invalidProof"))
  {
    extend(&mut io, 2, gs(&row["address"]), gs(&row["bytes"]));
    extend(
      &mut io,
      3,
      gs(&row["address"]),
      vec![G::from_u64(row["hint"].as_u64().unwrap())],
    );
  }
  for row in fixture["blobs"].as_array().unwrap() {
    extend(&mut io, 4, gs(&row["address"]), gs(&row["bytes"]));
  }
  io
}
