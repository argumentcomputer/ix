//! Decode the trusted Lean bytecode export. No native code generation.
use aiur::{
  G,
  bytecode::{Block, Circuit, Ctrl, Function, FunctionLayout, Op, Toplevel},
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
    "call" => {
      assert_eq!(
        a[3].as_bool(),
        Some(false),
        "unconstrained calls are forbidden"
      );
      Op::Call(n(&a[0]), ns(&a[1]), n(&a[2]), false)
    },
    "store" => Op::Store(ns(a)),
    "load" => Op::Load(n(&a[0]), n(&a[1])),
    "assertEq" => {
      Op::AssertEq(ns(&a[0]), ns(&a[1]), a[2].as_str().map(str::to_owned))
    },
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
