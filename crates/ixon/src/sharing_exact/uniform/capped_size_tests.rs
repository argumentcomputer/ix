use super::*;
use crate::contract::{BinderContract, LetContract, ValueContract};
use crate::serialize::put_expr;
use num_bigint::BigUint;

fn exact_excluded(occ: &BigUint, size: &BigUint, width: u64) -> bool {
  if *occ == BigUint::from(0u8) {
    return false;
  }
  (occ - 1u8) * size < occ * BigUint::from(width)
}

#[test]
fn predicate_caps_match_biguint_including_zero_and_max_width() {
  let cap = BigUint::from(EMPTY_SIZE_CAP);
  let max = BigUint::from(u128::MAX);
  let occs = [0u128, 1, 2, 3, u128::MAX]
    .map(BigUint::from)
    .into_iter()
    .chain([&max + 1u8, BigUint::from(1u8) << 200]);
  let sizes = [
    0u128,
    1,
    2,
    3,
    6,
    u128::from(u64::MAX),
    EMPTY_SIZE_CAP - 1,
    EMPTY_SIZE_CAP,
    EMPTY_SIZE_CAP + 1,
    u128::MAX,
  ]
  .map(BigUint::from)
  .into_iter()
  .chain([BigUint::from(1u8) << 200])
  .collect::<Vec<_>>();
  for occ in occs {
    for size in &sizes {
      for width in [0, 1, 2, 3, u64::MAX - 1, u64::MAX] {
        let o = u128::try_from(occ.clone().min(max.clone())).unwrap();
        let s = u128::try_from(size.clone().min(cap.clone())).unwrap();
        assert_eq!(
          certainly_excluded(o, s, u128::from(width)),
          exact_excluded(&occ, size, width),
          "occ={occ} size={size} w={width}"
        );
      }
    }
  }
  for a in [0, EMPTY_SIZE_CAP - 1, EMPTY_SIZE_CAP, u128::MAX] {
    for b in [0, 1, EMPTY_SIZE_CAP, u128::MAX] {
      assert_eq!(
        BigUint::from(empty_cap_add(a, b)),
        (BigUint::from(a) + BigUint::from(b)).min(cap.clone())
      );
    }
  }
}

// Independent unbounded reference. Own bytes come from the serializer of
// one node with one-byte dummy children, not empty_own_size/Node::own_len.
fn reference(nodes: &[Node]) -> Vec<BigUint> {
  let mut cost: Vec<BigUint> = Vec::new();
  let mut payload: Vec<BigUint> = Vec::new();
  let mut lengths = Vec::new();
  for node in nodes {
    let mut bytes = Vec::new();
    put_expr(&node.to_expr(|_| Expr::var(0)), &mut bytes);
    let mut own = bytes.len() - node.children().as_slice().len();
    let mut body = BigUint::from(0u8);
    let mut length = 0;
    let full = if node.family().is_some() {
      own -= 1; // the single-node telescope header
      let next = ix(spine_next(node));
      let continued = nodes[next].family() == node.family();
      length = if continued { lengths[next] + 1 } else { 1 };
      body = BigUint::from(own)
        + &cost[ix(side_child(node))]
        + if continued { &payload[next] } else { &cost[next] };
      let mut header = Vec::new();
      TagN::put(4, 0, length, &mut header);
      BigUint::from(header.len()) + &body
    } else {
      node
        .children()
        .as_slice()
        .iter()
        .fold(BigUint::from(own), |sum, child| sum + &cost[ix(*child)])
    };
    cost.push(full);
    payload.push(body);
    lengths.push(length);
  }
  cost
}

fn check(nodes: &[Node]) {
  let (len, tail) = spine_tables(nodes, &vec![false; nodes.len()]);
  let actual = empty_sizes_capped(nodes, &len, &tail).unwrap();
  let exact = reference(nodes);
  assert_eq!(actual.len(), exact.len());
  for (actual, expected) in actual.into_iter().zip(exact) {
    assert_eq!(
      BigUint::from(actual),
      expected.min(BigUint::from(EMPTY_SIZE_CAP))
    );
  }
}

#[test]
fn empty_recurrence_matches_biguint_on_payloads_spines_and_random_dags() {
  let mut nodes = vec![
    Node::Var(0),
    Node::Sort(u64::MAX),
    Node::Str(u64::MAX),
    Node::Nat(u64::MAX),
    Node::Ref(u64::MAX, vec![u64::MAX; 1100]),
    Node::Rec(u64::MAX, vec![0, u64::MAX]),
    Node::Prj(u64::MAX, u64::MAX, 0),
    Node::Let(LetContract::plain(false), 1, 2, 3),
  ];
  for _ in 0..300 {
    let t = tid(nodes.len() - 1);
    nodes.push(Node::App(t, t));
  }
  check(&nodes); // exact costs exceed 2^300; never expand an occurrence tree
  let mut spine = vec![Node::Var(0)];
  for _ in 0..1100 {
    spine.push(Node::App(tid(spine.len() - 1), 0));
  }
  check(&spine); // includes TagN length-rung changes
  for seed in 0..1000u64 {
    let mut rng = seed + 1;
    let mut ns = vec![Node::Var(0), Node::Sort(0)];
    for _ in 0..80 {
      rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1);
      let a = u32::try_from(rng % len64(ns.len())).unwrap();
      let b = u32::try_from((rng >> 16) % len64(ns.len())).unwrap();
      ns.push(match rng % 5 {
        0 => Node::App(a, b),
        1 => Node::Lam(BinderContract::default(), a, b),
        2 => {
          Node::All(BinderContract::default(), ValueContract::default(), a, b)
        },
        3 => Node::Let(LetContract::plain(true), a, b, a),
        _ => Node::Prj(rng, rng >> 32, a),
      });
    }
    check(&ns);
  }
}
