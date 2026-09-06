//! Scratch allocation regressions: results remain call-local while capacity
//! adapts to a large binder-opening traversal followed by tiny substitutions.

use super::*;
use crate::env::KEnv;
use crate::id::KId;
use crate::level::KUniv;
use crate::mode::{Anon, Meta};
use crate::tc::TypeChecker;
use ix_common::address::Address;
use ix_common::env::{BinderInfo, DataValue, Name};

fn meta_name<M: KernelMode>(s: &str) -> M::MField<Name> {
  M::meta_field(Name::str(Name::anon(), s.to_owned()))
}

// A balanced tree has many distinct open nodes without deep recursion in
// construction, substitution, or destruction. Every leaf must be visited.
fn wide_open_tree<M: KernelMode>(
  intern: &mut InternTable<M>,
  leaves: u64,
) -> KExpr<M> {
  assert!(leaves.is_power_of_two());
  let mut layer: Vec<_> = (0..leaves)
    .map(|i| intern.intern_expr(KExpr::var(i, meta_name::<M>("v"))))
    .collect();
  while layer.len() > 1 {
    layer = layer
      .as_chunks::<2>()
      .0
      .iter()
      .map(|pair| intern.intern_app(&pair[0], &pair[1]))
      .collect();
  }
  layer.pop().unwrap()
}

fn large_then_small<M: KernelMode>() {
  let mut intern = InternTable::<M>::new();
  let body = wide_open_tree(&mut intern, 8_192);
  let fv = intern.intern_expr(KExpr::fvar(FVarId(0), meta_name::<M>("bulk")));
  let _ = instantiate_rev(&mut intern, &body, &[fv]);
  let high_water = intern.subst_scratch.capacity();
  assert!(high_water > 4_096);

  let var = intern.intern_expr(KExpr::var(0, meta_name::<M>("v")));
  for i in 1..=5 {
    let arg =
      intern.intern_expr(KExpr::fvar(FVarId(i), meta_name::<M>("small")));
    let result = subst(&mut intern, &var, &arg, 0);
    assert!(result.ptr_eq(&arg), "memo entries leaked between calls");
  }
  assert!(
    intern.subst_scratch.capacity() <= 4_096,
    "tiny substitutions retained the bulk table: high_water={high_water}, current={}",
    intern.subst_scratch.capacity()
  );
}

#[test]
fn scratch_releases_bulk_capacity_after_tiny_substitutions() {
  large_then_small::<Anon>();
  large_then_small::<Meta>();
}

fn lift_large_then_small<M: KernelMode>() {
  let mut intern = InternTable::<M>::new();
  let body = wide_open_tree(&mut intern, 8_192);
  let _ = lift(&mut intern, &body, 1, 0);
  assert!(intern.lift_scratch.capacity() > 4_096);
  let var = intern.intern_expr(KExpr::var(0, meta_name::<M>("v")));
  for shift in 1..=5 {
    let result = lift(&mut intern, &var, shift, 0);
    assert!(matches!(result.data(), ExprData::Var(i, ..) if *i == shift));
  }
  assert!(intern.lift_scratch.capacity() <= 4_096);
}

#[test]
fn scratch_lift_adapts_independently() {
  lift_large_then_small::<Anon>();
  lift_large_then_small::<Meta>();
}

// Small, shared expressions containing every binder/child position touched
// by substitution. Metadata is deliberately nonempty in Meta mode.
fn expressions<M: KernelMode>(intern: &mut InternTable<M>) -> Vec<KExpr<M>> {
  let mut nodes: Vec<_> = (0..4)
    .map(|i| intern.intern_expr(KExpr::var(i, meta_name::<M>("var"))))
    .collect();
  for i in 0..4 {
    nodes
      .push(intern.intern_expr(KExpr::fvar(FVarId(i), meta_name::<M>("free"))));
  }
  let metadata = M::meta_field(vec![vec![(
    Name::str(Name::anon(), "tag".to_owned()),
    DataValue::OfString("scratch differential".to_owned()),
  )]]);
  let ty =
    intern.intern_expr(KExpr::sort_mdata(KUniv::zero(), metadata.clone()));
  nodes.push(ty.clone());
  for i in 0..40 {
    let a = nodes[i % nodes.len()].clone();
    let b = nodes[(i * 7 + 3) % nodes.len()].clone();
    let node = match i % 5 {
      0 => KExpr::app_mdata(a.clone(), a, metadata.clone()),
      1 => KExpr::lam(
        meta_name::<M>("lambda"),
        M::meta_field(BinderInfo::Implicit),
        a,
        b,
      ),
      2 => KExpr::all(
        meta_name::<M>("forall"),
        M::meta_field(BinderInfo::InstImplicit),
        a,
        b,
      ),
      3 => KExpr::let_(meta_name::<M>("let"), ty.clone(), a, b, i % 2 == 0),
      _ => KExpr::prj(
        KId::new(Address::hash(b"scratch struct"), meta_name::<M>("S")),
        0,
        a,
      ),
    };
    nodes.push(intern.intern_expr(node));
  }
  nodes
}

fn differential<M: KernelMode>() {
  let mut intern = InternTable::<M>::new();
  let bulk = wide_open_tree(&mut intern, 8_192);
  let _ = lift(&mut intern, &bulk, 1, 0);
  let fv = intern.intern_expr(KExpr::fvar(FVarId(0), meta_name::<M>("free")));
  let _ = instantiate_rev(&mut intern, &bulk, &[fv]);
  let nodes = expressions(&mut intern);

  for round in 0..4u64 {
    let fvars: Vec<_> = (0..3)
      .map(|i| {
        intern.intern_expr(KExpr::fvar(
          FVarId((i + round) % 4),
          meta_name::<M>("free"),
        ))
      })
      .collect();
    // Open replacements force nested lift calls while subst owns its memo.
    let replacements =
      [nodes[usize::try_from(round).unwrap()].clone(), fvars[0].clone()];
    let ids: Vec<_> = (0..3).map(|i| FVarId((i + round) % 4)).collect();
    let pos: FxHashMap<_, _> = ids
      .iter()
      .rev()
      .enumerate()
      .map(|(i, id)| (*id, u64::try_from(i).unwrap()))
      .collect();
    for body in &nodes {
      for op in 0..5 {
        // Same trusted traversal with an independent, empty memo: no old
        // result, capacity, replacement list, binder depth, or shift can leak
        // from the adaptive cache into this reference result.
        let mut fresh = FxHashMap::default();
        let expected = match op {
          0 => {
            subst_cached(&mut intern, body, &replacements[0], round, &mut fresh)
          },
          1 => simul_subst_cached(
            &mut intern,
            body,
            &replacements,
            round,
            &mut fresh,
          ),
          2 => lift_cached(&mut intern, body, round + 1, round, &mut fresh),
          3 => instantiate_rev_cached(&mut intern, body, &fvars, 0, &mut fresh),
          _ => abstract_fvars_cached(&mut intern, body, &pos, 3, 0, &mut fresh),
        };
        let actual = match op {
          0 => subst(&mut intern, body, &replacements[0], round),
          1 => simul_subst(&mut intern, body, &replacements, round),
          2 => lift(&mut intern, body, round + 1, round),
          3 => instantiate_rev(&mut intern, body, &fvars),
          _ => abstract_fvars(&mut intern, body, &ids),
        };
        // Pointer equality in the SAME live interner also checks metadata
        // and annotations, unlike KExpr's structural PartialEq alone.
        assert!(actual.ptr_eq(&expected), "op={op} round={round}");
      }
    }
  }
  assert!(intern.subst_scratch.capacity() <= 4_096);
  assert!(intern.lift_scratch.capacity() <= 4_096);
}

#[test]
fn scratch_mixed_operations_match_fresh_memos() {
  differential::<Anon>();
  differential::<Meta>();
}

fn checked_application<M: KernelMode>(polluted: bool) -> u64 {
  let mut env = KEnv::<M>::new();
  if polluted {
    let bulk = wide_open_tree(&mut env.intern, 8_192);
    let _ = lift(&mut env.intern, &bulk, 1, 0);
    let fv =
      env.intern.intern_expr(KExpr::fvar(FVarId(100), meta_name::<M>("seed")));
    let _ = instantiate_rev(&mut env.intern, &bulk, &[fv]);
  }
  // (fun (A : Sort 1) => A) (Sort 0) is a closed, well-typed application.
  let sort0 = KExpr::sort(KUniv::zero());
  let sort1 = KExpr::sort(KUniv::succ(KUniv::zero()));
  let identity = KExpr::lam(
    meta_name::<M>("A"),
    M::meta_field(BinderInfo::Default),
    sort1.clone(),
    KExpr::var(0, meta_name::<M>("A")),
  );
  let app = KExpr::app(identity, sort0.clone());
  let mut tc = TypeChecker::new(&mut env);
  let ty = tc.infer(&app).unwrap();
  assert_eq!(ty, sort1);
  let reduced = tc.whnf(&app).unwrap();
  assert_eq!(reduced, sort0);
  tc.fuel_used()
}

#[test]
fn scratch_history_does_not_change_kernel_results_or_fuel() {
  assert_eq!(
    checked_application::<Anon>(false),
    checked_application::<Anon>(true)
  );
  assert_eq!(
    checked_application::<Meta>(false),
    checked_application::<Meta>(true)
  );
}

// Pre-adaptive take/clear/restore policy, kept only for a paired benchmark.
// The traversal, interner, operand shapes, and call-local memo keys are the
// same. All benchmark arguments are closed, so nested lift is a no-op.
fn legacy_subst(
  intern: &mut InternTable<Anon>,
  slot: &mut FxHashMap<(Addr, u64), KExpr<Anon>>,
  body: &KExpr<Anon>,
  arg: &KExpr<Anon>,
) -> KExpr<Anon> {
  // Match the disabled production diagnostic branch, without timing logs.
  assert!(!*IX_SUBST_COUNT_LOG);
  if body.lbr() == 0 {
    return body.clone();
  }
  let mut cache = std::mem::take(slot);
  cache.clear();
  let result = subst_cached(intern, body, arg, 0, &mut cache);
  *slot = cache;
  result
}

#[derive(Clone, Copy, Debug)]
enum Workload {
  Small,
  LargeThenSmall,
  Dense,
  Alternating,
}

fn scratch_sample(
  workload: Workload,
  adaptive: bool,
) -> (std::time::Duration, usize, usize) {
  use std::hint::black_box;
  use std::time::Instant;

  let mut intern = InternTable::<Anon>::new();
  let leaves = match workload {
    Workload::Small => 32,
    Workload::LargeThenSmall => 131_072,
    Workload::Dense | Workload::Alternating => 4_096,
  };
  let large = wide_open_tree(&mut intern, leaves);
  let small = intern.intern_expr(KExpr::var(0, ()));
  let arg = intern.intern_expr(KExpr::fvar(FVarId(0), ()));
  let mut legacy = FxHashMap::default();
  // Simulate the real preceding bulk binder-opening operation, outside the
  // timed loop. Both variants retain all of its canonical nodes identically.
  if adaptive {
    black_box(instantiate_rev(&mut intern, &large, std::slice::from_ref(&arg)));
  } else {
    black_box(instantiate_rev_cached(
      &mut intern,
      &large,
      std::slice::from_ref(&arg),
      0,
      &mut legacy,
    ));
  }
  let before =
    if adaptive { intern.subst_scratch.capacity() } else { legacy.capacity() };
  let iterations = match workload {
    Workload::Small => 200_000,
    Workload::LargeThenSmall => 5_000,
    Workload::Dense => 100,
    Workload::Alternating => 200,
  };
  let start = Instant::now();
  for i in 0..iterations {
    let body = match workload {
      Workload::Dense => &large,
      Workload::Alternating if i % 2 == 0 => &large,
      _ => &small,
    };
    let result = if adaptive {
      subst(&mut intern, black_box(body), black_box(&arg), 0)
    } else {
      legacy_subst(&mut intern, &mut legacy, black_box(body), black_box(&arg))
    };
    black_box(result);
  }
  let elapsed = start.elapsed();
  let after =
    if adaptive { intern.subst_scratch.capacity() } else { legacy.capacity() };
  if adaptive && matches!(workload, Workload::LargeThenSmall) {
    assert!(after <= 4_096);
  } else {
    assert_eq!(before, after, "unexpected capacity churn in {workload:?}");
  }
  (elapsed, before, after)
}

#[test]
#[ignore = "manual paired release microbenchmark; no wall-clock assertions"]
fn benchmark_adaptive_scratch() {
  for workload in [
    Workload::Small,
    Workload::LargeThenSmall,
    Workload::Dense,
    Workload::Alternating,
  ] {
    let mut samples = [Vec::new(), Vec::new()];
    let mut capacities = [(0, 0); 2];
    for round in 0..5 {
      // Alternate order to reduce warmup/thermal bias. Each sample has a
      // fresh interner and scratch; construction and teardown are excluded.
      for variant in [round % 2, 1 - round % 2] {
        let (elapsed, before, after) = scratch_sample(workload, variant == 1);
        samples[variant].push(elapsed);
        capacities[variant] = (before, after);
      }
    }
    let [old, new] = samples.map(|mut times| {
      times.sort_unstable();
      times[times.len() / 2].as_secs_f64() * 1_000.0
    });
    eprintln!(
      "{workload:?}: legacy={old:.3}ms adaptive={new:.3}ms ratio={:.3}; capacities legacy={:?} adaptive={:?}",
      new / old,
      capacities[0],
      capacities[1]
    );
  }
}
