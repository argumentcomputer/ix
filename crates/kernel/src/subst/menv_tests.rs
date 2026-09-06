//! Persistent-environment regressions and an opt-in paired microbenchmark.

// Match the production closure API, including its worker-private Arc use;
// replacing these with Rc would change what the reference benchmark measures.
#![allow(clippy::arc_with_non_send_sync)]

use std::hint::black_box;
use std::mem::size_of;
use std::sync::Arc;
use std::time::{Duration, Instant};

use super::{Clo, MEnv, MEnvNode, clo_readback};
use crate::env::{InternTable, KEnv};
use crate::expr::KExpr;
use crate::level::KUniv;
use crate::mode::Anon;
use crate::tc::TypeChecker;

type Closure = Arc<Clo<Anon>>;

/// The original representation, retained only as a benchmark/reference.
#[derive(Clone)]
struct LinearEnv {
  node: Option<Arc<LinearNode>>,
  len: u64,
}

struct LinearNode {
  head: Closure,
  tail: LinearEnv,
}

trait TestEnv: Clone {
  fn empty() -> Self;
  fn push(&self, c: Closure) -> Self;
  fn get(&self, i: u64) -> &Closure;
}

impl TestEnv for LinearEnv {
  fn empty() -> Self {
    Self { node: None, len: 0 }
  }

  fn push(&self, c: Closure) -> Self {
    Self {
      node: Some(Arc::new(LinearNode { head: c, tail: self.clone() })),
      len: self.len + 1,
    }
  }

  fn get(&self, mut i: u64) -> &Closure {
    let mut node = self.node.as_ref().expect("linear lookup out of range");
    while i > 0 {
      node = node.tail.node.as_ref().expect("linear lookup out of range");
      i -= 1;
    }
    &node.head
  }
}

impl TestEnv for MEnv<Anon> {
  fn empty() -> Self {
    Self::empty()
  }

  fn push(&self, c: Closure) -> Self {
    self.push(c)
  }

  fn get(&self, i: u64) -> &Closure {
    self.get(i)
  }
}

fn closure(tag: u64) -> Closure {
  Arc::new(Clo::closed(KExpr::var(tag, ())))
}

#[test]
fn menv_lookup_preserves_every_snapshot() {
  let entries: Vec<_> = (0..256).map(closure).collect();
  let mut versions = vec![MEnv::empty()];
  for entry in &entries {
    let next = versions.last().unwrap().push(entry.clone());
    versions.push(next);
  }
  for (len, env) in versions.iter().enumerate() {
    assert_eq!(env.len(), u64::try_from(len).unwrap());
    for (i, expected) in entries[..len].iter().rev().enumerate() {
      assert!(Arc::ptr_eq(env.get(u64::try_from(i).unwrap()), expected));
    }
  }
  // Release newest first so even the linear reference has shallow drops.
  while versions.pop().is_some() {}
}

#[test]
fn menv_persistent_branches_match_vector_model() {
  let mut versions = vec![(MEnv::empty(), Vec::<Closure>::new())];
  let mut rng = 1u64;
  for tag in 0..2_000 {
    rng = rng.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
    let parent =
      usize::try_from(rng % u64::try_from(versions.len()).unwrap()).unwrap();
    let (env, entries) = &versions[parent];
    let value = closure(tag);
    let next = env.push(value.clone());
    let mut expected = entries.clone();
    expected.push(value);
    for (i, entry) in expected.iter().rev().enumerate() {
      assert!(Arc::ptr_eq(next.get(u64::try_from(i).unwrap()), entry));
    }
    versions.push((next, expected));
  }
  while versions.pop().is_some() {}
}

#[test]
fn menv_jump_spans_match_ordinary_ancestors() {
  let value = closure(0);
  let mut versions = build_versions::<MEnv<Anon>>(4_096, &value);
  for (len, env) in versions.iter().enumerate().skip(1) {
    let node = env.node.as_ref().unwrap();
    let span = usize::try_from(node.jump_len).unwrap();
    assert!((span + 1).is_power_of_two());
    assert!(span <= len);
    match (&node.jump, &versions[len - span].node) {
      (Some(actual), Some(expected)) => assert!(Arc::ptr_eq(actual, expected)),
      (None, None) => {},
      _ => panic!("jump must reach the same ancestor as its span"),
    }
    let mut block = node;
    let mut position = 0;
    while let Some(next) = &block.jump {
      assert!(block.jump_len <= next.jump_len);
      if block.jump_len == next.jump_len {
        assert_eq!(position, 0, "only the first two blocks may be equal");
      }
      block = next;
      position += 1;
    }
  }
  while versions.pop().is_some() {}
}

#[test]
fn menv_deep_lookups_match_linear_model_with_logarithmic_hops() {
  let entries: Vec<_> = (0..16_385).map(closure).collect();
  let mut versions = vec![MEnv::empty()];
  for value in &entries {
    versions.push(versions.last().unwrap().push(value.clone()));
  }
  for len in [63usize, 64, 65, 1_023, 1_024, 1_025, 16_383, 16_384, 16_385] {
    let env = &versions[len];
    for (index, expected) in entries[..len].iter().rev().enumerate() {
      let index = u64::try_from(index).unwrap();
      assert!(Arc::ptr_eq(env.get(index), expected));
      // Check the structural work bound without adding instrumentation
      // to the production lookup hot path.
      let mut node = env.node.as_ref().unwrap();
      let mut remaining = index;
      let mut hops = 0;
      while remaining >= 8 {
        if node.jump_len <= remaining {
          remaining -= node.jump_len;
          node = node.jump.as_ref().unwrap();
        } else {
          remaining -= 1;
          node = node.tail.as_ref().unwrap();
        }
        hops += 1;
      }
      while remaining > 0 {
        remaining -= 1;
        node = node.tail.as_ref().unwrap();
        hops += 1;
      }
      assert!(Arc::ptr_eq(&node.head, expected));
      assert!(hops <= 2 * (env.len().ilog2() + 1));
    }
  }
  while versions.pop().is_some() {}
}

#[test]
fn menv_readback_preserves_captured_environments_and_lifting() {
  let mut env = MEnv::empty().push(closure(3));
  let mut versions = vec![env.clone()];
  for _ in 0..127 {
    // Each new entry denotes the previous entry in its captured snapshot,
    // not Var(0) in the eventual caller's environment.
    env = env.push(Arc::new(Clo::new(KExpr::var(0, ()), env.clone())));
    versions.push(env.clone());
  }
  let ty = KExpr::sort(KUniv::zero());
  let body = KExpr::lam(
    (),
    (),
    ty.clone(),
    KExpr::app(
      KExpr::var(1, ()),
      KExpr::app(KExpr::var(env.len(), ()), KExpr::var(env.len() + 5, ())),
    ),
  );
  let c = Clo::new(body, env);
  let expected = KExpr::lam(
    (),
    (),
    ty,
    KExpr::app(
      KExpr::var(4, ()),
      KExpr::app(KExpr::var(4, ()), KExpr::var(5, ())),
    ),
  );
  let mut intern = InternTable::new();
  let result = clo_readback(&mut intern, &c);
  assert_eq!(result, expected);
  assert!(result.ptr_eq(&clo_readback(&mut intern, &c)));
  drop(c);
  while versions.pop().is_some() {}
}

#[test]
fn menv_deep_beta_machine_selects_original_arguments() {
  for depth in [7u64, 8, 15, 63, 64, 65, 127, 128, 129] {
    for selected in [0, depth / 2, depth - 1] {
      let mut env = KEnv::<Anon>::new();
      let ty = KExpr::sort(KUniv::zero());
      // Open arguments let us distinguish every position and also verify
      // that ambient variables are not captured by the machine binders.
      let args: Vec<_> = (0..depth).map(|i| KExpr::var(i + 10, ())).collect();
      let mut expr = KExpr::var(depth - 1 - selected, ());
      for _ in 0..depth {
        expr = KExpr::lam((), (), ty.clone(), expr);
      }
      for arg in &args {
        expr = KExpr::app(expr, arg.clone());
      }
      let mut tc = TypeChecker::new(&mut env);
      let result = tc.whnf(&expr).unwrap();
      assert_eq!(result, args[usize::try_from(selected).unwrap()]);
    }
  }
}

#[test]
#[should_panic(expected = "MEnv::get out of range")]
fn menv_empty_lookup_panics() {
  let _ = MEnv::<Anon>::empty().get(0);
}

#[test]
#[should_panic(expected = "MEnv::get out of range")]
fn menv_len_lookup_panics() {
  let env = MEnv::empty().push(closure(0));
  let _ = env.get(env.len());
}

#[test]
#[should_panic(expected = "MEnv::get out of range")]
fn menv_large_out_of_range_lookup_panics() {
  let env = MEnv::empty().push(closure(0));
  let _ = env.get(u64::MAX);
}

fn build_versions<E: TestEnv>(depth: u64, value: &Closure) -> Vec<E> {
  let mut versions = Vec::with_capacity(usize::try_from(depth + 1).unwrap());
  versions.push(E::empty());
  for _ in 0..depth {
    let next = versions.last().unwrap().push(value.clone());
    versions.push(next);
  }
  versions
}

fn measure_lookup<E: TestEnv>(env: &E, indices: &[u64], count: u64) -> f64 {
  let start = Instant::now();
  let mut indices = indices.iter().cycle();
  for _ in 0..count {
    black_box(black_box(env).get(black_box(*indices.next().unwrap())));
  }
  start.elapsed().as_secs_f64() * 1e9 / f64::from(u32::try_from(count).unwrap())
}

fn median(mut samples: Vec<f64>) -> f64 {
  samples.sort_by(f64::total_cmp);
  samples[samples.len() / 2]
}

fn build_sample<E: TestEnv>(
  depth: u64,
  value: &Closure,
) -> (Duration, Duration) {
  let start = Instant::now();
  let mut versions = black_box(build_versions::<E>(depth, value));
  let build = start.elapsed();
  let start = Instant::now();
  while versions.pop().is_some() {}
  (build, start.elapsed())
}

/// No timing assertions: performance results depend on host load/allocator.
/// Construction includes retaining each version; destruction releases newest
/// first. Closure allocation is excluded, to isolate the environment itself.
#[test]
#[ignore = "release microbenchmark: --release menv_lookup_benchmark -- --ignored --nocapture"]
fn menv_lookup_benchmark() {
  eprintln!(
    "MEnv node payload={} B; linear={} B; handle={} B; one node allocation/push (excludes Arc header/allocator rounding)",
    size_of::<MEnvNode<Anon>>(),
    size_of::<LinearNode>(),
    size_of::<MEnv<Anon>>(),
  );
  let value = closure(0);
  for depth in [8u64, 64, 1_024, 16_384] {
    let mut current = build_versions::<MEnv<Anon>>(depth, &value);
    let mut linear = build_versions::<LinearEnv>(depth, &value);
    let uniform: Vec<_> = (0..256u64)
      .map(|i| i.wrapping_mul(6_364_136_223_846_793_005) % depth)
      .collect();
    for (pattern, indices) in [
      ("front", vec![0]),
      ("near", (0..8).collect()),
      ("oldest", vec![depth - 1]),
      ("uniform", uniform),
    ] {
      let count = if pattern == "front" || pattern == "near" {
        500_000
      } else {
        (4_000_000 / depth).clamp(4_096, 500_000)
      };
      let mut current_samples = Vec::new();
      let mut linear_samples = Vec::new();
      for round in 0..7 {
        if round % 2 == 0 {
          current_samples.push(measure_lookup(
            current.last().unwrap(),
            &indices,
            count,
          ));
          linear_samples.push(measure_lookup(
            linear.last().unwrap(),
            &indices,
            count,
          ));
        } else {
          linear_samples.push(measure_lookup(
            linear.last().unwrap(),
            &indices,
            count,
          ));
          current_samples.push(measure_lookup(
            current.last().unwrap(),
            &indices,
            count,
          ));
        }
      }
      let current_ns = median(current_samples);
      let linear_ns = median(linear_samples);
      eprintln!(
        "depth={depth:5} {pattern:7}: current={current_ns:10.2} ns/lookup linear={linear_ns:10.2} ns/lookup ratio={:.3}",
        current_ns / linear_ns
      );
    }
    while current.pop().is_some() {}
    while linear.pop().is_some() {}
  }
  for depth in [1_024u32, 16_384] {
    let mut build = [Vec::new(), Vec::new()];
    let mut drop = [Vec::new(), Vec::new()];
    for round in 0..7 {
      for index in [round % 2, 1 - round % 2] {
        let (built, dropped) = if index == 0 {
          build_sample::<MEnv<Anon>>(u64::from(depth), &value)
        } else {
          build_sample::<LinearEnv>(u64::from(depth), &value)
        };
        build[index].push(built.as_secs_f64() * 1e9 / f64::from(depth));
        drop[index].push(dropped.as_secs_f64() * 1e9 / f64::from(depth));
      }
    }
    let [current_build, linear_build] = build.map(median);
    let [current_drop, linear_drop] = drop.map(median);
    eprintln!(
      "depth={depth:5} build: current={current_build:.2} linear={linear_build:.2} ns/binding; drop: current={current_drop:.2} linear={linear_drop:.2} ns/binding"
    );
  }
}
