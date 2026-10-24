//! Independent product-family controls. The oracle evaluates full-DAG
//! uniform lengths and orders boolean membership vectors; it does not use
//! production component deltas, family_table, trim, knapsack or set_prec.

use super::*;
use crate::sharing_exact::uniform::{DagPrep, optimize_family_at_test};

fn run(w: u64, dag: &SharingDag, k: usize) -> UniformSharingResult {
  let lim = limits();
  let (mut out, plan) = optimize_family_at_test(
    w,
    dag,
    &DagPrep::new(dag),
    &mut Meter::new(&lim),
    k,
  )
  .unwrap();
  let built = plan.build(dag, &out.table_terms, &lim).unwrap();
  out.roots = built.roots;
  out.sharing = built.entries;
  out.variable_len = built.measured;
  out
}

fn flags(n: usize, set: &[u32]) -> Vec<bool> {
  (0..n as u32).map(|t| set.contains(&t)).collect()
}

fn merged(a: &[u32], b: &[u32]) -> Vec<u32> {
  let mut out = [a, b].concat();
  out.sort_unstable();
  out
}

fn body(dag: &SharingDag, w: u64, set: &[u32]) -> i128 {
  i128::from(uniform_set_len(dag, w, set))
    - i128::from(tag0_len(set.len() as u64))
}

fn oracle_family(
  dag: &SharingDag,
  w: u64,
  cs: &[u32],
  members: &[u32],
  k: usize,
) -> Vec<Vec<u32>> {
  if members.len() <= k {
    assert!(members.len() <= 12);
    return (0..1u64 << members.len())
      .map(|mask| {
        members
          .iter()
          .enumerate()
          .filter_map(|(j, &t)| (mask >> j & 1 != 0).then_some(t))
          .collect()
      })
      .collect();
  }
  let mut chain: Vec<Vec<u32>> = vec![Vec::new()];
  for q in 1..=members.len() {
    let previous = chain.last().unwrap();
    let extensions: Vec<_> = members
      .iter()
      .filter(|&&t| !previous.contains(&t))
      .map(|t| merged(previous, &[*t]))
      .collect();
    let next = extensions
      .iter()
      .filter(|s| s.len() == q && previous.iter().all(|t| s.contains(t)))
      .min_by_key(|s| (body(dag, w, &merged(cs, s)), flags(dag.len(), s)))
      .unwrap();
    chain.push(next.clone());
  }
  chain
}

/// Exhaust the actual succinct product on small cases, evaluating every
/// complete set with the full dictionary oracle, including the count header.
fn check_product(
  dag: &SharingDag,
  w: u64,
  k: usize,
  actual: &UniformSharingResult,
) -> (usize, usize) {
  let cs = &actual.certain_stored;
  let mut product = vec![cs.clone()];
  let mut negative = 0;
  let mut tied = 0;
  let slack = i128::from(
    tag0_len((cs.len() + actual.uncertain.len()) as u64)
      - tag0_len(cs.len() as u64),
  );
  for (members, retained) in
    actual.components.iter().zip(&actual.component_tables)
  {
    let family = oracle_family(dag, w, cs, members, k);
    // Independent complete per-count rows, then the declared slack rule.
    let mut rows = Vec::new();
    for q in 0..=members.len() {
      let selected = family
        .iter()
        .filter(|s| s.len() == q)
        .min_by_key(|s| (body(dag, w, &merged(cs, s)), flags(dag.len(), s)))
        .unwrap();
      let delta = body(dag, w, &merged(cs, selected)) - body(dag, w, cs);
      negative += usize::from(delta < 0);
      tied += usize::from(
        family
          .iter()
          .filter(|s| {
            s.len() == q
              && body(dag, w, &merged(cs, s)) - body(dag, w, cs) == delta
          })
          .count()
          > 1,
      );
      rows.push((delta, selected.clone()));
    }
    let best = rows.iter().map(|r| r.0).min().unwrap();
    let expected: Vec<_> =
      rows.into_iter().map(|r| (r.0 <= best + slack).then_some(r)).collect();
    assert_eq!(retained, &expected, "retained per-count rows w={w} k={k}");
    product = product
      .iter()
      .flat_map(|p| family.iter().map(|s| merged(p, s)))
      .collect();
  }
  let chosen = product
    .iter()
    .min_by_key(|s| (uniform_set_len(dag, w, s), flags(dag.len(), s)))
    .unwrap();
  tied += usize::from(
    product
      .iter()
      .filter(|s| uniform_set_len(dag, w, s) == uniform_set_len(dag, w, chosen))
      .count()
      > 1,
  );
  assert_eq!(
    (&actual.stored, actual.model_len),
    (chosen, uniform_set_len(dag, w, chosen)),
    "complete family product w={w} k={k}"
  );
  (negative, tied)
}

#[test]
fn mixed_products_match_full_dictionary_oracle() {
  let mut rng = Rng(9137);
  let (mut checked, mut mixed, mut negative, mut tied, mut bracket, mut lower) =
    (0, 0, 0, 0, 0, 0);
  for attempt in 0..4000 {
    let mut roots = gen_search_roots(&mut rng);
    let w = [1, 2, 3, 5][rng.below(4) as usize];
    if attempt % 2 == 0 {
      // Large guaranteed-positive atoms supply a fixed CS prefix close to
      // the 128-entry count boundary without enlarging the product family.
      for j in 0..(120 + rng.below(8)) {
        let atom = Expr::reference(10_000 + j, vec![0; 5]);
        roots.extend([atom.clone(), atom.clone(), atom]);
      }
    }
    // One independent uncertain singleton guarantees an exact factor at k=1.
    let atom = Expr::reference(113, vec![0; (2 * w - 2) as usize]);
    roots.extend([atom.clone(), atom]);
    let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
    let k = if attempt % 3 == 0 { 2 } else { 1 };
    let actual = run(w, &dag, k);
    if actual.uncertain.len() > 10 || actual.components.is_empty() {
      continue;
    }
    let is_mixed = actual.components.iter().any(|c| c.len() <= k)
      && actual.components.iter().any(|c| c.len() > k);
    if !is_mixed {
      continue;
    }
    let (n, t) = check_product(&dag, w, k, &actual);
    negative += n;
    tied += t;
    mixed += 1;
    bracket += usize::from(
      tag0_len(actual.certain_stored.len() as u64)
        != tag0_len(
          (actual.certain_stored.len() + actual.uncertain.len()) as u64,
        ),
    );
    lower += usize::from(actual.lower_bracket);
    checked += 1;
    if checked >= 120 {
      break;
    }
  }
  eprintln!(
    "mixed product oracle: checked={checked} mixed={mixed} negative_rows={negative} tied_choices={tied} header_crossings={bracket} lower_bracket_winners={lower}"
  );
  assert_eq!(checked, 120);
  assert!(
    mixed >= 20 && negative > 0 && tied > 0 && bracket >= 20 && lower > 0
  );
}

#[test]
fn actual_k16_mixed_product_matches_full_dictionary_oracle() {
  let mut checked = 0;
  for n in [17, 18, 24, 32] {
    for w in [3, 5] {
      let mut roots = Vec::new();
      let mut prefix = Expr::var(0);
      for j in 0..n {
        prefix = Expr::app(prefix, Expr::var(j % 5));
        roots.push(Expr::app(prefix.clone(), Expr::sort(1)));
      }
      roots.push(prefix);
      let atom = Expr::reference(113, vec![0; (2 * w - 2) as usize]);
      roots.extend([atom.clone(), atom]);
      let dag = SharingDag::from_expanded_roots(&roots, &limits()).unwrap();
      let out = run(w, &dag, 16);
      let sizes: Vec<_> = out.components.iter().map(Vec::len).collect();
      eprintln!("K16 mixed n={n} w={w}: components={sizes:?}");
      if !sizes.iter().any(|&m| m > 16) || !sizes.iter().any(|&m| m <= 16) {
        continue;
      }
      let families: usize = sizes
        .iter()
        .map(|&m| if m <= 16 { 1usize << m } else { m + 1 })
        .product();
      assert!(families <= 4096 && sizes.iter().all(|&m| m > 16 || m <= 12));
      check_product(&dag, w, 16, &out);
      checked += 1;
    }
  }
  assert!(checked > 0, "fixture must cross the actual K16 gate");
  eprintln!("actual K16 mixed product oracle: {checked} complete products");
}

/// The historical fixed-seed 400 + 600 cases now also exercise the actual
/// production family entry. Stats intentionally differ under R3 precharges.
pub(super) fn compare_production(
  w: u64,
  roots: &[E],
  old: &UniformSharingResult,
) {
  let dag = SharingDag::from_expanded_roots(roots, &limits()).unwrap();
  let actual = run(w, &dag, 16);
  assert_eq!(actual.components, old.components);
  assert_eq!(actual.certain_stored, old.certain_stored);
  let fallback = actual.components.iter().any(|c| c.len() > 16);
  let semantic = |r: &UniformSharingResult| {
    (
      r.stored.clone(),
      r.model_len,
      r.variable_len,
      r.table_terms.clone(),
      r.sharing.iter().map(|e| bytes_of(e)).collect::<Vec<_>>(),
      r.roots.iter().map(|e| bytes_of(e)).collect::<Vec<_>>(),
    )
  };
  let equal = semantic(&actual) == semantic(old);
  assert!(equal || fallback, "all-exact production bytes/model/set differ");
  let old_rows = retained_component_counts(old);
  let new_rows = retained_component_counts(&actual);
  for (j, c) in actual.components.iter().enumerate() {
    if c.len() <= 16 {
      assert_eq!(old_rows[j], new_rows[j]);
    }
  }
  eprintln!(
    "K16 G2 width={w} fallback={fallback} equal={equal} old_states={} new_states={} old_work={} new_work={}",
    old.stats.states_created,
    actual.stats.states_created,
    old.stats.work,
    actual.stats.work
  );
}
