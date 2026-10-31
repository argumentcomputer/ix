//! Phase-1 arithmetic past `u128`. The exact representation agrees with
//! the fast one, counters included, wherever the fast one succeeds, and
//! decides the inputs on which the fast one leaves its range: doubling DAGs
//! whose unshared costs exceed `2^127` while their sharing encodings are a
//! few hundred bytes. Lean computes these lengths with `Nat`; the byte
//! comparison with Lean is in the Lean/Rust sharing suite.

use super::*;
use crate::sharing_exact::uniform::{
  DagPrep, Exact, Fast, optimize_family_at_test, optimize_family_in_test,
};

/// `x_(i+1) = step(x_i)` from `x_0 = Var(0)`, `depth` times.
fn tower(depth: usize, step: impl Fn(E) -> E) -> E {
  (0..depth).fold(Expr::var(0), |x, _| step(x))
}

/// Fresh meters for one width, under the checked-mode limits.
fn phase1<A: uniform::Arith>(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
) -> Result<UniformSharingResult, SharingError> {
  let lim = limits();
  optimize_family_in_test::<A>(w, dag, prep, &mut Meter::new(&lim), 16)
    .map(|r| r.0)
}

#[test]
fn exact_arithmetic_matches_fast_where_fast_succeeds() {
  let mut rng = Rng(0x5EED_0B1C);
  let mut checked = 0;
  for seed in 0..240u64 {
    let roots = if seed % 2 == 0 {
      gen_search_roots(&mut rng)
    } else {
      constant_info_root_exprs(&gen_constant(seed, 2, 40, 5).info)
    };
    let Ok(dag) = SharingDag::from_expanded_roots(&roots, &limits()) else {
      continue;
    };
    let prep = DagPrep::new(&dag);
    for w in 1..=3 {
      let fast = phase1::<Fast>(w, &dag, &prep);
      let exact = phase1::<Exact>(w, &dag, &prep);
      assert_eq!(fast, exact, "seed {seed} w={w}");
      checked += usize::from(fast.is_ok());
    }
  }
  assert!(checked > 600, "{checked} successful comparisons");
}

#[test]
fn exact_arithmetic_decides_doubling_dags_past_u128() {
  let towers = [
    ("App(x, x) depth 127", tower(127, |x| Expr::app(x.clone(), x))),
    ("App(x, x) depth 130", tower(130, |x| Expr::app(x.clone(), x))),
    ("Lam(x, x) depth 130", tower(130, |x| Expr::lam(x.clone(), x))),
    ("All(x, x) depth 130", tower(130, |x| Expr::all(x.clone(), x))),
    (
      "two App towers depth 128",
      Expr::app(
        tower(128, |x| Expr::app(x.clone(), x)),
        tower(128, |x| Expr::app(x.clone(), Expr::app(Expr::var(1), x))),
      ),
    ),
  ];
  for (name, root) in towers {
    let c = axiom(root, 1);
    let dag = SharingDag::from_constant(&c, &limits()).unwrap();
    let prep = DagPrep::new(&dag);
    let mut refused = 0;
    for w in 1..=3 {
      let fast = phase1::<Fast>(w, &dag, &prep);
      let exact = phase1::<Exact>(w, &dag, &prep).unwrap();
      match fast {
        Ok(fast) => assert_eq!(fast, exact, "{name} w={w}"),
        Err(e) => {
          assert_eq!(
            e,
            SharingError::FormatBound(FormatBound::LengthOverflow),
            "{name} w={w}"
          );
          refused += 1;
        },
      }
      // The production entry retries from the meter it was given: its
      // result and counters are those of the exact run alone.
      let lim = limits();
      let mut meter = Meter::new(&lim);
      let (retried, _) =
        optimize_family_at_test(w, &dag, &prep, &mut meter, 16).unwrap();
      assert_eq!(retried, exact, "{name} w={w}");
      assert_eq!(meter.stats, exact.stats, "{name} w={w}");
      assert_eq!(exact.unshared_len, None, "{name} w={w}");
    }
    assert!(refused > 0, "{name}: the fast representation must overflow");
    // The whole construction succeeds, checked (`full_check`), and is
    // idempotent.
    let (out, _) =
      normalize_constant_sharing_tiered(ShareLayout::TagN, &c, &limits())
        .unwrap();
    let bytes = roundtrip(&out);
    let (again, _) =
      normalize_constant_sharing_tiered(ShareLayout::TagN, &out, &limits())
        .unwrap();
    assert_eq!(roundtrip(&again), bytes, "{name}: not a fixed point");
    eprintln!(
      "{name}: {} bytes, {} entries, fast refused at {refused} widths",
      bytes.len(),
      out.sharing.len()
    );
  }
}
