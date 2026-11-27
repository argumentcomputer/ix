//! Booleanity of every send and memory enable of an exported Aiur artifact.
//!
//! In the circuit model the compiler theorems are stated over, a send or a
//! memory lookup is a premise exactly when its enable evaluates to 1; in the
//! lowered AIR the enable is the lookup's LogUp multiplicity
//! (`trace/stark/grouping.rs`, `rom.rs`). The two agree only if every enable
//! is 0 or 1 on every row that satisfies the chip's constraints: an enable of
//! -1 would provide the message it should demand. No theorem states this for
//! the final chips, so this check decides it for an artifact, and CI runs it on
//! the exported IxVM, recursion and aggregation artifacts. It exits non-zero
//! unless every enable is proved boolean.
//!
//! Every chip is lowered as its own circuit (groups cleared): the Lean packet
//! certificate makes a group slot's enable the selected member's enable and 0
//! on padding. In a chip circuit exactly one lookup is the chip's receive, the
//! pull of its multiplicity column (the last main column); every other lookup
//! is a send or memory push whose multiplicity is an enable, and is checked,
//! a negated enable included.
//!
//! Sound, incomplete static check:
//!  * a column is boolean if a constraint whose only column it is forces it
//!    into {0, 1} (degree at most 3 in it, by finite differences at 0..3);
//!  * pairwise exclusions are read off constraints `(k·Σ_A + c)(k'·Σ_B + c')`
//!    over boolean columns, whose integer sums stay below p;
//!  * forced zeros: a constraint `(k·Σ_A + c)(k'·Σ_A + c')` over boolean
//!    columns whose only root in the integer range `[0, |A|]` of `Σ_A` is 0
//!    (for example `S·(S + 1)`) sets every column of A to 0;
//!  * an enable is proved boolean when, after closing its support under the
//!    boolean-only constraints touching it (at most `CAP` columns), every
//!    assignment in {0, 1} satisfying the constraints within that set (and the
//!    exclusions and forced zeros) gives the enable the value 0 or 1.
//!
//! Usage: `check_enables [--self-test] ARTIFACT.ixa...`
use aiur::{
  artifact::Package,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::{
  expr::{RowOffset, Source},
  graph::{ConstraintGraph, Node},
  p3_field::{Field, PrimeCharacteristicRing, PrimeField64},
  types::Val,
};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

const CAP: usize = 18;
const BUDGET: u64 = 1 << 22;

type Affine = (BTreeMap<u32, Val>, Val);

fn supports(g: &ConstraintGraph<Val>) -> Vec<Option<Vec<u32>>> {
  let mut out: Vec<Option<Vec<u32>>> = Vec::with_capacity(g.nodes.len());
  for n in &g.nodes {
    let s = match n {
      Node::Const(_) => Some(vec![]),
      Node::Var(c)
        if c.source == Source::Main && c.offset == RowOffset::Current =>
      {
        Some(vec![c.index])
      },
      Node::Var(_)
      | Node::Public(_)
      | Node::IsFirstRow
      | Node::IsLastRow
      | Node::IsTransition => None,
      Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
        match (&out[a.0 as usize], &out[b.0 as usize]) {
          (Some(x), Some(y)) => {
            let mut v: Vec<u32> = x.iter().chain(y).copied().collect();
            v.sort_unstable();
            v.dedup();
            Some(v)
          },
          _ => None,
        }
      },
      Node::Neg(a) => out[a.0 as usize].clone(),
    };
    out.push(s);
  }
  out
}

fn eval(
  g: &ConstraintGraph<Val>,
  id: usize,
  col: &dyn Fn(u32) -> Val,
  memo: &mut HashMap<usize, Val>,
) -> Val {
  if let Some(v) = memo.get(&id) {
    return *v;
  }
  let v = match &g.nodes[id] {
    Node::Const(c) => *c,
    Node::Var(c) => col(c.index),
    Node::Add(x, y) => {
      eval(g, x.0 as usize, col, memo) + eval(g, y.0 as usize, col, memo)
    },
    Node::Sub(x, y) => {
      eval(g, x.0 as usize, col, memo) - eval(g, y.0 as usize, col, memo)
    },
    Node::Mul(x, y) => {
      eval(g, x.0 as usize, col, memo) * eval(g, y.0 as usize, col, memo)
    },
    Node::Neg(x) => -eval(g, x.0 as usize, col, memo),
    _ => unreachable!("evaluated only on local nodes"),
  };
  memo.insert(id, v);
  v
}

/// Whether a polynomial of degree at most 3 in one variable, given by its
/// values at 0..3, vanishes only on {0, 1} (and somewhere there).
fn forces_bool(q: [Val; 4]) -> bool {
  let d1 = [q[1] - q[0], q[2] - q[1], q[3] - q[2]];
  let d2 = [d1[1] - d1[0], d1[2] - d1[1]];
  if d2[1] - d2[0] != Val::ZERO {
    return false;
  }
  if d2[0] != Val::ZERO {
    return q[0] == Val::ZERO && q[1] == Val::ZERO;
  }
  if d1[0] != Val::ZERO {
    return q[0] == Val::ZERO || q[1] == Val::ZERO;
  }
  q[0] != Val::ZERO
}

/// The affine form of a node over main columns, if it is affine.
fn affine(
  g: &ConstraintGraph<Val>,
  id: usize,
  memo: &mut HashMap<usize, Option<Affine>>,
) -> Option<Affine> {
  if let Some(v) = memo.get(&id) {
    return v.clone();
  }
  let add = |a: Affine, b: Affine, sign: Val| {
    let mut m = a.0;
    for (k, v) in b.0 {
      let e = m.entry(k).or_insert(Val::ZERO);
      *e += sign * v;
    }
    m.retain(|_, v| *v != Val::ZERO);
    (m, a.1 + sign * b.1)
  };
  let r = match &g.nodes[id] {
    Node::Const(c) => Some((BTreeMap::new(), *c)),
    Node::Var(c)
      if c.source == Source::Main && c.offset == RowOffset::Current =>
    {
      Some(([(c.index, Val::ONE)].into(), Val::ZERO))
    },
    Node::Add(a, b) => {
      let (x, y) =
        (affine(g, a.0 as usize, memo), affine(g, b.0 as usize, memo));
      x.zip(y).map(|(x, y)| add(x, y, Val::ONE))
    },
    Node::Sub(a, b) => {
      let (x, y) =
        (affine(g, a.0 as usize, memo), affine(g, b.0 as usize, memo));
      x.zip(y).map(|(x, y)| add(x, y, -Val::ONE))
    },
    Node::Neg(a) => affine(g, a.0 as usize, memo)
      .map(|(m, c)| (m.into_iter().map(|(k, v)| (k, -v)).collect(), -c)),
    Node::Mul(a, b) => {
      let (x, y) =
        (affine(g, a.0 as usize, memo), affine(g, b.0 as usize, memo));
      match (x, y) {
        (Some((mx, cx)), Some((my, cy))) if mx.is_empty() => {
          Some((my.into_iter().map(|(k, v)| (k, v * cx)).collect(), cx * cy))
        },
        (Some((mx, cx)), Some((my, cy))) if my.is_empty() => {
          Some((mx.into_iter().map(|(k, v)| (k, v * cy)).collect(), cx * cy))
        },
        _ => None,
      }
    },
    _ => None,
  };
  memo.insert(id, r.clone());
  r
}

/// For an affine form `k·Σ_A x + c` with one common coefficient `k` over a
/// non-empty A: (A, the canonical field value of `Σ_A x` at which it vanishes).
fn uniform(form: &Affine) -> Option<(BTreeSet<u32>, u64)> {
  let k = *form.0.values().next()?;
  if form.0.values().any(|v| *v != k) {
    return None;
  }
  let root = (-form.1) * k.inverse();
  Some((form.0.keys().copied().collect(), root.as_canonical_u64()))
}

/// The two uniform factors of a product constraint over boolean columns.
fn factors(
  g: &ConstraintGraph<Val>,
  z: usize,
  boolean: &BTreeSet<u32>,
  memo: &mut HashMap<usize, Option<Affine>>,
) -> Option<((BTreeSet<u32>, u64), (BTreeSet<u32>, u64))> {
  let Node::Mul(a, b) = g.nodes[z] else { return None };
  let fa = uniform(&affine(g, a.0 as usize, memo)?)?;
  let fb = uniform(&affine(g, b.0 as usize, memo)?)?;
  fa.0.iter().chain(&fb.0).all(|v| boolean.contains(v)).then_some((fa, fb))
}

/// Pairs of boolean columns no satisfying row sets to 1 together, read off
/// constraints `(k·Σ_A + c)(k'·Σ_B + c')`: `Σ_A ∈ {0, 1}` (same A, roots 0 and
/// 1), `Σ_A = 0 ∨ Σ_B = 0` (roots 0 and 0), or `Σ_A = 0 ∨ Σ_B = 1` with
/// `A ⊆ B`. Integer sums of booleans stay below p, so these are exact.
fn exclusions(
  g: &ConstraintGraph<Val>,
  zeros: &[usize],
  boolean: &BTreeSet<u32>,
) -> HashSet<(u32, u32)> {
  let mut out = HashSet::new();
  let mut memo = HashMap::new();
  for &z in zeros {
    let Some(((sa, ra), (sb, rb))) = factors(g, z, boolean, &mut memo) else {
      continue;
    };
    if ra > 1 || rb > 1 {
      continue;
    }
    if sa == sb && ra != rb {
      for &x in &sa {
        for &y in &sa {
          if x != y {
            out.insert((x, y));
          }
        }
      }
    } else if ra == 0 && rb == 0 && sa.is_disjoint(&sb) {
      for &x in &sa {
        for &y in &sb {
          out.insert((x, y));
          out.insert((y, x));
        }
      }
    } else {
      for (small, rs, big, rbig) in [(&sa, ra, &sb, rb), (&sb, rb, &sa, ra)] {
        if rs == 0 && rbig == 1 && small.is_subset(big) {
          for &x in small {
            for &y in big {
              if x != y {
                out.insert((x, y));
                out.insert((y, x));
              }
            }
          }
        }
      }
    }
  }
  out
}

/// Boolean columns every satisfying row sets to 0: the columns of A for a
/// constraint `(k·Σ_A + c)(k'·Σ_A + c')` over boolean columns whose roots in
/// the integer range `[0, |A|]` of `Σ_A` (below p) are 0 only.
fn forced_zeros(
  g: &ConstraintGraph<Val>,
  zeros: &[usize],
  boolean: &BTreeSet<u32>,
) -> BTreeSet<u32> {
  let mut out = BTreeSet::new();
  let mut memo = HashMap::new();
  for &z in zeros {
    let Some(((sa, ra), (sb, rb))) = factors(g, z, boolean, &mut memo) else {
      continue;
    };
    let n = sa.len() as u64;
    let reachable: Vec<u64> =
      [ra, rb].into_iter().filter(|r| *r <= n).collect();
    if sa == sb && !reachable.is_empty() && reachable.iter().all(|r| *r == 0) {
      out.extend(sa);
    }
  }
  out
}

struct Search<'g> {
  g: &'g ConstraintGraph<Val>,
  at: Vec<Vec<usize>>,
  cols: Vec<u32>,
  idx: HashMap<u32, usize>,
  excl: &'g HashSet<(u32, u32)>,
  forced: &'g BTreeSet<u32>,
  e: usize,
  budget: std::cell::Cell<u64>,
}

enum Outcome {
  Budget,
  Counter(Vec<u8>, Val),
}

impl Search<'_> {
  fn val(&self, node: usize, assign: &[u8]) -> Val {
    let col = |c: u32| Val::from_u64(u64::from(assign[self.idx[&c]]));
    eval(self.g, node, &col, &mut HashMap::new())
  }

  /// A counterexample (or an exhausted budget) below `depth`, if any.
  fn dfs(&self, depth: usize, assign: &mut Vec<u8>) -> Option<Outcome> {
    if self.budget.get() == 0 {
      return Some(Outcome::Budget);
    }
    self.budget.set(self.budget.get() - 1);
    if self.at[depth].iter().any(|&z| self.val(z, assign) != Val::ZERO) {
      return None;
    }
    if depth == self.cols.len() {
      let x = self.val(self.e, assign);
      return (x != Val::ZERO && x != Val::ONE)
        .then(|| Outcome::Counter(assign.clone(), x));
    }
    assign[depth] = 0;
    if let Some(o) = self.dfs(depth + 1, assign) {
      return Some(o);
    }
    let c = self.cols[depth];
    let clash = self.forced.contains(&c)
      || (0..depth)
        .any(|k| assign[k] == 1 && self.excl.contains(&(self.cols[k], c)));
    let r = if clash {
      None
    } else {
      assign[depth] = 1;
      self.dfs(depth + 1, assign)
    };
    assign[depth] = 0;
    r
  }
}

/// Whether lookup multiplicity `node` is the chip's receive: the pull of its
/// multiplicity column, the last main column (`-x_{main_width - 1}`).
fn is_receive(
  g: &ConstraintGraph<Val>,
  node: usize,
  main_width: usize,
) -> bool {
  let Node::Neg(x) = g.nodes[node] else { return false };
  matches!(&g.nodes[x.0 as usize], Node::Var(c)
    if c.source == Source::Main
      && c.offset == RowOffset::Current
      && c.index as usize + 1 == main_width)
}

/// The verdict on every push (send or memory) enable of one chip circuit:
/// `Ok(n)` with the number of enables proved boolean, or the failures.
fn check_circuit(
  g: &ConstraintGraph<Val>,
  main_width: usize,
  name: &str,
) -> Result<usize, Vec<String>> {
  let sup = supports(g);
  let zeros: Vec<usize> = g.zeros.iter().map(|z| z.0 as usize).collect();
  let mut boolean = BTreeSet::new();
  for &z in &zeros {
    if let Some(s) = &sup[z]
      && s.len() == 1
      && g.degrees[z] <= 3
    {
      let q = [0u64, 1, 2, 3].map(|x| {
        let col = |_: u32| Val::from_u64(x);
        eval(g, z, &col, &mut HashMap::new())
      });
      if q != [Val::ZERO; 4] && forces_bool(q) {
        boolean.insert(s[0]);
      }
    }
  }
  let bool_zeros: Vec<(usize, BTreeSet<u32>)> = zeros
    .iter()
    .filter_map(|&z| {
      let s = sup[z].as_ref()?;
      (!s.is_empty() && s.iter().all(|v| boolean.contains(v)))
        .then(|| (z, s.iter().copied().collect()))
    })
    .collect();
  let excl = exclusions(g, &zeros, &boolean);
  let forced = forced_zeros(g, &zeros, &boolean);
  let mut failures = vec![];
  let mut proven = 0usize;
  let receives = g
    .lookups
    .iter()
    .filter(|l| is_receive(g, l.multiplicity.0 as usize, main_width))
    .count();
  if receives != 1 {
    return Err(vec![format!(
      "{name}: {receives} lookups pull the multiplicity column, not one"
    )]);
  }
  for (li, l) in g.lookups.iter().enumerate() {
    let mi = l.multiplicity.0 as usize;
    if is_receive(g, mi, main_width) {
      continue;
    }
    let fail = |why: String| format!("{name}: enable of lookup {li}: {why}");
    let s0 = match &sup[mi] {
      None => {
        failures.push(fail("reads more than the current row".into()));
        continue;
      },
      Some(s0) => s0,
    };
    if let Some(v) = s0.iter().find(|v| !boolean.contains(v)) {
      failures.push(fail(format!("column x{v} is not proved boolean")));
      continue;
    }
    let mut s: BTreeSet<u32> = s0.iter().copied().collect();
    loop {
      let mut grew = false;
      let mut cands: Vec<&BTreeSet<u32>> = bool_zeros
        .iter()
        .map(|(_, zs)| zs)
        .filter(|zs| zs.iter().any(|v| s.contains(v)) && !zs.is_subset(&s))
        .collect();
      cands.sort_by_key(|zs| zs.len());
      for zs in cands {
        let union: BTreeSet<u32> = s.union(zs).copied().collect();
        if union.len() <= CAP {
          s = union;
          grew = true;
        }
      }
      if !grew {
        break;
      }
    }
    // Column order: next, the column that completes the most local
    // constraints (ties: most incident constraints), so the search prunes early.
    let local: Vec<&BTreeSet<u32>> = bool_zeros
      .iter()
      .map(|(_, zs)| zs)
      .filter(|zs| zs.is_subset(&s))
      .collect();
    let mut cols: Vec<u32> = vec![];
    let mut done: BTreeSet<u32> = BTreeSet::new();
    while cols.len() < s.len() {
      let best = s
        .iter()
        .filter(|c| !done.contains(c))
        .max_by_key(|&&c| {
          let complete = local
            .iter()
            .filter(|zs| {
              zs.contains(&c) && zs.iter().all(|v| *v == c || done.contains(v))
            })
            .count();
          let incident = local.iter().filter(|zs| zs.contains(&c)).count();
          (complete, incident, std::cmp::Reverse(c))
        })
        .copied()
        .expect("a remaining column");
      done.insert(best);
      cols.push(best);
    }
    let idx: HashMap<u32, usize> =
      cols.iter().enumerate().map(|(k, &c)| (c, k)).collect();
    let mut at = vec![vec![]; cols.len() + 1];
    for (z, zs) in &bool_zeros {
      if zs.is_subset(&s) {
        let last = zs.iter().map(|v| idx[v] + 1).max().unwrap_or(0);
        at[last].push(*z);
      }
    }
    let search = Search {
      g,
      at,
      cols: cols.clone(),
      idx,
      excl: &excl,
      forced: &forced,
      e: mi,
      budget: std::cell::Cell::new(BUDGET),
    };
    let mut assign = vec![0u8; cols.len()];
    match search.dfs(0, &mut assign) {
      None => proven += 1,
      Some(Outcome::Budget) => {
        failures.push(fail("search budget exhausted".into()))
      },
      Some(Outcome::Counter(bits, x)) => {
        let ones: Vec<String> = cols
          .iter()
          .zip(&bits)
          .filter(|(_, b)| **b == 1)
          .map(|(c, _)| format!("x{c}=1"))
          .collect();
        failures.push(fail(format!(
          "value {} at {} (support {} columns)",
          x.as_canonical_u64(),
          if ones.is_empty() { "all zero".into() } else { ones.join(",") },
          cols.len()
        )));
      },
    }
  }
  if failures.is_empty() { Ok(proven) } else { Err(failures) }
}

fn check_artifact(path: &str) -> Result<bool, Box<dyn std::error::Error>> {
  let (package, digest) = Package::load(path.as_ref())?;
  println!("[check-enables] {path}: blake3 {digest}");
  let mut program = package.program.check_field::<Val>()?;
  let mut trace = package.trace.ok_or("the artifact has no circuits")?;
  trace.groups.clear();
  program.track_depth(&trace)?;
  let plan = TracePlan::new(&program, trace)?;
  let chips = plan.artifact().chips.len();
  let backend = Backend::for_statistics(&plan, Parameters::default())?;
  let stats = backend.statistics();
  let mut proven = 0usize;
  let mut failed = 0usize;
  for (ci, circuit) in backend.system().circuits.iter().enumerate().take(chips)
  {
    match check_circuit(&circuit.graph, circuit.main_width, &stats[ci].name) {
      Ok(n) => proven += n,
      Err(fs) => {
        failed += fs.len();
        for f in fs {
          println!("  UNPROVEN {f}");
        }
      },
    }
  }
  println!(
    "[check-enables] {path}: {chips} chips, {proven} enables proved boolean, {failed} not"
  );
  Ok(failed == 0)
}

/// Negative and positive controls on hand-built chips: lookup 0 is the receive
/// (`pull` of the multiplicity column), the rest pushes with the given enables.
fn self_test() -> Result<(), String> {
  use multi_stark::{
    expr::Expr,
    lookup::Lookup,
    system::{CircuitInputs, System},
    types::{CommitmentParameters, FriParameters, GoldilocksBlake3V6Config},
  };
  let cp = CommitmentParameters { log_blowup: 2, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 4,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let x = |i: u32| Expr::main(i);
  let one = || Expr::constant(Val::ONE);
  let boolean = |i: u32| x(i) * (x(i) - one());
  let sum3 = || x(1) + x(2) + x(3);
  // (name, constraints, enables, every enable proved boolean?)
  let cases = vec![
    ("boolean selector", vec![boolean(1)], vec![x(1)], true),
    ("complement of a selector", vec![boolean(1)], vec![one() - x(1)], true),
    ("doubled selector", vec![boolean(1)], vec![x(1) + x(1)], false),
    ("negated selector", vec![boolean(1)], vec![-x(1)], false),
    ("unconstrained enable", vec![], vec![x(1)], false),
    (
      "exclusive pair",
      vec![boolean(1), boolean(2), x(1) * x(2)],
      vec![x(1) + x(2)],
      true,
    ),
    (
      "non-exclusive pair",
      vec![boolean(1), boolean(2)],
      vec![x(1) + x(2)],
      false,
    ),
    (
      "forced-zero sum S·(S + 1)",
      vec![boolean(1), boolean(2), boolean(3), sum3() * (sum3() + one())],
      vec![x(1) + x(2)],
      true,
    ),
    (
      "sum without S·(S + 1)",
      vec![boolean(1), boolean(2), boolean(3)],
      vec![x(1) + x(2)],
      false,
    ),
  ];
  let mut bad = vec![];
  for (name, constraints, enables, want) in cases {
    // Columns 0..4 are data or selectors, column 5 the receive multiplicity.
    let mut lookups = vec![Lookup::pull(x(5), vec![one(), x(0)])];
    lookups.extend(enables.into_iter().map(|e| Lookup::push(e, vec![x(0)])));
    let (sys, _) = System::new(
      GoldilocksBlake3V6Config::new(cp, fp),
      vec![CircuitInputs {
        main_width: 6,
        constraints,
        lookups,
        ..Default::default()
      }],
    );
    let got = check_circuit(&sys.circuits[0].graph, 6, name);
    if got.is_ok() != want {
      let want = if want { "proved" } else { "refused" };
      bad.push(format!("{name}: expected {want}, got {got:?}"));
    }
  }
  if bad.is_empty() { Ok(()) } else { Err(bad.join("\n")) }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let mut args: Vec<String> = std::env::args().skip(1).collect();
  if args.first().map(String::as_str) == Some("--self-test") {
    args.remove(0);
    self_test()
      .map_err(|e| format!("[check-enables] self-test FAILED:\n{e}"))?;
    println!("[check-enables] self-test passed");
  }
  let mut ok = true;
  for path in &args {
    ok &= check_artifact(path)?;
  }
  if !ok {
    return Err(
      "[check-enables] FAILED: an enable is not proved boolean".into(),
    );
  }
  Ok(())
}
