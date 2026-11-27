//! Differential and mutation test of the merged BLAKE3 circuit.
//!
//! `MergedLayout::try_merge` discards the lowered compact-BLAKE3 circuits'
//! constraints and lookups and restates them by hand (`B3_All`,
//! `UnifiedTable`). This test checks the hand-written circuits, FRI-arity
//! height alignment and horizontal packing against the unmerged lowering of
//! multi-stark's Plonkish frontend, with a row/column mapping written from
//! multi-stark's `plonkish/hash.rs`, not from `circuit_merge.rs`. It also
//! checks that the lowering it compares against is the one `try_merge`
//! admits (`COMPACT_BLAKE3_STRUCTURE_DIGEST`): when that constant has to move
//! after a multi-stark change, this test is the review gate.
//!
//! For every admitted `align_arity` (1..=4), with and without packing:
//! 1. honest witness: every constraint is zero on every row and the LogUp
//!    ledger (net multiplicity per trailing-zero-trimmed tuple) plus the
//!    claims is empty, for the unmerged and for the merged system;
//! 2. every active row of each original BLAKE3 trace `t0..t5` is compared with
//!    its `B3_All` row (a row/column mapping written from `hash.rs`, not
//!    from `circuit_merge.rs`): the multiset of nonzero constraint values and
//!    the net ledger agree at random main values, after renaming the BLAKE3
//!    table channel `(ns,4,2,id,..)` to `(ns,2,10+..,..)`; the merged ledger does
//!    not depend on unmapped columns; constraints that do are only the
//!    unconditional carry checks on unmapped columns; the `t4` duplicate column
//!    is tied to its slot; padding rows carry no message;
//! 3. the unified table supplies exactly the union of the original tables'
//!    tuples (after renaming);
//! 4. computation shards keep their fixed rows and every appended row is inert;
//! 5. the packed circuit equals the disjoint union of the unpacked merged
//!    circuits row by row (sampled), and every padding slice is inert;
//! 6. single-cell mutations of mapped columns on active `B3_All` rows of the
//!    honest trace are rejected (nonzero constraint or nonempty ledger delta).
use std::collections::{BTreeMap, BTreeSet};

use ix_proof_compression::fri::{
  Blake3Domain, ByteGadgets, ByteValue, blake3_domain,
};
use multi_stark::{
  expr::{Expr, RowOffset, Source},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::{Matrix, dense::RowMajorMatrix},
  plonkish::{Assignment, Circuit, CircuitBuilder, MultiStarkCircuit},
  system::CircuitInputs,
  types::Val,
};
use stark_shrinker::circuit_merge::{
  COMPACT_BLAKE3_STRUCTURE_DIGEST, MergedLayout,
  compact_blake3_structure_digest,
};

const NS: u8 = 107;
const MW: [usize; 6] = [32, 40, 32, 40, 12, 4];

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

struct Rng(u64);
impl Rng {
  fn next(&mut self) -> u64 {
    let mut x = self.0;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    self.0 = x;
    x
  }
  fn val(&mut self) -> Val {
    Val::from_u64(self.next())
  }
  fn below(&mut self, n: usize) -> usize {
    usize::try_from(self.next() % n as u64).unwrap()
  }
}

fn ev(e: &Expr<Val>, main: &[Val], fixed: &[Val]) -> Val {
  match e {
    Expr::Const(c) => *c,
    Expr::Var(c) => {
      assert_eq!(c.offset, RowOffset::Current, "next-row variable");
      match c.source {
        Source::Main => main[c.index as usize],
        Source::Preprocessed => fixed[c.index as usize],
        Source::Stage2 => panic!("stage-2 variable"),
      }
    },
    Expr::Add(a, b) => ev(a, main, fixed) + ev(b, main, fixed),
    Expr::Sub(a, b) => ev(a, main, fixed) - ev(b, main, fixed),
    Expr::Mul(a, b) => ev(a, main, fixed) * ev(b, main, fixed),
    Expr::Neg(a) => -ev(a, main, fixed),
    other => panic!("unsupported expression {other:?}"),
  }
}

fn main_vars(e: &Expr<Val>, out: &mut BTreeSet<usize>) {
  match e {
    Expr::Var(c) if c.source == Source::Main => {
      out.insert(c.index as usize);
    },
    Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
      main_vars(a, out);
      main_vars(b, out);
    },
    Expr::Neg(a) => main_vars(a, out),
    _ => {},
  }
}

type Tuple = Vec<u64>;
type Ledger = BTreeMap<Tuple, u64>;

fn trim(mut t: Tuple) -> Tuple {
  while t.last() == Some(&0) {
    t.pop();
  }
  t
}

fn add(l: &mut BTreeMap<Tuple, Val>, t: Tuple, m: Val) {
  if m == Val::ZERO {
    return;
  }
  *l.entry(t).or_insert(Val::ZERO) += m;
}

fn finish(l: BTreeMap<Tuple, Val>) -> Ledger {
  l.into_iter()
    .filter(|(_, v)| *v != Val::ZERO)
    .map(|(k, v)| (k, v.as_canonical_u64()))
    .collect()
}

/// Original BLAKE3 table channel `(ns,4,2,id,..)` in the merged vocabulary.
fn rename_b3(a: Vec<u64>) -> Tuple {
  let ns = u64::from(NS);
  if a.len() >= 4 && a[0] == ns && a[1] == 4 && a[2] == 2 {
    match a[3] {
      0 => [vec![ns, 2, 10], a[4..].to_vec()].concat(),
      1 => {
        let tid = match a[4] {
          4 => 11,
          7 => 12,
          other => panic!("split bits {other}"),
        };
        [vec![ns, 2, tid], a[5..].to_vec()].concat()
      },
      2 => [vec![ns, 2, 13], a[4..].to_vec()].concat(),
      other => panic!("unknown BLAKE3 table {other}"),
    }
  } else {
    a
  }
}

/// Sorted nonzero constraint values (with indices) and net ledger of one row.
fn row_eval(
  def: &CircuitInputs<Val>,
  main: &[Val],
  fixed: &[Val],
  rename: bool,
) -> (Vec<u64>, Vec<(usize, u64)>, Ledger) {
  let indexed: Vec<(usize, u64)> = def
    .constraints
    .iter()
    .enumerate()
    .map(|(i, c)| (i, ev(c, main, fixed).as_canonical_u64()))
    .filter(|&(_, v)| v != 0)
    .collect();
  let mut cons: Vec<u64> = indexed.iter().map(|&(_, v)| v).collect();
  cons.sort_unstable();
  let mut l = BTreeMap::new();
  for lk in &def.lookups {
    let m = ev(&lk.multiplicity, main, fixed);
    if m == Val::ZERO {
      continue;
    }
    let args: Vec<u64> =
      lk.args.iter().map(|a| ev(a, main, fixed).as_canonical_u64()).collect();
    let t = if rename { rename_b3(args) } else { args };
    add(&mut l, trim(t), m);
  }
  (cons, indexed, finish(l))
}

fn fixed_row(def: &CircuitInputs<Val>, r: usize) -> &[Val] {
  let p = def.preprocessed.as_ref().expect("fixed matrix");
  &p.values[r * p.width..(r + 1) * p.width]
}

fn height(def: &CircuitInputs<Val>) -> usize {
  def.preprocessed.as_ref().map_or(0, Matrix::height)
}

/// Honest witness: violated constraint rows, and the residual ledger after the
/// claims with the sign that empties it (or the smaller residual).
fn global(
  defs: &[CircuitInputs<Val>],
  traces: &[RowMajorMatrix<Val>],
  claims: &[Vec<Val>],
) -> (usize, i32, usize) {
  assert_eq!(defs.len(), traces.len());
  let mut bad = 0usize;
  let mut l = BTreeMap::new();
  for (def, tr) in defs.iter().zip(traces) {
    let h = tr.height();
    if h == 0 {
      continue;
    }
    assert_eq!(h, height(def), "trace height differs from fixed height");
    assert_eq!(tr.width, def.main_width);
    for r in 0..h {
      let main = &tr.values[r * tr.width..(r + 1) * tr.width];
      let fixed = fixed_row(def, r);
      if def.constraints.iter().any(|c| ev(c, main, fixed) != Val::ZERO) {
        bad += 1;
      }
      for lk in &def.lookups {
        let m = ev(&lk.multiplicity, main, fixed);
        if m == Val::ZERO {
          continue;
        }
        let args: Vec<u64> = lk
          .args
          .iter()
          .map(|a| ev(a, main, fixed).as_canonical_u64())
          .collect();
        add(&mut l, trim(args), m);
      }
    }
  }
  let mut best = (0, usize::MAX);
  for sign in [1i32, -1] {
    let mut l2 = l.clone();
    for c in claims {
      let t = trim(c.iter().map(|v| v.as_canonical_u64()).collect());
      add(&mut l2, t, if sign == 1 { Val::ONE } else { Val::NEG_ONE });
    }
    let residual = finish(l2).len();
    if residual < best.1 {
      best = (sign, residual);
    }
  }
  (bad, best.0, best.1)
}

/// Mapped merged columns of original trace `t` (and the `t4` duplicate).
fn map_row(t: usize, m: &[Val], out: &mut [Val]) -> BTreeSet<usize> {
  let mut mapped = BTreeSet::new();
  match t {
    0..=3 => {
      for j in 0..MW[t] {
        out[j] = m[j];
        mapped.insert(j);
      }
    },
    4 => {
      for j in 0..12 {
        out[12 + j] = m[j];
        mapped.insert(12 + j);
      }
      for i in 0..4 {
        out[28 + i] = m[8 + i];
        mapped.insert(28 + i);
      }
    },
    _ => {
      for j in 0..4 {
        out[j] = m[j];
        mapped.insert(j);
      }
    },
  }
  mapped
}

struct Report {
  rows: usize,
  failures: Vec<String>,
}

impl Report {
  fn fail(&mut self, s: String) {
    if self.failures.len() < 40 {
      eprintln!("FAIL {s}");
    }
    self.failures.push(s);
  }
}

/// Checks 2–4 for one unpacked merged layout.
fn check_unpacked(
  raw: &[CircuitInputs<Val>],
  merged: &[CircuitInputs<Val>],
  num_main: usize,
  rng: &mut Rng,
  rep: &mut Report,
) {
  assert_eq!(merged.len(), num_main + 2, "unpacked merged circuit count");
  let b3s = num_main + 1;
  let b3 = &merged[num_main];
  let unified = &merged[num_main + 1];
  assert_eq!(b3.main_width, 40);
  // Active rows per original trace (contiguous from row 0, row 0 always kept).
  let mut active = [0usize; 6];
  for t in 0..6 {
    let d = &raw[b3s + t];
    assert_eq!(d.main_width, MW[t]);
    let h = height(d);
    let enabled: Vec<bool> =
      (0..h).map(|r| fixed_row(d, r)[0] != Val::ZERO).collect();
    let n = enabled.iter().filter(|&&e| e).count();
    if !enabled[..n].iter().all(|&e| e) {
      rep.fail(format!("t{t}: enabled rows are not contiguous"));
    }
    for r in n.max(1)..h {
      if fixed_row(d, r).iter().any(|&v| v != Val::ZERO) {
        rep.fail(format!("t{t}: nonzero fixed row {r} past the enabled rows"));
      }
    }
    active[t] = n.max(1);
  }
  let used: usize = active.iter().sum();
  if used > height(b3) {
    rep.fail(format!("B3_All height {} < used {used}", height(b3)));
    return;
  }
  // Check 2: each active original row against its merged row.
  let mut base = 0usize;
  for t in 0..6 {
    let orig = &raw[b3s + t];
    for r in 0..active[t] {
      let fo = fixed_row(orig, r);
      let fm = fixed_row(b3, base + r);
      for trial in 0..2 {
        let m: Vec<Val> = (0..MW[t]).map(|_| rng.val()).collect();
        let mut mz = vec![Val::ZERO; 40];
        let mapped = map_row(t, &m, &mut mz);
        let (co, _, lo) = row_eval(orig, &m, fo, true);
        let (cm, im, lm) = row_eval(b3, &mz, fm, false);
        rep.rows += 1;
        if co != cm {
          rep.fail(format!(
            "t{t} row {r} trial {trial}: constraints differ ({} original nonzero, {} merged nonzero)",
            co.len(),
            cm.len()
          ));
        }
        if lo != lm {
          let only_o: Vec<_> =
            lo.iter().filter(|(k, v)| lm.get(*k) != Some(*v)).take(3).collect();
          let only_m: Vec<_> =
            lm.iter().filter(|(k, v)| lo.get(*k) != Some(*v)).take(3).collect();
          rep.fail(format!(
            "t{t} row {r} trial {trial}: ledgers differ; original-only {only_o:?}; merged-only {only_m:?}"
          ));
        }
        // Unmapped columns: ledger invariant; constraints that move read only
        // unmapped columns.
        let mut mr = mz.clone();
        for (c, cell) in mr.iter_mut().enumerate() {
          if !mapped.contains(&c) {
            *cell = rng.val();
          }
        }
        let (_, ir, lr) = row_eval(b3, &mr, fm, false);
        if lr != lm {
          rep.fail(format!(
            "t{t} row {r}: merged ledger depends on unmapped columns"
          ));
        }
        let before: BTreeMap<usize, u64> = im.iter().copied().collect();
        let after: BTreeMap<usize, u64> = ir.iter().copied().collect();
        for (i, c) in b3.constraints.iter().enumerate() {
          if before.get(&i) != after.get(&i) {
            let mut vars = BTreeSet::new();
            main_vars(c, &mut vars);
            if vars.iter().any(|v| mapped.contains(v)) {
              rep.fail(format!(
                "t{t} row {r}: constraint {i} moves with unmapped columns but also reads mapped ones {vars:?}"
              ));
            }
          }
        }
        // The t4 duplicate must be tied to its slot.
        if t == 4 {
          for i in 0..4 {
            let mut md = mz.clone();
            md[28 + i] += Val::ONE;
            let (cd, _, ld) = row_eval(b3, &md, fm, false);
            if cd.is_empty() && ld == lm {
              rep.fail(format!(
                "t4 row {r}: duplicate column {} is free",
                28 + i
              ));
            }
          }
        }
      }
    }
    base += active[t];
  }
  // Padding rows of B3_All: no message; only constraints on unmapped carries.
  for r in used..height(b3) {
    if r > used + 64 && r + 64 < height(b3) && rng.below(64) != 0 {
      continue;
    }
    let fm = fixed_row(b3, r);
    let mr: Vec<Val> = (0..40).map(|_| rng.val()).collect();
    let (_, im, lm) = row_eval(b3, &mr, fm, false);
    if !lm.is_empty() {
      rep.fail(format!(
        "B3_All padding row {r} carries {} message(s)",
        lm.len()
      ));
    }
    for (i, _) in im {
      let mut vars = BTreeSet::new();
      main_vars(&b3.constraints[i], &mut vars);
      if !vars.iter().all(|v| (24..28).contains(v)) {
        rep.fail(format!(
          "B3_All padding row {r}: constraint {i} reads {vars:?}"
        ));
      }
    }
  }
  // Check 3: the unified table supplies exactly the original tables' tuples.
  let one = [Val::ONE];
  let mut expected = BTreeSet::new();
  for d in std::iter::once(&raw[num_main]).chain(&raw[b3s + 6..b3s + 9]) {
    assert_eq!(d.main_width, 1);
    for r in 0..height(d) {
      let (_, _, l) = row_eval(d, &one, fixed_row(d, r), true);
      for (k, v) in l {
        assert_eq!(v, 1, "original table multiplicity");
        expected.insert(k);
      }
    }
  }
  let mut supplied = BTreeSet::new();
  assert_eq!(unified.main_width, 1);
  if !unified.constraints.is_empty() {
    rep.fail("unified table has constraints".into());
  }
  for r in 0..height(unified) {
    let (_, _, l) = row_eval(unified, &one, fixed_row(unified, r), false);
    for (k, v) in l {
      if v != 1 {
        rep.fail(format!("unified row {r}: multiplicity sign {v}"));
      }
      supplied.insert(k);
    }
  }
  if supplied != expected {
    rep.fail(format!(
      "unified table tuples differ: {} supplied, {} expected, {} extra, {} missing",
      supplied.len(),
      expected.len(),
      supplied.difference(&expected).count(),
      expected.difference(&supplied).count()
    ));
  }
  // Check 4: computation shards keep their rows; appended rows are inert.
  for i in 0..num_main {
    let (a, b) = (&raw[i], &merged[i]);
    let (ha, hb) = (height(a), height(b));
    if hb < ha || a.main_width != b.main_width {
      rep.fail(format!(
        "shard {i}: shape {ha}x{} -> {hb}x{}",
        a.main_width, b.main_width
      ));
      continue;
    }
    for r in 0..ha {
      if fixed_row(a, r) != fixed_row(b, r) {
        rep.fail(format!("shard {i}: fixed row {r} changed"));
        break;
      }
    }
    for r in ha..hb {
      if fixed_row(b, r).iter().any(|&v| v != Val::ZERO) {
        rep.fail(format!("shard {i}: appended row {r} is not zero"));
        break;
      }
    }
    if hb > ha {
      for _ in 0..16 {
        let r = ha + rng.below(hb - ha);
        let m: Vec<Val> = (0..b.main_width).map(|_| rng.val()).collect();
        let (c, _, l) = row_eval(b, &m, fixed_row(b, r), false);
        if !c.is_empty() || !l.is_empty() {
          rep.fail(format!("shard {i}: appended row {r} is not inert"));
        }
      }
    }
    // Same relation on the kept rows (the expressions themselves).
    for _ in 0..8 {
      let r = rng.below(ha);
      let m: Vec<Val> = (0..a.main_width).map(|_| rng.val()).collect();
      let x = row_eval(a, &m, fixed_row(a, r), false);
      let y = row_eval(b, &m, fixed_row(b, r), false);
      if x.0 != y.0 || x.2 != y.2 {
        rep.fail(format!("shard {i}: row {r} relation changed"));
      }
    }
  }
}

/// Check 5: the packed circuit is the disjoint union of the unpacked ones.
fn check_packed(
  unpacked: &[CircuitInputs<Val>],
  packed: &CircuitInputs<Val>,
  table_tuples: &BTreeSet<Tuple>,
  rng: &mut Rng,
  rep: &mut Report,
) {
  let hp = height(packed);
  let hmax = unpacked.iter().map(height).max().unwrap();
  if hp != hmax {
    rep.fail(format!("packed height {hp} != max sub height {hmax}"));
  }
  let mut mo = vec![];
  let mut fo = vec![];
  let (mut m, mut f) = (0, 0);
  for d in unpacked {
    mo.push(m);
    fo.push(f);
    m += d.main_width;
    f += d.preprocessed.as_ref().unwrap().width;
  }
  if packed.main_width != m || packed.preprocessed.as_ref().unwrap().width != f
  {
    rep.fail("packed widths".into());
    return;
  }
  let mut padding_kind = vec![(0usize, 0usize); unpacked.len()];
  for r in 0..hp {
    let pr = fixed_row(packed, r);
    for (k, d) in unpacked.iter().enumerate() {
      let w = d.preprocessed.as_ref().unwrap().width;
      let slice = &pr[fo[k]..fo[k] + w];
      if r < height(d) {
        if slice != fixed_row(d, r) {
          rep.fail(format!("packed row {r}: sub {k} fixed slice differs"));
        }
      } else if slice.iter().all(|&v| v == Val::ZERO) {
        padding_kind[k].0 += 1;
      } else if slice == fixed_row(d, 0) {
        padding_kind[k].1 += 1;
      } else {
        rep.fail(format!(
          "packed row {r}: sub {k} padding slice is neither zero nor row 0"
        ));
      }
    }
  }
  eprintln!(
    "  packed padding (zero rows, row-0 repeats) per sub-circuit: {padding_kind:?}"
  );
  let mut samples: BTreeSet<usize> = (0..hp.min(512)).collect();
  samples.extend(hp.saturating_sub(512)..hp);
  for d in unpacked {
    let h = height(d);
    samples.extend(h.saturating_sub(32)..(h + 32).min(hp));
  }
  for _ in 0..2048 {
    samples.insert(rng.below(hp));
  }
  for &r in &samples {
    let pr = fixed_row(packed, r);
    let x: Vec<Val> = (0..packed.main_width).map(|_| rng.val()).collect();
    let (cp, _, lp) = row_eval(packed, &x, pr, false);
    let mut cu = vec![];
    let mut lu: BTreeMap<Tuple, Val> = BTreeMap::new();
    for (k, d) in unpacked.iter().enumerate() {
      let w = d.preprocessed.as_ref().unwrap().width;
      let slice = &pr[fo[k]..fo[k] + w];
      let main = &x[mo[k]..mo[k] + d.main_width];
      let (c, ic, l) = row_eval(d, main, slice, false);
      if r >= height(d) {
        // Padding slice: inert, or a repeated genuine table row.
        for key in l.keys() {
          if !table_tuples.contains(key) {
            rep.fail(format!(
              "packed row {r}: sub {k} padding supplies a non-table tuple"
            ));
          }
        }
        for (i, _) in &ic {
          let mut vars = BTreeSet::new();
          main_vars(&d.constraints[*i], &mut vars);
          if !(d.main_width == 40 && vars.iter().all(|v| (24..28).contains(v)))
          {
            rep.fail(format!(
              "packed row {r}: sub {k} padding constraint {i} reads {vars:?}"
            ));
          }
        }
      }
      cu.extend(c);
      for (key, v) in l {
        add(&mut lu, key, Val::from_u64(v));
      }
    }
    cu.sort_unstable();
    rep.rows += 1;
    if cp != cu || lp != finish(lu) {
      rep.fail(format!(
        "packed row {r}: differs from the union of sub-circuits"
      ));
    }
  }
}

/// Check 6: mutations of mapped columns on active `B3_All` rows are rejected.
fn mutate_b3(
  raw: &[CircuitInputs<Val>],
  merged: &[CircuitInputs<Val>],
  traces: &[RowMajorMatrix<Val>],
  num_main: usize,
  rng: &mut Rng,
  rep: &mut Report,
) -> (usize, usize) {
  let b3s = num_main + 1;
  let b3 = &merged[num_main];
  let tr = &traces[num_main];
  let mut spans = vec![];
  let mut base = 0;
  for t in 0..6 {
    let d = &raw[b3s + t];
    let n = (0..height(d)).filter(|&r| fixed_row(d, r)[0] != Val::ZERO).count();
    spans.push((t, base, n));
    base += n.max(1);
  }
  let (mut tried, mut accepted) = (0, 0);
  for _ in 0..3000 {
    let (t, start, n) = spans[rng.below(6)];
    if n == 0 {
      continue;
    }
    let r = start + rng.below(n);
    let mut probe = vec![Val::ZERO; 40];
    let mapped: Vec<usize> =
      map_row(t, &vec![Val::ZERO; MW[t]], &mut probe).into_iter().collect();
    let c = mapped[rng.below(mapped.len())];
    let row = tr.values[r * 40..(r + 1) * 40].to_vec();
    let fm = fixed_row(b3, r);
    let (_, _, l0) = row_eval(b3, &row, fm, false);
    let mut mutated = row.clone();
    mutated[c] += Val::from_u64(1 + rng.next() % 255);
    let (c1, _, l1) = row_eval(b3, &mutated, fm, false);
    tried += 1;
    if c1.is_empty() && l1 == l0 {
      accepted += 1;
      rep.fail(format!("mutation of t{t} row {r} column {c} accepted"));
    }
  }
  (tried, accepted)
}

/// A circuit with byte gadgets and compact BLAKE3 calls of the given lengths.
fn build(lens: &[usize], seed: u64) -> (Circuit<Val>, Assignment<Val>) {
  let mut b = CircuitBuilder::<Val>::new();
  b.enable_compact_blake3();
  let bytes = ByteGadgets::new(&mut b);
  let mut inputs: Vec<(ByteValue, u8)> = vec![];
  let mut publics = vec![];
  let mut rng = Rng(seed);
  for (k, &len) in lens.iter().enumerate() {
    let data: Vec<u8> = (0..len).map(|_| rng.next().to_le_bytes()[0]).collect();
    let msg: Vec<ByteValue> = data
      .iter()
      .enumerate()
      .map(|(i, &x)| {
        let v = bytes.input(&mut b, &format!("m{k}_{i}"));
        inputs.push((v, x));
        v
      })
      .collect();
    let domain =
      if k % 2 == 0 { Blake3Domain::MerkleLeaf } else { Blake3Domain::Plain };
    let digest = blake3_domain(&mut b, &bytes, domain, &msg);
    let expected = domain.hash_bytes(&data);
    for j in [0usize, 31] {
      let p = b.public_input(format!("d{k}_{j}"));
      b.assert_equal(digest[j].value(), p);
      publics.push((p, expected[j]));
    }
  }
  let circuit = b.finish();
  let mut w = circuit.witness();
  for (v, x) in inputs {
    w.set(v.value(), Val::from_u8(x)).unwrap();
  }
  for (p, x) in publics {
    w.set(p, Val::from_u8(x)).unwrap();
  }
  let a = w.generate().unwrap();
  (circuit, a)
}

fn run_case(
  name: &str,
  lens: &[usize],
  lower_h: usize,
  merge_h: usize,
) -> Vec<String> {
  eprintln!(
    "== case {name}: lengths {lens:?}, lowering cap 2^{}, merge cap 2^{}",
    lower_h.ilog2(),
    merge_h.ilog2()
  );
  let (circuit, assignment) = build(lens, 0x5eed_0000 ^ lens.len() as u64);
  let publics = assignment.public_values().to_vec();
  let compiled: MultiStarkCircuit<Val> = circuit
    .lower_to_multi_stark_sharded(Val::from_u8(NS), lower_h)
    .unwrap()
    .merge_table_traces(lower_h)
    .unwrap();
  let claims = compiled.claims(&publics).unwrap();
  let raw = compiled.circuit_inputs();
  let num_main = compiled.main_heights().len();
  eprintln!(
    "  {} computation partition(s) {:?}; {} circuits; B3 trace heights {:?}",
    num_main,
    compiled.main_heights(),
    raw.len(),
    raw[num_main + 1..num_main + 7].iter().map(height).collect::<Vec<_>>()
  );
  assert_eq!(raw.len(), num_main + 10, "standard compact-BLAKE3 layout");
  let digest = compact_blake3_structure_digest(&raw[num_main + 1..]);
  eprintln!("  compact-BLAKE3 structure digest {}", hex(&digest));
  assert_eq!(
    digest, COMPACT_BLAKE3_STRUCTURE_DIGEST,
    "the lowering compared here is not the one try_merge admits"
  );
  // A changed gadget (one more constraint, a changed lookup or table entry)
  // is refused by `try_merge` until the merged circuits are reviewed.
  for (what, change) in
    [("constraint", 0usize), ("lookup argument", 1), ("table entry", 2)]
  {
    let mut changed = raw.clone();
    match change {
      0 => {
        let c = changed[num_main + 1].constraints[0].clone();
        changed[num_main + 1].constraints.push(c);
      },
      1 => {
        let arg = changed[num_main + 2].lookups[0].args.pop().unwrap();
        changed[num_main + 2].lookups[0].args.push(arg + Expr::Const(Val::ONE));
      },
      _ => {
        let prep = changed[num_main + 7].preprocessed.as_mut().unwrap();
        prep.values[5] += Val::ONE;
      },
    }
    let err = MergedLayout::try_merge(&compiled, changed, NS, merge_h, 1, true)
      .err()
      .unwrap_or_else(|| panic!("{name}: try_merge admitted a changed {what}"));
    assert!(err.contains("structure digest"), "{err}");
  }
  let shards = compiled.trace_shards(&assignment).unwrap();
  let unmerged: Vec<_> =
    (0..compiled.num_circuits()).map(|i| shards.trace(i).unwrap()).collect();
  let (bad, sign, residual) = global(&raw, &unmerged, &claims);
  eprintln!(
    "  unmerged honest: {bad} violated rows, claims sign {sign}, residual {residual}"
  );
  let mut failures = vec![];
  if bad != 0 || residual != 0 {
    failures
      .push(format!("{name}: unmerged honest witness rejected by the checker"));
  }
  let mut rng = Rng(0x0123_4567_89ab_cdef);
  let mut table_tuples = BTreeSet::new();
  for align in 1..=4usize {
    let (unpacked, layout) = MergedLayout::try_merge(
      &compiled,
      raw.clone(),
      NS,
      merge_h,
      align,
      false,
    )
    .unwrap();
    assert!(layout.is_merged(), "layout did not merge");
    let mut rep = Report { rows: 0, failures: vec![] };
    check_unpacked(&raw, &unpacked, num_main, &mut rng, &mut rep);
    let traces = layout.build_traces(&compiled, &assignment).unwrap();
    let (bad, sign2, residual) = global(&unpacked, &traces, &claims);
    if bad != 0 || residual != 0 || sign2 != sign {
      rep.fail(format!("align {align}: merged honest witness: {bad} violated rows, residual {residual}"));
    }
    let (tried, accepted) =
      mutate_b3(&raw, &unpacked, &traces, num_main, &mut rng, &mut rep);
    if table_tuples.is_empty() {
      let one = [Val::ONE];
      let u = &unpacked[num_main + 1];
      for r in 0..height(u) {
        table_tuples
          .extend(row_eval(u, &one, fixed_row(u, r), false).2.into_keys());
      }
    }
    eprintln!(
      "  align {align} unpacked: heights {:?}; {} row comparisons; honest ok={}; mutations {tried} tried, {accepted} accepted; {} failure(s)",
      unpacked.iter().map(height).collect::<Vec<_>>(),
      rep.rows,
      bad == 0 && residual == 0,
      rep.failures.len()
    );
    failures.extend(
      rep.failures.iter().map(|f| format!("{name} align {align}: {f}")),
    );
    let (packed, playout) =
      MergedLayout::try_merge(&compiled, raw.clone(), NS, merge_h, align, true)
        .unwrap();
    assert_eq!(packed.len(), 1, "packing did not produce one circuit");
    let mut rep = Report { rows: 0, failures: vec![] };
    check_packed(&unpacked, &packed[0], &table_tuples, &mut rng, &mut rep);
    let ptraces = playout.build_traces(&compiled, &assignment).unwrap();
    let (bad, _, residual) = global(&packed, &ptraces, &claims);
    if bad != 0 || residual != 0 {
      rep.fail(format!(
        "packed honest witness: {bad} violated rows, residual {residual}"
      ));
    }
    eprintln!(
      "  align {align} packed: height {}, main width {}, fixed width {}; {} sampled rows; honest ok={}; {} failure(s)",
      height(&packed[0]),
      packed[0].main_width,
      packed[0].preprocessed.as_ref().unwrap().width,
      rep.rows,
      bad == 0 && residual == 0,
      rep.failures.len()
    );
    failures.extend(
      rep.failures.iter().map(|f| format!("{name} align {align} packed: {f}")),
    );
  }
  failures
}

#[test]
fn merged_blake3_circuit_is_equivalent_for_every_alignment() {
  let mut failures = vec![];
  failures.extend(run_case(
    "small",
    &[0, 1, 7, 64, 65, 200, 1100],
    1 << 16,
    1 << 18,
  ));
  failures.extend(run_case(
    "two-partitions",
    &[16_000, 3, 1025],
    1 << 16,
    1 << 18,
  ));
  // Computation shard taller than the unified table: exercises the row-0
  // repeat padding of the table inside the packed circuit (align 1).
  failures.extend(run_case(
    "tall-computation",
    &[30_000, 17],
    1 << 18,
    1 << 18,
  ));
  for f in failures.iter().take(60) {
    eprintln!("{f}");
  }
  assert!(failures.is_empty(), "{} failure(s)", failures.len());
}
