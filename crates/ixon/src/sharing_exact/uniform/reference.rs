//! Old unbounded uniform solver: test/reference feature only.
//! Algorithm and controls moved from uniform.rs without rule changes.

use super::*;

/// `x` as a delta; the reference refuses outside `i128`.
fn to_i(x: u128) -> Result<i128, SharingError> {
  Fast::signed(&x)
}

impl CompCtx<'_, '_> {
  /// Depth-first branch and bound over the members (ascending), "not
  /// stored" first. Returns the best choice and the best per set size.
  fn search(
    &mut self,
    meter: &mut Meter<'_>,
  ) -> Result<(Choice, Vec<Option<Choice>>), SharingError> {
    let mut best: Option<Choice> = None;
    let mut by_size: Vec<Option<Choice>> = Vec::new();
    // Frames: (next member index, chosen so far).
    let mut stack: Vec<(usize, Vec<TermId>)> = vec![(0, Vec::new())];
    while let Some((i, chosen)) = stack.pop() {
      meter.state()?;
      for (k, &m) in self.members.iter().enumerate() {
        self.avail[ix(m)] = k >= i || chosen.contains(&m);
      }
      let (phi, work) = self.phi(&chosen)?;
      meter.work(work)?;
      let delta = to_i(phi)? - to_i(self.phi0)?;
      if i >= self.members.len() {
        if better(&delta, &chosen, best.as_ref()) {
          best = Some((delta, chosen.clone()));
        }
        let k = chosen.len();
        if by_size.len() <= k {
          by_size.resize(k + 1, None);
        }
        if better(&delta, &chosen, by_size[k].as_ref()) {
          by_size[k] = Some((delta, chosen));
        }
        continue;
      }
      if let Some((b, _)) = &best
        && delta > b + self.slack
      {
        continue;
      }
      let t = self.members[i];
      let mut with = chosen.clone();
      with.push(t);
      stack.push((i + 1, with));
      stack.push((i + 1, chosen));
    }
    for &m in &self.members {
      self.avail[ix(m)] = false;
    }
    let best =
      best.ok_or_else(|| internal("component search found no choice"))?;
    Ok((best, by_size))
  }
}

/// The sorted concatenation of two ascending slices, without allocation.
/// Equal elements are emitted twice, just as `merge_sorted` preserves them.
struct Merged<'a> {
  a: &'a [TermId],
  b: &'a [TermId],
}

impl Iterator for Merged<'_> {
  type Item = TermId;

  fn next(&mut self) -> Option<TermId> {
    match (self.a.split_first(), self.b.split_first()) {
      (Some((&x, a)), Some((&y, b))) => {
        if x <= y {
          self.a = a;
          Some(x)
        } else {
          self.b = b;
          Some(y)
        }
      },
      (Some((&x, a)), None) => {
        self.a = a;
        Some(x)
      },
      (None, Some((&y, b))) => {
        self.b = b;
        Some(y)
      },
      (None, None) => None,
    }
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let n = self.a.len() + self.b.len();
    (n, Some(n))
  }
}

impl ExactSizeIterator for Merged<'_> {}

/// Exactly `set_prec` on the two materialized merges, including prefix and
/// equal-sequence behavior. No disjointness or duplicate removal is assumed.
fn merged_prec(mut a: Merged<'_>, mut b: Merged<'_>) -> bool {
  loop {
    match (a.next(), b.next()) {
      (Some(x), Some(y)) if x == y => {},
      (Some(x), Some(y)) => return y < x,
      (None, Some(_)) => return true,
      _ => return false,
    }
  }
}

#[cfg(test)]
type DelayedChoice<'a> = (i128, &'a [TermId], &'a [TermId]);

/// Convolve tables of ascending choices in the original pair order, keeping
/// the same winner at every actual merged count. Only final winners allocate.
#[cfg(test)]
fn table_conv(a: &CTable, b: &CTable) -> CTable {
  let mut out: Vec<Option<DelayedChoice<'_>>> = Vec::new();
  for (da, sa) in a.iter().flatten() {
    for (db, sb) in b.iter().flatten() {
      let delta = da + db;
      let k = sa.len() + sb.len();
      if out.len() <= k {
        out.resize(k + 1, None);
      }
      let wins = match out[k] {
        None => true,
        Some((d, a, b)) => {
          delta < d
            || (delta == d
              && merged_prec(Merged { a: sa, b: sb }, Merged { a, b }))
        },
      };
      if wins {
        out[k] = Some((delta, sa, sb));
      }
    }
  }
  out
    .into_iter()
    .map(|e| e.map(|(d, a, b)| (d, Merged { a, b }.collect())))
    .collect()
}

// SCtx choices use a bounded component-local encoding. Global tables and
// the count knapsack still receive the original sorted ID vectors.
const PACKED_MEMBERS: usize = 512;

#[derive(Clone, Debug, PartialEq, Eq)]
enum LocalSet {
  Listed(Vec<TermId>),
  Packed(Box<[u64]>),
}

impl LocalSet {
  fn len(&self) -> usize {
    match self {
      Self::Listed(ids) => ids.len(),
      Self::Packed(words) => {
        words.iter().map(|w| w.count_ones() as usize).sum()
      },
    }
  }
}

type LocalTable = Vec<Option<(i128, LocalSet)>>;

enum LocalIter<'a> {
  Listed(std::slice::Iter<'a, TermId>),
  Packed { members: &'a [TermId], words: &'a [u64], at: usize, bits: u64 },
}

impl Iterator for LocalIter<'_> {
  type Item = TermId;
  fn next(&mut self) -> Option<TermId> {
    match self {
      Self::Listed(ids) => ids.next().copied(),
      Self::Packed { members, words, at, bits } => loop {
        if *bits != 0 {
          let bit = bits.trailing_zeros() as usize;
          *bits &= *bits - 1;
          return Some(members[*at * 64 + bit]);
        }
        *at += 1;
        *bits = *words.get(*at)?;
      },
    }
  }
}

#[derive(Clone, Copy)]
struct LocalPair<'a> {
  a: &'a LocalSet,
  b: &'a LocalSet,
  packed: bool,
}

#[derive(Clone, Copy)]
struct ComponentSets<'a> {
  members: &'a [TermId],
  words: Option<usize>,
}

impl<'a> ComponentSets<'a> {
  fn new(members: &'a [TermId], enabled: bool) -> Self {
    let packed = enabled
      && members.len() <= PACKED_MEMBERS
      && members.windows(2).all(|w| w[0] < w[1]);
    Self { members, words: packed.then(|| members.len().div_ceil(64)) }
  }

  fn pack(&self, ids: Vec<TermId>) -> LocalSet {
    let Some(n) = self.words else {
      return LocalSet::Listed(ids);
    };
    if !ids.windows(2).all(|w| w[0] < w[1]) {
      return LocalSet::Listed(ids);
    }
    let mut words = vec![0u64; n];
    for &t in &ids {
      let Ok(i) = self.members.binary_search(&t) else {
        return LocalSet::Listed(ids);
      };
      words[i / 64] |= 1 << (i % 64);
    }
    LocalSet::Packed(words.into_boxed_slice())
  }

  fn iter<'b>(&'b self, set: &'b LocalSet) -> LocalIter<'b> {
    match set {
      LocalSet::Listed(ids) => LocalIter::Listed(ids.iter()),
      LocalSet::Packed(words) => LocalIter::Packed {
        members: self.members,
        words,
        at: 0,
        bits: words.first().copied().unwrap_or(0),
      },
    }
  }

  fn iter_prec(
    mut a: impl Iterator<Item = TermId>,
    mut b: impl Iterator<Item = TermId>,
  ) -> bool {
    loop {
      match (a.next(), b.next()) {
        (Some(x), Some(y)) if x == y => {},
        (Some(x), Some(y)) => return y < x,
        (None, Some(_)) => return true,
        _ => return false,
      }
    }
  }

  fn prec(&self, a: &LocalSet, b: &LocalSet) -> bool {
    match (a, b) {
      (LocalSet::Listed(a), LocalSet::Listed(b)) => set_prec(a, b),
      (LocalSet::Packed(a), LocalSet::Packed(b)) => {
        for (&a, &b) in a.iter().zip(b) {
          let diff = a ^ b;
          if diff != 0 {
            return a & (1 << diff.trailing_zeros()) == 0;
          }
        }
        false
      },
      _ => Self::iter_prec(self.iter(a), self.iter(b)),
    }
  }

  fn pair<'b>(&self, a: &'b LocalSet, b: &'b LocalSet) -> LocalPair<'b> {
    let packed = match (self.words, a, b) {
      (Some(n), LocalSet::Packed(a), LocalSet::Packed(b)) => {
        a.len() == n && b.len() == n && a.iter().zip(b).all(|(a, b)| a & b == 0)
      },
      _ => false,
    };
    LocalPair { a, b, packed }
  }

  fn union<'b>(
    &'b self,
    pair: LocalPair<'b>,
  ) -> impl Iterator<Item = TermId> + 'b {
    let mut a = self.iter(pair.a).peekable();
    let mut b = self.iter(pair.b).peekable();
    std::iter::from_fn(move || match (a.peek(), b.peek()) {
      (Some(x), Some(y)) if x <= y => a.next(),
      (_, Some(_)) => b.next(),
      (Some(_), None) => a.next(),
      (None, None) => None,
    })
  }

  fn pair_prec(&self, a: LocalPair<'_>, b: LocalPair<'_>) -> bool {
    if a.packed
      && b.packed
      && let (
        LocalSet::Packed(a1),
        LocalSet::Packed(a2),
        LocalSet::Packed(b1),
        LocalSet::Packed(b2),
      ) = (a.a, a.b, b.a, b.b)
    {
      for ((&a1, &a2), (&b1, &b2)) in a1.iter().zip(a2).zip(b1.iter().zip(b2)) {
        let a = a1 | a2;
        let diff = a ^ (b1 | b2);
        if diff != 0 {
          return a & (1 << diff.trailing_zeros()) == 0;
        }
      }
      return false;
    }
    if let (
      LocalSet::Listed(a1),
      LocalSet::Listed(a2),
      LocalSet::Listed(b1),
      LocalSet::Listed(b2),
    ) = (a.a, a.b, b.a, b.b)
    {
      return merged_prec(Merged { a: a1, b: a2 }, Merged { a: b1, b: b2 });
    }
    Self::iter_prec(self.union(a), self.union(b))
  }

  fn materialize(&self, pair: LocalPair<'_>) -> LocalSet {
    if pair.packed
      && let (LocalSet::Packed(a), LocalSet::Packed(b)) = (pair.a, pair.b)
    {
      return LocalSet::Packed(a.iter().zip(b).map(|(a, b)| a | b).collect());
    }
    let ids = match (pair.a, pair.b) {
      (LocalSet::Listed(a), LocalSet::Listed(b)) => Merged { a, b }.collect(),
      _ => self.union(pair).collect(),
    };
    // Duplicate/overlapping or out-of-vocabulary choices remain listed.
    self.pack(ids)
  }

  fn add(&self, tb: &mut LocalTable, e: (i128, LocalSet)) {
    let k = e.1.len();
    if tb.len() <= k {
      tb.resize(k + 1, None);
    }
    if tb[k]
      .as_ref()
      .is_none_or(|(d, s)| e.0 < *d || (e.0 == *d && self.prec(&e.1, s)))
    {
      tb[k] = Some(e);
    }
  }

  fn best(tb: &LocalTable) -> Option<i128> {
    tb.iter().flatten().map(|(d, _)| *d).min()
  }

  fn trim(tb: LocalTable, slack: i128) -> LocalTable {
    match Self::best(&tb) {
      None => tb,
      Some(b) => {
        tb.into_iter().map(|e| e.filter(|(d, _)| *d <= b + slack)).collect()
      },
    }
  }

  fn conv(&self, a: &LocalTable, b: &LocalTable) -> LocalTable {
    let mut out: Vec<Option<(i128, LocalPair<'_>)>> = Vec::new();
    for (da, sa) in a.iter().flatten() {
      for (db, sb) in b.iter().flatten() {
        let delta = da + db;
        let k = sa.len() + sb.len();
        if out.len() <= k {
          out.resize(k + 1, None);
        }
        let pair = self.pair(sa, sb);
        if out[k].is_none_or(|(d, old)| {
          delta < d || (delta == d && self.pair_prec(pair, old))
        }) {
          out[k] = Some((delta, pair));
        }
      }
    }
    out.into_iter().map(|e| e.map(|(d, p)| (d, self.materialize(p)))).collect()
  }

  fn decode(&self, tb: LocalTable) -> CTable {
    tb.into_iter()
      .map(|e| {
        e.map(|(d, set)| {
          let ids = match set {
            LocalSet::Listed(ids) => ids,
            set => self.iter(&set).collect(),
          };
          (d, ids)
        })
      })
      .collect()
  }
}

/// The undecided member to branch on: the largest `|gain|`, then the
/// smaller ID.
fn pick_branch(gains: &[(TermId, i128)]) -> Option<(TermId, i128)> {
  let mut acc: Option<(TermId, i128)> = None;
  for &(t, g) in gains {
    acc = match acc {
      None => Some((t, g)),
      Some((a, ga)) => {
        if g.unsigned_abs() > ga.unsigned_abs()
          || (g.unsigned_abs() == ga.unsigned_abs() && t < a)
        {
          Some((t, g))
        } else {
          acc
        }
      },
    };
  }
  acc
}

/// Area position of no term (`SCtx::pos`).
const NO_POS: usize = usize::MAX;

/// Bounds of the area under a maybe-stored predicate, over the root-level
/// bounds (Lean `SCtx.rebound`): `vals[j]` for the area term at position
/// `j`, the root-level bounds elsewhere.
struct Overlay<'b> {
  base: &'b Bounds,
  pos: &'b [usize],
  vals: Vec<[u128; 4]>,
}

impl Overlay<'_> {
  fn get(&self, t: TermId) -> [u128; 4] {
    match self.pos[ix(t)] {
      NO_POS => {
        let k = ix(t);
        [
          self.base.inl[k],
          self.base.merged[k],
          self.base.head_lb[k],
          self.base.cont_lb[k],
        ]
      },
      j => self.vals[j],
    }
  }

  /// The `i`-th bound of `t`, as [`Overlay::get`].
  fn bound(&self, t: TermId, i: usize) -> &u128 {
    match self.pos[ix(t)] {
      NO_POS => {
        let k = ix(t);
        match i {
          0 => &self.base.inl[k],
          1 => &self.base.merged[k],
          2 => &self.base.head_lb[k],
          _ => &self.base.cont_lb[k],
        }
      },
      j => &self.vals[j][i],
    }
  }
}

/// The search of one component (Lean `SCtx`). Sets of decided members are
/// passed as sorted term lists and, inside one call, as flags over the area
/// positions (every member is in the area; a term outside the area is in
/// none of them).
struct SCtx<'a, 'd> {
  up: &'a UPrep<'d>,
  facts: &'a Facts,
  cand: &'a [bool],
  b0: &'a Bounds,
  vis0: &'a (Vec<u128>, Vec<u128>),
  spine_len: &'a [u64],
  dag_size: usize,
  members: Vec<TermId>,
  /// Member index of each area position (`NO_POS` for other terms).
  member_of: Vec<usize>,
  area: Vec<TermId>,
  /// Area position of every term of the DAG (`NO_POS` outside the area).
  pos: &'a [usize],
  /// Per area node: `(parent, its area position, edges, head edges)` per
  /// distinct parent.
  in_edges: Vec<Vec<(TermId, usize, u64, u64)>>,
  root_occ: Vec<u64>,
  root_mult: Vec<(TermId, u128)>,
  stored_in: Vec<TermId>,
  slack: i128,
  theta: i128,
  /// At most eight words per packed choice; None retains listed choices.
  set_words: Option<usize>,
  // Completed group tables are immutable; memo hits share their per-count
  // choices instead of cloning every selected-term vector.
  memo: FxHashMap<Vec<usize>, Arc<LocalTable>>,
  memo_hits: u64,
  /// Scratch of `phi`: the value of each area term.
  vals: Vec<UVal>,
}

impl SCtx<'_, '_> {
  fn sets(&self) -> ComponentSets<'_> {
    ComponentSets { members: &self.members, words: self.set_words }
  }

  fn at(&self, t: TermId) -> Option<usize> {
    match self.pos.get(ix(t)).copied()? {
      NO_POS => None,
      j => Some(j),
    }
  }

  /// Flags over the area positions of the terms `ts`.
  fn flags(&self, ts: &[TermId]) -> Vec<bool> {
    let mut f = vec![false; self.area.len()];
    for &t in ts {
      if let Some(j) = self.at(t) {
        f[j] = true;
      }
    }
    f
  }

  /// The component cost with the area terms flagged in `avail` available
  /// and the entries of `stored`, and the evaluation work (Lean
  /// `SCtx.phi`). Every area term is evaluated, children first; other terms
  /// keep their root-level values.
  fn phi(
    &mut self,
    avail: &[bool],
    stored: &[TermId],
  ) -> Result<(u128, u64), SharingError> {
    let mut work = 0u64;
    for k in 0..self.area.len() {
      let t = self.area[k];
      let (v, s) = {
        let (vals, base, pos) = (&self.vals, &self.up.base, self.pos);
        let get = |c: TermId| match pos[ix(c)] {
          NO_POS => &base[ix(c)],
          j => &vals[j],
        };
        let av = |c: TermId| match pos[ix(c)] {
          NO_POS => false,
          j => avail[j],
        };
        self.up.node(&get, &av, t)?
      };
      self.vals[k] = v;
      work = work.saturating_add(1 + s);
    }
    let get = |c: TermId| match self.pos[ix(c)] {
      NO_POS => &self.up.base[ix(c)],
      j => &self.vals[j],
    };
    let mut total = 0u128;
    for &(r, m) in &self.root_mult {
      total = total.saturating_add(m.saturating_mul(get(r).cost));
    }
    for &c in self.stored_in.iter().chain(stored) {
      total = total.saturating_add(get(c).inl);
    }
    if total == u128::MAX {
      return Err(overflow());
    }
    Ok((total, work))
  }

  fn charge(meter: &mut Meter<'_>, work: u64) -> Result<(), SharingError> {
    meter.state()?;
    meter.work(work)
  }

  /// Whether `t` may be stored: a candidate not decided "not stored".
  fn maybe(&self, out: &[bool], t: TermId) -> bool {
    self.cand[ix(t)] && self.at(t).is_none_or(|j| !out[j])
  }

  fn rebound(&self, out: &[bool]) -> Result<Overlay<'_>, SharingError> {
    let mut ov = Overlay {
      base: self.b0,
      pos: self.pos,
      vals: Vec::with_capacity(self.area.len()),
    };
    for (j, &t) in self.area.iter().enumerate() {
      let v = {
        let ovr = &ov;
        bound_step::<Fast>(
          self.up.nodes,
          t,
          &self.up.w,
          self.cand[ix(t)] && !out[j],
          &|c| ovr.bound(c, 2),
          &|c| ovr.bound(c, 3),
        )?
      };
      ov.vals.push(v);
    }
    Ok(ov)
  }

  /// Visible counts of the area terms (by area position).
  fn revisible(&self, out: &[bool]) -> Vec<(u128, u128)> {
    let mut vis: Vec<(u128, u128)> = vec![(0, 0); self.area.len()];
    for j in (0..self.area.len()).rev() {
      let r = u128::from(self.root_occ[j]);
      let (mut d, mut h) = (r, r);
      for &(q, qj, ma, mh) in &self.in_edges[j] {
        let wq = if self.maybe(out, q) {
          1
        } else {
          match qj {
            NO_POS => self.vis0.0[ix(q)],
            qj => vis[qj].0,
          }
          .min(VISIBLE_CAP)
        };
        d = d.saturating_add(u128::from(ma).saturating_mul(wq));
        h = h.saturating_add(u128::from(mh).saturating_mul(wq));
      }
      vis[j] = (d, h);
    }
    vis
  }

  fn opaque_under(&self, b: &Overlay<'_>, t: TermId) -> bool {
    let v = b.get(t);
    if self.up.nodes[ix(t)].family().is_none() {
      v[0] >= self.up.w
    } else {
      v[1] >= self.up.w
    }
  }

  /// Groups of the undecided members (Lean `SCtx.groups`); `opq` and
  /// `avail_fixed` are flags over the area positions.
  fn groups(
    &self,
    opq: &[bool],
    avail_fixed: &[bool],
    und: &[TermId],
  ) -> Vec<Vec<TermId>> {
    let und_f = self.flags(und);
    let mut uf: Vec<usize> = (0..self.members.len()).collect();
    let mut reps: Vec<Vec<usize>> = vec![Vec::new(); self.area.len()];
    let union = |uf: &mut Vec<usize>, x: usize, y: usize| {
      let a = uf_find(uf, x);
      let b = uf_find(uf, y);
      if a != b {
        if a < b {
          uf[b] = a;
        } else {
          uf[a] = b;
        }
      }
    };
    let member = |j: usize| match self.member_of[j] {
      NO_POS => 0,
      m => m,
    };
    for j in 0..self.area.len() {
      let y = self.area[j];
      if opq[j] {
        continue;
      }
      let mut rs: Vec<usize> = Vec::new();
      for &c in self.up.nodes[ix(y)].children().as_slice() {
        if let Some(jc) = self.at(c) {
          for &r in &reps[jc] {
            let fr = uf_find(&uf, r);
            if !rs.contains(&fr) {
              rs.push(fr);
            }
          }
        }
      }
      if und_f[j] {
        let iy = member(j);
        for &r in &rs {
          union(&mut uf, iy, r);
        }
        reps[j] = vec![uf_find(&uf, iy)];
      } else if avail_fixed[j] && rs.len() > 1 {
        let r0 = rs[0];
        for &r in &rs {
          union(&mut uf, r0, r);
        }
        reps[j] = vec![uf_find(&uf, r0)];
      } else {
        reps[j] = rs;
      }
    }
    let mut groups: FxHashMap<usize, Vec<TermId>> = FxHashMap::default();
    for &t in und {
      let r = uf_find(&uf, self.at(t).map_or(0, member));
      groups.entry(r).or_default().push(t);
    }
    let mut gs: Vec<Vec<TermId>> = groups
      .into_values()
      .map(|mut g| {
        g.sort_unstable();
        g
      })
      .collect();
    gs.sort_by_key(|g| g[0]);
    gs
  }

  /// Memo key of a group and the decided members that reach it (Lean
  /// `SCtx.memoKey`), and those members as flags over the area positions.
  /// `opq`, `in_f` and `out` are flags over the area positions.
  fn memo_key(
    &self,
    opq: &[bool],
    in_f: &[bool],
    out: &[bool],
    g: &[TermId],
  ) -> (Vec<usize>, Vec<bool>) {
    let code = |q: TermId, j: usize| q * 3 + if opq[j] { 2 } else { 1 };
    let mut entries: Vec<usize> = Vec::new();
    let mut rel = vec![false; self.area.len()];
    let mut down_start: Vec<TermId> = g.to_vec();
    let mut seen = self.flags(g);
    let mut stack: Vec<TermId> = g.to_vec();
    while let Some(y) = stack.pop() {
      for &q in &self.facts.parents[ix(y)] {
        let Some(j) = self.at(q) else { continue };
        if seen[j] {
          continue;
        }
        seen[j] = true;
        if out[j] {
          entries.push(q * 3);
          rel[j] = true;
        } else if in_f[j] {
          entries.push(code(q, j));
          rel[j] = true;
          if !opq[j] {
            down_start.push(q);
          }
        }
        if !opq[j] {
          stack.push(q);
        }
      }
    }
    let mut seen = self.flags(&down_start);
    let mut stack = down_start;
    while let Some(y) = stack.pop() {
      for &c in self.up.nodes[ix(y)].children().as_slice() {
        let Some(j) = self.at(c) else { continue };
        if seen[j] {
          continue;
        }
        seen[j] = true;
        if !rel[j] {
          if out[j] {
            entries.push(c * 3);
            rel[j] = true;
          } else if in_f[j] {
            entries.push(code(c, j));
            rel[j] = true;
          }
        }
        if !opq[j] {
          stack.push(c);
        }
      }
    }
    entries.sort_unstable();
    let mut key: Vec<usize> = g.to_vec();
    key.push(3 * self.dag_size + 3);
    key.extend(entries);
    (key, rel)
  }

  /// Lean `keyContext` and the checks before `solveP`'s memo lookup. Only
  /// the key's context suffix is decoded; the group and separator are not.
  fn key_context(
    &self,
    g: &[TermId],
    entries: &[usize],
    in_f: &[bool],
    out: &[bool],
  ) -> Result<(Vec<TermId>, Vec<TermId>), SharingError> {
    let err =
      || internal("memo key context is not part of the decided context");
    let (mut in_red, mut out_red) = (Vec::new(), Vec::new());
    for &e in entries {
      let t: TermId = e / 3;
      if e % 3 == 0 {
        out_red.push(t);
      } else {
        in_red.push(t);
      }
    }
    let ordered_members = |ts: &[TermId]| {
      ts.windows(2).all(|w| w[0] < w[1])
        && ts
          .iter()
          .all(|&t| self.at(t).is_some_and(|j| self.member_of[j] != NO_POS))
    };
    let has = |set: &[bool], t| self.at(t).is_some_and(|j| set[j]);
    if !ordered_members(g)
      || !ordered_members(&in_red)
      || !ordered_members(&out_red)
      || g.iter().any(|&t| has(in_f, t) || has(out, t))
      || in_red.iter().any(|&t| !has(in_f, t) || has(out, t))
      || out_red.iter().any(|&t| !has(out, t) || has(in_f, t))
    {
      return Err(err());
    }
    Ok((in_red, out_red))
  }

  /// Lean `sepCheckA`: a non-out, non-opaque member must not reach both
  /// the group and other members. Recompute opacity under the reduced
  /// context; a cut inferred from the full context is not sufficient.
  fn sep_check(
    &self,
    g: &[TermId],
    in_red: &[TermId],
    out_red: &[TermId],
  ) -> Result<bool, SharingError> {
    let in_f = self.flags(in_red);
    let out = self.flags(out_red);
    let b = self.rebound(&out)?;
    let opq: Vec<bool> = self
      .area
      .iter()
      .enumerate()
      .map(|(j, &t)| {
        self.up.opaq[ix(t)] || (in_f[j] && self.opaque_under(&b, t))
      })
      .collect();
    // Bit 1: group; bit 2: other member; zero: unlabeled. OR is the
    // reach-label join, and 3 is Lean's mixed label `some none`.
    let mut label = vec![0u8; self.area.len()];
    for (ts, bit) in [(&self.members[..], 2), (g, 1), (in_red, 0), (out_red, 0)]
    {
      for &t in ts {
        let Some(j) = self.at(t) else {
          return Ok(false);
        };
        label[j] = bit;
      }
    }
    let mut reach = vec![0u8; self.area.len()];
    for (j, &t) in self.area.iter().enumerate() {
      let mut r = label[j];
      for &c in self.up.nodes[ix(t)].children().as_slice() {
        if let Some(k) = self.at(c) {
          r |= if opq[k] { label[k] } else { reach[k] };
        }
      }
      reach[j] = r;
    }
    Ok(
      g.iter().all(|&t| {
        self.at(t).is_some_and(|j| self.member_of[j] != NO_POS && label[j] == 1)
      }) && self.members.iter().all(|&t| {
        self.at(t).is_some_and(|j| out[j] || opq[j] || reach[j] != 3)
      }),
    )
  }

  /// Exact table of a group under the decided members outside it (Lean
  /// `SCtx.solve`).
  fn solve(
    &mut self,
    meter: &mut Meter<'_>,
    g: &[TermId],
    in_all: &[TermId],
    out_all: &[TermId],
  ) -> Result<Arc<LocalTable>, SharingError> {
    let out = self.flags(out_all);
    let in_f = self.flags(in_all);
    let key = {
      let b = self.rebound(&out)?;
      let opq: Vec<bool> = self
        .area
        .iter()
        .enumerate()
        .map(|(j, &t)| {
          self.up.opaq[ix(t)] || (in_f[j] && self.opaque_under(&b, t))
        })
        .collect();
      self.memo_key(&opq, &in_f, &out, g).0
    };
    let (in_red, out_red) =
      self.key_context(g, &key[g.len() + 1..], &in_f, &out)?;
    if let Some(tb) = self.memo.get(&key) {
      self.memo_hits += 1;
      return Ok(Arc::clone(tb));
    }
    if !self.sep_check(g, &in_red, &out_red)? {
      return Err(internal("search group is not separated"));
    }
    let (phi0, work) = self.phi(&self.flags(&in_red), &in_red)?;
    Self::charge(meter, work.saturating_add(len64(self.area.len())))?;
    let tb = self.node(
      meter,
      phi0,
      &in_red,
      out_red.clone(),
      out_red.len(),
      Vec::new(),
      g,
      Vec::new(),
    )?;
    let tb = Arc::new(ComponentSets::trim(tb, self.slack));
    self.memo.insert(key, Arc::clone(&tb));
    Ok(tb)
  }

  /// Branch-and-bound node of a group (Lean `SCtx.node`).
  #[allow(clippy::too_many_arguments)]
  fn node(
    &mut self,
    meter: &mut Meter<'_>,
    phi0: u128,
    in_ctx: &[TermId],
    out_all: Vec<TermId>,
    n_out_ctx: usize,
    local_in: Vec<TermId>,
    und: &[TermId],
    mut tb: LocalTable,
  ) -> Result<LocalTable, SharingError> {
    let out = self.flags(&out_all);
    // Reclassify.
    let (gains, opaque_in) = {
      let b = self.rebound(&out)?;
      let vis = self.revisible(&out);
      let mut gains: Vec<(TermId, i128)> = Vec::with_capacity(und.len());
      for &t in und {
        let (d, h) = self
          .at(t)
          .map_or((self.vis0.0[ix(t)], self.vis0.1[ix(t)]), |j| vis[j]);
        let v = b.get(t);
        let gt = stored_gain::<Fast>(
          &self.up.nodes[ix(t)],
          d,
          h,
          self.spine_len[ix(t)],
          &v[0],
          &v[1],
          &self.up.w,
        )?;
        gains.push((t, gt));
      }
      // Opacity of every decided-stored member under these bounds (the
      // forced members included), for the split below.
      let mut opaque_in = vec![false; self.area.len()];
      for &t in in_ctx
        .iter()
        .chain(&local_in)
        .chain(gains.iter().filter(|(_, g)| *g >= self.theta).map(|(t, _)| t))
      {
        if self.opaque_under(&b, t)
          && let Some(j) = self.at(t)
        {
          opaque_in[j] = true;
        }
      }
      (gains, opaque_in)
    };
    let forced: Vec<TermId> =
      gains.iter().filter(|(_, g)| *g >= self.theta).map(|(t, _)| *t).collect();
    let local_in = if forced.is_empty() {
      local_in
    } else {
      merge_sorted(&local_in, &forced)
    };
    let open: Vec<(TermId, i128)> =
      gains.into_iter().filter(|(_, g)| *g < self.theta).collect();
    let und: Vec<TermId> = open.iter().map(|(t, _)| *t).collect();
    let in_all: Vec<TermId> = in_ctx.iter().chain(&local_in).copied().collect();
    let in_f = self.flags(&in_all);
    // Lower bound: every undecided member available, its entry free.
    let mut in_und = self.flags(&und);
    for (a, &b) in in_und.iter_mut().zip(&in_f) {
      *a |= b;
    }
    let (phi, work) = self.phi(&in_und, &in_all)?;
    Self::charge(meter, work.saturating_add(2 * len64(self.area.len())))?;
    let delta = to_i(phi)? - to_i(phi0)?;
    if und.is_empty() {
      let sets = self.sets();
      sets.add(&mut tb, (delta, sets.pack(local_in)));
      return Ok(tb);
    }
    if let Some(bd) = ComponentSets::best(&tb)
      && delta > bd + self.slack
    {
      return Ok(tb);
    }
    // Split into independent groups.
    let opq: Vec<bool> = self
      .area
      .iter()
      .enumerate()
      .map(|(j, &t)| self.up.opaq[ix(t)] || (in_f[j] && opaque_in[j]))
      .collect();
    let avail_fixed: Vec<bool> =
      in_f.iter().zip(&opq).map(|(&i, &o)| i && !o).collect();
    let groups = self.groups(&opq, &avail_fixed, &und);
    let route = if groups.len() > 1 {
      true
    } else if groups.len() == 1 {
      let (_, rel) = self.memo_key(&opq, &in_f, &out, &groups[0]);
      let related = |t: &TermId| self.at(*t).is_some_and(|j| rel[j]);
      local_in.iter().any(|t| !related(t))
        || out_all[n_out_ctx..].iter().any(|t| !related(t))
    } else {
      false
    };
    if route {
      let (phi_none, work) = self.phi(&in_f, &in_all)?;
      Self::charge(meter, work)?;
      let base = to_i(phi_none)? - to_i(phi0)?;
      let mut comb: LocalTable =
        vec![Some((base, self.sets().pack(local_in.clone())))];
      for grp in &groups {
        let sub = self.solve(meter, grp, &in_all, &out_all)?;
        comb = ComponentSets::trim(self.sets().conv(&comb, &sub), self.slack);
      }
      for e in comb.into_iter().flatten() {
        self.sets().add(&mut tb, e);
      }
      return Ok(tb);
    }
    // Branch on the largest |gain|, "stored" first when it is positive.
    let Some((t, gt)) = pick_branch(&open) else {
      return Ok(tb);
    };
    let mut und2 = und.clone();
    if let Some(p) = und2.iter().position(|&x| x == t) {
      und2.remove(p);
    }
    let with_t = merge_sorted(&local_in, &[t]);
    let mut out_t = out_all.clone();
    out_t.push(t);
    if gt > 0 {
      let tb = self
        .node(meter, phi0, in_ctx, out_all, n_out_ctx, with_t, &und2, tb)?;
      self.node(meter, phi0, in_ctx, out_t, n_out_ctx, local_in, &und2, tb)
    } else {
      let tb = self.node(
        meter,
        phi0,
        in_ctx,
        out_t,
        n_out_ctx,
        local_in.clone(),
        &und2,
        tb,
      )?;
      self.node(meter, phi0, in_ctx, out_all, n_out_ctx, with_t, &und2, tb)
    }
  }
}

/// Exact optimization up to decisions; the returned plan builds expressions
/// or describes their shares for the tiered construction's dry run.
pub(crate) fn optimize_uniform_with(
  w: u64,
  dag: &SharingDag,
  prep: &DagPrep,
  meter: &mut Meter<'_>,
) -> Result<(UniformSharingResult, UniformPlan), SharingError> {
  let p = prof::scope(Phase::Classify);
  // Fail closed on a telescope spine of `TELE_SUBADD_END` or more steps,
  // before the search (Lean's `optimizeUniformExpanded`): the reference
  // optimality argument needs subadditive telescope headers. A zero width
  // is refused first, by `initial`.
  if w != 0 && !spines_within_bound(&prep.spine_len) {
    return Err(SharingError::FormatBound(FormatBound::TelescopeSpine {
      bound: TELE_SUBADD_END,
    }));
  }
  let Initial {
    up,
    cand,
    bounds,
    vis0,
    theta,
    cs,
    ce_terms,
    unc,
    low,
    comps,
    slack,
  } = initial::<Fast>(w, dag, prep, meter)?;
  let nodes = dag.nodes();
  let n = nodes.len();
  let facts = &prep.facts;
  let spine_len = &prep.spine_len;
  // Search each component (independent searches; see `Parallelism`).
  let search_area = |members: &Vec<TermId>,
                     area: Vec<TermId>,
                     meter: &mut Meter<'_>,
                     pos: &[usize]|
   -> Result<(Choice, CTable), SharingError> {
    let mut mult: std::collections::BTreeMap<TermId, u128> =
      std::collections::BTreeMap::new();
    for &r in dag.roots() {
      if pos[ix(r)] != NO_POS {
        *mult.entry(r).or_default() += 1;
      }
    }
    let root_mult: Vec<(TermId, u128)> = mult.into_iter().collect();
    let stored_in: Vec<TermId> =
      area.iter().copied().filter(|&t| up.opaq[ix(t)]).collect();
    if meter.limits().uniform_subset_search {
      // The reference: plain subset enumeration.
      let mut cx = CompCtx {
        up: &up,
        members: members.clone(),
        area,
        root_mult,
        stored_in,
        phi0: 0,
        slack,
        vals: vec![UVal::default(); n],
        stamp: vec![0; n],
        epoch: 0,
        avail: vec![false; n],
      };
      let (phi0, _) = cx.phi(&[])?;
      cx.phi0 = phi0;
      return cx.search(meter);
    }
    let mut member_of: Vec<usize> = vec![NO_POS; area.len()];
    for (m, &t) in members.iter().enumerate() {
      let j = pos[ix(t)];
      if j < area.len() {
        member_of[j] = m;
      }
    }
    let in_edges: Vec<Vec<(TermId, usize, u64, u64)>> = area
      .iter()
      .map(|&y| {
        facts.parents[ix(y)]
          .iter()
          .map(|&q| {
            let node = &nodes[ix(q)];
            let (mut ma, mut mh) = (0u64, 0u64);
            for (i, &c) in node.children().as_slice().iter().enumerate() {
              if c == y {
                ma += 1;
                if !continuation_edge(node, i, &nodes[ix(y)]) {
                  mh += 1;
                }
              }
            }
            (q, pos[ix(q)], ma, mh)
          })
          .collect()
      })
      .collect();
    let root_occ: Vec<u64> = area
      .iter()
      .map(|y| {
        root_mult
          .iter()
          .find(|(r, _)| r == y)
          .map_or(0, |(_, m)| u64::try_from(*m).unwrap_or(u64::MAX))
      })
      .collect();
    let area_len = area.len();
    let mut cx = SCtx {
      up: &up,
      facts,
      cand: &cand,
      b0: &bounds,
      vis0: &vis0,
      spine_len,
      dag_size: n,
      members: members.clone(),
      member_of,
      area,
      pos,
      in_edges,
      root_occ,
      root_mult,
      stored_in,
      slack,
      theta,
      set_words: ComponentSets::new(members, true).words,
      memo: FxHashMap::default(),
      memo_hits: 0,
      vals: vec![UVal::default(); area_len],
    };
    let tb = cx.solve(meter, members, &[], &[])?;
    // Only the final component table escapes. Release its memo owners
    // before recovering the owned table expected by the existing API.
    drop(cx);
    let tb = ComponentSets::new(members, true).decode(Arc::unwrap_or_clone(tb));
    let bd = table_best(&tb)
      .ok_or_else(|| internal("component search found no choice"))?;
    let mut best_set: Option<&Vec<TermId>> = None;
    for (d, s) in tb.iter().flatten() {
      if *d == bd && best_set.is_none_or(|a| set_prec(s, a)) {
        best_set = Some(s);
      }
    }
    let bs = best_set
      .cloned()
      .ok_or_else(|| internal("component search found no choice"))?;
    Ok(((bd, bs), tb))
  };
  // `pos` maps every term to its position in the component's area
  // (`NO_POS` outside it); it is set for the area of each component and
  // cleared afterwards, so one buffer serves every component.
  let search_one = |members: &Vec<TermId>,
                    meter: &mut Meter<'_>,
                    pos: &mut [usize],
                    stack: &mut Vec<TermId>|
   -> Result<(Choice, CTable), SharingError> {
    let area = component_area_pos(&up, facts, members, pos, NO_POS, stack);
    let res = search_area(members, area.clone(), meter, pos);
    for &t in &area {
      pos[ix(t)] = NO_POS;
    }
    res
  };
  drop(p);
  let p = prof::scope(Phase::Search);
  let budget = meter.parallel.components;
  let mut results: Vec<(Choice, CTable)> = Vec::with_capacity(comps.len());
  if budget <= 1 {
    let mut pos = vec![NO_POS; n];
    let mut stack = Vec::new();
    for members in &comps {
      results.push(search_one(members, meter, &mut pos, &mut stack)?);
    }
  } else {
    // Each component on its own meter; the counts are added in component
    // order afterwards (`Meter::absorb`), then the results are used in the
    // same order as sequentially.
    let limits = meter.limits();
    let outs = super::super::par::map_ranges(comps.len(), budget, |r| {
      let mut pos = vec![NO_POS; n];
      let mut stack = Vec::new();
      r.map(|j| {
        let mut m = Meter::new(limits);
        let res = search_one(&comps[j], &mut m, &mut pos, &mut stack);
        (res, m.stats)
      })
      .collect()
    });
    for (res, stats) in outs {
      meter.absorb(&stats)?;
      results.push(res?);
    }
  }
  drop(p);
  combine_uniform(
    w,
    dag,
    prep,
    meter,
    Initial {
      up,
      cand,
      bounds,
      vis0,
      theta,
      cs,
      ce_terms,
      unc,
      low,
      comps,
      slack,
    },
    results,
  )
}

#[cfg(test)]
mod convolution_tests {
  use super::*;

  // The previous eager implementation is the complete-table oracle.
  fn eager(a: &CTable, b: &CTable) -> CTable {
    let mut out = CTable::new();
    for (da, sa) in a.iter().flatten() {
      for (db, sb) in b.iter().flatten() {
        table_add(&mut out, (da + db, merge_sorted(sa, sb)));
      }
    }
    out
  }

  #[test]
  fn merged_streams_preserve_duplicates_prefixes_and_exact_ties() {
    let mut lists = vec![Vec::new()];
    for len in 1..=3u32 {
      for mut code in 0..3usize.pow(len) {
        let mut xs = Vec::new();
        for _ in 0..len {
          xs.push(code % 3);
          code /= 3;
        }
        xs.sort_unstable();
        if !lists.contains(&xs) {
          lists.push(xs);
        }
      }
    }
    assert_eq!(lists.len(), 20);
    let pairs: Vec<_> = lists
      .iter()
      .flat_map(|a| {
        lists
          .iter()
          .map(move |b| (a.as_slice(), b.as_slice(), merge_sorted(a, b)))
      })
      .collect();
    for (a, b, expected) in &pairs {
      let mut merged = Merged { a, b };
      for (i, &t) in expected.iter().enumerate() {
        assert_eq!(merged.len(), expected.len() - i);
        assert_eq!(merged.next(), Some(t));
      }
      assert_eq!((merged.len(), merged.next()), (0, None));
      for (c, d, other) in &pairs {
        assert_eq!(
          merged_prec(Merged { a, b }, Merged { a: c, b: d }),
          set_prec(expected, other),
          "{a:?}+{b:?} vs {c:?}+{d:?}"
        );
      }
    }
    // Equal choices must not replace the first winner, even when split differently.
    assert!(!merged_prec(
      Merged { a: &[1], b: &[2] },
      Merged { a: &[], b: &[1, 2] }
    ));
  }

  #[test]
  fn convolution_preserves_complete_sparse_tables_and_actual_counts() {
    let tables = [
      vec![],
      vec![None, None],
      vec![Some((0, vec![])), None, None],
      vec![None, Some((0, vec![1, 1])), None, Some((0, vec![]))],
      vec![
        Some((-1, vec![0, 4])),
        Some((0, vec![1])),
        None,
        Some((-1, vec![4])),
      ],
      vec![Some((0, vec![2])), Some((0, vec![1])), Some((0, vec![1]))],
    ];
    for a in &tables {
      for b in &tables {
        assert_eq!(table_conv(a, b), eager(a, b));
      }
    }
    // Deliberately unrelated row indices and overlapping input sets: count
    // the actual merged multiset, preserve every duplicate and every hole.
    let got = table_conv(
      &vec![Some((0, vec![1, 1]))],
      &vec![Some((0, vec![1, 2])), None],
    );
    assert_eq!(got, vec![None, None, None, None, Some((0, vec![1, 1, 1, 2]))]);
  }

  fn next(seed: &mut u64, n: u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed % n
  }

  fn random_table(seed: &mut u64, parity: Option<TermId>) -> CTable {
    (0..next(seed, 10))
      .map(|_| {
        if next(seed, 4) == 0 {
          return None;
        }
        let mut xs: Vec<_> = (0..next(seed, 9))
          .map(|_| {
            let t = TermId::try_from(next(seed, 12)).unwrap();
            parity.map_or(t, |p| 2 * t + p)
          })
          .collect();
        xs.sort_unstable();
        if parity.is_some() {
          xs.dedup();
        }
        Some((i128::from(next(seed, 5)) - 2, xs))
      })
      .collect()
  }

  #[test]
  fn convolution_matches_eager_random_tables() {
    let mut seed = 0x9E37_79B9_7F4A_7C15;
    for i in 0..1000 {
      // Alternate arbitrary overlapping multisets and disjoint group sets.
      let disjoint = i % 2 == 0;
      let a = random_table(&mut seed, disjoint.then_some(0));
      let b = random_table(&mut seed, disjoint.then_some(1));
      assert_eq!(table_conv(&a, &b), eager(&a, &b), "case {i}: {a:?} {b:?}");
    }
  }
}

#[cfg(test)]
mod compact_choice_tests {
  use super::*;

  fn encode(codec: ComponentSets<'_>, tb: &CTable, mixed: bool) -> LocalTable {
    tb.iter()
      .enumerate()
      .map(|(i, e)| {
        e.as_ref().map(|(d, ids)| {
          let set = if mixed && i % 2 == 1 {
            LocalSet::Listed(ids.clone())
          } else {
            codec.pack(ids.clone())
          };
          (*d, set)
        })
      })
      .collect()
  }

  #[test]
  fn compact_roundtrip_and_ties_cover_word_and_fallback_boundaries() {
    for n in [0, 1, 63, 64, 65, 127, 128, 511, 512, 513] {
      let members: Vec<_> = (0..n).map(|i| 10 + 3 * i).collect();
      let codec = ComponentSets::new(&members, true);
      assert_eq!(codec.words.is_some(), n <= PACKED_MEMBERS);
      let mut cases = vec![
        vec![],
        members.clone(),
        members.iter().step_by(2).copied().collect(),
        members.iter().take(3).copied().collect(),
        members.iter().skip(n.saturating_sub(3)).copied().collect(),
        vec![0],
      ];
      if n != 0 {
        cases.push(vec![members[0], members[0]]);
      }
      for a in &cases {
        let packed = codec.pack(a.clone());
        assert_eq!(packed.len(), a.len());
        assert_eq!(codec.iter(&packed).collect::<Vec<_>>(), *a);
        let eligible = n <= PACKED_MEMBERS
          && a.windows(2).all(|w| w[0] < w[1])
          && a.iter().all(|t| members.binary_search(t).is_ok());
        assert_eq!(matches!(packed, LocalSet::Packed(_)), eligible);
        for b in &cases {
          let bp = codec.pack(b.clone());
          let al = LocalSet::Listed(a.clone());
          let bl = LocalSet::Listed(b.clone());
          for (x, y) in [(&packed, &bp), (&packed, &bl), (&al, &bp), (&al, &bl)]
          {
            assert_eq!(codec.prec(x, y), set_prec(a, b));
            let union = codec.materialize(codec.pair(x, y));
            assert_eq!(union.len(), a.len() + b.len());
            assert_eq!(
              codec.iter(&union).collect::<Vec<_>>(),
              merge_sorted(a, b)
            );
          }
        }
      }
      if n != 0 && n <= PACKED_MEMBERS {
        let one = codec.pack(vec![members[0]]);
        let pair = codec.pair(&one, &one);
        assert!(!pair.packed, "overlap must preserve multiplicity");
        assert_eq!(
          codec.materialize(pair),
          LocalSet::Listed(vec![members[0]; 2])
        );
      }
    }
    for members in [vec![2, 1], vec![1, 1]] {
      let codec = ComponentSets::new(&members, true);
      assert!(codec.words.is_none());
      assert_eq!(codec.pack(vec![1, 2]), LocalSet::Listed(vec![1, 2]));
    }
  }

  #[test]
  fn compact_pairs_match_all_stream_ties_and_equal_choices() {
    let members = [3, 6, 9, 12, 15, 18, 21, 24, 27];
    let codec = ComponentSets::new(&members, true);
    let cases = [
      vec![],
      vec![3],
      vec![6],
      vec![3, 6],
      vec![6, 9],
      vec![3, 3],
      vec![0, 6],
    ];
    let sets: Vec<_> = cases
      .iter()
      .flat_map(|s| [codec.pack(s.clone()), LocalSet::Listed(s.clone())])
      .collect();
    for a in &sets {
      for b in &sets {
        for c in &sets {
          for d in &sets {
            let p = codec.pair(a, b);
            let q = codec.pair(c, d);
            let expected_p = codec.union(p).collect::<Vec<_>>();
            let expected_q = codec.union(q).collect::<Vec<_>>();
            assert_eq!(
              codec.pair_prec(p, q),
              set_prec(&expected_p, &expected_q)
            );
          }
        }
      }
    }
  }

  fn next(seed: &mut u64, n: usize) -> usize {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    usize::try_from(*seed % len64(n)).unwrap()
  }

  fn table(seed: &mut u64, members: &[TermId], unique: bool) -> CTable {
    (0..next(seed, 9))
      .map(|_| {
        if next(seed, 4) == 0 {
          return None;
        }
        let mut ids: Vec<_> = (0..next(seed, 12))
          .map(|_| {
            let i = next(seed, members.len() + 2);
            members.get(i).copied().unwrap_or(1_000_000 + i)
          })
          .collect();
        ids.sort_unstable();
        if unique {
          ids.dedup();
        }
        Some((i128::try_from(next(seed, 5)).unwrap() - 2, ids))
      })
      .collect()
  }

  #[test]
  fn compact_tables_match_complete_listed_results() {
    let mut seed = 0x9E37_79B9_7F4A_7C15;
    for n in [0, 1, 63, 64, 65, 511, 512, 513] {
      let members: Vec<_> = (0..n).map(|i| 17 + 5 * i).collect();
      for i in 0..100 {
        let a = table(&mut seed, &members, i % 2 == 0);
        let b = table(&mut seed, &members, i % 2 == 0);
        let expected = table_conv(&a, &b);
        for enabled in [false, true] {
          let codec = ComponentSets::new(&members, enabled);
          for mixed in [false, true] {
            let local =
              codec.conv(&encode(codec, &a, mixed), &encode(codec, &b, mixed));
            assert_eq!(codec.decode(local.clone()), expected, "n={n} case={i}");
            for slack in [0, 1, 2] {
              assert_eq!(
                codec.decode(ComponentSets::trim(local.clone(), slack)),
                table_trim(expected.clone(), slack)
              );
            }
          }
        }
      }
    }
  }

  #[test]
  fn compact_and_forced_listed_search_have_identical_tables_and_counters() {
    let mut results = Vec::new();
    for packed in [false, true] {
      context_tests::with_context(1, |cx, parent| {
        if !packed {
          cx.set_words = None;
        }
        let limits = ExactSharingLimits::default();
        let mut meter = Meter::new(&limits);
        let table = cx.solve(&mut meter, &[0, 1], &[2, parent], &[3]).unwrap();
        results.push((cx.sets().decode(table.as_ref().clone()), meter.stats));
      });
    }
    assert_eq!(results[0], results[1]);
    eprintln!(
      "choice metadata: listed cell={}B local cell={}B; target packed payload=5*8B; vector capacity/hash/allocator overhead is additional",
      size_of::<Option<Choice>>(),
      size_of::<Option<(i128, LocalSet)>>()
    );
  }
}

#[cfg(test)]
mod context_tests {
  use super::*;

  // Four candidate leaves under one candidate App ancestor. The two
  // intermediate App prefixes have compact in-degree one, hence are not
  // candidates. Storing the ancestor separates the leaves.
  pub(super) fn with_context(
    w: u128,
    test: impl FnOnce(&mut SCtx<'_, '_>, TermId),
  ) {
    let leaves: Vec<_> = (0..4).map(|i| Expr::reference(i, vec![0])).collect();
    let parent = leaves[1..]
      .iter()
      .fold(leaves[0].clone(), |f, x| Expr::app(f, x.clone()));
    let mut roots = vec![parent.clone(), parent];
    roots.extend(leaves);
    let dag =
      SharingDag::from_expanded_roots(&roots, &ExactSharingLimits::default())
        .unwrap();
    let nodes = dag.nodes();
    let n = nodes.len();
    let facts = graph_facts(&dag);
    let cand: Vec<bool> = facts.deg.iter().map(|&d| d >= 2).collect();
    let members: Vec<_> = (0..n).filter(|&t| cand[t]).collect();
    let up = UPrep::<Fast>::new(nodes, w, vec![false; n]).unwrap();
    let b0 = uniform_bounds::<Fast>(nodes, &w, &cand).unwrap();
    let vis0 = visible_counts(&dag, &cand);
    let (spine_len, _) = spine_tables(nodes, &vec![false; n]);
    let pos: Vec<_> = (0..n).collect();
    let mut member_of = vec![NO_POS; n];
    for (i, &t) in members.iter().enumerate() {
      member_of[ix(t)] = i;
    }
    let in_edges = (0..n)
      .map(|y| {
        facts.parents[y]
          .iter()
          .map(|&q| {
            let p = &nodes[ix(q)];
            let edge =
              p.children().as_slice().iter().position(|&c| ix(c) == y).unwrap();
            (q, q, 1, u64::from(!continuation_edge(p, edge, &nodes[y])))
          })
          .collect()
      })
      .collect();
    let mut root_occ = vec![0; n];
    for &r in dag.roots() {
      root_occ[ix(r)] += 1;
    }
    let root_mult = root_occ
      .iter()
      .enumerate()
      .filter(|(_, m)| **m != 0)
      .map(|(t, &m)| (t, u128::from(m)))
      .collect();
    let set_words = ComponentSets::new(&members, true).words;
    let mut cx = SCtx {
      up: &up,
      facts: &facts,
      cand: &cand,
      b0: &b0,
      vis0: &vis0,
      spine_len: &spine_len,
      dag_size: n,
      members,
      member_of,
      area: pos.clone(),
      pos: &pos,
      in_edges,
      root_occ,
      root_mult,
      stored_in: vec![],
      slack: 1,
      theta: 2,
      set_words,
      memo: FxHashMap::default(),
      memo_hits: 0,
      vals: vec![UVal::default(); n],
    };
    test(&mut cx, dag.roots()[0]);
  }

  #[test]
  fn reduced_context_keeps_all_counts_ties_and_memo_replay() {
    with_context(1, |cx, parent| {
      let group = [0, 1];
      let in_all = [2, parent];
      let out_all = [3];
      let in_f = cx.flags(&in_all);
      let out = cx.flags(&out_all);
      let b = cx.rebound(&out).unwrap();
      let opq: Vec<_> = cx
        .area
        .iter()
        .enumerate()
        .map(|(j, &t)| in_f[j] && cx.opaque_under(&b, t))
        .collect();
      let key = cx.memo_key(&opq, &in_f, &out, &group).0;
      let (in_red, out_red) =
        cx.key_context(&group, &key[group.len() + 1..], &in_f, &out).unwrap();
      assert_eq!((&in_red, &out_red), (&vec![parent], &vec![]));
      assert!(in_red.len() < in_all.len() && out_red.len() < out_all.len());
      let base_full = cx.phi(&in_f, &in_all).unwrap().0;
      let base_red = cx.phi(&cx.flags(&in_red), &in_red).unwrap().0;
      let mut reference = CTable::new();
      for mask in 0..4 {
        let chosen: Vec<_> = group
          .iter()
          .enumerate()
          .filter(|(i, _)| mask & (1 << i) != 0)
          .map(|(_, &t)| t)
          .collect();
        let full = merge_sorted(&in_all, &chosen);
        let red = merge_sorted(&in_red, &chosen);
        let df = to_i(cx.phi(&cx.flags(&full), &full).unwrap().0).unwrap()
          - to_i(base_full).unwrap();
        let dr = to_i(cx.phi(&cx.flags(&red), &red).unwrap().0).unwrap()
          - to_i(base_red).unwrap();
        assert_eq!(df, dr, "subset {chosen:?}");
        table_add(&mut reference, (dr, chosen));
      }
      let reference = table_trim(reference, cx.slack);
      assert!(reference.iter().flatten().count() >= 2);
      assert_eq!(
        reference[1].as_ref().unwrap().1,
        vec![1],
        "canonical one-member tie"
      );
      let limits = ExactSharingLimits::default();
      let mut meter = Meter::new(&limits);
      let got = cx.solve(&mut meter, &group, &in_all, &out_all).unwrap();
      let decoded = cx.sets().decode(got.as_ref().clone());
      assert_eq!(
        decoded.iter().flatten().collect::<Vec<_>>(),
        reference.iter().flatten().collect::<Vec<_>>()
      );
      let (hits, states) = (cx.memo_hits, meter.stats.states_created);
      let replay = cx.solve(&mut meter, &group, &[parent], &[2, 3]).unwrap();
      assert_eq!(got, replay);
      assert_eq!(
        (cx.memo_hits, meter.stats.states_created),
        (hits + 1, states)
      );
    });
  }

  #[test]
  fn reduced_context_rejects_mixed_reach_and_bad_keys() {
    with_context(1, |cx, parent| {
      assert!(cx.sep_check(&[0, 1], &[parent], &[]).unwrap());
      assert!(cx.sep_check(&[0, 1], &[], &[parent]).unwrap());
      assert!(!cx.sep_check(&[0, 1], &[], &[]).unwrap());
      assert!(!cx.sep_check(&[0, 1], &[0, parent], &[]).unwrap());
      let inside = cx.flags(&[parent]);
      let outside = cx.flags(&[]);
      for (group, entries) in [
        (vec![0, 0], vec![]),
        (vec![0], vec![3 * parent + 2; 2]),
        (vec![0], vec![3 * parent]),
        (vec![0], vec![3 * (TermId::MAX / 3 - 1) + 2]),
        (vec![parent], vec![]),
      ] {
        assert!(cx.key_context(&group, &entries, &inside, &outside).is_err());
      }
      let limits = ExactSharingLimits::default();
      assert!(matches!(cx.solve(&mut Meter::new(&limits), &[0, 1], &[], &[]),
        Err(SharingError::Internal(msg)) if msg == "search group is not separated"));
    });
    with_context(100, |cx, parent| {
      // A stored term is not necessarily opaque: recheck under the actual
      // reduced bounds instead of trusting an encoded opaque tag.
      assert!(!cx.sep_check(&[0, 1], &[parent], &[]).unwrap());
    });
  }
}
