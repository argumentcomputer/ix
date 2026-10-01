//! Exact serialized-length helpers for the v3 expression and Constant grammar.
//!
//! Every function here mirrors a writer in `serialize.rs` byte for byte; the
//! tests compare them against the real serializer. Arithmetic is checked:
//! helpers that measure caller data return `None` instead of wrapping.

use std::cmp::Ordering;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::roots::constant_info_root_exprs;
use crate::constant::{
  Constant, ConstantInfo, Constructor, Inductive, MutConst, Recursor,
};
use crate::expr::Expr;
use crate::univ::put_univ;

/// Serialized byte length with an explicit overflow sentinel.
///
/// Values below `u64::MAX` are exact. [`Len::OVERFLOW`] stands for every
/// length `>= u64::MAX`: addition saturates into it, so it compares strictly
/// greater than every exact length and two exact lengths always compare
/// exactly. The optimizer only ever returns exact lengths; an overflowed
/// candidate can lose a comparison but can never be selected.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Len(u64);

impl Len {
  pub const ZERO: Len = Len(0);
  pub const OVERFLOW: Len = Len(u64::MAX);

  /// `v == u64::MAX` is read as [`Len::OVERFLOW`].
  pub const fn new(v: u64) -> Len {
    Len(v)
  }

  #[must_use]
  pub const fn plus(self, other: Len) -> Len {
    Len(self.0.saturating_add(other.0))
  }

  #[must_use]
  pub const fn plus_u64(self, other: u64) -> Len {
    Len(self.0.saturating_add(other))
  }

  pub const fn is_exact(self) -> bool {
    self.0 != u64::MAX
  }

  /// The exact value, or `None` for [`Len::OVERFLOW`].
  pub const fn exact(self) -> Option<u64> {
    if self.0 == u64::MAX { None } else { Some(self.0) }
  }

  /// Raw value; `u64::MAX` is the overflow sentinel.
  pub const fn raw(self) -> u64 {
    self.0
  }
}

/// Minimal little-endian byte count of `x` (0 for 0), as `u64_byte_count`.
pub fn byte_count(x: u64) -> u64 {
  (64 - u64::from(x.leading_zeros())).div_ceil(8)
}

/// Encoded length of `Tag4 { flag, size }` for any flag.
pub fn tag4_len(size: u64) -> u64 {
  if size < 8 { 1 } else { 1 + byte_count(size) }
}

/// Encoded length of `Tag0 { size }`.
pub fn tag0_len(size: u64) -> u64 {
  if size < 128 { 1 } else { 1 + byte_count(size) }
}

/// Byte width of `Expr::Share(index)`.
pub fn share_width(index: u64) -> u64 {
  tag4_len(index)
}

/// The low-nibble part of a Tag4 header followed by its size bytes. The flag
/// nibble is omitted: callers compare headers of one flag only.
fn tag4_size_bytes(size: u64) -> ([u8; 9], usize) {
  let mut out = [0u8; 9];
  if size < 8 {
    out[0] = size.to_le_bytes()[0];
    (out, 1)
  } else {
    let n = usize::try_from(byte_count(size)).unwrap_or(8);
    // n is in 1..=8, so n - 1 fits the three low header bits.
    out[0] = 0b1000 | n.to_le_bytes()[0].wrapping_sub(1);
    out[1..=n].copy_from_slice(&size.to_le_bytes()[..n]);
    (out, n + 1)
  }
}

/// Unsigned lexicographic order of the Tag4 encodings of two sizes under the
/// same flag. Distinct sizes always differ inside the header.
pub(crate) fn tag4_bytes_cmp(a: u64, b: u64) -> Ordering {
  let (xa, na) = tag4_size_bytes(a);
  let (xb, nb) = tag4_size_bytes(b);
  xa[..na].cmp(&xb[..nb])
}

fn usize_u64(n: usize) -> Option<u64> {
  u64::try_from(n).ok()
}

/// Exact `put_expr` length of an expression (Share leaves allowed).
///
/// Iterative, memoized by pointer, so an `Arc` DAG is measured without
/// walking its occurrence tree. Returns `None` if the length overflows.
pub fn expr_len(e: &Expr) -> Option<u64> {
  #[derive(Clone, Copy)]
  struct Info {
    /// Standalone length.
    len: u64,
    /// Telescope count, summed side bytes and tail length when this node
    /// is the top of its App/Lam/All spine.
    count: u64,
    sum: u64,
    tail: u64,
  }
  fn leaf(len: u64) -> Info {
    Info { len, count: 0, sum: 0, tail: 0 }
  }
  let mut memo: FxHashMap<*const Expr, Info> = FxHashMap::default();
  let mut stack: Vec<(&Expr, bool)> = vec![(e, false)];
  while let Some((node, ready)) = stack.pop() {
    let key = std::ptr::from_ref(node);
    if memo.contains_key(&key) {
      continue;
    }
    if !ready && !node.children().is_empty() {
      stack.push((node, true));
      for child in node.children() {
        if !memo.contains_key(&Arc::as_ptr(child)) {
          stack.push((child.as_ref(), false));
        }
      }
      continue;
    }
    let get = |c: &Arc<Expr>| memo[&Arc::as_ptr(c)];
    let info = match node {
      Expr::Sort(n)
      | Expr::Var(n)
      | Expr::Str(n)
      | Expr::Nat(n)
      | Expr::Share(n) => leaf(tag4_len(*n)),
      Expr::Ref(n, us) | Expr::Rec(n, us) => {
        let mut len =
          tag4_len(usize_u64(us.len())?).checked_add(tag0_len(*n))?;
        for u in us {
          len = len.checked_add(tag0_len(*u))?;
        }
        leaf(len)
      },
      Expr::Prj(t, f, v) => {
        leaf(tag4_len(*f).checked_add(tag0_len(*t))?.checked_add(get(v).len)?)
      },
      Expr::Let(c, ty, v, b) => leaf(
        tag4_len(c.flags())
          .checked_add(1)?
          .checked_add(get(ty).len)?
          .checked_add(get(v).len)?
          .checked_add(get(b).len)?,
      ),
      Expr::App(f, a) => {
        let (count, sum, tail) = if matches!(f.as_ref(), Expr::App(..)) {
          let fi = get(f);
          (fi.count.checked_add(1)?, fi.sum.checked_add(get(a).len)?, fi.tail)
        } else {
          (1, get(a).len, get(f).len)
        };
        let len = tag4_len(count).checked_add(sum)?.checked_add(tail)?;
        Info { len, count, sum, tail }
      },
      Expr::Lam(_, ty, b) | Expr::All(_, _, ty, b) => {
        let all = matches!(node, Expr::All(..));
        let same = if all {
          matches!(b.as_ref(), Expr::All(..))
        } else {
          matches!(b.as_ref(), Expr::Lam(..))
        };
        let side = get(ty).len.checked_add(1)?;
        let (count, sum, tail) = if same {
          let bi = get(b);
          (bi.count.checked_add(1)?, bi.sum.checked_add(side)?, bi.tail)
        } else {
          (1, side, get(b).len)
        };
        let len = tag4_len(count).checked_add(sum)?.checked_add(tail)?;
        Info { len, count, sum, tail }
      },
    };
    memo.insert(key, info);
  }
  memo.get(&std::ptr::from_ref(e)).map(|i| i.len)
}

/// Exact length of a sharing table: its Tag0 count plus every entry.
pub fn sharing_table_len(table: &[Arc<Expr>]) -> Option<u64> {
  let mut len = tag0_len(usize_u64(table.len())?);
  for e in table {
    len = len.checked_add(expr_len(e)?)?;
  }
  Some(len)
}

fn definition_fixed(lvls: u64) -> u64 {
  1 + tag0_len(lvls)
}

fn recursor_fixed(r: &Recursor) -> Option<u64> {
  let mut len = 1 + tag0_len(r.lvls);
  for x in [r.params, r.indices, r.motives, r.minors] {
    len = len.checked_add(tag0_len(x))?;
  }
  len = len.checked_add(tag0_len(usize_u64(r.rules.len())?))?;
  for rule in &r.rules {
    len = len.checked_add(tag0_len(rule.fields))?;
  }
  Some(len)
}

fn constructor_fixed(c: &Constructor) -> Option<u64> {
  let mut len = 1u64;
  for x in [c.lvls, c.cidx, c.params, c.fields] {
    len = len.checked_add(tag0_len(x))?;
  }
  Some(len)
}

fn inductive_fixed(i: &Inductive) -> Option<u64> {
  let mut len = 1u64;
  for x in [i.lvls, i.params, i.indices] {
    len = len.checked_add(tag0_len(x))?;
  }
  len = len.checked_add(tag0_len(usize_u64(i.ctors.len())?))?;
  for c in &i.ctors {
    len = len.checked_add(constructor_fixed(c)?)?;
  }
  Some(len)
}

fn mut_const_fixed(m: &MutConst) -> Option<u64> {
  let body = match m {
    MutConst::Defn(d) => definition_fixed(d.lvls),
    MutConst::Indc(i) => inductive_fixed(i)?,
    MutConst::Recr(r) => recursor_fixed(r)?,
  };
  body.checked_add(1)
}

/// Exact length of every byte of `c` except its root expressions (as listed
/// by [`constant_info_root_exprs`]) and its whole sharing table, including
/// the table's Tag0 count.
pub fn constant_fixed_len(c: &Constant) -> Option<u64> {
  let info = match &c.info {
    ConstantInfo::Muts(ms) => {
      let mut len = tag4_len(usize_u64(ms.len())?);
      for m in ms {
        len = len.checked_add(mut_const_fixed(m)?)?;
      }
      len
    },
    other => {
      let header = tag4_len(other.variant()?);
      let body = match other {
        ConstantInfo::Defn(d) => definition_fixed(d.lvls),
        ConstantInfo::Recr(r) => recursor_fixed(r)?,
        ConstantInfo::Axio(a) => definition_fixed(a.lvls),
        ConstantInfo::Quot(q) => definition_fixed(q.lvls),
        ConstantInfo::CPrj(p) => {
          tag0_len(p.idx).checked_add(tag0_len(p.cidx))?.checked_add(32)?
        },
        ConstantInfo::RPrj(p) => tag0_len(p.idx).checked_add(32)?,
        ConstantInfo::IPrj(p) => tag0_len(p.idx).checked_add(32)?,
        ConstantInfo::DPrj(p) => tag0_len(p.idx).checked_add(32)?,
        ConstantInfo::Muts(_) => return None,
      };
      header.checked_add(body)?
    },
  };
  let refs = usize_u64(c.refs.len())?;
  let mut len = info
    .checked_add(tag0_len(refs))?
    .checked_add(refs.checked_mul(32)?)?
    .checked_add(tag0_len(usize_u64(c.univs.len())?))?;
  let mut scratch = Vec::new();
  for u in &c.univs {
    scratch.clear();
    put_univ(u, &mut scratch);
    len = len.checked_add(usize_u64(scratch.len())?)?;
  }
  Some(len)
}

/// Exact `Constant::put` length, decomposed as fixed bytes + roots + table.
pub fn constant_len(c: &Constant) -> Option<u64> {
  let mut len = constant_fixed_len(c)?;
  for root in constant_info_root_exprs(&c.info) {
    len = len.checked_add(expr_len(&root)?)?;
  }
  len.checked_add(sharing_table_len(&c.sharing)?)
}
