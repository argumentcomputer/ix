//! Ordered expression roots of a ConstantInfo and their exact reassembly.
//!
//! The order mirrors Lean's `Ix.CompileM.constantInfoRootExprs` and the Rust
//! compiler's `apply_sharing_to_*` layout: definitions `[type, value]`;
//! axioms and quotients `[type]`; recursors `type` then every rule `rhs`;
//! mutual blocks flatten each member in order (an inductive contributes its
//! type then each constructor type); projections contribute nothing.

use std::sync::Arc;

use super::{MalformedSharing, SharingError};
use crate::constant::{
  ConstantInfo, Constructor, Definition, Inductive, MutConst, Recursor,
  RecursorRule,
};
use crate::expr::Expr;

fn push_mut_const_roots(m: &MutConst, out: &mut Vec<Arc<Expr>>) {
  match m {
    MutConst::Defn(d) => {
      out.push(d.typ.clone());
      out.push(d.value.clone());
    },
    MutConst::Indc(i) => {
      out.push(i.typ.clone());
      out.extend(i.ctors.iter().map(|c| c.typ.clone()));
    },
    MutConst::Recr(r) => push_recursor_roots(r, out),
  }
}

fn push_recursor_roots(r: &Recursor, out: &mut Vec<Arc<Expr>>) {
  out.push(r.typ.clone());
  out.extend(r.rules.iter().map(|rule| rule.rhs.clone()));
}

/// The ordered sharing roots of `info`.
pub fn constant_info_root_exprs(info: &ConstantInfo) -> Vec<Arc<Expr>> {
  let mut out = Vec::new();
  match info {
    ConstantInfo::Defn(d) => {
      out.push(d.typ.clone());
      out.push(d.value.clone());
    },
    ConstantInfo::Recr(r) => push_recursor_roots(r, &mut out),
    ConstantInfo::Axio(a) => out.push(a.typ.clone()),
    ConstantInfo::Quot(q) => out.push(q.typ.clone()),
    ConstantInfo::CPrj(_)
    | ConstantInfo::RPrj(_)
    | ConstantInfo::IPrj(_)
    | ConstantInfo::DPrj(_) => {},
    ConstantInfo::Muts(ms) => {
      for m in ms {
        push_mut_const_roots(m, &mut out);
      }
    },
  }
  out
}

/// Number of roots [`constant_info_root_exprs`] returns, without cloning.
pub fn constant_info_root_count(info: &ConstantInfo) -> usize {
  fn mut_count(m: &MutConst) -> usize {
    match m {
      MutConst::Defn(_) => 2,
      MutConst::Indc(i) => 1 + i.ctors.len(),
      MutConst::Recr(r) => 1 + r.rules.len(),
    }
  }
  match info {
    ConstantInfo::Defn(_) => 2,
    ConstantInfo::Recr(r) => 1 + r.rules.len(),
    ConstantInfo::Axio(_) | ConstantInfo::Quot(_) => 1,
    ConstantInfo::CPrj(_)
    | ConstantInfo::RPrj(_)
    | ConstantInfo::IPrj(_)
    | ConstantInfo::DPrj(_) => 0,
    ConstantInfo::Muts(ms) => ms.iter().map(mut_count).sum(),
  }
}

struct Feed<'a> {
  roots: &'a [Arc<Expr>],
  next: usize,
}

impl Feed<'_> {
  fn take(&mut self) -> Option<Arc<Expr>> {
    let e = self.roots.get(self.next)?.clone();
    self.next += 1;
    Some(e)
  }
}

fn rebuild_definition(
  d: &Definition,
  feed: &mut Feed<'_>,
) -> Option<Definition> {
  Some(Definition {
    kind: d.kind,
    safety: d.safety,
    lvls: d.lvls,
    typ: feed.take()?,
    value: feed.take()?,
  })
}

fn rebuild_recursor(r: &Recursor, feed: &mut Feed<'_>) -> Option<Recursor> {
  let typ = feed.take()?;
  let mut rules = Vec::with_capacity(r.rules.len());
  for rule in &r.rules {
    rules.push(RecursorRule { fields: rule.fields, rhs: feed.take()? });
  }
  Some(Recursor {
    k: r.k,
    is_unsafe: r.is_unsafe,
    lvls: r.lvls,
    params: r.params,
    indices: r.indices,
    motives: r.motives,
    minors: r.minors,
    typ,
    rules,
  })
}

fn rebuild_inductive(i: &Inductive, feed: &mut Feed<'_>) -> Option<Inductive> {
  let typ = feed.take()?;
  let mut ctors = Vec::with_capacity(i.ctors.len());
  for c in &i.ctors {
    ctors.push(Constructor {
      is_unsafe: c.is_unsafe,
      lvls: c.lvls,
      cidx: c.cidx,
      params: c.params,
      fields: c.fields,
      typ: feed.take()?,
    });
  }
  Some(Inductive {
    is_unsafe: i.is_unsafe,
    lvls: i.lvls,
    params: i.params,
    indices: i.indices,
    typ,
    ctors,
  })
}

fn rebuild_with(
  info: &ConstantInfo,
  feed: &mut Feed<'_>,
) -> Option<ConstantInfo> {
  Some(match info {
    ConstantInfo::Defn(d) => ConstantInfo::Defn(rebuild_definition(d, feed)?),
    ConstantInfo::Recr(r) => ConstantInfo::Recr(rebuild_recursor(r, feed)?),
    ConstantInfo::Axio(a) => {
      let mut a = a.clone();
      a.typ = feed.take()?;
      ConstantInfo::Axio(a)
    },
    ConstantInfo::Quot(q) => {
      let mut q = q.clone();
      q.typ = feed.take()?;
      ConstantInfo::Quot(q)
    },
    ConstantInfo::CPrj(_)
    | ConstantInfo::RPrj(_)
    | ConstantInfo::IPrj(_)
    | ConstantInfo::DPrj(_) => info.clone(),
    ConstantInfo::Muts(ms) => {
      let mut out = Vec::with_capacity(ms.len());
      for m in ms {
        out.push(match m {
          MutConst::Defn(d) => MutConst::Defn(rebuild_definition(d, feed)?),
          MutConst::Indc(i) => MutConst::Indc(rebuild_inductive(i, feed)?),
          MutConst::Recr(r) => MutConst::Recr(rebuild_recursor(r, feed)?),
        });
      }
      ConstantInfo::Muts(out)
    },
  })
}

/// Replace the roots of `info`, in [`constant_info_root_exprs`] order, by
/// `roots`. Every non-expression field is kept. Fails unless the rebuild
/// consumes exactly `roots.len()` expressions.
pub fn rebuild_constant_info(
  info: &ConstantInfo,
  roots: &[Arc<Expr>],
) -> Result<ConstantInfo, SharingError> {
  let expected = constant_info_root_count(info);
  let mismatch = || {
    SharingError::Malformed(MalformedSharing::RootCountMismatch {
      expected: u64::try_from(expected).unwrap_or(u64::MAX),
      actual: u64::try_from(roots.len()).unwrap_or(u64::MAX),
    })
  };
  let mut feed = Feed { roots, next: 0 };
  let rebuilt = rebuild_with(info, &mut feed).ok_or_else(mismatch)?;
  if feed.next != roots.len() || expected != roots.len() {
    return Err(mismatch());
  }
  Ok(rebuilt)
}
