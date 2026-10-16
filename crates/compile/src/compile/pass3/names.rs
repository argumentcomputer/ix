//! Pass 3: the reserved names. A port of `Ix/Compile/Pass/Names.lean`,
//! the naming contract of the faithful rewrite.
//!
//! * `_ix` is the reserved component: a Lean input name with a component that
//!   is `_ix` or starts with `_ix` is refused, and so is an input constant
//!   with a metadata key that has such a component (`compile_env` checks both
//!   before compiling, naming the least message, as the Lean IO pipeline
//!   does).
//! * The Ix auxiliaries of a changed block are displayed as `x._ix.S` for the
//!   Lean name `x.S`; a nested auxiliary by its canonical position
//!   (`rep0._ix.rec_i`).
//! * The decompile record of a rewritten call site is the metadata key pair
//!   `_ix.inline` / `_ix.inline_meta`.
//!
//! The name-component helpers ([`Comp`], [`comps`], [`append_comps`],
//! [`strip_prefix`]) compare names by their components, never by a stored
//! hash.

use ix_common::env::{ConstantInfo, Name, NameData};

use bignat::Nat;

/// The reserved component.
pub const IX_COMPONENT: &str = "_ix";

pub fn mk_str(p: &Name, s: &str) -> Name {
  Name::str(p.clone(), s.to_string())
}

pub fn root_name(s: &str) -> Name {
  Name::str(Name::anon(), s.to_string())
}

/// A name component.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Comp {
  S(String),
  N(Nat),
}

/// The components of a name, outermost first.
pub fn comps(n: &Name) -> Vec<Comp> {
  let mut out = Vec::new();
  let mut cur = n.clone();
  loop {
    let next = match cur.as_data() {
      NameData::Anonymous(_) => break,
      NameData::Str(p, s, _) => {
        out.push(Comp::S(s.clone()));
        p.clone()
      },
      NameData::Num(p, k, _) => {
        out.push(Comp::N(k.clone()));
        p.clone()
      },
    };
    cur = next;
  }
  out.reverse();
  out
}

/// Append components to a name.
pub fn append_comps(n: &Name, cs: &[Comp]) -> Name {
  let mut out = n.clone();
  for c in cs {
    out = match c {
      Comp::S(s) => Name::str(out, s.clone()),
      Comp::N(k) => Name::num(out, k.clone()),
    };
  }
  out
}

/// `x ++ cs` with `x`'s components a prefix of `n`'s: the rest.
pub fn strip_prefix(x: &Name, n: &Name) -> Option<Vec<Comp>> {
  let xs = comps(x);
  let ns = comps(n);
  if xs.len() <= ns.len() && ns[..xs.len()] == xs[..] {
    Some(ns[xs.len()..].to_vec())
  } else {
    None
  }
}

/// A component that is reserved: `_ix` or any string starting with it.
pub fn is_reserved_component(s: &str) -> bool {
  s.starts_with(IX_COMPONENT)
}

/// Some component of `n` is reserved.
pub fn has_reserved(n: &Name) -> bool {
  let mut cur = n.clone();
  loop {
    let next = match cur.as_data() {
      NameData::Anonymous(_) => return false,
      NameData::Str(p, s, _) => {
        if is_reserved_component(s) {
          return true;
        }
        p.clone()
      },
      NameData::Num(p, _, _) => p.clone(),
    };
    cur = next;
  }
}

/// The rejection message of a Lean input name with a reserved component.
pub fn reserved_input(n: &Name) -> Option<String> {
  if has_reserved(n) {
    Some(format!(
      "input name '{}' contains the reserved component `_ix` \
(`_ix` names the Ix auxiliaries and images of the faithful rewrite)",
      n.pretty()
    ))
  } else {
    None
  }
}

/// The least rejection message (by its text) over `names`, as the Lean IO
/// pipeline names it (`Ix.CompileM.reservedInputRefusal?`): with several
/// reserved names both compilers name the same one.
pub fn reserved_input_in<'a>(
  names: impl Iterator<Item = &'a Name>,
) -> Option<String> {
  names.filter_map(reserved_input).min()
}

/// The rejection message of a Lean input constant with a metadata key that
/// has a reserved component (such a key could stand for the placeholder or
/// decompile record of [`inline_key`]).
pub fn reserved_metadata_input(n: &Name) -> String {
  format!(
    "input constant '{}' has a metadata key with the reserved component `_ix` \
(`_ix` names the Ix auxiliaries and images of the faithful rewrite)",
    n.pretty()
  )
}

/// `_ix.inline`.
pub fn inline_key() -> Name {
  mk_str(&root_name(IX_COMPONENT), "inline")
}

/// `_ix.inline_meta`.
pub fn inline_meta_key() -> Name {
  mk_str(&root_name(IX_COMPONENT), "inline_meta")
}

/// `c._ix`: the canonical form of the Lean constant `c` written by a
/// proof-justified pass (`Names.ixFormName`).
pub fn ix_form_name(c: &Name) -> Name {
  mk_str(c, IX_COMPONENT)
}

/// A nested-index suffix component `kind_j` (`kind` one of `rec`, `below`,
/// `brecOn`, `j >= 1`).
fn nested_comp(c: &Comp) -> Option<(String, usize)> {
  match c {
    Comp::S(x) => ["rec", "below", "brecOn"].iter().find_map(|k| {
      let pre = format!("{k}_");
      let rest = x.strip_prefix(&pre)?;
      // Lean's `String.toNat?` on aux-gen names: plain decimal digits.
      if rest.is_empty() || !rest.bytes().all(|b| b.is_ascii_digit()) {
        return None;
      }
      let j: usize = rest.parse().ok()?;
      if j >= 1 { Some(((*k).to_string(), j)) } else { None }
    }),
    Comp::N(_) => None,
  }
}

/// The display name of an Ix auxiliary of a changed block whose Lean name is
/// `n` (`Names.ixAuxName`).
pub fn ix_aux_name(
  members: &[Name],
  rep0: &Name,
  perm: &[Option<usize>],
  n: &Name,
) -> Option<Name> {
  let mut best: Option<(Name, Vec<Comp>)> = None;
  for x in members {
    if let Some(rest) = strip_prefix(x, n)
      && !rest.is_empty()
    {
      match &best {
        Some((_, r)) => {
          if rest.len() < r.len() {
            best = Some((x.clone(), rest));
          }
        },
        None => best = Some((x.clone(), rest)),
      }
    }
  }
  let (x, rest) = best?;
  if let Some(all0) = members.first()
    && comps(&x) == comps(all0)
    && let Some((c, tl)) = rest.split_first()
    && let Some((k, j)) = nested_comp(c)
    && let Some(Some(i)) = perm.get(j - 1)
  {
    let mut cs = vec![Comp::S(format!("{k}_{}", i + 1))];
    cs.extend_from_slice(tl);
    return Some(append_comps(&mk_str(rep0, IX_COMPONENT), &cs));
  }
  Some(append_comps(&mk_str(&x, IX_COMPONENT), &rest))
}

/// The Lean auxiliaries of a block that have images (`Names.imageKinds`).
pub fn image_kinds(
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  all: &[Name],
) -> Vec<Name> {
  let Some(all0) = all.first() else { return Vec::new() };
  let (num_nested, rec_block) = match const_of(all0) {
    Some(ConstantInfo::InductInfo(v)) => (
      v.num_nested.to_u64().and_then(|u| usize::try_from(u).ok()).unwrap_or(0),
      v.is_rec,
    ),
    _ => (0, false),
  };
  let is_rec_of_block = |n: &Name| match const_of(n) {
    Some(ConstantInfo::RecInfo(rv)) => rv.all == all,
    _ => false,
  };
  let is_def = |n: &Name| {
    matches!(
      const_of(n),
      Some(ConstantInfo::DefnInfo(_) | ConstantInfo::ThmInfo(_))
    )
  };
  let family = |b: &Name| vec![b.clone(), mk_str(b, "go"), mk_str(b, "eq")];
  let mut out = Vec::new();
  for x in all {
    let r = mk_str(x, "rec");
    if is_rec_of_block(&r) {
      out.push(r);
    }
    for s in ["casesOn", "recOn"] {
      let n = mk_str(x, s);
      if is_def(&n) {
        out.push(n);
      }
    }
    if rec_block {
      let b = mk_str(x, "below");
      if is_def(&b) {
        out.push(b);
      }
      for n in family(&mk_str(x, "brecOn")) {
        if is_def(&n) {
          out.push(n);
        }
      }
    }
  }
  for j in 1..=num_nested {
    let r = mk_str(all0, &format!("rec_{j}"));
    if is_rec_of_block(&r) {
      out.push(r);
    }
    if rec_block {
      let b = mk_str(all0, &format!("below_{j}"));
      if is_def(&b) {
        out.push(b);
      }
      for n in family(&mk_str(all0, &format!("brecOn_{j}"))) {
        if is_def(&n) {
          out.push(n);
        }
      }
    }
  }
  out
}

#[cfg(test)]
mod tests {
  use super::*;

  /// `Ix.Name.fromLeanName` of a dotted ASCII name without numeric parts.
  fn dotted(s: &str) -> Name {
    let mut n = Name::anon();
    for c in s.split('.') {
      n = Name::str(n, c.to_string());
    }
    n
  }

  #[test]
  fn reserved_names() {
    assert!(reserved_input(&dotted("A._ix.rec")).is_some());
    assert!(reserved_input(&dotted("A._ixfoo")).is_some());
    assert!(reserved_input(&dotted("A.ix.rec")).is_none());
    // a valid neighbour: `_i` is not reserved
    assert!(reserved_input(&dotted("A._i")).is_none());
    assert!(has_reserved(&inline_key()));
    assert!(has_reserved(&inline_meta_key()));
    assert_eq!(ix_form_name(&dotted("A")), dotted("A._ix"));
  }

  #[test]
  fn reserved_input_in_names_the_least_message() {
    let names: Vec<Name> =
      (0..40).rev().map(|i| dotted(&format!("R.N{}._ix.v", i + 10))).collect();
    let mut all = vec![dotted("R.a"), dotted("S.c")];
    all.extend(names);
    assert_eq!(
      reserved_input_in(all.iter()),
      reserved_input(&dotted("R.N10._ix.v"))
    );
    assert_eq!(reserved_input_in([dotted("R.a")].iter()), None);
  }

  #[test]
  fn aux_names() {
    let a = dotted("A");
    let b = dotted("B");
    let members = vec![a.clone(), b.clone()];
    assert_eq!(
      ix_aux_name(&members, &b, &[], &dotted("A.rec")),
      Some(dotted("A._ix.rec"))
    );
    assert_eq!(
      ix_aux_name(&members, &b, &[Some(1), Some(0)], &dotted("A.rec_1")),
      Some(dotted("B._ix.rec_2"))
    );
    assert_eq!(
      ix_aux_name(&members, &b, &[None], &dotted("A.rec_1")),
      Some(dotted("A._ix.rec_1"))
    );
    assert_eq!(ix_aux_name(&members, &b, &[], &dotted("C.rec")), None);
  }
}
