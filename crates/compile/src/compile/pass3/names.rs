//! Pass 3: the switch and the reserved names (D14). A port of
//! `Ix/Compile/Pass/Names.lean`, the naming contract of the faithful rewrite.
//!
//! * `IX_PASS3` selects the mode: `images` (Pass 3) or `off` (the legacy
//!   call-site surgery). Rust's default stays the surgery until M6R slice 6;
//!   any other value is refused with the Lean side's text.
//! * `_ix` is the reserved component: a Lean input name with a component that
//!   is `_ix` or starts with `_ix` is rejected under the switch.
//! * The Ix auxiliaries of a changed block are displayed as `x._ix.S` for the
//!   Lean name `x.S`; a nested auxiliary by its canonical position
//!   (`rep0._ix.rec_i`).
//! * The decompile record of a rewritten call site is the metadata key pair
//!   `_ix.inline` / `_ix.inline_meta`.

use bignat::Nat;

use ix_common::env::{ConstantInfo, Name, NameData};

use super::expr::{
  Comp, append_comps, dotted, mk_str, root_name, strip_prefix,
};

/// The environment variable that selects the mode.
pub const SWITCH_VAR: &str = "IX_PASS3";
/// The value that selects Pass 3.
pub const SWITCH_VALUE: &str = "images";
/// The value that selects the legacy surgery.
pub const SWITCH_OFF_VALUE: &str = "off";
/// The mode when `IX_PASS3` is unset: the Rust compiler stays on the surgery
/// until M6R slice 6 (the Lean compiler flips at M6).
pub const SWITCH_DEFAULT: bool = false;

/// The mode a value of `IX_PASS3` selects (`None`: refused).
pub fn switch_mode(v: Option<&str>) -> Option<bool> {
  match v {
    None => Some(SWITCH_DEFAULT),
    Some(v) if v == SWITCH_VALUE => Some(true),
    Some(v) if v == SWITCH_OFF_VALUE => Some(false),
    Some(_) => None,
  }
}

/// The refusal of an unrecognised `IX_PASS3` value, word for word the Lean
/// side's (`Ix.Compile.Pass.switchRefusal`).
pub fn switch_refusal(v: &str) -> String {
  format!(
    "{SWITCH_VAR}={v} is not a mode: use {SWITCH_VALUE} (Pass 3, the default) or \
{SWITCH_OFF_VALUE} (the legacy surgery, the comparison mode against the Rust compiler)"
  )
}

/// The mode `IX_PASS3` selects in this process, or the refusal.
pub fn switch_from_env() -> Result<bool, String> {
  match std::env::var(SWITCH_VAR) {
    Err(std::env::VarError::NotPresent) => Ok(SWITCH_DEFAULT),
    Err(std::env::VarError::NotUnicode(s)) => {
      Err(switch_refusal(&s.to_string_lossy()))
    },
    Ok(v) => switch_mode(Some(&v)).ok_or_else(|| switch_refusal(&v)),
  }
}

/// The reserved component (D14).
pub const IX_COMPONENT: &str = "_ix";

/// The reserved component of a re-typed structural handler.
pub const RETYPED_COMPONENT: &str = "_ix_retyped";

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
(D14: `_ix` names the Ix auxiliaries and images of the faithful rewrite)",
      n.pretty()
    ))
  } else {
    None
  }
}

/// `_ix.inline`.
pub fn inline_key() -> Name {
  mk_str(&root_name(IX_COMPONENT), "inline")
}

/// `_ix.inline_meta`.
pub fn inline_meta_key() -> Name {
  mk_str(&root_name(IX_COMPONENT), "inline_meta")
}

/// `c._ix`: the image name / the canonical form of a proof-justified pass.
pub fn ix_form_name(c: &Name) -> Name {
  mk_str(c, IX_COMPONENT)
}

/// The reserved name of the re-typed handler of the Lean constant `p.s`:
/// `p._ix_retyped.s` (`Names.retypedName`; distinct from the clique hook's
/// `p._ix.s`).
pub fn retyped_name(n: &Name) -> Option<Name> {
  match n.as_data() {
    NameData::Str(p, s, _) => Some(mk_str(&mk_str(p, RETYPED_COMPONENT), s)),
    _ => None,
  }
}

/// A nested-index suffix component `kind_j` (`kind` one of `rec`, `below`,
/// `brecOn`, `j >= 1`).
fn nested_comp(c: &Comp) -> Option<(String, usize)> {
  match c {
    Comp::S(x) => ["rec", "below", "brecOn"].iter().find_map(|k| {
      let pre = format!("{k}_");
      let rest = x.strip_prefix(&pre)?;
      // Lean's `String.toNat?`: decimal digits (underscores allowed between
      // digits are not produced by aux-gen names; plain digits only here).
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
    && x == *all0
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
    Some(ConstantInfo::InductInfo(v)) => {
      (v.num_nested.to_u64().unwrap_or(0) as usize, v.is_rec)
    },
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

// The constants the construction uses.
pub fn n_pprod() -> Name {
  root_name("PProd")
}
pub fn n_pprod_mk() -> Name {
  dotted("PProd.mk")
}
pub fn n_and() -> Name {
  root_name("And")
}
pub fn n_and_intro() -> Name {
  dotted("And.intro")
}
pub fn n_true() -> Name {
  root_name("True")
}
pub fn n_true_intro() -> Name {
  dotted("True.intro")
}

/// `nat` helper for name components.
pub fn name_num(p: &Name, k: usize) -> Name {
  Name::num(p.clone(), Nat::from(k as u64))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn switch_values() {
    assert_eq!(switch_mode(None), Some(false));
    assert_eq!(switch_mode(Some("images")), Some(true));
    assert_eq!(switch_mode(Some("off")), Some(false));
    assert_eq!(switch_mode(Some("on")), None);
    assert!(switch_refusal("on").starts_with("IX_PASS3=on is not a mode"));
  }

  #[test]
  fn reserved_names() {
    assert!(reserved_input(&dotted("A._ix.rec")).is_some());
    assert!(reserved_input(&dotted("A._ixfoo")).is_some());
    assert!(reserved_input(&dotted("A.ix.rec")).is_none());
    // a valid neighbour: `_i` is not reserved
    assert!(reserved_input(&dotted("A._i")).is_none());
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
