//! Pass 3: the call-site rewrite. A port of `Ix/Compile/Pass/Translate.lean`
//! without the optimisation passes: at every full application of an
//! image-kind head the image is inlined (developed at the occurrence's
//! arguments); a bare or partial occurrence keeps the Lean name, which
//! denotes the stored image.
//!
//! Every outermost rewritten occurrence is wrapped in the placeholder
//! `[(_ix.inline, n)]` and the source occurrence is returned as source `n`;
//! the compiler turns the placeholder into the decompile record.

use rustc_hash::FxHashMap;

use bignat::Nat;
use ix_common::env::{ConstantInfo, DataValue, Expr, ExprData, Level, Name};

use super::develop::{DevState, instantiate_with};
use super::expr::{Hash, get_app_fn_args, key, mk_app_n, subst_levels};
use super::names::inline_key;
use super::view::Expansion;

/// The expansion lookup of a rewrite: `None` when the name is not an
/// image-kind head of a changed block.
pub type ExpansionLookup<'a> =
  dyn FnMut(&Name) -> Result<Option<Expansion>, String> + 'a;

/// A recursion bound for one rewrite.
pub const REWRITE_FUEL: usize = 1 << 20;

#[derive(Default)]
pub struct RwState {
  /// The source occurrences, placeholder `i` for entry `i`.
  pub sources: Vec<Expr>,
  /// Rewritten expansions.
  pub exps: FxHashMap<Name, Expansion>,
  /// Rewritten subterms, each entry retaining its input: a hit is confirmed
  /// by raw equality (the key's hash is only its fast path).
  cache: FxHashMap<(Hash, bool), (Expr, Expr)>,
  /// An expansion's value at universe arguments, by the head and the
  /// arguments' hashes, each entry retaining its levels (confirmed raw).
  level_cache: FxHashMap<(Name, Vec<Hash>), (Vec<Level>, Expr)>,
  dev: DevState,
}

impl RwState {
  fn expansion_of(
    &mut self,
    lookup: &mut ExpansionLookup<'_>,
    fuel: usize,
    n: &Name,
  ) -> Result<Option<Expansion>, String> {
    if fuel == 0 {
      return Err("Pass 3 rewrite: recursion bound exhausted".into());
    }
    let fuel = fuel - 1;
    if let Some(x) = self.exps.get(n) {
      return Ok(Some(x.clone()));
    }
    let Some(x) = lookup(n)? else { return Ok(None) };
    let x = if x.needs_rewrite {
      let v = self.rw(lookup, fuel, false, &x.value)?;
      Expansion { value: v, needs_rewrite: false, ..x }
    } else {
      x
    };
    self.exps.insert(n.clone(), x.clone());
    Ok(Some(x))
  }

  /// The value of expansion `x` of head `n` at universe arguments `us`.
  fn at_levels(&mut self, n: &Name, us: &[Level], x: &Expansion) -> Expr {
    let lk = (n.clone(), us.iter().map(|u| *u.get_hash()).collect());
    let hit = self.level_cache.get(&lk).filter(|(ls, _)| {
      ls.len() == us.len()
        && ls.iter().zip(us.iter()).all(|(a, b)| a.same_raw(b))
    });
    match hit {
      Some((_, f)) => f.clone(),
      None => {
        let f = subst_levels(&x.level_params, us, &x.value);
        self.level_cache.insert(lk, (us.to_owned(), f.clone()));
        f
      },
    }
  }

  /// `base(e)`: every occurrence of an image-kind auxiliary rewritten.
  /// `record` is false inside the arguments of a rewritten occurrence and
  /// inside expansions.
  pub fn rw(
    &mut self,
    lookup: &mut ExpansionLookup<'_>,
    fuel: usize,
    record: bool,
    e: &Expr,
  ) -> Result<Expr, String> {
    if fuel == 0 {
      return Err("Pass 3 rewrite: recursion bound exhausted".into());
    }
    let fuel = fuel - 1;
    let ck = (key(e), record);
    if let Some((input, r)) = self.cache.get(&ck)
      && input.same_raw(e)
    {
      return Ok(r.clone());
    }
    let r = match e.as_data() {
      ExprData::App(..) | ExprData::Const(..) => {
        let (h, args) = get_app_fn_args(e);
        match h.as_data() {
          ExprData::Const(n, us, _) => {
            match self.expansion_of(lookup, fuel, n)? {
              Some(x) => {
                let mut args2 = Vec::with_capacity(args.len());
                for a in &args {
                  args2.push(self.rw(lookup, fuel, false, a)?);
                }
                if args.len() < x.arity {
                  // bare or partial: the Lean name denotes the stored image
                  mk_app_n(Expr::cnst(n.clone(), us.clone()), &args2)
                } else {
                  let f = self.at_levels(n, us, &x);
                  let body = instantiate_with(&mut self.dev, &f, &args2)?;
                  if record {
                    let k = self.sources.len();
                    self.sources.push(e.clone());
                    Expr::mdata(
                      vec![(
                        inline_key(),
                        DataValue::OfNat(Nat::from(k as u64)),
                      )],
                      body,
                    )
                  } else {
                    body
                  }
                }
              },
              None => {
                let mut args2 = Vec::with_capacity(args.len());
                for a in &args {
                  args2.push(self.rw(lookup, fuel, record, a)?);
                }
                mk_app_n(h.clone(), &args2)
              },
            }
          },
          _ => {
            let h2 = self.rw(lookup, fuel, record, &h)?;
            let mut args2 = Vec::with_capacity(args.len());
            for a in &args {
              args2.push(self.rw(lookup, fuel, record, a)?);
            }
            mk_app_n(h2, &args2)
          },
        }
      },
      ExprData::Lam(n, t, b, bi, _) => {
        let t2 = self.rw(lookup, fuel, record, t)?;
        let b2 = self.rw(lookup, fuel, record, b)?;
        Expr::lam(n.clone(), t2, b2, bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        let t2 = self.rw(lookup, fuel, record, t)?;
        let b2 = self.rw(lookup, fuel, record, b)?;
        Expr::all(n.clone(), t2, b2, bi.clone())
      },
      ExprData::LetE(n, t, v, b, nd, _) => {
        let t2 = self.rw(lookup, fuel, record, t)?;
        let v2 = self.rw(lookup, fuel, record, v)?;
        let b2 = self.rw(lookup, fuel, record, b)?;
        Expr::letE(n.clone(), t2, v2, b2, *nd)
      },
      ExprData::Proj(s, i, x, _) => {
        let x2 = self.rw(lookup, fuel, record, x)?;
        Expr::proj(s.clone(), i.clone(), x2)
      },
      ExprData::Mdata(md, x, _) => {
        let x2 = self.rw(lookup, fuel, record, x)?;
        Expr::mdata(md.clone(), x2)
      },
      _ => e.clone(),
    };
    self.cache.insert(ck, (e.clone(), r.clone()));
    Ok(r)
  }

  /// Rewrite every expression of a constant (`rewriteConstM`), and whether
  /// one of them changed (compared raw, not by digest).
  pub fn rewrite_const(
    &mut self,
    lookup: &mut ExpansionLookup<'_>,
    ci: &ConstantInfo,
  ) -> Result<(ConstantInfo, bool), String> {
    let mut changed = false;
    let mut go = |st: &mut RwState, e: &Expr| -> Result<Expr, String> {
      let r = st.rw(lookup, REWRITE_FUEL, true, e)?;
      changed |= !r.same_raw(e);
      Ok(r)
    };
    let ci2 = match ci {
      ConstantInfo::AxiomInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        ConstantInfo::AxiomInfo(v)
      },
      ConstantInfo::DefnInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        v.value = go(self, &v.value)?;
        ConstantInfo::DefnInfo(v)
      },
      ConstantInfo::ThmInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        v.value = go(self, &v.value)?;
        ConstantInfo::ThmInfo(v)
      },
      ConstantInfo::OpaqueInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        v.value = go(self, &v.value)?;
        ConstantInfo::OpaqueInfo(v)
      },
      ConstantInfo::QuotInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        ConstantInfo::QuotInfo(v)
      },
      ConstantInfo::InductInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        ConstantInfo::InductInfo(v)
      },
      ConstantInfo::CtorInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        ConstantInfo::CtorInfo(v)
      },
      ConstantInfo::RecInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        let mut rules = Vec::with_capacity(v.rules.len());
        for r in &v.rules {
          let mut r = r.clone();
          r.rhs = go(self, &r.rhs)?;
          rules.push(r);
        }
        v.rules = rules;
        ConstantInfo::RecInfo(v)
      },
    };
    Ok((ci2, changed))
  }
}

/// The result of rewriting one block.
#[derive(Default)]
pub struct BlockRewrite {
  /// The rewritten members that changed.
  pub overlay: Vec<(Name, ConstantInfo)>,
  /// The source occurrences, placeholder `i` for entry `i`.
  pub sources: Vec<Expr>,
}

/// Rewrite the members of one block; placeholder indices are block-unique
/// (`rewriteBlock`).
pub fn rewrite_block(
  lookup: &mut ExpansionLookup<'_>,
  members: &[(Name, ConstantInfo)],
) -> Result<BlockRewrite, String> {
  let mut st = RwState::default();
  let mut overlay = Vec::new();
  for (n, ci) in members {
    let (ci2, changed) = st.rewrite_const(lookup, ci)?;
    if changed {
      overlay.push((n.clone(), ci2));
    }
  }
  Ok(BlockRewrite { overlay, sources: st.sources })
}

/// The value and type of an image constant `a` with every head rewritten,
/// no records (`imageDeclWith`), from a rewrite state carried across the
/// members of an image block.
pub fn image_decl_with(
  st: &mut RwState,
  lookup: &mut ExpansionLookup<'_>,
  a: &Name,
  x: &Expansion,
  ty: &Expr,
) -> Result<(Expr, Expr), String> {
  let value = match st.exps.get(a) {
    Some(e) => e.value.clone(),
    None => {
      if x.needs_rewrite {
        st.rw(lookup, REWRITE_FUEL, false, &x.value)?
      } else {
        x.value.clone()
      }
    },
  };
  let typ = st.rw(lookup, REWRITE_FUEL, false, ty)?;
  st.sources.clear();
  Ok((value, typ))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::root_name;
  use ix_common::env::{AxiomVal, BinderInfo, ConstantVal};

  fn term(s: &str) -> Expr {
    Expr::cnst(root_name(s), vec![])
  }

  /// `head` is an image of arity 1 whose value is `fun x => x`.
  fn head(n: &Name) -> Option<Expansion> {
    (n == &root_name("head")).then(|| Expansion {
      level_params: vec![],
      value: Expr::lam(
        root_name("x"),
        term("T"),
        Expr::bvar(Nat::from(0u64)),
        BinderInfo::Default,
      ),
      arity: 1,
      needs_rewrite: false,
    })
  }

  #[test]
  fn full_application_inlined_and_recorded() {
    let mut st = RwState::default();
    let occ = Expr::app(term("head"), term("a"));
    let e = Expr::app(term("f"), occ.clone());
    let r = st.rw(&mut |n| Ok(head(n)), 16, true, &e).unwrap();
    let placeholder = Expr::mdata(
      vec![(inline_key(), DataValue::OfNat(Nat::from(0u64)))],
      term("a"),
    );
    assert_eq!(r, Expr::app(term("f"), placeholder));
    assert_eq!(st.sources, vec![occ]);
  }

  #[test]
  fn bare_occurrence_keeps_the_lean_name() {
    let mut st = RwState::default();
    let r = st.rw(&mut |n| Ok(head(n)), 16, true, &term("head")).unwrap();
    assert_eq!(r, term("head"));
    assert!(st.sources.is_empty());
  }

  #[test]
  fn block_overlay_holds_the_changed_members_only() {
    let axiom = |n: &str, typ: Expr| {
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal { name: root_name(n), level_params: vec![], typ },
        is_unsafe: false,
      })
    };
    let members = vec![
      (root_name("u"), axiom("u", term("T"))),
      (root_name("c"), axiom("c", Expr::app(term("head"), term("T")))),
    ];
    let rw = rewrite_block(&mut |n| Ok(head(n)), &members).unwrap();
    assert_eq!(rw.overlay.len(), 1);
    assert_eq!(rw.overlay[0].0, root_name("c"));
    assert_eq!(rw.sources.len(), 1);
  }

  #[test]
  fn exhausted_bound_is_an_error() {
    let mut st = RwState::default();
    let e = Expr::app(term("f"), term("a"));
    assert!(st.rw(&mut |n| Ok(head(n)), 1, true, &e).is_err());
  }
}
