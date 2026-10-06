//! Pass 3b: the call-site rewrite (design document §4.5, Def 3.5, Def 3.6).
//! A port of `Ix/Compile/Pass/Translate.lean` for slice 1 of M6R: the
//! optimisation hook (`RwState.opt?`, the definitional passes O1-O6/O11a and
//! the proof-justified passes O7-O12) and the decline hook are absent, so
//! every full application of an image-kind head is inlined from its image
//! (the baseline, Def 3.6), which is exactly the form the Lean driver gives
//! with those passes absent.
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
  cache: FxHashMap<(Hash, bool, Option<Name>), Expr>,
  /// The definition whose value is rewritten (`RwState.site`; read only by
  /// the passes, kept in the cache key as on the Lean side).
  site: Option<Name>,
  level_cache: FxHashMap<(Name, Vec<Hash>), Expr>,
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
      // an expansion is shared by every site: no proof-justified pass
      let site = self.site.take();
      let v = self.rw(lookup, fuel, false, &x.value)?;
      self.site = site;
      Expansion { value: v, needs_rewrite: false, ..x }
    } else {
      x
    };
    self.exps.insert(n.clone(), x.clone());
    Ok(Some(x))
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
    let ck = (key(e), record, self.site.clone());
    if let Some(r) = self.cache.get(&ck) {
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
                  let lk =
                    (n.clone(), us.iter().map(|u| *u.get_hash()).collect());
                  let f = match self.level_cache.get(&lk) {
                    Some(f) => f.clone(),
                    None => {
                      let f = subst_levels(&x.level_params, us, &x.value);
                      self.level_cache.insert(lk, f.clone());
                      f
                    },
                  };
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
    self.cache.insert(ck, r.clone());
    Ok(r)
  }

  /// Rewrite every expression of a constant (`rewriteConstM`).
  pub fn rewrite_const(
    &mut self,
    lookup: &mut ExpansionLookup<'_>,
    ci: &ConstantInfo,
  ) -> Result<ConstantInfo, String> {
    let mut go =
      |st: &mut RwState, e: &Expr| st.rw(lookup, REWRITE_FUEL, true, e);
    Ok(match ci {
      ConstantInfo::AxiomInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        ConstantInfo::AxiomInfo(v)
      },
      ConstantInfo::DefnInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        self.site = Some(v.cnst.name.clone());
        let value = go(self, &v.value);
        self.site = None;
        v.value = value?;
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
    })
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
/// (`rewriteBlock`, no passes).
pub fn rewrite_block(
  lookup: &mut ExpansionLookup<'_>,
  members: &[(Name, ConstantInfo)],
) -> Result<BlockRewrite, String> {
  let mut st = RwState::default();
  let mut overlay = Vec::new();
  for (n, ci) in members {
    let ci2 = st.rewrite_const(lookup, ci)?;
    if ci2.get_hash() != ci.get_hash() {
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

/// Unused-level helper kept for symmetry with the Lean API.
pub fn levels_key(us: &[Level]) -> Vec<Hash> {
  us.iter().map(|u| *u.get_hash()).collect()
}
