//! Pass 3b: the call-site rewrite (design document §4.5, Def 3.5, Def 3.6).
//! A port of `Ix/Compile/Pass/Translate.lean`. At every full application of
//! an image-kind head the optimisation hook is tried first (`RwState.opt?`:
//! `opt::engine_full`), then the image is inlined (the baseline, Def 3.6);
//! the decline hook (`RwState.decline?`) records O11a's declines.
//!
//! A definitional pass's term replaces the inline form. A proof-justified
//! pass's term (O7-O12) never replaces it under a Lean name (decision 5,
//! D1): the Lean name keeps the baseline and the definition's canonical form
//! `c._ix` (Lean's constant renamed) is returned in `BlockRewrite.canon`, to
//! be rewritten in place (`RwState.inPlace`) by the driver
//! (`Driver.compileCanon`).
//!
//! Every outermost rewritten occurrence is wrapped in the placeholder
//! `[(_ix.inline, n)]` and the source occurrence is returned as source `n`;
//! the compiler turns the placeholder into the decompile record.

use rustc_hash::FxHashMap;

use bignat::Nat;
use ix_common::env::{
  ConstantInfo, ConstantVal, DataValue, DefinitionVal, Expr, ExprData, Level,
  Name,
};

use super::develop::{DevState, instantiate_with};
use super::expr::{Hash, get_app_fn_args, key, mk_app_n, subst_levels};
use super::names::{inline_key, ix_form_name};
use super::view::Expansion;

/// The expansion lookup of a rewrite: `None` when the name is not an
/// image-kind head of a changed block.
pub type ExpansionLookup<'a> =
  dyn FnMut(&Name) -> Result<Option<Expansion>, String> + 'a;

/// A recursion bound for one rewrite.
pub const REWRITE_FUEL: usize = 1 << 20;

/// The optimisation hook (`RwState.opt?`, `Opt.engineFull` through
/// `Driver.optLookup`): at a full application `n.{us} args` with the site
/// (`RwState.site`), the rewrite, the canonical constants it references, and
/// whether the pass is proof-justified (O7-O12, `Opt.isProofJustified`); or
/// `None` (the baseline).
pub type OptHook<'h> = dyn Fn(
    Option<&Name>,
    &Name,
    &[Level],
    &[Expr],
  ) -> Option<(Expr, Vec<ConstantInfo>, bool)>
  + 'h;

/// The decline hook (`RwState.decline?`): the cause of a recorded decline at
/// a full application.
pub type DeclineHook<'h> =
  dyn Fn(&Name, &[Level], &[Expr]) -> Option<String> + 'h;

type CacheKey = (Hash, bool, Option<Name>);

#[derive(Default)]
pub struct RwState<'h> {
  /// The source occurrences, placeholder `i` for entry `i`.
  pub sources: Vec<Expr>,
  /// Rewritten expansions.
  pub exps: FxHashMap<Name, Expansion>,
  cache: FxHashMap<CacheKey, Expr>,
  /// The definition whose value is rewritten (`RwState.site`; read only by
  /// the passes, kept in the cache key as on the Lean side).
  site: Option<Name>,
  level_cache: FxHashMap<(Name, Vec<Hash>), Expr>,
  dev: DevState,
  /// The definitional passes, tried at every full application before the
  /// image is inlined (`RwState.opt?`).
  opt: Option<&'h OptHook<'h>>,
  /// The recorded declines, tried next to `opt` (`RwState.decline?`).
  decline: Option<&'h DeclineHook<'h>>,
  /// The causes recorded so far, in rewrite order (`RwState.declines`).
  pub declines: Vec<String>,
  /// The declines recorded while rewriting a cached subterm
  /// (`RwState.declineCache`, same key as `cache`).
  decline_cache: FxHashMap<CacheKey, Vec<String>>,
  /// Canonical constants to compile with the block (reserved `_ix` names,
  /// `RwState.canon`): the canonical form `c._ix` of a definition `c` where a
  /// proof-justified pass fires, and the helpers the passes' rewrites
  /// reference (O9/O10: re-typed handlers, O12: the pair-valued helper).
  pub canon: Vec<ConstantInfo>,
  /// Decision 5 (D1, `RwState.inPlace`): `false` for a Lean constant, whose
  /// name keeps the faithful form (a proof-justified rewrite keeps the
  /// baseline and sets `pj_fired`); `true` for a canonical constant (an
  /// `_ix` name), which takes the proof-justified rewrites in place.
  in_place: bool,
  /// A proof-justified pass fired in the value being rewritten
  /// (`RwState.pjFired`).
  pj_fired: bool,
}

impl<'h> RwState<'h> {
  /// A rewrite state with the passes' hooks; `in_place` (D1) for the
  /// canonical constants (`_ix` names).
  pub fn with_hooks(
    opt: Option<&'h OptHook<'h>>,
    decline: Option<&'h DeclineHook<'h>>,
    in_place: bool,
  ) -> Self {
    RwState { opt, decline, in_place, ..Default::default() }
  }

  /// Add canonical constants, each name once (`RwState.canon`'s fold).
  fn add_canon(&mut self, cs: Vec<ConstantInfo>) {
    for c in cs {
      if !self.canon.iter().any(|x| x.get_name() == c.get_name()) {
        self.canon.push(c);
      }
    }
  }

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
      // a cached subterm records its declines again (they belong to the
      // constant being rewritten now)
      if let Some(ds) = self.decline_cache.get(&ck) {
        self.declines.extend(ds.iter().cloned());
      }
      return Ok(r.clone());
    }
    let before = self.declines.len();
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
                  // the optimisation passes first; the inline image is the
                  // baseline when none applies
                  let site = self.site.clone();
                  let opt =
                    self.opt.and_then(|p| p(site.as_ref(), n, us, &args2));
                  let res: Option<(Expr, Vec<ConstantInfo>)> = match opt {
                    Some((e2, cs, false)) => Some((e2, cs)),
                    Some((e2, cs, true)) => {
                      if self.in_place {
                        Some((e2, cs))
                      } else {
                        // a Lean name keeps the faithful form (D1): the
                        // baseline here, the rewrite in the canonical form
                        // `c._ix`
                        self.pj_fired = true;
                        self
                          .opt
                          .and_then(|p| p(None, n, us, &args2))
                          .map(|(e3, cs3, _)| (e3, cs3))
                      }
                    },
                    None => None,
                  };
                  let body = match res {
                    Some((b, cs)) => {
                      if !cs.is_empty() {
                        self.add_canon(cs);
                      }
                      b
                    },
                    None => {
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
                      instantiate_with(&mut self.dev, &f, &args2)?
                    },
                  };
                  if let Some(cause) =
                    self.decline.and_then(|d| d(n, us, &args2))
                  {
                    self.declines.push(cause);
                  }
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
    if self.declines.len() != before {
      self.decline_cache.insert(ck.clone(), self.declines[before..].to_vec());
    }
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
      |st: &mut RwState<'_>, e: &Expr| st.rw(lookup, REWRITE_FUEL, true, e);
    Ok(match ci {
      ConstantInfo::AxiomInfo(v) => {
        let mut v = v.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        ConstantInfo::AxiomInfo(v)
      },
      ConstantInfo::DefnInfo(v0) => {
        let mut v = v0.clone();
        v.cnst.typ = go(self, &v.cnst.typ)?;
        // the value of a definition is the one place a proof-justified pass
        // may fire (`RwState.site`)
        self.site = Some(v.cnst.name.clone());
        self.pj_fired = false;
        let value = go(self, &v.value);
        let fired = self.pj_fired;
        self.site = None;
        self.pj_fired = false;
        v.value = value?;
        if fired && !self.in_place {
          // decision 5 (D1): the canonical form under `c._ix`, Lean's
          // constant renamed, rewritten in place when the block's canonical
          // constants compile (`Driver.compileCanon`)
          let c = ix_form_name(&v0.cnst.name);
          if !self.canon.iter().any(|x| *x.get_name() == c) {
            let cv = DefinitionVal {
              cnst: ConstantVal { name: c.clone(), ..v0.cnst.clone() },
              all: vec![c],
              ..v0.clone()
            };
            self.canon.push(ConstantInfo::DefnInfo(cv));
          }
        }
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
  /// The recorded declines, each with the member whose term had the
  /// occurrence, in rewrite order without repeats (`BlockRewrite.declines`).
  pub declines: Vec<(Name, String)>,
  /// Canonical constants the passes' rewrites reference (`RwState.canon`).
  pub canon: Vec<ConstantInfo>,
}

/// Rewrite the members of one block; placeholder indices are block-unique
/// (`rewriteBlock`), with the optimisation passes and the decline records
/// when the hooks are given. `in_place` (D1): the members are canonical
/// constants (`_ix` names), which take the proof-justified rewrites in
/// place; otherwise they are Lean constants, which keep the faithful form,
/// and the canonical form of each one a proof-justified pass fires in is
/// returned in `canon`.
pub fn rewrite_block<'h>(
  lookup: &mut ExpansionLookup<'_>,
  members: &[(Name, ConstantInfo)],
  opt: Option<&'h OptHook<'h>>,
  decline: Option<&'h DeclineHook<'h>>,
  in_place: bool,
) -> Result<BlockRewrite, String> {
  let mut st = RwState::with_hooks(opt, decline, in_place);
  let mut overlay = Vec::new();
  let mut declines: Vec<(Name, String)> = Vec::new();
  for (n, ci) in members {
    let before = st.declines.len();
    let ci2 = st.rewrite_const(lookup, ci)?;
    for c in &st.declines[before..] {
      let d = (n.clone(), c.clone());
      if !declines.contains(&d) {
        declines.push(d);
      }
    }
    if ci2.get_hash() != ci.get_hash() {
      overlay.push((n.clone(), ci2));
    }
  }
  Ok(BlockRewrite { overlay, sources: st.sources, declines, canon: st.canon })
}

/// The value and type of an image constant `a` with every head rewritten,
/// no records (`imageDeclWith`), from a rewrite state carried across the
/// members of an image block.
pub fn image_decl_with(
  st: &mut RwState<'_>,
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
