//! Pass 3: the call-site rewrite. A port of `Ix/Compile/Pass/Translate.lean`
//! with optional definitional-pass and decline hooks. At every full
//! application of an image-kind head the pass runs first, then its image
//! is the fallback. A bare or partial occurrence keeps the Lean name,
//! which denotes the stored image.
//!
//! Every outermost rewritten occurrence is wrapped in the placeholder
//! `[(_ix.inline, n)]` and the source occurrence is returned as source `n`;
//! the compiler turns the placeholder into the decompile record.
//!
//! The memo is keyed by the term, its record mode and the definition site
//! (Lean `RwKey`): an occurrence in a definition's value never shares a
//! placeholder with the same occurrence in a type, an expansion or another
//! member's value, so both compilers write the same records.

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

/// The definitional passes (Lean `RwConfig.opt?`, [`super::opt::engine`]):
/// tried at every full application of a head, before its image is inlined;
/// `None` keeps the baseline.
pub type OptHook<'a> =
  dyn Fn(&Name, &[Level], &[Expr]) -> Option<(Expr, Vec<String>)> + 'a;

/// A recorded side-condition failure at a full occurrence (Lean decline?).
pub type DeclineHook<'a> =
  dyn Fn(&Name, &[Level], &[Expr]) -> Option<String> + 'a;

/// Effects are sets in first-occurrence order, never occurrence counts.
/// This also bounds recursive Engine/O2 merges before they reach the memo.
pub(crate) fn extend_causes(
  out: &mut Vec<String>,
  reports: impl IntoIterator<Item = String>,
) {
  for cause in reports {
    if !out.contains(&cause) {
      out.push(cause);
    }
  }
}

#[derive(Default)]
pub struct RwState<'o> {
  /// The passes of this rewrite (`None`: the default `RwConfig`, the
  /// faithful baseline).
  pub opt: Option<&'o OptHook<'o>>,
  pub decline: Option<&'o DeclineHook<'o>>,
  /// Distinct causes in the current scope, replayed on a term-cache hit.
  pub declines: Vec<String>,
  /// The source occurrences, placeholder `i` for entry `i`.
  pub sources: Vec<Expr>,
  /// Rewritten expansions.
  pub exps: FxHashMap<Name, Expansion>,
  /// The definition whose value is being rewritten (Lean `RwConfig.site`):
  /// `Some` only inside a definition's value (`rewrite_const`), `None` in
  /// types, other roots and expansions. Part of the memo key, as in Lean's
  /// `RwKey` and the donor (`a9cf3607`); no pass reads it here.
  site: Option<Name>,
  /// Rewritten subterms by (term, record mode, site), each entry retaining
  /// its input: a hit is confirmed by raw equality (the key's hash is only
  /// its fast path).
  cache: FxHashMap<(Hash, bool, Option<Name>), (Expr, Expr, Vec<String>)>,
  /// An expansion's value at universe arguments, by the head and the
  /// arguments' hashes, each entry retaining its levels (confirmed raw).
  level_cache: FxHashMap<(Name, Vec<Hash>), (Vec<Level>, Expr)>,
  dev: DevState,
}

impl RwState<'_> {
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
    let outer = std::mem::take(&mut self.declines);
    let x = if x.needs_rewrite {
      // an expansion is shared by every site (Lean: `site := none`)
      let site = self.site.take();
      let v = self.rw(lookup, fuel, false, &x.value);
      self.site = site;
      Expansion { value: v?, needs_rewrite: false, ..x }
    } else {
      x
    };
    // A head entry carries no effects. Revisit an expansion that recorded
    // a decline; its term-cache entries retain and replay those causes.
    let effects = std::mem::replace(&mut self.declines, outer);
    if effects.is_empty() {
      self.exps.insert(n.clone(), x.clone());
    }
    extend_causes(&mut self.declines, effects);
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
    let ck = (key(e), record, self.site.clone());
    if let Some((input, r, declines)) = self.cache.get(&ck)
      && input.same_raw(e)
    {
      extend_causes(&mut self.declines, declines.iter().cloned());
      return Ok(r.clone());
    }
    // Capture a complete local effect set, independent of ambient causes.
    // Global deduplication followed by a suffix would lose repeated effects.
    let outer = std::mem::take(&mut self.declines);
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
                  // the passes first (Lean `RwConfig.opt?`), else the image
                  let body = match self.opt.and_then(|opt| opt(n, us, &args2)) {
                    Some((e, reports)) => {
                      extend_causes(&mut self.declines, reports);
                      e
                    },
                    None => {
                      let f = self.at_levels(n, us, &x);
                      instantiate_with(&mut self.dev, &f, &args2)?
                    },
                  };
                  if let Some(cause) =
                    self.decline.and_then(|decline| decline(n, us, &args2))
                  {
                    extend_causes(&mut self.declines, [cause]);
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
    let effects = std::mem::replace(&mut self.declines, outer);
    extend_causes(&mut self.declines, effects.iter().cloned());
    self.cache.insert(ck, (e.clone(), r.clone(), effects));
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
    let mut go = |st: &mut RwState<'_>, e: &Expr| -> Result<Expr, String> {
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
        // a definition's value is its own site (Lean `rewriteConstM`)
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
  /// Recorded declines, attributed to every member that encountered them.
  pub declines: Vec<(Name, String)>,
}

/// Rewrite the members of one block; placeholder indices are block-unique
/// (`rewriteBlock`). `opt` is the passes' hook (Lean `RwConfig.opt?`).
pub fn rewrite_block(
  lookup: &mut ExpansionLookup<'_>,
  members: &[(Name, ConstantInfo)],
  opt: Option<&OptHook<'_>>,
  decline: Option<&DeclineHook<'_>>,
) -> Result<BlockRewrite, String> {
  let mut st = RwState { opt, decline, ..RwState::default() };
  let mut overlay = Vec::new();
  let mut declines: Vec<(Name, String)> = Vec::new();
  for (n, ci) in members {
    st.declines.clear();
    let (ci2, changed) = st.rewrite_const(lookup, ci)?;
    let mut causes = st.declines.clone();
    causes.sort();
    causes.dedup();
    if !causes.is_empty() {
      declines.push((n.clone(), causes.join("; ")));
    }
    if changed {
      overlay.push((n.clone(), ci2));
    }
  }
  Ok(BlockRewrite { overlay, sources: st.sources, declines })
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

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::root_name;
  use ix_common::env::{
    AxiomVal, BinderInfo, ConstantVal, DefinitionSafety, DefinitionVal,
    ReducibilityHints,
  };

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
    let rw = rewrite_block(&mut |n| Ok(head(n)), &members, None, None).unwrap();
    assert_eq!(rw.overlay.len(), 1);
    assert_eq!(rw.overlay[0].0, root_name("c"));
    assert_eq!(rw.sources.len(), 1);
  }

  /// The placeholder of each `head` occurrence in a rewritten term, in order.
  fn placeholders(e: &Expr, out: &mut Vec<u64>) {
    match e.as_data() {
      ExprData::Mdata(md, x, _) => {
        for (k, v) in md {
          if *k == inline_key()
            && let DataValue::OfNat(n) = v
          {
            out.push(n.to_u64().unwrap());
          }
        }
        placeholders(x, out);
      },
      ExprData::App(f, a, _) => {
        placeholders(f, out);
        placeholders(a, out);
      },
      _ => {},
    }
  }

  fn defn(n: &str, typ: Expr, value: Expr) -> ConstantInfo {
    ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal { name: root_name(n), level_params: vec![], typ },
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![root_name(n)],
    })
  }

  /// The memo is keyed by the definition site (Lean `RwKey`): one occurrence
  /// in a definition's type and its value gets two placeholders (the
  /// type's is never the value's record), as does one occurrence in two
  /// members' values; the members' types share one. The structural
  /// recursion functional `T.size._f : (x : T) → T.below … x → Nat :=
  /// fun x (f : T.below … x) => …` has this shape (the lockstep divergence
  /// on `ReaderFidelityDefs`).
  #[test]
  fn definition_value_is_its_own_site() {
    let occ = Expr::app(term("head"), term("a"));
    let typ = Expr::app(term("f"), occ.clone());
    let members = vec![
      (root_name("m1"), defn("m1", typ.clone(), typ.clone())),
      (root_name("m2"), defn("m2", typ.clone(), typ.clone())),
    ];
    let rw = rewrite_block(&mut |n| Ok(head(n)), &members, None, None).unwrap();
    assert_eq!(rw.sources, vec![occ.clone(), occ.clone(), occ]);
    let mut got = Vec::new();
    for (_, ci) in &rw.overlay {
      let ConstantInfo::DefnInfo(v) = ci else { panic!("not a definition") };
      placeholders(&v.cnst.typ, &mut got);
      placeholders(&v.value, &mut got);
    }
    // m1: type 0, value 1; m2: type 0 (shared with m1's type), value 2
    assert_eq!(got, vec![0, 1, 0, 2]);
  }

  #[test]
  fn exhausted_bound_is_an_error() {
    let mut st = RwState::default();
    let e = Expr::app(term("f"), term("a"));
    assert!(st.rw(&mut |n| Ok(head(n)), 1, true, &e).is_err());
  }

  #[test]
  fn shared_dag_effects_are_bounded_and_independent_of_ambient_causes() {
    for depth in [6, 64] {
      let mut lookup = |n: &Name| {
        Ok(if n.same_raw(&root_name("outer")) {
          Some(Expansion {
            level_params: vec![],
            value: term("inner"),
            arity: 0,
            needs_rewrite: true,
          })
        } else if n.same_raw(&root_name("inner")) {
          Some(Expansion {
            level_params: vec![],
            value: term("baseline"),
            arity: 0,
            needs_rewrite: false,
          })
        } else {
          None
        })
      };
      let cause = "zeta cause";
      let expected = [cause, "alpha cause"];
      let decline = |n: &Name, _: &[Level], _: &[Expr]| {
        if n.same_raw(&root_name("inner")) {
          Some(cause.to_owned())
        } else {
          n.same_raw(&root_name("outer")).then(|| "alpha cause".to_owned())
        }
      };
      let mut st = RwState {
        decline: Some(&decline),
        declines: vec![cause.to_owned()],
        ..RwState::default()
      };
      let mut e = term("outer");
      for _ in 0..depth {
        e = Expr::app(Expr::app(term("pair"), e.clone()), e);
      }
      st.rw(&mut lookup, 256, false, &e).unwrap();
      assert_eq!(st.declines, expected);
      assert!(!st.exps.contains_key(&root_name("outer")));
      assert!(st.cache.len() <= depth + 4);
      assert!(st.cache.values().all(|(_, _, effects)| effects.len() <= 2));
      st.declines.clear();
      st.rw(&mut lookup, 256, false, &e).unwrap();
      assert_eq!(st.declines, expected);
      let member = (root_name("member"), defn("member", term("T"), e));
      let out =
        rewrite_block(&mut lookup, &[member], None, Some(&decline)).unwrap();
      assert_eq!(
        out.declines,
        [(root_name("member"), "alpha cause; zeta cause".to_owned())]
      );
    }
  }

  #[test]
  fn declines_survive_shared_expansions_and_term_cache_hits() {
    let mut lookup = |n: &Name| {
      Ok(if n.same_raw(&root_name("outer")) {
        Some(Expansion {
          level_params: vec![],
          value: term("inner"),
          arity: 0,
          needs_rewrite: true,
        })
      } else if n.same_raw(&root_name("inner")) {
        Some(Expansion {
          level_params: vec![],
          value: term("baseline"),
          arity: 0,
          needs_rewrite: false,
        })
      } else {
        None
      })
    };
    let cause = "recorded decline inside a shared expansion";
    let decline = |n: &Name, _: &[Level], _: &[Expr]| {
      n.same_raw(&root_name("inner")).then(|| cause.to_owned())
    };
    let theorem = |n: &str| {
      ConstantInfo::ThmInfo(ix_common::env::TheoremVal {
        cnst: ConstantVal {
          name: root_name(n),
          level_params: vec![],
          typ: term("T"),
        },
        value: term("outer"),
        all: vec![root_name(n)],
      })
    };
    let members = vec![
      (root_name("a"), defn("a", term("T"), term("outer"))),
      (root_name("b"), defn("b", term("T"), term("outer"))),
      (root_name("c"), theorem("c")),
      (root_name("d"), theorem("d")),
    ];
    let out =
      rewrite_block(&mut lookup, &members, None, Some(&decline)).unwrap();
    assert_eq!(out.overlay.len(), 4);
    assert_eq!(
      out.declines,
      ["a", "b", "c", "d"].map(|n| (root_name(n), cause.to_owned()))
    );
  }
}
