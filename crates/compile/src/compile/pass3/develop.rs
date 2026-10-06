//! Pass 3: the development as hereditary substitution (design document §4.3,
//! decision Q10). A port of `Ix/Compile/Image/Develop.lean`.
//!
//! `hinst v k e` substitutes `v` for the loose variable `bvar k` of `e` and
//! contracts exactly the redexes the substitution forms at the substituted
//! positions, hereditarily: beta at an application whose head became a
//! lambda, projection of a `PProd.mk`/`And.intro`, and eta at a binder whose
//! body became `x a1 ... an y` with `x` directly substituted. Nothing else is
//! reduced (never iota). Every traversal is memoised per node, as on the Lean
//! side; the results are those of the plain recursions.

use rustc_hash::FxHashMap;

use ix_common::env::{Expr, ExprData, Name};

use super::expr::{
  Hash, abstract_fvars, bvar, get_app_fn_args, key, mk_app_n, nat_usize,
};
use super::names::{n_and, n_and_intro, n_pprod, n_pprod_mk};

/// How the head of a substituted term was formed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Created {
  No,
  Direct,
  Reduced,
}

/// `.proj S i (S.mk a b x y)` to `x`/`y` for `PProd` and `And`.
fn proj_ctor(s: &Name, i: usize, e: &Expr) -> Option<Expr> {
  let (h, args) = get_app_fn_args(e);
  match h.as_data() {
    ExprData::Const(c, _, _) => {
      if args.len() == 4
        && i < 2
        && ((*s == n_pprod() && *c == n_pprod_mk())
          || (*s == n_and() && *c == n_and_intro()))
      {
        args.get(2 + i).cloned()
      } else {
        None
      }
    },
    _ => None,
  }
}

/// The fuel-free tables (values of total functions of their keys) and the
/// substitution table.
#[derive(Default)]
pub struct DevState {
  range: FxHashMap<Hash, usize>,
  lifted: FxHashMap<(Hash, usize, usize), Expr>,
  lowered: FxHashMap<(Hash, usize, usize), Expr>,
  occurs: FxHashMap<(Hash, usize), bool>,
  insts: FxHashMap<(Hash, Hash, usize), (Expr, Created)>,
}

impl DevState {
  /// One more than the largest loose bound variable of `e`.
  fn loose_range(&mut self, e: &Expr) -> usize {
    if let Some(r) = self.range.get(&key(e)) {
      return *r;
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => nat_usize(i).saturating_add(1),
      ExprData::App(f, a, _) => {
        let x = self.loose_range(f);
        let y = self.loose_range(a);
        x.max(y)
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        let x = self.loose_range(t);
        let y = self.loose_range(b).saturating_sub(1);
        x.max(y)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        let x = self.loose_range(t);
        let y = self.loose_range(v);
        let z = self.loose_range(b).saturating_sub(1);
        x.max(y).max(z)
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        self.loose_range(s)
      },
      _ => 0,
    };
    self.range.insert(key(e), r);
    r
  }

  fn lift(&mut self, e: &Expr, n: usize, c: usize) -> Expr {
    if n == 0 || self.loose_range(e) <= c {
      return e.clone();
    }
    let k = (key(e), n, c);
    if let Some(r) = self.lifted.get(&k) {
      return r.clone();
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i >= c { bvar(i + n) } else { e.clone() }
      },
      ExprData::App(f, a, _) => {
        let f2 = self.lift(f, n, c);
        let a2 = self.lift(a, n, c);
        Expr::app(f2, a2)
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = self.lift(t, n, c);
        let b2 = self.lift(b, n, c + 1);
        Expr::lam(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.lift(t, n, c);
        let b2 = self.lift(b, n, c + 1);
        Expr::all(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.lift(t, n, c);
        let v2 = self.lift(v, n, c);
        let b2 = self.lift(b, n, c + 1);
        Expr::letE(nm.clone(), t2, v2, b2, *nd)
      },
      ExprData::Proj(nm, i, s, _) => {
        let s2 = self.lift(s, n, c);
        Expr::proj(nm.clone(), i.clone(), s2)
      },
      ExprData::Mdata(md, x, _) => {
        let x2 = self.lift(x, n, c);
        Expr::mdata(md.clone(), x2)
      },
      _ => e.clone(),
    };
    self.lifted.insert(k, r.clone());
    r
  }

  fn lower(&mut self, e: &Expr, n: usize, c: usize) -> Expr {
    if n == 0 || self.loose_range(e) <= c {
      return e.clone();
    }
    let k = (key(e), n, c);
    if let Some(r) = self.lowered.get(&k) {
      return r.clone();
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i >= c + n { bvar(i - n) } else { e.clone() }
      },
      ExprData::App(f, a, _) => {
        let f2 = self.lower(f, n, c);
        let a2 = self.lower(a, n, c);
        Expr::app(f2, a2)
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = self.lower(t, n, c);
        let b2 = self.lower(b, n, c + 1);
        Expr::lam(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.lower(t, n, c);
        let b2 = self.lower(b, n, c + 1);
        Expr::all(nm.clone(), t2, b2, bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.lower(t, n, c);
        let v2 = self.lower(v, n, c);
        let b2 = self.lower(b, n, c + 1);
        Expr::letE(nm.clone(), t2, v2, b2, *nd)
      },
      ExprData::Proj(nm, i, s, _) => {
        let s2 = self.lower(s, n, c);
        Expr::proj(nm.clone(), i.clone(), s2)
      },
      ExprData::Mdata(md, x, _) => {
        let x2 = self.lower(x, n, c);
        Expr::mdata(md.clone(), x2)
      },
      _ => e.clone(),
    };
    self.lowered.insert(k, r.clone());
    r
  }

  fn occurs(&mut self, e: &Expr, k: usize) -> bool {
    if self.loose_range(e) <= k {
      return false;
    }
    let kk = (key(e), k);
    if let Some(r) = self.occurs.get(&kk) {
      return *r;
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => nat_usize(i) == k,
      ExprData::App(f, a, _) => self.occurs(f, k) || self.occurs(a, k),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        self.occurs(t, k) || self.occurs(b, k + 1)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        self.occurs(t, k) || self.occurs(v, k) || self.occurs(b, k + 1)
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        self.occurs(s, k)
      },
      _ => false,
    };
    self.occurs.insert(kk, r);
    r
  }

  /// `e[bvar k := v]`, contracting the redexes formed at the substituted
  /// positions.
  pub fn hinst(
    &mut self,
    fuel: usize,
    v: &Expr,
    k: usize,
    e: &Expr,
  ) -> Result<(Expr, Created), String> {
    if fuel == 0 {
      return Err("development: out of fuel".into());
    }
    let fuel = fuel - 1;
    if self.loose_range(e) <= k {
      return Ok((e.clone(), Created::No));
    }
    let ik = (key(v), key(e), k);
    if let Some(r) = self.insts.get(&ik) {
      return Ok(r.clone());
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i == k {
          (self.lift(v, k, 0), Created::Direct)
        } else if i > k {
          (bvar(i - 1), Created::No)
        } else {
          (e.clone(), Created::No)
        }
      },
      ExprData::App(..) => {
        let (h, args) = get_app_fn_args(e);
        let mut args2 = Vec::with_capacity(args.len());
        for a in &args {
          args2.push(self.hinst(fuel, v, k, a)?.0);
        }
        let (h2, c) = self.hinst(fuel, v, k, &h)?;
        match (c, h2.as_data()) {
          (Created::No, _) => (mk_app_n(h2, &args2), Created::No),
          (_, ExprData::Lam(..)) => {
            (self.happ(fuel, &h2, &args2)?, Created::Reduced)
          },
          (c, _) => (mk_app_n(h2, &args2), c),
        }
      },
      ExprData::Proj(s, i, x, _) => {
        let (x2, c) = self.hinst(fuel, v, k, x)?;
        match c {
          Created::No => (Expr::proj(s.clone(), i.clone(), x2), Created::No),
          _ => match proj_ctor(s, nat_usize(i), &x2) {
            Some(f) => (f, Created::Reduced),
            None => (Expr::proj(s.clone(), i.clone(), x2), Created::No),
          },
        }
      },
      ExprData::Lam(n, t, b, bi, _) => {
        let (t2, _) = self.hinst(fuel, v, k, t)?;
        let (b2, c) = self.hinst(fuel, v, k + 1, b)?;
        let mut out = None;
        if c == Created::Direct
          && let ExprData::App(f, a, _) = b2.as_data()
          && let ExprData::Bvar(z, _) = a.as_data()
          && nat_usize(z) == 0
          && !self.occurs(f, 0)
        {
          out = Some((self.lower(f, 1, 0), Created::Direct));
        }
        match out {
          Some(o) => o,
          None => (Expr::lam(n.clone(), t2, b2, bi.clone()), Created::No),
        }
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        let (t2, _) = self.hinst(fuel, v, k, t)?;
        let (b2, _) = self.hinst(fuel, v, k + 1, b)?;
        (Expr::all(n.clone(), t2, b2, bi.clone()), Created::No)
      },
      ExprData::LetE(n, t, x, b, nd, _) => {
        let (t2, _) = self.hinst(fuel, v, k, t)?;
        let (x2, _) = self.hinst(fuel, v, k, x)?;
        let (b2, _) = self.hinst(fuel, v, k + 1, b)?;
        (Expr::letE(n.clone(), t2, x2, b2, *nd), Created::No)
      },
      ExprData::Mdata(md, x, _) => {
        let (x2, c) = self.hinst(fuel, v, k, x)?;
        (Expr::mdata(md.clone(), x2), c)
      },
      _ => (e.clone(), Created::No),
    };
    self.insts.insert(ik, r.clone());
    Ok(r)
  }

  /// `f a1 ... an` with the beta-redexes at the head contracted
  /// hereditarily.
  pub fn happ(
    &mut self,
    fuel: usize,
    f: &Expr,
    args: &[Expr],
  ) -> Result<Expr, String> {
    if fuel == 0 {
      return Err("development: out of fuel".into());
    }
    let fuel = fuel - 1;
    match (f.as_data(), args.split_first()) {
      (ExprData::Lam(_, _, b, _, _), Some((a, rest))) => {
        let (b2, _) = self.hinst(fuel, a, 0, b)?;
        self.happ(fuel, &b2, rest)
      },
      _ => Ok(mk_app_n(f.clone(), args)),
    }
  }

  /// Clear the substitution table (its entries are computed under a fuel
  /// bound), keeping the fuel-free tables (`instantiateWith`).
  pub fn reset_insts(&mut self) {
    self.insts.clear();
  }
}

/// A bound on the recursion depth of the development.
pub const DEFAULT_FUEL: usize = 1 << 16;

/// The developed application `f args`.
pub fn instantiate(f: &Expr, args: &[Expr]) -> Result<Expr, String> {
  DevState::default().happ(DEFAULT_FUEL, f, args)
}

/// `instantiate` with the fuel-free tables of an earlier development carried
/// over and the substitution table fresh.
pub fn instantiate_with(
  st: &mut DevState,
  f: &Expr,
  args: &[Expr],
) -> Result<Expr, String> {
  st.reset_insts();
  st.happ(DEFAULT_FUEL, f, args)
}

/// `e[xs := vs]` for free variables, developed.
pub fn subst_fvars(xs: &[Name], vs: &[Expr], e: &Expr) -> Result<Expr, String> {
  if xs.len() != vs.len() {
    return Err("substFVars: arity mismatch".into());
  }
  let mut st = DevState::default();
  let mut acc = abstract_fvars(xs, e);
  for v in vs.iter().rev() {
    acc = st.hinst(DEFAULT_FUEL, v, 0, &acc)?.0;
  }
  Ok(acc)
}
