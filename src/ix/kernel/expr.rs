//! Expressions with optional metadata.
//!
//! `KExpr<M>` is an Arc-wrapped expression. Each variant carries an `ExprInfo<M>`
//! with its blake3 hash, substitution annotations, and mdata.

use std::fmt;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::env::{
  BinderInfo, DataValue, EALL, EAPP, ELAM, ELET, ENAT, EPRJ, EREF, ESORT, ESTR,
  EVAR, Name,
};
use lean_ffi::nat::Nat;

use super::env::Addr;
use super::id::KId;
use super::level::KUniv;
use super::mode::{KernelMode, MetaDisplay, MetaHash};

/// Expression. Thin Arc wrapper — cheap to clone, O(1) identity via `Arc::ptr_eq`.
#[derive(Clone, Debug)]
pub struct KExpr<M: KernelMode>(Arc<ExprData<M>>);

/// A single mdata layer: key-value pairs from Lean's `Expr.mdata`.
pub type MData = Vec<(Name, DataValue)>;

/// Per-expression metadata: blake3 hash, substitution annotations, and mdata.
#[derive(Clone, Debug)]
pub struct ExprInfo<M: KernelMode> {
  /// Blake3 hash (includes metadata contributions in Meta mode).
  pub addr: Addr,
  /// Loose bound variable range: upper bound on free de Bruijn indices.
  pub lbr: u64,
  /// Count of free `Var(0)` occurrences.
  pub count_0: u64,
  /// Lean mdata annotations. Semantically transparent, erased in Anon mode.
  pub mdata: M::MField<Vec<MData>>,
}

/// Expression data. Each variant carries its [`ExprInfo<M>`].
#[derive(Clone, Debug)]
pub enum ExprData<M: KernelMode> {
  Var(u64, M::MField<Name>, ExprInfo<M>),
  Sort(KUniv<M>, ExprInfo<M>),
  Const(KId<M>, Box<[KUniv<M>]>, ExprInfo<M>),
  App(KExpr<M>, KExpr<M>, ExprInfo<M>),
  Lam(M::MField<Name>, M::MField<BinderInfo>, KExpr<M>, KExpr<M>, ExprInfo<M>),
  All(M::MField<Name>, M::MField<BinderInfo>, KExpr<M>, KExpr<M>, ExprInfo<M>),
  /// Let binding: name, type, value, body, non_dep flag.
  Let(M::MField<Name>, KExpr<M>, KExpr<M>, KExpr<M>, bool, ExprInfo<M>),
  /// Projection: struct type id, field index, struct value.
  Prj(KId<M>, u64, KExpr<M>, ExprInfo<M>),
  Nat(Nat, Address, ExprInfo<M>),
  Str(String, Address, ExprInfo<M>),
}

impl<M: KernelMode> ExprData<M> {
  pub fn info(&self) -> &ExprInfo<M> {
    match self {
      ExprData::Var(.., i)
      | ExprData::Sort(.., i)
      | ExprData::Const(.., i)
      | ExprData::App(.., i)
      | ExprData::Lam(.., i)
      | ExprData::All(.., i)
      | ExprData::Let(.., i)
      | ExprData::Prj(.., i)
      | ExprData::Nat(.., i)
      | ExprData::Str(.., i) => i,
    }
  }
}

impl<M: KernelMode> KExpr<M> {
  pub fn new(data: ExprData<M>) -> Self {
    KExpr(Arc::new(data))
  }

  pub fn data(&self) -> &ExprData<M> {
    &self.0
  }

  pub fn info(&self) -> &ExprInfo<M> {
    self.data().info()
  }

  pub fn addr(&self) -> &Addr {
    &self.info().addr
  }

  pub fn lbr(&self) -> u64 {
    self.info().lbr
  }

  pub fn count_0(&self) -> u64 {
    self.info().count_0
  }

  pub fn mdata(&self) -> &M::MField<Vec<MData>> {
    &self.info().mdata
  }

  pub fn ptr_key(&self) -> usize {
    Arc::as_ptr(&self.0) as usize
  }

  pub fn ptr_eq(&self, other: &KExpr<M>) -> bool {
    Arc::ptr_eq(&self.0, &other.0)
  }

  pub fn hash_eq(&self, other: &KExpr<M>) -> bool {
    self.ptr_eq(other) || self.addr() == other.addr()
  }
}

impl<M: KernelMode> PartialEq for KExpr<M> {
  fn eq(&self, other: &Self) -> bool {
    self.hash_eq(other)
  }
}

impl<M: KernelMode> Eq for KExpr<M> {}

fn no_mdata<M: KernelMode>() -> M::MField<Vec<MData>> {
  M::meta_field(vec![])
}

fn mk_info<M: KernelMode>(
  addr: Addr,
  lbr: u64,
  count_0: u64,
  mdata: M::MField<Vec<MData>>,
) -> ExprInfo<M> {
  ExprInfo { addr, lbr, count_0, mdata }
}

impl<M: KernelMode> KExpr<M> {
  pub fn var(idx: u64, name: M::MField<Name>) -> Self {
    Self::var_mdata(idx, name, no_mdata::<M>())
  }

  pub fn var_mdata(
    idx: u64,
    name: M::MField<Name>,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[EVAR]);
    h.update(&idx.to_le_bytes());
    name.meta_hash(&mut h);
    mdata.meta_hash(&mut h);
    let info = mk_info::<M>(
      Arc::new(h.finalize()),
      idx + 1,
      if idx == 0 { 1 } else { 0 },
      mdata,
    );
    KExpr::new(ExprData::Var(idx, name, info))
  }

  pub fn sort(u: KUniv<M>) -> Self {
    Self::sort_mdata(u, no_mdata::<M>())
  }

  pub fn sort_mdata(u: KUniv<M>, mdata: M::MField<Vec<MData>>) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[ESORT]);
    h.update(u.addr().as_bytes());
    mdata.meta_hash(&mut h);
    KExpr::new(ExprData::Sort(
      u,
      mk_info::<M>(Arc::new(h.finalize()), 0, 0, mdata),
    ))
  }

  pub fn cnst(id: KId<M>, univs: Box<[KUniv<M>]>) -> Self {
    Self::cnst_mdata(id, univs, no_mdata::<M>())
  }

  pub fn cnst_mdata(
    id: KId<M>,
    univs: Box<[KUniv<M>]>,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[EREF]);
    h.update(id.addr.as_bytes());
    id.name.meta_hash(&mut h);
    for u in univs.iter() {
      h.update(u.addr().as_bytes());
    }
    mdata.meta_hash(&mut h);
    KExpr::new(ExprData::Const(
      id,
      univs,
      mk_info::<M>(Arc::new(h.finalize()), 0, 0, mdata),
    ))
  }

  pub fn app(f: KExpr<M>, a: KExpr<M>) -> Self {
    Self::app_mdata(f, a, no_mdata::<M>())
  }

  pub fn app_mdata(
    f: KExpr<M>,
    a: KExpr<M>,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[EAPP]);
    h.update(f.addr().as_bytes());
    h.update(a.addr().as_bytes());
    mdata.meta_hash(&mut h);
    let info = mk_info::<M>(
      Arc::new(h.finalize()),
      f.lbr().max(a.lbr()),
      f.count_0() + a.count_0(),
      mdata,
    );
    KExpr::new(ExprData::App(f, a, info))
  }

  pub fn lam(
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    ty: KExpr<M>,
    body: KExpr<M>,
  ) -> Self {
    Self::lam_mdata(name, bi, ty, body, no_mdata::<M>())
  }

  pub fn lam_mdata(
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    ty: KExpr<M>,
    body: KExpr<M>,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[ELAM]);
    name.meta_hash(&mut h);
    bi.meta_hash(&mut h);
    h.update(ty.addr().as_bytes());
    h.update(body.addr().as_bytes());
    mdata.meta_hash(&mut h);
    let info = mk_info::<M>(
      Arc::new(h.finalize()),
      ty.lbr().max(body.lbr().saturating_sub(1)),
      ty.count_0(),
      mdata,
    );
    KExpr::new(ExprData::Lam(name, bi, ty, body, info))
  }

  pub fn all(
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    ty: KExpr<M>,
    body: KExpr<M>,
  ) -> Self {
    Self::all_mdata(name, bi, ty, body, no_mdata::<M>())
  }

  pub fn all_mdata(
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    ty: KExpr<M>,
    body: KExpr<M>,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[EALL]);
    name.meta_hash(&mut h);
    bi.meta_hash(&mut h);
    h.update(ty.addr().as_bytes());
    h.update(body.addr().as_bytes());
    mdata.meta_hash(&mut h);
    let info = mk_info::<M>(
      Arc::new(h.finalize()),
      ty.lbr().max(body.lbr().saturating_sub(1)),
      ty.count_0(),
      mdata,
    );
    KExpr::new(ExprData::All(name, bi, ty, body, info))
  }

  pub fn let_(
    name: M::MField<Name>,
    ty: KExpr<M>,
    val: KExpr<M>,
    body: KExpr<M>,
    non_dep: bool,
  ) -> Self {
    Self::let_mdata(name, ty, val, body, non_dep, no_mdata::<M>())
  }

  pub fn let_mdata(
    name: M::MField<Name>,
    ty: KExpr<M>,
    val: KExpr<M>,
    body: KExpr<M>,
    non_dep: bool,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[ELET]);
    name.meta_hash(&mut h);
    h.update(ty.addr().as_bytes());
    h.update(val.addr().as_bytes());
    h.update(body.addr().as_bytes());
    h.update(&[non_dep as u8]);
    mdata.meta_hash(&mut h);
    let info = mk_info::<M>(
      Arc::new(h.finalize()),
      ty.lbr().max(val.lbr()).max(body.lbr().saturating_sub(1)),
      ty.count_0() + val.count_0(),
      mdata,
    );
    KExpr::new(ExprData::Let(name, ty, val, body, non_dep, info))
  }

  pub fn prj(id: KId<M>, field: u64, val: KExpr<M>) -> Self {
    Self::prj_mdata(id, field, val, no_mdata::<M>())
  }

  pub fn prj_mdata(
    id: KId<M>,
    field: u64,
    val: KExpr<M>,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[EPRJ]);
    h.update(id.addr.as_bytes());
    id.name.meta_hash(&mut h);
    h.update(&field.to_le_bytes());
    h.update(val.addr().as_bytes());
    mdata.meta_hash(&mut h);
    let info =
      mk_info::<M>(Arc::new(h.finalize()), val.lbr(), val.count_0(), mdata);
    KExpr::new(ExprData::Prj(id, field, val, info))
  }

  pub fn nat(val: Nat, blob_addr: Address) -> Self {
    Self::nat_mdata(val, blob_addr, no_mdata::<M>())
  }

  pub fn nat_mdata(
    val: Nat,
    blob_addr: Address,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[ENAT]);
    h.update(blob_addr.as_bytes());
    mdata.meta_hash(&mut h);
    KExpr::new(ExprData::Nat(
      val,
      blob_addr,
      mk_info::<M>(Arc::new(h.finalize()), 0, 0, mdata),
    ))
  }

  pub fn str(val: String, blob_addr: Address) -> Self {
    Self::str_mdata(val, blob_addr, no_mdata::<M>())
  }

  pub fn str_mdata(
    val: String,
    blob_addr: Address,
    mdata: M::MField<Vec<MData>>,
  ) -> Self {
    let mut h = blake3::Hasher::new();
    h.update(&[ESTR]);
    h.update(blob_addr.as_bytes());
    mdata.meta_hash(&mut h);
    KExpr::new(ExprData::Str(
      val,
      blob_addr,
      mk_info::<M>(Arc::new(h.finalize()), 0, 0, mdata),
    ))
  }
}

/// Meta mode: shows names when available. Anon mode: positional/hash fallbacks.
impl<M: KernelMode> fmt::Display for KExpr<M> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    fmt_expr(self, f, 0)
  }
}

fn fmt_expr<M: KernelMode>(
  e: &KExpr<M>,
  f: &mut fmt::Formatter<'_>,
  depth: usize,
) -> fmt::Result {
  if depth > 20 {
    return write!(f, "...");
  }
  match e.data() {
    ExprData::Var(idx, name, _) => {
      if name.has_meta() {
        name.meta_fmt(f)
      } else {
        write!(f, "#{idx}")
      }
    },
    ExprData::Sort(u, _) => write!(f, "Sort {u}"),
    ExprData::Const(id, us, _) => {
      write!(f, "{id}")?;
      if !us.is_empty() {
        write!(f, ".{{")?;
        for (i, u) in us.iter().enumerate() {
          if i > 0 {
            write!(f, ", ")?;
          }
          write!(f, "{u}")?;
        }
        write!(f, "}}")?;
      }
      Ok(())
    },
    ExprData::App(..) => {
      let (head, args) = collect_spine(e);
      write!(f, "(")?;
      fmt_expr(&head, f, depth + 1)?;
      for a in &args {
        write!(f, " ")?;
        fmt_expr(a, f, depth + 1)?;
      }
      write!(f, ")")
    },
    ExprData::Lam(name, _, ty, body, _) => {
      write!(f, "(fun (")?;
      if name.has_meta() {
        name.meta_fmt(f)?;
      } else {
        write!(f, "_")?;
      }
      write!(f, " : ")?;
      fmt_expr(ty, f, depth + 1)?;
      write!(f, ") => ")?;
      fmt_expr(body, f, depth + 1)?;
      write!(f, ")")
    },
    ExprData::All(name, _, ty, body, _) => {
      write!(f, "((")?;
      if name.has_meta() {
        name.meta_fmt(f)?;
      } else {
        write!(f, "_")?;
      }
      write!(f, " : ")?;
      fmt_expr(ty, f, depth + 1)?;
      write!(f, ") -> ")?;
      fmt_expr(body, f, depth + 1)?;
      write!(f, ")")
    },
    ExprData::Let(name, ty, val, body, _, _) => {
      write!(f, "(let ")?;
      if name.has_meta() {
        name.meta_fmt(f)?;
      } else {
        write!(f, "_")?;
      }
      write!(f, " : ")?;
      fmt_expr(ty, f, depth + 1)?;
      write!(f, " := ")?;
      fmt_expr(val, f, depth + 1)?;
      write!(f, " in ")?;
      fmt_expr(body, f, depth + 1)?;
      write!(f, ")")
    },
    ExprData::Prj(id, field, val, _) => {
      fmt_expr(val, f, depth + 1)?;
      write!(f, ".{field}@{id}")
    },
    ExprData::Nat(val, _, _) => write!(f, "{val}"),
    ExprData::Str(val, _, _) => write!(f, "{val:?}"),
  }
}

fn collect_spine<M: KernelMode>(e: &KExpr<M>) -> (KExpr<M>, Vec<KExpr<M>>) {
  let mut args = Vec::new();
  let mut cur = e.clone();
  loop {
    match cur.data() {
      ExprData::App(func, arg, _) => {
        args.push(arg.clone());
        cur = func.clone();
      },
      _ => break,
    }
  }
  args.reverse();
  (cur, args)
}

#[cfg(test)]
mod tests {
  use super::super::mode::{Anon, Meta};
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::env::BinderInfo;

  type ME = KExpr<Meta>;
  type AE = KExpr<Anon>;
  type MU = KUniv<Meta>;
  type AU = KUniv<Anon>;

  fn mk_name(s: &str) -> Name {
    let mut name = Name::anon();
    for part in s.split('.') {
      name = Name::str(name, part.to_string());
    }
    name
  }

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  // ---- Constructors & hashing ----

  #[test]
  fn var_hash_deterministic() {
    assert_eq!(AE::var(0, ()).addr(), AE::var(0, ()).addr());
  }

  #[test]
  fn var_different_indices() {
    assert_ne!(AE::var(0, ()).addr(), AE::var(1, ()).addr());
  }

  #[test]
  fn var_meta_name_affects_hash() {
    assert_ne!(
      ME::var(0, mk_name("x")).addr(),
      ME::var(0, mk_name("y")).addr()
    );
  }

  #[test]
  fn sort_hash() {
    assert_ne!(
      AE::sort(AU::zero()).addr(),
      AE::sort(AU::succ(AU::zero())).addr()
    );
  }

  #[test]
  fn const_hash() {
    let c = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    assert_eq!(c.lbr(), 0);
    assert_eq!(c.count_0(), 0);
  }

  #[test]
  fn const_meta_name_affects_hash() {
    let a = ME::cnst(KId::new(mk_addr("Nat"), mk_name("Nat")), Box::new([]));
    let b = ME::cnst(KId::new(mk_addr("Nat"), mk_name("Int")), Box::new([]));
    assert_ne!(a.addr(), b.addr());
  }

  #[test]
  fn app_hash_and_lbr() {
    let a = AE::app(AE::var(0, ()), AE::var(1, ()));
    assert_eq!(a.lbr(), 2);
    assert_eq!(a.count_0(), 1);
  }

  #[test]
  fn app_order_matters() {
    let v0 = AE::var(0, ());
    let v1 = AE::var(1, ());
    assert_ne!(AE::app(v0.clone(), v1.clone()).addr(), AE::app(v1, v0).addr());
  }

  #[test]
  fn lam_meta_name_affects_hash() {
    let ty = ME::sort(MU::zero());
    let body = ME::var(0, mk_name("x"));
    let a =
      ME::lam(mk_name("x"), BinderInfo::Default, ty.clone(), body.clone());
    let b = ME::lam(mk_name("y"), BinderInfo::Default, ty, body);
    assert_ne!(a.addr(), b.addr());
  }

  #[test]
  fn lam_binder_info_affects_hash() {
    let ty = ME::sort(MU::zero());
    let body = ME::var(0, mk_name("x"));
    let a =
      ME::lam(mk_name("x"), BinderInfo::Default, ty.clone(), body.clone());
    let b = ME::lam(mk_name("x"), BinderInfo::Implicit, ty, body);
    assert_ne!(a.addr(), b.addr());
  }

  #[test]
  fn lam_lbr() {
    let e = AE::lam((), (), AE::sort(AU::zero()), AE::var(1, ()));
    assert_eq!(e.lbr(), 1);
    let e2 = AE::lam((), (), AE::var(0, ()), AE::var(0, ()));
    assert_eq!(e2.lbr(), 1);
  }

  #[test]
  fn all_hash_differs_from_lam() {
    let ty = AE::sort(AU::zero());
    let body = AE::var(0, ());
    assert_ne!(
      AE::lam((), (), ty.clone(), body.clone()).addr(),
      AE::all((), (), ty, body).addr()
    );
  }

  #[test]
  fn let_hash() {
    let e =
      AE::let_((), AE::sort(AU::zero()), AE::var(0, ()), AE::var(1, ()), true);
    assert_eq!(e.lbr(), 1);
    assert_eq!(e.count_0(), 1);
  }

  #[test]
  fn let_non_dep_affects_hash() {
    let ty = AE::sort(AU::zero());
    let val = AE::var(0, ());
    let body = AE::var(0, ());
    let a = AE::let_((), ty.clone(), val.clone(), body.clone(), true);
    let b = AE::let_((), ty, val, body, false);
    assert_ne!(a.addr(), b.addr());
  }

  #[test]
  fn prj_hash() {
    let p = AE::prj(KId::new(mk_addr("Prod"), ()), 0, AE::var(0, ()));
    assert_eq!(p.lbr(), 1);
  }

  #[test]
  fn nat_str_hash() {
    let n = AE::nat(Nat::from(42u64), mk_addr("42"));
    let s = AE::str("hello".into(), mk_addr("hello"));
    assert_ne!(n.addr(), s.addr());
    assert_eq!(n.lbr(), 0);
  }

  // ---- mdata accessor ----

  #[test]
  fn mdata_default_empty() {
    let e = ME::var(0, mk_name("x"));
    assert!(e.mdata().is_empty());
  }

  // ---- PartialEq ----

  #[test]
  fn eq_by_hash() {
    let a = AE::app(AE::var(0, ()), AE::var(1, ()));
    let b = AE::app(AE::var(0, ()), AE::var(1, ()));
    assert_eq!(a, b);
    assert_ne!(a, AE::var(0, ()));
  }

  // ---- Display ----

  #[test]
  fn display_var_anon() {
    assert_eq!(format!("{}", AE::var(0, ())), "#0");
  }

  #[test]
  fn display_var_meta_named() {
    assert_eq!(format!("{}", ME::var(0, mk_name("x"))), "x");
  }

  #[test]
  fn display_sort() {
    assert_eq!(format!("{}", AE::sort(AU::zero())), "Sort 0");
  }

  #[test]
  fn display_const_anon() {
    let c = AE::cnst(KId::new(mk_addr("Nat"), ()), Box::new([]));
    let s = format!("{c}");
    assert_eq!(s.len(), 8, "got '{s}'"); // 8 hex chars (hash only)
  }

  #[test]
  fn display_const_meta() {
    let c = ME::cnst(KId::new(mk_addr("Nat"), mk_name("Nat")), Box::new([]));
    assert!(format!("{c}").starts_with("Nat@"));
  }

  #[test]
  fn display_const_with_univs() {
    let c =
      AE::cnst(KId::new(mk_addr("List"), ()), Box::new([AU::param(0, ())]));
    let s = format!("{c}");
    assert!(s.contains(".{u0}"), "got '{s}'");
  }

  #[test]
  fn display_app() {
    assert_eq!(
      format!("{}", AE::app(AE::var(0, ()), AE::var(1, ()))),
      "(#0 #1)"
    );
  }

  #[test]
  fn display_app_spine() {
    let e = AE::app(AE::app(AE::var(0, ()), AE::var(1, ())), AE::var(2, ()));
    assert_eq!(format!("{e}"), "(#0 #1 #2)");
  }

  #[test]
  fn display_lam_meta() {
    let e = ME::lam(
      mk_name("x"),
      BinderInfo::Default,
      ME::sort(MU::zero()),
      ME::var(0, mk_name("x")),
    );
    assert_eq!(format!("{e}"), "(fun (x : Sort 0) => x)");
  }

  #[test]
  fn display_all_anon() {
    let e = AE::all((), (), AE::sort(AU::zero()), AE::var(0, ()));
    assert_eq!(format!("{e}"), "((_ : Sort 0) -> #0)");
  }

  #[test]
  fn display_let() {
    let e =
      AE::let_((), AE::sort(AU::zero()), AE::var(0, ()), AE::var(0, ()), true);
    assert_eq!(format!("{e}"), "(let _ : Sort 0 := #0 in #0)");
  }

  #[test]
  fn display_nat() {
    assert_eq!(format!("{}", AE::nat(Nat::from(42u64), mk_addr("42"))), "42");
  }

  #[test]
  fn display_str() {
    assert_eq!(
      format!("{}", AE::str("hello".into(), mk_addr("hello"))),
      "\"hello\""
    );
  }
}
