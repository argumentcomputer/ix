//! Expressions in the Ixon format.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::needless_pass_by_value)]

use crate::contract::{BinderContract, LetContract, Locality, ValueContract};
use std::sync::Arc;

/// Computational usage, independent of ownership and locality.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Uses {
  Erased = 0,
  Linear = 1,
  Affine = 2,
  Many = 3,
}

impl Uses {
  pub const fn to_bits(self) -> u8 {
    self as u8
  }

  pub const fn from_bits(bits: u8) -> Option<Self> {
    match bits {
      0 => Some(Self::Erased),
      1 => Some(Self::Linear),
      2 => Some(Self::Affine),
      3 => Some(Self::Many),
      _ => None,
    }
  }
}

/// Ownership of a bound or returned value, independent of usage and locality.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Owned {
  Unique = 0,
  Shared = 1,
}

impl Owned {
  pub const fn to_bits(self) -> u8 {
    self as u8
  }

  pub const fn from_bits(bits: u8) -> Option<Self> {
    match bits {
      0 => Some(Self::Unique),
      1 => Some(Self::Shared),
      _ => None,
    }
  }
}

/// Expression in the Ixon format.
///
/// This is the alpha-invariant representation of Lean expressions.
/// Names are stripped, binder info is stored in metadata.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Expr {
  /// Sort/Type at a universe level (index into Constant.univs table)
  Sort(u64),
  /// De Bruijn variable
  Var(u64),
  /// Reference to a top-level constant with universe arguments.
  /// First u64 is index into Constant.refs, Vec<u64> are indices into Constant.univs.
  Ref(u64, Vec<u64>),
  /// Mutual recursion reference (index within block) with universe arguments.
  /// First u64 is rec index, Vec<u64> are indices into Constant.univs.
  Rec(u64, Vec<u64>),
  /// Projection: (struct_type_ref_idx, field_index, struct_value)
  /// The first u64 is an index into Constant.refs table for the struct type.
  Prj(u64, u64, Arc<Expr>),
  /// String literal - index into Constant.refs table (address points to blob)
  Str(u64),
  /// Natural number literal - index into Constant.refs table (address points to blob)
  Nat(u64),
  /// Application: (function, argument)
  App(Arc<Expr>, Arc<Expr>),
  /// Lambda: (input contract, binder type, body)
  Lam(BinderContract, Arc<Expr>, Arc<Expr>),
  /// Forall/Pi: (input contract, independent result contract, domain, body)
  All(BinderContract, ValueContract, Arc<Expr>, Arc<Expr>),
  /// Ordinary let: (dependency/input contract, type, value, body)
  Let(LetContract, Arc<Expr>, Arc<Expr>, Arc<Expr>),
  /// Reference to shared subexpression in MutualBlock.sharing[idx]
  Share(u64),
}

impl Expr {
  // Tag4 flags for expression variants (0x0-0xB)
  pub const FLAG_SORT: u8 = 0x0;
  pub const FLAG_VAR: u8 = 0x1;
  pub const FLAG_REF: u8 = 0x2;
  pub const FLAG_REC: u8 = 0x3;
  pub const FLAG_PRJ: u8 = 0x4;
  pub const FLAG_STR: u8 = 0x5;
  pub const FLAG_NAT: u8 = 0x6;
  pub const FLAG_APP: u8 = 0x7;
  pub const FLAG_LAM: u8 = 0x8;
  pub const FLAG_ALL: u8 = 0x9;
  pub const FLAG_LET: u8 = 0xA; // size holds dependency and borrow flags
  pub const FLAG_SHARE: u8 = 0xB;

  pub fn sort(univ_idx: u64) -> Arc<Self> {
    Arc::new(Expr::Sort(univ_idx))
  }

  pub fn var(idx: u64) -> Arc<Self> {
    Arc::new(Expr::Var(idx))
  }

  pub fn reference(ref_idx: u64, univ_indices: Vec<u64>) -> Arc<Self> {
    Arc::new(Expr::Ref(ref_idx, univ_indices))
  }

  pub fn rec(rec_idx: u64, univ_indices: Vec<u64>) -> Arc<Self> {
    Arc::new(Expr::Rec(rec_idx, univ_indices))
  }

  pub fn prj(type_ref_idx: u64, field_idx: u64, val: Arc<Expr>) -> Arc<Self> {
    Arc::new(Expr::Prj(type_ref_idx, field_idx, val))
  }

  pub fn str(ref_idx: u64) -> Arc<Self> {
    Arc::new(Expr::Str(ref_idx))
  }

  pub fn nat(ref_idx: u64) -> Arc<Self> {
    Arc::new(Expr::Nat(ref_idx))
  }

  pub fn app(f: Arc<Expr>, a: Arc<Expr>) -> Arc<Self> {
    Arc::new(Expr::App(f, a))
  }

  pub fn lam(ty: Arc<Expr>, body: Arc<Expr>) -> Arc<Self> {
    Self::lam_mode(Uses::Many, ty, body)
  }

  pub fn lam_mode(uses: Uses, ty: Arc<Expr>, body: Arc<Expr>) -> Arc<Self> {
    Self::lam_contract(BinderContract::plain(uses), ty, body)
  }

  pub fn lam_contract(
    contract: BinderContract,
    ty: Arc<Expr>,
    body: Arc<Expr>,
  ) -> Arc<Self> {
    Arc::new(Expr::Lam(contract, ty, body))
  }

  pub fn all(ty: Arc<Expr>, body: Arc<Expr>) -> Arc<Self> {
    Self::all_mode(Uses::Many, Owned::Shared, ty, body)
  }

  pub fn all_mode(
    uses: Uses,
    owned: Owned,
    ty: Arc<Expr>,
    body: Arc<Expr>,
  ) -> Arc<Self> {
    Self::all_contract(
      BinderContract::plain(uses),
      ValueContract { owned, locality: Locality::Unrestricted },
      ty,
      body,
    )
  }

  pub fn all_contract(
    contract: BinderContract,
    result: ValueContract,
    ty: Arc<Expr>,
    body: Arc<Expr>,
  ) -> Arc<Self> {
    Arc::new(Expr::All(contract, result, ty, body))
  }

  pub fn let_(
    non_dep: bool,
    ty: Arc<Expr>,
    val: Arc<Expr>,
    body: Arc<Expr>,
  ) -> Arc<Self> {
    Self::let_contract(LetContract::plain(non_dep), ty, val, body)
  }

  pub fn let_contract(
    contract: LetContract,
    ty: Arc<Expr>,
    val: Arc<Expr>,
    body: Arc<Expr>,
  ) -> Arc<Self> {
    Arc::new(Expr::Let(contract, ty, val, body))
  }

  pub fn share(idx: u64) -> Arc<Self> {
    Arc::new(Expr::Share(idx))
  }

  /// Direct expression children, preserving contracts on their parent.
  pub fn children(&self) -> Vec<&Arc<Self>> {
    match self {
      Self::Sort(_)
      | Self::Var(_)
      | Self::Ref(..)
      | Self::Rec(..)
      | Self::Str(_)
      | Self::Nat(_)
      | Self::Share(_) => vec![],
      Self::Prj(_, _, e) => vec![e],
      Self::App(a, b) | Self::Lam(_, a, b) | Self::All(_, _, a, b) => {
        vec![a, b]
      },
      Self::Let(_, a, b, c) => vec![a, b, c],
    }
  }

  /// Rebuild a node without dropping any scalar or contract field.
  pub fn with_children(&self, children: &[Arc<Self>]) -> Result<Self, String> {
    if self.children().len() != children.len() {
      return Err("expression reconstruction child count mismatch".into());
    }
    Ok(match self {
      Self::Sort(_)
      | Self::Var(_)
      | Self::Ref(..)
      | Self::Rec(..)
      | Self::Str(_)
      | Self::Nat(_)
      | Self::Share(_) => self.clone(),
      Self::Prj(t, f, _) => Self::Prj(*t, *f, children[0].clone()),
      Self::App(..) => Self::App(children[0].clone(), children[1].clone()),
      Self::Lam(c, ..) => {
        Self::Lam(*c, children[0].clone(), children[1].clone())
      },
      Self::All(c, v, ..) => {
        Self::All(*c, *v, children[0].clone(), children[1].clone())
      },
      Self::Let(c, ..) => Self::Let(
        *c,
        children[0].clone(),
        children[1].clone(),
        children[2].clone(),
      ),
    })
  }

  /// Count nested applications for telescope compression.
  pub fn app_telescope_count(&self) -> u64 {
    let mut count = 0u64;
    let mut curr = self;
    while let Expr::App(f, _) = curr {
      count += 1;
      curr = f.as_ref();
    }
    count
  }

  /// Count nested lambdas for telescope compression.
  pub fn lam_telescope_count(&self) -> u64 {
    let mut count = 0u64;
    let mut curr = self;
    while let Expr::Lam(_, _, body) = curr {
      count += 1;
      curr = body.as_ref();
    }
    count
  }

  /// Count nested foralls for telescope compression.
  pub fn all_telescope_count(&self) -> u64 {
    let mut count = 0u64;
    let mut curr = self;
    while let Expr::All(_, _, _, body) = curr {
      count += 1;
      curr = body.as_ref();
    }
    count
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::constant::Constant;
  use crate::serialize::{get_expr, put_expr};
  use crate::tests::gen_range;
  use quickcheck::{Arbitrary, Gen};
  use quickcheck_macros::quickcheck;
  use std::ptr;

  #[derive(Clone, Copy)]
  enum Case {
    Var,
    Share,
    Str,
    Nat,
    Sort,
    Ref,
    Rec,
    App,
    Lam,
    All,
    Prj,
    Let,
  }

  fn arbitrary_value_contract(g: &mut Gen) -> ValueContract {
    ValueContract {
      owned: if bool::arbitrary(g) { Owned::Unique } else { Owned::Shared },
      locality: if bool::arbitrary(g) {
        Locality::Local
      } else {
        Locality::Unrestricted
      },
    }
  }

  fn arbitrary_binder_contract(g: &mut Gen, uses: Uses) -> BinderContract {
    BinderContract { uses, value: arbitrary_value_contract(g) }
  }

  /// Generate an arbitrary Expr using pointer-tree technique (no stack overflow)
  pub fn arbitrary_expr(g: &mut Gen) -> Arc<Expr> {
    use crate::tests::next_case;

    let mut root = Expr::Var(0);
    let mut stack = vec![&mut root as *mut Expr];

    while let Some(ptr) = stack.pop() {
      let gens = [
        (100, Case::Var),
        (80, Case::Share),
        (60, Case::Str),
        (60, Case::Nat),
        (40, Case::Sort),
        (40, Case::Ref),
        (40, Case::Rec),
        (30, Case::App),
        (30, Case::Lam),
        (30, Case::All),
        (20, Case::Prj),
        (10, Case::Let),
      ];

      match next_case(g, &gens) {
        Case::Var => unsafe {
          ptr::write(ptr, Expr::Var(gen_range(g, 0..16) as u64));
        },
        Case::Share => unsafe {
          ptr::write(ptr, Expr::Share(gen_range(g, 0..16) as u64));
        },
        Case::Str => unsafe {
          ptr::write(ptr, Expr::Str(gen_range(g, 0..16) as u64));
        },
        Case::Nat => unsafe {
          ptr::write(ptr, Expr::Nat(gen_range(g, 0..16) as u64));
        },
        Case::Sort => unsafe {
          ptr::write(ptr, Expr::Sort(gen_range(g, 0..16) as u64));
        },
        Case::Ref => {
          let univ_indices: Vec<_> = (0..gen_range(g, 0..4))
            .map(|_| gen_range(g, 0..16) as u64)
            .collect();
          unsafe {
            ptr::write(
              ptr,
              Expr::Ref(gen_range(g, 0..16) as u64, univ_indices),
            );
          }
        },
        Case::Rec => {
          let univ_indices: Vec<_> = (0..gen_range(g, 0..4))
            .map(|_| gen_range(g, 0..16) as u64)
            .collect();
          unsafe {
            ptr::write(ptr, Expr::Rec(gen_range(g, 0..8) as u64, univ_indices));
          }
        },
        Case::App => {
          let mut f = Arc::new(Expr::Var(0));
          let mut a = Arc::new(Expr::Var(0));
          let (f_ptr, a_ptr) = (
            Arc::get_mut(&mut f).unwrap() as *mut Expr,
            Arc::get_mut(&mut a).unwrap() as *mut Expr,
          );
          unsafe {
            ptr::write(ptr, Expr::App(f, a));
          }
          stack.push(a_ptr);
          stack.push(f_ptr);
        },
        Case::Lam => {
          let uses = match gen_range(g, 0..4) {
            0 => Uses::Erased,
            1 => Uses::Linear,
            2 => Uses::Affine,
            _ => Uses::Many,
          };
          let mut ty = Arc::new(Expr::Var(0));
          let mut body = Arc::new(Expr::Var(0));
          let (ty_ptr, body_ptr) = (
            Arc::get_mut(&mut ty).unwrap() as *mut Expr,
            Arc::get_mut(&mut body).unwrap() as *mut Expr,
          );
          unsafe {
            ptr::write(
              ptr,
              Expr::Lam(arbitrary_binder_contract(g, uses), ty, body),
            );
          }
          stack.push(body_ptr);
          stack.push(ty_ptr);
        },
        Case::All => {
          let uses = match gen_range(g, 0..4) {
            0 => Uses::Erased,
            1 => Uses::Linear,
            2 => Uses::Affine,
            _ => Uses::Many,
          };
          let mut ty = Arc::new(Expr::Var(0));
          let mut body = Arc::new(Expr::Var(0));
          let (ty_ptr, body_ptr) = (
            Arc::get_mut(&mut ty).unwrap() as *mut Expr,
            Arc::get_mut(&mut body).unwrap() as *mut Expr,
          );
          unsafe {
            ptr::write(
              ptr,
              Expr::All(
                arbitrary_binder_contract(g, uses),
                arbitrary_value_contract(g),
                ty,
                body,
              ),
            );
          }
          stack.push(body_ptr);
          stack.push(ty_ptr);
        },
        Case::Prj => {
          let mut val = Arc::new(Expr::Var(0));
          let val_ptr = Arc::get_mut(&mut val).unwrap() as *mut Expr;
          let type_ref_idx = gen_range(g, 0..16) as u64;
          let field_idx = gen_range(g, 0..8) as u64;
          unsafe {
            ptr::write(ptr, Expr::Prj(type_ref_idx, field_idx, val));
          }
          stack.push(val_ptr);
        },
        Case::Let => {
          let uses = Uses::from_bits(gen_range(g, 0..4) as u8).unwrap();
          let mut ty = Arc::new(Expr::Var(0));
          let mut val = Arc::new(Expr::Var(0));
          let mut body = Arc::new(Expr::Var(0));
          let (ty_ptr, val_ptr, body_ptr) = (
            Arc::get_mut(&mut ty).unwrap() as *mut Expr,
            Arc::get_mut(&mut val).unwrap() as *mut Expr,
            Arc::get_mut(&mut body).unwrap() as *mut Expr,
          );
          unsafe {
            ptr::write(
              ptr,
              Expr::Let(
                LetContract {
                  non_dep: bool::arbitrary(g),
                  kind: if bool::arbitrary(g) {
                    crate::contract::LetKind::BorrowShared
                  } else {
                    crate::contract::LetKind::Value
                  },
                  binder: arbitrary_binder_contract(g, uses),
                },
                ty,
                val,
                body,
              ),
            );
          }
          stack.push(body_ptr);
          stack.push(val_ptr);
          stack.push(ty_ptr);
        },
      }
    }
    Arc::new(root)
  }

  #[derive(Clone, Debug)]
  struct ArbitraryExpr(Arc<Expr>);

  impl Arbitrary for ArbitraryExpr {
    fn arbitrary(g: &mut Gen) -> Self {
      ArbitraryExpr(arbitrary_expr(g))
    }
  }

  fn expr_roundtrip(e: &Expr) -> bool {
    let mut buf = Vec::new();
    put_expr(e, &mut buf);
    match get_expr(&mut buf.as_slice()) {
      Ok(e2) => e == e2.as_ref(),
      Err(err) => {
        eprintln!("expr_roundtrip error: {err}");
        false
      },
    }
  }

  #[quickcheck]
  fn prop_expr_roundtrip(e: ArbitraryExpr) -> bool {
    expr_roundtrip(&e.0)
  }

  #[test]
  fn test_nested_app_telescope() {
    let e = Expr::app(
      Expr::app(Expr::app(Expr::var(0), Expr::var(1)), Expr::var(2)),
      Expr::var(3),
    );
    assert!(expr_roundtrip(&e));
  }

  #[test]
  fn test_nested_lam_telescope() {
    let ty = Expr::sort(0);
    let e =
      Expr::lam(ty.clone(), Expr::lam(ty.clone(), Expr::lam(ty, Expr::var(0))));
    assert!(expr_roundtrip(&e));
  }

  #[test]
  fn test_nested_all_telescope() {
    let ty = Expr::sort(0);
    let e = Expr::all(
      ty.clone(),
      Expr::all(ty.clone(), Expr::all(ty, Expr::sort(0))),
    );
    assert!(expr_roundtrip(&e));
  }

  #[test]
  fn ser_de_expr_var() {
    for idx in [0u64, 1, 7, 8, 100, 1000] {
      assert!(expr_roundtrip(&Expr::Var(idx)));
    }
  }

  #[test]
  fn ser_de_expr_sort() {
    for idx in [0u64, 1, 7, 8, 100, 1000] {
      assert!(expr_roundtrip(&Expr::Sort(idx)));
    }
  }

  #[test]
  fn ser_de_expr_str_nat() {
    for idx in [0u64, 1, 7, 8, 100, 1000] {
      assert!(expr_roundtrip(&Expr::Str(idx)));
      assert!(expr_roundtrip(&Expr::Nat(idx)));
    }
  }

  #[test]
  fn ser_de_expr_share() {
    for idx in [0u64, 1, 7, 8, 100] {
      assert!(expr_roundtrip(&Expr::Share(idx)));
    }
  }

  #[test]
  fn ser_de_expr_lam_telescope_size() {
    let ty = Expr::var(1);
    let expr =
      Expr::lam(ty.clone(), Expr::lam(ty.clone(), Expr::lam(ty, Expr::var(0))));
    let mut buf = Vec::new();
    put_expr(expr.as_ref(), &mut buf);
    assert_eq!(buf.len(), 8);
    assert!(expr_roundtrip(&expr));
  }

  #[test]
  fn ser_de_expr_app_telescope_size() {
    let expr = Expr::app(
      Expr::app(Expr::app(Expr::var(3), Expr::var(2)), Expr::var(1)),
      Expr::var(0),
    );
    let mut buf = Vec::new();
    put_expr(expr.as_ref(), &mut buf);
    assert_eq!(buf.len(), 5);
    assert!(expr_roundtrip(&expr));
  }

  #[test]
  fn telescope_lam_byte_boundaries() {
    for (n, tag_bytes) in
      [(1u64, 1), (7, 1), (8, 2), (255, 2), (256, 3), (500, 3)]
    {
      let ty = Expr::var(1);
      let mut expr: Arc<Expr> = Expr::var(0);
      for _ in 0..n {
        expr = Expr::lam(ty.clone(), expr);
      }
      let mut buf = Vec::new();
      put_expr(expr.as_ref(), &mut buf);
      assert_eq!(buf.len(), tag_bytes + 2 * (n as usize) + 1);
      assert!(expr_roundtrip(&expr));
    }
  }

  #[test]
  fn expr_and_constant_flags_unique() {
    assert_eq!(Expr::FLAG_SORT, 0x0);
    assert_eq!(Expr::FLAG_SHARE, 0xB);
    assert_eq!(Constant::FLAG_MUTS, 0xC);
    assert_eq!(Constant::FLAG, 0xD);
    // Expression flags are 0x0-0xB, Constant flags are 0xC-0xD
    assert!(
      ![0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB]
        .contains(&Constant::FLAG)
    );
    assert!(
      ![0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0x6, 0x7, 0x8, 0x9, 0xA, 0xB]
        .contains(&Constant::FLAG_MUTS)
    );
  }
}
