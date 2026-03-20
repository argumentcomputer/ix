//! Ix.Expr build/decode/roundtrip FFI.
//!
//! Ix.Expr layout (12 constructors):
//! - Tag 0: bvar (idx : Nat) (hash : Address)
//! - Tag 1: fvar (name : Name) (hash : Address)
//! - Tag 2: mvar (name : Name) (hash : Address)
//! - Tag 3: sort (level : Level) (hash : Address)
//! - Tag 4: const (name : Name) (levels : Array Level) (hash : Address)
//! - Tag 5: app (fn arg : Expr) (hash : Address)
//! - Tag 6: lam (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address)
//! - Tag 7: forallE (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address)
//! - Tag 8: letE (name : Name) (ty val body : Expr) (nonDep : Bool) (hash : Address)
//! - Tag 9: lit (l : Literal) (hash : Address)
//! - Tag 10: mdata (data : Array (Name × DataValue)) (expr : Expr) (hash : Address)
//! - Tag 11: proj (typeName : Name) (idx : Nat) (struct : Expr) (hash : Address)

use crate::ffi::builder::LeanBuildCache;
use crate::ix::env::{
  BinderInfo, DataValue, Expr, ExprData, Level, Literal, Name,
};
use crate::lean::LeanIxAddress;
use crate::lean::{
  LeanIxBinderInfo, LeanIxDataValue, LeanIxExpr, LeanIxLevel, LeanIxLiteral,
  LeanIxName,
};
use lean_ffi::nat::Nat;
use lean_ffi::object::{
  LeanCtor, LeanOwned, LeanRef, LeanString,
};
#[cfg(feature = "test-ffi")]
use lean_ffi::object::LeanBorrowed;

impl LeanIxExpr<LeanOwned> {
  /// Build a Lean Ix.Expr with embedded hash.
  /// Uses caching to avoid rebuilding the same expression.
  pub fn build(cache: &mut LeanBuildCache, expr: &Expr) -> Self {
    let hash = *expr.get_hash();
    if let Some(cached) = cache.exprs.get(&hash) {
      return cached.clone();
    }

    let result = match expr.as_data() {
      ExprData::Bvar(idx, h) => {
        let ctor = LeanCtor::alloc(0, 2, 0);
        ctor.set(0, Nat::to_lean(idx));
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::Fvar(name, h) => {
        let ctor = LeanCtor::alloc(1, 2, 0);
        ctor.set(0, LeanIxName::build(cache, name));
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::Mvar(name, h) => {
        let ctor = LeanCtor::alloc(2, 2, 0);
        ctor.set(0, LeanIxName::build(cache, name));
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::Sort(level, h) => {
        let ctor = LeanCtor::alloc(3, 2, 0);
        ctor.set(0, LeanIxLevel::build(cache, level));
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::Const(name, levels, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let levels_obj = LeanIxLevel::build_array(cache, levels);
        let ctor = LeanCtor::alloc(4, 3, 0);
        ctor.set(0, name_obj);
        ctor.set(1, levels_obj);
        ctor.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::App(fn_expr, arg_expr, h) => {
        let fn_obj = Self::build(cache, fn_expr);
        let arg_obj = Self::build(cache, arg_expr);
        let ctor = LeanCtor::alloc(5, 3, 0);
        ctor.set(0, fn_obj);
        ctor.set(1, arg_obj);
        ctor.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::Lam(name, ty, body, bi, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let ty_obj = Self::build(cache, ty);
        let body_obj = Self::build(cache, body);
        let hash_obj = LeanIxAddress::build_from_hash(h);
        // 4 object fields, 1 scalar byte for BinderInfo
        let ctor = LeanCtor::alloc(6, 4, 1);
        ctor.set(0, name_obj);
        ctor.set(1, ty_obj);
        ctor.set(2, body_obj);
        ctor.set(3, hash_obj);
        ctor.set_u8(4, 0, LeanIxBinderInfo::<LeanOwned>::to_u8(bi));
        Self::new(ctor.into())
      },
      ExprData::ForallE(name, ty, body, bi, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let ty_obj = Self::build(cache, ty);
        let body_obj = Self::build(cache, body);
        let hash_obj = LeanIxAddress::build_from_hash(h);
        let ctor = LeanCtor::alloc(7, 4, 1);
        ctor.set(0, name_obj);
        ctor.set(1, ty_obj);
        ctor.set(2, body_obj);
        ctor.set(3, hash_obj);
        ctor.set_u8(4, 0, LeanIxBinderInfo::<LeanOwned>::to_u8(bi));
        Self::new(ctor.into())
      },
      ExprData::LetE(name, ty, val, body, non_dep, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let ty_obj = Self::build(cache, ty);
        let val_obj = Self::build(cache, val);
        let body_obj = Self::build(cache, body);
        let hash_obj = LeanIxAddress::build_from_hash(h);
        // 5 object fields, 1 scalar byte for Bool
        let ctor = LeanCtor::alloc(8, 5, 1);
        ctor.set(0, name_obj);
        ctor.set(1, ty_obj);
        ctor.set(2, val_obj);
        ctor.set(3, body_obj);
        ctor.set(4, hash_obj);
        ctor.set_u8(5, 0, *non_dep as u8);
        Self::new(ctor.into())
      },
      ExprData::Lit(lit, h) => {
        let lit_obj = LeanIxLiteral::build(lit);
        let ctor = LeanCtor::alloc(9, 2, 0);
        ctor.set(0, lit_obj);
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::Mdata(md, inner, h) => {
        let md_obj = LeanIxDataValue::build_kvmap(cache, md);
        let inner_obj = Self::build(cache, inner);
        let ctor = LeanCtor::alloc(10, 3, 0);
        ctor.set(0, md_obj);
        ctor.set(1, inner_obj);
        ctor.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
      ExprData::Proj(type_name, idx, struct_expr, h) => {
        let name_obj = LeanIxName::build(cache, type_name);
        let idx_obj = Nat::to_lean(idx);
        let struct_obj = Self::build(cache, struct_expr);
        let ctor = LeanCtor::alloc(11, 4, 0);
        ctor.set(0, name_obj);
        ctor.set(1, idx_obj);
        ctor.set(2, struct_obj);
        ctor.set(3, LeanIxAddress::build_from_hash(h));
        Self::new(ctor.into())
      },
    };

    cache.exprs.insert(hash, result.clone());
    result
  }
}

impl<R: LeanRef> LeanIxExpr<R> {
  /// Decode a Lean Ix.Expr to Rust Expr.
  pub fn decode(&self) -> Expr {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // bvar
        let idx = Nat::from_obj(&ctor.get(0));
        Expr::bvar(idx)
      },
      1 => {
        // fvar
        let name = LeanIxName(ctor.get(0)).decode();
        Expr::fvar(name)
      },
      2 => {
        // mvar
        let name = LeanIxName(ctor.get(0)).decode();
        Expr::mvar(name)
      },
      3 => {
        // sort
        let level = LeanIxLevel(ctor.get(0)).decode();
        Expr::sort(level)
      },
      4 => {
        // const
        let name = LeanIxName(ctor.get(0)).decode();
        let levels: Vec<Level> =
          ctor.get(1).as_array().map(|x| LeanIxLevel(x).decode());

        Expr::cnst(name, levels)
      },
      5 => {
        // app
        let fn_expr = LeanIxExpr(ctor.get(0)).decode();
        let arg_expr = LeanIxExpr(ctor.get(1)).decode();
        Expr::app(fn_expr, arg_expr)
      },
      6 => {
        // lam: name, ty, body, hash, bi (scalar)
        let name = LeanIxName(ctor.get(0)).decode();
        let ty = LeanIxExpr(ctor.get(1)).decode();
        let body = LeanIxExpr(ctor.get(2)).decode();

        // Read BinderInfo scalar (4 obj fields: name, ty, body, hash)
        let bi_byte = ctor.get_u8(4, 0);
        let bi = LeanIxBinderInfo::<LeanOwned>::from_u8(bi_byte);

        Expr::lam(name, ty, body, bi)
      },
      7 => {
        // forallE: same layout as lam
        let name = LeanIxName(ctor.get(0)).decode();
        let ty = LeanIxExpr(ctor.get(1)).decode();
        let body = LeanIxExpr(ctor.get(2)).decode();

        // 4 obj fields: name, ty, body, hash
        let bi_byte = ctor.get_u8(4, 0);
        let bi = LeanIxBinderInfo::<LeanOwned>::from_u8(bi_byte);

        Expr::all(name, ty, body, bi)
      },
      8 => {
        // letE: name, ty, val, body, hash, nonDep (scalar)
        let name = LeanIxName(ctor.get(0)).decode();
        let ty = LeanIxExpr(ctor.get(1)).decode();
        let val = LeanIxExpr(ctor.get(2)).decode();
        let body = LeanIxExpr(ctor.get(3)).decode();

        // 5 obj fields: name, ty, val, body, hash
        let non_dep = ctor.get_u8(5, 0) != 0;

        Expr::letE(name, ty, val, body, non_dep)
      },
      9 => {
        // lit
        let lit = LeanIxLiteral(ctor.get(0)).decode();
        Expr::lit(lit)
      },
      10 => {
        // mdata: data, expr, hash
        let data: Vec<(Name, DataValue)> = ctor.get(0).as_array().map(|obj| {
          let pair = obj.as_ctor();
          let name = LeanIxName(pair.get(0)).decode();
          let dv = LeanIxDataValue(pair.get(1)).decode();
          (name, dv)
        });

        let inner = LeanIxExpr(ctor.get(1)).decode();
        Expr::mdata(data, inner)
      },
      11 => {
        // proj: typeName, idx, struct, hash
        let type_name = LeanIxName(ctor.get(0)).decode();
        let idx = Nat::from_obj(&ctor.get(1));
        let struct_expr = LeanIxExpr(ctor.get(2)).decode();

        Expr::proj(type_name, idx, struct_expr)
      },
      _ => panic!("Invalid Ix.Expr tag: {}", ctor.tag()),
    }
  }
}

impl LeanIxLiteral<LeanOwned> {
  /// Build a Literal (natVal or strVal).
  pub fn build(lit: &Literal) -> Self {
    match lit {
      Literal::NatVal(n) => {
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, Nat::to_lean(n));
        Self::new(ctor.into())
      },
      Literal::StrVal(s) => {
        let ctor = LeanCtor::alloc(1, 1, 0);
        ctor.set(0, LeanString::new(s.as_str()));
        Self::new(ctor.into())
      },
    }
  }
}

impl<R: LeanRef> LeanIxLiteral<R> {
  /// Decode Lean.Literal from a Lean object.
  pub fn decode(&self) -> Literal {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // natVal
        let nat = Nat::from_obj(&ctor.get(0));
        Literal::NatVal(nat)
      },
      1 => {
        // strVal
        Literal::StrVal(ctor.get(0).as_string().to_string())
      },
      _ => panic!("Invalid Literal tag: {}", ctor.tag()),
    }
  }
}

impl LeanIxBinderInfo<LeanOwned> {
  /// Build Ix.BinderInfo enum.
  /// BinderInfo is a 4-constructor enum with no fields, stored as boxed scalar.
  pub fn build(bi: &BinderInfo) -> Self {
    Self::new(LeanOwned::box_usize(Self::to_u8(bi) as usize))
  }

  /// Convert BinderInfo to u8 tag.
  pub fn to_u8(bi: &BinderInfo) -> u8 {
    match bi {
      BinderInfo::Default => 0,
      BinderInfo::Implicit => 1,
      BinderInfo::StrictImplicit => 2,
      BinderInfo::InstImplicit => 3,
    }
  }

  /// Decode BinderInfo from byte.
  pub fn from_u8(bi_byte: u8) -> BinderInfo {
    match bi_byte {
      0 => BinderInfo::Default,
      1 => BinderInfo::Implicit,
      2 => BinderInfo::StrictImplicit,
      3 => BinderInfo::InstImplicit,
      _ => panic!("Invalid BinderInfo: {}", bi_byte),
    }
  }
}

/// Round-trip an Ix.Expr: decode from Lean, re-encode via LeanBuildCache.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_expr(
  expr_ptr: LeanIxExpr<LeanBorrowed<'_>>,
) -> LeanIxExpr<LeanOwned> {
  let expr = expr_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxExpr::build(&mut cache, &expr)
}
