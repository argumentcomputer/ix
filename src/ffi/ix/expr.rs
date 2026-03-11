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

use crate::ix::env::{
  BinderInfo, DataValue, Expr, ExprData, Level, Literal, Name,
};
use crate::lean::{
  LeanIxBinderInfo, LeanIxDataValue, LeanIxExpr, LeanIxLevel, LeanIxLiteral,
  LeanIxName,
};
use lean_ffi::nat::Nat;
use lean_ffi::object::{LeanCtor, LeanObject, LeanString};

use crate::ffi::builder::LeanBuildCache;
use crate::ffi::primitives::build_nat;
use crate::lean::LeanIxAddress;

impl LeanIxExpr {
  /// Build a Lean Ix.Expr with embedded hash.
  /// Uses caching to avoid rebuilding the same expression.
  pub fn build(cache: &mut LeanBuildCache, expr: &Expr) -> Self {
    let hash = *expr.get_hash();
    if let Some(&cached) = cache.exprs.get(&hash) {
      cached.inc_ref();
      return cached;
    }

    let result = match expr.as_data() {
      ExprData::Bvar(idx, h) => {
        let obj = LeanCtor::alloc(0, 2, 0);
        obj.set(0, build_nat(idx));
        obj.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::Fvar(name, h) => {
        let obj = LeanCtor::alloc(1, 2, 0);
        obj.set(0, LeanIxName::build(cache, name));
        obj.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::Mvar(name, h) => {
        let obj = LeanCtor::alloc(2, 2, 0);
        obj.set(0, LeanIxName::build(cache, name));
        obj.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::Sort(level, h) => {
        let obj = LeanCtor::alloc(3, 2, 0);
        obj.set(0, LeanIxLevel::build(cache, level));
        obj.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::Const(name, levels, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let levels_obj = LeanIxLevel::build_array(cache, levels);
        let obj = LeanCtor::alloc(4, 3, 0);
        obj.set(0, name_obj);
        obj.set(1, levels_obj);
        obj.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::App(fn_expr, arg_expr, h) => {
        let fn_obj = Self::build(cache, fn_expr);
        let arg_obj = Self::build(cache, arg_expr);
        let obj = LeanCtor::alloc(5, 3, 0);
        obj.set(0, fn_obj);
        obj.set(1, arg_obj);
        obj.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::Lam(name, ty, body, bi, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let ty_obj = Self::build(cache, ty);
        let body_obj = Self::build(cache, body);
        let hash_obj = LeanIxAddress::build_from_hash(h);
        // 4 object fields, 1 scalar byte for BinderInfo
        let obj = LeanCtor::alloc(6, 4, 1);
        obj.set(0, name_obj);
        obj.set(1, ty_obj);
        obj.set(2, body_obj);
        obj.set(3, hash_obj);
        obj.set_scalar_u8(4, 0, LeanIxBinderInfo::to_u8(bi));
        Self::new(*obj)
      },
      ExprData::ForallE(name, ty, body, bi, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let ty_obj = Self::build(cache, ty);
        let body_obj = Self::build(cache, body);
        let hash_obj = LeanIxAddress::build_from_hash(h);
        let obj = LeanCtor::alloc(7, 4, 1);
        obj.set(0, name_obj);
        obj.set(1, ty_obj);
        obj.set(2, body_obj);
        obj.set(3, hash_obj);
        obj.set_scalar_u8(4, 0, LeanIxBinderInfo::to_u8(bi));
        Self::new(*obj)
      },
      ExprData::LetE(name, ty, val, body, non_dep, h) => {
        let name_obj = LeanIxName::build(cache, name);
        let ty_obj = Self::build(cache, ty);
        let val_obj = Self::build(cache, val);
        let body_obj = Self::build(cache, body);
        let hash_obj = LeanIxAddress::build_from_hash(h);
        // 5 object fields, 1 scalar byte for Bool
        let obj = LeanCtor::alloc(8, 5, 1);
        obj.set(0, name_obj);
        obj.set(1, ty_obj);
        obj.set(2, val_obj);
        obj.set(3, body_obj);
        obj.set(4, hash_obj);
        obj.set_scalar_u8(5, 0, *non_dep as u8);
        Self::new(*obj)
      },
      ExprData::Lit(lit, h) => {
        let lit_obj = LeanIxLiteral::build(lit);
        let obj = LeanCtor::alloc(9, 2, 0);
        obj.set(0, lit_obj);
        obj.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::Mdata(md, inner, h) => {
        let md_obj = LeanIxDataValue::build_kvmap(cache, md);
        let inner_obj = Self::build(cache, inner);
        let obj = LeanCtor::alloc(10, 3, 0);
        obj.set(0, md_obj);
        obj.set(1, inner_obj);
        obj.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
      ExprData::Proj(type_name, idx, struct_expr, h) => {
        let name_obj = LeanIxName::build(cache, type_name);
        let idx_obj = build_nat(idx);
        let struct_obj = Self::build(cache, struct_expr);
        let obj = LeanCtor::alloc(11, 4, 0);
        obj.set(0, name_obj);
        obj.set(1, idx_obj);
        obj.set(2, struct_obj);
        obj.set(3, LeanIxAddress::build_from_hash(h));
        Self::new(*obj)
      },
    };

    cache.exprs.insert(hash, result);
    result
  }

  /// Decode a Lean Ix.Expr to Rust Expr.
  pub fn decode(self) -> Expr {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // bvar
        let idx = Nat::from_obj(ctor.get(0));
        Expr::bvar(idx)
      },
      1 => {
        // fvar
        let name = LeanIxName::new(ctor.get(0)).decode();
        Expr::fvar(name)
      },
      2 => {
        // mvar
        let name = LeanIxName::new(ctor.get(0)).decode();
        Expr::mvar(name)
      },
      3 => {
        // sort
        let level = LeanIxLevel::new(ctor.get(0)).decode();
        Expr::sort(level)
      },
      4 => {
        // const
        let name = LeanIxName::new(ctor.get(0)).decode();
        let levels: Vec<Level> =
          ctor.get(1).as_array().map(|x| LeanIxLevel::new(x).decode());

        Expr::cnst(name, levels)
      },
      5 => {
        // app
        let fn_expr = Self::new(ctor.get(0)).decode();
        let arg_expr = Self::new(ctor.get(1)).decode();
        Expr::app(fn_expr, arg_expr)
      },
      6 => {
        // lam: name, ty, body, hash, bi (scalar)
        let name = LeanIxName::new(ctor.get(0)).decode();
        let ty = Self::new(ctor.get(1)).decode();
        let body = Self::new(ctor.get(2)).decode();

        // Read BinderInfo scalar (4 obj fields: name, ty, body, hash)
        let bi_byte = ctor.scalar_u8(4, 0);
        let bi = LeanIxBinderInfo::from_u8(bi_byte);

        Expr::lam(name, ty, body, bi)
      },
      7 => {
        // forallE: same layout as lam
        let name = LeanIxName::new(ctor.get(0)).decode();
        let ty = Self::new(ctor.get(1)).decode();
        let body = Self::new(ctor.get(2)).decode();

        // 4 obj fields: name, ty, body, hash
        let bi_byte = ctor.scalar_u8(4, 0);
        let bi = LeanIxBinderInfo::from_u8(bi_byte);

        Expr::all(name, ty, body, bi)
      },
      8 => {
        // letE: name, ty, val, body, hash, nonDep (scalar)
        let name = LeanIxName::new(ctor.get(0)).decode();
        let ty = Self::new(ctor.get(1)).decode();
        let val = Self::new(ctor.get(2)).decode();
        let body = Self::new(ctor.get(3)).decode();

        // 5 obj fields: name, ty, val, body, hash
        let non_dep = ctor.scalar_u8(5, 0) != 0;

        Expr::letE(name, ty, val, body, non_dep)
      },
      9 => {
        // lit
        let lit = LeanIxLiteral::new(ctor.get(0)).decode();
        Expr::lit(lit)
      },
      10 => {
        // mdata: data, expr, hash
        let data: Vec<(Name, DataValue)> = ctor.get(0).as_array().map(|obj| {
          let pair = obj.as_ctor();
          let name = LeanIxName::new(pair.get(0)).decode();
          let dv = LeanIxDataValue::new(pair.get(1)).decode();
          (name, dv)
        });

        let inner = Self::new(ctor.get(1)).decode();
        Expr::mdata(data, inner)
      },
      11 => {
        // proj: typeName, idx, struct, hash
        let type_name = LeanIxName::new(ctor.get(0)).decode();
        let idx = Nat::from_obj(ctor.get(1));
        let struct_expr = Self::new(ctor.get(2)).decode();

        Expr::proj(type_name, idx, struct_expr)
      },
      _ => panic!("Invalid Ix.Expr tag: {}", ctor.tag()),
    }
  }
}

impl LeanIxLiteral {
  /// Build a Literal (natVal or strVal).
  pub fn build(lit: &Literal) -> Self {
    let obj = match lit {
      Literal::NatVal(n) => {
        let obj = LeanCtor::alloc(0, 1, 0);
        obj.set(0, build_nat(n));
        *obj
      },
      Literal::StrVal(s) => {
        let obj = LeanCtor::alloc(1, 1, 0);
        obj.set(0, LeanString::new(s.as_str()));
        *obj
      },
    };
    Self::new(obj)
  }

  /// Decode Lean.Literal from a Lean object.
  pub fn decode(self) -> Literal {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // natVal
        let nat = Nat::from_obj(ctor.get(0));
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

impl LeanIxBinderInfo {
  /// Build Ix.BinderInfo enum.
  /// BinderInfo is a 4-constructor enum with no fields, stored as boxed scalar.
  pub fn build(bi: &BinderInfo) -> Self {
    Self::new(LeanObject::box_usize(Self::to_u8(bi) as usize))
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
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_expr(expr_ptr: LeanIxExpr) -> LeanIxExpr {
  let expr = expr_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxExpr::build(&mut cache, &expr)
}
