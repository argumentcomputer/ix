//! Build Lean Ix types from Rust env types using Lean's C API.
//!
//! This module provides functions to construct Lean objects (Ix.Name, Ix.Level,
//! Ix.Expr, Ix.ConstantInfo, Ix.Environment) from their Rust counterparts.

use std::ffi::{c_void, CString};

use blake3::Hash;
use rustc_hash::FxHashMap;

use crate::ix::env::{
  BinderInfo, ConstantInfo, ConstantVal, DataValue, DefinitionSafety, Expr, ExprData,
  Int, Level, LevelData, Literal, Name, NameData, QuotKind, ReducibilityHints,
  SourceInfo, Substring, Syntax, SyntaxPreresolved,
};
use crate::lean::nat::Nat;
use crate::lean::{
  lean_alloc_array, lean_alloc_ctor, lean_alloc_sarray, lean_array_get_core, lean_array_set_core,
  lean_box_fn, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_inc, lean_is_scalar,
  lean_mk_string, lean_obj_tag, lean_sarray_cptr, lean_uint64_to_nat,
};

/// Builder for constructing Lean Ix types with caching.
pub struct IxEnvBuilder {
  names: FxHashMap<Hash, *mut c_void>,
  levels: FxHashMap<Hash, *mut c_void>,
  exprs: FxHashMap<Hash, *mut c_void>,
}

impl IxEnvBuilder {
  pub fn new() -> Self {
    Self {
      names: FxHashMap::default(),
      levels: FxHashMap::default(),
      exprs: FxHashMap::default(),
    }
  }

  pub fn with_capacity(cap: usize) -> Self {
    Self {
      names: FxHashMap::with_capacity_and_hasher(cap, Default::default()),
      levels: FxHashMap::with_capacity_and_hasher(cap, Default::default()),
      exprs: FxHashMap::with_capacity_and_hasher(cap * 10, Default::default()),
    }
  }

  // ===========================================================================
  // Address (ByteArray wrapper)
  // ===========================================================================

  /// Build an Address from a blake3 Hash.
  /// Address = { hash : ByteArray } - single field struct, UNBOXED to ByteArray
  pub fn build_address(&self, hash: &Hash) -> *mut c_void {
    unsafe {
      // ByteArray is a scalar array of u8
      // Address is a single-field struct, so it's UNBOXED - just return the ByteArray
      let byte_array = lean_alloc_sarray(1, 32, 32);
      let data_ptr = lean_sarray_cptr(byte_array);
      std::ptr::copy_nonoverlapping(hash.as_bytes().as_ptr(), data_ptr, 32);
      byte_array
    }
  }

  // ===========================================================================
  // Ix.Name (3 constructors)
  // ===========================================================================

  /// Build a Ix.Name from a Rust Name.
  /// | anonymous (hash : Address)                           -- tag 0
  /// | str (parent : Name) (s : String) (hash : Address)    -- tag 1
  /// | num (parent : Name) (i : Nat) (hash : Address)       -- tag 2
  pub fn build_name(&mut self, name: &Name) -> *mut c_void {
    let hash = name.get_hash();
    if let Some(&cached) = self.names.get(&hash) {
      unsafe { lean_inc(cached) };
      return cached;
    }

    let result = unsafe {
      match name.as_data() {
        NameData::Anonymous(h) => {
          let obj = lean_alloc_ctor(0, 1, 0);
          lean_ctor_set(obj, 0, self.build_address(h));
          obj
        },
        NameData::Str(parent, s, h) => {
          let parent_obj = self.build_name(parent);
          let s_cstr = CString::new(s.as_str()).unwrap();
          let s_obj = lean_mk_string(s_cstr.as_ptr());
          let hash_obj = self.build_address(h);

          let obj = lean_alloc_ctor(1, 3, 0);
          lean_ctor_set(obj, 0, parent_obj);
          lean_ctor_set(obj, 1, s_obj);
          lean_ctor_set(obj, 2, hash_obj);
          obj
        },
        NameData::Num(parent, n, h) => {
          let parent_obj = self.build_name(parent);
          let n_obj = self.build_nat(n);
          let hash_obj = self.build_address(h);

          let obj = lean_alloc_ctor(2, 3, 0);
          lean_ctor_set(obj, 0, parent_obj);
          lean_ctor_set(obj, 1, n_obj);
          lean_ctor_set(obj, 2, hash_obj);
          obj
        },
      }
    };

    self.names.insert(hash, result);
    result
  }

  // ===========================================================================
  // Ix.Level (6 constructors)
  // ===========================================================================

  /// Build a Ix.Level from a Rust Level.
  /// | zero (hash : Address)                           -- tag 0
  /// | succ (l : Level) (hash : Address)               -- tag 1
  /// | max (l₁ l₂ : Level) (hash : Address)            -- tag 2
  /// | imax (l₁ l₂ : Level) (hash : Address)           -- tag 3
  /// | param (n : Name) (hash : Address)               -- tag 4
  /// | mvar (n : Name) (hash : Address)                -- tag 5
  pub fn build_level(&mut self, level: &Level) -> *mut c_void {
    let hash = *level.get_hash();
    if let Some(&cached) = self.levels.get(&hash) {
      unsafe { lean_inc(cached) };
      return cached;
    }

    let result = unsafe {
      match level.as_data() {
        LevelData::Zero(h) => {
          let obj = lean_alloc_ctor(0, 1, 0);
          lean_ctor_set(obj, 0, self.build_address(h));
          obj
        },
        LevelData::Succ(l, h) => {
          let l_obj = self.build_level(l);
          let obj = lean_alloc_ctor(1, 2, 0);
          lean_ctor_set(obj, 0, l_obj);
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
        LevelData::Max(l1, l2, h) => {
          let l1_obj = self.build_level(l1);
          let l2_obj = self.build_level(l2);
          let obj = lean_alloc_ctor(2, 3, 0);
          lean_ctor_set(obj, 0, l1_obj);
          lean_ctor_set(obj, 1, l2_obj);
          lean_ctor_set(obj, 2, self.build_address(h));
          obj
        },
        LevelData::Imax(l1, l2, h) => {
          let l1_obj = self.build_level(l1);
          let l2_obj = self.build_level(l2);
          let obj = lean_alloc_ctor(3, 3, 0);
          lean_ctor_set(obj, 0, l1_obj);
          lean_ctor_set(obj, 1, l2_obj);
          lean_ctor_set(obj, 2, self.build_address(h));
          obj
        },
        LevelData::Param(n, h) => {
          let n_obj = self.build_name(n);
          let obj = lean_alloc_ctor(4, 2, 0);
          lean_ctor_set(obj, 0, n_obj);
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
        LevelData::Mvar(n, h) => {
          let n_obj = self.build_name(n);
          let obj = lean_alloc_ctor(5, 2, 0);
          lean_ctor_set(obj, 0, n_obj);
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
      }
    };

    self.levels.insert(hash, result);
    result
  }

  // ===========================================================================
  // Ix.Expr (12 constructors)
  // ===========================================================================

  /// Build a Ix.Expr from a Rust Expr.
  pub fn build_expr(&mut self, expr: &Expr) -> *mut c_void {
    let hash = *expr.get_hash();
    if let Some(&cached) = self.exprs.get(&hash) {
      unsafe { lean_inc(cached) };
      return cached;
    }

    let result = unsafe {
      match expr.as_data() {
        // | bvar (idx : Nat) (hash : Address) -- tag 0
        ExprData::Bvar(idx, h) => {
          let obj = lean_alloc_ctor(0, 2, 0);
          lean_ctor_set(obj, 0, self.build_nat(idx));
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
        // | fvar (name : Name) (hash : Address) -- tag 1
        ExprData::Fvar(name, h) => {
          let obj = lean_alloc_ctor(1, 2, 0);
          lean_ctor_set(obj, 0, self.build_name(name));
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
        // | mvar (name : Name) (hash : Address) -- tag 2
        ExprData::Mvar(name, h) => {
          let obj = lean_alloc_ctor(2, 2, 0);
          lean_ctor_set(obj, 0, self.build_name(name));
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
        // | sort (level : Level) (hash : Address) -- tag 3
        ExprData::Sort(level, h) => {
          let obj = lean_alloc_ctor(3, 2, 0);
          lean_ctor_set(obj, 0, self.build_level(level));
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
        // | const (name : Name) (levels : Array Level) (hash : Address) -- tag 4
        ExprData::Const(name, levels, h) => {
          let name_obj = self.build_name(name);
          let levels_obj = self.build_level_array(levels);
          let obj = lean_alloc_ctor(4, 3, 0);
          lean_ctor_set(obj, 0, name_obj);
          lean_ctor_set(obj, 1, levels_obj);
          lean_ctor_set(obj, 2, self.build_address(h));
          obj
        },
        // | app (fn arg : Expr) (hash : Address) -- tag 5
        ExprData::App(fn_expr, arg_expr, h) => {
          let fn_obj = self.build_expr(fn_expr);
          let arg_obj = self.build_expr(arg_expr);
          let obj = lean_alloc_ctor(5, 3, 0);
          lean_ctor_set(obj, 0, fn_obj);
          lean_ctor_set(obj, 1, arg_obj);
          lean_ctor_set(obj, 2, self.build_address(h));
          obj
        },
        // | lam (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address) -- tag 6
        ExprData::Lam(name, ty, body, bi, h) => {
          let name_obj = self.build_name(name);
          let ty_obj = self.build_expr(ty);
          let body_obj = self.build_expr(body);
          let hash_obj = self.build_address(h);
          // 4 object fields, 1 scalar byte for BinderInfo
          let obj = lean_alloc_ctor(6, 4, 1);
          lean_ctor_set(obj, 0, name_obj);
          lean_ctor_set(obj, 1, ty_obj);
          lean_ctor_set(obj, 2, body_obj);
          lean_ctor_set(obj, 3, hash_obj);
          lean_ctor_set_uint8(obj, 4 * 8, binder_info_to_u8(bi));
          obj
        },
        // | forallE (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address) -- tag 7
        ExprData::ForallE(name, ty, body, bi, h) => {
          let name_obj = self.build_name(name);
          let ty_obj = self.build_expr(ty);
          let body_obj = self.build_expr(body);
          let hash_obj = self.build_address(h);
          let obj = lean_alloc_ctor(7, 4, 1);
          lean_ctor_set(obj, 0, name_obj);
          lean_ctor_set(obj, 1, ty_obj);
          lean_ctor_set(obj, 2, body_obj);
          lean_ctor_set(obj, 3, hash_obj);
          lean_ctor_set_uint8(obj, 4 * 8, binder_info_to_u8(bi));
          obj
        },
        // | letE (name : Name) (ty val body : Expr) (nonDep : Bool) (hash : Address) -- tag 8
        ExprData::LetE(name, ty, val, body, non_dep, h) => {
          let name_obj = self.build_name(name);
          let ty_obj = self.build_expr(ty);
          let val_obj = self.build_expr(val);
          let body_obj = self.build_expr(body);
          let hash_obj = self.build_address(h);
          // 5 object fields, 1 scalar byte for Bool
          let obj = lean_alloc_ctor(8, 5, 1);
          lean_ctor_set(obj, 0, name_obj);
          lean_ctor_set(obj, 1, ty_obj);
          lean_ctor_set(obj, 2, val_obj);
          lean_ctor_set(obj, 3, body_obj);
          lean_ctor_set(obj, 4, hash_obj);
          lean_ctor_set_uint8(obj, 5 * 8, *non_dep as u8);
          obj
        },
        // | lit (l : Literal) (hash : Address) -- tag 9
        ExprData::Lit(lit, h) => {
          let lit_obj = self.build_literal(lit);
          let obj = lean_alloc_ctor(9, 2, 0);
          lean_ctor_set(obj, 0, lit_obj);
          lean_ctor_set(obj, 1, self.build_address(h));
          obj
        },
        // | mdata (md : Array (Name × DataValue)) (expr : Expr) (hash : Address) -- tag 10
        ExprData::Mdata(md, inner, h) => {
          let md_obj = self.build_mdata_array(md);
          let inner_obj = self.build_expr(inner);
          let obj = lean_alloc_ctor(10, 3, 0);
          lean_ctor_set(obj, 0, md_obj);
          lean_ctor_set(obj, 1, inner_obj);
          lean_ctor_set(obj, 2, self.build_address(h));
          obj
        },
        // | proj (typeName : Name) (idx : Nat) (struct : Expr) (hash : Address) -- tag 11
        ExprData::Proj(type_name, idx, struct_expr, h) => {
          let name_obj = self.build_name(type_name);
          let idx_obj = self.build_nat(idx);
          let struct_obj = self.build_expr(struct_expr);
          let obj = lean_alloc_ctor(11, 4, 0);
          lean_ctor_set(obj, 0, name_obj);
          lean_ctor_set(obj, 1, idx_obj);
          lean_ctor_set(obj, 2, struct_obj);
          lean_ctor_set(obj, 3, self.build_address(h));
          obj
        },
      }
    };

    self.exprs.insert(hash, result);
    result
  }

  // ===========================================================================
  // Helper functions for building various types
  // ===========================================================================

  /// Build a Lean Nat from a Rust Nat.
  /// Small nats are boxed scalars, large nats use GMP via limbs.
  fn build_nat(&self, n: &Nat) -> *mut c_void {
    // Try to get as u64 first
    if let Some(val) = n.to_u64() {
      // For small values that fit in a boxed scalar (max value is usize::MAX >> 1)
      if val <= (usize::MAX >> 1) as u64 {
        return lean_box_fn(val as usize);
      }
      // For larger u64 values, use lean_uint64_to_nat
      return unsafe { lean_uint64_to_nat(val) };
    }
    // For values larger than u64, convert to limbs and use GMP
    let bytes = n.to_le_bytes();
    let mut limbs: Vec<u64> = Vec::with_capacity((bytes.len() + 7) / 8);
    for chunk in bytes.chunks(8) {
      let mut arr = [0u8; 8];
      arr[..chunk.len()].copy_from_slice(chunk);
      limbs.push(u64::from_le_bytes(arr));
    }
    unsafe { crate::lean::lean_nat_from_limbs(limbs.len(), limbs.as_ptr()) }
  }

  /// Build a Lean.Literal.
  /// | natVal (n : Nat) -- tag 0
  /// | strVal (s : String) -- tag 1
  fn build_literal(&self, lit: &Literal) -> *mut c_void {
    unsafe {
      match lit {
        Literal::NatVal(n) => {
          let obj = lean_alloc_ctor(0, 1, 0);
          lean_ctor_set(obj, 0, self.build_nat(n));
          obj
        },
        Literal::StrVal(s) => {
          let s_cstr = CString::new(s.as_str()).unwrap();
          let obj = lean_alloc_ctor(1, 1, 0);
          lean_ctor_set(obj, 0, lean_mk_string(s_cstr.as_ptr()));
          obj
        },
      }
    }
  }

  /// Build an Array of Levels.
  fn build_level_array(&mut self, levels: &[Level]) -> *mut c_void {
    unsafe {
      let arr = lean_alloc_array(levels.len(), levels.len());
      for (i, level) in levels.iter().enumerate() {
        let level_obj = self.build_level(level);
        lean_array_set_core(arr, i, level_obj);
      }
      arr
    }
  }

  /// Build an Array of Names.
  fn build_name_array(&mut self, names: &[Name]) -> *mut c_void {
    unsafe {
      let arr = lean_alloc_array(names.len(), names.len());
      for (i, name) in names.iter().enumerate() {
        let name_obj = self.build_name(name);
        lean_array_set_core(arr, i, name_obj);
      }
      arr
    }
  }

  /// Build an Array of (Name, DataValue) pairs for mdata.
  fn build_mdata_array(&mut self, md: &[(Name, DataValue)]) -> *mut c_void {
    unsafe {
      let arr = lean_alloc_array(md.len(), md.len());
      for (i, (name, dv)) in md.iter().enumerate() {
        let pair = self.build_name_datavalue_pair(name, dv);
        lean_array_set_core(arr, i, pair);
      }
      arr
    }
  }

  /// Build a (Name, DataValue) pair (Prod).
  fn build_name_datavalue_pair(&mut self, name: &Name, dv: &DataValue) -> *mut c_void {
    unsafe {
      let name_obj = self.build_name(name);
      let dv_obj = self.build_data_value(dv);
      // Prod is a structure with 2 fields
      let obj = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(obj, 0, name_obj);
      lean_ctor_set(obj, 1, dv_obj);
      obj
    }
  }

  /// Build a Ix.DataValue.
  fn build_data_value(&mut self, dv: &DataValue) -> *mut c_void {
    unsafe {
      match dv {
        // | ofString (s : String) -- tag 0
        DataValue::OfString(s) => {
          let s_cstr = CString::new(s.as_str()).unwrap();
          let obj = lean_alloc_ctor(0, 1, 0);
          lean_ctor_set(obj, 0, lean_mk_string(s_cstr.as_ptr()));
          obj
        },
        // | ofBool (b : Bool) -- tag 1, 0 object fields, 1 scalar byte
        DataValue::OfBool(b) => {
          let obj = lean_alloc_ctor(1, 0, 1);
          lean_ctor_set_uint8(obj, 0, if *b { 1 } else { 0 });
          obj
        },
        // | ofName (n : Name) -- tag 2
        DataValue::OfName(name) => {
          let obj = lean_alloc_ctor(2, 1, 0);
          lean_ctor_set(obj, 0, self.build_name(name));
          obj
        },
        // | ofNat (n : Nat) -- tag 3
        DataValue::OfNat(n) => {
          let obj = lean_alloc_ctor(3, 1, 0);
          lean_ctor_set(obj, 0, self.build_nat(n));
          obj
        },
        // | ofInt (i : Int) -- tag 4
        DataValue::OfInt(i) => {
          let obj = lean_alloc_ctor(4, 1, 0);
          lean_ctor_set(obj, 0, self.build_int(i));
          obj
        },
        // | ofSyntax (s : Syntax) -- tag 5
        DataValue::OfSyntax(syn) => {
          let obj = lean_alloc_ctor(5, 1, 0);
          lean_ctor_set(obj, 0, self.build_syntax(syn));
          obj
        },
      }
    }
  }

  /// Build a Ix.Int.
  fn build_int(&self, i: &Int) -> *mut c_void {
    unsafe {
      match i {
        // | ofNat (n : Nat) -- tag 0
        Int::OfNat(n) => {
          let obj = lean_alloc_ctor(0, 1, 0);
          lean_ctor_set(obj, 0, self.build_nat(n));
          obj
        },
        // | negSucc (n : Nat) -- tag 1
        Int::NegSucc(n) => {
          let obj = lean_alloc_ctor(1, 1, 0);
          lean_ctor_set(obj, 0, self.build_nat(n));
          obj
        },
      }
    }
  }

  /// Build a Ix.Substring.
  fn build_substring(&self, ss: &Substring) -> *mut c_void {
    unsafe {
      let s_cstr = CString::new(ss.str.as_str()).unwrap();
      // Substring = { str : String, startPos : Nat, stopPos : Nat }
      let obj = lean_alloc_ctor(0, 3, 0);
      lean_ctor_set(obj, 0, lean_mk_string(s_cstr.as_ptr()));
      lean_ctor_set(obj, 1, self.build_nat(&ss.start_pos));
      lean_ctor_set(obj, 2, self.build_nat(&ss.stop_pos));
      obj
    }
  }

  /// Build a Ix.SourceInfo.
  fn build_source_info(&self, si: &SourceInfo) -> *mut c_void {
    unsafe {
      match si {
        // | original (leading : Substring) (pos : Nat) (trailing : Substring) (endPos : Nat) -- tag 0
        SourceInfo::Original(leading, pos, trailing, end_pos) => {
          let obj = lean_alloc_ctor(0, 4, 0);
          lean_ctor_set(obj, 0, self.build_substring(leading));
          lean_ctor_set(obj, 1, self.build_nat(pos));
          lean_ctor_set(obj, 2, self.build_substring(trailing));
          lean_ctor_set(obj, 3, self.build_nat(end_pos));
          obj
        },
        // | synthetic (pos : Nat) (endPos : Nat) (canonical : Bool) -- tag 1
        SourceInfo::Synthetic(pos, end_pos, canonical) => {
          let obj = lean_alloc_ctor(1, 2, 1);
          lean_ctor_set(obj, 0, self.build_nat(pos));
          lean_ctor_set(obj, 1, self.build_nat(end_pos));
          lean_ctor_set_uint8(obj, 2 * 8, *canonical as u8);
          obj
        },
        // | none -- tag 2
        SourceInfo::None => lean_alloc_ctor(2, 0, 0),
      }
    }
  }

  /// Build a Ix.SyntaxPreresolved.
  fn build_syntax_preresolved(&mut self, sp: &SyntaxPreresolved) -> *mut c_void {
    unsafe {
      match sp {
        // | namespace (name : Name) -- tag 0
        SyntaxPreresolved::Namespace(name) => {
          let obj = lean_alloc_ctor(0, 1, 0);
          lean_ctor_set(obj, 0, self.build_name(name));
          obj
        },
        // | decl (name : Name) (aliases : Array String) -- tag 1
        SyntaxPreresolved::Decl(name, aliases) => {
          let name_obj = self.build_name(name);
          let aliases_obj = self.build_string_array(aliases);
          let obj = lean_alloc_ctor(1, 2, 0);
          lean_ctor_set(obj, 0, name_obj);
          lean_ctor_set(obj, 1, aliases_obj);
          obj
        },
      }
    }
  }

  /// Build an Array of Strings.
  fn build_string_array(&self, strings: &[String]) -> *mut c_void {
    unsafe {
      let arr = lean_alloc_array(strings.len(), strings.len());
      for (i, s) in strings.iter().enumerate() {
        let s_cstr = CString::new(s.as_str()).unwrap();
        lean_array_set_core(arr, i, lean_mk_string(s_cstr.as_ptr()));
      }
      arr
    }
  }

  /// Build a Ix.Syntax.
  fn build_syntax(&mut self, syn: &Syntax) -> *mut c_void {
    unsafe {
      match syn {
        // | missing -- tag 0
        Syntax::Missing => lean_alloc_ctor(0, 0, 0),
        // | node (info : SourceInfo) (kind : Name) (args : Array Syntax) -- tag 1
        Syntax::Node(info, kind, args) => {
          let info_obj = self.build_source_info(info);
          let kind_obj = self.build_name(kind);
          let args_obj = self.build_syntax_array(args);
          let obj = lean_alloc_ctor(1, 3, 0);
          lean_ctor_set(obj, 0, info_obj);
          lean_ctor_set(obj, 1, kind_obj);
          lean_ctor_set(obj, 2, args_obj);
          obj
        },
        // | atom (info : SourceInfo) (val : String) -- tag 2
        Syntax::Atom(info, val) => {
          let info_obj = self.build_source_info(info);
          let val_cstr = CString::new(val.as_str()).unwrap();
          let obj = lean_alloc_ctor(2, 2, 0);
          lean_ctor_set(obj, 0, info_obj);
          lean_ctor_set(obj, 1, lean_mk_string(val_cstr.as_ptr()));
          obj
        },
        // | ident (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : Array SyntaxPreresolved) -- tag 3
        Syntax::Ident(info, raw_val, val, preresolved) => {
          let info_obj = self.build_source_info(info);
          let raw_val_obj = self.build_substring(raw_val);
          let val_obj = self.build_name(val);
          let preresolved_obj = self.build_syntax_preresolved_array(preresolved);
          let obj = lean_alloc_ctor(3, 4, 0);
          lean_ctor_set(obj, 0, info_obj);
          lean_ctor_set(obj, 1, raw_val_obj);
          lean_ctor_set(obj, 2, val_obj);
          lean_ctor_set(obj, 3, preresolved_obj);
          obj
        },
      }
    }
  }

  /// Build an Array of Syntax.
  fn build_syntax_array(&mut self, items: &[Syntax]) -> *mut c_void {
    unsafe {
      let arr = lean_alloc_array(items.len(), items.len());
      for (i, item) in items.iter().enumerate() {
        let item_obj = self.build_syntax(item);
        lean_array_set_core(arr, i, item_obj);
      }
      arr
    }
  }

  /// Build an Array of SyntaxPreresolved.
  fn build_syntax_preresolved_array(&mut self, items: &[SyntaxPreresolved]) -> *mut c_void {
    unsafe {
      let arr = lean_alloc_array(items.len(), items.len());
      for (i, item) in items.iter().enumerate() {
        let item_obj = self.build_syntax_preresolved(item);
        lean_array_set_core(arr, i, item_obj);
      }
      arr
    }
  }

  // ===========================================================================
  // Ix.ConstantInfo (8 variants)
  // ===========================================================================

  /// Build a Ix.ConstantVal structure.
  fn build_constant_val(&mut self, cv: &ConstantVal) -> *mut c_void {
    unsafe {
      // ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
      let name_obj = self.build_name(&cv.name);
      let level_params_obj = self.build_name_array(&cv.level_params);
      let type_obj = self.build_expr(&cv.typ);

      let obj = lean_alloc_ctor(0, 3, 0);
      lean_ctor_set(obj, 0, name_obj);
      lean_ctor_set(obj, 1, level_params_obj);
      lean_ctor_set(obj, 2, type_obj);
      obj
    }
  }

  /// Build ReducibilityHints.
  /// NOTE: In Lean 4, 0-field constructors are boxed scalars when the inductive has
  /// other constructors with fields. So opaque and abbrev use lean_box_fn.
  fn build_reducibility_hints(&self, hints: &ReducibilityHints) -> *mut c_void {
    unsafe {
      match hints {
        // | opaque -- tag 0, boxed as scalar
        ReducibilityHints::Opaque => lean_box_fn(0),
        // | abbrev -- tag 1, boxed as scalar
        ReducibilityHints::Abbrev => lean_box_fn(1),
        // | regular (h : UInt32) -- tag 2, object constructor
        ReducibilityHints::Regular(h) => {
          // UInt32 is a scalar, stored inline
          let obj = lean_alloc_ctor(2, 0, 4);
          // Set the uint32 at offset 0 in the scalar area
          let ptr = obj as *mut u8;
          *(ptr.add(8) as *mut u32) = *h;
          obj
        },
      }
    }
  }

  // NOTE: DefinitionSafety and QuotKind are stored as scalar fields in their
  // containing structures, not as separate objects. The build functions below
  // are kept for reference but not used.
  //
  // /// Build DefinitionSafety.
  // fn build_definition_safety(&self, safety: &DefinitionSafety) -> *mut c_void {
  //   match safety {
  //     DefinitionSafety::Unsafe => lean_box_fn(0),
  //     DefinitionSafety::Safe => lean_box_fn(1),
  //     DefinitionSafety::Partial => lean_box_fn(2),
  //   }
  // }
  //
  // /// Build QuotKind.
  // fn build_quot_kind(&self, kind: &QuotKind) -> *mut c_void {
  //   match kind {
  //     QuotKind::Type => lean_box_fn(0),
  //     QuotKind::Ctor => lean_box_fn(1),
  //     QuotKind::Lift => lean_box_fn(2),
  //     QuotKind::Ind => lean_box_fn(3),
  //   }
  // }

  /// Build a Ix.ConstantInfo from a Rust ConstantInfo.
  pub fn build_constant_info(&mut self, info: &ConstantInfo) -> *mut c_void {
    unsafe {
      match info {
        // | axiomInfo (v : AxiomVal) -- tag 0
        ConstantInfo::AxiomInfo(v) => {
          // AxiomVal = { cnst : ConstantVal, isUnsafe : Bool }
          let cnst_obj = self.build_constant_val(&v.cnst);
          let axiom_val = lean_alloc_ctor(0, 1, 1);
          lean_ctor_set(axiom_val, 0, cnst_obj);
          lean_ctor_set_uint8(axiom_val, 8, v.is_unsafe as u8);

          let obj = lean_alloc_ctor(0, 1, 0);
          lean_ctor_set(obj, 0, axiom_val);
          obj
        },
        // | defnInfo (v : DefinitionVal) -- tag 1
        ConstantInfo::DefnInfo(v) => {
          // DefinitionVal = { cnst, value, hints, safety, all }
          // NOTE: safety (DefinitionSafety) is a small enum stored as SCALAR
          // Memory layout: 4 obj fields (cnst, value, hints, all), 1 scalar byte (safety)
          let cnst_obj = self.build_constant_val(&v.cnst);
          let value_obj = self.build_expr(&v.value);
          let hints_obj = self.build_reducibility_hints(&v.hints);
          let all_obj = self.build_name_array(&v.all);
          let safety_byte = match v.safety {
            DefinitionSafety::Unsafe => 0u8,
            DefinitionSafety::Safe => 1u8,
            DefinitionSafety::Partial => 2u8,
          };

          let defn_val = lean_alloc_ctor(0, 4, 1);  // 4 obj fields, 1 scalar byte
          lean_ctor_set(defn_val, 0, cnst_obj);
          lean_ctor_set(defn_val, 1, value_obj);
          lean_ctor_set(defn_val, 2, hints_obj);
          lean_ctor_set(defn_val, 3, all_obj);
          lean_ctor_set_uint8(defn_val, 4 * 8, safety_byte);

          let obj = lean_alloc_ctor(1, 1, 0);
          lean_ctor_set(obj, 0, defn_val);
          obj
        },
        // | thmInfo (v : TheoremVal) -- tag 2
        ConstantInfo::ThmInfo(v) => {
          // TheoremVal = { cnst, value, all }
          let cnst_obj = self.build_constant_val(&v.cnst);
          let value_obj = self.build_expr(&v.value);
          let all_obj = self.build_name_array(&v.all);

          let thm_val = lean_alloc_ctor(0, 3, 0);
          lean_ctor_set(thm_val, 0, cnst_obj);
          lean_ctor_set(thm_val, 1, value_obj);
          lean_ctor_set(thm_val, 2, all_obj);

          let obj = lean_alloc_ctor(2, 1, 0);
          lean_ctor_set(obj, 0, thm_val);
          obj
        },
        // | opaqueInfo (v : OpaqueVal) -- tag 3
        ConstantInfo::OpaqueInfo(v) => {
          // OpaqueVal = { cnst, value, isUnsafe, all }
          let cnst_obj = self.build_constant_val(&v.cnst);
          let value_obj = self.build_expr(&v.value);
          let all_obj = self.build_name_array(&v.all);

          let opaque_val = lean_alloc_ctor(0, 3, 1);
          lean_ctor_set(opaque_val, 0, cnst_obj);
          lean_ctor_set(opaque_val, 1, value_obj);
          lean_ctor_set(opaque_val, 2, all_obj);
          lean_ctor_set_uint8(opaque_val, 3 * 8, v.is_unsafe as u8);

          let obj = lean_alloc_ctor(3, 1, 0);
          lean_ctor_set(obj, 0, opaque_val);
          obj
        },
        // | quotInfo (v : QuotVal) -- tag 4
        ConstantInfo::QuotInfo(v) => {
          // QuotVal = { cnst, kind }
          // NOTE: QuotKind is a small enum stored as SCALAR
          // Memory layout: 1 obj field (cnst), 1 scalar byte (kind)
          let cnst_obj = self.build_constant_val(&v.cnst);
          let kind_byte = match v.kind {
            QuotKind::Type => 0u8,
            QuotKind::Ctor => 1u8,
            QuotKind::Lift => 2u8,
            QuotKind::Ind => 3u8,
          };

          let quot_val = lean_alloc_ctor(0, 1, 1);  // 1 obj field, 1 scalar byte
          lean_ctor_set(quot_val, 0, cnst_obj);
          lean_ctor_set_uint8(quot_val, 1 * 8, kind_byte);

          let obj = lean_alloc_ctor(4, 1, 0);
          lean_ctor_set(obj, 0, quot_val);
          obj
        },
        // | inductInfo (v : InductiveVal) -- tag 5
        ConstantInfo::InductInfo(v) => {
          // InductiveVal = { cnst, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive }
          let cnst_obj = self.build_constant_val(&v.cnst);
          let num_params_obj = self.build_nat(&v.num_params);
          let num_indices_obj = self.build_nat(&v.num_indices);
          let all_obj = self.build_name_array(&v.all);
          let ctors_obj = self.build_name_array(&v.ctors);
          let num_nested_obj = self.build_nat(&v.num_nested);

          // 6 object fields, 3 scalar bytes for bools
          let induct_val = lean_alloc_ctor(0, 6, 3);
          lean_ctor_set(induct_val, 0, cnst_obj);
          lean_ctor_set(induct_val, 1, num_params_obj);
          lean_ctor_set(induct_val, 2, num_indices_obj);
          lean_ctor_set(induct_val, 3, all_obj);
          lean_ctor_set(induct_val, 4, ctors_obj);
          lean_ctor_set(induct_val, 5, num_nested_obj);
          lean_ctor_set_uint8(induct_val, 6 * 8, v.is_rec as u8);
          lean_ctor_set_uint8(induct_val, 6 * 8 + 1, v.is_unsafe as u8);
          lean_ctor_set_uint8(induct_val, 6 * 8 + 2, v.is_reflexive as u8);

          let obj = lean_alloc_ctor(5, 1, 0);
          lean_ctor_set(obj, 0, induct_val);
          obj
        },
        // | ctorInfo (v : ConstructorVal) -- tag 6
        ConstantInfo::CtorInfo(v) => {
          // ConstructorVal = { cnst, induct, cidx, numParams, numFields, isUnsafe }
          let cnst_obj = self.build_constant_val(&v.cnst);
          let induct_obj = self.build_name(&v.induct);
          let cidx_obj = self.build_nat(&v.cidx);
          let num_params_obj = self.build_nat(&v.num_params);
          let num_fields_obj = self.build_nat(&v.num_fields);

          // 5 object fields, 1 scalar byte for bool
          let ctor_val = lean_alloc_ctor(0, 5, 1);
          lean_ctor_set(ctor_val, 0, cnst_obj);
          lean_ctor_set(ctor_val, 1, induct_obj);
          lean_ctor_set(ctor_val, 2, cidx_obj);
          lean_ctor_set(ctor_val, 3, num_params_obj);
          lean_ctor_set(ctor_val, 4, num_fields_obj);
          lean_ctor_set_uint8(ctor_val, 5 * 8, v.is_unsafe as u8);

          let obj = lean_alloc_ctor(6, 1, 0);
          lean_ctor_set(obj, 0, ctor_val);
          obj
        },
        // | recInfo (v : RecursorVal) -- tag 7
        ConstantInfo::RecInfo(v) => {
          // RecursorVal = { cnst, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }
          let cnst_obj = self.build_constant_val(&v.cnst);
          let all_obj = self.build_name_array(&v.all);
          let num_params_obj = self.build_nat(&v.num_params);
          let num_indices_obj = self.build_nat(&v.num_indices);
          let num_motives_obj = self.build_nat(&v.num_motives);
          let num_minors_obj = self.build_nat(&v.num_minors);
          let rules_obj = self.build_recursor_rules(&v.rules);

          // 7 object fields, 2 scalar bytes for bools
          let rec_val = lean_alloc_ctor(0, 7, 2);
          lean_ctor_set(rec_val, 0, cnst_obj);
          lean_ctor_set(rec_val, 1, all_obj);
          lean_ctor_set(rec_val, 2, num_params_obj);
          lean_ctor_set(rec_val, 3, num_indices_obj);
          lean_ctor_set(rec_val, 4, num_motives_obj);
          lean_ctor_set(rec_val, 5, num_minors_obj);
          lean_ctor_set(rec_val, 6, rules_obj);
          lean_ctor_set_uint8(rec_val, 7 * 8, v.k as u8);
          lean_ctor_set_uint8(rec_val, 7 * 8 + 1, v.is_unsafe as u8);

          let obj = lean_alloc_ctor(7, 1, 0);
          lean_ctor_set(obj, 0, rec_val);
          obj
        },
      }
    }
  }

  /// Build an Array of RecursorRule.
  fn build_recursor_rules(
    &mut self,
    rules: &[crate::ix::env::RecursorRule],
  ) -> *mut c_void {
    unsafe {
      let arr = lean_alloc_array(rules.len(), rules.len());
      for (i, rule) in rules.iter().enumerate() {
        // RecursorRule = { ctor : Name, nFields : Nat, rhs : Expr }
        let ctor_obj = self.build_name(&rule.ctor);
        let n_fields_obj = self.build_nat(&rule.n_fields);
        let rhs_obj = self.build_expr(&rule.rhs);

        let rule_obj = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(rule_obj, 0, ctor_obj);
        lean_ctor_set(rule_obj, 1, n_fields_obj);
        lean_ctor_set(rule_obj, 2, rhs_obj);

        lean_array_set_core(arr, i, rule_obj);
      }
      arr
    }
  }
}

/// Convert BinderInfo to u8 tag.
fn binder_info_to_u8(bi: &BinderInfo) -> u8 {
  match bi {
    BinderInfo::Default => 0,
    BinderInfo::Implicit => 1,
    BinderInfo::StrictImplicit => 2,
    BinderInfo::InstImplicit => 3,
  }
}

// =============================================================================
// HashMap Building
// =============================================================================

/// Build a Lean HashMap from pre-built key-value pairs.
///
/// Lean's Std.HashMap structure (with unboxing):
/// - HashMap α β unboxes through DHashMap to Raw
/// - Raw = { size : Nat, buckets : Array (AssocList α β) }
/// - Field 0 = size (Nat), Field 1 = buckets (Array)
///
/// AssocList α β = nil | cons (key : α) (value : β) (tail : AssocList α β)
fn build_hashmap_from_pairs(
  pairs: Vec<(*mut c_void, *mut c_void, u64)>, // (key_obj, val_obj, hash)
) -> *mut c_void {
  let size = pairs.len();
  let bucket_count = (size * 4 / 3 + 1).next_power_of_two().max(8);

  unsafe {
    // Create array of AssocLists (initially all nil = boxed 0)
    let buckets = lean_alloc_array(bucket_count, bucket_count);
    for i in 0..bucket_count {
      lean_array_set_core(buckets, i, lean_box_fn(0)); // nil
    }

    // Insert entries
    for (key_obj, val_obj, hash) in pairs {
      let bucket_idx = (hash as usize) % bucket_count;

      // Get current bucket (AssocList)
      let buckets_arr = buckets as *mut crate::lean::array::LeanArrayObject;
      let current_tail = (*buckets_arr).data()[bucket_idx];

      // cons (key : α) (value : β) (tail : AssocList α β) -- tag 1
      let cons = lean_alloc_ctor(1, 3, 0);
      lean_ctor_set(cons, 0, key_obj);
      lean_ctor_set(cons, 1, val_obj);
      lean_ctor_set(cons, 2, current_tail as *mut c_void);

      lean_array_set_core(buckets, bucket_idx, cons);
    }

    // Build Raw { size : Nat, buckets : Array }
    // Due to unboxing, this IS the HashMap directly
    // Field 0 = size, Field 1 = buckets (2 object fields, no scalars)
    let size_obj = if size <= (usize::MAX >> 1) {
      lean_box_fn(size)
    } else {
      lean_uint64_to_nat(size as u64)
    };

    let raw = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(raw, 0, size_obj);
    lean_ctor_set(raw, 1, buckets);
    raw
  }
}

// =============================================================================
// Environment Building
// =============================================================================

impl IxEnvBuilder {
  /// Build a Ix.RawEnvironment from collected caches.
  /// RawEnvironment has arrays that Lean will convert to HashMaps.
  ///
  /// Ix.RawEnvironment = {
  ///   consts : Array (Name × ConstantInfo)
  /// }
  ///
  /// NOTE: RawEnvironment with a single field is UNBOXED by Lean,
  /// so we return just the array, not a structure containing it.
  pub fn build_raw_environment(
    &mut self,
    consts: &FxHashMap<Name, ConstantInfo>,
  ) -> *mut c_void {
    unsafe {
      // Build consts array: Array (Name × ConstantInfo)
      // Since RawEnvironment is unboxed, the array IS the RawEnvironment
      let consts_arr = lean_alloc_array(consts.len(), consts.len());
      for (i, (name, info)) in consts.iter().enumerate() {
        let key_obj = self.build_name(name);
        let val_obj = self.build_constant_info(info);
        // Build pair (Name × ConstantInfo)
        let pair = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(pair, 0, key_obj);
        lean_ctor_set(pair, 1, val_obj);
        lean_array_set_core(consts_arr, i, pair);
      }

      consts_arr
    }
  }
}

// =============================================================================
// FFI Function
// =============================================================================

use crate::ix::env::Env;
use crate::lean::ffi::lean_env::lean_ptr_to_env;
use crate::lean::lean_io_result_mk_ok;

/// FFI function to canonicalize a Lean environment and return Ix.Environment.
///
/// Takes: List (Lean.Name × Lean.ConstantInfo)
/// Returns: IO Ix.Environment
#[unsafe(no_mangle)]
pub extern "C" fn rs_canonicalize_env_to_ix(
  env_consts_ptr: *const c_void,
) -> *mut c_void {
  use std::time::Instant;
  let total_start = Instant::now();

  // Phase 1: Decode Lean environment into Rust Env
  eprintln!("[Rust] Phase 1: Decoding Lean environment...");
  let decode_start = Instant::now();
  let rust_env = lean_ptr_to_env(env_consts_ptr);
  eprintln!("[Rust]   Decoded {} constants in {:.2}s",
    rust_env.len(), decode_start.elapsed().as_secs_f64());

  // Phase 2: Build Ix.RawEnvironment using C API
  eprintln!("[Rust] Phase 2: Building Ix.RawEnvironment...");
  let build_start = Instant::now();
  let mut builder = IxEnvBuilder::with_capacity(rust_env.len());
  let ix_env = builder.build_raw_environment(&rust_env);
  eprintln!("[Rust]   Built Ix.RawEnvironment in {:.2}s", build_start.elapsed().as_secs_f64());

  eprintln!("[Rust] Total time: {:.2}s", total_start.elapsed().as_secs_f64());

  // Wrap in IO result
  unsafe { lean_io_result_mk_ok(ix_env) }
}

// =============================================================================
// Utility FFI Functions
// =============================================================================

/// Read first 8 bytes of a ByteArray as little-endian UInt64.
/// Used by Address.Hashable to match Rust's bucket hash computation.
/// This is essentially just a pointer cast - very fast.
#[unsafe(no_mangle)]
pub extern "C" fn rs_bytearray_to_u64_le(ba_ptr: *const c_void) -> u64 {
  unsafe {
    // ByteArray layout: header followed by data bytes
    // lean_sarray_cptr gives us the pointer to the data
    let data_ptr = lean_sarray_cptr(ba_ptr as *mut _);
    // Direct cast - assumes little-endian platform and at least 8 bytes
    *(data_ptr as *const u64)
  }
}

// =============================================================================
// Round-trip FFI Functions for Testing
// =============================================================================

use crate::lean::string::LeanStringObject;
use crate::lean::array::LeanArrayObject;

/// Round-trip a Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_nat(nat_ptr: *const c_void) -> *mut c_void {
  // Decode
  let nat = crate::lean::nat::Nat::from_ptr(nat_ptr);
  // Re-encode
  build_nat_standalone(&nat)
}

/// Round-trip a String: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_string(s_ptr: *const c_void) -> *mut c_void {
  // Decode
  let s_obj: &LeanStringObject = crate::lean::as_ref_unsafe(s_ptr.cast());
  let s = s_obj.as_string();
  // Re-encode
  unsafe {
    let cstr = CString::new(s.as_str()).unwrap();
    lean_mk_string(cstr.as_ptr())
  }
}

/// Round-trip a List Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_list_nat(list_ptr: *const c_void) -> *mut c_void {
  // Decode list to Vec<Nat>
  let nats: Vec<crate::lean::nat::Nat> =
    crate::lean::collect_list(list_ptr, crate::lean::nat::Nat::from_ptr);
  // Re-encode as Lean List
  build_list_nat(&nats)
}

/// Round-trip an Array Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_array_nat(arr_ptr: *const c_void) -> *mut c_void {
  // Decode array
  let arr_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(arr_ptr.cast());
  let nats: Vec<crate::lean::nat::Nat> = arr_obj
    .data()
    .iter()
    .map(|&p| crate::lean::nat::Nat::from_ptr(p))
    .collect();
  // Re-encode as Lean Array
  build_array_nat(&nats)
}

/// Round-trip a ByteArray: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_bytearray(ba_ptr: *const c_void) -> *mut c_void {
  // Decode ByteArray (scalar array of u8)
  let sarray: &crate::lean::sarray::LeanSArrayObject =
    crate::lean::as_ref_unsafe(ba_ptr.cast());
  let bytes = sarray.data();
  // Re-encode
  unsafe {
    let ba = lean_alloc_sarray(1, bytes.len(), bytes.len());
    let data_ptr = lean_sarray_cptr(ba);
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, bytes.len());
    ba
  }
}

// =============================================================================
// Helper functions for building basic Lean types
// =============================================================================

/// Build a Lean Nat from a Rust Nat (standalone version without IxEnvBuilder).
fn build_nat_standalone(n: &crate::lean::nat::Nat) -> *mut c_void {
  // Try to get as u64 first
  if let Some(val) = n.to_u64() {
    // For small values that fit in a boxed scalar (max value is usize::MAX >> 1)
    if val <= (usize::MAX >> 1) as u64 {
      return lean_box_fn(val as usize);
    }
    // For larger u64 values, use lean_uint64_to_nat
    return unsafe { lean_uint64_to_nat(val) };
  }
  // For values larger than u64, convert to limbs and use GMP
  let bytes = n.to_le_bytes();
  let mut limbs: Vec<u64> = Vec::with_capacity((bytes.len() + 7) / 8);
  for chunk in bytes.chunks(8) {
    let mut arr = [0u8; 8];
    arr[..chunk.len()].copy_from_slice(chunk);
    limbs.push(u64::from_le_bytes(arr));
  }
  unsafe { crate::lean::lean_nat_from_limbs(limbs.len(), limbs.as_ptr()) }
}

/// Build a Lean List Nat from a Vec<Nat>.
fn build_list_nat(nats: &[crate::lean::nat::Nat]) -> *mut c_void {
  unsafe {
    // Build list in reverse (cons builds from the end)
    let mut list = lean_box_fn(0); // nil
    for nat in nats.iter().rev() {
      let nat_obj = build_nat_standalone(nat);
      // cons : α → List α → List α (tag 1, 2 object fields)
      let cons = lean_alloc_ctor(1, 2, 0);
      lean_ctor_set(cons, 0, nat_obj);
      lean_ctor_set(cons, 1, list);
      list = cons;
    }
    list
  }
}

/// Build a Lean Array Nat from a Vec<Nat>.
fn build_array_nat(nats: &[crate::lean::nat::Nat]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(nats.len(), nats.len());
    for (i, nat) in nats.iter().enumerate() {
      let nat_obj = build_nat_standalone(nat);
      lean_array_set_core(arr, i, nat_obj);
    }
    arr
  }
}

// =============================================================================
// FFI roundtrip functions for struct/inductive/HashMap
// =============================================================================

/// Round-trip a Point (structure with x, y : Nat).
/// Point is a structure, which in Lean is represented as a constructor with tag 0.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_point(point_ptr: *const c_void) -> *mut c_void {
  unsafe {
    // Point is a structure (single constructor, tag 0) with 2 Nat fields
    let x_ptr = lean_ctor_get(point_ptr as *mut _, 0);
    let y_ptr = lean_ctor_get(point_ptr as *mut _, 1);

    // Decode the Nats
    let x = crate::lean::nat::Nat::from_ptr(x_ptr);
    let y = crate::lean::nat::Nat::from_ptr(y_ptr);

    // Re-encode as Point
    let point = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(point, 0, build_nat_standalone(&x));
    lean_ctor_set(point, 1, build_nat_standalone(&y));
    point
  }
}

/// Round-trip a NatTree (inductive with leaf : Nat → NatTree | node : NatTree → NatTree → NatTree).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_nat_tree(tree_ptr: *const c_void) -> *mut c_void {
  roundtrip_nat_tree_recursive(tree_ptr)
}

fn roundtrip_nat_tree_recursive(tree_ptr: *const c_void) -> *mut c_void {
  unsafe {
    let tag = lean_obj_tag(tree_ptr as *mut _);
    match tag {
      0 => {
        // leaf : Nat → NatTree
        let nat_ptr = lean_ctor_get(tree_ptr as *mut _, 0);
        let nat = crate::lean::nat::Nat::from_ptr(nat_ptr);
        let leaf = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leaf, 0, build_nat_standalone(&nat));
        leaf
      }
      1 => {
        // node : NatTree → NatTree → NatTree
        let left_ptr = lean_ctor_get(tree_ptr as *mut _, 0);
        let right_ptr = lean_ctor_get(tree_ptr as *mut _, 1);
        let left = roundtrip_nat_tree_recursive(left_ptr);
        let right = roundtrip_nat_tree_recursive(right_ptr);
        let node = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(node, 0, left);
        lean_ctor_set(node, 1, right);
        node
      }
      _ => panic!("Invalid NatTree tag: {}", tag),
    }
  }
}

/// Round-trip an AssocList Nat Nat.
/// AssocList: nil (tag 0, 0 fields) | cons key value tail (tag 1, 3 fields)
/// Note: nil with 0 fields may be represented as lean_box(0)
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_assoclist_nat_nat(list_ptr: *const c_void) -> *mut c_void {
  // Check if it's a scalar (nil represented as lean_box(0))
  if lean_is_scalar(list_ptr) {
    // Return lean_box(0) for nil
    return lean_box_fn(0);
  }
  let pairs = decode_assoc_list_nat_nat(list_ptr);
  build_assoc_list_nat_nat(&pairs)
}

/// Build an AssocList Nat Nat from pairs
fn build_assoc_list_nat_nat(pairs: &[(crate::lean::nat::Nat, crate::lean::nat::Nat)]) -> *mut c_void {
  unsafe {
    // Build in reverse to preserve order
    // AssocList.nil with 0 fields is represented as lean_box(0)
    let mut list = lean_box_fn(0);
    for (k, v) in pairs.iter().rev() {
      let cons = lean_alloc_ctor(1, 3, 0); // AssocList.cons
      lean_ctor_set(cons, 0, build_nat_standalone(k));
      lean_ctor_set(cons, 1, build_nat_standalone(v));
      lean_ctor_set(cons, 2, list);
      list = cons;
    }
    list
  }
}

/// Round-trip a DHashMap.Raw Nat Nat.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_dhashmap_raw_nat_nat(raw_ptr: *const c_void) -> *mut c_void {
  unsafe {
    if lean_is_scalar(raw_ptr) {
      return raw_ptr as *mut c_void;
    }

    let size_ptr = lean_ctor_get(raw_ptr as *mut _, 0);
    let buckets_ptr = lean_ctor_get(raw_ptr as *mut _, 1);

    let size = crate::lean::nat::Nat::from_ptr(size_ptr);

    // Decode and rebuild buckets
    let buckets_obj: &crate::lean::array::LeanArrayObject =
      crate::lean::as_ref_unsafe(buckets_ptr.cast());
    let num_buckets = buckets_obj.data().len();

    let mut all_pairs: Vec<(crate::lean::nat::Nat, crate::lean::nat::Nat)> = Vec::new();
    for &bucket_ptr in buckets_obj.data() {
      let pairs = decode_assoc_list_nat_nat(bucket_ptr);
      all_pairs.extend(pairs);
    }

    // Rebuild buckets
    let new_buckets = lean_alloc_array(num_buckets, num_buckets);
    for i in 0..num_buckets {
      lean_array_set_core(new_buckets, i, lean_box_fn(0)); // AssocList.nil
    }

    for (k, v) in &all_pairs {
      let k_u64 = k.to_u64().unwrap_or_else(|| {
        let bytes = k.to_le_bytes();
        let mut arr = [0u8; 8];
        let len = bytes.len().min(8);
        arr[..len].copy_from_slice(&bytes[..len]);
        u64::from_le_bytes(arr)
      });
      let bucket_idx = (k_u64 as usize) & (num_buckets - 1);

      let old_bucket = lean_array_get_core(new_buckets, bucket_idx) as *mut c_void;
      let new_bucket = lean_alloc_ctor(1, 3, 0);
      lean_ctor_set(new_bucket, 0, build_nat_standalone(k));
      lean_ctor_set(new_bucket, 1, build_nat_standalone(v));
      lean_ctor_set(new_bucket, 2, old_bucket);
      lean_array_set_core(new_buckets, bucket_idx, new_bucket);
    }

    // Build Raw
    let raw = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(raw, 0, build_nat_standalone(&size));
    lean_ctor_set(raw, 1, new_buckets);

    raw
  }
}

/// Round-trip a Std.HashMap Nat Nat.
///
/// IMPORTANT: Single-field structures are unboxed in Lean 4!
/// - HashMap has 1 field (inner : DHashMap)
/// - DHashMap has 1 field (inner : Raw) - wf : Prop is erased
/// So HashMap pointer points DIRECTLY to Raw!
///
/// Memory layout (after unboxing):
/// - HashMap/DHashMap/Raw all share the same pointer
/// - Raw: ctor 0, 2 fields
///   - field 0: size : Nat
///   - field 1: buckets : Array (AssocList α β)
/// - AssocList:
///   - nil: lean_box(0)
///   - cons key value tail: ctor 1, 3 fields
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_hashmap_nat_nat(map_ptr: *const c_void) -> *mut c_void {
  unsafe {
    // Due to unboxing, map_ptr points directly to Raw
    let size_ptr = lean_ctor_get(map_ptr as *mut _, 0);
    let buckets_ptr = lean_ctor_get(map_ptr as *mut _, 1);

    let size = crate::lean::nat::Nat::from_ptr(size_ptr);

    // Decode buckets (Array of AssocLists)
    let buckets_obj: &crate::lean::array::LeanArrayObject =
      crate::lean::as_ref_unsafe(buckets_ptr.cast());
    let mut pairs: Vec<(crate::lean::nat::Nat, crate::lean::nat::Nat)> = Vec::new();

    for &bucket_ptr in buckets_obj.data() {
      // Each bucket is an AssocList
      let bucket_pairs = decode_assoc_list_nat_nat(bucket_ptr);
      pairs.extend(bucket_pairs);
    }

    // Rebuild the HashMap with the same bucket count
    let num_buckets = buckets_obj.data().len();
    let new_buckets = lean_alloc_array(num_buckets, num_buckets);

    // Initialize all buckets to AssocList.nil (lean_box(0))
    for i in 0..num_buckets {
      lean_array_set_core(new_buckets, i, lean_box_fn(0)); // AssocList.nil
    }

    // Insert each pair into the appropriate bucket using Lean's hash function
    for (k, v) in &pairs {
      // Hash the key - for Nat, Lean uses the value itself as hash
      let k_u64 = k.to_u64().unwrap_or_else(|| {
        // For large nats, use low 64 bits
        let bytes = k.to_le_bytes();
        let mut arr = [0u8; 8];
        let len = bytes.len().min(8);
        arr[..len].copy_from_slice(&bytes[..len]);
        u64::from_le_bytes(arr)
      });
      // Lean uses (hash & (buckets.size - 1)) for bucket index (power of 2)
      let bucket_idx = (k_u64 as usize) & (num_buckets - 1);

      // Get current bucket AssocList
      let old_bucket = lean_array_get_core(new_buckets, bucket_idx) as *mut c_void;

      // Build AssocList.cons key value tail (tag 1, 3 fields)
      let new_bucket = lean_alloc_ctor(1, 3, 0);
      lean_ctor_set(new_bucket, 0, build_nat_standalone(k));
      lean_ctor_set(new_bucket, 1, build_nat_standalone(v));
      lean_ctor_set(new_bucket, 2, old_bucket);

      lean_array_set_core(new_buckets, bucket_idx, new_bucket);
    }

    // Build Raw (ctor 0, 2 fields: size, buckets)
    // Due to unboxing, this IS the HashMap
    let raw = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(raw, 0, build_nat_standalone(&size));
    lean_ctor_set(raw, 1, new_buckets);

    raw
  }
}

/// Decode a Lean AssocList Nat Nat to Vec of pairs
/// AssocList: nil (tag 0) | cons key value tail (tag 1, 3 fields)
fn decode_assoc_list_nat_nat(
  list_ptr: *const c_void,
) -> Vec<(crate::lean::nat::Nat, crate::lean::nat::Nat)> {
  let mut result = Vec::new();
  let mut current = list_ptr;

  loop {
    unsafe {
      // Check if scalar (shouldn't happen) or object
      if lean_is_scalar(current) {
        break;
      }

      let tag = lean_obj_tag(current as *mut _);
      if tag == 0 {
        // AssocList.nil
        break;
      }

      // AssocList.cons: 3 fields (key, value, tail)
      let key_ptr = lean_ctor_get(current as *mut _, 0);
      let value_ptr = lean_ctor_get(current as *mut _, 1);
      let tail_ptr = lean_ctor_get(current as *mut _, 2);

      let k = crate::lean::nat::Nat::from_ptr(key_ptr);
      let v = crate::lean::nat::Nat::from_ptr(value_ptr);

      result.push((k, v));
      current = tail_ptr;
    }
  }

  result
}

// =============================================================================
// Ix Type Roundtrip FFI Functions
// =============================================================================
//
// These functions roundtrip Ix types (canonical types with embedded hashes):
// - Ix.Name: anonymous | str (parent, s, hash) | num (parent, i, hash)
// - Ix.Level: zero | succ | max | imax | param | mvar (each with hash)
// - Ix.Expr: 12 variants (each with hash)
//
// The pattern: decode Lean Ix type → Rust env type → rebuild via IxEnvBuilder
// =============================================================================

/// Decode a Lean Ix.Name to Rust Name.
///
/// Ix.Name layout:
/// - Tag 0: anonymous (hash : Address)
/// - Tag 1: str (parent : Name) (s : String) (hash : Address)
/// - Tag 2: num (parent : Name) (i : Nat) (hash : Address)
fn decode_ix_name(ptr: *const c_void) -> Name {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // anonymous: just has hash, construct anon Name
        Name::anon()
      }
      1 => {
        // str: parent, s, hash
        let parent_ptr = lean_ctor_get(ptr as *mut _, 0);
        let s_ptr = lean_ctor_get(ptr as *mut _, 1);
        // hash at field 2 is ignored - Rust recomputes it

        let parent = decode_ix_name(parent_ptr);
        let s_obj: &LeanStringObject = crate::lean::as_ref_unsafe(s_ptr.cast());
        let s = s_obj.as_string();

        Name::str(parent, s)
      }
      2 => {
        // num: parent, i, hash
        let parent_ptr = lean_ctor_get(ptr as *mut _, 0);
        let i_ptr = lean_ctor_get(ptr as *mut _, 1);
        // hash at field 2 is ignored

        let parent = decode_ix_name(parent_ptr);
        let i = crate::lean::nat::Nat::from_ptr(i_ptr);

        Name::num(parent, i)
      }
      _ => panic!("Invalid Ix.Name tag: {}", tag),
    }
  }
}

/// Decode a Lean Ix.Level to Rust Level.
///
/// Ix.Level layout:
/// - Tag 0: zero (hash : Address)
/// - Tag 1: succ (x : Level) (hash : Address)
/// - Tag 2: max (x y : Level) (hash : Address)
/// - Tag 3: imax (x y : Level) (hash : Address)
/// - Tag 4: param (n : Name) (hash : Address)
/// - Tag 5: mvar (n : Name) (hash : Address)
fn decode_ix_level(ptr: *const c_void) -> Level {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => Level::zero(),
      1 => {
        let x_ptr = lean_ctor_get(ptr as *mut _, 0);
        let x = decode_ix_level(x_ptr);
        Level::succ(x)
      }
      2 => {
        let x_ptr = lean_ctor_get(ptr as *mut _, 0);
        let y_ptr = lean_ctor_get(ptr as *mut _, 1);
        let x = decode_ix_level(x_ptr);
        let y = decode_ix_level(y_ptr);
        Level::max(x, y)
      }
      3 => {
        let x_ptr = lean_ctor_get(ptr as *mut _, 0);
        let y_ptr = lean_ctor_get(ptr as *mut _, 1);
        let x = decode_ix_level(x_ptr);
        let y = decode_ix_level(y_ptr);
        Level::imax(x, y)
      }
      4 => {
        let n_ptr = lean_ctor_get(ptr as *mut _, 0);
        let n = decode_ix_name(n_ptr);
        Level::param(n)
      }
      5 => {
        let n_ptr = lean_ctor_get(ptr as *mut _, 0);
        let n = decode_ix_name(n_ptr);
        Level::mvar(n)
      }
      _ => panic!("Invalid Ix.Level tag: {}", tag),
    }
  }
}

/// Decode a Lean Ix.Expr to Rust Expr.
///
/// Ix.Expr layout (12 constructors):
/// - Tag 0: bvar (idx : Nat) (hash : Address)
/// - Tag 1: fvar (name : Name) (hash : Address)
/// - Tag 2: mvar (name : Name) (hash : Address)
/// - Tag 3: sort (level : Level) (hash : Address)
/// - Tag 4: const (name : Name) (levels : Array Level) (hash : Address)
/// - Tag 5: app (fn arg : Expr) (hash : Address)
/// - Tag 6: lam (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address) - 4 obj + 1 scalar
/// - Tag 7: forallE (name : Name) (ty body : Expr) (bi : BinderInfo) (hash : Address) - 4 obj + 1 scalar
/// - Tag 8: letE (name : Name) (ty val body : Expr) (nonDep : Bool) (hash : Address) - 5 obj + 1 scalar
/// - Tag 9: lit (l : Literal) (hash : Address)
/// - Tag 10: mdata (data : Array (Name × DataValue)) (expr : Expr) (hash : Address)
/// - Tag 11: proj (typeName : Name) (idx : Nat) (struct : Expr) (hash : Address)
fn decode_ix_expr(ptr: *const c_void) -> Expr {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // bvar
        let idx_ptr = lean_ctor_get(ptr as *mut _, 0);
        let idx = crate::lean::nat::Nat::from_ptr(idx_ptr);
        Expr::bvar(idx)
      }
      1 => {
        // fvar
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let name = decode_ix_name(name_ptr);
        Expr::fvar(name)
      }
      2 => {
        // mvar
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let name = decode_ix_name(name_ptr);
        Expr::mvar(name)
      }
      3 => {
        // sort
        let level_ptr = lean_ctor_get(ptr as *mut _, 0);
        let level = decode_ix_level(level_ptr);
        Expr::sort(level)
      }
      4 => {
        // const
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let levels_ptr = lean_ctor_get(ptr as *mut _, 1);

        let name = decode_ix_name(name_ptr);
        let levels_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(levels_ptr.cast());
        let levels: Vec<Level> = levels_obj
          .data()
          .iter()
          .map(|&p| decode_ix_level(p))
          .collect();

        Expr::cnst(name, levels)
      }
      5 => {
        // app
        let fn_ptr = lean_ctor_get(ptr as *mut _, 0);
        let arg_ptr = lean_ctor_get(ptr as *mut _, 1);
        let fn_expr = decode_ix_expr(fn_ptr);
        let arg_expr = decode_ix_expr(arg_ptr);
        Expr::app(fn_expr, arg_expr)
      }
      6 => {
        // lam: name, ty, body, hash, bi (scalar)
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_ptr = lean_ctor_get(ptr as *mut _, 1);
        let body_ptr = lean_ctor_get(ptr as *mut _, 2);
        // hash at field 3
        // bi is a scalar byte at offset 4*8

        let name = decode_ix_name(name_ptr);
        let ty = decode_ix_expr(ty_ptr);
        let body = decode_ix_expr(body_ptr);

        // Read BinderInfo scalar (4 obj fields: name, ty, body, hash)
        let ctor: &crate::lean::ctor::LeanCtorObject = crate::lean::as_ref_unsafe(ptr.cast());
        let bi_byte = ctor.get_scalar_u8(4, 0);
        let bi = match bi_byte {
          0 => BinderInfo::Default,
          1 => BinderInfo::Implicit,
          2 => BinderInfo::StrictImplicit,
          3 => BinderInfo::InstImplicit,
          _ => panic!("Invalid BinderInfo: {}", bi_byte),
        };

        Expr::lam(name, ty, body, bi)
      }
      7 => {
        // forallE: same layout as lam
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_ptr = lean_ctor_get(ptr as *mut _, 1);
        let body_ptr = lean_ctor_get(ptr as *mut _, 2);

        let name = decode_ix_name(name_ptr);
        let ty = decode_ix_expr(ty_ptr);
        let body = decode_ix_expr(body_ptr);

        // 4 obj fields: name, ty, body, hash
        let ctor: &crate::lean::ctor::LeanCtorObject = crate::lean::as_ref_unsafe(ptr.cast());
        let bi_byte = ctor.get_scalar_u8(4, 0);
        let bi = match bi_byte {
          0 => BinderInfo::Default,
          1 => BinderInfo::Implicit,
          2 => BinderInfo::StrictImplicit,
          3 => BinderInfo::InstImplicit,
          _ => panic!("Invalid BinderInfo: {}", bi_byte),
        };

        Expr::all(name, ty, body, bi)
      }
      8 => {
        // letE: name, ty, val, body, hash, nonDep (scalar)
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let ty_ptr = lean_ctor_get(ptr as *mut _, 1);
        let val_ptr = lean_ctor_get(ptr as *mut _, 2);
        let body_ptr = lean_ctor_get(ptr as *mut _, 3);
        // hash at field 4
        // nonDep is scalar byte after 5 obj fields

        let name = decode_ix_name(name_ptr);
        let ty = decode_ix_expr(ty_ptr);
        let val = decode_ix_expr(val_ptr);
        let body = decode_ix_expr(body_ptr);

        // 5 obj fields: name, ty, val, body, hash
        let ctor: &crate::lean::ctor::LeanCtorObject = crate::lean::as_ref_unsafe(ptr.cast());
        let non_dep = ctor.get_scalar_u8(5, 0) != 0;

        Expr::letE(name, ty, val, body, non_dep)
      }
      9 => {
        // lit
        let lit_ptr = lean_ctor_get(ptr as *mut _, 0);
        let lit = decode_literal(lit_ptr);
        Expr::lit(lit)
      }
      10 => {
        // mdata: data, expr, hash
        let data_ptr = lean_ctor_get(ptr as *mut _, 0);
        let expr_ptr = lean_ctor_get(ptr as *mut _, 1);

        let data_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(data_ptr.cast());
        let data: Vec<(Name, DataValue)> = data_obj
          .data()
          .iter()
          .map(|&p| decode_name_data_value(p))
          .collect();

        let inner = decode_ix_expr(expr_ptr);
        Expr::mdata(data, inner)
      }
      11 => {
        // proj: typeName, idx, struct, hash
        let type_name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let idx_ptr = lean_ctor_get(ptr as *mut _, 1);
        let struct_ptr = lean_ctor_get(ptr as *mut _, 2);

        let type_name = decode_ix_name(type_name_ptr);
        let idx = crate::lean::nat::Nat::from_ptr(idx_ptr);
        let struct_expr = decode_ix_expr(struct_ptr);

        Expr::proj(type_name, idx, struct_expr)
      }
      _ => panic!("Invalid Ix.Expr tag: {}", tag),
    }
  }
}

/// Decode Lean.Literal from a Lean pointer.
fn decode_literal(ptr: *const c_void) -> Literal {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // natVal
        let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
        let nat = crate::lean::nat::Nat::from_ptr(nat_ptr);
        Literal::NatVal(nat)
      }
      1 => {
        // strVal
        let str_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_obj: &LeanStringObject = crate::lean::as_ref_unsafe(str_ptr.cast());
        Literal::StrVal(str_obj.as_string())
      }
      _ => panic!("Invalid Literal tag: {}", tag),
    }
  }
}

/// Decode a (Name × DataValue) pair for mdata.
fn decode_name_data_value(ptr: *const c_void) -> (Name, DataValue) {
  unsafe {
    // Prod: ctor 0 with 2 fields
    let name_ptr = lean_ctor_get(ptr as *mut _, 0);
    let dv_ptr = lean_ctor_get(ptr as *mut _, 1);

    let name = decode_ix_name(name_ptr);
    let dv = decode_data_value(dv_ptr);

    (name, dv)
  }
}

/// Decode Ix.DataValue from a Lean pointer.
fn decode_data_value(ptr: *const c_void) -> DataValue {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);

    match tag {
      0 => {
        // ofString: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        let str_obj: &LeanStringObject = crate::lean::as_ref_unsafe(inner_ptr.cast());
        DataValue::OfString(str_obj.as_string())
      }
      1 => {
        // ofBool: 0 object fields, 1 scalar byte
        let ctor: &crate::lean::ctor::LeanCtorObject = crate::lean::as_ref_unsafe(ptr.cast());
        let b = ctor.get_scalar_u8(0, 0) != 0;
        DataValue::OfBool(b)
      }
      2 => {
        // ofName: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        DataValue::OfName(decode_ix_name(inner_ptr))
      }
      3 => {
        // ofNat: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        DataValue::OfNat(crate::lean::nat::Nat::from_ptr(inner_ptr))
      }
      4 => {
        // ofInt: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        let int_tag = lean_obj_tag(inner_ptr as *mut _);
        let nat_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let nat = crate::lean::nat::Nat::from_ptr(nat_ptr);
        match int_tag {
          0 => DataValue::OfInt(Int::OfNat(nat)),
          1 => DataValue::OfInt(Int::NegSucc(nat)),
          _ => panic!("Invalid Int tag: {}", int_tag),
        }
      }
      5 => {
        // ofSyntax: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        DataValue::OfSyntax(decode_ix_syntax(inner_ptr).into())
      }
      _ => panic!("Invalid DataValue tag: {}", tag),
    }
  }
}

/// Decode Ix.Syntax from a Lean pointer.
fn decode_ix_syntax(ptr: *const c_void) -> Syntax {
  unsafe {
    if lean_is_scalar(ptr) {
      return Syntax::Missing;
    }
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => Syntax::Missing,
      1 => {
        // node: info, kind, args
        let info_ptr = lean_ctor_get(ptr as *mut _, 0);
        let kind_ptr = lean_ctor_get(ptr as *mut _, 1);
        let args_ptr = lean_ctor_get(ptr as *mut _, 2);

        let info = decode_ix_source_info(info_ptr);
        let kind = decode_ix_name(kind_ptr);
        let args_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(args_ptr.cast());
        let args: Vec<Syntax> = args_obj
          .data()
          .iter()
          .map(|&p| decode_ix_syntax(p))
          .collect();

        Syntax::Node(info, kind, args)
      }
      2 => {
        // atom: info, val
        let info_ptr = lean_ctor_get(ptr as *mut _, 0);
        let val_ptr = lean_ctor_get(ptr as *mut _, 1);

        let info = decode_ix_source_info(info_ptr);
        let val_obj: &LeanStringObject = crate::lean::as_ref_unsafe(val_ptr.cast());

        Syntax::Atom(info, val_obj.as_string())
      }
      3 => {
        // ident: info, rawVal, val, preresolved
        let info_ptr = lean_ctor_get(ptr as *mut _, 0);
        let raw_val_ptr = lean_ctor_get(ptr as *mut _, 1);
        let val_ptr = lean_ctor_get(ptr as *mut _, 2);
        let preresolved_ptr = lean_ctor_get(ptr as *mut _, 3);

        let info = decode_ix_source_info(info_ptr);
        let raw_val = decode_substring(raw_val_ptr);
        let val = decode_ix_name(val_ptr);
        let preresolved_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(preresolved_ptr.cast());
        let preresolved: Vec<SyntaxPreresolved> = preresolved_obj
          .data()
          .iter()
          .map(|&p| decode_syntax_preresolved(p))
          .collect();

        Syntax::Ident(info, raw_val, val, preresolved)
      }
      _ => panic!("Invalid Syntax tag: {}", tag),
    }
  }
}

/// Decode Ix.SourceInfo.
fn decode_ix_source_info(ptr: *const c_void) -> SourceInfo {
  unsafe {
    if lean_is_scalar(ptr) {
      return SourceInfo::None;
    }
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // original
        let leading_ptr = lean_ctor_get(ptr as *mut _, 0);
        let pos_ptr = lean_ctor_get(ptr as *mut _, 1);
        let trailing_ptr = lean_ctor_get(ptr as *mut _, 2);
        let end_pos_ptr = lean_ctor_get(ptr as *mut _, 3);

        SourceInfo::Original(
          decode_substring(leading_ptr),
          crate::lean::nat::Nat::from_ptr(pos_ptr),
          decode_substring(trailing_ptr),
          crate::lean::nat::Nat::from_ptr(end_pos_ptr),
        )
      }
      1 => {
        // synthetic: 2 obj fields (pos, end_pos), 1 scalar byte (canonical)
        let pos_ptr = lean_ctor_get(ptr as *mut _, 0);
        let end_pos_ptr = lean_ctor_get(ptr as *mut _, 1);

        let ctor: &crate::lean::ctor::LeanCtorObject = crate::lean::as_ref_unsafe(ptr.cast());
        let canonical = ctor.get_scalar_u8(2, 0) != 0;

        SourceInfo::Synthetic(
          crate::lean::nat::Nat::from_ptr(pos_ptr),
          crate::lean::nat::Nat::from_ptr(end_pos_ptr),
          canonical,
        )
      }
      2 => SourceInfo::None,
      _ => panic!("Invalid SourceInfo tag: {}", tag),
    }
  }
}

/// Decode Ix.Substring.
fn decode_substring(ptr: *const c_void) -> Substring {
  unsafe {
    let str_ptr = lean_ctor_get(ptr as *mut _, 0);
    let start_ptr = lean_ctor_get(ptr as *mut _, 1);
    let stop_ptr = lean_ctor_get(ptr as *mut _, 2);

    let str_obj: &LeanStringObject = crate::lean::as_ref_unsafe(str_ptr.cast());
    Substring {
      str: str_obj.as_string(),
      start_pos: crate::lean::nat::Nat::from_ptr(start_ptr),
      stop_pos: crate::lean::nat::Nat::from_ptr(stop_ptr),
    }
  }
}

/// Decode Ix.SyntaxPreresolved.
fn decode_syntax_preresolved(ptr: *const c_void) -> SyntaxPreresolved {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // namespace
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        SyntaxPreresolved::Namespace(decode_ix_name(name_ptr))
      }
      1 => {
        // decl
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let aliases_ptr = lean_ctor_get(ptr as *mut _, 1);

        let name = decode_ix_name(name_ptr);
        let aliases_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(aliases_ptr.cast());
        let aliases: Vec<String> = aliases_obj
          .data()
          .iter()
          .map(|&p| {
            let s: &LeanStringObject = crate::lean::as_ref_unsafe(p.cast());
            s.as_string()
          })
          .collect();

        SyntaxPreresolved::Decl(name, aliases)
      }
      _ => panic!("Invalid SyntaxPreresolved tag: {}", tag),
    }
  }
}

// =============================================================================
// FFI Exports for Ix Type Roundtrips
// =============================================================================

/// Round-trip an Ix.Address: decode ByteArray, re-encode.
/// Address = { hash : ByteArray } - single field struct, so UNBOXED to ByteArray directly
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_address(addr_ptr: *const c_void) -> *mut c_void {
  unsafe {
    // Address is a single-field struct { hash : ByteArray }
    // Due to unboxing, addr_ptr IS the ByteArray directly
    let ba: &crate::lean::sarray::LeanSArrayObject = crate::lean::as_ref_unsafe(addr_ptr.cast());
    let bytes = ba.data();

    // Rebuild ByteArray - this IS the Address due to unboxing
    let new_ba = lean_alloc_sarray(1, bytes.len(), bytes.len());
    let data_ptr = lean_sarray_cptr(new_ba);
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, bytes.len());
    new_ba
  }
}

/// Round-trip an Ix.Name: decode from Lean, re-encode via IxEnvBuilder.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_name(name_ptr: *const c_void) -> *mut c_void {
  let name = decode_ix_name(name_ptr);
  let mut builder = IxEnvBuilder::new();
  builder.build_name(&name)
}

/// Round-trip an Ix.Level: decode from Lean, re-encode via IxEnvBuilder.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_level(level_ptr: *const c_void) -> *mut c_void {
  let level = decode_ix_level(level_ptr);
  let mut builder = IxEnvBuilder::new();
  builder.build_level(&level)
}

/// Round-trip an Ix.Expr: decode from Lean, re-encode via IxEnvBuilder.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_expr(expr_ptr: *const c_void) -> *mut c_void {
  let expr = decode_ix_expr(expr_ptr);
  let mut builder = IxEnvBuilder::new();
  builder.build_expr(&expr)
}

/// Decode Ix.Int from Lean pointer.
/// Ix.Int: ofNat (tag 0, 1 field) | negSucc (tag 1, 1 field)
fn decode_ix_int(ptr: *const c_void) -> Int {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
    let nat = crate::lean::nat::Nat::from_ptr(nat_ptr);
    match tag {
      0 => Int::OfNat(nat),
      1 => Int::NegSucc(nat),
      _ => panic!("Invalid Ix.Int tag: {}", tag),
    }
  }
}

/// Round-trip an Ix.Int: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_int(int_ptr: *const c_void) -> *mut c_void {
  let int_val = decode_ix_int(int_ptr);
  let builder = IxEnvBuilder::new();
  builder.build_int(&int_val)
}

/// Round-trip an Ix.Substring: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_substring(sub_ptr: *const c_void) -> *mut c_void {
  let sub = decode_substring(sub_ptr);
  let builder = IxEnvBuilder::new();
  builder.build_substring(&sub)
}

/// Decode Ix.SourceInfo from Lean pointer.
fn decode_ix_source_info_standalone(ptr: *const c_void) -> SourceInfo {
  decode_ix_source_info(ptr)
}

/// Round-trip an Ix.SourceInfo: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_source_info(si_ptr: *const c_void) -> *mut c_void {
  let si = decode_ix_source_info_standalone(si_ptr);
  let builder = IxEnvBuilder::new();
  builder.build_source_info(&si)
}

/// Round-trip an Ix.SyntaxPreresolved: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax_preresolved(sp_ptr: *const c_void) -> *mut c_void {
  let sp = decode_syntax_preresolved(sp_ptr);
  let mut builder = IxEnvBuilder::new();
  builder.build_syntax_preresolved(&sp)
}

/// Round-trip an Ix.Syntax: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax(syn_ptr: *const c_void) -> *mut c_void {
  let syn = decode_ix_syntax(syn_ptr);
  let mut builder = IxEnvBuilder::new();
  builder.build_syntax(&syn)
}

/// Round-trip an Ix.DataValue: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_data_value(dv_ptr: *const c_void) -> *mut c_void {
  let dv = decode_data_value(dv_ptr);
  let mut builder = IxEnvBuilder::new();
  builder.build_data_value(&dv)
}

/// Round-trip a Bool: decode from Lean, re-encode.
/// Bool in Lean is passed as unboxed scalar: false = 0, true = 1
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_bool(bool_ptr: *const c_void) -> *mut c_void {
  // Bool is passed as unboxed scalar - just return it as-is
  bool_ptr as *mut c_void
}

// =============================================================================
// ConstantInfo Decoders
// =============================================================================

use crate::ix::env::{
  AxiomVal, ConstructorVal, DefinitionVal, InductiveVal, OpaqueVal, QuotVal, RecursorRule,
  RecursorVal, TheoremVal,
};

/// Decode Ix.ConstantVal from Lean pointer.
/// ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
fn decode_constant_val(ptr: *const c_void) -> ConstantVal {
  unsafe {
    let name_ptr = lean_ctor_get(ptr as *mut _, 0);
    let level_params_ptr = lean_ctor_get(ptr as *mut _, 1);
    let type_ptr = lean_ctor_get(ptr as *mut _, 2);

    let name = decode_ix_name(name_ptr);

    let level_params_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(level_params_ptr.cast());
    let level_params: Vec<Name> = level_params_obj
      .data()
      .iter()
      .map(|&p| decode_ix_name(p))
      .collect();

    let typ = decode_ix_expr(type_ptr);

    ConstantVal {
      name,
      level_params,
      typ,
    }
  }
}

/// Decode Lean.ReducibilityHints from Lean pointer.
/// | opaque -- tag 0
/// | abbrev -- tag 1
/// | regular (h : UInt32) -- tag 2
///
/// NOTE: In Lean 4, boxed scalars are `(tag << 1) | 1`:
/// - opaque (tag 0) → scalar value 1
/// - abbrev (tag 1) → scalar value 3
fn decode_reducibility_hints(ptr: *const c_void) -> ReducibilityHints {
  unsafe {
    if lean_is_scalar(ptr) {
      // Unbox the scalar: tag = (ptr >> 1)
      let tag = (ptr as usize) >> 1;
      match tag {
        0 => return ReducibilityHints::Opaque,
        1 => return ReducibilityHints::Abbrev,
        _ => panic!("Invalid ReducibilityHints scalar tag: {}", tag),
      }
    }

    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => ReducibilityHints::Opaque,
      1 => ReducibilityHints::Abbrev,
      2 => {
        // regular: 0 obj fields, 4 scalar bytes (UInt32)
        let ctor_ptr = ptr as *const u8;
        let h = *(ctor_ptr.add(8) as *const u32);
        ReducibilityHints::Regular(h)
      }
      _ => panic!("Invalid ReducibilityHints tag: {}", tag),
    }
  }
}

// NOTE: DefinitionSafety and QuotKind are decoded directly as scalar bytes
// from their containing structures, not as separate objects. The decode
// functions below are kept for reference but not used.
//
// /// Decode Lean.DefinitionSafety from Lean pointer.
// fn decode_definition_safety(ptr: *const c_void) -> DefinitionSafety {
//   let val = ptr as usize;
//   match val {
//     0 => DefinitionSafety::Unsafe,
//     1 => DefinitionSafety::Safe,
//     2 => DefinitionSafety::Partial,
//     _ => panic!("Invalid DefinitionSafety: {}", val),
//   }
// }
//
// /// Decode Lean.QuotKind from Lean pointer.
// fn decode_quot_kind(ptr: *const c_void) -> QuotKind {
//   let val = ptr as usize;
//   match val {
//     0 => QuotKind::Type,
//     1 => QuotKind::Ctor,
//     2 => QuotKind::Lift,
//     3 => QuotKind::Ind,
//     _ => panic!("Invalid QuotKind: {}", val),
//   }
// }

/// Decode Ix.RecursorRule from Lean pointer.
/// RecursorRule = { ctor : Name, nfields : Nat, rhs : Expr }
fn decode_recursor_rule(ptr: *const c_void) -> RecursorRule {
  unsafe {
    let ctor_ptr = lean_ctor_get(ptr as *mut _, 0);
    let n_fields_ptr = lean_ctor_get(ptr as *mut _, 1);
    let rhs_ptr = lean_ctor_get(ptr as *mut _, 2);

    RecursorRule {
      ctor: decode_ix_name(ctor_ptr),
      n_fields: crate::lean::nat::Nat::from_ptr(n_fields_ptr),
      rhs: decode_ix_expr(rhs_ptr),
    }
  }
}

/// Decode Array of Names from Lean pointer.
fn decode_name_array(ptr: *const c_void) -> Vec<Name> {
  let arr_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(ptr.cast());
  arr_obj.data().iter().map(|&p| decode_ix_name(p)).collect()
}

/// Decode Ix.ConstantInfo from Lean pointer.
///
/// ConstantInfo variants:
/// - Tag 0: axiomInfo (v : AxiomVal)
/// - Tag 1: defnInfo (v : DefinitionVal)
/// - Tag 2: thmInfo (v : TheoremVal)
/// - Tag 3: opaqueInfo (v : OpaqueVal)
/// - Tag 4: quotInfo (v : QuotVal)
/// - Tag 5: inductInfo (v : InductiveVal)
/// - Tag 6: ctorInfo (v : ConstructorVal)
/// - Tag 7: recInfo (v : RecursorVal)
fn decode_constant_info(ptr: *const c_void) -> ConstantInfo {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    let inner_ptr = lean_ctor_get(ptr as *mut _, 0);

    match tag {
      0 => {
        // axiomInfo: AxiomVal = { cnst : ConstantVal, isUnsafe : Bool }
        // Structure: 1 obj field (cnst), 1 scalar byte (isUnsafe)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let ctor: &crate::lean::ctor::LeanCtorObject =
          crate::lean::as_ref_unsafe(inner_ptr.cast());
        let is_unsafe = ctor.get_scalar_u8(1, 0) != 0;

        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: decode_constant_val(cnst_ptr),
          is_unsafe,
        })
      }
      1 => {
        // defnInfo: DefinitionVal = { cnst, value, hints, safety, all }
        // NOTE: safety (DefinitionSafety) is a small enum and is stored as a SCALAR field
        // Memory layout: 4 obj fields (cnst, value, hints, all), 1 scalar byte (safety)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let value_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let hints_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 3);  // all is at index 3, not 4!

        // safety is a scalar at offset 4*8 = 32 bytes from start of object fields
        let ctor: &crate::lean::ctor::LeanCtorObject = crate::lean::as_ref_unsafe(inner_ptr.cast());
        let safety_byte = ctor.get_scalar_u8(4, 0);  // 4 obj fields, offset 0 in scalar area
        let safety = match safety_byte {
          0 => DefinitionSafety::Unsafe,
          1 => DefinitionSafety::Safe,
          2 => DefinitionSafety::Partial,
          _ => panic!("Invalid DefinitionSafety: {}", safety_byte),
        };

        ConstantInfo::DefnInfo(DefinitionVal {
          cnst: decode_constant_val(cnst_ptr),
          value: decode_ix_expr(value_ptr),
          hints: decode_reducibility_hints(hints_ptr),
          safety,
          all: decode_name_array(all_ptr),
        })
      }
      2 => {
        // thmInfo: TheoremVal = { cnst, value, all }
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let value_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 2);

        ConstantInfo::ThmInfo(TheoremVal {
          cnst: decode_constant_val(cnst_ptr),
          value: decode_ix_expr(value_ptr),
          all: decode_name_array(all_ptr),
        })
      }
      3 => {
        // opaqueInfo: OpaqueVal = { cnst, value, isUnsafe, all }
        // Structure: 3 obj fields (cnst, value, all), 1 scalar byte (isUnsafe)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let value_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let ctor: &crate::lean::ctor::LeanCtorObject =
          crate::lean::as_ref_unsafe(inner_ptr.cast());
        let is_unsafe = ctor.get_scalar_u8(3, 0) != 0;

        ConstantInfo::OpaqueInfo(OpaqueVal {
          cnst: decode_constant_val(cnst_ptr),
          value: decode_ix_expr(value_ptr),
          is_unsafe,
          all: decode_name_array(all_ptr),
        })
      }
      4 => {
        // quotInfo: QuotVal = { cnst, kind }
        // NOTE: QuotKind is a small enum (4 0-field ctors), stored as SCALAR
        // Memory layout: 1 obj field (cnst), 1 scalar byte (kind)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);

        let ctor: &crate::lean::ctor::LeanCtorObject = crate::lean::as_ref_unsafe(inner_ptr.cast());
        let kind_byte = ctor.get_scalar_u8(1, 0);  // 1 obj field, offset 0 in scalar area
        let kind = match kind_byte {
          0 => QuotKind::Type,
          1 => QuotKind::Ctor,
          2 => QuotKind::Lift,
          3 => QuotKind::Ind,
          _ => panic!("Invalid QuotKind: {}", kind_byte),
        };

        ConstantInfo::QuotInfo(QuotVal {
          cnst: decode_constant_val(cnst_ptr),
          kind,
        })
      }
      5 => {
        // inductInfo: InductiveVal = { cnst, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive }
        // 6 obj fields, 3 scalar bytes
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let num_params_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let num_indices_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 3);
        let ctors_ptr = lean_ctor_get(inner_ptr as *mut _, 4);
        let num_nested_ptr = lean_ctor_get(inner_ptr as *mut _, 5);

        let ctor: &crate::lean::ctor::LeanCtorObject =
          crate::lean::as_ref_unsafe(inner_ptr.cast());
        let is_rec = ctor.get_scalar_u8(6, 0) != 0;
        let is_unsafe = ctor.get_scalar_u8(6, 1) != 0;
        let is_reflexive = ctor.get_scalar_u8(6, 2) != 0;

        ConstantInfo::InductInfo(InductiveVal {
          cnst: decode_constant_val(cnst_ptr),
          num_params: crate::lean::nat::Nat::from_ptr(num_params_ptr),
          num_indices: crate::lean::nat::Nat::from_ptr(num_indices_ptr),
          all: decode_name_array(all_ptr),
          ctors: decode_name_array(ctors_ptr),
          num_nested: crate::lean::nat::Nat::from_ptr(num_nested_ptr),
          is_rec,
          is_unsafe,
          is_reflexive,
        })
      }
      6 => {
        // ctorInfo: ConstructorVal = { cnst, induct, cidx, numParams, numFields, isUnsafe }
        // 5 obj fields, 1 scalar byte
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let induct_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let cidx_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let num_params_ptr = lean_ctor_get(inner_ptr as *mut _, 3);
        let num_fields_ptr = lean_ctor_get(inner_ptr as *mut _, 4);

        let ctor: &crate::lean::ctor::LeanCtorObject =
          crate::lean::as_ref_unsafe(inner_ptr.cast());
        let is_unsafe = ctor.get_scalar_u8(5, 0) != 0;

        ConstantInfo::CtorInfo(ConstructorVal {
          cnst: decode_constant_val(cnst_ptr),
          induct: decode_ix_name(induct_ptr),
          cidx: crate::lean::nat::Nat::from_ptr(cidx_ptr),
          num_params: crate::lean::nat::Nat::from_ptr(num_params_ptr),
          num_fields: crate::lean::nat::Nat::from_ptr(num_fields_ptr),
          is_unsafe,
        })
      }
      7 => {
        // recInfo: RecursorVal = { cnst, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }
        // 7 obj fields, 2 scalar bytes
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let num_params_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let num_indices_ptr = lean_ctor_get(inner_ptr as *mut _, 3);
        let num_motives_ptr = lean_ctor_get(inner_ptr as *mut _, 4);
        let num_minors_ptr = lean_ctor_get(inner_ptr as *mut _, 5);
        let rules_ptr = lean_ctor_get(inner_ptr as *mut _, 6);

        let ctor: &crate::lean::ctor::LeanCtorObject =
          crate::lean::as_ref_unsafe(inner_ptr.cast());
        let k = ctor.get_scalar_u8(7, 0) != 0;
        let is_unsafe = ctor.get_scalar_u8(7, 1) != 0;

        let rules_obj: &LeanArrayObject = crate::lean::as_ref_unsafe(rules_ptr.cast());
        let rules: Vec<RecursorRule> = rules_obj
          .data()
          .iter()
          .map(|&p| decode_recursor_rule(p))
          .collect();

        ConstantInfo::RecInfo(RecursorVal {
          cnst: decode_constant_val(cnst_ptr),
          all: decode_name_array(all_ptr),
          num_params: crate::lean::nat::Nat::from_ptr(num_params_ptr),
          num_indices: crate::lean::nat::Nat::from_ptr(num_indices_ptr),
          num_motives: crate::lean::nat::Nat::from_ptr(num_motives_ptr),
          num_minors: crate::lean::nat::Nat::from_ptr(num_minors_ptr),
          rules,
          k,
          is_unsafe,
        })
      }
      _ => panic!("Invalid ConstantInfo tag: {}", tag),
    }
  }
}

/// Round-trip an Ix.ConstantInfo: decode from Lean, re-encode via IxEnvBuilder.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_constant_info(info_ptr: *const c_void) -> *mut c_void {
  let info = decode_constant_info(info_ptr);
  let mut builder = IxEnvBuilder::new();
  builder.build_constant_info(&info)
}

// =============================================================================
// Environment Decoder and FFI
// =============================================================================

/// Decode a HashMap's AssocList and collect key-value pairs using a custom decoder.
fn decode_assoc_list<K, V, FK, FV>(
  list_ptr: *const c_void,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(*const c_void) -> K,
  FV: Fn(*const c_void) -> V,
{
  let mut result = Vec::new();
  let mut current = list_ptr;

  loop {
    unsafe {
      if lean_is_scalar(current) {
        break;
      }

      let tag = lean_obj_tag(current as *mut _);
      if tag == 0 {
        // AssocList.nil
        break;
      }

      // AssocList.cons: 3 fields (key, value, tail)
      let key_ptr = lean_ctor_get(current as *mut _, 0);
      let value_ptr = lean_ctor_get(current as *mut _, 1);
      let tail_ptr = lean_ctor_get(current as *mut _, 2);

      result.push((decode_key(key_ptr), decode_val(value_ptr)));
      current = tail_ptr;
    }
  }

  result
}

/// Decode a Lean HashMap into a Vec of key-value pairs.
/// HashMap structure (after unboxing): Raw { size : Nat, buckets : Array (AssocList α β) }
///
/// Due to single-field struct unboxing:
/// - HashMap { inner : DHashMap } unboxes to DHashMap
/// - DHashMap { inner : Raw, wf : Prop } unboxes to Raw (Prop is erased)
/// - Raw { size : Nat, buckets : Array } - field 0 = size, field 1 = buckets
fn decode_hashmap<K, V, FK, FV>(
  map_ptr: *const c_void,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(*const c_void) -> K + Copy,
  FV: Fn(*const c_void) -> V + Copy,
{
  unsafe {
    // Raw layout: field 0 = size (Nat), field 1 = buckets (Array)
    let _size_ptr = lean_ctor_get(map_ptr as *mut _, 0);  // unused but needed for layout
    let buckets_ptr = lean_ctor_get(map_ptr as *mut _, 1);

    let buckets_obj: &crate::lean::array::LeanArrayObject =
      crate::lean::as_ref_unsafe(buckets_ptr.cast());

    let mut pairs = Vec::new();
    for &bucket_ptr in buckets_obj.data() {
      let bucket_pairs = decode_assoc_list(bucket_ptr, decode_key, decode_val);
      pairs.extend(bucket_pairs);
    }

    pairs
  }
}

/// Decode Ix.Environment from Lean pointer.
///
/// Ix.Environment = {
///   consts : HashMap Name ConstantInfo
/// }
///
/// NOTE: Environment with a single field is UNBOXED by Lean,
/// so the pointer IS the HashMap directly, not a structure containing it.
fn decode_ix_environment(ptr: *const c_void) -> FxHashMap<Name, ConstantInfo> {
  // Environment is unboxed - ptr IS the HashMap directly
  let consts_pairs = decode_hashmap(ptr, decode_ix_name, decode_constant_info);
  let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
  for (name, info) in consts_pairs {
    consts.insert(name, info);
  }

  consts
}

/// Round-trip an Ix.Environment: decode from Lean, re-encode via IxEnvBuilder.
/// Returns Ix.RawEnvironment (caller must convert via .toEnvironment).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_environment(env_ptr: *const c_void) -> *mut c_void {
  let consts = decode_ix_environment(env_ptr);

  // Convert to Env type for building
  let env: Env = consts.into_iter().collect();

  let mut builder = IxEnvBuilder::with_capacity(env.len());
  builder.build_raw_environment(&env)
}

/// Decode Ix.RawEnvironment from Lean pointer.
///
/// Ix.RawEnvironment = {
///   consts : Array (Name × ConstantInfo)
/// }
///
/// NOTE: RawEnvironment with a single field is UNBOXED by Lean,
/// so the pointer IS the array directly, not a structure containing it.
fn decode_ix_raw_environment(ptr: *const c_void) -> FxHashMap<Name, ConstantInfo> {
  unsafe {
    // RawEnvironment is unboxed - ptr IS the array directly
    let consts_arr: &LeanArrayObject = crate::lean::as_ref_unsafe(ptr.cast());

    let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
    for &pair_ptr in consts_arr.data() {
      let name_ptr = lean_ctor_get(pair_ptr as *mut _, 0);
      let info_ptr = lean_ctor_get(pair_ptr as *mut _, 1);
      let name = decode_ix_name(name_ptr);
      let info = decode_constant_info(info_ptr);
      consts.insert(name, info);
    }

    consts
  }
}

/// Round-trip an Ix.RawEnvironment: decode from Lean, re-encode via IxEnvBuilder.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_raw_environment(env_ptr: *const c_void) -> *mut c_void {
  let consts = decode_ix_raw_environment(env_ptr);

  let mut builder = IxEnvBuilder::with_capacity(consts.len());
  builder.build_raw_environment(&consts)
}
