//! Ix.DataValue, Ix.Syntax, Ix.SourceInfo build/decode/roundtrip FFI.

use std::ffi::c_void;

use crate::ix::env::{
  DataValue, Int, Name, SourceInfo, Substring, Syntax, SyntaxPreresolved,
};
use crate::lean::lean::{
  lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_ctor_get,
  lean_ctor_set, lean_ctor_set_uint8, lean_mk_string, lean_obj_tag,
};
use crate::lean::nat::Nat;
use crate::lean::{
  lean_array_data, lean_ctor_scalar_u8, lean_is_scalar, lean_obj_to_string,
};

use super::super::builder::LeanBuildCache;
use super::super::primitives::build_nat;
use super::name::{build_name, decode_ix_name};

/// Build a Ix.Int (ofNat or negSucc).
pub fn build_int(int: &Int) -> *mut c_void {
  unsafe {
    match int {
      Int::OfNat(n) => {
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, build_nat(n).cast());
        obj.cast()
      },
      Int::NegSucc(n) => {
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, build_nat(n).cast());
        obj.cast()
      },
    }
  }
}

/// Build a Ix.Substring.
pub fn build_substring(ss: &Substring) -> *mut c_void {
  unsafe {
    let s_cstr = crate::lean::safe_cstring(ss.str.as_str());
    let obj = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(obj, 0, lean_mk_string(s_cstr.as_ptr()));
    lean_ctor_set(obj, 1, build_nat(&ss.start_pos).cast());
    lean_ctor_set(obj, 2, build_nat(&ss.stop_pos).cast());
    obj.cast()
  }
}

/// Build a Ix.SourceInfo.
pub fn build_source_info(si: &SourceInfo) -> *mut c_void {
  unsafe {
    match si {
      // | original (leading : Substring) (pos : Nat) (trailing : Substring) (endPos : Nat) -- tag 0
      SourceInfo::Original(leading, pos, trailing, end_pos) => {
        let obj = lean_alloc_ctor(0, 4, 0);
        lean_ctor_set(obj, 0, build_substring(leading).cast());
        lean_ctor_set(obj, 1, build_nat(pos).cast());
        lean_ctor_set(obj, 2, build_substring(trailing).cast());
        lean_ctor_set(obj, 3, build_nat(end_pos).cast());
        obj.cast()
      },
      // | synthetic (pos : Nat) (endPos : Nat) (canonical : Bool) -- tag 1
      SourceInfo::Synthetic(pos, end_pos, canonical) => {
        let obj = lean_alloc_ctor(1, 2, 1);
        lean_ctor_set(obj, 0, build_nat(pos).cast());
        lean_ctor_set(obj, 1, build_nat(end_pos).cast());
        lean_ctor_set_uint8(obj, 2 * 8, *canonical as u8);
        obj.cast()
      },
      // | none -- tag 2
      SourceInfo::None => lean_alloc_ctor(2, 0, 0).cast(),
    }
  }
}

/// Build a Ix.SyntaxPreresolved.
pub fn build_syntax_preresolved(
  cache: &mut LeanBuildCache,
  sp: &SyntaxPreresolved,
) -> *mut c_void {
  unsafe {
    match sp {
      // | namespace (name : Name) -- tag 0
      SyntaxPreresolved::Namespace(name) => {
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, build_name(cache, name).cast());
        obj.cast()
      },
      // | decl (name : Name) (aliases : Array String) -- tag 1
      SyntaxPreresolved::Decl(name, aliases) => {
        let name_obj = build_name(cache, name);
        let aliases_obj = build_string_array(aliases);
        let obj = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(obj, 0, name_obj.cast());
        lean_ctor_set(obj, 1, aliases_obj.cast());
        obj.cast()
      },
    }
  }
}

/// Build an Array of Strings.
pub fn build_string_array(strings: &[String]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(strings.len(), strings.len());
    for (i, s) in strings.iter().enumerate() {
      let s_cstr = crate::lean::safe_cstring(s.as_str());
      lean_array_set_core(arr, i, lean_mk_string(s_cstr.as_ptr()));
    }
    arr.cast()
  }
}

/// Build a Ix.Syntax.
pub fn build_syntax(cache: &mut LeanBuildCache, syn: &Syntax) -> *mut c_void {
  unsafe {
    match syn {
      // | missing -- tag 0
      Syntax::Missing => lean_alloc_ctor(0, 0, 0).cast(),
      // | node (info : SourceInfo) (kind : Name) (args : Array Syntax) -- tag 1
      Syntax::Node(info, kind, args) => {
        let info_obj = build_source_info(info);
        let kind_obj = build_name(cache, kind);
        let args_obj = build_syntax_array(cache, args);
        let obj = lean_alloc_ctor(1, 3, 0);
        lean_ctor_set(obj, 0, info_obj.cast());
        lean_ctor_set(obj, 1, kind_obj.cast());
        lean_ctor_set(obj, 2, args_obj.cast());
        obj.cast()
      },
      // | atom (info : SourceInfo) (val : String) -- tag 2
      Syntax::Atom(info, val) => {
        let info_obj = build_source_info(info);
        let val_cstr = crate::lean::safe_cstring(val.as_str());
        let obj = lean_alloc_ctor(2, 2, 0);
        lean_ctor_set(obj, 0, info_obj.cast());
        lean_ctor_set(obj, 1, lean_mk_string(val_cstr.as_ptr()));
        obj.cast()
      },
      // | ident (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : Array SyntaxPreresolved) -- tag 3
      Syntax::Ident(info, raw_val, val, preresolved) => {
        let info_obj = build_source_info(info);
        let raw_val_obj = build_substring(raw_val);
        let val_obj = build_name(cache, val);
        let preresolved_obj =
          build_syntax_preresolved_array(cache, preresolved);
        let obj = lean_alloc_ctor(3, 4, 0);
        lean_ctor_set(obj, 0, info_obj.cast());
        lean_ctor_set(obj, 1, raw_val_obj.cast());
        lean_ctor_set(obj, 2, val_obj.cast());
        lean_ctor_set(obj, 3, preresolved_obj.cast());
        obj.cast()
      },
    }
  }
}

/// Build an Array of Syntax.
pub fn build_syntax_array(
  cache: &mut LeanBuildCache,
  items: &[Syntax],
) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(items.len(), items.len());
    for (i, item) in items.iter().enumerate() {
      let item_obj = build_syntax(cache, item);
      lean_array_set_core(arr, i, item_obj.cast());
    }
    arr.cast()
  }
}

/// Build an Array of SyntaxPreresolved.
pub fn build_syntax_preresolved_array(
  cache: &mut LeanBuildCache,
  items: &[SyntaxPreresolved],
) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(items.len(), items.len());
    for (i, item) in items.iter().enumerate() {
      let item_obj = build_syntax_preresolved(cache, item);
      lean_array_set_core(arr, i, item_obj.cast());
    }
    arr.cast()
  }
}

/// Build Ix.DataValue.
pub fn build_data_value(
  cache: &mut LeanBuildCache,
  dv: &DataValue,
) -> *mut c_void {
  unsafe {
    match dv {
      DataValue::OfString(s) => {
        let s_cstr = crate::lean::safe_cstring(s.as_str());
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, lean_mk_string(s_cstr.as_ptr()));
        obj.cast()
      },
      DataValue::OfBool(b) => {
        // 0 object fields, 1 scalar byte
        let obj = lean_alloc_ctor(1, 0, 1);
        lean_ctor_set_uint8(obj, 0, *b as u8);
        obj.cast()
      },
      DataValue::OfName(n) => {
        let obj = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(obj, 0, build_name(cache, n).cast());
        obj.cast()
      },
      DataValue::OfNat(n) => {
        let obj = lean_alloc_ctor(3, 1, 0);
        lean_ctor_set(obj, 0, build_nat(n).cast());
        obj.cast()
      },
      DataValue::OfInt(i) => {
        let obj = lean_alloc_ctor(4, 1, 0);
        lean_ctor_set(obj, 0, build_int(i).cast());
        obj.cast()
      },
      DataValue::OfSyntax(syn) => {
        let obj = lean_alloc_ctor(5, 1, 0);
        lean_ctor_set(obj, 0, build_syntax(cache, syn).cast());
        obj.cast()
      },
    }
  }
}

/// Build an Array of (Name × DataValue) for mdata.
pub fn build_kvmap(
  cache: &mut LeanBuildCache,
  data: &[(Name, DataValue)],
) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(data.len(), data.len());
    for (i, (name, dv)) in data.iter().enumerate() {
      let name_obj = build_name(cache, name);
      let dv_obj = build_data_value(cache, dv);
      // Prod (Name × DataValue)
      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, name_obj.cast());
      lean_ctor_set(pair, 1, dv_obj.cast());
      lean_array_set_core(arr, i, pair);
    }
    arr.cast()
  }
}

// =============================================================================
// Decode Functions
// =============================================================================

/// Decode Ix.Int from Lean pointer.
/// Ix.Int: ofNat (tag 0, 1 field) | negSucc (tag 1, 1 field)
pub fn decode_ix_int(ptr: *const c_void) -> Int {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    let nat_ptr = lean_ctor_get(ptr as *mut _, 0);
    let nat = Nat::from_ptr(nat_ptr.cast());
    match tag {
      0 => Int::OfNat(nat),
      1 => Int::NegSucc(nat),
      _ => panic!("Invalid Ix.Int tag: {}", tag),
    }
  }
}

/// Decode Ix.DataValue from a Lean pointer.
pub fn decode_data_value(ptr: *const c_void) -> DataValue {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);

    match tag {
      0 => {
        // ofString: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        DataValue::OfString(lean_obj_to_string(inner_ptr as *const _))
      },
      1 => {
        // ofBool: 0 object fields, 1 scalar byte
        let b = lean_ctor_scalar_u8(ptr, 0, 0) != 0;
        DataValue::OfBool(b)
      },
      2 => {
        // ofName: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        DataValue::OfName(decode_ix_name(inner_ptr.cast()))
      },
      3 => {
        // ofNat: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        DataValue::OfNat(Nat::from_ptr(inner_ptr.cast()))
      },
      4 => {
        // ofInt: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        let int_tag = lean_obj_tag(inner_ptr.cast());
        let nat_ptr = lean_ctor_get(inner_ptr.cast(), 0);
        let nat = Nat::from_ptr(nat_ptr.cast());
        match int_tag {
          0 => DataValue::OfInt(Int::OfNat(nat)),
          1 => DataValue::OfInt(Int::NegSucc(nat)),
          _ => panic!("Invalid Int tag: {}", int_tag),
        }
      },
      5 => {
        // ofSyntax: 1 object field
        let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
        DataValue::OfSyntax(decode_ix_syntax(inner_ptr.cast()).into())
      },
      _ => panic!("Invalid DataValue tag: {}", tag),
    }
  }
}

/// Decode Ix.Syntax from a Lean pointer.
pub fn decode_ix_syntax(ptr: *const c_void) -> Syntax {
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

        let info = decode_ix_source_info(info_ptr.cast());
        let kind = decode_ix_name(kind_ptr.cast());
        let args: Vec<Syntax> = lean_array_data(args_ptr.cast())
          .iter()
          .map(|&p| decode_ix_syntax(p))
          .collect();

        Syntax::Node(info, kind, args)
      },
      2 => {
        // atom: info, val
        let info_ptr = lean_ctor_get(ptr as *mut _, 0);
        let val_ptr = lean_ctor_get(ptr as *mut _, 1);

        let info = decode_ix_source_info(info_ptr.cast());
        Syntax::Atom(info, lean_obj_to_string(val_ptr.cast()))
      },
      3 => {
        // ident: info, rawVal, val, preresolved
        let info_ptr = lean_ctor_get(ptr as *mut _, 0);
        let raw_val_ptr = lean_ctor_get(ptr as *mut _, 1);
        let val_ptr = lean_ctor_get(ptr as *mut _, 2);
        let preresolved_ptr = lean_ctor_get(ptr as *mut _, 3);

        let info = decode_ix_source_info(info_ptr.cast());
        let raw_val = decode_substring(raw_val_ptr.cast());
        let val = decode_ix_name(val_ptr.cast());
        let preresolved: Vec<SyntaxPreresolved> =
          lean_array_data(preresolved_ptr.cast())
            .iter()
            .map(|&p| decode_syntax_preresolved(p))
            .collect();

        Syntax::Ident(info, raw_val, val, preresolved)
      },
      _ => panic!("Invalid Syntax tag: {}", tag),
    }
  }
}

/// Decode Ix.SourceInfo.
pub fn decode_ix_source_info(ptr: *const c_void) -> SourceInfo {
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
          decode_substring(leading_ptr.cast()),
          Nat::from_ptr(pos_ptr.cast()),
          decode_substring(trailing_ptr.cast()),
          Nat::from_ptr(end_pos_ptr.cast()),
        )
      },
      1 => {
        // synthetic: 2 obj fields (pos, end_pos), 1 scalar byte (canonical)
        let pos_ptr = lean_ctor_get(ptr as *mut _, 0);
        let end_pos_ptr = lean_ctor_get(ptr as *mut _, 1);

        let canonical = lean_ctor_scalar_u8(ptr, 2, 0) != 0;

        SourceInfo::Synthetic(
          Nat::from_ptr(pos_ptr.cast()),
          Nat::from_ptr(end_pos_ptr.cast()),
          canonical,
        )
      },
      2 => SourceInfo::None,
      _ => panic!("Invalid SourceInfo tag: {}", tag),
    }
  }
}

/// Decode Ix.Substring.
pub fn decode_substring(ptr: *const c_void) -> Substring {
  unsafe {
    let str_ptr = lean_ctor_get(ptr as *mut _, 0);
    let start_ptr = lean_ctor_get(ptr as *mut _, 1);
    let stop_ptr = lean_ctor_get(ptr as *mut _, 2);

    Substring {
      str: lean_obj_to_string(str_ptr.cast()),
      start_pos: Nat::from_ptr(start_ptr.cast()),
      stop_pos: Nat::from_ptr(stop_ptr.cast()),
    }
  }
}

/// Decode Ix.SyntaxPreresolved.
pub fn decode_syntax_preresolved(ptr: *const c_void) -> SyntaxPreresolved {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // namespace
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        SyntaxPreresolved::Namespace(decode_ix_name(name_ptr.cast()))
      },
      1 => {
        // decl
        let name_ptr = lean_ctor_get(ptr as *mut _, 0);
        let aliases_ptr = lean_ctor_get(ptr as *mut _, 1);

        let name = decode_ix_name(name_ptr.cast());
        let aliases: Vec<String> = lean_array_data(aliases_ptr.cast())
          .iter()
          .map(|&p| lean_obj_to_string(p))
          .collect();

        SyntaxPreresolved::Decl(name, aliases)
      },
      _ => panic!("Invalid SyntaxPreresolved tag: {}", tag),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip an Ix.Int: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_int(int_ptr: *const c_void) -> *mut c_void {
  let int_val = decode_ix_int(int_ptr);
  build_int(&int_val)
}

/// Round-trip an Ix.Substring: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_substring(
  sub_ptr: *const c_void,
) -> *mut c_void {
  let sub = decode_substring(sub_ptr);
  build_substring(&sub)
}

/// Round-trip an Ix.SourceInfo: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_source_info(
  si_ptr: *const c_void,
) -> *mut c_void {
  let si = decode_ix_source_info(si_ptr);
  build_source_info(&si)
}

/// Round-trip an Ix.SyntaxPreresolved: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax_preresolved(
  sp_ptr: *const c_void,
) -> *mut c_void {
  let sp = decode_syntax_preresolved(sp_ptr);
  let mut cache = LeanBuildCache::new();
  build_syntax_preresolved(&mut cache, &sp)
}

/// Round-trip an Ix.Syntax: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax(
  syn_ptr: *const c_void,
) -> *mut c_void {
  let syn = decode_ix_syntax(syn_ptr);
  let mut cache = LeanBuildCache::new();
  build_syntax(&mut cache, &syn)
}

/// Round-trip an Ix.DataValue: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_data_value(
  dv_ptr: *const c_void,
) -> *mut c_void {
  let dv = decode_data_value(dv_ptr);
  let mut cache = LeanBuildCache::new();
  build_data_value(&mut cache, &dv)
}
