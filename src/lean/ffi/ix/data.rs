//! Ix.DataValue, Ix.Syntax, Ix.SourceInfo build/decode/roundtrip FFI.

use std::ffi::c_void;

use crate::ix::env::{
  DataValue, Int, Name, SourceInfo, Substring, Syntax, SyntaxPreresolved,
};
use crate::lean::lean::{lean_ctor_get, lean_obj_tag};
use crate::lean::nat::Nat;
use crate::lean::obj::{
  IxDataValue, IxInt, IxSourceInfo, IxSubstring, IxSyntax,
  IxSyntaxPreresolved, LeanArray, LeanCtor, LeanString,
};
use crate::lean::{
  lean_array_data, lean_ctor_scalar_u8, lean_is_scalar, lean_obj_to_string,
};

use super::super::builder::LeanBuildCache;
use super::super::primitives::build_nat;
use super::name::{build_name, decode_ix_name};

/// Build a Ix.Int (ofNat or negSucc).
pub fn build_int(int: &Int) -> IxInt {
  match int {
    Int::OfNat(n) => {
      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, build_nat(n));
      IxInt::new(*obj)
    },
    Int::NegSucc(n) => {
      let obj = LeanCtor::alloc(1, 1, 0);
      obj.set(0, build_nat(n));
      IxInt::new(*obj)
    },
  }
}

/// Build a Ix.Substring.
pub fn build_substring(ss: &Substring) -> IxSubstring {
  let obj = LeanCtor::alloc(0, 3, 0);
  obj.set(0, LeanString::from_str(ss.str.as_str()));
  obj.set(1, build_nat(&ss.start_pos));
  obj.set(2, build_nat(&ss.stop_pos));
  IxSubstring::new(*obj)
}

/// Build a Ix.SourceInfo.
pub fn build_source_info(si: &SourceInfo) -> IxSourceInfo {
  match si {
    // | original (leading : Substring) (pos : Nat) (trailing : Substring) (endPos : Nat) -- tag 0
    SourceInfo::Original(leading, pos, trailing, end_pos) => {
      let obj = LeanCtor::alloc(0, 4, 0);
      obj.set(0, build_substring(leading));
      obj.set(1, build_nat(pos));
      obj.set(2, build_substring(trailing));
      obj.set(3, build_nat(end_pos));
      IxSourceInfo::new(*obj)
    },
    // | synthetic (pos : Nat) (endPos : Nat) (canonical : Bool) -- tag 1
    SourceInfo::Synthetic(pos, end_pos, canonical) => {
      let obj = LeanCtor::alloc(1, 2, 1);
      obj.set(0, build_nat(pos));
      obj.set(1, build_nat(end_pos));
      obj.set_u8(2 * 8, *canonical as u8);
      IxSourceInfo::new(*obj)
    },
    // | none -- tag 2
    SourceInfo::None => IxSourceInfo::new(*LeanCtor::alloc(2, 0, 0)),
  }
}

/// Build a Ix.SyntaxPreresolved.
pub fn build_syntax_preresolved(
  cache: &mut LeanBuildCache,
  sp: &SyntaxPreresolved,
) -> IxSyntaxPreresolved {
  match sp {
    // | namespace (name : Name) -- tag 0
    SyntaxPreresolved::Namespace(name) => {
      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, build_name(cache, name));
      IxSyntaxPreresolved::new(*obj)
    },
    // | decl (name : Name) (aliases : Array String) -- tag 1
    SyntaxPreresolved::Decl(name, aliases) => {
      let name_obj = build_name(cache, name);
      let aliases_obj = build_string_array(aliases);
      let obj = LeanCtor::alloc(1, 2, 0);
      obj.set(0, name_obj);
      obj.set(1, aliases_obj);
      IxSyntaxPreresolved::new(*obj)
    },
  }
}

/// Build an Array of Strings.
pub fn build_string_array(strings: &[String]) -> LeanArray {
  let arr = LeanArray::alloc(strings.len());
  for (i, s) in strings.iter().enumerate() {
    arr.set(i, LeanString::from_str(s.as_str()));
  }
  arr
}

/// Build a Ix.Syntax.
pub fn build_syntax(cache: &mut LeanBuildCache, syn: &Syntax) -> IxSyntax {
  match syn {
    // | missing -- tag 0
    Syntax::Missing => IxSyntax::new(*LeanCtor::alloc(0, 0, 0)),
    // | node (info : SourceInfo) (kind : Name) (args : Array Syntax) -- tag 1
    Syntax::Node(info, kind, args) => {
      let info_obj = build_source_info(info);
      let kind_obj = build_name(cache, kind);
      let args_obj = build_syntax_array(cache, args);
      let obj = LeanCtor::alloc(1, 3, 0);
      obj.set(0, info_obj);
      obj.set(1, kind_obj);
      obj.set(2, args_obj);
      IxSyntax::new(*obj)
    },
    // | atom (info : SourceInfo) (val : String) -- tag 2
    Syntax::Atom(info, val) => {
      let info_obj = build_source_info(info);
      let obj = LeanCtor::alloc(2, 2, 0);
      obj.set(0, info_obj);
      obj.set(1, LeanString::from_str(val.as_str()));
      IxSyntax::new(*obj)
    },
    // | ident (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : Array SyntaxPreresolved) -- tag 3
    Syntax::Ident(info, raw_val, val, preresolved) => {
      let info_obj = build_source_info(info);
      let raw_val_obj = build_substring(raw_val);
      let val_obj = build_name(cache, val);
      let preresolved_obj =
        build_syntax_preresolved_array(cache, preresolved);
      let obj = LeanCtor::alloc(3, 4, 0);
      obj.set(0, info_obj);
      obj.set(1, raw_val_obj);
      obj.set(2, val_obj);
      obj.set(3, preresolved_obj);
      IxSyntax::new(*obj)
    },
  }
}

/// Build an Array of Syntax.
pub fn build_syntax_array(
  cache: &mut LeanBuildCache,
  items: &[Syntax],
) -> LeanArray {
  let arr = LeanArray::alloc(items.len());
  for (i, item) in items.iter().enumerate() {
    arr.set(i, build_syntax(cache, item));
  }
  arr
}

/// Build an Array of SyntaxPreresolved.
pub fn build_syntax_preresolved_array(
  cache: &mut LeanBuildCache,
  items: &[SyntaxPreresolved],
) -> LeanArray {
  let arr = LeanArray::alloc(items.len());
  for (i, item) in items.iter().enumerate() {
    arr.set(i, build_syntax_preresolved(cache, item));
  }
  arr
}

/// Build Ix.DataValue.
pub fn build_data_value(
  cache: &mut LeanBuildCache,
  dv: &DataValue,
) -> IxDataValue {
  match dv {
    DataValue::OfString(s) => {
      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, LeanString::from_str(s.as_str()));
      IxDataValue::new(*obj)
    },
    DataValue::OfBool(b) => {
      // 0 object fields, 1 scalar byte
      let obj = LeanCtor::alloc(1, 0, 1);
      obj.set_u8(0, *b as u8);
      IxDataValue::new(*obj)
    },
    DataValue::OfName(n) => {
      let obj = LeanCtor::alloc(2, 1, 0);
      obj.set(0, build_name(cache, n));
      IxDataValue::new(*obj)
    },
    DataValue::OfNat(n) => {
      let obj = LeanCtor::alloc(3, 1, 0);
      obj.set(0, build_nat(n));
      IxDataValue::new(*obj)
    },
    DataValue::OfInt(i) => {
      let obj = LeanCtor::alloc(4, 1, 0);
      obj.set(0, build_int(i));
      IxDataValue::new(*obj)
    },
    DataValue::OfSyntax(syn) => {
      let obj = LeanCtor::alloc(5, 1, 0);
      obj.set(0, build_syntax(cache, syn));
      IxDataValue::new(*obj)
    },
  }
}

/// Build an Array of (Name × DataValue) for mdata.
pub fn build_kvmap(
  cache: &mut LeanBuildCache,
  data: &[(Name, DataValue)],
) -> LeanArray {
  let arr = LeanArray::alloc(data.len());
  for (i, (name, dv)) in data.iter().enumerate() {
    let name_obj = build_name(cache, name);
    let dv_obj = build_data_value(cache, dv);
    // Prod (Name × DataValue)
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, name_obj);
    pair.set(1, dv_obj);
    arr.set(i, pair);
  }
  arr
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
pub extern "C" fn rs_roundtrip_ix_int(int_ptr: IxInt) -> IxInt {
  let int_val = decode_ix_int(int_ptr.as_ptr());
  build_int(&int_val)
}

/// Round-trip an Ix.Substring: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_substring(
  sub_ptr: IxSubstring,
) -> IxSubstring {
  let sub = decode_substring(sub_ptr.as_ptr());
  build_substring(&sub)
}

/// Round-trip an Ix.SourceInfo: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_source_info(
  si_ptr: IxSourceInfo,
) -> IxSourceInfo {
  let si = decode_ix_source_info(si_ptr.as_ptr());
  build_source_info(&si)
}

/// Round-trip an Ix.SyntaxPreresolved: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax_preresolved(
  sp_ptr: IxSyntaxPreresolved,
) -> IxSyntaxPreresolved {
  let sp = decode_syntax_preresolved(sp_ptr.as_ptr());
  let mut cache = LeanBuildCache::new();
  build_syntax_preresolved(&mut cache, &sp)
}

/// Round-trip an Ix.Syntax: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax(syn_ptr: IxSyntax) -> IxSyntax {
  let syn = decode_ix_syntax(syn_ptr.as_ptr());
  let mut cache = LeanBuildCache::new();
  build_syntax(&mut cache, &syn)
}

/// Round-trip an Ix.DataValue: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_data_value(
  dv_ptr: IxDataValue,
) -> IxDataValue {
  let dv = decode_data_value(dv_ptr.as_ptr());
  let mut cache = LeanBuildCache::new();
  build_data_value(&mut cache, &dv)
}
