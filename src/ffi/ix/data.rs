//! Ix.DataValue, Ix.Syntax, Ix.SourceInfo build/decode/roundtrip FFI.

use crate::ix::env::{
  DataValue, Int, Name, SourceInfo, Substring, Syntax, SyntaxPreresolved,
};
use crate::lean::nat::Nat;
use crate::lean::object::{
  LeanArray, LeanCtor, LeanIxDataValue, LeanIxInt, LeanIxSourceInfo,
  LeanIxSubstring, LeanIxSyntax, LeanIxSyntaxPreresolved, LeanObject,
  LeanString,
};

use crate::ffi::builder::LeanBuildCache;
use crate::ffi::ix::name::{build_name, decode_ix_name};
use crate::ffi::primitives::build_nat;

/// Build a Ix.Int (ofNat or negSucc).
pub fn build_int(int: &Int) -> LeanIxInt {
  match int {
    Int::OfNat(n) => {
      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, build_nat(n));
      LeanIxInt::new(*obj)
    },
    Int::NegSucc(n) => {
      let obj = LeanCtor::alloc(1, 1, 0);
      obj.set(0, build_nat(n));
      LeanIxInt::new(*obj)
    },
  }
}

/// Build a Ix.Substring.
pub fn build_substring(ss: &Substring) -> LeanIxSubstring {
  let obj = LeanCtor::alloc(0, 3, 0);
  obj.set(0, LeanString::new(ss.str.as_str()));
  obj.set(1, build_nat(&ss.start_pos));
  obj.set(2, build_nat(&ss.stop_pos));
  LeanIxSubstring::new(*obj)
}

/// Build a Ix.SourceInfo.
pub fn build_source_info(si: &SourceInfo) -> LeanIxSourceInfo {
  match si {
    // | original (leading : Substring) (pos : Nat) (trailing : Substring) (endPos : Nat) -- tag 0
    SourceInfo::Original(leading, pos, trailing, end_pos) => {
      let obj = LeanCtor::alloc(0, 4, 0);
      obj.set(0, build_substring(leading));
      obj.set(1, build_nat(pos));
      obj.set(2, build_substring(trailing));
      obj.set(3, build_nat(end_pos));
      LeanIxSourceInfo::new(*obj)
    },
    // | synthetic (pos : Nat) (endPos : Nat) (canonical : Bool) -- tag 1
    SourceInfo::Synthetic(pos, end_pos, canonical) => {
      let obj = LeanCtor::alloc(1, 2, 1);
      obj.set(0, build_nat(pos));
      obj.set(1, build_nat(end_pos));
      obj.set_u8(2 * 8, *canonical as u8);
      LeanIxSourceInfo::new(*obj)
    },
    // | none -- tag 2
    SourceInfo::None => LeanIxSourceInfo::new(*LeanCtor::alloc(2, 0, 0)),
  }
}

/// Build a Ix.SyntaxPreresolved.
pub fn build_syntax_preresolved(
  cache: &mut LeanBuildCache,
  sp: &SyntaxPreresolved,
) -> LeanIxSyntaxPreresolved {
  match sp {
    // | namespace (name : Name) -- tag 0
    SyntaxPreresolved::Namespace(name) => {
      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, build_name(cache, name));
      LeanIxSyntaxPreresolved::new(*obj)
    },
    // | decl (name : Name) (aliases : Array String) -- tag 1
    SyntaxPreresolved::Decl(name, aliases) => {
      let name_obj = build_name(cache, name);
      let aliases_obj = build_string_array(aliases);
      let obj = LeanCtor::alloc(1, 2, 0);
      obj.set(0, name_obj);
      obj.set(1, aliases_obj);
      LeanIxSyntaxPreresolved::new(*obj)
    },
  }
}

/// Build an Array of Strings.
pub fn build_string_array(strings: &[String]) -> LeanArray {
  let arr = LeanArray::alloc(strings.len());
  for (i, s) in strings.iter().enumerate() {
    arr.set(i, LeanString::new(s.as_str()));
  }
  arr
}

/// Build a Ix.Syntax.
pub fn build_syntax(cache: &mut LeanBuildCache, syn: &Syntax) -> LeanIxSyntax {
  match syn {
    // | missing -- tag 0
    Syntax::Missing => LeanIxSyntax::new(*LeanCtor::alloc(0, 0, 0)),
    // | node (info : SourceInfo) (kind : Name) (args : Array Syntax) -- tag 1
    Syntax::Node(info, kind, args) => {
      let info_obj = build_source_info(info);
      let kind_obj = build_name(cache, kind);
      let args_obj = build_syntax_array(cache, args);
      let obj = LeanCtor::alloc(1, 3, 0);
      obj.set(0, info_obj);
      obj.set(1, kind_obj);
      obj.set(2, args_obj);
      LeanIxSyntax::new(*obj)
    },
    // | atom (info : SourceInfo) (val : String) -- tag 2
    Syntax::Atom(info, val) => {
      let info_obj = build_source_info(info);
      let obj = LeanCtor::alloc(2, 2, 0);
      obj.set(0, info_obj);
      obj.set(1, LeanString::new(val.as_str()));
      LeanIxSyntax::new(*obj)
    },
    // | ident (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : Array SyntaxPreresolved) -- tag 3
    Syntax::Ident(info, raw_val, val, preresolved) => {
      let info_obj = build_source_info(info);
      let raw_val_obj = build_substring(raw_val);
      let val_obj = build_name(cache, val);
      let preresolved_obj = build_syntax_preresolved_array(cache, preresolved);
      let obj = LeanCtor::alloc(3, 4, 0);
      obj.set(0, info_obj);
      obj.set(1, raw_val_obj);
      obj.set(2, val_obj);
      obj.set(3, preresolved_obj);
      LeanIxSyntax::new(*obj)
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
) -> LeanIxDataValue {
  match dv {
    DataValue::OfString(s) => {
      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, LeanString::new(s.as_str()));
      LeanIxDataValue::new(*obj)
    },
    DataValue::OfBool(b) => {
      // 0 object fields, 1 scalar byte
      let obj = LeanCtor::alloc(1, 0, 1);
      obj.set_u8(0, *b as u8);
      LeanIxDataValue::new(*obj)
    },
    DataValue::OfName(n) => {
      let obj = LeanCtor::alloc(2, 1, 0);
      obj.set(0, build_name(cache, n));
      LeanIxDataValue::new(*obj)
    },
    DataValue::OfNat(n) => {
      let obj = LeanCtor::alloc(3, 1, 0);
      obj.set(0, build_nat(n));
      LeanIxDataValue::new(*obj)
    },
    DataValue::OfInt(i) => {
      let obj = LeanCtor::alloc(4, 1, 0);
      obj.set(0, build_int(i));
      LeanIxDataValue::new(*obj)
    },
    DataValue::OfSyntax(syn) => {
      let obj = LeanCtor::alloc(5, 1, 0);
      obj.set(0, build_syntax(cache, syn));
      LeanIxDataValue::new(*obj)
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

/// Decode Ix.Int from Lean object.
/// Ix.Int: ofNat (tag 0, 1 field) | negSucc (tag 1, 1 field)
pub fn decode_ix_int(obj: LeanObject) -> Int {
  let ctor = obj.as_ctor();
  let nat = Nat::from_obj(ctor.get(0));
  match ctor.tag() {
    0 => Int::OfNat(nat),
    1 => Int::NegSucc(nat),
    _ => panic!("Invalid Ix.Int tag: {}", ctor.tag()),
  }
}

/// Decode Ix.DataValue from a Lean object.
pub fn decode_data_value(obj: LeanObject) -> DataValue {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      // ofString: 1 object field
      DataValue::OfString(ctor.get(0).as_string().to_string())
    },
    1 => {
      // ofBool: 0 object fields, 1 scalar byte
      let b = ctor.scalar_u8(0, 0) != 0;
      DataValue::OfBool(b)
    },
    2 => {
      // ofName: 1 object field
      DataValue::OfName(decode_ix_name(ctor.get(0)))
    },
    3 => {
      // ofNat: 1 object field
      DataValue::OfNat(Nat::from_obj(ctor.get(0)))
    },
    4 => {
      // ofInt: 1 object field
      let inner = ctor.get(0);
      let inner_ctor = inner.as_ctor();
      let nat = Nat::from_obj(inner_ctor.get(0));
      match inner_ctor.tag() {
        0 => DataValue::OfInt(Int::OfNat(nat)),
        1 => DataValue::OfInt(Int::NegSucc(nat)),
        _ => panic!("Invalid Int tag: {}", inner_ctor.tag()),
      }
    },
    5 => {
      // ofSyntax: 1 object field
      DataValue::OfSyntax(decode_ix_syntax(ctor.get(0)).into())
    },
    _ => panic!("Invalid DataValue tag: {}", ctor.tag()),
  }
}

/// Decode Ix.Syntax from a Lean object.
pub fn decode_ix_syntax(obj: LeanObject) -> Syntax {
  if obj.is_scalar() {
    return Syntax::Missing;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => Syntax::Missing,
    1 => {
      // node: info, kind, args
      let info = decode_ix_source_info(ctor.get(0));
      let kind = decode_ix_name(ctor.get(1));
      let args: Vec<Syntax> = ctor.get(2).as_array().map(decode_ix_syntax);

      Syntax::Node(info, kind, args)
    },
    2 => {
      // atom: info, val
      let info = decode_ix_source_info(ctor.get(0));
      Syntax::Atom(info, ctor.get(1).as_string().to_string())
    },
    3 => {
      // ident: info, rawVal, val, preresolved
      let info = decode_ix_source_info(ctor.get(0));
      let raw_val = decode_substring(ctor.get(1));
      let val = decode_ix_name(ctor.get(2));
      let preresolved: Vec<SyntaxPreresolved> =
        ctor.get(3).as_array().map(decode_syntax_preresolved);

      Syntax::Ident(info, raw_val, val, preresolved)
    },
    _ => panic!("Invalid Syntax tag: {}", ctor.tag()),
  }
}

/// Decode Ix.SourceInfo.
pub fn decode_ix_source_info(obj: LeanObject) -> SourceInfo {
  if obj.is_scalar() {
    return SourceInfo::None;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      // original
      SourceInfo::Original(
        decode_substring(ctor.get(0)),
        Nat::from_obj(ctor.get(1)),
        decode_substring(ctor.get(2)),
        Nat::from_obj(ctor.get(3)),
      )
    },
    1 => {
      // synthetic: 2 obj fields (pos, end_pos), 1 scalar byte (canonical)
      let canonical = ctor.scalar_u8(2, 0) != 0;

      SourceInfo::Synthetic(
        Nat::from_obj(ctor.get(0)),
        Nat::from_obj(ctor.get(1)),
        canonical,
      )
    },
    2 => SourceInfo::None,
    _ => panic!("Invalid SourceInfo tag: {}", ctor.tag()),
  }
}

/// Decode Ix.Substring.
pub fn decode_substring(obj: LeanObject) -> Substring {
  let ctor = obj.as_ctor();
  Substring {
    str: ctor.get(0).as_string().to_string(),
    start_pos: Nat::from_obj(ctor.get(1)),
    stop_pos: Nat::from_obj(ctor.get(2)),
  }
}

/// Decode Ix.SyntaxPreresolved.
pub fn decode_syntax_preresolved(obj: LeanObject) -> SyntaxPreresolved {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      // namespace
      SyntaxPreresolved::Namespace(decode_ix_name(ctor.get(0)))
    },
    1 => {
      // decl
      let name = decode_ix_name(ctor.get(0));
      let aliases: Vec<String> =
        ctor.get(1).as_array().map(|obj| obj.as_string().to_string());

      SyntaxPreresolved::Decl(name, aliases)
    },
    _ => panic!("Invalid SyntaxPreresolved tag: {}", ctor.tag()),
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip an Ix.Int: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_int(int_ptr: LeanIxInt) -> LeanIxInt {
  let int_val = decode_ix_int(*int_ptr);
  build_int(&int_val)
}

/// Round-trip an Ix.Substring: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_substring(
  sub_ptr: LeanIxSubstring,
) -> LeanIxSubstring {
  let sub = decode_substring(*sub_ptr);
  build_substring(&sub)
}

/// Round-trip an Ix.SourceInfo: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_source_info(
  si_ptr: LeanIxSourceInfo,
) -> LeanIxSourceInfo {
  let si = decode_ix_source_info(*si_ptr);
  build_source_info(&si)
}

/// Round-trip an Ix.SyntaxPreresolved: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax_preresolved(
  sp_ptr: LeanIxSyntaxPreresolved,
) -> LeanIxSyntaxPreresolved {
  let sp = decode_syntax_preresolved(*sp_ptr);
  let mut cache = LeanBuildCache::new();
  build_syntax_preresolved(&mut cache, &sp)
}

/// Round-trip an Ix.Syntax: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax(
  syn_ptr: LeanIxSyntax,
) -> LeanIxSyntax {
  let syn = decode_ix_syntax(*syn_ptr);
  let mut cache = LeanBuildCache::new();
  build_syntax(&mut cache, &syn)
}

/// Round-trip an Ix.DataValue: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_data_value(
  dv_ptr: LeanIxDataValue,
) -> LeanIxDataValue {
  let dv = decode_data_value(*dv_ptr);
  let mut cache = LeanBuildCache::new();
  build_data_value(&mut cache, &dv)
}
