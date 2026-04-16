//! Ix.DataValue, Ix.Syntax, Ix.SourceInfo build/decode/roundtrip FFI.

use crate::ix::env::{
  DataValue, Int, Name, SourceInfo, Substring, Syntax, SyntaxPreresolved,
};
use crate::lean::{
  LeanIxDataValue, LeanIxInt, LeanIxName, LeanIxSourceInfo, LeanIxSubstring,
  LeanIxSyntax, LeanIxSyntaxPreresolved,
};
use lean_ffi::nat::Nat;
#[cfg(feature = "test-ffi")]
use lean_ffi::object::LeanBorrowed;
use lean_ffi::object::{LeanArray, LeanOwned, LeanProd, LeanRef, LeanString};

use crate::ffi::builder::LeanBuildCache;

impl LeanIxInt<LeanOwned> {
  /// Build a Ix.Int (ofNat or negSucc).
  pub fn build(int: &Int) -> Self {
    match int {
      Int::OfNat(n) => {
        let ctor = LeanIxInt::alloc(0);
        ctor.set_obj(0, Nat::to_lean(n));
        ctor
      },
      Int::NegSucc(n) => {
        let ctor = LeanIxInt::alloc(1);
        ctor.set_obj(0, Nat::to_lean(n));
        ctor
      },
    }
  }
}

impl<R: LeanRef> LeanIxInt<R> {
  /// Decode Ix.Int from Lean object.
  /// Ix.Int: ofNat (tag 0, 1 field) | negSucc (tag 1, 1 field)
  pub fn decode(&self) -> Int {
    let ctor = self.as_ctor();
    let nat = Nat::from_obj(&ctor.get(0));
    match ctor.tag() {
      0 => Int::OfNat(nat),
      1 => Int::NegSucc(nat),
      _ => panic!("Invalid Ix.Int tag: {}", ctor.tag()),
    }
  }
}

impl LeanIxSubstring<LeanOwned> {
  /// Build a Ix.Substring.
  pub fn build(ss: &Substring) -> Self {
    let ctor = LeanIxSubstring::alloc(0);
    ctor.set_obj(0, LeanString::new(ss.str.as_str()));
    ctor.set_obj(1, Nat::to_lean(&ss.start_pos));
    ctor.set_obj(2, Nat::to_lean(&ss.stop_pos));
    ctor
  }
}

impl<R: LeanRef> LeanIxSubstring<R> {
  /// Decode Ix.Substring.
  pub fn decode(&self) -> Substring {
    let ctor = self.as_ctor();
    Substring {
      str: ctor.get(0).as_string().to_string(),
      start_pos: Nat::from_obj(&ctor.get(1)),
      stop_pos: Nat::from_obj(&ctor.get(2)),
    }
  }
}

impl LeanIxSourceInfo<LeanOwned> {
  /// Build a Ix.SourceInfo.
  pub fn build(si: &SourceInfo) -> Self {
    match si {
      // | original (leading : Substring) (pos : Nat) (trailing : Substring) (endPos : Nat) -- tag 0
      SourceInfo::Original(leading, pos, trailing, end_pos) => {
        let ctor = LeanIxSourceInfo::alloc(0);
        ctor.set_obj(0, LeanIxSubstring::build(leading));
        ctor.set_obj(1, Nat::to_lean(pos));
        ctor.set_obj(2, LeanIxSubstring::build(trailing));
        ctor.set_obj(3, Nat::to_lean(end_pos));
        ctor
      },
      // | synthetic (pos : Nat) (endPos : Nat) (canonical : Bool) -- tag 1
      SourceInfo::Synthetic(pos, end_pos, canonical) => {
        let ctor = LeanIxSourceInfo::alloc(1);
        ctor.set_obj(0, Nat::to_lean(pos));
        ctor.set_obj(1, Nat::to_lean(end_pos));
        ctor.set_num_8(0, *canonical as u8);
        ctor
      },
      // | none -- tag 2 (no fields — scalar)
      SourceInfo::None => Self::new(LeanOwned::box_usize(2)),
    }
  }
}

impl<R: LeanRef> LeanIxSourceInfo<R> {
  /// Decode Ix.SourceInfo.
  pub fn decode(&self) -> SourceInfo {
    if self.inner().is_scalar() {
      return SourceInfo::None;
    }
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // original
        SourceInfo::Original(
          LeanIxSubstring(ctor.get(0)).decode(),
          Nat::from_obj(&ctor.get(1)),
          LeanIxSubstring(ctor.get(2)).decode(),
          Nat::from_obj(&ctor.get(3)),
        )
      },
      1 => {
        // synthetic: 2 obj fields (pos, end_pos), 1 scalar byte (canonical)
        let canonical = self.get_num_8(0) != 0;

        SourceInfo::Synthetic(
          Nat::from_obj(&self.get_obj(0)),
          Nat::from_obj(&self.get_obj(1)),
          canonical,
        )
      },
      2 => SourceInfo::None,
      _ => panic!("Invalid SourceInfo tag: {}", ctor.tag()),
    }
  }
}

impl LeanIxSyntaxPreresolved<LeanOwned> {
  /// Build a Ix.SyntaxPreresolved.
  pub fn build(cache: &mut LeanBuildCache, sp: &SyntaxPreresolved) -> Self {
    match sp {
      // | namespace (name : Name) -- tag 0
      SyntaxPreresolved::Namespace(name) => {
        let ctor = LeanIxSyntaxPreresolved::alloc(0);
        ctor.set_obj(0, LeanIxName::build(cache, name));
        ctor
      },
      // | decl (name : Name) (aliases : Array String) -- tag 1
      SyntaxPreresolved::Decl(name, aliases) => {
        let ctor = LeanIxSyntaxPreresolved::alloc(1);
        ctor.set_obj(0, LeanIxName::build(cache, name));
        ctor.set_obj(1, build_string_array(aliases));
        ctor
      },
    }
  }
}

impl<R: LeanRef> LeanIxSyntaxPreresolved<R> {
  /// Decode Ix.SyntaxPreresolved.
  pub fn decode(&self) -> SyntaxPreresolved {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // namespace
        SyntaxPreresolved::Namespace(LeanIxName(ctor.get(0)).decode())
      },
      1 => {
        // decl
        let name = LeanIxName(ctor.get(0)).decode();
        let aliases: Vec<String> =
          ctor.get(1).as_array().map(|obj| obj.as_string().to_string());

        SyntaxPreresolved::Decl(name, aliases)
      },
      _ => panic!("Invalid SyntaxPreresolved tag: {}", ctor.tag()),
    }
  }
}

/// Build an Array of Strings.
pub fn build_string_array(strings: &[String]) -> LeanArray<LeanOwned> {
  let arr = LeanArray::alloc(strings.len());
  for (i, s) in strings.iter().enumerate() {
    arr.set(i, LeanString::new(s.as_str()));
  }
  arr
}

impl LeanIxSyntax<LeanOwned> {
  /// Build a Ix.Syntax.
  pub fn build(cache: &mut LeanBuildCache, syn: &Syntax) -> Self {
    match syn {
      // | missing -- tag 0 (no fields — scalar)
      Syntax::Missing => Self::new(LeanOwned::box_usize(0)),
      // | node (info : SourceInfo) (kind : Name) (args : Array Syntax) -- tag 1
      Syntax::Node(info, kind, args) => {
        let ctor = LeanIxSyntax::alloc(1);
        ctor.set_obj(0, LeanIxSourceInfo::build(info));
        ctor.set_obj(1, LeanIxName::build(cache, kind));
        ctor.set_obj(2, Self::build_array(cache, args));
        ctor
      },
      // | atom (info : SourceInfo) (val : String) -- tag 2
      Syntax::Atom(info, val) => {
        let ctor = LeanIxSyntax::alloc(2);
        ctor.set_obj(0, LeanIxSourceInfo::build(info));
        ctor.set_obj(1, LeanString::new(val.as_str()));
        ctor
      },
      // | ident (info : SourceInfo) (rawVal : Substring) (val : Name) (preresolved : Array SyntaxPreresolved) -- tag 3
      Syntax::Ident(info, raw_val, val, preresolved) => {
        let ctor = LeanIxSyntax::alloc(3);
        ctor.set_obj(0, LeanIxSourceInfo::build(info));
        ctor.set_obj(1, LeanIxSubstring::build(raw_val));
        ctor.set_obj(2, LeanIxName::build(cache, val));
        ctor.set_obj(3, Self::build_preresolved_array(cache, preresolved));
        ctor
      },
    }
  }

  /// Build an Array of Syntax.
  pub fn build_array(
    cache: &mut LeanBuildCache,
    items: &[Syntax],
  ) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(items.len());
    for (i, item) in items.iter().enumerate() {
      arr.set(i, Self::build(cache, item));
    }
    arr
  }

  /// Build an Array of SyntaxPreresolved.
  fn build_preresolved_array(
    cache: &mut LeanBuildCache,
    items: &[SyntaxPreresolved],
  ) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(items.len());
    for (i, item) in items.iter().enumerate() {
      arr.set(i, LeanIxSyntaxPreresolved::build(cache, item));
    }
    arr
  }
}

impl<R: LeanRef> LeanIxSyntax<R> {
  /// Decode Ix.Syntax from a Lean object.
  pub fn decode(&self) -> Syntax {
    if self.inner().is_scalar() {
      return Syntax::Missing;
    }
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => Syntax::Missing,
      1 => {
        // node: info, kind, args
        let info = LeanIxSourceInfo(ctor.get(0)).decode();
        let kind = LeanIxName(ctor.get(1)).decode();
        let args: Vec<Syntax> =
          ctor.get(2).as_array().map(|x| LeanIxSyntax(x).decode());

        Syntax::Node(info, kind, args)
      },
      2 => {
        // atom: info, val
        let info = LeanIxSourceInfo(ctor.get(0)).decode();
        Syntax::Atom(info, ctor.get(1).as_string().to_string())
      },
      3 => {
        // ident: info, rawVal, val, preresolved
        let info = LeanIxSourceInfo(ctor.get(0)).decode();
        let raw_val = LeanIxSubstring(ctor.get(1)).decode();
        let val = LeanIxName(ctor.get(2)).decode();
        let preresolved: Vec<SyntaxPreresolved> =
          ctor.get(3).as_array().map(|x| LeanIxSyntaxPreresolved(x).decode());

        Syntax::Ident(info, raw_val, val, preresolved)
      },
      _ => panic!("Invalid Syntax tag: {}", ctor.tag()),
    }
  }
}

impl LeanIxDataValue<LeanOwned> {
  /// Build Ix.DataValue.
  pub fn build(cache: &mut LeanBuildCache, dv: &DataValue) -> Self {
    match dv {
      DataValue::OfString(s) => {
        let ctor = LeanIxDataValue::alloc(0);
        ctor.set_obj(0, LeanString::new(s.as_str()));
        ctor
      },
      DataValue::OfBool(b) => {
        let ctor = LeanIxDataValue::alloc(1);
        ctor.set_num_8(0, *b as u8);
        ctor
      },
      DataValue::OfName(n) => {
        let ctor = LeanIxDataValue::alloc(2);
        ctor.set_obj(0, LeanIxName::build(cache, n));
        ctor
      },
      DataValue::OfNat(n) => {
        let ctor = LeanIxDataValue::alloc(3);
        ctor.set_obj(0, Nat::to_lean(n));
        ctor
      },
      DataValue::OfInt(i) => {
        let ctor = LeanIxDataValue::alloc(4);
        ctor.set_obj(0, LeanIxInt::build(i));
        ctor
      },
      DataValue::OfSyntax(syn) => {
        let ctor = LeanIxDataValue::alloc(5);
        ctor.set_obj(0, LeanIxSyntax::build(cache, syn));
        ctor
      },
    }
  }

  /// Build an Array of (Name x DataValue) for mdata.
  pub fn build_kvmap(
    cache: &mut LeanBuildCache,
    data: &[(Name, DataValue)],
  ) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(data.len());
    for (i, (name, dv)) in data.iter().enumerate() {
      let name_obj = LeanIxName::build(cache, name);
      let dv_obj = Self::build(cache, dv);
      // Prod (Name x DataValue)
      let pair = LeanProd::new(name_obj, dv_obj);
      arr.set(i, pair);
    }
    arr
  }
}

impl<R: LeanRef> LeanIxDataValue<R> {
  /// Decode Ix.DataValue from a Lean object.
  pub fn decode(&self) -> DataValue {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // ofString: 1 object field
        DataValue::OfString(ctor.get(0).as_string().to_string())
      },
      1 => {
        // ofBool: 0 object fields, 1 scalar byte
        let b = self.get_num_8(0) != 0;
        DataValue::OfBool(b)
      },
      2 => {
        // ofName: 1 object field
        DataValue::OfName(LeanIxName(ctor.get(0)).decode())
      },
      3 => {
        // ofNat: 1 object field
        DataValue::OfNat(Nat::from_obj(&ctor.get(0)))
      },
      4 => {
        // ofInt: 1 object field
        let inner = ctor.get(0);
        let inner_ctor = inner.as_ctor();
        let nat = Nat::from_obj(&inner_ctor.get(0));
        match inner_ctor.tag() {
          0 => DataValue::OfInt(Int::OfNat(nat)),
          1 => DataValue::OfInt(Int::NegSucc(nat)),
          _ => panic!("Invalid Int tag: {}", inner_ctor.tag()),
        }
      },
      5 => {
        // ofSyntax: 1 object field
        DataValue::OfSyntax(LeanIxSyntax(ctor.get(0)).decode().into())
      },
      _ => panic!("Invalid DataValue tag: {}", ctor.tag()),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip an Ix.Int: decode from Lean, re-encode.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_int(
  int_ptr: LeanIxInt<LeanBorrowed<'_>>,
) -> LeanIxInt<LeanOwned> {
  let int_val = int_ptr.decode();
  LeanIxInt::build(&int_val)
}

/// Round-trip an Ix.Substring: decode from Lean, re-encode.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_substring(
  sub_ptr: LeanIxSubstring<LeanBorrowed<'_>>,
) -> LeanIxSubstring<LeanOwned> {
  let sub = sub_ptr.decode();
  LeanIxSubstring::build(&sub)
}

/// Round-trip an Ix.SourceInfo: decode from Lean, re-encode.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_source_info(
  si_ptr: LeanIxSourceInfo<LeanBorrowed<'_>>,
) -> LeanIxSourceInfo<LeanOwned> {
  let si = si_ptr.decode();
  LeanIxSourceInfo::build(&si)
}

/// Round-trip an Ix.SyntaxPreresolved: decode from Lean, re-encode.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax_preresolved(
  sp_ptr: LeanIxSyntaxPreresolved<LeanBorrowed<'_>>,
) -> LeanIxSyntaxPreresolved<LeanOwned> {
  let sp = sp_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxSyntaxPreresolved::build(&mut cache, &sp)
}

/// Round-trip an Ix.Syntax: decode from Lean, re-encode.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_syntax(
  syn_ptr: LeanIxSyntax<LeanBorrowed<'_>>,
) -> LeanIxSyntax<LeanOwned> {
  let syn = syn_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxSyntax::build(&mut cache, &syn)
}

/// Round-trip an Ix.DataValue: decode from Lean, re-encode.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_data_value(
  dv_ptr: LeanIxDataValue<LeanBorrowed<'_>>,
) -> LeanIxDataValue<LeanOwned> {
  let dv = dv_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxDataValue::build(&mut cache, &dv)
}
