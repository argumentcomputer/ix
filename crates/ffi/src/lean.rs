//! Ix-specific Lean domain type definitions.
//!
//! Ctor-backed types use `lean_inductive!` which declares the domain type,
//! layout metadata (one entry per Lean constructor), and typed accessors.
//! Types without a ctor layout (simple enums, opaque objects, arenas) use
//! bare `lean_domain_type!`.

use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanOwned, LeanRef};

// =============================================================================
// Types without ctor layouts
// =============================================================================

lean_ffi::lean_domain_type! {
  // Simple enums (passed as raw unboxed tag values)
  LeanIxBinderInfo;
  LeanIxonDefKind;
  LeanIxonDefinitionSafety;
  LeanIxonQuotKind;

  // Opaque types (passed through without field access)
  LeanIxonExprMetaArena;
}

// =============================================================================
// Ctor-backed types
// =============================================================================

lean_ffi::lean_inductive! {
  // --- Ixon structures (single-constructor) ---

  LeanIxonValueContract  [ { num_8: 2 } ];
  LeanIxonBinderContract [ { num_obj: 1, num_8: 1 } ];
  LeanIxonLetContract    [ { num_obj: 1, num_8: 2 } ];
  LeanIxonDefinition      [ { num_obj: 2, num_64: 1, num_8: 2 } ];
  LeanIxonRecursorRule    [ { num_obj: 1, num_64: 1 } ];
  LeanIxonRecursor        [ { num_obj: 2, num_64: 5, num_8: 2 } ];
  LeanIxonAxiom           [ { num_obj: 1, num_64: 1, num_8: 1 } ];
  LeanIxonQuotient        [ { num_obj: 1, num_64: 1, num_8: 1 } ];
  LeanIxonConstructor     [ { num_obj: 1, num_64: 4, num_8: 1 } ];
  LeanIxonInductive       [ { num_obj: 2, num_64: 3, num_8: 1 } ];
  LeanIxonInductiveProj   [ { num_obj: 1, num_64: 1 } ];
  LeanIxonConstructorProj [ { num_obj: 1, num_64: 2 } ];
  LeanIxonRecursorProj    [ { num_obj: 1, num_64: 1 } ];
  LeanIxonDefinitionProj  [ { num_obj: 1, num_64: 1 } ];
  LeanIxonNamed           [ { num_obj: 4 } ];
  LeanIxonComm            [ { num_obj: 2 } ];
  LeanIxonConstant        [ { num_obj: 5 } ];
  LeanIxonBinderBlock     [ { num_obj: 1, num_64: 2, num_8: 1 } ];
  LeanIxonRawConst        [ { num_obj: 2 } ];
  // name, addr, constMeta, original, hints
  LeanIxonRawNamed        [ { num_obj: 5 } ];
  LeanIxonRawBlob         [ { num_obj: 2 } ];
  LeanIxonRoleBinding     [ { num_obj: 2 } ];
  LeanIxonRawComm         [ { num_obj: 2 } ];
  LeanIxonRawNameEntry    [ { num_obj: 2 } ];
  // consts, named, blobs, comms, names, main, assumptions, anonHints,
  // roleBinding
  LeanIxonRawEnv          [ { num_obj: 9 } ];

  // Lazy/anon deserialization (`rs_de_env_lazy`): zero-copy const windows
  // (addr + offset + len), name->addr, copied blobs, the bundle header
  // fields (main, assumptions), and the hints-section pairs.
  LeanIxonRawConstSlice   [ { num_obj: 1, num_64: 2 } ];
  LeanIxonRawNamedLite    [ { num_obj: 3 } ];
  LeanIxonRawEnvLazy      [ { num_obj: 7 } ];

  // Env diff report (`rs_diff_envs`). Slot counts MUST match the Lean
  // structures in Ix/Ixon.lean (Ixon.EnvStats / NamedDiff / EnvDiff).
  // consts, named, blobs, comms counts
  LeanIxonEnvStats        [ { num_64: 4 } ];
  // name, oldAddr, newAddr, oldKind, newKind, fields, metaFields
  // + rippled (Bool scalar)
  LeanIxonNamedDiff       [ { num_obj: 7, num_8: 1 } ];
  // mainChanged, assumptions±, named±/changed/metaOnly, comms±/changed,
  // constsOnly×2, blobsOnly×2, hintsChanged, statsA, statsB,
  // roleBindingChanged
  LeanIxonEnvDiff         [ { num_obj: 18 } ];

  // --- Ixon multi-variant inductives ---

  LeanIxonBinderNode [
    { },                                      // tag 0: never (scalar)
    { },                                      // tag 1: zero (scalar)
    { num_obj: 1 },                           // tag 2: ifAllZero
    { num_64: 1 },                            // tag 3: share
    { },                                      // tag 4: undecided (scalar)
  ];

  LeanIxonUniv [
    { },                                      // tag 0: zero
    { num_obj: 1 },                           // tag 1: succ
    { num_obj: 2 },                           // tag 2: max
    { num_obj: 2 },                           // tag 3: imax
    { num_64: 1 },                            // tag 4: var
  ];

  LeanIxonExpr [
    { num_64: 1 },                            // tag 0: sort
    { num_64: 1 },                            // tag 1: var
    { num_obj: 1, num_64: 1 },                // tag 2: ref
    { num_obj: 1, num_64: 1 },                // tag 3: rec
    { num_obj: 1, num_64: 2 },                // tag 4: prj
    { num_64: 1 },                            // tag 5: str
    { num_64: 1 },                            // tag 6: nat
    { num_obj: 2 },                           // tag 7: app
    { num_obj: 3 },                           // tag 8: lam
    { num_obj: 4 },                           // tag 9: all
    { num_obj: 4 },                           // tag 10: let
    { num_64: 1 },                            // tag 11: share
  ];

  LeanIxonExprMetaData [
    { },                                      // tag 0: leaf (scalar)
    { num_64: 2 },                            // tag 1: app
    { num_obj: 1, num_64: 2, num_8: 1 },      // tag 2: binder
    { num_obj: 1, num_64: 3 },                // tag 3: letBinder
    { num_obj: 1 },                           // tag 4: ref
    { num_obj: 1, num_64: 1 },                // tag 5: prj
    { num_obj: 1, num_64: 1 },                // tag 6: mdata
  ];

  // perm, sourceCtorCounts, evaporated (all Array UInt64; evaporated is 0/1)
  LeanIxonAuxLayout       [ { num_obj: 3 } ];

  LeanIxonConstantMetaInfo [
    { },                                      // tag 0: empty (scalar)
    { num_obj: 5, num_64: 2 },                // tag 1: defn
    { num_obj: 3, num_64: 1 },                // tag 2: axio
    { num_obj: 3, num_64: 1 },                // tag 3: quot
    { num_obj: 6, num_64: 1 },                // tag 4: indc
    { num_obj: 4, num_64: 1 },                // tag 5: ctor
    { num_obj: 7, num_64: 1 },                // tag 6: recr
    { num_obj: 2 },                           // tag 7: muts (all, auxLayout)
  ];

  // univIdxs (Array UInt64) + arenaIdx (UInt64 scalar)
  LeanIxonUnivPatch       [ { num_obj: 1, num_64: 1 } ];

  // Wrapper structure: info, metaSharing, metaRefs, metaUnivs, univPatches
  LeanIxonConstantMeta    [ { num_obj: 5 } ];

  LeanIxonDataValue [
    { num_obj: 1 },                           // tag 0: ofString
    { num_8: 1 },                             // tag 1: ofBool
    { num_obj: 1 },                           // tag 2: ofName
    { num_obj: 1 },                           // tag 3: ofNat
    { num_obj: 1 },                           // tag 4: ofInt
    { num_obj: 1 },                           // tag 5: ofSyntax
  ];

  LeanIxonMutConst [
    { num_obj: 1 },                           // tag 0: defn
    { num_obj: 1 },                           // tag 1: indc
    { num_obj: 1 },                           // tag 2: recr
  ];

  LeanIxonConstantInfo [
    { num_obj: 1 },                           // tag 0: defn
    { num_obj: 1 },                           // tag 1: recr
    { num_obj: 1 },                           // tag 2: axio
    { num_obj: 1 },                           // tag 3: quot
    { num_obj: 1 },                           // tag 4: cPrj
    { num_obj: 1 },                           // tag 5: rPrj
    { num_obj: 1 },                           // tag 6: iPrj
    { num_obj: 1 },                           // tag 7: dPrj
    { num_obj: 1 },                           // tag 8: muts
  ];

  // --- Ix multi-variant inductives ---

  LeanIxName [
    { num_obj: 1 },                           // tag 0: anonymous
    { num_obj: 3 },                           // tag 1: str
    { num_obj: 3 },                           // tag 2: num
  ];

  LeanIxReducibilityHints [
    { },                                      // tag 0: opaque (scalar)
    { },                                      // tag 1: abbrev (scalar)
    { num_32: 1 },                            // tag 2: regular
  ];

  // --- Iroh types ---

  LeanPutResponse [ { num_obj: 2 } ];
  LeanGetResponse [ { num_obj: 3 } ];
}

// =============================================================================
// LeanIxAddress — manual newtype over LeanByteArray
// =============================================================================

/// Lean `Address` object — newtype over `LeanByteArray`.
///
/// Address is a single-field struct in Lean, so it's unboxed to ByteArray
/// at the FFI boundary.
#[repr(transparent)]
pub struct LeanIxAddress<R: LeanRef>(LeanByteArray<R>);

impl<R: LeanRef> Clone for LeanIxAddress<R> {
  #[inline]
  fn clone(&self) -> Self {
    Self(self.0.clone())
  }
}

impl<R: LeanRef + Copy> Copy for LeanIxAddress<R> {}

impl<R: LeanRef> std::ops::Deref for LeanIxAddress<R> {
  type Target = LeanByteArray<R>;
  #[inline]
  fn deref(&self) -> &LeanByteArray<R> {
    &self.0
  }
}

impl From<LeanIxAddress<LeanOwned>> for LeanOwned {
  #[inline]
  fn from(x: LeanIxAddress<LeanOwned>) -> Self {
    x.0.into()
  }
}

impl<'a> From<LeanByteArray<LeanBorrowed<'a>>>
  for LeanIxAddress<LeanBorrowed<'a>>
{
  #[inline]
  fn from(x: LeanByteArray<LeanBorrowed<'a>>) -> Self {
    Self(x)
  }
}

impl From<LeanByteArray<LeanOwned>> for LeanIxAddress<LeanOwned> {
  #[inline]
  fn from(x: LeanByteArray<LeanOwned>) -> Self {
    Self(x)
  }
}

impl LeanIxAddress<LeanOwned> {
  #[inline]
  pub fn new(ba: LeanByteArray<LeanOwned>) -> Self {
    Self(ba)
  }
}

impl<'a> LeanIxAddress<LeanBorrowed<'a>> {
  #[inline]
  pub fn from_borrowed(ba: LeanByteArray<LeanBorrowed<'a>>) -> Self {
    Self(ba)
  }
}

// =============================================================================
// LeanBuildCache & Scalar Domain Builders/Decoders
// =============================================================================

use ix_common::address::Address;
use ix_common::env::{BinderInfo, Name, NameData, ReducibilityHints};
use lean_ffi::object::{LeanArray, LeanNat, LeanString};
use rustc_hash::FxHashMap;

/// Deduplication cache for constructing Lean objects during FFI calls.
#[derive(Default)]
pub struct LeanBuildCache {
  /// Cached `Ix.Name` objects keyed by content hash.
  pub names: FxHashMap<blake3::Hash, LeanIxName<LeanOwned>>,
}

impl LeanBuildCache {
  /// Create an empty build cache.
  pub fn new() -> Self {
    Self::default()
  }
}

impl LeanIxAddress<LeanOwned> {
  /// Construct a Lean `Address` (`ByteArray` of length 32).
  pub fn build(addr: &Address) -> Self {
    LeanIxAddress::new(LeanByteArray::from_bytes(addr.as_bytes()))
  }

  /// Construct a Lean `Address` from a [`blake3::Hash`].
  pub fn build_hash(hash: &blake3::Hash) -> Self {
    LeanIxAddress::new(LeanByteArray::from_bytes(hash.as_bytes()))
  }

  /// Construct a `LeanArray` of `Address` values.
  pub fn build_array(addrs: &[Address]) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(addrs.len());
    for (i, a) in addrs.iter().enumerate() {
      arr.set(i, Self::build(a));
    }
    arr
  }
}

impl<R: LeanRef> LeanIxAddress<R> {
  /// Decode a 32-byte Lean `Address` into a Rust [`Address`].
  pub fn decode(&self) -> Address {
    Address::from_slice(self.as_bytes()).expect("Lean Address must be 32 bytes")
  }
}

impl LeanIxAddress<LeanBorrowed<'_>> {
  /// Decode a `LeanArray` of `Address` values into a `Vec<Address>`.
  pub fn decode_array(arr: LeanArray<LeanBorrowed<'_>>) -> Vec<Address> {
    arr
      .iter()
      .map(|elem| LeanIxAddress::from_borrowed(elem.as_byte_array()).decode())
      .collect()
  }
}

impl LeanIxName<LeanOwned> {
  /// Construct a Lean `Ix.Name` (deduplicated via `cache`).
  pub fn build(cache: &mut LeanBuildCache, name: &Name) -> Self {
    let key = *name.get_hash();
    if let Some(existing) = cache.names.get(&key) {
      return existing.clone();
    }
    let built = match name.as_data() {
      NameData::Anonymous(h) => {
        let ctor = LeanIxName::alloc(0);
        ctor.set_obj(0, LeanIxAddress::build_hash(h));
        ctor
      },
      NameData::Str(parent, s, h) => {
        let p_obj = Self::build(cache, parent);
        let ctor = LeanIxName::alloc(1);
        ctor.set_obj(0, p_obj);
        ctor.set_obj(1, LeanString::new(s));
        ctor.set_obj(2, LeanIxAddress::build_hash(h));
        ctor
      },
      NameData::Num(parent, n, h) => {
        let p_obj = Self::build(cache, parent);
        let ctor = LeanIxName::alloc(2);
        ctor.set_obj(0, p_obj);
        ctor.set_obj(1, LeanNat::from_nat(n));
        ctor.set_obj(2, LeanIxAddress::build_hash(h));
        ctor
      },
    };
    cache.names.insert(key, built.clone());
    built
  }
}

impl<R: LeanRef> LeanIxName<R> {
  /// Decode a Lean `Ix.Name` into a Rust [`Name`].
  pub fn decode(&self) -> Name {
    match self.as_ctor().tag() {
      0 => Name::anon(),
      1 => {
        let parent = LeanIxName::new(self.get_obj(0).to_owned_ref()).decode();
        let s = self.get_obj(1).as_string().to_string();
        Name::str(parent, s)
      },
      2 => {
        let parent = LeanIxName::new(self.get_obj(0).to_owned_ref()).decode();
        let n = LeanNat::to_nat(&self.get_obj(1));
        Name::num(parent, n)
      },
      t => panic!("LeanIxName::decode: unexpected tag {t}"),
    }
  }
}

impl LeanIxBinderInfo<LeanOwned> {
  /// Encode [`BinderInfo`] as a Lean enum tag.
  pub fn to_u8(bi: &BinderInfo) -> u8 {
    match bi {
      BinderInfo::Default => 0,
      BinderInfo::Implicit => 1,
      BinderInfo::StrictImplicit => 2,
      BinderInfo::InstImplicit => 3,
    }
  }

  /// Decode [`BinderInfo`] from a Lean enum tag.
  pub fn from_u8(v: u8) -> BinderInfo {
    match v {
      0 => BinderInfo::Default,
      1 => BinderInfo::Implicit,
      2 => BinderInfo::StrictImplicit,
      3 => BinderInfo::InstImplicit,
      _ => panic!("Invalid BinderInfo tag: {v}"),
    }
  }
}

impl LeanIxReducibilityHints<LeanOwned> {
  /// Construct a Lean `Ix.ReducibilityHints`.
  pub fn build(hints: &ReducibilityHints) -> Self {
    match hints {
      ReducibilityHints::Opaque => Self::new(LeanOwned::box_usize(0)),
      ReducibilityHints::Abbrev => Self::new(LeanOwned::box_usize(1)),
      ReducibilityHints::Regular(h) => {
        let ctor = LeanIxReducibilityHints::alloc(2);
        ctor.set_num_32(0, *h);
        ctor
      },
    }
  }
}

impl<R: LeanRef> LeanIxReducibilityHints<R> {
  /// Decode a Lean `Ix.ReducibilityHints`.
  pub fn decode(&self) -> ReducibilityHints {
    if self.inner().is_scalar() {
      match (self.inner().as_raw() as usize) >> 1 {
        0 => ReducibilityHints::Opaque,
        1 => ReducibilityHints::Abbrev,
        t => panic!("Invalid scalar ReducibilityHints tag: {t}"),
      }
    } else {
      assert_eq!(self.as_ctor().tag(), 2);
      ReducibilityHints::Regular(self.get_num_32(0))
    }
  }
}
