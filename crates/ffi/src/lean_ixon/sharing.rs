//! Exact and canonical sharing FFI (test hooks).

use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanExcept, LeanOwned};

/// FFI: canonical exact-minimum sharing of one serialized Constant.
///
/// Lean signature:
/// `@[extern "rs_exact_sharing_normalize"]
///  opaque exactSharingNormalize : @& ByteArray → Except String ByteArray`
///
/// Decodes exactly one Constant (trailing bytes are rejected), expands and
/// validates its sharing table under the backward-reference rule, and
/// returns the serialized canonical encoding computed with
/// `ExactSharingLimits::default()`. Error strings start with `decode:`,
/// `malformed sharing:`, `format bound:`, `resource exhausted:` or
/// `internal error:`; no error carries a partial encoding.
#[unsafe(no_mangle)]
extern "C" fn rs_exact_sharing_normalize(
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ixon::sharing_exact::{ExactSharingLimits, normalize_constant_bytes};
  match normalize_constant_bytes(
    bytes_obj.as_bytes(),
    &ExactSharingLimits::default(),
  ) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// FFI: uniform-width exact sharing of one serialized Constant.
///
/// Lean signature:
/// `@[extern "rs_uniform_sharing_normalize"]
///  opaque uniformSharingNormalize : UInt64 → @& ByteArray → Except String ByteArray`
///
/// Every Share is priced `w` bytes (the uniform-width model of
/// `Ix.Sharing.Exact.Uniform`); the output uses real table indices. Uses
/// `ExactSharingLimits::default()`; `w = 0` is a `format bound:` error.
#[unsafe(no_mangle)]
extern "C" fn rs_uniform_sharing_normalize(
  w: u64,
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ixon::sharing_exact::{
    ExactSharingLimits, normalize_constant_bytes_uniform,
  };
  match normalize_constant_bytes_uniform(
    w,
    bytes_obj.as_bytes(),
    &ExactSharingLimits::default(),
  ) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// FFI: tiered canonical sharing of one serialized Constant.
///
/// Lean signature:
/// `@[extern "rs_tiered_sharing_normalize"]
///  opaque tieredSharingNormalize : UInt8 → @& ByteArray → Except String ByteArray`
///
/// `layout` selects the Share layout: 0 = Tag4, 1 = TagN (any other value
/// is a `format bound:` error). Uses `ExactSharingLimits::default()`; the
/// output is serialized with Tag4 Shares in both layouts.
#[unsafe(no_mangle)]
extern "C" fn rs_tiered_sharing_normalize(
  layout: u8,
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ixon::sharing_exact::{
    ExactSharingLimits, ShareLayout, normalize_constant_bytes_tiered,
  };
  let Some(layout) = ShareLayout::from_code(layout) else {
    return LeanExcept::error_string(&format!(
      "format bound: unknown Share layout code {layout}"
    ));
  };
  match normalize_constant_bytes_tiered(
    layout,
    bytes_obj.as_bytes(),
    &ExactSharingLimits::default(),
  ) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// FFI: build one block Constant through the compiler's sharing route.
///
/// Lean signature:
/// `@[extern "rs_compiler_sharing_build"]
///  opaque compilerSharingBuild : @& ByteArray → Except String ByteArray`
///
/// Decodes exactly one Constant whose roots carry no sharing table, and
/// rebuilds it with `ix_compile::compile::apply_sharing_to_*_via` (the
/// functions every compile, aux-gen, kernel-egress and decompile-recompile
/// path calls; the canonical construction) under
/// `ExactSharingLimits::default()`. Projections are returned unchanged.
/// Errors are the compile error's text, prefixed `decode:` for input errors.
#[unsafe(no_mangle)]
extern "C" fn rs_compiler_sharing_build(
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ix_compile::compile::{
    apply_sharing_to_axiom_via, apply_sharing_to_definition_via,
    apply_sharing_to_mutual_block_via, apply_sharing_to_quotient_via,
    apply_sharing_to_recursor_via,
  };
  use ixon::constant::{Constant, ConstantInfo};
  use ixon::sharing_exact::ExactSharingLimits;
  let limits = ExactSharingLimits::default();
  let mut input = bytes_obj.as_bytes();
  let c = match Constant::get(&mut input) {
    Ok(c) => c,
    Err(e) => return LeanExcept::error_string(&format!("decode: {e}")),
  };
  if !input.is_empty() || !c.sharing.is_empty() {
    return LeanExcept::error_string(
      "decode: expected one Constant with an empty sharing table",
    );
  }
  let (refs, univs) = (c.refs.clone(), c.univs.clone());
  let built = match c.info.clone() {
    ConstantInfo::Defn(d) => {
      apply_sharing_to_definition_via(&limits, d, refs, univs)
        .map(|r| r.constant)
    },
    ConstantInfo::Recr(r) => {
      apply_sharing_to_recursor_via(&limits, r, refs, univs).map(|r| r.constant)
    },
    ConstantInfo::Axio(a) => {
      apply_sharing_to_axiom_via(&limits, a, refs, univs).map(|r| r.constant)
    },
    ConstantInfo::Quot(q) => {
      apply_sharing_to_quotient_via(&limits, q, refs, univs).map(|r| r.constant)
    },
    ConstantInfo::Muts(ms) => {
      apply_sharing_to_mutual_block_via(&limits, ms, refs, univs)
        .map(|r| r.constant)
    },
    _ => Ok(c),
  };
  match built {
    Ok(out) => {
      let mut buf = Vec::new();
      out.put(&mut buf);
      LeanExcept::ok(LeanByteArray::from_bytes(&buf))
    },
    Err(e) => LeanExcept::error_string(&e.to_string()),
  }
}
