//! Exact and canonical sharing FFI (test hooks for the Lean/Rust
//! differential, `Tests/Ix/SharingExactFFI.lean`).

use ixon::sharing_exact::ExactSharingLimits;
use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanExcept, LeanOwned};

/// The limits of every hook: the defaults (the compiler's) in the checked
/// mode (`full_check`), so that the differential also builds and checks
/// every candidate of the tiered construction. The checked mode changes no
/// output and no limit outcome; it fails only on an internal discrepancy.
fn parity_limits() -> ExactSharingLimits {
  ExactSharingLimits { full_check: true, ..ExactSharingLimits::default() }
}

/// FFI: exact-minimum sharing of one serialized Constant (the width-state
/// search, a test oracle; not the compiler path).
///
/// Lean signature:
/// `@[extern "rs_exact_sharing_normalize"]
///  opaque exactSharingNormalize : @& ByteArray → Except String ByteArray`
///
/// Decodes exactly one Constant (trailing bytes are rejected), expands and
/// validates its sharing table under the backward-reference rule, and
/// returns the serialized exact-minimum encoding computed with the default
/// limits ([`parity_limits`]). Error strings start with `decode:`,
/// `malformed sharing:`, `format bound:`, `resource exhausted:` or
/// `internal error:`; no error carries a partial encoding.
#[unsafe(no_mangle)]
extern "C" fn rs_exact_sharing_normalize(
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ixon::sharing_exact::normalize_constant_bytes;
  match normalize_constant_bytes(bytes_obj.as_bytes(), &parity_limits()) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// FFI: uniform-width exact sharing of one serialized Constant (phase 1 of
/// the canonical construction, at a given width).
///
/// Lean signature:
/// `@[extern "rs_uniform_sharing_normalize"]
///  opaque uniformSharingNormalize : UInt64 → @& ByteArray → Except String ByteArray`
///
/// Every Share is priced `w` bytes (the uniform-width model of
/// `Ix.Sharing.Exact.Uniform`); the output uses real table indices. Uses the
/// default limits ([`parity_limits`]); `w = 0` is a `format bound:` error.
#[unsafe(no_mangle)]
extern "C" fn rs_uniform_sharing_normalize(
  w: u64,
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ixon::sharing_exact::normalize_constant_bytes_uniform;
  match normalize_constant_bytes_uniform(
    w,
    bytes_obj.as_bytes(),
    &parity_limits(),
  ) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// FFI: tiered canonical sharing of one serialized Constant.
///
/// Lean signature:
/// `@[extern "rs_tiered_sharing_normalize"]
///  opaque tieredSharingNormalize : @& ByteArray → Except String ByteArray`
///
/// Expands the Constant's table and re-shares it with the canonical tiered
/// construction under the TagN layout and the default limits in the checked
/// mode ([`parity_limits`]); the output is serialized with the wire (TagN)
/// Share code.
#[unsafe(no_mangle)]
extern "C" fn rs_tiered_sharing_normalize(
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ixon::sharing_exact::{ShareLayout, normalize_constant_bytes_tiered};
  match normalize_constant_bytes_tiered(
    ShareLayout::TagN,
    bytes_obj.as_bytes(),
    &parity_limits(),
  ) {
    Ok(bytes) => LeanExcept::ok(LeanByteArray::from_bytes(&bytes)),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// FFI: build one block Constant through the compiler's sharing functions.
///
/// Lean signature:
/// `@[extern "rs_compiler_sharing_build"]
///  opaque compilerSharingBuild : @& ByteArray → Except String ByteArray`
///
/// Decodes exactly one Constant whose roots carry no sharing table, and
/// rebuilds it with `ix_compile::compile::apply_sharing_to_*_with_limits`
/// (the explicit-limits forms of the functions every compile, aux-gen,
/// kernel-egress and decompile-recompile path calls) under the default
/// limits in the checked mode ([`parity_limits`]; the compiler itself runs
/// the default mode, which writes the same bytes). Projections are returned
/// unchanged. Errors are the compile error's text, prefixed `decode:` for
/// input errors.
#[unsafe(no_mangle)]
extern "C" fn rs_compiler_sharing_build(
  bytes_obj: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  use ix_compile::compile::{
    apply_sharing_to_axiom_with_limits,
    apply_sharing_to_definition_with_limits,
    apply_sharing_to_mutual_block_with_limits,
    apply_sharing_to_quotient_with_limits,
    apply_sharing_to_recursor_with_limits,
  };
  use ixon::constant::{Constant, ConstantInfo};
  let limits = parity_limits();
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
      apply_sharing_to_definition_with_limits(&limits, d, refs, univs)
    },
    ConstantInfo::Recr(r) => {
      apply_sharing_to_recursor_with_limits(&limits, r, refs, univs)
    },
    ConstantInfo::Axio(a) => {
      apply_sharing_to_axiom_with_limits(&limits, a, refs, univs)
    },
    ConstantInfo::Quot(q) => {
      apply_sharing_to_quotient_with_limits(&limits, q, refs, univs)
    },
    ConstantInfo::Muts(ms) => {
      apply_sharing_to_mutual_block_with_limits(&limits, ms, refs, univs)
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
