//! Minimal Lean runtime support loaded while elaborating `IxTcVerify`.
//!
//! Lean's native evaluator calls the boxed entry points generated for opaque
//! `@[extern]` declarations. Normal executables receive those wrappers and the
//! raw Rust FFI symbols at final link time, which is too late for
//! `native_decide`. This crate exports both layers from one loadable artifact.

use std::sync::LazyLock;

use lean_ffi::object::{
  ExternalClass, LeanBorrowed, LeanByteArray, LeanExternal, LeanOwned, LeanRef,
};

static HASHER_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<blake3::Hasher>);

fn blake3_init() -> LeanExternal<blake3::Hasher, LeanOwned> {
  LeanExternal::alloc(&HASHER_CLASS, blake3::Hasher::new())
}

fn blake3_init_keyed(key: &[u8]) -> LeanExternal<blake3::Hasher, LeanOwned> {
  let key: &[u8; 32] = key.try_into().expect("key must be 32 bytes");
  LeanExternal::alloc(&HASHER_CLASS, blake3::Hasher::new_keyed(key))
}

fn blake3_init_derive_key(
  context: &[u8],
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  let context =
    std::str::from_utf8(context).expect("context must be valid UTF-8");
  LeanExternal::alloc(&HASHER_CLASS, blake3::Hasher::new_derive_key(context))
}

fn blake3_update(
  mut hasher: LeanExternal<blake3::Hasher, LeanOwned>,
  input: &[u8],
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  if let Some(inner) = hasher.get_mut() {
    inner.update(input);
    hasher
  } else {
    let mut inner = hasher.get().clone();
    inner.update(input);
    LeanExternal::alloc(&HASHER_CLASS, inner)
  }
}

fn blake3_finalize(
  hasher: &LeanExternal<blake3::Hasher, LeanOwned>,
  length: usize,
) -> LeanByteArray<LeanOwned> {
  let mut output = vec![0; length];
  hasher.get().finalize_xof().fill(&mut output);
  LeanByteArray::from_bytes(&output)
}

#[unsafe(no_mangle)]
pub extern "C" fn rs_blake3_init() -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_init()
}

#[unsafe(no_mangle)]
pub extern "C" fn rs_blake3_init_keyed(
  key: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_init_keyed(key.as_bytes())
}

#[unsafe(no_mangle)]
pub extern "C" fn rs_blake3_init_derive_key(
  context: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_init_derive_key(context.as_bytes())
}

#[unsafe(no_mangle)]
pub extern "C" fn rs_blake3_hasher_update(
  hasher: LeanExternal<blake3::Hasher, LeanOwned>,
  input: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_update(hasher, input.as_bytes())
}

#[unsafe(no_mangle)]
pub extern "C" fn rs_blake3_hasher_finalize(
  hasher: LeanExternal<blake3::Hasher, LeanOwned>,
  length: usize,
) -> LeanByteArray<LeanOwned> {
  blake3_finalize(&hasher, length)
}

#[unsafe(export_name = "lp_Blake3_Blake3_Rust_hasherInit___boxed")]
pub extern "C" fn boxed_blake3_init(
  _unit: LeanOwned,
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_init()
}

#[unsafe(export_name = "lp_Blake3_Blake3_Rust_hasherInitKeyed___boxed")]
pub extern "C" fn boxed_blake3_init_keyed(
  key: LeanByteArray<LeanOwned>,
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_init_keyed(key.as_bytes())
}

#[unsafe(export_name = "lp_Blake3_Blake3_Rust_hasherInitDeriveKey___boxed")]
pub extern "C" fn boxed_blake3_init_derive_key(
  context: LeanByteArray<LeanOwned>,
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_init_derive_key(context.as_bytes())
}

#[unsafe(export_name = "lp_Blake3_Blake3_Rust_hasherUpdate___boxed")]
pub extern "C" fn boxed_blake3_update(
  hasher: LeanExternal<blake3::Hasher, LeanOwned>,
  input: LeanByteArray<LeanOwned>,
) -> LeanExternal<blake3::Hasher, LeanOwned> {
  blake3_update(hasher, input.as_bytes())
}

#[unsafe(export_name = "lp_Blake3_Blake3_Rust_hasherFinalize___boxed")]
pub extern "C" fn boxed_blake3_finalize(
  hasher: LeanExternal<blake3::Hasher, LeanOwned>,
  length: LeanOwned,
) -> LeanByteArray<LeanOwned> {
  blake3_finalize(&hasher, length.unbox_usize_obj())
}

#[unsafe(no_mangle)]
pub extern "C" fn c_u16_to_le_bytes(value: u16) -> LeanByteArray<LeanOwned> {
  LeanByteArray::from_bytes(&value.to_le_bytes())
}

#[unsafe(no_mangle)]
pub extern "C" fn c_u32_to_le_bytes(value: u32) -> LeanByteArray<LeanOwned> {
  LeanByteArray::from_bytes(&value.to_le_bytes())
}

#[unsafe(no_mangle)]
pub extern "C" fn c_u64_to_le_bytes(value: u64) -> LeanByteArray<LeanOwned> {
  LeanByteArray::from_bytes(&value.to_le_bytes())
}

#[unsafe(no_mangle)]
pub extern "C" fn c_usize_to_le_bytes(
  value: usize,
) -> LeanByteArray<LeanOwned> {
  LeanByteArray::from_bytes(&value.to_le_bytes())
}

#[unsafe(export_name = "lp_ix_UInt16_toLEBytes___boxed")]
pub extern "C" fn boxed_u16_to_le_bytes(
  value: LeanOwned,
) -> LeanByteArray<LeanOwned> {
  let value =
    u16::try_from(value.unbox_usize()).expect("UInt16 value must fit in u16");
  c_u16_to_le_bytes(value)
}

#[unsafe(export_name = "lp_ix_UInt32_toLEBytes___boxed")]
pub extern "C" fn boxed_u32_to_le_bytes(
  value: LeanOwned,
) -> LeanByteArray<LeanOwned> {
  c_u32_to_le_bytes(value.unbox_u32())
}

#[unsafe(export_name = "lp_ix_UInt64_toLEBytes___boxed")]
pub extern "C" fn boxed_u64_to_le_bytes(
  value: LeanOwned,
) -> LeanByteArray<LeanOwned> {
  c_u64_to_le_bytes(value.unbox_u64())
}

#[unsafe(export_name = "lp_ix_USize_toLEBytes___boxed")]
pub extern "C" fn boxed_usize_to_le_bytes(
  value: LeanOwned,
) -> LeanByteArray<LeanOwned> {
  c_usize_to_le_bytes(value.unbox_usize_obj())
}
