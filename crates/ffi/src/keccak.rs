use std::sync::LazyLock;

use tiny_keccak::{Hasher, Keccak};

use lean_ffi::object::{
  ExternalClass, LeanBorrowed, LeanByteArray, LeanExternal, LeanOwned,
};

static KECCAK_CLASS: LazyLock<ExternalClass> =
  LazyLock::new(ExternalClass::register_with_drop::<Keccak>);

/// `Keccak.Hasher.init : Unit → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_init(
  _unit: LeanOwned,
) -> LeanExternal<Keccak, LeanOwned> {
  LeanExternal::alloc(&KECCAK_CLASS, Keccak::v256())
}

/// `Keccak.Hasher.update : (hasher: Hasher) → (input: @& ByteArray) → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_update(
  mut hasher: LeanExternal<Keccak, LeanOwned>,
  input: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<Keccak, LeanOwned> {
  if let Some(h) = hasher.get_mut() {
    h.update(input.as_bytes());
    hasher
  } else {
    let mut new_hasher = hasher.get().clone();
    new_hasher.update(input.as_bytes());
    LeanExternal::alloc(&KECCAK_CLASS, new_hasher)
  }
}

/// `Keccak.Hasher.finalize : (hasher: Hasher) → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_finalize(
  mut hasher: LeanExternal<Keccak, LeanOwned>,
) -> LeanByteArray<LeanOwned> {
  let mut data = [0u8; 32];
  if let Some(h) = hasher.get_mut() {
    std::mem::replace(h, Keccak::v256()).finalize(&mut data);
  } else {
    hasher.get().clone().finalize(&mut data);
  }
  LeanByteArray::from_bytes(&data)
}
