use std::sync::OnceLock;

use tiny_keccak::{Hasher, Keccak};

use lean_ffi::object::{
  ExternalClass, LeanBorrowed, LeanByteArray, LeanExternal, LeanOwned,
};

static KECCAK_CLASS: OnceLock<ExternalClass> = OnceLock::new();

fn keccak_class() -> &'static ExternalClass {
  KECCAK_CLASS.get_or_init(ExternalClass::register_with_drop::<Keccak>)
}

/// `Keccak.Hasher.init : Unit → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_init(
  _unit: LeanOwned,
) -> LeanExternal<Keccak, LeanOwned> {
  LeanExternal::alloc(keccak_class(), Keccak::v256())
}

/// `Keccak.Hasher.update : (hasher: Hasher) → (input: @& ByteArray) → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_update(
  hasher: LeanExternal<Keccak, LeanOwned>,
  input: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanExternal<Keccak, LeanOwned> {
  let mut new_hasher = hasher.get().clone();
  new_hasher.update(input.as_bytes());
  LeanExternal::alloc(keccak_class(), new_hasher)
}

/// `Keccak.Hasher.finalize : (hasher: Hasher) → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_finalize(
  hasher: LeanExternal<Keccak, LeanOwned>,
) -> LeanByteArray<LeanOwned> {
  let mut data = [0u8; 32];
  hasher.get().clone().finalize(&mut data);
  LeanByteArray::from_bytes(&data)
}
