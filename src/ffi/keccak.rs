use std::sync::OnceLock;

use tiny_keccak::{Hasher, Keccak};

use lean_sys::object::{
  ExternalClass, LeanByteArray, LeanExternal, LeanObject,
};

static KECCAK_CLASS: OnceLock<ExternalClass> = OnceLock::new();

fn keccak_class() -> &'static ExternalClass {
  KECCAK_CLASS.get_or_init(ExternalClass::register_with_drop::<Keccak>)
}

/// `Keccak.Hasher.init : Unit → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_init(
  _unit: LeanObject,
) -> LeanExternal<Keccak> {
  LeanExternal::alloc(keccak_class(), Keccak::v256())
}

/// `Keccak.Hasher.update : (hasher: Hasher) → (input: @& ByteArray) → Hasher`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_update(
  hasher: LeanExternal<Keccak>,
  input: LeanByteArray,
) -> LeanExternal<Keccak> {
  let mut new_hasher = hasher.get().clone();
  new_hasher.update(input.as_bytes());
  LeanExternal::alloc(keccak_class(), new_hasher)
}

/// `Keccak.Hasher.finalize : (hasher: Hasher) → ByteArray`
#[unsafe(no_mangle)]
extern "C" fn rs_keccak256_hasher_finalize(
  hasher: LeanExternal<Keccak>,
) -> LeanByteArray {
  let mut data = [0u8; 32];
  hasher.get().clone().finalize(&mut data);
  LeanByteArray::from_bytes(&data)
}
