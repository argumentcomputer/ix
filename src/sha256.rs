use sha2::{Digest, Sha256};

use lean_sys::object::LeanByteArray;

#[unsafe(no_mangle)]
extern "C" fn rs_sha256(bytes: LeanByteArray) -> LeanByteArray {
  let mut hasher = Sha256::new();
  hasher.update(bytes.as_bytes());
  let digest = hasher.finalize();
  LeanByteArray::from_bytes(digest.as_slice())
}
