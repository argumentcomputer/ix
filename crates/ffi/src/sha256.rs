use sha2::{Digest, Sha256};

use lean_ffi::object::{LeanBorrowed, LeanByteArray, LeanOwned};

#[unsafe(no_mangle)]
extern "C" fn rs_sha256(
  bytes: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanByteArray<LeanOwned> {
  let mut hasher = Sha256::new();
  hasher.update(bytes.as_bytes());
  let digest = hasher.finalize();
  LeanByteArray::from_bytes(digest.as_slice())
}
