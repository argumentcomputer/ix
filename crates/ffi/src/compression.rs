//! Main CLI bridge; compression is linked into the ix executable.
use ix_proof_compression::pipeline;
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanIOResult, LeanOwned, LeanString,
};

#[unsafe(no_mangle)]
extern "C" fn rs_compression_worker(
  json: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::worker(&json.to_string()) {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_run(
  vk: LeanByteArray<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
  dir: LeanString<LeanBorrowed<'_>>,
  registry: LeanString<LeanBorrowed<'_>>,
  resume: bool,
  resident: bool,
  log_height: u32,
) -> LeanIOResult<LeanOwned> {
  let result = (|| -> pipeline::Result<Vec<u8>> {
    let dir = dir.to_string();
    let dir = std::path::Path::new(&dir);
    let bytes = pipeline::compress(
      vk.as_bytes(),
      proof.as_bytes(),
      claim.as_bytes(),
      dir,
      resume,
      resident,
      log_height,
    )?;
    pipeline::verify(&dir.join("final-kzg"), &bytes, claim.as_bytes())?;
    pipeline::registry::register(
      &dir.join("final-kzg/verifier.bin"),
      std::path::Path::new(&registry.to_string()),
      None,
    )?;
    Ok(bytes)
  })();
  match result {
    Ok(bytes) => LeanIOResult::ok(LeanByteArray::from_bytes(bytes.as_slice())),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_verify(
  dir: LeanString<LeanBorrowed<'_>>,
  proof: LeanByteArray<LeanBorrowed<'_>>,
  claim: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::registry::verify(
    std::path::Path::new(&dir.to_string()),
    proof.as_bytes(),
    claim.as_bytes(),
  ) {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_check_claim(
  claim: LeanByteArray<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::check_claim(claim.as_bytes()) {
    Ok(()) => LeanIOResult::ok(LeanOwned::box_usize(0)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_compression_import_verifier(
  file: LeanString<LeanBorrowed<'_>>,
  digest: LeanString<LeanBorrowed<'_>>,
  registry: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  match pipeline::registry::register(
    std::path::Path::new(&file.to_string()),
    std::path::Path::new(&registry.to_string()),
    Some(&digest.to_string()),
  ) {
    Ok(id) => LeanIOResult::ok(LeanString::new(&id)),
    Err(e) => LeanIOResult::error_string(&e.to_string()),
  }
}
