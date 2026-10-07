//! CLI bridge for catalog-bound incremental proving.

use lean_ffi::object::{LeanBorrowed, LeanIOResult, LeanOwned, LeanString};

#[unsafe(no_mangle)]
pub extern "C" fn rs_catalog_prove(
  request: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = (|| {
    let value = serde_json::from_str(request.as_str())
      .map_err(|e| format!("invalid catalog proving request: {e}"))?;
    let options = ix_kernel::catalog_prove::Options::from_json(&value)?;
    ix_kernel::catalog_prove::run_catalog(&options)
  })();
  match result {
    Ok(value) => LeanIOResult::ok(LeanString::new(&value.to_string())),
    Err(error) => LeanIOResult::error_string(&error),
  }
}
