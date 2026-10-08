//! CLI bridge for catalog-bound incremental proving.

use lean_ffi::object::{LeanBorrowed, LeanIOResult, LeanOwned, LeanString};

#[unsafe(no_mangle)]
pub extern "C" fn rs_catalog_prove(
  request: LeanString<LeanBorrowed<'_>>,
) -> LeanIOResult<LeanOwned> {
  let result = (|| {
    let value = serde_json::from_str(request.as_str())
      .map_err(|e| format!("invalid catalog proving request: {e}"))?;
    let mut options = ix_kernel::catalog_prove::Options::from_json(&value)?;
    if !options.plan_only && !options.verify_only {
      let visible = crate::aiur::device::visible_gpu_count()?;
      if options.lanes > visible {
        return Err(format!(
          "requested {} GPU lanes, but only {visible} devices are visible",
          options.lanes
        ));
      }
      if options.lanes == 0 {
        options.lanes = visible;
      }
      if options.lanes > 0 {
        options.trace_shards = true;
      }
    }
    ix_kernel::catalog_prove::run_catalog(&options)
  })();
  match result {
    Ok(value) => LeanIOResult::ok(LeanString::new(&value.to_string())),
    Err(error) => LeanIOResult::error_string(&error),
  }
}
