use lean_ffi::object::{LeanIOResult, LeanOwned};

#[cfg(feature = "cuda")]
pub(crate) fn visible_gpu_count() -> Result<usize, String> {
  unsafe extern "C" {
    fn cudaGetDeviceCount(count: *mut i32) -> i32;
    fn cudaGetErrorString(error: i32) -> *const std::ffi::c_char;
  }
  let mut count = 0;
  // CUDA applies CUDA_VISIBLE_DEVICES, including logical device reordering.
  let status = unsafe { cudaGetDeviceCount(&raw mut count) };
  if status == 100 {
    return Ok(0);
  }
  if status != 0 {
    let message =
      unsafe { std::ffi::CStr::from_ptr(cudaGetErrorString(status)) };
    return Err(format!(
      "CUDA device discovery failed: {}",
      message.to_string_lossy()
    ));
  }
  usize::try_from(count)
    .map_err(|_| "CUDA returned a negative device count".into())
}

#[cfg(not(feature = "cuda"))]
pub(crate) fn visible_gpu_count() -> Result<usize, String> {
  Ok(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn rs_aiur_visible_gpu_count() -> LeanIOResult<LeanOwned> {
  match visible_gpu_count() {
    Ok(count) => LeanIOResult::ok(LeanOwned::box_usize(count)),
    Err(error) => LeanIOResult::error_string(&error),
  }
}
