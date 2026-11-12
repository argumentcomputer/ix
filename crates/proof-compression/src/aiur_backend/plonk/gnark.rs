//! Compilation through the pinned gnark sparse PLONK backend.

use super::Schema;
pub use crate::pipeline::gnark::CircuitInfo;
use std::{ffi::c_void, path::Path};

#[allow(
  non_camel_case_types,
  non_snake_case,
  non_upper_case_globals,
  dead_code,
  unreachable_pub
)]
mod raw {
  include!(concat!(env!("OUT_DIR"), "/gnark_bindings.rs"));
}

struct Response(raw::ix_gnark_result);
impl Drop for Response {
  fn drop(&mut self) {
    // All buffers are owned by the archive's C allocator.
    unsafe {
      raw::ix_gnark_free(self.0.data.cast::<c_void>());
      raw::ix_gnark_free(self.0.solidity.cast::<c_void>());
      raw::ix_gnark_free(self.0.error.cast::<c_void>());
    }
  }
}

/// Compile the trusted schema and persist its constraint system. The exact
/// PLONK domain is checked against the retained Ignition limit before writing.
pub fn compile(
  schema: &Schema,
  output: &Path,
) -> Result<CircuitInfo, Box<dyn std::error::Error>> {
  let schema = serde_json::to_vec(schema)?;
  if schema.len() > 16 << 20 {
    return Err("Aiur PLONK schema exceeds the 16 MiB bridge limit".into());
  }
  let path = output.to_str().ok_or("gnark paths must be UTF-8")?.as_bytes();
  let view =
    |data: &[u8]| raw::ix_gnark_view { data: data.as_ptr(), len: data.len() };
  // The synchronous archive call retains no Rust buffers.
  let response =
    Response(unsafe { raw::ix_gnark_aiur_compile(view(&schema), view(path)) });
  if !response.0.error.is_null() {
    // The response owns this bounded buffer until it is dropped.
    let message = unsafe {
      std::slice::from_raw_parts(response.0.error, response.0.error_len)
    };
    return Err(String::from_utf8_lossy(message).into_owned().into());
  }
  if response.0.data.is_null() || response.0.len == 0 {
    return Err("gnark returned empty compile metadata".into());
  }
  // Metadata remains alive throughout deserialization.
  let bytes =
    unsafe { std::slice::from_raw_parts(response.0.data, response.0.len) };
  Ok(serde_json::from_slice(bytes)?)
}
