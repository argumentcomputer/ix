use lean_ffi::object::{LeanArray, LeanExcept, LeanString};

const ERR_MSG: &str = "Iroh functions not supported when the Rust `net` feature is disabled \
   or on MacOS aarch64-darwin";

/// `Iroh.Connect.putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_put(
  _node_id: LeanString,
  _addrs: LeanArray,
  _relay_url: LeanString,
  _input: LeanString,
) -> LeanExcept {
  LeanExcept::error_string(ERR_MSG)
}

/// `Iroh.Connect.getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_get(
  _node_id: LeanString,
  _addrs: LeanArray,
  _relay_url: LeanString,
  _hash: LeanString,
) -> LeanExcept {
  LeanExcept::error_string(ERR_MSG)
}

/// `Iroh.Serve.serve' : Unit → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_serve() -> LeanExcept {
  LeanExcept::error_string(
    "Iroh functions not supported when the Rust `net` feature is disabled \
     or on MacOS aarch64-darwin",
  )
}
