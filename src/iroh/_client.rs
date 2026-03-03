use crate::lean::object::{LeanExcept, LeanObject};

const ERR_MSG: &str = "Iroh functions not supported when the Rust `net` feature is disabled \
   or on MacOS aarch64-darwin";

/// `Iroh.Connect.putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_put(
  _node_id: LeanObject,
  _addrs: LeanObject,
  _relay_url: LeanObject,
  _input: LeanObject,
) -> LeanExcept {
  LeanExcept::error_string(ERR_MSG)
}

/// `Iroh.Connect.getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_get(
  _node_id: LeanObject,
  _addrs: LeanObject,
  _relay_url: LeanObject,
  _hash: LeanObject,
) -> LeanExcept {
  LeanExcept::error_string(ERR_MSG)
}
