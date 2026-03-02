use crate::lean::obj::LeanExcept;

/// `Iroh.Serve.serve' : Unit → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_serve() -> LeanExcept {
  LeanExcept::error_string(
    "Iroh functions not supported when the Rust `net` feature is disabled \
     or on MacOS aarch64-darwin",
  )
}
