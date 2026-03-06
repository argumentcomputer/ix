use lean_ffi::object::{
  LeanArray, LeanByteArray, LeanCtor, LeanExcept, LeanString,
};

use crate::iroh::common::{GetRequest, PutRequest, Request, Response};
use crate::iroh::{client, server};

lean_ffi::lean_domain_type! {
  /// Lean `Iroh.Connect.PutResponse` object.
  LeanPutResponse;
  /// Lean `Iroh.Connect.GetResponse` object.
  LeanGetResponse;
}

impl LeanPutResponse {
  /// Build from `message` and `hash` strings.
  ///
  /// ```lean
  /// structure PutResponse where
  ///   message : String
  ///   hash : String
  /// ```
  pub fn mk(message: &str, hash: &str) -> Self {
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, LeanString::new(message));
    ctor.set(1, LeanString::new(hash));
    Self::new(*ctor)
  }
}

impl LeanGetResponse {
  /// Build from `message`, `hash`, and raw `bytes`.
  ///
  /// ```lean
  /// structure GetResponse where
  ///   message : String
  ///   hash : String
  ///   bytes : ByteArray
  /// ```
  pub fn mk(message: &str, hash: &str, bytes: &[u8]) -> Self {
    let ctor = LeanCtor::alloc(0, 3, 0);
    ctor.set(0, LeanString::new(message));
    ctor.set(1, LeanString::new(hash));
    ctor.set(2, LeanByteArray::from_bytes(bytes));
    Self::new(*ctor)
  }
}

/// `Iroh.Connect.putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_put(
  node_id: LeanString,
  addrs: LeanArray,
  relay_url: LeanString,
  input: LeanString,
) -> LeanExcept {
  let node_id = node_id.to_string();
  let addrs: Vec<String> = addrs.map(|x| x.as_string().to_string());
  let relay_url = relay_url.to_string();
  let input_str = input.to_string();

  let request =
    Request::Put(PutRequest { bytes: input_str.as_bytes().to_vec() });
  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  match rt.block_on(client::connect(&node_id, &addrs, &relay_url, request)) {
    Ok(response) => match response {
      Response::Put(put_response) => LeanExcept::ok(LeanPutResponse::mk(
        &put_response.message,
        &put_response.hash,
      )),
      _ => LeanExcept::error_string("error: incorrect server response"),
    },
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// `Iroh.Connect.getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_get(
  node_id: LeanString,
  addrs: LeanArray,
  relay_url: LeanString,
  hash: LeanString,
) -> LeanExcept {
  let node_id = node_id.to_string();
  let addrs: Vec<String> = addrs.map(|x| x.as_string().to_string());
  let relay_url = relay_url.to_string();
  let hash_str = hash.to_string();

  let request = Request::Get(GetRequest { hash: hash_str.clone() });

  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  match rt.block_on(client::connect(&node_id, &addrs, &relay_url, request)) {
    Ok(response) => match response {
      Response::Get(get_response) => LeanExcept::ok(LeanGetResponse::mk(
        &get_response.message,
        &get_response.hash,
        &get_response.bytes,
      )),
      _ => LeanExcept::error_string("error: incorrect server response"),
    },
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// `Iroh.Serve.serve' : Unit → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_serve() -> LeanExcept {
  let rt =
    tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");

  match rt.block_on(server::serve()) {
    Ok(()) => LeanExcept::ok(0),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}
