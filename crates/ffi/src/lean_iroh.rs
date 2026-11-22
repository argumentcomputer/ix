use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanByteArray, LeanExcept, LeanOwned, LeanString,
};

use crate::iroh::common::{GetRequest, PutRequest, Request, Response};
use crate::iroh::{client, server};

use crate::lean::{LeanGetResponse, LeanPutResponse};

impl LeanPutResponse<LeanOwned> {
  /// Build from `message` and `hash` strings.
  ///
  /// ```lean
  /// structure PutResponse where
  ///   message : String
  ///   hash : String
  /// ```
  pub fn mk(message: &str, hash: &str) -> Self {
    let ctor = LeanPutResponse::alloc(0);
    ctor.set_obj(0, LeanString::new(message));
    ctor.set_obj(1, LeanString::new(hash));
    ctor
  }
}

impl LeanGetResponse<LeanOwned> {
  /// Build from `message`, `hash`, and raw `bytes`.
  ///
  /// ```lean
  /// structure GetResponse where
  ///   message : String
  ///   hash : String
  ///   bytes : ByteArray
  /// ```
  pub fn mk(message: &str, hash: &str, bytes: &[u8]) -> Self {
    let ctor = LeanGetResponse::alloc(0);
    ctor.set_obj(0, LeanString::new(message));
    ctor.set_obj(1, LeanString::new(hash));
    ctor.set_obj(2, LeanByteArray::from_bytes(bytes));
    ctor
  }
}

/// `Iroh.Connect.putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_put(
  node_id: LeanString<LeanBorrowed<'_>>,
  addrs: LeanArray<LeanBorrowed<'_>>,
  relay_url: LeanString<LeanBorrowed<'_>>,
  input: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let node_id = node_id.to_string();
  let addrs: Vec<String> = addrs.map(|x| x.as_string().to_string());
  let relay_url = relay_url.to_string();
  let input_str = input.to_string();

  let request =
    Request::Put(PutRequest { bytes: input_str.as_bytes().to_vec() });
  let rt = match tokio::runtime::Runtime::new() {
    Ok(rt) => rt,
    Err(err) => {
      return LeanExcept::error_string(&format!(
        "failed to create Tokio runtime: {err}"
      ));
    },
  };

  match rt.block_on(client::connect(&node_id, &addrs, &relay_url, request)) {
    Ok(response) => match response {
      Response::Put(put_response) => {
        if put_response.is_err {
          LeanExcept::error_string(&put_response.message)
        } else {
          LeanExcept::ok(LeanPutResponse::mk(
            &put_response.message,
            &put_response.hash,
          ))
        }
      },
      _ => LeanExcept::error_string("error: incorrect server response"),
    },
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// `Iroh.Connect.getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_get(
  node_id: LeanString<LeanBorrowed<'_>>,
  addrs: LeanArray<LeanBorrowed<'_>>,
  relay_url: LeanString<LeanBorrowed<'_>>,
  hash: LeanString<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let node_id = node_id.to_string();
  let addrs: Vec<String> = addrs.map(|x| x.as_string().to_string());
  let relay_url = relay_url.to_string();
  let hash_str = hash.to_string();

  let request = Request::Get(GetRequest { hash: hash_str.clone() });

  let rt = match tokio::runtime::Runtime::new() {
    Ok(rt) => rt,
    Err(err) => {
      return LeanExcept::error_string(&format!(
        "failed to create Tokio runtime: {err}"
      ));
    },
  };

  match rt.block_on(client::connect(&node_id, &addrs, &relay_url, request)) {
    Ok(response) => match response {
      Response::Get(get_response) => {
        if get_response.is_err {
          LeanExcept::error_string(&get_response.message)
        } else {
          LeanExcept::ok(LeanGetResponse::mk(
            &get_response.message,
            &get_response.hash,
            &get_response.bytes,
          ))
        }
      },
      _ => LeanExcept::error_string("error: incorrect server response"),
    },
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}

/// `Iroh.Serve.serve' : Unit → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_serve(_unit: LeanOwned) -> LeanExcept<LeanOwned> {
  let rt = match tokio::runtime::Runtime::new() {
    Ok(rt) => rt,
    Err(err) => {
      return LeanExcept::error_string(&format!(
        "failed to create Tokio runtime: {err}"
      ));
    },
  };

  match rt.block_on(server::serve()) {
    Ok(()) => LeanExcept::ok(LeanOwned::box_usize(0)),
    Err(err) => LeanExcept::error_string(&err.to_string()),
  }
}
