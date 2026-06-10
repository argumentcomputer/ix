pub mod client;
pub mod server;

pub mod common {
  use bincode::{Decode, Encode};
  use serde::{Deserialize, Serialize};

  /// ALPN for the ix iroh protocol. Versioned and ix-specific (this code
  /// was derived from the iroh examples, which use
  /// `n0/iroh/examples/magic/0` — keeping that would collide with anything
  /// else built from the same example).
  pub const ALPN: &[u8] = b"ix/iroh/0";

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub enum Request {
    Put(PutRequest),
    Get(GetRequest),
  }

  /// Decode a length-framed message from untrusted network bytes.
  ///
  /// Never panics: any malformed/truncated/trailing-garbage input is an
  /// `Err`. With `panic = "abort"` a panicking decode would let a single
  /// bad frame kill the whole process.
  fn decode_untrusted<T: Decode<()>>(bytes: &[u8]) -> Result<T, String> {
    match bincode::decode_from_slice(bytes, bincode::config::standard()) {
      Ok((v, consumed)) if consumed == bytes.len() => Ok(v),
      Ok((_, consumed)) => Err(format!(
        "trailing garbage: consumed {consumed} of {} bytes",
        bytes.len()
      )),
      Err(e) => Err(format!("malformed message: {e}")),
    }
  }

  impl Request {
    pub fn to_bytes(&self) -> Vec<u8> {
      bincode::encode_to_vec(self, bincode::config::standard()).unwrap()
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
      decode_untrusted(bytes)
    }
  }

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub struct PutRequest {
    pub bytes: Vec<u8>,
  }

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub struct GetRequest {
    pub hash: String,
  }

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub enum Response {
    Put(PutResponse),
    Get(GetResponse),
  }

  impl Response {
    pub fn to_bytes(&self) -> Vec<u8> {
      bincode::encode_to_vec(self, bincode::config::standard()).unwrap()
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
      decode_untrusted(bytes)
    }
  }

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub struct PutResponse {
    pub is_err: bool,
    pub message: String,
    pub hash: String,
  }

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub struct GetResponse {
    pub is_err: bool,
    pub message: String,
    pub hash: String,
    pub bytes: Vec<u8>,
  }
}
