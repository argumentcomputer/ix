pub mod client;
pub mod server;

pub mod common {
  use bincode::{Decode, Encode};
  use serde::{Deserialize, Serialize};

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub enum Request {
    Put(PutRequest),
    Get(GetRequest),
  }

  impl Request {
    pub fn to_bytes(&self) -> Vec<u8> {
      bincode::encode_to_vec(self, bincode::config::standard()).unwrap()
    }
    pub fn from_bytes(bytes: &[u8]) -> Self {
      bincode::decode_from_slice(bytes, bincode::config::standard()).unwrap().0
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
    pub fn from_bytes(bytes: &[u8]) -> Self {
      bincode::decode_from_slice(bytes, bincode::config::standard()).unwrap().0
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
