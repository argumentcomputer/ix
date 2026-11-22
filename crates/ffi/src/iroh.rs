pub mod client;
pub mod server;

pub mod common {
  use bincode::{Decode, Encode};
  use serde::{Deserialize, Serialize};

  /// Maximum serialized frame size (in bytes) accepted from the network.
  pub const READ_SIZE_LIMIT: usize = 100_000_000;

  fn decode_config() -> impl bincode::config::Config {
    bincode::config::standard().with_limit::<READ_SIZE_LIMIT>()
  }

  #[derive(Debug, Serialize, Deserialize, Encode, Decode)]
  pub enum Request {
    Put(PutRequest),
    Get(GetRequest),
  }

  impl Request {
    pub fn to_bytes(&self) -> Result<Vec<u8>, bincode::error::EncodeError> {
      bincode::encode_to_vec(self, bincode::config::standard())
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
      let (req, len): (Self, usize) =
        bincode::decode_from_slice(bytes, decode_config())
          .map_err(|e| format!("failed to decode request: {e}"))?;
      if len != bytes.len() {
        return Err(format!(
          "trailing bytes in request frame: decoded {len} of {} bytes",
          bytes.len()
        ));
      }
      Ok(req)
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
    pub fn to_bytes(&self) -> Result<Vec<u8>, bincode::error::EncodeError> {
      bincode::encode_to_vec(self, bincode::config::standard())
    }
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
      let (resp, len): (Self, usize) =
        bincode::decode_from_slice(bytes, decode_config())
          .map_err(|e| format!("failed to decode response: {e}"))?;
      if len != bytes.len() {
        return Err(format!(
          "trailing bytes in response frame: decoded {len} of {} bytes",
          bytes.len()
        ));
      }
      Ok(resp)
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

  #[cfg(test)]
  mod tests {
    use super::*;

    #[test]
    fn request_from_bytes_rejects_malformed_and_oversized_prefix() {
      assert!(Request::from_bytes(&[]).is_err());
      // Variant 0 (Put) followed by a bincode u64 length prefix exceeding READ_SIZE_LIMIT.
      let mut malicious = vec![0u8, 253u8];
      malicious.extend_from_slice(&(u64::MAX).to_le_bytes());
      assert!(Request::from_bytes(&malicious).is_err());
    }

    #[test]
    fn response_from_bytes_rejects_malformed_and_trailing_bytes() {
      assert!(Response::from_bytes(&[]).is_err());
      let resp = Response::Get(GetResponse {
        is_err: false,
        message: "ok".to_string(),
        hash: "0".repeat(64),
        bytes: b"hello".to_vec(),
      });
      let mut encoded = resp.to_bytes().unwrap();
      assert!(Response::from_bytes(&encoded).is_ok());
      encoded.push(0xAA);
      assert!(Response::from_bytes(&encoded).is_err());
    }
  }
}
