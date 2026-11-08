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

  /// Return `~/.ix` directory path if `HOME` is set.
  pub fn ix_dir() -> Option<std::path::PathBuf> {
    std::env::var_os("HOME").map(|h| std::path::PathBuf::from(h).join(".ix"))
  }

  /// Load a persistent 32-byte node `SecretKey` from `~/.ix/identity.key`,
  /// or generate and persist a fresh key if none exists yet.
  pub fn load_or_create_secret_key() -> iroh::SecretKey {
    if let Some(dir) = ix_dir() {
      let key_path = dir.join("identity.key");
      if let Ok(bytes) = std::fs::read(&key_path) {
        if let Ok(arr) = <[u8; 32]>::try_from(bytes.as_slice()) {
          return iroh::SecretKey::from(arr);
        }
      }
      let mut bytes = [0u8; 32];
      getrandom::fill(&mut bytes).expect("failed to generate random bytes");
      if std::fs::create_dir_all(&dir).is_ok() {
        let _ = std::fs::write(&key_path, bytes);
      }
      iroh::SecretKey::from(bytes)
    } else {
      let mut bytes = [0u8; 32];
      getrandom::fill(&mut bytes).expect("failed to generate random bytes");
      iroh::SecretKey::from(bytes)
    }
  }

  /// Atomically persist `bytes` into the global `IxStore` (`~/.ix/store`).
  pub fn write_store_blob(
    hash_hex: &str,
    bytes: &[u8],
  ) -> std::io::Result<std::path::PathBuf> {
    let addr = ix_common::address::Address::from_hex(hash_hex).ok_or_else(|| {
      std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        "invalid BLAKE3 hex hash",
      )
    })?;
    let store = ix_common::store::IxStore::global()
      .map_err(|e| std::io::Error::other(e.to_string()))?;
    store
      .write_at(&addr, bytes)
      .map_err(|e| std::io::Error::other(e.to_string()))?;
    Ok(store.loose_path(&addr))
  }

  /// Read and BLAKE3-verify a content-addressed blob from the global `IxStore` (`~/.ix/store`).
  pub fn read_store_blob(hash_hex: &str) -> Option<Vec<u8>> {
    let addr = ix_common::address::Address::from_hex(hash_hex)?;
    let store = ix_common::store::IxStore::global().ok()?;
    store.read_verified(&addr).ok()
  }
}
