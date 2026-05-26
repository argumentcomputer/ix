//! Content-addressed filesystem store for Ix data.
//!
//! Objects are stored at `~/.ix/store/XX/YY/ZZ/<remaining_hex>` where `XX/YY/ZZ`
//! are derived from the first 6 hex characters of the Blake3 hash. This provides
//! deterministic addressing: identical content always maps to the same path.

use crate::ix::address::Address;
use std::env;
use std::fs;
use std::io;
use std::path::PathBuf;

/// Errors that can occur during store operations.
#[derive(Debug)]
pub enum StoreError {
  /// The requested address does not exist in the store.
  UnknownAddress(Address),
  /// An underlying filesystem I/O error.
  IoError(io::Error),
  /// An error during ixon serialization or deserialization.
  IxonError(String),
  /// The `HOME` environment variable is not set.
  NoHome(env::VarError),
}

impl std::fmt::Display for StoreError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      StoreError::UnknownAddress(a) => write!(f, "unknown address {:?}", a),
      StoreError::IoError(e) => write!(f, "IO error: {}", e),
      StoreError::IxonError(e) => write!(f, "ixon error: {}", e),
      StoreError::NoHome(e) => write!(f, "no HOME environment variable: {}", e),
    }
  }
}

impl std::error::Error for StoreError {}

impl From<io::Error> for StoreError {
  fn from(error: io::Error) -> Self {
    StoreError::IoError(error)
  }
}

/// Alias for `Result<T, StoreError>`.
pub type StoreResult<T> = Result<T, StoreError>;

/// Handle for reading and writing content-addressed objects under `~/.ix/store`.
pub struct Store;

impl Store {
  /// Get the home directory from the HOME environment variable
  fn get_home_dir() -> StoreResult<PathBuf> {
    env::var("HOME").map(PathBuf::from).map_err(StoreError::NoHome)
  }

  /// Get the store directory path (~/.ix/store), creating it if needed
  fn store_dir() -> StoreResult<PathBuf> {
    let home = Self::get_home_dir()?;
    let path = home.join(".ix").join("store");
    if !path.exists() {
      fs::create_dir_all(&path)?;
    }
    Ok(path)
  }

  /// Get the full path for a given address, creating parent directories if needed
  /// Path structure: store/XX/YY/ZZ/remaining_hex
  /// where XX, YY, ZZ are the first 6 hex characters of the hash
  fn store_path(addr: &Address) -> StoreResult<PathBuf> {
    let store = Self::store_dir()?;
    let hex = addr.hex();
    let dir1 = &hex[0..2];
    let dir2 = &hex[2..4];
    let dir3 = &hex[4..6];
    let file = &hex[6..];
    let path = store.join(dir1).join(dir2).join(dir3);
    if !path.exists() {
      fs::create_dir_all(&path)?;
    }

    Ok(path.join(file))
  }

  /// Write bytes to the store and return their address (blake3 hash)
  pub fn write(bytes: &[u8]) -> StoreResult<Address> {
    let addr = Address::hash(bytes);
    let path = Self::store_path(&addr)?;
    fs::write(path, bytes)?;
    Ok(addr)
  }

  /// Read bytes from the store given an address
  pub fn read(addr: &Address) -> StoreResult<Vec<u8>> {
    let path = Self::store_path(addr)?;
    let bytes = fs::read(path)?;
    Ok(bytes)
  }
}
