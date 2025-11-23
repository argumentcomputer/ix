use crate::ix::address::Address;
use std::env;
use std::fs;
use std::io;
use std::path::PathBuf;

#[derive(Debug)]
pub enum StoreError {
  UnknownAddress(Address),
  IoError(io::Error),
  IxonError(String),
  NoHome,
}

impl std::fmt::Display for StoreError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      StoreError::UnknownAddress(a) => write!(f, "unknown address {:?}", a),
      StoreError::IoError(e) => write!(f, "IO error: {}", e),
      StoreError::IxonError(e) => write!(f, "ixon error: {}", e),
      StoreError::NoHome => write!(f, "no HOME environment variable"),
    }
  }
}

impl std::error::Error for StoreError {}

impl From<io::Error> for StoreError {
  fn from(error: io::Error) -> Self {
    StoreError::IoError(error)
  }
}

pub type StoreResult<T> = Result<T, StoreError>;

pub struct Store;

impl Store {
  /// Get the home directory from the HOME environment variable
  fn get_home_dir() -> StoreResult<PathBuf> {
    env::var("HOME").map(PathBuf::from).map_err(|_| StoreError::NoHome)
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
