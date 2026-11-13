//! The committed IxVM witness fixture (`IxVM/IxVM/fixtures/*.ixf`), in Ixon
//! serialization. `IxVM/IxVM/Fixture.lean` documents the grammar and builds
//! the execution package's hints from it.
use aiur::ixon::Reader;
use std::path::Path;

pub const MAGIC: &[u8; 8] = b"IXVMFIX\0";
pub const VERSION: u64 = 3;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Serialized {
  pub address: [u8; 32],
  pub bytes: Vec<u8>,
  pub hint: u64,
}

impl Serialized {
  /// The address as the verifier's 32 byte-valued arguments.
  pub fn address_words(&self) -> Vec<u64> {
    words(&self.address)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fixture {
  /// The Ixon wire format of the serialized bytes.
  pub format: String,
  pub name: String,
  pub address: [u8; 32],
  /// Correctly hashed, but ill-typed: the verifier must reject it.
  pub invalid_proof: Serialized,
  pub constants: Vec<Serialized>,
  pub blobs: Vec<Serialized>,
  pub roles: Vec<Serialized>,
}

fn words(address: &[u8; 32]) -> Vec<u64> {
  address.iter().copied().map(u64::from).collect()
}

fn address(r: &mut Reader<'_>) -> Result<[u8; 32], String> {
  Ok(r.raw(32)?.try_into().expect("32 bytes"))
}

fn serialized(r: &mut Reader<'_>) -> Result<Serialized, String> {
  Ok(Serialized {
    address: address(r)?,
    bytes: r.bytes()?.to_vec(),
    hint: r.nat()?,
  })
}

impl Fixture {
  pub fn decode(bytes: &[u8]) -> Result<Self, String> {
    let mut r = Reader::new(bytes);
    if r.raw(MAGIC.len()).ok() != Some(&MAGIC[..]) {
      return Err("not an IxVM fixture".into());
    }
    let version = r.nat()?;
    // Version 3: Ixon v5 records, each carrying its binder data. Version 2
    // carried the binder data beside the records, which IxVM no longer reads.
    if version != VERSION {
      return Err(format!("unsupported IxVM fixture version {version}"));
    }
    let fixture = Self {
      format: r.string()?,
      name: r.string()?,
      address: address(&mut r)?,
      invalid_proof: serialized(&mut r)?,
      constants: r.list(serialized)?,
      blobs: r.list(serialized)?,
      roles: r.list(serialized)?,
    };
    r.finish()?;
    Ok(fixture)
  }

  pub fn load(path: &Path) -> Result<Self, String> {
    let bytes = std::fs::read(path)
      .map_err(|e| format!("cannot read fixture {}: {e}", path.display()))?;
    Self::decode(&bytes)
      .map_err(|e| format!("invalid fixture {}: {e}", path.display()))
  }

  /// The target address as the verifier's 32 byte-valued arguments.
  pub fn address_words(&self) -> Vec<u64> {
    words(&self.address)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// The committed fixture decodes strictly, and its addresses are the
  /// BLAKE3 hashes of their bytes.
  #[test]
  fn committed_fixture_is_well_formed() {
    let path = concat!(
      env!("CARGO_MANIFEST_DIR"),
      "/../../IxVM/IxVM/fixtures/nat-add-comm.ixf"
    );
    let fixture = Fixture::load(Path::new(path)).unwrap();
    assert_eq!(fixture.format, "ixon-v5");
    assert_eq!(fixture.name, "Nat.add_comm");
    assert!(fixture.constants.iter().any(|c| c.address == fixture.address));
    for entry in fixture
      .constants
      .iter()
      .chain(&fixture.blobs)
      .chain(&fixture.roles)
      .chain([&fixture.invalid_proof])
    {
      assert_eq!(*blake3::hash(&entry.bytes).as_bytes(), entry.address);
    }
    let bytes = std::fs::read(path).unwrap();
    for end in [0, 8, 9, bytes.len() - 1] {
      assert!(Fixture::decode(&bytes[..end]).is_err());
    }
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(Fixture::decode(&trailing).unwrap_err().contains("trailing"));
  }
}
