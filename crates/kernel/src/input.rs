//! Read-only input used by ingress. A bound artifact never materializes a
//! caller's Constant cache; every semantic read crosses its raw-source gate.

use std::cell::RefCell;
use std::sync::Arc;

use ix_common::address::Address;
use ix_common::env::{Name, ReducibilityHints};
use ixon::constant::Constant;
use ixon::env::{Env, Named};

#[derive(Clone, Copy)]
pub(crate) enum Input<'a> {
  Legacy(&'a Env),
  #[cfg(not(target_arch = "riscv64"))]
  Artifact(&'a crate::role_admission::ArtifactSource),
}

impl<'a> From<&'a Env> for Input<'a> {
  fn from(env: &'a Env) -> Self {
    Self::Legacy(env)
  }
}

impl Input<'_> {
  /// A reference from a declaration being read must name an authentic
  /// carried record, not merely a present key (see
  /// `ArtifactSource::authenticate_reference`).
  pub(crate) fn require_reference(
    self,
    address: &Address,
  ) -> Result<(), String> {
    #[cfg(not(target_arch = "riscv64"))]
    if let Self::Artifact(source) = self {
      return source
        .authenticate_reference(address)
        .map_err(|error| format!("reference {}: {error}", address.hex()));
    }
    let _ = address;
    Ok(())
  }
  pub(crate) fn constant(
    self,
    address: &Address,
  ) -> Result<Option<Arc<Constant>>, String> {
    match self {
      Self::Legacy(env) => {
        env.consts.get(address).map(|entry| entry.get_at(address)).transpose()
      },
      #[cfg(not(target_arch = "riscv64"))]
      Self::Artifact(source) => match source.record(address) {
        Ok(record) => Ok(Some(Arc::new(record.into_constant()))),
        Err(crate::role_admission::Error::MissingRecord(_)) => Ok(None),
        Err(error) => Err(error.to_string()),
      },
    }
  }

  pub(crate) fn blob(
    self,
    address: &Address,
  ) -> Result<Option<Vec<u8>>, String> {
    match self {
      Self::Legacy(env) => Ok(env.get_blob(address)),
      #[cfg(not(target_arch = "riscv64"))]
      Self::Artifact(source) => match source.blob(address) {
        Ok(blob) => Ok(Some(blob.bytes().to_vec())),
        Err(crate::role_admission::Error::MissingBlob(_)) => Ok(None),
        Err(error) => Err(error.to_string()),
      },
    }
  }

  pub(crate) fn contains(self, address: &Address) -> bool {
    match self {
      Self::Legacy(env) => env.consts.contains_key(address),
      #[cfg(not(target_arch = "riscv64"))]
      Self::Artifact(source) => source.contains_record(address),
    }
  }

  pub(crate) fn named(self, name: &Name) -> Option<Named> {
    match self {
      Self::Legacy(env) => env.lookup_name(name),
      #[cfg(not(target_arch = "riscv64"))]
      Self::Artifact(source) => source.named(name),
    }
  }

  pub(crate) fn hint(self, address: &Address) -> Option<ReducibilityHints> {
    match self {
      Self::Legacy(env) => env.anon_hints.get(address).map(|entry| *entry),
      #[cfg(not(target_arch = "riscv64"))]
      Self::Artifact(source) => source.hint(address),
    }
  }

  pub(crate) fn mdata(
    self,
    map: &ixon::metadata::KVMap,
  ) -> Result<crate::expr::MData, String> {
    struct Reader<'a> {
      input: Input<'a>,
      error: RefCell<Option<String>>,
    }
    impl ixon::metadata::MetadataSource for Reader<'_> {
      fn get_blob(&self, address: &Address) -> Option<Vec<u8>> {
        match self.input.blob(address) {
          Ok(bytes) => bytes,
          Err(error) => {
            self.error.borrow_mut().get_or_insert(error);
            None
          },
        }
      }
      fn get_name(&self, address: &Address) -> Option<Name> {
        match self.input {
          Input::Legacy(env) => env.get_name(address),
          #[cfg(not(target_arch = "riscv64"))]
          Input::Artifact(source) => source.name(address),
        }
      }
    }
    let reader = Reader { input: self, error: RefCell::new(None) };
    let data = ixon::metadata::resolve_kvmap(map, &reader);
    match reader.error.into_inner() {
      Some(error) => Err(error),
      None => Ok(data),
    }
  }
}
