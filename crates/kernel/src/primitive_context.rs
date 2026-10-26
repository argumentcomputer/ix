//! Primitive identities and permission are separate. Bound candidate addresses
//! may build expected syntax; this guarded stage enables no bound shortcut.

use ix_common::address::Address;
use ixon::role_table::Role;
use std::sync::Arc;

use crate::mode::KernelMode;
use crate::primitive::Primitives;

#[derive(Clone)]
pub(crate) enum PrimitiveContext<M: KernelMode> {
  Legacy(Arc<Primitives<M>>),
  #[cfg(not(target_arch = "riscv64"))]
  Bound(crate::role_admission::ArtifactSource),
  #[cfg(not(target_arch = "riscv64"))]
  UnpreparedBound,
}

impl<M: KernelMode> PrimitiveContext<M> {
  pub(crate) fn legacy(&self) -> Option<&Primitives<M>> {
    match self {
      Self::Legacy(primitives) => Some(primitives),
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(_) | Self::UnpreparedBound => None,
    }
  }

  pub(crate) fn candidate_address(&self, role: Role) -> Option<&Address> {
    match self {
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(source) => {
        source.binding().and_then(|binding| binding.role(role))
      },
      _ => {
        let _ = role;
        None
      },
    }
  }

  pub(crate) fn entry_error(&self) -> Option<&'static str> {
    match self {
      #[cfg(not(target_arch = "riscv64"))]
      Self::UnpreparedBound => {
        Some("bound input requires an owned artifact checker")
      },
      _ => None,
    }
  }

  pub(crate) fn unavailable(&self) -> String {
    self
      .entry_error()
      .unwrap_or(
        "bound artifact primitive rules have not been semantically admitted",
      )
      .into()
  }
}
