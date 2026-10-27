//! Primitive identities and permission are separate. Bound candidate addresses
//! may build expected syntax; a bound artifact's primitive table holds only
//! the roles its binding has admitted (see `role_admission`).

use ix_common::address::Address;
use ixon::role_table::Role;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

use crate::mode::KernelMode;
use crate::primitive::Primitives;

#[derive(Clone)]
pub(crate) enum PrimitiveContext<M: KernelMode> {
  /// Unbound input: the pinned primitive addresses.
  Legacy(Arc<Primitives<M>>),
  /// A bound artifact, with the table built from its admitted roles and
  /// what those roles allow.
  #[cfg(not(target_arch = "riscv64"))]
  Bound(
    crate::role_admission::ArtifactSource,
    Arc<Primitives<M>>,
    Arc<BoundRoles>,
  ),
  #[cfg(not(target_arch = "riscv64"))]
  UnpreparedBound,
}

/// What a bound artifact's admitted roles allow beyond its table.
#[derive(Default)]
pub(crate) struct BoundRoles {
  admitted: FxHashSet<Role>,
  /// The standard axioms in the table: `propext`, `Classical.choice` and
  /// `Quot.sound`. These, and only these, may be used.
  axioms: FxHashSet<Address>,
  /// `sorryAx`, which may be declared but not used.
  inert: FxHashSet<Address>,
}

impl<M: KernelMode> PrimitiveContext<M> {
  /// The context of a bound artifact whose admitted roles are `admitted`:
  /// those of the source's completed admission, or, while a group is being
  /// validated, only the groups admitted before it.
  #[cfg(not(target_arch = "riscv64"))]
  pub(crate) fn bound<F>(
    source: crate::role_admission::ArtifactSource,
    admitted: &FxHashMap<Role, Address>,
    name_for_addr: F,
  ) -> Self
  where
    F: FnMut(&Address) -> Option<ix_common::env::Name>,
  {
    let roles = admitted.keys().copied().collect();
    Self::bound_with_table(source, admitted, roles, name_for_addr)
  }

  /// A bound context whose table holds `table` while only `admitted` roles
  /// are admitted. The table may hold, besides the admitted roles, the
  /// candidates of the group under validation, for declarations the kernel
  /// recognises only at their table addresses (the quotient records).
  #[cfg(not(target_arch = "riscv64"))]
  pub(crate) fn bound_with_table<F>(
    source: crate::role_admission::ArtifactSource,
    table: &FxHashMap<Role, Address>,
    admitted: FxHashSet<Role>,
    name_for_addr: F,
  ) -> Self
  where
    F: FnMut(&Address) -> Option<ix_common::env::Name>,
  {
    let in_table = |roles: &[Role]| -> FxHashSet<Address> {
      roles.iter().filter_map(|role| table.get(role).cloned()).collect()
    };
    let roles = BoundRoles {
      axioms: in_table(&[Role::Propext, Role::Choice, Role::QuotSound]),
      inert: in_table(&[Role::SorryAx]),
      admitted,
    };
    let table = Primitives::from_admitted(
      |role| table.get(&role).cloned(),
      name_for_addr,
    );
    Self::Bound(source, Arc::new(table), Arc::new(roles))
  }

  /// Whether checking follows the certified checker's safety tier: partial
  /// definitions stay opaque, every safe declaration, not only a definition,
  /// is fenced from partial and unsafe constants, and an opaque is checked as
  /// safe. A bound artifact does; unbound input follows Lean's kernel.
  pub(crate) fn follows_safety_tier(&self) -> bool {
    match self {
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(..) => true,
      _ => false,
    }
  }

  /// Whether the safe axiom at `address` may be used: any axiom in unbound
  /// input; in a bound artifact only an admitted standard axiom. The
  /// certified theory is Lean with its three standard axioms; unsafe axioms
  /// are outside it (safe declarations cannot reference them).
  pub(crate) fn axiom_usable(&self, address: &Address) -> bool {
    match self {
      Self::Legacy(_) => {
        let _ = address;
        true
      },
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(_, _, roles) => roles.axioms.contains(address),
      #[cfg(not(target_arch = "riscv64"))]
      Self::UnpreparedBound => false,
    }
  }

  /// Whether the axiom at `address` may be declared: as usable, and also
  /// `sorryAx`, which a bound artifact tolerates as a declaration only.
  pub(crate) fn axiom_declarable(&self, address: &Address) -> bool {
    match self {
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(_, _, roles) => {
        roles.inert.contains(address) || self.axiom_usable(address)
      },
      _ => self.axiom_usable(address),
    }
  }

  /// The primitive table: the pinned one for unbound input, the admitted
  /// one for a bound artifact, none before a bound input is prepared.
  pub(crate) fn table(&self) -> Option<&Primitives<M>> {
    match self {
      Self::Legacy(primitives) => Some(primitives),
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(_, primitives, _) => Some(primitives),
      #[cfg(not(target_arch = "riscv64"))]
      Self::UnpreparedBound => None,
    }
  }

  /// Whether rules that need `role` may run. Unbound input keeps the
  /// pinned addresses; a bound artifact needs the role admitted.
  pub(crate) fn admits(&self, role: Role) -> bool {
    match self {
      Self::Legacy(_) => {
        let _ = role;
        true
      },
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(_, _, roles) => roles.admitted.contains(&role),
      #[cfg(not(target_arch = "riscv64"))]
      Self::UnpreparedBound => false,
    }
  }

  pub(crate) fn candidate_address(&self, role: Role) -> Option<&Address> {
    match self {
      #[cfg(not(target_arch = "riscv64"))]
      Self::Bound(source, _, _) => {
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
    self.entry_error().unwrap_or("primitive table is unavailable").into()
  }
}
