//! Names at generated-reference construction sites. Copied source expressions
//! are never traversed or renamed by this policy.

use ix_common::env::Name;

#[derive(Clone, Default)]
pub struct AuxNames {
  /// None retains source spellings (decompilation and source recognition).
  scope: Option<(Name, Vec<usize>)>,
}

impl AuxNames {
  pub fn compiler(representative: Name, perm: Vec<usize>) -> Self {
    Self { scope: Some((representative, perm)) }
  }

  pub fn is_private(&self) -> bool {
    self.scope.is_some()
  }

  /// Primary recursors retain the existing intrinsic-recursion publication
  /// path; derived helpers have their own reserved namespace.
  pub fn member(&self, owner: &Name, kind: &str) -> Name {
    let owner = if self.scope.is_some() && kind != "rec" {
      Name::str(owner.clone(), "_ix".into())
    } else {
      owner.clone()
    };
    Name::str(owner, kind.into())
  }

  pub fn nested(&self, owner: &Name, kind: &str, index: usize) -> Name {
    let Some((representative, perm)) = &self.scope else {
      return Name::str(owner.clone(), format!("{kind}_{index}"));
    };
    if kind == "rec" {
      return Name::str(owner.clone(), format!("{kind}_{index}"));
    }
    let (owner, index) = match perm.get(index.saturating_sub(1)) {
      Some(slot) if *slot != usize::MAX => (representative, slot + 1),
      _ => (owner, index),
    };
    Name::str(Name::str(owner.clone(), "_ix".into()), format!("{kind}_{index}"))
  }
}
