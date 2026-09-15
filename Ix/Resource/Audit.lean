import Ix.Tc.Verify.Audit.Basic
import Ix.Resource.Admit

/-! Exact trust manifest for the executable resource-state invariants.
No native, upstream, pending, or sorry axioms are admitted. -/

namespace Ix.Resource.Audit
open Ix.Tc.Verify.Audit
private def roots : Array RootAllowance := #[
  { root := ``Ix.Resource.root_scopeTree, standardAxioms := #[``propext] },
  { root := ``Ix.Resource.push_scopeTree, standardAxioms := #[``propext, ``Classical.choice, ``Quot.sound] },
  { root := ``Ix.Resource.ancestor_older },
  { root := ``Ix.Resource.outlivesAux_sound, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Ix.Resource.outlives_sound, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Ix.Resource.fresh_scope_cannot_escape, standardAxioms := #[``propext, ``Classical.choice, ``Quot.sound] },
  { root := ``Ix.Resource.checkOrigins_sound, standardAxioms := #[``propext, ``Quot.sound] },
  { root := ``Ix.Resource.endLoan_live },
  { root := ``Ix.Resource.endLoan_unique },
  { root := ``Ix.Resource.moveOwner_requires, standardAxioms := #[``propext] },
  { root := ``Ix.Resource.shareOwner_permanent, standardAxioms := #[``propext] },
  { root := ``Ix.Resource.checkUnrestricted_sound, standardAxioms := #[``propext] },
  { root := ``Ix.Resource.joinOwner_live, standardAxioms := #[``propext] },
  { root := ``Ix.Resource.joinOwner_unique, standardAxioms := #[``propext] },
  { root := ``Ix.Resource.checkDemand_sound, standardAxioms := #[``propext, ``Quot.sound] }
]
run_cmd Ix.Tc.Verify.Audit.check roots
end Ix.Resource.Audit

