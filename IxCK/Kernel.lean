import IxCK.Address.Core
import IxCK.Kernel.Ref
import IxCK.Kernel.Search
import IxCK.Kernel.Ingress.Records
import IxCK.Kernel.Egress.Projection
import IxCK.Kernel.Ixon.Prelude
import IxCK.Kernel.Ixon.ReaderSpec
import IxCK.Kernel.Ixon.Installed
import IxCK.Kernel.Ixon.Values

/-! # Ix.Kernel

The kernel-side boundary of the certified Ixon checker. The checker
(`Ix.Kernel.Cached.checkDecls` at `.verified`, with `Ix.Kernel.model_exists`)
is derived from con-leche (`IxCK/Kernel/NOTICE`); Ix contributes only the
boundary:

* `Ix.Kernel.Reader` (`IxCK/Kernel/Ixon/Reader.lean`, with
  `ReaderSpec`): the Ixon reader from decoded records to
  `Array Ix.Kernel.Declaration`, keyed by the addresses the records'
  references use, and its record-by-record specification;
* `IxCK/Kernel/Ixon/RoleTable.lean`: the role table, its binding-section
  format and canonical decoder (`RoleTable.ofBytes_eq_some_iff`) and its
  well-formedness (`RoleTable.check`); the specification set it binds is
  `IxCK/Kernel/Roles.lean`;
* `IxCK/Kernel/Ixon/{RoleData,Prelude}.lean`: the default role table, its
  evidence records and the Ixon prelude, generated from the compiled Init's
  records (`kernel-pin-gen`);
* `IxCK/Kernel/Ixon/{Installed,Values}.lean`: installation and definition
  values of the fold (`Ix.Kernel.Cached.checkDecls_installs`,
  `Ix.Kernel.Cached.checkDecls_model_defn_values`, beside the fold they
  are about), used by the public theorems;
* `Ix.Kernel.ConstRef` (`Ref`), the decoded-record store
  (`Ix.Kernel.Ingress`, `Ingress/Records.lean`), bounded search outcomes
  (`Search`), and the projection-record writer (`Ix.Kernel.Egress`,
  `Egress/Projection.lean`) that projection reconstruction runs;
* `Ix.Kernel.Audit`: the certified gate's manifest and audits.

The certified API, `Ix.Kernel.Admission.checkBytes`
(`IxCK/Kernel/Admission.lean`), runs the byte stage, this reader and the
fold; this umbrella does not import it. Its public theorems (model
existence over `Ix.Kernel.Model`, no proof of the pinned `False`, fidelity,
resources) are in `Ix.Kernel.Admission.Theorems`. The contract, trust
surface, audits and origin are described in `docs/kernel.md`. -/
