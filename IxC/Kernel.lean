import IxC.Address.Core
import IxC.Kernel.Ref
import IxC.Kernel.Search
import IxC.Kernel.Ingress.Records
import IxC.Kernel.Egress.Projection
import IxC.Kernel.Ixon.Prelude
import IxC.Kernel.Ixon.ReaderSpec
import IxC.Kernel.Ixon.Installed
import IxC.Kernel.Ixon.Values

/-! # Ix.Kernel

The kernel-side boundary of the certified Ixon checker. The checker
(`Ix.Kernel.Cached.checkDecls` at `.verified`, with `Ix.Kernel.model_exists`)
is derived from con-leche (`IxC/Kernel/NOTICE`); Ix contributes only the
boundary:

* `Ix.Kernel.Reader` (`IxC/Kernel/Ixon/Reader.lean`, with
  `ReaderSpec`): the Ixon reader from decoded records to
  `Array Ix.Kernel.Declaration`, its address-to-name encoding (`keyName`,
  injective) and its record-by-record specification;
* `IxC/Kernel/Ixon/{PinData,NatOpPinData,Prelude}.lean`: the committed pin
  table, Nat-operation pins and Ixon prelude, generated from the compiled
  Init's records;
* `IxC/Kernel/Ixon/{Installed,Values}.lean`: installation and definition
  values of the fold (`Ix.Kernel.Cached.checkDecls_installs`,
  `Ix.Kernel.Cached.checkDecls_model_defn_values`, beside the fold they
  are about), used by the public theorems;
* `Ix.Kernel.ConstRef` (`Ref`), the decoded-record store
  (`Ix.Kernel.Ingress`, `Ingress/Records.lean`), bounded search outcomes
  (`Search`), and the projection-record writer (`Ix.Kernel.Egress`,
  `Egress/Projection.lean`) that projection reconstruction runs;
* `Ix.Kernel.Audit`: the certified gate's manifest and audits.

The certified API, `Ix.Kernel.Admission.checkBytes`
(`IxC/Kernel/Admission.lean`), runs the byte stage, this reader and the
fold; this umbrella does not import it. Its public theorems (model
existence over `Ix.Kernel.Model`, no proof of the pinned `False`, fidelity,
resources) are in `Ix.Kernel.Admission.Theorems`. The contract, trust
surface, audits and origin are described in `docs/kernel.md`. -/
