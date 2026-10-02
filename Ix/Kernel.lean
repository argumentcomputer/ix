import Ix.Address.Core
import Ix.Kernel.Ref
import Ix.Kernel.Search
import Ix.Kernel.Ingress.Records
import Ix.Kernel.Egress.Projection
import Ix.Kernel.Ixon.Prelude
import Ix.Kernel.Ixon.ReaderSpec
import Ix.Kernel.Ixon.Installed
import Ix.Kernel.Ixon.Values

/-! # Ix.Kernel

The kernel-side boundary of the certified Ixon checker. The checker
(`Ix.Kernel.Cached.checkDecls` at `.verified`, with `Ix.Kernel.model_exists`)
is derived from con-leche (`Ix/Kernel/NOTICE`); Ix contributes only the
boundary:

* `Ix.Kernel.Reader` (`Ix/Kernel/Ixon/Reader.lean`, with
  `ReaderSpec`): the Ixon reader from decoded records to
  `Array Ix.Kernel.Declaration`, its address-to-name encoding (`keyName`,
  injective) and its record-by-record specification;
* `Ix/Kernel/Ixon/{PinData,NatOpPinData,Prelude}.lean`: the committed pin
  table, Nat-operation pins and Ixon prelude, generated from the compiled
  Init's records;
* `Ix/Kernel/Ixon/{Installed,Values}.lean`: installation and definition
  values of the fold (`Ix.Kernel.Cached.checkDecls_installs`,
  `Ix.Kernel.Cached.checkDecls_model_defn_values`, beside the fold they
  are about), used by the public theorems;
* `Ix.Kernel.ConstRef` (`Ref`), the decoded-record store
  (`Ix.Kernel.Ingress`, `Ingress/Records.lean`), bounded search outcomes
  (`Search`), and the projection-record writer (`Ix.Kernel.Egress`,
  `Egress/Projection.lean`) that projection reconstruction runs;
* `Ix.Kernel.Audit`: the certified gate's manifest and audits.

The certified API, `Ix.Kernel.Admission.checkBytes`
(`Ix/Kernel/Admission.lean`), runs the byte stage, this reader and the
fold; this umbrella does not import it. Its public theorems (model
existence over `Ix.Kernel.Model`, no proof of the pinned `False`, fidelity,
resources) are in `Ix.Kernel.Admission.Theorems`. The contract, trust
surface, audits and origin are described in `docs/kernel.md`. -/
