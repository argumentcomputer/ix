/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Address.Core
import Ix.Kernel.Ref
import Ix.Kernel.Search
import Ix.Kernel.Ingress.Records
import Ix.Kernel.Egress.Projection
import Ix.Kernel.ConLeche.Prelude
import Ix.Kernel.ConLeche.ReaderSpec
import Ix.Kernel.ConLeche.Installed
import Ix.Kernel.ConLeche.Values

/-! # Ix.Kernel

The kernel-side boundary of the certified Ixon checker (plan v4). The checker
is con-leche's, ported in place under `ConLeche/**` (`ConLeche.Cached.checkDecls`
at `.verified`, with `ConLeche.model_exists`); Ix contributes only the
boundary:

* `Ix.Kernel.ConLecheReader` (`Ix/Kernel/ConLeche/Reader.lean`, with
  `ReaderSpec`): the Ixon reader from decoded records to
  `Array ConLeche.Declaration`, its address-to-name encoding (`keyName`,
  injective) and its record-by-record specification;
* `Ix/Kernel/ConLeche/{PinData,NatOpPinData,Prelude}.lean`: the committed pin
  table, Nat-operation pins and Ixon prelude, generated from the compiled
  Init's records;
* `Ix.Kernel.ConLecheFold` (`Installed`, `Values`): installation and
  definition values of the fold, used by the public theorems;
* `Ix.Kernel.ConstRef` (`Ref`), the decoded-record store
  (`Ix.Kernel.Ingress`, `Ingress/Records.lean`), bounded search outcomes
  (`Search`), and the projection-record writer (`Ix.Kernel.Egress`,
  `Egress/Projection.lean`) that projection reconstruction runs;
* `Ix.Kernel.Audit`: the certified gate's manifest and audits.

The certified API is `Ix.Ixon.Admission.checkBytes`; its public theorems
(model existence over `ConLeche.Model`, no proof of the pinned `False`,
fidelity, resources) are in `Ix.Ixon.Consistency` and
`Ix.Ixon.ConLecheConsistency`.

The intrinsic proof-carrying kernel that this module exported through L5
(`Ix.Kernel.check`, `checkDecls`, `checkEnv`, the `Ix.Kernel.Model` set model
and `Ix.Kernel.Consistency`) was retired at L6; its final state is
integration head `tmxpopss` (`plans/ix-kernel-con-leche-port-v4.md`,
section 6).

Roadmap: `plans/ix-certified-roadmap.md`. -/
