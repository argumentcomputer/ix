module

import IxC.Kernel.Verify.Cached.MainC
public import IxC.Kernel.Denotes
public import IxC.Kernel.Cached.Installed
import IxC.Kernel.Model.Denotes
public section

/-!
# The main theorem

What the checker accepts has a model.  That theorem is all this file
holds.  (Upstream's file also proves the main corollary over the NDJSON
frontend; Ix reads Ixon only, so the frontend and the corollary are not
imported.)  The reading of terms and the notion of model — and
`Denotes_functional`, which says a term has at most one denotation — are
in `IxC/Kernel/Denotes.lean`.

* `checkDecls` (`IxC/Kernel/Cached/Installed.lean`) is the declaration
  fold: it installs every declaration — a definition, theorem or opaque
  annotated and pushed with its check recorded, everything else checked
  in full as it is installed — and then checks every recorded
  declaration against the prefix of the environment it was installed
  at.
* `Declaration` is a declaration record, and the records travel as an
  `Array` of them — what the fold folds; `Env` is the environment the
  checker builds; `env.consts` are the constants it accepted;
  `.verified` is the default mode.
* `False` and `Eq` are built in: the checker installs them from its own
  specifications (`Role.spec`), and a stream that declares them
  differently is rejected.
* `ev` is the role table's evidence the operations' install gates read
  (`Evidences`, `IxC/Kernel/Roles.lean`).  The statement is for EVERY
  value: consistency does not depend on it — with no evidence every
  stream that declares a certified `Nat` operation simply declines, and
  with any other what an accept establishes is the certificates' and
  recurrences' verdicts in the accepted environment, which is all the
  model tier reads.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`Tests/Ix/Kernel/Axioms.lean`).
-/

namespace Ix.Kernel

open SetTheory
open Ix.Kernel.Cached (checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory — at every role-table evidence `ev`, so
consistency does not depend on the evidence the install gates are
handed (none included: then every stream that declares a certified
`Nat` operation declines). It is stated at the certified modes
(`Mode.Certified`: `.anon`, the Ixon entry's, and `.source`, the Lean
ingress's); `.meta`'s verdicts are never reported (IXC-PLAN §11). -/
theorem model_exists {md : Mode} [md.Certified] (V : Type w) [SetTheory V]
    (ev : Evidences md) (ds : Array (Declaration md)) (env : Env md)
    (accepted : checkDecls .verified ev ds = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

end Ix.Kernel
