/-
Ported from con-leche (ae0c0c4e4ce6a0081648aff03fe9c39d002c4526).
Source: ConLeche/MainTheorem.lean
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
Changes: only `model_exists` is kept; the NDJSON corollary
`no_False_declaration` and the imports it needs (`ConLeche.Accepts`,
`ConLeche.Frontend.Prelude`, `ConLeche.Verify.Cached.StreamThm`,
`ConLeche.Verify.Frontend.{Prepare,FileFalse}`) are dropped, the module
docstring is cut to match, and this header is added. The statement and
proof of `model_exists` are upstream's, token for token.
-/
module

import ConLeche.Verify.Cached.MainC
public import ConLeche.Denotes
public import ConLeche.Cached.Installed
import ConLeche.Model.Denotes
public section

/-!
# The main theorem

What the checker accepts has a model.  That theorem is all this file
holds.  (Upstream's file also proves the main corollary over the NDJSON
frontend; Ix reads Ixon only, so the frontend and the corollary are not
imported.)  The reading of terms and the notion of model — and
`Denotes_functional`, which says a term has at most one denotation — are
in `ConLeche/Denotes.lean`.

* `checkDecls` (`ConLeche/Cached/Installed.lean`) is the declaration
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
  pins, and a stream that declares them differently is rejected.
* `pins` is the list of `Nat.div`/`Nat.mod` pin variants the fold's
  install gate tries (task #304).  The statement is for EVERY list:
  consistency does not depend on it — under the empty list every
  stream that declares `Nat.div` simply declines, and under any other
  what an accept establishes is the certificates' verdict in the
  accepted environment, which is all the model tier reads.
* `SetTheory V` is the set theory the model lives in; the proof works
  for any `V` implementing that interface.

The axioms used are exactly `propext`, `Classical.choice` and
`Quot.sound` (`Tests/ConLeche/Axioms.lean`).
-/

namespace ConLeche

open SetTheory
open ConLeche.Cached (checkDecls)

universe w

/-- **The main theorem.**  Every environment the checker accepts has a
model in every set theory — at every `Nat.div`/`Nat.mod` pin list, so
consistency does not depend on which variants the install gate is
handed (the empty list included: under it every stream that declares
`Nat.div` declines).  The shipped binary runs the fold at
`natOpPinSets`. -/
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (accepted : checkDecls .verified pins ds = .ok env) :
    Nonempty (Model V env) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  exact ⟨Model.Model.ofEnvModelM m⟩

end ConLeche
