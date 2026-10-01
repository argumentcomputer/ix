/-
Ported from con-leche at ae0c0c4e4ce6a0081648aff03fe9c39d002c4526.
Source: tests/ConLecheTests/Axioms.lean
Transformations: namespace `ConLecheTests.Axioms` renamed to
`Tests.ConLeche.Axioms`; the imports of `ConLeche.Verify.Cached.StreamConsts`
and `ConLeche.Verify.Cached.StreamThm` and the guards on
`ConLeche.no_False_declaration`, `ConLeche.no_False_theorem_accepted` and
`ConLeche.Cached.checkDecls_consts` are dropped (their modules are outside
the imported closure of `model_exists`); the docstrings are cut to match;
this header is added. The other seventeen guards are upstream's, verbatim.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/
module

public import ConLeche.MainTheorem
public import ConLeche.Verify.Cached.MainC
public import ConLeche.Model.Fold
public import ConLeche.Model.Capstone
public section

/-!
# The axiom pin for the imported con-leche closure

Con-leche's headline is that its consistency theorems stand on nothing but
Lean's three standard axioms, `[propext, Classical.choice, Quot.sound]`.
This module pins that on the roots of the closure Ix imports (the closure
of `ConLeche.model_exists`, plan v4 L1-L3): if a `sorry`, a new axiom or a
stray `Classical`-adjacent import ever enters one of these proof terms, the
message changes and the build fails.

`#print axioms` is blind to compiler escapes (`@[implemented_by]`,
`@[computed_field]`); upstream pairs this module with
`tests/trust-surface.sh`, which Ix ports later (plan v4, D-trust row 25).

Of upstream's twenty roots, three are not here: the NDJSON corollary
`no_False_declaration` (the frontend is not imported, plan v4 D6), and
`no_False_theorem_accepted` and `Cached.checkDecls_consts`, whose modules
(`Verify/Cached/StreamThm`, `Verify/Cached/StreamConsts`) are outside the
closure of `model_exists`.
-/

namespace Tests.ConLeche.Axioms

/--
info: 'ConLeche.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.model_exists

/--
info: 'ConLeche.Denotes_functional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Denotes_functional

/--
info: 'ConLeche.Cached.no_proof_of_False_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_False_cached

/--
info: 'ConLeche.Cached.no_proof_of_Empty_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_Empty_cached

/--
info: 'ConLeche.Cached.checkDecls_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_sound

/--
info: 'ConLeche.Cached.fullyChecked_checkDecls' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.fullyChecked_checkDecls

/--
info: 'ConLeche.Cached.checkDecls_fullyChecked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.checkDecls_fullyChecked

/--
info: 'ConLeche.Cached.no_proof_of_False_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_False_checked

/--
info: 'ConLeche.Cached.no_proof_of_Empty_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.no_proof_of_Empty_checked

/--
info: 'ConLeche.Cached.fullyChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Cached.fullyChecked_sound

/--
info: 'ConLeche.Model.no_proof_of_False_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_False_pure

/--
info: 'ConLeche.Model.no_proof_of_Empty_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_Empty_pure

/--
info: 'ConLeche.Model.no_proof_of_Empty_pure_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_proof_of_Empty_pure_of

/--
info: 'ConLeche.Model.no_constant_of_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_False

/--
info: 'ConLeche.Model.no_constant_of_Empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_Empty

/--
info: 'ConLeche.Model.no_constant_of_emptyPin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Model.no_constant_of_emptyPin

/--
info: 'ConLeche.Expr.beq_eq_beqMemo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConLeche.Expr.beq_eq_beqMemo

end Tests.ConLeche.Axioms
