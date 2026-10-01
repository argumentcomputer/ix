/-
Ported from con-leche at ae0c0c4e4ce6a0081648aff03fe9c39d002c4526.
Source: tests/ConLecheTests/Axioms.lean
Transformations: namespace `ConLecheTests.Axioms` renamed to
`Tests.Ix.Kernel.Axioms`; the imports of `ConLeche.Verify.Cached.StreamConsts`
and `ConLeche.Verify.Cached.StreamThm` and the guards on
`ConLeche.no_False_declaration`, `ConLeche.no_False_theorem_accepted` and
`ConLeche.Cached.checkDecls_consts` are dropped (their modules are outside
the imported closure of `model_exists`); the docstrings are cut to match;
the names of the remaining guards go through the vendoring rewrite of
`scripts/vendor-conleche.py` (`ConLeche` → `Ix.Kernel`), as do the modules
they import; this header is added. The other seventeen guards are
upstream's, verbatim up to the rewrite.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/
module

public import Ix.Kernel.MainTheorem
public import Ix.Kernel.Verify.Cached.MainC
public import Ix.Kernel.Model.Fold
public import Ix.Kernel.Model.Capstone
public section

/-!
# The axiom pin for the imported con-leche closure

Con-leche's headline is that its consistency theorems stand on nothing but
Lean's three standard axioms, `[propext, Classical.choice, Quot.sound]`.
This module pins that on the roots of the closure Ix imports (the closure
of `Ix.Kernel.model_exists`, plan v4 L1-L3): if a `sorry`, a new axiom or a
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

namespace Tests.Ix.Kernel.Axioms

/--
info: 'Ix.Kernel.model_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.model_exists

/--
info: 'Ix.Kernel.Denotes_functional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Denotes_functional

/--
info: 'Ix.Kernel.Cached.no_proof_of_False_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.no_proof_of_False_cached

/--
info: 'Ix.Kernel.Cached.no_proof_of_Empty_cached' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.no_proof_of_Empty_cached

/--
info: 'Ix.Kernel.Cached.checkDecls_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.checkDecls_sound

/--
info: 'Ix.Kernel.Cached.fullyChecked_checkDecls' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.fullyChecked_checkDecls

/--
info: 'Ix.Kernel.Cached.checkDecls_fullyChecked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.checkDecls_fullyChecked

/--
info: 'Ix.Kernel.Cached.no_proof_of_False_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.no_proof_of_False_checked

/--
info: 'Ix.Kernel.Cached.no_proof_of_Empty_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.no_proof_of_Empty_checked

/--
info: 'Ix.Kernel.Cached.fullyChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Cached.fullyChecked_sound

/--
info: 'Ix.Kernel.Model.no_proof_of_False_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Model.no_proof_of_False_pure

/--
info: 'Ix.Kernel.Model.no_proof_of_Empty_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Model.no_proof_of_Empty_pure

/--
info: 'Ix.Kernel.Model.no_proof_of_Empty_pure_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Model.no_proof_of_Empty_pure_of

/--
info: 'Ix.Kernel.Model.no_constant_of_False' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Model.no_constant_of_False

/--
info: 'Ix.Kernel.Model.no_constant_of_Empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Model.no_constant_of_Empty

/--
info: 'Ix.Kernel.Model.no_constant_of_emptyPin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Model.no_constant_of_emptyPin

/--
info: 'Ix.Kernel.Expr.beq_eq_beqMemo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Ix.Kernel.Expr.beq_eq_beqMemo

end Tests.Ix.Kernel.Axioms
