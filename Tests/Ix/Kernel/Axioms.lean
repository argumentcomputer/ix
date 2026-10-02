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
of `Ix.Kernel.model_exists`): if a `sorry`, a new axiom or a
stray `Classical`-adjacent import ever enters one of these proof terms, the
message changes and the build fails.

`#print axioms` is blind to compiler escapes (`@[implemented_by]`,
`@[computed_field]`); `kernel-trust-surface`
(`Tests/Ix/Kernel/TrustSurface.lean`, derived from upstream's
`tests/trust-surface.sh`) scans `Ix/Kernel` for those.

Of upstream's twenty roots, three are not here: the NDJSON corollary
`no_False_declaration` (the NDJSON frontend is not imported), and
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
