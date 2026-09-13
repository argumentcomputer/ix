# Consistency model

`Ix.Theory` contains Ix's set-theoretic consistency model, its certified acceptance
interface, and certificate construction. Build it with `lake build IxTheory`;
run the selected regression tests, provenance check, and exact foundation
audit with `lake run check-theory`.

`Ix.Theory.Certified.accepted_has_model` constructs a model for accepted
declarations. `accepted_proof_sound` and `no_proof_of_False` give the corresponding
semantic and consistency results. These theorems assume a type `V` equipped
with `Ix.Theory.Model.SetTheory V`: set operations and laws together with a
countable tower of Grothendieck universes. The separate
[`Models/SetTheory`](../Models/SetTheory/README.md) package constructs this
structure on Mathlib's `ZFSet` from a strictly increasing countable sequence
of strongly inaccessible cardinals. Its `carneiro_implies_ix` theorem retains
that large-cardinal hypothesis explicitly and passes an axiom guard for
`propext`, `Classical.choice`, and `Quot.sound`. User-supplied logical axioms and
open frontiers retain their stated model hypotheses.

The [certified host adapters](certified-checking.md) connect authenticated
serialized Ixon to model admission. Separately, a production `checkEnvAnon`
[fragment](kernel-verification.md#production-environment-fragment) for
monomorphic aliases and closed universe terms extends every model of its
source axioms under explicit execution witnesses. Full checker consistency
and compiler/backend refinement remain open.

`Ix.Theory.Named` retains the local name-indexed specification and proof
support needed by the existing kernel and compiler verification. It shares
`Ix.Theory.VLevel`; its expression calculus remains separate from the store
references and annotated semantics of the set model. The `IxTheory` build and
foundation import graph exclude this auxiliary development.

The foundation audit freezes 145 named roots, their types and dependencies,
the fields of the set-theory assumption, and the compiler-generated recursion
workers. It rejects proof holes and unapproved axioms, native implementations,
and mathematical imports from the checker, compiler, test harnesses, or older
metatheory. Its exact report is `Tests/Theory/certified-foundation.txt`.
The axiom checks read checked declaration types, bodies, and constructor fields
directly, including the full graph of every declaration in the mathematical
import boundary.

## Provenance and scope

The port contains 120 selected source modules and a certified umbrella, from
the Lean4Ix working tree on 2026-09-11,
based on commit `ab42e79e2a4e2615a3ca6ef983d510f374057a38`. The new model included
uncommitted files, so that revision alone is insufficient to identify the
input. `Tests/Theory/ImportManifest.lean` records each selected source path and
SHA-256. Namespace changes move `Lean4Ix` to `Ix.Theory` and flatten the former
`Lean4Ix.Theory` syntax helpers.

The import includes the exact dependencies of the certified interface and
certificate builders. The old full theory umbrella, generators, conjecture
frontier, and harness are excluded. Matching model tests live in `Tests/Theory`.
Tests that formerly invoked the old generators use frozen constructor and
recursor data extracted from their upstream compiled test fixtures.

The model's 20 con-leche foundation files derive from revision
`86cd20a65660d757cedc81561a44579099b565d0`. Their upstream and intermediate hashes,
ported content hashes, and notices are retained and checked. Imported license
and notice texts are under `Ix/Theory`; `PORTING.md` explains their scope.

The exact report records each root's checked type, axioms, and dependencies.
For example, `Modeled.CheckedCompanions.fixed_old` and
`Modeled.assignment_agrees` use `propext`, `Classical.choice`, and `Quot.sound`.
