# The strict Lean core resource profile (Lean 4.34.1, Ixon v4), for
#   ix compile --profile profiles/lean-core-strict.profile ...
#
# The Lean core profile without shareable types: usage contracts never cross
# a call or closure boundary. A `1` (linear) or `&` (affine) value is
# consumed exactly / at most once on every type, Nat, Bool, String, Char and
# the UIntN included, as in Idris 2 and Linear Haskell: passing it to a
# many-use callee, or capturing it in a reusable closure, is a rejection.
# This profile therefore does not rely on the immediate-linearity assumption
# (docs/resource-checking.md, "Named assumptions"), which the standard and
# core profiles do. `0` (erased) inputs and proof arguments keep their zero
# demand: they are erased computation, not usage crossing.
#
# Every entry is an explicit assumption bound into the profile address that
# `ix compile` prints. Entries naming constants outside the compiled closure
# are omitted. See docs/resource-checking.md, "Profiles, claims, and
# consumers".
#
# Named assumptions a consumer relying on admission under this profile must
# establish (docs/resource-checking.md, "Named assumptions"):
# - A fresh construction is a new object. Literals and closed constructions
#   (`[1, 2, 3]`) are shared static data and need no assumption; a
#   constructor application with a run-time field that depends on a run-time
#   local (`x :: acc`) is treated as a new, unique object at each
#   evaluation. The consumer must allocate it anew at each evaluation that
#   reaches a unique position -- no CSE, float-out, or extraction after
#   inlining of such a value -- and keep it a cell of its own (the checker
#   counts a one-field constructor as unboxed only for single-constructor
#   types), or else keep the run-time exclusivity check before any in-place
#   update of it.
# - A constructor without run-time fields (`Nat.zero`, `[]`, `none`) is an
#   immediate, unique: the consumer represents it without a heap object (a
#   scalar, as Lean and Compilatr do), never as a shared static object.
# - A field is an owned reference: a value extracted by a projection or a
#   case split stays valid after its aggregate is dropped (the consumer takes
#   its own reference, as Lean's runtime does). The checker ties a field to
#   its aggregate only until the field is consumed.
# And the behaviour this profile states below: choices by need; case splits
# and case definitions without closures and without dead induction
# hypotheses; every other call strict; each definition the equation sidecar
# lists under `resourceChecked` run by its bound equation's right-hand side,
# fetched by address (`ix compile` refuses annotated recursion that is not
# checked through its equation; `ix check-equations` re-verifies the list).

# The standard profile's Nat and String literal types, without its shareable
# types (`standard` would add Nat, Bool and String as shareable).
literals

# Selection primitives: strict leading arguments, then two alternatives
# evaluated by need (the consumer compiles them as `macro_inline`). `dite`
# supplies a proof to each alternative. This is about evaluation, not usage
# crossing: a linear value used in only one alternative is still rejected.
choice ite
choice dite
choice cond

# Case splits: a recursor application whose minor premises ignore their
# induction hypotheses is a case on its major premise. `ix compile` binds
# every `casesOn` and matcher of the closure that Lean verifiably generated
# (not a definition merely tagged as one) as a case definition (generated
# `case` lines; this file may not contain any); such a definition is
# unfolded, its alternatives taken by need. Every other application -- a
# beta-redex, or a call of any other definition however match-shaped --
# evaluates each argument exactly once, before the body. The consumer must
# compile case splits and case definitions without closures and without
# computing dead induction hypotheses, and every other call strictly; it
# takes the case definitions from this profile, by address, with by-need
# positions derived from their bound bodies (docs/resource-checking.md,
# consumer obligation (e)).
cases

# Library readers: they inspect their input and return a fresh unrestricted
# value, so a local (`~`) input may reach them.
interface List.length _ ~
interface Array.size _ ~
interface String.length ~
