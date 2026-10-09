# The plain-data Lean core resource profile (Lean 4.34.1, Ixon v4), for
#   ix compile --profile profiles/lean-core-plain.profile ...
#
# The Lean core profile's evaluation rules with OxCaml's division of the
# usage axis (docs/resource-checking.md, "Usage crossing on plain data"):
# usage contracts (`1` linear, `&` affine) are enforced on functions, on type
# variables and on types without a visible block, and cross on plain data --
# an inductive whose constructors all carry default contracts (`Nat`,
# `String`, `Bool`, `Char`, `UIntN`, `List`, `Option`, `Prod`, `Subtype`,
# `Decidable`, class dictionaries, inductives with function fields, ...). On
# a crossing type both bounds of a written `1`/`&` are dropped (OxCaml has no
# relevance axis) and `ix compile` reports the binder. Ownership (`!`),
# locality (`~`), borrows, freeze, the one-shot closure rule (a closure that
# moves a capture is one-shot) and case-split field views are unchanged, as
# under profiles/lean-core-strict.profile; `0` (erased) inputs and proof
# arguments keep their zero demand. No type is `shareable`: Nat, String,
# Bool, Char and UInt8-UInt64 are visible blocks in Ixon v4, so they cross
# as plain data and are owned like any other value.
#
# Every entry is an explicit assumption bound into the profile address that
# `ix compile` prints. Entries naming constants outside the compiled closure
# are omitted. See docs/resource-checking.md, "Profiles, claims, and
# consumers".
#
# Named assumptions a consumer relying on admission under this profile must
# establish (docs/resource-checking.md, "Named assumptions"):
# - Usage on plain data carries no consumer obligation: a `1` or `&`
#   contract on a value of a crossing type bounds nothing the consumer may
#   rely on (no elided drop or increment, no move-only representation, no
#   single-use capability); ownership on it is still checked and may be
#   relied on. A data type that does represent a capability must be opted
#   out with `linear NAME`.
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
# types.
literals

# Usage crosses on plain data. (A capability token type would be opted out
# here with `linear NAME`; Lean's core library has none.)
crossing plain

# Selection primitives: strict leading arguments, then two alternatives
# evaluated by need (the consumer compiles them as `macro_inline`). `dite`
# supplies a proof to each alternative.
choice ite
choice dite
choice cond

# Case splits: a recursor application whose minor premises ignore their
# induction hypotheses is a case on its major premise. `ix compile` binds
# every `casesOn` and matcher of the closure as a case definition (generated
# `case` lines; this file may not contain any); such a definition is
# unfolded, its alternatives taken by need. Every other application -- a
# beta-redex, or a call of any other definition however match-shaped --
# evaluates each argument exactly once, before the body. The consumer must
# compile case splits and case definitions without closures and without
# computing dead induction hypotheses, and every other call strictly.
cases

# Library readers: they inspect their input and return a fresh unrestricted
# value, so a local (`~`) input may reach them.
interface List.length _ ~
interface Array.size _ ~
interface String.length ~
