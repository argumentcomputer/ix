# The Lean core resource profile (Lean 4.34.1, Ixon v4), for
#   ix compile --profile profiles/lean-core.profile ...
#
# Every entry is an explicit assumption bound into the profile address that
# `ix compile` prints. Entries naming constants outside the compiled closure
# are omitted. See docs/resource-checking.md, "Profiles, claims, and
# consumers".
#
# Named assumptions (docs/resource-checking.md, "Named assumptions"); a
# consumer relying on admission under this profile must establish them:
# - A fully applied constructor, a nullary constructor and a literal are
#   fresh: the checker treats each evaluation as a new, unique object. The
#   consumer must allocate it anew at each evaluation that reaches a unique
#   position -- never replace it by a shared static object (no hoisting,
#   CSE, float-out or closed-term extraction of such a value), or else keep
#   the run-time exclusivity check before any in-place update of it.
# - The linearity of a shareable immediate has no run-time meaning: a `1` or
#   `&` contract on a Nat, Bool, String, Char or UIntN value bounds how often
#   the program names it, not a resource the consumer relies on. (Uniqueness
#   is not covered: a closure that moves a captured immediate is one-shot.)
# - A field is an owned reference: a value extracted by a projection or a
#   case split stays valid after its aggregate is dropped (the consumer takes
#   its own reference, as Lean's runtime does). The checker ties a field to
#   its aggregate only until the field is consumed.
# And the behaviour this profile states below: choices by need; case splits
# and case definitions without closures and without dead induction
# hypotheses; every other call strict; each definition the equation sidecar
# lists under `resourceChecked` run by its unfolding equation.

# The standard profile: Nat and String literal types; Nat, Bool and String
# are shareable immediates.
standard

# More scalar immediates: their values hold no resource.
shareable Char
shareable UInt8
shareable UInt16
shareable UInt32
shareable UInt64

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
