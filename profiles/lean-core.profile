# The Lean core resource profile (Lean 4.34, Ixon v3), for
#   ix compile --profile profiles/lean-core.profile ...
#
# Every entry is an explicit assumption bound into the profile address that
# `ix compile` prints. Entries naming constants outside the compiled closure
# are omitted. See docs/resource-checking.md, "Profiles, claims, and
# consumers".

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
# induction hypotheses is a case on its major premise; `casesOn` and matchers
# that only wrap such a split are unfolded, and a beta-redex binds its
# argument. The consumer compiles these without closures.
cases

# Library readers: they inspect their input and return a fresh unrestricted
# value, so a local (`~`) input may reach them.
interface List.length _ ~
interface Array.size _ ~
interface String.length ~
