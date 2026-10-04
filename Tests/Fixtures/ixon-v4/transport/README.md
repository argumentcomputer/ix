# Source-contract transport admission fixtures

Both Lean and Rust must run their full combined validators on these exact
IXON v4 bytes and profile bytes. A resource-only diagnostic is insufficient.
The bridge negative must reject; the other three cases must accept.

Closures were exported with the verified frozen producer `cb68d94c`, Lean
4.34.1, using `compile --no-build --consts --anon` and the baseline core
profile. This older producer intentionally permits the negative term; these
fixtures exercise the strengthened validator's behavior on committed input,
not an expectation that a current compiler will emit a rejected closure.
The source files preserve the original elaborated contract syntax.

The bridge roots were selected independently as
`IndependentR21EqBridge.rejectedWitness` and
`IndependentR21EqBridge.acceptedWitness`; both use the original 100,000-step
profile. The bad function returns closed shared static data under a unique
result promise. The good function allocates a fresh cons cell from its input.
The proof converts `True` into `Nonempty` through an equality helper, ensuring
that canonical-Eq result shape alone cannot authorize an unchecked witness.

Each recursion source was exported independently with root `entry` and
`--equations`. Its checked equation binding and complete theorem closure are
in the profile/input. These two profiles explicitly increase only the step
limit from 100,000 to 300,000; depth and all policy bindings are unchanged.
The old 100,000-step profiles decline by budget. The pinned 300,000-step
positive is a cost regression for the supported annotated recursion fragment,
not a change to the public `Limits` default or the consumer's final profile.

Profile addresses are asserted independently in the Lean and Rust loaders.
`sha256.txt` records the exact fixture/source files. Source reproduction and
artifact verification are distinct: changes to producer elaboration can
change exported addresses and require an explicit fixture review.
