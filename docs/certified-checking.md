# Certified source and claim checking

Ix contains certified source and claim adapters under
`Ix.Certified`, with checker wrappers in `Ix.Kernel.Certified` and
`Ix.Kernel.CertifiedClaims`. Successful validation constructs receipts that
connect the authenticated Ixon source to the set model in `Ix.Theory`.
The maintained implementation and its regression evidence are local to this
repository.

The certificate profile checks a specific collection of declaration forms
and logical schemas. Witness search supplies proposals; the certified
validator checks every proposal before reporting success. Unsupported forms,
missing models and unsuccessful searches decline. These commands provide an
explicit entry point for that profile.

## Commands

Build the source and claim commands:

```sh
lake build --wfail certified-check certified-claim-check
```

Source checking takes a lazy `.ixe` file and a JSON request that selects the
target or subjects, primitive addresses, source objects and natural values:

```sh
.lake/build/bin/certified-check proof SOURCE.ixe REQUEST.json
.lake/build/bin/certified-check store SOURCE.ixe REQUEST.json
```

The request fields are `target`, `subjects`, `objects`, `naturals`,
`falseType`, `falseElim`, nullable `natType`, and optional `models`. Addresses
are 32-byte hexadecimal strings. Model hints select earlier source
declarations; the validator checks their types and complete source equations.
The request parser is defined in
[`Command.lean`](../Ix/Certified/Command.lean).

For a runnable source example:

```sh
lake build certified-source-tests
.lake/build/bin/certified-source-tests /tmp/ix-certified-examples
.lake/build/bin/certified-check proof \
  /tmp/ix-certified-examples/identity/source.ixe \
  /tmp/ix-certified-examples/identity/request.json
```

Claim checking also takes the exact serialized envelope. The JSON request
selects its expected address and supplies logical, membership or revelation
witness hints:

```sh
.lake/build/bin/certified-claim-check SOURCE.ixe ENVELOPE.bin REQUEST.json
```

The envelope binds the claim, primitive profile, logical-axiom manifest and
protocol versions. The current checker version is **2**; format, codec,
policy and aggregation versions are **1**. Exact decoding, canonical
re-encoding, the expected content address and all versions are checked.
Trailing bytes and older checker envelopes reject. See
[`Envelope.lean`](../Ix/Certified/Envelope.lean) and
[`ClaimCommand.lean`](../Ix/Certified/ClaimCommand.lean).

Both commands currently use fuel 6,400. Success exits 0 and prints a JSON
acceptance record; a rejected request exits 1. Fuel or witness-search failure
can reject a valid source, so success and completeness are separate
properties.

## Semantic contract

`ClaimCommand.run_meaning` proves that successful pure command execution
produces a receipt for the exact envelope bytes and establishes
`SemanticClaimMeaning`. For logical claims, the receipt preserves the
original source statements and constructs a compatible interpretation while
preserving the declared frontier. Model companions for mutual and nested
inductives must already have been checked; their complete recursor equations
are validated before the new source package is admitted.

For a logical receipt with no structural frontier,
`LogicalReceipt.closed_subject_meaning` constructs its model.
`LogicalReceipt.no_False` then rules out a checked subject whose type is the
profile's false proposition, under the explicit `[SetTheory V]` hypothesis.
The admitted logical schemas have realizations in that model. A closed
structural frontier does not imply an empty logical-axiom manifest; the
manifest records admitted source axioms under the enforced policy.

Membership and revelation establish their respective structural meanings.
Evaluation claims are excluded from this semantic profile. The relevant
definitions and statements are in
[`ClaimAccept.lean`](../Ix/Certified/ClaimAccept.lean),
[`ClaimMeaning.lean`](../Ix/Certified/ClaimMeaning.lean) and
[`LogicalPolicy.lean`](../Ix/Theory/Certified/LogicalPolicy.lean).

The mathematical contract concerns the Lean functions. Native Lean
execution, filesystem loading and the BLAKE3 foreign interface remain
execution boundaries. Full production-checker refinement and execution
of this certification inside an authenticated Aiur proof remain separate
obligations described in
[`kernel-verification.md`](kernel-verification.md).

## Audits and regression evidence

Run the complete local gate with:

```sh
lake run check-certified
```

The gate builds the adapters, audits and test programs with warnings treated
as errors. It compares the exact foundation report, checks the frozen source
archive and maintained import identities, runs six native host test programs,
and exercises the actual source and claim executables on all three CLI
corpora. CI runs the same gate.

The combined audit covers **86 distinct roots**, **74 premise definitions or
constructor types**, **9,682 logical declarations** and **10,957 declarations
including runtime dependencies**. The five historical component audits
remain independently callable. All 90 historical root occurrences and 75
premise occurrences retain their statements after namespace qualification is
normalized. The exact report is
[`Tests/Certified/foundation.txt`](../Tests/Certified/foundation.txt).

The audit traverses full checked types, bodies and inductive constructors.
It checks exact axiom sets and follows compiler recursion workers and
executable replacements transitively, including private constants. These
roots use only `propext`, `Classical.choice` and `Quot.sound`. The runtime
inventory records five BLAKE3 foreign operations and 130 recursion workers
with safe source definitions; it permits no partial opaque worker source or
executable replacement.

This stronger traversal exposed a native-evaluation axiom that the historical
imported axiom summaries missed. It came from the BLAKE3 helper's 32-byte
output bound. `Address.blake3` now supplies a kernel-checked proof of that
bound. The wrapper is definitionally equal to the former hash operation,
and generated source/envelope corpora are unchanged.
The affected kernel and source-compiler audits also remove this dependency.

| Actual command corpus | Fixtures | Accepted | Rejected |
| --- | ---: | ---: | ---: |
| Source proof/store | 42 source fixtures | 84 | 562 |
| Versioned claims | 1,578 claim fixtures | 584 | 5,454 |
| Modeled source and claims | 44 source and 74 claim fixtures | 30 | 540 |

The native modeled tests additionally cover 29 source mutations with accepted
controls, 42 forged witnesses and nine malformed mutual inputs. The other
native suites cover source fidelity, lazy loading, cold/warm caches,
rollback, claim cycles, shared dependencies, membership and revelation.

All generated source and envelope bytes and CLI process outputs are
compared against the frozen adapter evidence. Host reports preserve every
non-VM field; only `pilotDeclined` and `pilotDeclines` are projected away
from the three historical reports that mixed host and VM checks. The VM
pilot, packet encoder and VM execution suite are archived for a later change.
CLI JSON requests and aggregate records are compared as parsed values because
the maintained Lean driver formats JSON differently. The archive, source mappings, licenses and
historical reproduction limits are documented in
[`Tests/Fixtures/Certified`](../Tests/Fixtures/Certified/README.md). The archive
recovers the selected adapter sources and fixtures; it does not include the
complete historical Ix base checkout.
