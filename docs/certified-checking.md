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

Source checking takes a lazy `.ixe` file and a typed request that selects the
target or subjects, primitive addresses, source objects and natural values.
Binary Ixon is the default input format:

```sh
.lake/build/bin/certified-check proof SOURCE.ixe REQUEST.ix
.lake/build/bin/certified-check store SOURCE.ixe REQUEST.ix
.lake/build/bin/certified-claim-check SOURCE.ixe ENVELOPE.ix REQUEST.ix
```

Use `--request-format text` for a readable `.ixon` request. Claim checking
selects the request and envelope encodings independently:

```sh
.lake/build/bin/certified-check --request-format text proof SOURCE.ixe REQUEST.ixon
.lake/build/bin/certified-check --request-format text store SOURCE.ixe REQUEST.ixon
.lake/build/bin/certified-claim-check \
  --request-format text --envelope-format text \
  SOURCE.ixe ENVELOPE.ixon REQUEST.ixon
.lake/build/bin/certified-claim-check \
  --request-format text --envelope-format binary \
  SOURCE.ixe ENVELOPE.ix REQUEST.ixon
```

Both flags accept `binary` or `text`, including `--request-format=text`
syntax. The selected flag determines the encoding independently of the file
suffix. `SOURCE.ixe` always contains a serialized Ixon environment.

For runnable examples in both encodings:

```sh
lake build certified-input-tests
.lake/build/bin/certified-input-tests --examples /tmp/ix-certified-examples
.lake/build/bin/certified-check --request-format text proof \
  /tmp/ix-certified-examples/source/source.ixe \
  /tmp/ix-certified-examples/source/request.ixon
.lake/build/bin/certified-claim-check --request-format text --envelope-format binary \
  /tmp/ix-certified-examples/claim/source.ixe \
  /tmp/ix-certified-examples/claim/envelope.ix \
  /tmp/ix-certified-examples/claim/request.ixon
```

Both commands use fuel 6,400. Success exits 0 and prints a JSON acceptance
record; rejection or a file-reading error exits 1, and invalid command-line
arguments exit 2. Fuel or witness-search failure can reject a valid source,
so success and completeness are separate properties.

### Lean API

Import `Ix.Certified` to construct the actual Lean values:

| Value | Type |
| --- | --- |
| Source proof/store request | `Ix.Certified.Command.Request` |
| Claim request and witness hints | `Ix.Certified.ClaimCommand.Request` |
| Public claim envelope | `Ix.Certified.Envelope` |

Source requests contain `profile`, `target`, `subjects`, `selection`, and
`models`. The profile pins `falseType`, `falseElim`, and optional `natType`;
the selection lists object and natural-value addresses. Model hints select
earlier source declarations whose types and complete equations the validator
checks. Claim requests contain the expected envelope `address` and a typed
`.logical`, `.contains`, or `.reveal` hint.

Each of the three types provides `toIxon`/`ofIxon` and `toText`/`ofText`.
They also have `Ixon.Serialize` instances. Use the named `ofIxon` decoders
when reading a complete input: they reject trailing and noncanonical bytes.
For example, a Lean program can export a source request without JSON:

```lean
import Ix.Certified

def saveRequest (directory : System.FilePath)
    (request : Ix.Certified.Command.Request) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "request.ix") request.toIxon
  IO.FS.writeFile (directory / "request.ixon") request.toText
```

`Command.run` and `ClaimCommand.run` also accept these typed requests directly
when the source environment is already loaded. Lean authoring supports normal
record syntax and computation; the exported `.ixon` file contains the resulting
data value.

### Input representations

Text inputs use the existing Ixon parser and printer. Each file contains one
safe monomorphic `def` or one annotated main expression. The reader checks
the type annotation, constructor names, argument counts, and literal values.
Lists, options, claims, model hints, and revelation fields use their actual
Lean constructors, with explicit type arguments as required by Ixon syntax.
`Ix.Certified.Text.address!` and `bytes!` provide hexadecimal literals.
The data reader accepts constructor expressions and checks their contents;
imports, extra declarations, and arbitrary computation are rejected.

Binary requests have an `IX-CERTIFIED-REQUEST` header, request-format version
1, and a distinct source/claim tag. Addresses occupy 32 bytes; list and byte
lengths use Ixon `Tag0` encoding, and options use tags 0 and 1. Complete binary
decoding requires canonical re-encoding. Request decoding is capped at 1 MiB;
text additionally uses the standard Ixon parser's node and depth limits.
See [`RequestCodec.lean`](../Ix/Certified/RequestCodec.lean),
[`TextCodec.lean`](../Ix/Certified/TextCodec.lean), and
[`InputText.lean`](../Ix/Certified/InputText.lean).

Claim envelopes retain their existing canonical Ixon representation. With
binary input, authentication checks the exact bytes read from the file.
With text input, the authenticated object is the parsed envelope's canonical
binary encoding. The request's expected address must match the BLAKE3 hash
of those bytes. Text formatting therefore does not change the claim address.

The envelope binds the claim, primitive profile, logical-axiom manifest and
protocol versions. The current checker version is **2**; format, codec,
policy and aggregation versions are **1**. Exact decoding, canonical
re-encoding, the expected content address and all versions are checked.
Trailing bytes and older checker envelopes reject. See
[`Envelope.lean`](../Ix/Certified/Envelope.lean) and
[`ClaimCommand.lean`](../Ix/Certified/ClaimCommand.lean).

Existing JSON requests remain available with `--request-format json` for
compatibility. The frozen CLI corpus selects this mode explicitly. All
formats pass through the same witness search and certified validation.
The file interface is implemented in [`CLI.lean`](../Ix/Certified/CLI.lean).

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
execution, transport parsing, filesystem loading and the BLAKE3 foreign interface remain
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
and exercises the actual source and claim executables on all three legacy CLI
corpora. It also checks the binary/text input codecs and format-selection
regressions. CI runs the same gate.

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

`Address.blake3` supplies a kernel-checked proof of its 32-byte output bound,
replacing a native-evaluation axiom missed by the historical imported summaries.
The wrapper is definitionally equal to the former hash operation. The frozen
corpora check that source and envelope bytes are unchanged.

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
the maintained Lean driver formats JSON differently. Typed binary/text
roundtrips cover all 86 source requests and 1,652 claim requests and envelopes
from the source, claim, and modeled corpora. Additional process tests exercise
mixed input formats, malformed encodings, wrong digests, unsupported versions,
and command-line errors. The archive, source
mappings, licenses and historical reproduction limits are documented in
[`Tests/Fixtures/Certified`](../Tests/Fixtures/Certified/README.md). The archive
recovers the selected adapter sources and fixtures; it does not include the
complete historical Ix base checkout.
