# Typed Ixby runtime representation proofs

The runtime proofs for the [typed Lean frontend](ixby-lean.md) establish exact
numeric representation laws and certify seven generated extension helpers and
eleven number conversion helpers against the unchanged Ixby evaluator. The
conversion proofs include complete loops and calls into existing caller
continuations. The complete LCNF transformation and Stage2 verifier remain
outside this certificate boundary.

## Exact values and conversions

[Representation.lean](../Compilatrix/Ixby/Runtime/Representation.lean) defines
`Number layout n value` for the runtime's three numeric layouts:

| Representation | Required contents | Source Nat |
| --- | --- | --- |
| Cached number | Nat `n` and exactly `n.toUInt32` | `n` |
| Raw number | Nat `n` | `n` |
| Field number | Canonical Goldilocks `f` | `f.val` |

`Field layout f value` requires this same relation at `f.val`. A field-backed
number therefore retains its exact Nat observation. Mixed comparisons never
reduce the other Nat operand modulo the field. The proofs cover cache
preservation for addition, multiplication, and both branches of truncated
subtraction, together with the base-16 accumulator identities used by the
word conversion loops.

The byte laws quantify over every width and Nat. Decoding `bytesLE width n`
returns `n % 256^width`, making truncation explicit. Slicing an encoding is
equivalent to encoding the corresponding quotient. These facts establish
word and field roundtrips, exact reconstruction of a field's Nat from its two
words, and reconstruction of `Goldilocks.reduce n` from the reduced Nat's two
words using native field arithmetic.

[ScalarLaws.lean](../Compilatrix/Ixby/Runtime/ScalarLaws.lean) connects these
facts to `Primitive.eval`. It covers Nat arithmetic and equality, native field
and extension operations, field/word conversion, canonical field byte
roundtrips, and rejection of noncanonical field bytes. Input and result
capacities remain explicit wherever scalar validation can fail. Field and
extension arithmetic do not require a Nat or byte capacity premise.

[LeanSound.lean](../Compilatrix/Ixby/LeanSound.lean) connects the representation
relation to the actual `Image.number` and `Image.decodeNumber` APIs. A checked
layout witness proves encoding/decoding roundtrip, unique Nat observation,
and rejection of an inconsistent cached word. These are universal laws,
including naturals above 64 bits and field values at the modulus boundary.

`claimResult` separately specifies the external Option-to-bytes/erased
observation. Its injectivity proof distinguishes rejection from every
successful byte string, including an empty string. This is an observation
law, not yet a simulation of the generated Stage2 adapter.

## Certificates for actual generated functions

`Image.certifyScalars` locates candidates through the image's function names,
then checks complete function bodies, arities, entry blocks, and the field
projection constructor declaration. Acceptance retains kernel equality
evidence about that exact program. Names and function-body hashes alone do
not authorize a certificate.

[ScalarCertificate.lean](../Compilatrix/Ixby/Runtime/ScalarCertificate.lean)
provides universal source-operation agreement for these functions:

| Generated helper | Result | Reference transitions |
| --- | --- | ---: |
| Extension add, subtract, multiply | Exact source extension result | 3 |
| Extension inverse | Exact source total inverse, including zero | 3 |
| Extension equality | Exact source Boolean | 3 |
| First and second extension projections | Field box containing the source coefficient | 4 |

The local contracts start at the helper with an empty continuation and require
at most three local slots. They execute the actual reference `run` function.
The underlying [function contracts](../Compilatrix/Ixby/Runtime/ScalarFunction.lean)
also derive whole-program `Evaluates` after ordinary program/input validation
and entry selection. Public multiplication, inverse, and first-projection
corollaries instantiate the primitive semantics with the source operations.
These extension contracts currently expose the empty-continuation form. The
conversion contracts below additionally preserve arbitrary caller continuations.

Both the typed comparison suite and Stage2 binary compilation obtain the
layout witness and scalar certificates. The certificate checker rejects
changed primitives, return operands, projections, arities, entry blocks,
extra blocks, constructor field counts, and name bindings. Five of these
mutations still pass whole-program structural admission, so the tests also
exercise semantic changes that the ordinary validator permits.

## Complete number conversion executions

`Image.certifyConversions` checks eleven generated functions, all three number
constructor declarations, distinct constructor tags, and the function and
constructor name bindings used to locate them. Its result retains both the
actual program certificate and the layout evidence needed by `Image.decodeNumber`.
The [code templates](../Compilatrix/Ixby/Runtime/ConversionCode.lean) contain
complete bodies with image-supplied function and constructor indices. Changed
code, linkage, arity, entry blocks, and extra unreachable blocks are rejected.

The [execution relation](../Compilatrix/Ixby/Runtime/Execution.lean) is a finite
path through the actual reference `step` function. A helper reaches its return
control with the caller's continuation intact. Ordinary calls push and restore
the saved frame, including its locals; tail calls retain the continuation.
The transfer and capacity checks remain part of execution. These paths compose
with reference `run`, and with `Evaluates` after reference program/input
admission. The proofs use concrete primitive semantics throughout.

Both [digit converters](../Compilatrix/Ixby/Runtime/Nibble.lean) are proved for
all sixteen possible digits. The [Nat-to-word loop](../Compilatrix/Ixby/Runtime/ToWord.lean)
terminates and returns `accumulator + n.toUInt32 * weight`, including its zero
Nat and zero weight exits. Its proof executes the nested digit call and the
recursive tail call. It covers arbitrary Nat inputs that fit the explicit
scalar limit, including inputs larger than a word or field.

The [word-to-Nat loop](../Compilatrix/Ixby/Runtime/FromWord.lean) terminates and
returns the exact `accumulator + word.toNat * weight`. Its invariant bounds
both the result and the final weight. With the usual initial weight of one,
the helper computes an unused final weight of `2^32`; this requires **33 Nat
bits**, although its result fits in 32. Tests confirm that the same nonzero
eight-digit input fails at 32 bits and succeeds at 33.

The [field adapters](../Compilatrix/Ixby/Runtime/FieldConversion.lean) execute
both word conversions and the native reconstruction operations. `fieldNatural`
returns the field's exact canonical Nat. `fieldFromNatural` returns
`Goldilocks.reduce n`. The [number dispatch proofs](../Compilatrix/Ixby/Runtime/NumberConversion.lean)
then cover all three values in the `Number` relation:

| Helper | Result | Local slots | Nat bits | Spare continuations | Byte capacity |
| --- | --- | ---: | ---: | ---: | ---: |
| `toWord n 1 0` | `n.toUInt32` | 11 | 5 + input fits | 1 | 0 |
| `fromWordLoop w 1 0` | Exact `w.toNat` | 10 | 33 | 1 | 0 |
| `fromWord w` | Consistent cached number | 10 | 33 | 2 | 0 |
| `fromRaw n` | Raw number containing `n` | 2 | No primitive Nat operation | 0 | 0 |
| `fieldNatural f` | Exact `f.val` | 10 | 64 | 2 | 8 |
| `fieldFromNatural n` | `Goldilocks.reduce n` | 11 | 64 + input fits | 2 | 0 |
| `natural value` | Exact represented Nat | 10 | 64 | 2 | 8 |
| `asField value` | Reduced represented Nat | 11 | 64 + represented Nat fits | 2 | 0 |
| `lowWord value` | Low word of represented Nat | 11 | 5 + represented Nat fits | 1 | 8 |

These are sufficient local-contract bounds. Whole-program admission also
checks every literal in the image and validates the input. The numeric
representation relation is an additional premise; structural input validation
alone does not establish cache consistency. Public `natural`, `asField`,
`lowWord`, `fromWord`, and `toWord` corollaries derive whole-program `Evaluates`
with explicit admission and input-validation premises. The `fromWord`
representation theorem establishes the cache invariant for its returned box.

The comparison suite obtains all eleven certificates on every compiled image.
It rejects 21 conversion mutations, including 17 that still pass structural
admission. Another 224 admitted helper executions cover all number layouts,
the field modulus boundaries, and large Nats; eleven local resource cases test
successful thresholds and exact capacity errors. Stage2 compilation obtains
the same certificates before export. Its binary and manifest are unchanged.

## Remaining simulation work

The next extension can use these conversion contracts to prove complete Nat
arithmetic and base-field helpers preserve the source representation relations.
Further composition must cover arrays and byte representations, the complete
Stage2 adapter, and general LCNF control flow.
Typed erasure, specialization, original Ixon source authentication, and
source/image reflection remain open. This slice introduces no new axiom or
native interface and does not produce an `IxonCompilation`.

## Validation

```sh
lake build Compilatrix.Ixby.Fence check-ixby-lean stage2-ixby
lake exe check-ixby-lean
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
cmp fixtures/ixby-stage2/stage2.ixby /tmp/stage2.ixby
nix flake check --no-update-lock-file
```

The axiom fence includes 22 representation/scalar guards and 20 conversion and
continuation guards. They pin the contracts to subsets of `propext`,
`Classical.choice`, and `Quot.sound`. The integration gate retains
the 4,585 differential executions, binary corpus, exact fresh Stage2 artifact
comparisons, and all eight serialized verifier cases.
