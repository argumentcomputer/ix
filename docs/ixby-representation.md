# Typed Ixby runtime representation proofs

The first proof slice for the [typed Lean frontend](ixby-lean.md) establishes
exact numeric representation laws and certifies seven generated extension
helpers against the unchanged Ixby evaluator. It does not yet certify the
complete LCNF transformation or the Stage2 verifier.

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
General caller-continuation composition remains a later boundary.

Both the typed comparison suite and Stage2 binary compilation obtain the
layout witness and scalar certificates. The certificate checker rejects
changed primitives, return operands, projections, arities, entry blocks,
extra blocks, constructor field counts, and name bindings. Five of these
mutations still pass whole-program structural admission, so the tests also
exercise semantic changes that the ordinary validator permits.

## Remaining simulation work

The next extension must connect the conversion-loop invariants to complete
machine executions of `toWord`, `fromWordLoop`, `natural`, and `asField`,
including their calls, branches, intermediate scalar capacities, and return
continuations. The arithmetic reconstruction suffix is proved; the loops
that supply its words are not yet machine-certified.

Further composition must cover base-field helper calls, arrays and byte
representations, the complete Stage2 adapter, and general LCNF control flow.
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

The axiom fence pins the representation and execution contracts to subsets of
`propext`, `Classical.choice`, and `Quot.sound`. The integration gate retains
the 4,585 differential executions, binary corpus, exact fresh Stage2 artifact
comparisons, and all eight serialized verifier cases.
