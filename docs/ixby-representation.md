# Typed Ixby runtime representation proofs

The runtime proofs for the [typed Lean frontend](ixby-lean.md) establish exact
numeric representation laws and certify all 52 generated number helpers and
all 14 field helpers against the unchanged Ixby evaluator. These include
eleven number conversions, eight Nat arithmetic/comparison helpers, six Nat
loop/wrapper functions, and 27 UInt8/UInt32/USize helpers.
The conversion and arithmetic proofs include complete loops and calls into existing caller
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

## Complete Nat arithmetic and comparisons

`Image.certifyNatArithmetic` checks the complete bodies of `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.decEq`, `Nat.decLt`, and `Nat.decLe`
together with all eleven conversion dependencies, number layouts,
and function/constructor name bindings. Its [certificate](../Compilatrix/Ixby/Runtime/NatArithmeticCertificate.lean)
retains propositional equality with the actual program's code. The
[templates](../Compilatrix/Ixby/Runtime/NatArithmeticCode.lean) use image-supplied
indices and leave the builder and emitted binary unchanged.

The [call contracts](../Compilatrix/Ixby/Runtime/NaturalCall.lean) execute each
ordinary call to `natural`, the complete conversion, and the restoration of
the saved caller frame. The [binary proof](../Compilatrix/Ixby/Runtime/NatBinary.lean)
then covers all nine input representation pairs. Both operands contribute
their exact Nat observations: a field box contributes its canonical Nat,
without reducing the other operand. For example, a field box containing
`p - 1` plus a raw Nat containing `p + 1` returns the exact Nat `2 * p`.

The [subtraction proof](../Compilatrix/Ixby/Runtime/NatSub.lean) executes both
branches. Underflow returns a consistent cached zero for every input layout.
Otherwise, the emitted helper repeats both conversion calls before subtraction.
For all three operations, two cached inputs retain a correct low-word cache;
the other non-underflow paths return a raw Nat. Word subtraction is used only
after the comparison establishes `b ≤ a`.

The [division and remainder proof](../Compilatrix/Ixby/Runtime/NatDivision.lean)
observes both exact Nats, executes the primitive, and follows the tail call to
`fromRaw`. Both operations always return the exact raw Nat box, including
Lean's zero-divisor results `a / 0 = 0` and `a % 0 = a`. Their results are
bounded by the left input, so no separate result-capacity premise is needed.

The [order proofs](../Compilatrix/Ixby/Runtime/NatOrder.lean) return the source
Booleans for `<` and `≤`, including both branches of the emitted less-or-equal
helper. The [equality proof](../Compilatrix/Ixby/Runtime/NatEquality.lean)
covers every constructor dispatch and both restored conversion calls whenever
either operand is cached or raw. Mixed equality preserves the exact Nat:
a raw Nat containing `p` is unequal to a field box containing zero. Two native
field boxes use the emitted `fieldEq` path directly. Its stronger local
contract needs only five slots, with no Nat, byte, or additional continuation
capacity.

The public [arithmetic contracts](../Compilatrix/Ixby/Runtime/NatArithmetic.lean)
return a represented exact Nat for addition, subtraction, and multiplication,
the exact raw box for division and remainder, and the exact source Boolean for
each comparison. Local paths preserve arbitrary caller continuations.
All eight whole-program `Evaluates` corollaries require ordinary program and
input validation, entry selection, and the input representation relations.

| Helpers | Local slots | Nat bits | Spare continuations | Byte capacity | Additional scalar bounds |
| --- | ---: | ---: | ---: | ---: | --- |
| `Nat.add`, `Nat.mul` | 11 | 64 | 3 | 8 | Both inputs and the exact result fit |
| `Nat.sub` | 14 | 64 | 3 | 8 | Both inputs fit; the result is bounded by the left input |
| `Nat.div`, `Nat.mod`, `Nat.decEq`, `Nat.decLt`, `Nat.decLe` | 10 | 64 | 3 | 8 | Both inputs fit |
| `Nat.decEq`, two native field boxes | 5 | 0 | 0 | 0 | None |

These are sufficient bounds across all representations. The 64-bit requirement
supports exact field decoding; larger Nats and results are allowed whenever
they fit the selected scalar limit. Structural input validation alone still
does not establish the cache invariant required by `Number`.

Every compared image and Stage2 export obtains the arithmetic certificate.
The suite rejects 48 arithmetic/comparison/dependency/layout mutations,
including 43 structurally admitted programs. Another 12,168 admitted executions
compare all nine representation pairs against source Nat arithmetic and
comparisons at zero divisors, word and field boundaries, and on Nats above
256 bits. Division and remainder also check the exact raw result layout.
Thirty-two caller cases check both saved inputs and the returned result.
Thirty-five local resource cases cover local slots, continuations, field bytes,
and scalar capacity, including the direct native-field equality path and
64-bit result failures that succeed at 65 bits. These local resource checks are
separate from whole-image admission, which also validates unrelated literals
and functions.

## Complete base-field helpers and extension packing

`Image.certifyFields` checks the six `Goldilocks` wrappers (`reduce`, `add`,
`sub`, `mul`, `neg`, and `inverse`) and `ExtGoldilocks.mk`. Together with the
seven extension-helper certificates above, this covers every function emitted
by `buildFields`. The [code templates](../Compilatrix/Ixby/Runtime/FieldArithmeticCode.lean)
use the image's actual conversion and constructor indices. The
[certificate](../Compilatrix/Ixby/Runtime/FieldArithmeticCertificate.lean) checks
complete bodies and retains all eleven conversion dependencies and number
layouts. Both regression images and Stage2 export require these certificates.

The [field-call contracts](../Compilatrix/Ixby/Runtime/FieldCall.lean) execute
each ordinary call to `asField`, its complete conversion path, and checked
caller restoration. The [field execution proofs](../Compilatrix/Ixby/Runtime/FieldArithmetic.lean)
then compose the actual native primitive and return instructions. They cover
all three input layouts, all nine binary representation pairs, and arbitrary
caller continuations.

All six base-field helpers return the exact canonical field box. Arithmetic
uses the source operations on `Goldilocks.reduce a` and `Goldilocks.reduce b`;
negation and inversion use the reduced input. The inverse contract includes
zero and multiples of the field modulus. Extension construction returns the
exact native extension scalar with the reduced first and second coefficients
in source order. Each helper also has a whole-program `Evaluates` corollary
with ordinary program/input admission, entry selection, and the input
representation relation.

The uniform local bounds are 11 slots, 64 Nat bits, and three spare
continuations. Each input Nat observation must fit the selected scalar limit.
No byte buffer or separate result-capacity premise is needed: field results
are canonical, and the conversions construct fields directly from words.
Structural admission alone still does not establish the `Number` cache
invariant.

The field suite has 6,201 admitted helper executions, 25 caller-preservation
cases, eight packing/projection compositions, and 24 local resource cases.
It covers zero inverse, modular boundaries, all layouts, and Nats above 256
bits, checking exact result boxes and coefficient order. The resource cases
test the uniform bounds and smaller native-field paths, including zero Nat
and byte capacity with one spare continuation. All 29 code, dependency,
constructor, and name-binding mutations are rejected; 24 remain structurally
admitted. Seventeen axiom guards cover the field paths, conversion calls, and
whole-program corollaries.

## Complete Nat shift, logarithm, and power loops

[NatLoopCode.lean](../Compilatrix/Ixby/Runtime/NatLoopCode.lean) specifies the
exact emitted bodies for `Nat.shiftRight`, `Nat.log2`, `Nat.pow`, and their
three loop helpers. The [certificate](../Compilatrix/Ixby/Runtime/NatLoopCertificate.lean)
checks those complete bodies together with the existing arithmetic certificate,
conversion dependencies, and number layouts. `Image.certifyNatLoops` retains
the actual image's name bindings and decoding layout; every compared image
and Stage2 export obtains it.

The [shift and logarithm proofs](../Compilatrix/Ixby/Runtime/NatShiftLog.lean)
establish finite paths through all branches. `shiftRightLoop n shift` returns
a number representing `n >>> shift`, including its early cached-zero return.
`log2Loop n accumulator` returns the exact raw box for
`accumulator + n.log2`; both zero and one contribute zero. Their tail calls
preserve the complete existing continuation without adding a frame.

The [power laws](../Compilatrix/Ixby/Runtime/NatPowLaws.lean) prove the even/odd
halving identities and bounds for every square and accumulator product.
[NatMulCall.lean](../Compilatrix/Ixby/Runtime/NatMulCall.lean) composes actual
calls to the certified multiplication helper with checked caller restoration.
The [power execution proof](../Compilatrix/Ixby/Runtime/NatPow.lean) then shows
that `powLoop base exponent accumulator` terminates with a number representing
`accumulator * base ^ exponent`. A zero exponent returns the original
accumulator, and the loop skips the unused final square. `Nat.pow` starts with
cached one, so the public result is exactly `base ^ exponent`, including
`0 ^ 0 = 1`. Every retained cache is consistent.

| Helpers | Local slots | Nat bits | Spare continuations | Byte capacity | Additional scalar bounds |
| --- | ---: | ---: | ---: | ---: | --- |
| `shiftRightLoop n shift` | 6 | 2 | 0 | 0 | Both inputs fit |
| `log2Loop n accumulator` | 5 | 2 | 0 | 0 | `n` and `accumulator + n.log2` fit |
| `Nat.shiftRight`, `Nat.log2` | 10 | 64 | 3 | 8 | Input Nat observations fit |
| `powLoop base exponent accumulator` | 11 | 64 | 4 | 8 | Inputs, `base ^ exponent`, and `accumulator * base ^ exponent` fit |
| `Nat.pow` | 11 | 64 | 4 | 8 | Both input Nat observations and the final power fit |

These are sufficient local bounds, independent of the iteration count.
Shift results and logarithm increments are bounded by the supplied valid
inputs/results. For the internal power loop, a valid accumulated result alone
does not bound intermediate squares: a zero accumulator can conceal a large
base power. Its extra unscaled-power bound handles this case. At the public
entry, the accumulator is one, so the single final-result premise covers all
intermediate products. All three public helpers accept every number layout.
The [six whole-program corollaries](../Compilatrix/Ixby/Runtime/NatLoops.lean)
add ordinary program/input admission and preserve the explicit representation
and scalar-validity premises.

The suite adds 6,016 admitted executions across all layouts and representation
pairs, exact result layouts and caches, word/field boundaries, Nats above 256
bits, and shift counts/exponents above 64 bits. The huge-exponent power cases
use bases zero and one with their exact source laws. Fifty-one actual caller
cases check every saved input, an untouched sentinel, and the result.
Forty-five local resource cases cover the stated bounds, smaller early-return
paths, byte/continuation failures, 64/65-bit result boundaries, skipped final
squares, and the internal zero-accumulator overflow case. All 44 code,
dependency, layout, and name-binding mutations are rejected; 40 remain
structurally admitted. Nineteen additional axiom guards cover the arithmetic
bounds, multiplication calls, all six return contracts, and all six
whole-program corollaries.

## Complete UInt8, UInt32, and USize helpers

`Image.certifyWords` checks all 27 word helpers with the eleven conversion
dependencies, constructor declarations, distinct layout tags, and source name
bindings. The [templates](../Compilatrix/Ixby/Runtime/WordCode.lean) and
[certificate](../Compilatrix/Ixby/Runtime/WordCertificate.lean) retain exact
propositional code equality using the image's actual function indices.
Together, the certificates cover all 52 functions emitted by `buildNumbers`
and all 14 emitted by `buildFields`.

The [conversion contracts](../Compilatrix/Ixby/Runtime/WordConversions.lean)
cover all five truncations and four identity conversions. Truncation returns
a canonical cached number with the source width's modular value. Identity
conversions preserve the original value and representation. `UInt32.ofNatLT`
requires its source bound and accepts any value in its erased proof slot;
whole-program admission still validates that supplied value.

The [arithmetic contracts](../Compilatrix/Ixby/Runtime/WordArithmetic.lean)
cover byte addition, UInt32 addition/subtraction/multiplication, and USize
addition/subtraction. Their [execution paths](../Compilatrix/Ixby/Runtime/WordModular.lean)
perform all four operand observations, construct the intermediate cache,
observe that result again, and truncate it. The
[cache laws](../Compilatrix/Ixby/Runtime/WordLaws.lean) establish consistency
before either result observation, including underflow subtraction. Bounds
on unreduced sums and products follow from the source operand widths.

The [comparison contracts](../Compilatrix/Ixby/Runtime/WordComparisons.lean)
return exact source Booleans for three equalities and two strict orders.
The [logical and shift contracts](../Compilatrix/Ixby/Runtime/WordBits.lean)
cover UInt32 AND/OR/XOR and both UInt8/UInt32 shifts. The
[shift laws](../Compilatrix/Ixby/Runtime/WordShiftLaws.lean) prove that the
count masks implement source reduction modulo 8 or 32 and satisfy the
reference primitive's strict count range. Byte shifts also mask the result
back to eight bits.

All numeric operations other than the identities return the exact cached
source result. The [call proofs](../Compilatrix/Ixby/Runtime/WordCall.lean)
execute ordinary observer calls and checked restoration of saved callers.
Every local contract preserves arbitrary caller continuations, and all 27
[whole-program corollaries](../Compilatrix/Ixby/Runtime/Words.lean) retain
program admission, input validation, and the source representation premises.

| Helpers | Local slots | Nat bits | Spare continuations | Byte capacity |
| --- | ---: | ---: | ---: | ---: |
| Four identity conversions | 1 | 0 | 0 | 0 |
| UInt8/UInt32 truncations, including `ofNatLT` | 11 | 64 | 3 | 8 |
| `USize.ofNat` | 11 | 65 | 3 | 8 |
| Five comparisons | 10 | 64 | 3 | 8 |
| UInt8/UInt32 arithmetic | 14 | 64 | 3 | 8 |
| USize addition/subtraction | 14 | 65 | 3 | 8 |
| Seven logical/shift helpers | 11 | 33 | 2 | 8 |

These are sufficient bounds across all admitted number layouts. Arbitrary
Nat inputs to `ofNat` must also fit the selected scalar limit. Source word
operands already bound the other numeric intermediates. USize conversion,
addition, and subtraction explicitly assume `System.Platform.numBits = 64`,
matching the compiler's fixed width. Their 65-bit capacity is necessary even
for some small results: truncating zero reads the literal `2^64`, and a
wrapped sum can exceed the final source range. The logical/shift bound allows
the word-to-Nat loop's final weight to reach `2^32`.

Every regression image and Stage2 export obtains the word certificate. The
word suite has 45,769 admitted executions, including every byte input, all
byte-shift residues and wrapped counts, all number layouts, word/field
boundaries, and Nat conversions above 256 bits. It checks exact results and
cache consistency. Another 136 caller cases retain every input, proof slot,
sentinel, and result; 45 local resource cases check successful capacities and
exact failures. All 92 code/dependency/name/layout mutations are rejected,
including 88 that pass structural admission. Seventy-six additional axiom
guards cover these source, execution, arithmetic, and caller contracts.

## Remaining simulation work

The next extension can compose these contracts through arrays and byte
representations. Further work must cover the complete Stage2 adapter and
general LCNF control flow.
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

The axiom fence includes 22 representation/scalar guards, 20 conversion and
continuation guards, 21 Nat arithmetic/comparison/call guards, 17 field/call
guards, 19 Nat loop/arithmetic-bound/call guards, and 76 word/source/call
guards: 175 runtime guards in total. They pin the contracts to
subsets of `propext`, `Classical.choice`, and
`Quot.sound`. The integration gate retains
the 4,585 differential executions, binary corpus, exact fresh Stage2 artifact
comparisons, and all eight serialized verifier cases.
