# Ixon v5: ExprObj and evaluation claims

Version 5 adds standalone expression objects and gives Eval claims an
implemented meaning. Existing constant, expression, universe, and literal
encodings are unchanged, so their content addresses and primitive pins remain
unchanged. Environment headers and claim/proof/catalog scopes change to 5.
Old scoped artifacts must be regenerated; a v4 Eval output must not be
interpreted as a v5 output.

## ExprObj

An `ExprObj` packages a closed expression, without declaring a type or adding
a constant to the environment:

```text
E0 05
TagN0(universe_parameter_count)
Expr(root)
TagN0(sharing_count) Expr*
TagN0(ref_count) Address*
TagN0(univ_count) Univ*
```

`E0` is TagN4(flag=E, value=0), distinct from constants and claims. `05` is
the object-format byte. Reference and universe indices have the same meaning
as in constants. Names and display metadata are external.

Every table entry is structurally validated, including unused entries.
Sharing references point strictly backward. Shared open subterms are allowed
under binders, but the root has no free term variables. Universe variables
are bounded by `universe_parameter_count`. Block-relative `Rec` is forbidden:
standalone references must name the corresponding addressed constant.

Objects are BLAKE3-addressed over their exact bytes. The transport stores them
in `Env.blobs`, not `Env.consts`; their tag and the consumer identify their
kind. They are not leaves in a CheckEnv typing subject. No new environment
section is needed.

Structural validity does not assert a unique table layout or minimal sharing.
Equivalent decoded terms can have different object addresses. The initial
`compileExprObj` helper reuses a compiled anonymous definition's tables,
including entries needed only by its type, then discards the declaration
fields. Consumers must not infer declaration typing from an ExprObj alone.

## Eval semantics

The claim remains:

```text
E3 05 01 input[32] output[32] assumptions
```

The input addresses a safe body-bearing declaration (definition, theorem, or
opaque declaration, including a definition projection). The output addresses
an ExprObj, with the same positional universe-parameter context.

IxVM:

1. Checks the input and its transitive constant dependencies. An optional
   assumption tree waives dependency checks only; it cannot contain the input.
2. Recursively normalizes the input body using the existing WHNF reducer.
   It normalizes lambda/Pi domains and bodies, constructor/application
   arguments, and stuck projection operands. The head of a residual
   application is preserved: isolated primitive unfolding must not destroy
   WHNF's compact stuck arithmetic forms. Opaque/theorem references retain
   the existing reducer's unfolding policy.
3. Authenticates the output object bytes, validates its tables and scope,
   resolves references/sharing, and compares its erased expression
   structurally with the computed result.

There is no independent output typecheck: its type is inherited by reduction
from the checked input. There is also no output normalization or general
definitional-equality check. A merely convertible, unreduced output fails.

The validator is `erased-lean-v1`. Ixon resource annotations remain committed
in the object's bytes but are erased for this comparison, just as they are
for existing typing claims. Eval does not certify their resource validity or
preservation. It is a deterministic reduction claim, not a resource claim,
an execution-time bound, or a claim that every accepted input terminates.

## Witness and API

Channels 0–5 keep their meanings. Channel 6 holds ExprObj bytes, keyed by
their 32-byte address. IxVM rehashes those bytes before interpreting them.
The witness includes the input closure and the objects referenced by the
output tables, including literal blobs. Output references are not additional
typing assumptions.

Lean: `Ixon.ExprObj.{validate,ser,de}`, `Ixon.Env.storeExprObj`,
`Ix.Commit.compileExprObj`, and `Ix.Commit.evalClaimWithEnv`. The latter
retains the input and output bytes for witness construction.

Rust: `ixon::ExprObj::{validate,put,get,from_bytes,commit}`.

Execution tests live in `Tests/Ix/IxVM/Eval.lean` and run as part of the
existing `ixvm` suite. They use Aiur execution and do not generate proofs.

```sh
lake test -- --ignored ixvm
```

The eval corpus includes indexed-vector recursion, dependent casts and
projections, mutual recursion, a structural fold over a nested inductive tree,
transparent well-founded recursion, capture avoidance,
Pi/lambda domain normalization, opacity, and compact symbolic Nat offsets.
The differential corpus generates 24 depth-4 arithmetic terms with lexical
lets and beta redexes from seed `0x4958564d`. Each term is checked against
both Lean's reducer and an independent numeric interpretation, and a mutated
result must be rejected. Labels include the sample index and seed for
reproduction; a coverage check requires all seven generation forms.
The command regression checks the printed result, claim, and digest against
an independently constructed claim and executes that exact claim in both backends.
Both execution backends run the semantic cases. Differential comparison is
restricted to terms where reduction policies agree; opacity, stuck arithmetic,
and well-founded recursion through accessibility theorems have explicit
expected results instead. Lean's meta reducer keeps theorem references opaque
even when all definition unfolding is enabled.
Likewise, `#ixeval` uses Lean's meta reducer to propose an output; it reports
the resulting claim without verifying it. Its candidate can differ from
IxVM's normal form where these reduction policies differ.
The elaborator-generated tree recursion also supplies a negative test: its
accessibility proof contains `Lean.opaqueId`, so a claim for the native
numeric result must fail. An explicit accessibility proof without that wrapper
supplies the positive well-founded recursion test.
