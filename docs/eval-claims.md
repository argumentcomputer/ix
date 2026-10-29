# Evaluation claims

`Eval(input, output, assumptions)` uses the existing Ixon v4 claim encoding.
Both addresses identify ordinary constants; neither is the hash of an entire
environment. There is no new expression object or wire-format version.

The input is a safe body-bearing declaration: a definition, theorem, opaque
declaration, or definition projection. The output is a safe standalone
definition wrapping the expected result, with the input's universe parameter
count and type. For example, an output may be an anonymous definition
`_obj : Nat := 42`.

IxVM verifies the claim by:

1. Typechecking the input and its transitive dependencies. An assumption tree
   may waive dependency checks, but cannot contain the input itself.
2. Authenticating the output constant through the existing constant channel.
   Its universe parameter count must equal the input's, and its decoded,
   erased type must be structurally identical to the input's type.
3. Recursively normalizing the input body with the existing WHNF reducer.
   This includes binder domains and bodies, application arguments, and
   projection operands. The reducer preserves opaque/theorem references and
   the kernel's compact symbolic arithmetic forms.
4. Comparing that normal form structurally with the decoded, erased output
   body. The proposed output is not reduced, and proof irrelevance does not
   make different results interchangeable.

Output typing follows from the checked input, the matching declared type,
and type preservation of reduction. IxVM does not independently typecheck
the output body. The output type must preserve the input's syntax after
table resolution and erasure; a merely definitionally equal type is rejected.
Different table layouts and sharing choices can still denote the same term.

The validator is `erased-lean-v1`. Resource annotations remain committed in
constant bytes but are erased by the kernel; Eval does not certify resource
admission or resource preservation. It also does not assert that arbitrary
inputs terminate or impose an execution-time bound.

## Environment bundles

The output can be shipped in an ordinary `.ixe` bundle whose `main` points
to the anonymous definition. Existing `ix pack` closure traversal carries
its referenced constants and literal blobs. A receiver compares `main` with
the output address expected by the claim, then supplies the input and output
closures through the existing witness builder.

The output address commits to its type, value, and definition fields. It is
independent of unrelated environment entries and display metadata. The
bundle is the transport artifact; its whole-file hash is not the eval output.
Bundle assumptions describe missing dependencies and do not automatically
authorize the typing assumptions committed by the claim.

## Host integration and tests

`Ix.Commit.evalClaimWithEnv` compiles both endpoints with the same type and
returns the claim together with the compilation cache containing their bytes.
`evalClaim` retains its existing interface. `#ixeval` uses Lean's
`Meta.reduceAll` to propose a result and prints the claim and digest; it does
not execute IxVM or prove the claim. Lean and IxVM can choose different
normal forms at opacity and symbolic-arithmetic boundaries, so a proposed
claim still needs verification.

The existing `ixvm` suite covers reductions, output type and safety checks,
malformed/authenticated bytes, assumptions, dependent and recursive programs,
24 generated arithmetic programs, and exact FFT-cost pins for successful evaluations.
The command regression packs both endpoints into ordinary bundles before
executing its printed claim. These tests execute Aiur without proving:

```sh
lake test -- --ignored ixvm
```
