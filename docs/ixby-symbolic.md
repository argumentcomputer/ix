# Reusable IxIR₀ → Ixby refinement

`Compiled.certifySymbolic` checks a compiled image once and returns a theorem
for every admitted runtime argument array. It takes no runtime inputs. The
source and target are evaluated symbolically with opaque parameter variables;
structural proofs show that each successful symbolic evaluation remains valid
after substituting arbitrary actual values for those parameters.

This is input-independent translation validation for a declared fragment.
It is not a general correctness theorem for every image emitted by `lower`.
The original [Ixby reference and codecs](ixby-backend.md) are unchanged.

## Admitted fragment

An accepted program has a finite symbolic execution path and returns a finite
data expression built from parameters, literals, erased values, and declared
constructors. Runtime parameters may flow through variables, strict lets,
closures, captured environments, partial applications, and constructors.
They can be duplicated, reordered, or projected from a constructor assembled
by the program. Known functions can accept them. Recursion and case analysis
are supported when the major value is symbolically known.

The checker rejects inspecting an opaque parameter, calling it as a function,
projecting its fields, or choosing a case based on it. It also rejects function
results, externs, divergence, failed source or target evaluation, and exhausted
checking or machine budgets. In particular, parsers and verifiers that inspect
runtime byte arrays need a broader proof. Increasing symbolic fuel does not
add that capability.

These restrictions bound the checked control path, not the number of future
inputs. Inputs may be any `Data` arrays admitted by the fixed arity, constructor
table, value limits, and chosen observation depth. Literal Nat/String inputs
are admitted by the current semantics-2 profile within its declared capacities.

## Proof and exact image binding

`SymbolicSource.eval_sound` proves substitution soundness for the unchanged
IxIR₀ evaluator by induction on fuel. `SymbolicTarget.run_sound` proves it for
the unchanged Ixby machine, including frames, calls, under/over-application,
continuations, returns, validation, and resource checks. The symbolic machine
does not add instructions to the target.

`certifySymbolicImage source config program` validates a complete candidate
image, checks both symbolic executions, and compares their complete parsed
data expressions. Equality covers parameter indices, all constructor addresses
and tags, field order, and every nested value. `Compiled.certifySymbolic`
specializes this evidence to the exact `compiled.program`; `Compiled` retains
its successful lowering and original whole-image validation equations.

For each `Arguments source config depth`, `certificate.source_evaluates`
derives a source evaluation. `certificate.refinement depth` has the original
upstream `ExecutionRefinement` contract: every successful execution of the
compiled program on the admitted arguments decodes to a source result.
Source termination and a separately supplied concrete source run are not
premises. Target determinism relates successful runs at any fuel to the
symbolically established output. Execution may still fail admission or exhaust
the caller's runtime fuel; reflection concerns successful executions.

`Arguments.check` performs host data admission and exact encoding/decoding
checks, without executing either guest evaluator. The observed output depth
is the sum of the input depth and certificate data depth. The proof covers
complete nested input and output trees, not hashes of those trees.

For canonical execution, `Arguments.export` encodes and decodes the input with
the original codec, retaining equality with the entire admitted argument array.
`Arguments.read` checks that same binding for bytes received externally.
`certificate.byte_refinement` then connects every successful original
`Codec.Evaluates` execution to a source result and the complete canonical output
encoding under the exact program and profile.

The six additional axiom fences use only `propext`, `Quot.sound`, and, where
needed, `Classical.choice`. No `sorry`, native decision axiom, hash injectivity
premise, or new native interface is used. The checked Ixon prefix retains its
existing separate source-address boundary. This theorem's source anchor is
IxIR₀ weak CBV; reverse Ixon erasure and upstream `Meta.reduce` reflection
remain separate obligations.

## Usage

```lean
import Compilatrix.Ixby.SymbolicWire

open Compilatrix Compilatrix.Ixby

def reuseIdentity : Except String (Array Data) := do
  let source : Source := { declarations := [], main := .var 0, parameters := 1 }
  let compiled ← compile source
  let certificate ← compiled.certifySymbolic
  let mut results := #[]
  for data in [#[Data.nat 42], #[Data.str "λ"], #[Data.erased]] do
    let args ← Arguments.check source {} 64 data
    -- certificate.source_evaluates args proves this result for each new input.
    results := results.push (certificate.result.instantiate args.dataAt)
  return results
```

The catalog CLI accepts `--symbolic` after its ordinary arguments:

```sh
lake exe ixon-to-ixby path/to/program.ixc MAIN new-output proving 2 --symbolic
```

Certification must succeed before the output directory is created. Alongside
the exact source, program, configuration, and optional wire artifacts,
`symbolic.json` records the fragment version, arity, checking budgets, and full
symbolic result. It is reproducible checker metadata, not a serialized Lean
proof. Reconstruct the certificate from the complete source/configuration/image
and recorded budgets.

## Validation

```sh
lake build source-ixby-symbolic check-ixby-symbolic ixon-to-ixby ixby-run
lake exe check-ixby-symbolic \
  --fixture .lake/build/bin/source-ixby-symbolic \
  --runner .lake/build/bin/ixby-run \
  --compiler .lake/build/bin/ixon-to-ixby
nix build .#checks.x86_64-linux.ixby-symbolic
```

The reviewed matrix has 44 programs: 24 focused open IxIR₀ cases, 12 generated
call chains, five checked open Ixon functions, and three unchanged upstream
Ixon exports. A certificate is constructed before each program's input loop.
The gate covers 576 reference executions and 203 canonical executions, including
fresh standalone reference-runner processes. It compares complete artifacts
from two fresh producers and three generic catalog CLI certifications.

Thirty rejection cases include opaque input inspection, strict evaluation of
unused arguments, function results, divergence, fuel/depth/capacity boundaries,
input representation errors, changed parameter/capture ordering, changed
constructor identity/arity, incorrectly bound canonical input, and malformed
input bytes. Seven additional program/profile/input corruptions must fail in
the standalone runner. The expected source/image/result and run digests are
reviewed fixtures; they are not used as proof premises.
