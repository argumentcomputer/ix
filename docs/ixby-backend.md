# Ixon → Ixby

The [experimental typed Lean frontend](ixby-lean.md) is a separate entry point
for retained monomorphic LCNF. Its reference execution tests do not extend the
certificates of the checked Ixon pipeline described here.

Compilatrix has a backend for the pure functional Ixby reference machine from
[`jcb/ixby` at `4fdbf4084516ce1a29f6753a20d797334d7fadbb`](https://github.com/argumentcomputer/ix/tree/4fdbf4084516ce1a29f6753a20d797334d7fadbb/Ix/Ixby).
It compiles checked Ixon through IxIR₀, without ownership lowering. The source
modules, canonical codec, profile, and pure BLAKE3 implementation are vendored
unchanged under [`vendor/ixby`](../vendor/ixby/README.md). The upstream toolchain
is 4.33.1; these exact modules also build with this repository's pinned 4.33.0.

## Entry points

`Ixby.compileIxon` checks usage, obtains the existing checked erasure and member
certificates, then compiles the exact raw IxIR₀ declarations. Its result retains
both the erasure certificate and successful lowering/admission equations.
`Ixby.compile` accepts an explicit IxIR₀ declaration list and expression instead.
Neither compiler executes the source program.

```sh
lake build ixon-to-ixby ixby-run source-ixby check-ixby

# General reference program; MAIN is a 64-digit source address.
lake exe ixon-to-ixby path/to/program.ixc MAIN new-output reference

# Canonical bytes admitted by the current upstream proving profile.
lake exe ixon-to-ixby path/to/program.ixc MAIN new-output proving

# Reproduce checked source examples and their byte artifacts.
lake exe source-ixby /tmp/ixby-examples
lake exe ixby-run \
  /tmp/ixby-examples/upstream-captureClosed/profile.ixbp \
  /tmp/ixby-examples/upstream-captureClosed/program.ixby \
  /tmp/ixby-examples/upstream-captureClosed/input.ixbi \
  /tmp/ixby-result.ixbo 100000
```

The compiler requires a new output directory. It writes the exact source
declarations/main in `source.json`, the complete reference program in
`program.txt`, and its configuration. Proving mode also writes `program.ixby`
and `profile.ixbp`. Reference mode's text is an inspection view, not a new wire
format. General execution is available through `Compiled.execute` in Lean.

The optional arguments after the mode are a runtime arity and a Nat-block
address. With arity `n`, entry evaluates the selected definition and applies it
to the `n` supplied arguments in order. The Nat-block argument configures the
existing source literal-recursor semantics; no declaration name is guessed.
Catalog ingress validates the original bytes. Blob interpretation uses the
literal occurrence's kind, canonical little-endian Nat bytes (zero is `[0]`),
and strict UTF-8. Identical raw bytes used as both Nat and String retain both
checked interpretations in the source evaluator and erasure certificate.

The Lean API is also usable without a catalog:

```lean
import Compilatrix.Ixby.Wire

open Compilatrix Compilatrix.Ixby

def identityRun : Except String Data := do
  let compiled ← compile {
    declarations := [], main := .app (.lam .many (.var 0)) (.var 0), parameters := 1 }
  let certificate ← compiled.certify #[.nat 42]
  return certificate.result
```

## Lowering and value ABI

The compiler supports all IxIR₀ expression forms, closed definitions, mutually
referencing definitions, constructors, and recursors. It preserves strict
left-to-right application and strict lets. Globals evaluate on each reference;
compilation does not memoize their values. Modes are inert at this semantic
boundary. Externs, duplicate declarations, unbound variables, missing references,
and excessive compilation work are rejected.

Lambdas become functions with explicit captured locals and one final argument.
Captures preserve the complete de Bruijn environment, including unused entries.
Constructors and recursors get a sequence of curried stages. Every source
application therefore calls an exactly saturated target function and receives
a source value, including a boxed function if more arguments remain. All global
function IDs are reserved before bodies are compiled, permitting recursive calls.

| Source value | Ixby representation |
| --- | --- |
| Erased | Private constructor, tag 0, no fields |
| Nat literal | Private constructor, tag 1, one raw Nat scalar |
| String literal | Private constructor, tag 2, one raw String scalar |
| Closure or partial application | Private constructor, tag 3, one raw PAP |
| Source constructor | Full source address as a little-endian 256-bit block, member 0, original tag, kept fields in order |

Private constructors have block zero and member 1, separating them from source
constructors. The first four constructor-table entries are these boxes. Whole
image validation rejects duplicate constructor identities. The external `Data`
ABI admits Nat, String, declared constructor trees, and erased values. It retains
full addresses and tags. Host function inputs and decoded function outputs are
outside that ABI; functions can still be returned and applied inside the program.

IxIR₀ recursors match constructors by tag and field count, including constructors
at distinct addresses. Lowering preserves that behavior. A Nat-enabled recursor
also accepts a boxed literal: its successor branch reboxes the predecessor before
entering the source rule. Literal and constructor Nats remain distinguishable.
Projection accepts source constructors and erased values; it cannot expose the
implementation fields of literal or function boxes.

Compilation has explicit work, depth, function, block, local, operand, and
constructor limits. The upstream validator checks every emitted function and
block, including unreachable code. Execution has separate transition and
continuation limits. Host input trees have a shared node budget before boxing;
data certification also bounds the output forest before decoding it.

## Canonical profile

The upstream revision-0 proving codec excludes Nat and String, including their
literals and `caseNat` instructions in unused code. `Config.crypto profile`
selects this fragment, uses the exact profile limits, rejects retained literal
expressions and host literal inputs, and emits constructor-only recursor cases.
It can compile explicit constructor Nats. General reference compilation includes
literal dispatch and uses Ixby's mathematical Nat/String semantics.

`Compiled.export profile` calls the original `IXBP`/`IXBY` codecs and decodes the
program again. It retains kernel equality between the decoded program and the
compiler image, and between the profile and compilation limits. Changing limits
at export is rejected. `Exported.certify` additionally produces canonical `IXBI`
and `IXBO` artifacts using the original byte executor. No target opcodes or wire
tags were added. The standalone runner imports the reference codec and no
compiler modules.

Admission to this reference profile does not mean admission to every upstream
prover implementation. In particular, individual proving backends may support
a smaller closure/application fragment. This change does not integrate a SNARK
prover, register a production `Claim`, or prove an external prover's conformance.

## Proof boundary

The backend distinguishes compilation from execution certification:

* `Compiled` retains the exact successful `lower` equation and upstream image
  validation. There is no general structural correctness theorem for `lower` yet.
* `Compiled.certify input` runs the unchanged IxIR₀ and Ixby evaluators and checks
  complete decoded data equality. It retains kernel proofs of both successful
  evaluations and their result correspondence. Failure, exhaustion, or a function
  result cannot produce a data certificate.
* `RunCertificate.refinement` has the upstream `ExecutionRefinement` type with
  the supplied input fixed. Target determinism covers every successful run with
  those exact inputs and limits, independently of its fuel. It does not certify
  all future arguments to an open function.
* `ByteCertificate.execution_refines` likewise covers every successful canonical
  byte execution of its exact program/input/profile and identifies the complete
  output bytes with the result tied to the checked source evaluation.
* `Compiled.certifySymbolic` adds [reusable refinement](ixby-symbolic.md) for
  programs with a finite symbolic control path and opaque data parameters.
  Its value and byte theorems cover every admitted future input without
  executing the source to certify that input. Runtime input inspection remains
  outside this fragment.
* `Pipeline.ValidatedErasure.sourcePreservation` retains the existing unbounded
  forward Ixon → IxIR₀ simulation and its sharing-well-formedness premise. The
  execution-refinement source anchor is IxIR₀'s weak CBV semantics. There is no
  reverse erasure theorem or assertion that this proves upstream `Meta.reduce`.

The twelve axiom fences distinguish ordinary logical axioms in the target, equality,
and execution proofs from the existing native BLAKE3 dependency of checked Ixon
erasure. No new axiom, native interface, `sorry`, or native-decide proof was added.
Serialized artifacts carry bytes, not persisted Lean proof objects; certification
is reconstructed by running the checkers on the exact inputs.

## Validation

`nix build .#checks.x86_64-linux.ixby` runs the complete gate. Locally:

```sh
lake exe check-ixby \
  --fixture .lake/build/bin/source-ixby \
  --runner .lake/build/bin/ixby-run \
  --compiler .lake/build/bin/ixon-to-ixby
```

The reviewed matrix includes 33 focused cases, 270 pure generated programs,
29 source/compiler/runtime rejections, and five canonical byte runs. It includes
large Nats, Unicode strings, captures, partial application, both Nat forms,
constructor identity, input order, erased absorption, checked Ixon list reversal
with sharing, and three unchanged upstream Ixon exports. Fresh processes must
produce identical complete artifacts. An independent byte inspection checks all
source constructor address/tag/arity entries. The gate rejects 35 corrupted
program/input/profile artifacts and compares three generic catalog compilations
with the source fixtures. It also checks every vendored file against the pinned
upstream inventory, including both licenses.

The upstream `addClosed` and `recClosed` fixtures still fail the existing source
certificate gate. They are recorded rejections, not claimed Ixby executions.

The [fixed Stage2 verifier fixture](ixby-stage2-fixture.md) retains the grouped
benchmark keys and complete original source closures. Full catalog admission
passes under explicit compiler budgets; checked usage and typed erasure remain
open. The separate [typed Lean frontend](ixby-lean.md) compiles a reference image
that accepts the valid proof with exact claim bytes and rejects seven invalid
cases. Canonical Nat/profile support and source/image certification remain open.
