# IxCertified port and growth plan

Date: 2026-09-16. Status: planning; the fresh workspace and branch exist, but
the library port has not started.

This plan establishes a separate, certified Ix library in Lean. Its first
release will preserve con-leche's complete connection from an executable
declaration checker to a set-theoretic model and relative consistency.
Subsequent work will add completed results from the Ix consistency branch,
then verified representations, Ixon codecs, source adapters, and other Ix
components. Every addition must preserve the public acceptance theorem.

The implementation may retain annotations, perform additional checks, reject
unsupported inputs, and use different data structures from the production Ix
checker. These choices are available tools for keeping the proofs tractable.

## 1. Starting points and scope

### Repository checkpoints

| Source | Pinned revision | Role |
| --- | --- | --- |
| `~/projects/ix-certified` | `main` at `cf77c957e50d64a5ed42330d3ae8c176296e7d1d` | Fresh jj workspace; branch `jcb/ix-certified`; implementation destination |
| `~/projects/con-leche` | `c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0` | Initial checker, semantics, model, complete acceptance proofs, and relevant regression evidence |
| `~/projects/ix`, branch `jcb/ix-kernel-consistency` | `ad60e5f6dd23655da79cf9898d2b6b3fefbe8658` | Completed Ix model and certificate results, concrete model construction, audits, fixtures, and selected implementation lemmas |

The destination and current Ix checkpoint use Lean `v4.33.1`; the con-leche
checkpoint uses `v4.33.0`. Preserve the destination toolchain initially and
measure the compatibility work. Toolchain changes are separate, recorded
changes with their own verification results.

The inspected con-leche tree contains 486 Lean modules under `ConLeche/`.
The first port is therefore an extraction of a substantial, coherent proof
dependency closure. It is not just the small set-theory foundation previously
copied into Ix.

The existing branch already defines a Lake target named `IxCertified`, but
that target roots at `Ix.Certified` and links `ix_rs`. The destination starts
from main and does not contain that target. The new target described here
will own the top-level `IxCertified` namespace and a separately audited
dependency graph.

### Results to preserve

The source provides several distinct results; preserve their statements and
scope when extracting them:

| Source result | What it establishes | Use in this plan |
| --- | --- | --- |
| `ConLeche.model_exists` | Success of `Cached.checkDecls .verified pins ds` constructs a model of the resulting environment, for every pin list and every supplied `SetTheory V` | Initial public acceptance theorem |
| `ConLeche.Denotes_functional` | The public denotation relation has at most one result | Public semantic specification |
| `ConLeche.Cached.checkDecls_sound` | Accepted declarations construct the stronger internal environment invariant | Proof dependency of the public theorem |
| `ConLeche.Cached.no_proof_of_False_cached` | An accepted environment contains no constant with the pinned `False` type | Environment-level consistency corollary |
| `ConLeche.no_False_theorem_accepted` | An input declaration array containing a theorem record of the pinned `False` type cannot be accepted | Input-level consistency corollary |
| `ConLeche.Cached.checkDecls_consts` and related stream theorems | Record the connection between input declarations and installed constants | Preserve source fidelity within their exact proved scope |
| `Ix.Theory.Certified.accepted_has_model`, `accepted_proof_sound`, `no_proof_of_False` | The Ix certificate validator checks its supplied witnesses and constructs the model needed for accepted proofs | Later pure certificate API |
| `Ix.Certified.LogicalReceipt.closed_subject_meaning`, `no_False` | Closed logical receipts establish the selected source subjects' meaning and relative consistency under the enforced profile | Later source and claim API after its dependencies qualify |
| `IxSetTheoryModel.carneiro_implies_ix` | The specified inaccessible-cardinal hypothesis supplies the existing Ix set-theory interface | Reuse for an instance of the exact new interface |

Con-leche's `no_False_declaration` additionally covers a particular JSON file
template through parsing and preparation. It is not a general theorem about
all byte encodings or arbitrary source transformations. The initial library
will use the declaration-array theorem; byte-level claims are separate
milestones.

### Scope of the first release

The first release consists of an executable Lean checker over its own typed
declaration representation, its semantics and model construction, the public
acceptance and no-False theorems, a concrete relative model construction,
audits, and executable examples.

The following are later work and are not prerequisites for that release:

- Equivalence with, completeness for, or consistency of main's `Ix.Tc`.
- Completion of the old branch's M2–M4 production-refinement roadmap.
- Converting the certified core to Ix's content-addressed representation.
- Full Ixon serialization, filesystem transport, and source-file fidelity.
- Performance parity with either Ix or Lean's kernel.
- Rust, IxVM, Aiur, circuit, or proof-system execution correctness.

The old branch is a source of proved components. Its unfinished method-table
contracts and execution-history infrastructure do not become obligations of
the new library merely because they exist.

## 2. Certification contract

### The public acceptance theorem

The initial theorem should retain the following source shape, after namespace
adaptation:

```lean
theorem model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (ds : Array Declaration) (env : Env)
    (accepted : Cached.checkDecls .verified pins ds = .ok env) :
    Nonempty (Model V env)
```

This is a target statement, not a declaration already implemented in this
workspace. A small public `check` wrapper may fix `.verified`; its theorem
must be derived from the exact function the API executes.

Preserve the input theorem that a `thmDecl` with the pinned `False` type
cannot occur in a successfully checked declaration array. Also expose the
environment-level theorem and the source correspondence results needed to
interpret acceptance. A theorem merely about a conveniently chosen internal
environment is insufficient as the public API contract.

No caller of the closed acceptance API should have to supply checker
soundness, annotation agreement, valid cache histories, admitted-declaration
meaning, a model of unchecked input, or a successful execution's semantic
invariants. The implementation and its proof must construct those facts.

Conditional extension APIs can remain useful. They must name their actual
preconditions and stay distinct from the closed acceptance API. For example,
extending an already modeled interface may assume that interface's model;
checking a closed input must establish its starting model itself.

### Mathematical assumptions

Consistency remains relative to an explicit `SetTheory V`. This interface
contains the set-theoretic operations and laws and a countable tower of
Grothendieck universes. The separate Mathlib construction supplies an instance
under the explicit `OmegaInaccessibles` hypothesis.

The proof audit permits Lean's standard logical axioms, `propext`,
`Classical.choice`, and `Quot.sound`, with exact sets recorded per public
root. A root may use fewer. Absence of additional Lean axioms does not remove
the theorem's explicit set-theoretic hypothesis.

Reject `sorryAx`, `Lean.ofReduceBool`, new project axioms, and unnamed
semantic premises from the certified proof closure. Audit checked theorem
types, definition bodies, and inductive constructor types; an axiom list
alone does not reveal an impossible or overly strong theorem hypothesis.

### Executable and source boundaries

The mathematical theorem is about the specified Lean functions. The Lean
kernel, compiler, runtime, and standard data representations remain the
ordinary execution foundation. Record con-leche's existing use of computed
fields and proved compiler simplifications. Do not expand that boundary by
silently linking the existing Ix Rust library or a foreign hash implementation.

Proof dependencies, imported modules, and compiled execution dependencies
need separate inventories. An optimization justified by a proved `csimp`
equation has different evidence from an unchecked `implemented_by` or an
opaque foreign function. Passing an axiom audit does not establish that a
foreign implementation matches its Lean specification.

Data supplied by a generator or witness search is untrusted input to a
validator. Its successful validation may be certified even when the search
procedure has no correctness or completeness theorem. Place such tools
outside the certified implementation unless their own advertised contract is
proved. Preserve the distinction between correctness of a checked declaration
and fidelity of a transformation from an earlier source representation.

### Coverage and rejection

Retain the supported cases and restrictions of the pinned upstream verified
checker. Unsupported features, exhausted resources, missing witnesses, and
failed checks must return a non-accepting result. No certified command may
fall back to the legacy checker and turn its verdict into certified success.

Maintain positive accepted examples alongside rejection examples. An
implementation that rejects everything satisfies a weak no-False statement
but does not satisfy this plan's functionality requirements. Soundness,
coverage, completeness, and performance are separately reported properties.

## 3. Library structure and dependency rules

### Proposed layout

The following paths are planned. Introduce optional directories only when
their corresponding component is ready.

```text
IxCertified.lean                 Small public API and theorem imports
IxCertified/
  Kernel/                       Ported names, levels, expressions, declarations, checker
  Cached/                       Ported executable cached implementation
  SetTheory/                    The shared abstract foundation and its derivations
  SetModel/                     Set constructions used by the model
  Term/                         Ported term support required by the proof
  Semantics/                    Interpretation and semantic judgments
  Model/                        Environment invariant and model construction
  Verify/                       Proofs about the executable checker
  Denotes.lean                   Public denotation and model specification
  Consistency.lean               Public acceptance and no-False theorems
  Theory/                       Later extraction of the closed Ix certificate theory
  Certificate/                  Later public certificate validation API
  Data/                         Later verified reusable representations
  Codec/Ixon/                   Later proved Ixon schema and codecs
  Source/                       Later declaration/source correspondence
  Claims/                       Later pure receipt and claim validation
Tests/IxCertified/              Proof, import, runtime, provenance, and regression gates
Tools/IxCertified/              Generators, witness search, benchmarks, and IO tools
Ix/CertifiedAdapter/            Host integration allowed to depend on ordinary Ix
Models/IxCertifiedSetTheory/    Separate Mathlib package instantiating the exact interface
docs/ix-certified.md            Public contract, feature coverage, build and trust boundary
```

Initially map the `ConLeche` prefix to `IxCertified`, retaining the internal
directory organization and declaration structure. The new `Consistency.lean`
will extract the required theorem declarations from the upstream assembly.
It need not inherit that file's unrelated frontend imports.

The later `Theory/` extraction can preserve the existing Ix model's distinct
annotated syntax under `IxCertified.Theory`. Sharing the same set-theory
foundation does not make its term semantics definitionally equal to
con-leche's. Keep the two APIs explicit until an actual bridge is proved;
neither API's theorem should depend on a speculative unification of them.

### Dependency direction

- `IxCertified` may depend on the pinned Lean/Std foundation and its own
  admitted modules. Add any other dependency through the same review and
  audit as project code.
- Its source and compiled closure must not import `Ix`, `Ix.Tc`,
  `Ix.Kernel`, `Ix.Theory.Named`, Lean4Lean verification frontiers, or
  ordinary Ix foreign interfaces.
- The executable kernel and cached implementation do not import the model
  or their correctness proofs. The proofs import the implementation.
- Audits and tests import the library. The library never imports test or
  audit roots.
- Host adapters may import both `IxCertified` and `Ix`. The reverse edge is
  forbidden. Their claims are limited to the connections actually proved.
- Mathlib stays in the separate model package. The ordinary certified
  checker and its abstract consistency theorem do not depend on Mathlib.

A separate `lean_lib` in the same Lake package does not enforce these
boundaries. Use an import-graph gate and a checked-declaration dependency
audit. A future package split is available if useful, but is not required to
obtain the first complete theorem.

Define `lean_lib IxCertified` without `moreLinkObjs := #[ix_rs]`, legacy
verification `dynlibs`, or dependencies on ordinary Ix test executables.
Use explicit roots/globs so unrelated host tools and unfinished experiments
are not included. Keep the certified target independently buildable even
though the repository also contains the existing default `Ix` target.

An unimported package requirement in the root Lake manifest is not a proof
dependency. Verify separately which packages are fetched, which modules are
elaborated, and which objects are linked; do not claim that a separate target
automatically eliminates all dependency-download work.

## 4. Source selection and migration policy

### From con-leche

Compute and record the transitive closure of the selected theorem and
execution roots. Include semantic and implementation helpers actually needed
by those roots, private declarations, meta imports required for elaboration,
and generated data required by `include_str`.

Retain the annotation discipline, scoped environments, declaration-prefix
checking, verified-mode checks, inductive admission routes, cached checker
simulation, and Nat-operation certificate validation as a unit. The current
Ix checker representations and algorithms do not constrain this first port.

Keep the pin-list parameter general. At the pinned revision the theorem is
valid for every `List NatOpPinSet`; the empty list may reduce coverage, but
does not justify a weaker soundness claim. Ship a documented pin selection
and verify its positive coverage independently.

Copy the relevant committed pin data and preserve its source identity. The
core's `Kernel/CheckerBase.lean` imports `Kernel/NatOpPins.lean`, whose meta
loader and relative `include_str` paths also need to be handled. Moving only
`.lean` files is insufficient. Toolchain-specific regeneration and freshness
checks must use the toolchain the data describes.

Do not import `ConLeche.Challenge`: it deliberately contains `sorry` and is
outside the original theorem's closure. Historical experiments, arena
artifacts, upstream task journals, and unrelated tool frontends are not
library dependencies.

The upstream main-theorem assembly imports frontend modules for its file
corollary. Extracting the declaration-level results first avoids bringing
the parser, projection rewriting, and model generators into the public
certified boundary before their exact contracts have been classified.

### From `jcb/ix-kernel-consistency`

| Component | Intended treatment | Qualification needed |
| --- | --- | --- |
| `Ix/Theory/Model/SetTheory`, `SetModel` | Compare with the new foundation and reuse matching definitions/proofs | Verify source revisions and definitions; no silent second meaning of `SetTheory` |
| `Models/SetTheory` | Adapt the concrete construction to the exact new foundation | Audit the new bridge and retain the explicit cardinal hypothesis |
| `Ix/Theory/Certified`, required syntax/model modules | Port a complete pure validator and its theorem closure | Construct models from actual validation; preserve accepted-input and annotation correspondence |
| `Ix/Theory/Certificate` search/builders | Separate proposal generation from validation | Generator output is checked; generator completeness is not implied |
| Context, substitution, level, Nat, quotient, and inductive lemmas | Reuse when they directly support an admitted component | Match actual definitions and assumptions; unused proof infrastructure is not mandatory |
| `Ix/Certified` receipts, source meaning, claims | Split pure contracts from existing Ix representations and host execution | Port only after the relevant source/codec/data dependencies qualify |
| `Ix/Kernel/Certified*` wrappers | Reimplement small adapters to the new public API where useful | Legacy module location does not make production checker success a premise of certification |
| `Ix/Compile/Verify` | Review later for reusable translation/codec proofs | Require the exact source/target specification and complete transitive proof closure |
| Provenance, axiom/runtime audits, frozen fixtures | Reuse their mechanisms and relevant evidence | Recompute for the new namespace and roots; test the audit machinery itself |
| General production `Verify/Consistency` contracts and histories | Leave on the old branch | They are unnecessary for the con-leche acceptance theorem |
| `Ix.Theory.Named`, old sorry frontiers, VM pilots | Exclude from the certified closure | Any later use needs its own completed contract and explicit scope |

The old branch's `CheckedTyping.annotations_not_determined` and
`sameRaw_not_conversion` results are architectural lessons: checked formation
or identical erased syntax does not imply interchangeable binder annotations.
Preserve the annotations justified by the new checker's actual operations.
Do not reinstate the refuted uniform annotation premise under a new name.

### Provenance and transformation discipline

For each imported file record the repository, full revision, original path,
source SHA-256, destination path, destination SHA-256, license, and a short
description of transformations. Record non-source assets and generators too.
Maintain separate entries for imported and newly authored modules.

Preserve con-leche's Apache-2.0 license and attribution and the existing Ix
port notices and licenses. The old Ix foundation came from con-leche
`86cd20a65660d757cedc81561a44579099b565d0`, not the new pinned revision;
compare those definitions before deduplicating or claiming identical origin.

Separate mechanical namespace/import/path changes, toolchain compatibility
changes, and algorithm changes into reviewable checkpoints. Record the
theorem statements and assumptions before and after each semantic change.
Distinguish Lean module/declaration names from names represented as data inside
the checked language or serialized pins. A namespace rewrite must not silently
rewrite those payloads or change the declarations the certificates describe.
Avoid importing the entire old branch or carrying its unrelated changes to
main into the fresh workspace.

## 5. Milestones and dependencies

| Milestone | Outcome | Depends on | Status |
| --- | --- | --- | --- |
| P0 | Reproducible source inventory and build/audit scaffold | Existing fresh workspace | Not started |
| P1 | Complete ported checker acceptance and no-False theorems | P0 | Not started |
| P2 | Stable public API, concrete model, and first certified release | P1 | Not started |
| P3 | Closed Ix certificate theory and validators | P2 | Not started |
| P4 | Verified Ix representations and source translation | P2; selected P3 results as useful | Not started |
| P5 | Verified Ixon schema and serialization | P4 data definitions | Not started |
| P6 | Source/claim adapters with composed acceptance meaning | P3–P5 for the selected API | Not started |
| P7 | Additional components and performance improvements | Relevant preceding component | Not started; recurring after P2 |

The first delivery is P0–P2. P3–P7 extend a library that already has its
headline theorem. Work on independent later components may overlap, but no
later milestone is allowed to make the initial theorem contingent on it.

### P0 — Establish reproducible inputs and the gates

1. Record the source checkpoints above in a machine-readable port manifest.
   Verify the source trees and distinguish committed input from local edits.
2. In a disposable checkout of con-leche, reproduce the selected upstream
   build, axiom guards, proof-dependency report, and relevant verified-mode
   fixtures on `v4.33.0`. Preserve logs and exact commands. Existing source
   guards are evidence to reproduce, not a substitute for this baseline run.
3. Inventory the closures of `model_exists`, `Denotes_functional`,
   `checkDecls_sound`, the environment/input no-False roots, and relevant
   declaration-fidelity results. Inventory runtime and generated-data inputs
   independently of proof dependencies.
4. Add the `IxCertified` Lake target, explicit module selection, test and
   audit targets, and a dedicated gate. Keep Rust and legacy verification
   targets outside its dependency graph.
5. Establish source/provenance checks, exact axiom and theorem-type reports,
   import rules, and compiled-dependency reporting. Initially incomplete
   required root sets must fail; an empty scaffold is not a certified release.
6. Reproduce the selected core on the destination `v4.33.1` toolchain during
   P1. Keep the source baseline and the compatibility changes distinguishable.

The imported audit scripts need review. In the pinned upstream
`tests/layering.sh`, the model classifier returns `model`, while the base-edge
predicate compares against `P`. Reusing that predicate unchanged would miss
its intended class of violations. Implement the intended classification and
add a test that deliberately introduces a forbidden edge and observes failure.
Similarly test missing theorem roots, unexpected axioms, constructor-field
dependencies, private dependencies, and runtime replacements. Audit scripts
can have bugs even when the theorems they inspect are sound.

**Exit criteria:** reproducible source selection and baseline evidence; an
independent build target; functioning negative tests of the audits; no
unexplained imported modules or executable dependencies. The source baseline
must be measured before freezing the destination's expected reports.

### P1 — Port the complete checker and its proof

1. Port the selected kernel, cached implementation, set foundation, semantics,
   model, and verification modules in dependency order. Start with namespace,
   import, module visibility, and asset-path changes.
2. Preserve the upstream representations and algorithms, including binder
   annotations and certification checks. Keep definitions, theorems, opaques,
   inductive admission, quotient handling, and enabled primitive reductions
   within the same proved configuration.
3. Bring over the cached-to-core simulation and the installed/fully-checked
   environment correspondence. The public theorem must cover the executable
   cached fold, not just a slower reference function with an unproved bridge.
4. Assemble `IxCertified.Consistency` with the complete model-existence,
   denotation-functionality, environment no-False, and input no-False roots.
   Extract the declaration-level proof from the upstream assembly without
   importing its file-oriented frontend solely to reuse a module name.
5. Preserve the relevant input-to-installed-declaration results, including
   declared type and universe information and the handling of source axioms.
6. Port representative positive and adversarial declaration fixtures.
   Exercise the actual verified cached fold and pin configuration. Include
   accepted definitions/theorems, dependent binders, universe instances,
   supported inductives, quotient cases, primitive reductions, and rejection
   of malformed declarations, illicit axioms, and invalid annotations.
7. Run the strict build and all proof/import/runtime/provenance audits. Compare
   statements and behavior with the pinned source, explaining any divergence.

Keep `.trusted` out of the certified public entrypoint. If preserving the
upstream internal mode datatype is the least disruptive port, the public
wrapper fixes `.verified`, and every certified result is indexed by that
choice. No claim extends to the unchecked mode merely because it shares code.

**Exit criteria:** success of the actual new checker constructs a model and
rules out an input theorem of pinned `False`; there are no caller-supplied
subroutine soundness or annotation-coherence premises. Required theorem roots
exist, use only their recorded logical axioms, and pass nonvacuity examples.
No project FFI or legacy checker is reached by the certified execution path.

### P2 — Publish the initial library and concrete model

1. Add a small public API with an unambiguous verified acceptance operation.
   Make the distinction between unchecked declarations, checker results, and
   evidence of acceptance visible in the API and documentation.
2. Expose the public semantics and no-False theorem without making users
   understand internal simulation or environment-invariant structures.
   Preserve stronger internal theorems for later library development.
3. Adapt the existing Mathlib construction into
   `Models/IxCertifiedSetTheory`. Instantiate the exact imported set-theory
   interface and audit the result under `OmegaInaccessibles`. Resolve version
   differences explicitly; a model of a similarly named interface is not enough.
4. Add checked examples that create declarations directly in Lean, run the
   public function, and connect an accepted result to the theorem. Document
   supported declaration forms, restrictions, errors, fuel, pin selection,
   and the source/runtime boundaries.
5. Add CI for a strict clean certified build, audits, tests, and the separate
   concrete model. Verify the build from a fresh checkout with no sibling
   repositories or copied build products available.
6. Record the initial feature matrix, proof roots, assumptions, execution
   inventory, source manifest, and baseline timings in the release docs.

**Exit criteria:** `lake build --wfail IxCertified` and the dedicated gate
work on the new repository checkout; the public theorem applies to executable
positive examples; the concrete model package builds against the exact API.
The library is useful at this point without Ixon, the old Ix checker, or a
future certificate-theory migration.

### P3 — Recover the closed Ix certificate results

The objective is to preserve the already completed certified Ix API, not to
recreate the unfinished proof about arbitrary production checker runs.

1. Extract the dependency closures of
   `Ix.Theory.Certified.accepted_has_model`, `accepted_proof_sound`,
   `no_proof_of_False`, and the required store/admission results into
   `IxCertified.Theory`. Preserve the generic reference type where possible;
   importing `Ix.Address` would prematurely import the Blake3 Rust backend.
2. Import the pure syntax, model, witnesses, validators, and admission rules
   those theorems actually use. Start from specific roots rather than the old
   umbrella, which also collects certificate search/building code.
3. Compare the old and new set-theory foundations. Reuse identical definitions
   through aliases where that preserves elaborated statements, or prove the
   small explicit interface adapter needed by the existing model. Keep
   independently audited term interpretations when their syntax differs.
4. Expose the pure certificate validator under `IxCertified.Certificate`.
   Acceptance must inspect its witnesses and construct the model; users must
   not have to trust the witness generator or supply a model of new declarations.
5. Port the completed admission coverage and associated tests, including the
   supported ordinary, standard-axiom, natural, quotient, structure, and
   modeled-inductive profiles. Record the exact supported cases and conditions.
6. Keep open-frontier model-extension theorems explicit. Derive the closed
   corollary from a checked initial interface. Preserve the logical-axiom
   policy separately: an empty structural frontier does not mean that no
   approved logical axioms were used.
7. Re-run the new audits and selected frozen fixtures. Preserve the old
   statements' meaning and assumptions under the documented namespace map.

Do not automatically import all lemmas proved during the old production
bridge. A lemma is worth porting when it supports an admitted component or
provides a useful independently specified operation. Leave old execution
histories, hash-key resources, and partial method contracts in the old tree
when the new architecture has no use for them.

**Exit criteria:** a useful pure Ix certificate validator has its own complete
acceptance, model-construction, and no-False theorems within the new library.
Its proof and execution closure contains no legacy checker or foreign Ix
representation dependency. The con-leche checker theorem remains independent
of this API. No theorem asserting equivalence of the two validators is needed.

### P4 — Add verified Ix data and source translation

Preserve con-leche's native names and annotated expressions for the initial
checker. Add Ix-facing data and partial translations around that core before
considering a change to its representation.

1. Identify the smallest pure data types needed by the next consumer:
   reference identifiers, byte strings, universe encodings, declaration
   records, and dependency stores. Introduce them under `IxCertified.Data`
   with the relevant invariants and operations.
2. Define an explicit reading relation between an Ix-facing declaration and
   the declaration the certified checker receives. Account for names or
   anonymous identifiers, level parameters, binder scope, applications,
   projections, literal expansion, sharing, and declared types.
3. Implement a partial translator and prove that success establishes this
   reading relation. Preserve each requested subject and its declared type;
   successful checking of a different generated statement is not source fidelity.
4. Treat name assignment for content identifiers as a structural encoding
   problem. Preserve reserved primitive names, distinct declarations,
   dependency references, and mutual-block identities. Prove any injectivity
   required of this encoding using the represented data itself.
5. Check dependency closure, reference bounds, and block ownership. Reject
   missing references and unsupported cycles. Support legitimate mutual or
   nested inductive groups through an already proved admission route.
6. Keep annotations computed or validated by the certified checker. An erased
   source term cannot supply unchecked annotations merely by sharing the same
   raw syntax as another checked term.
7. Compose translation correctness with checker soundness into a theorem for
   the selected Ix-facing in-memory input. State any remaining representational
   preconditions and make the actual adapter check them where feasible.

Content hashes are not globally injective. Do not add an axiom asserting that
equal BLAKE3 digests imply equal arbitrary values or byte arrays. Use structural
equality, compare stored bytes where required, or state a precise finite
collision assumption for a separately labeled authentication result. Keep the
mathematical meaning of the actual checked payload independent of an implicit
cryptographic assumption.

**Exit criteria:** success of the new adapter establishes meaning for the
specified input declarations and subjects. Tests include distinct identities,
malformed references, shadowing/reserved-name attempts, universe mismatches,
incorrect block ownership, and positive shared-dependency examples. Any
unsupported input shape declines explicitly.

### P5 — Formalize and promote Ixon serialization

Port codecs in useful increments, each with a precise byte-level contract.
Begin with the data needed by one complete certified use case; expand to full
environment serialization after the component codecs compose.

1. Write down the supported wire schema and version. Specify tags, lengths,
   integers, byte order, strings where applicable, references, sharing,
   recursive groups, and complete-input framing.
2. Implement or extract pure Lean encoders and total/appropriately bounded
   decoders over the qualified data types. Existing foreign serialization or
   byte-conversion code remains a host implementation until its own refinement
   is proved. Reuse existing codec lemmas only against the exact definitions.
3. Prove encoder/decoder agreement for every supported well-formed value:
   `decode (encode x) = .ok x`, with explicit bounds if the format imposes them.
4. Prove successful decoding establishes the format's structural invariants.
   Prove canonical re-encoding where canonical input is required; reject
   noncanonical alternatives or specify their normalization explicitly.
5. Prove full-input consumption. Handle truncation, out-of-range tags,
   overflowing lengths, invalid references, duplicate or inconsistent entries,
   and trailing data according to the documented format.
6. Compose the decoded structure's reading relation with P4 and the checker.
   The result must state which declaration, type, and requested subject the
   bytes describe, in addition to the decoder round trip.
7. Compare against frozen compatible Ixon bytes and adversarial mutations.
   Use the existing Rust encoder/decoder for differential evidence where
   useful, while keeping that testing role distinct from a refinement proof.
8. Move the completed pure modules to `IxCertified.Codec.Ixon`. Ordinary Ix
   may then call those implementations, retain an external optimized backend,
   or provide compatibility wrappers, according to their proved contracts.

Fuel and parser limits may reject otherwise valid encodings; document that
coverage boundary. Successful decoding must not require the caller to assume
that an unchecked parser read the intended value. Resource-limit and error
handling changes must preserve the non-accepting outcome on failure.

**Exit criteria:** the selected Ixon format has proved structural and
byte-level contracts, executable accepted/rejected examples, and a composed
statement connecting accepted bytes to their checked declaration meaning.
Only the completed codec subset is included in the certified public API.
The remaining serialization features stay ordinary Ix components.

### P6 — Rebuild source receipts, claims, and host integration

1. Extract the pure receipt and claim structures and their meanings from
   `Ix.Certified`. Port membership, revelation, and logical claims only under
   their respective proved contracts. Evaluation claims remain separate work.
2. Port validators using the new data, source, and codec APIs. Preserve source
   subject coverage, original declared types, dependency closure, the exact
   primitive profile, checked model companions, and the logical-axiom manifest.
3. Require claim envelopes to bind the applicable format/checker/profile
   versions and the exact interpreted payload. Check version compatibility;
   do not accept an envelope under a different policy by accident.
4. Recover the equivalents of `closed_subject_meaning`, `LogicalReceipt.no_False`,
   and the pure command's acceptance-to-receipt theorem. Trace every premise
   through the actual validator, rather than assuming a receipt supplied by
   the host is authentic or semantically valid.
5. Add byte-oriented acceptance composition using the P5 codecs. Distinguish
   the theorem about actual bytes from any external claim that a digest
   uniquely identifies them. A hashing specification, backend refinement,
   and cryptographic collision assumptions are different obligations.
6. Place IO, filesystem access, legacy lazy stores, witness search, and any
   remaining FFI in `Tools/IxCertified` or `Ix/CertifiedAdapter`. Check every
   supplied object required by the pure API; cached or loaded state must not
   manufacture certified acceptance without validation.
7. Port the relevant frozen source/claim corpora and adversarial tests. Retain
   source-byte comparisons, substituted statements, forged witnesses,
   malformed groups, wrong versions, wrong identifiers, and dependency cycles
   within the claimed input profile. Run the actual host command when its
   command-level behavior is part of the deliverable.

The existing `ClaimCommand.run_meaning` theorem is useful source material, but
its current closure includes ordinary Ix data and the BLAKE3 foreign interface.
That closure cannot simply be relabeled as the new isolated library. Rebuild
the theorem against the qualified pure interfaces and document the remaining
host execution boundary.

**Exit criteria:** the pure source/claim API has a complete chain from decoded
input through validation to the advertised receipt meaning and closed
no-False corollary. Host commands report success only from that API's success.
Document exactly which IO and cryptographic properties remain outside the
formal result. No host fallback expands the certified acceptance profile.

### P7 — Grow the library and improve performance

Continue by promoting independently specified components: reusable data
structures, additional serialization cases, source transformations, primitive
operations, declaration profiles, and optimized execution.

Prefer replacing an expensive implementation with one that has an equality,
simulation, or successful-result refinement theorem against the certified
operation. That theorem must cover the actual state and configuration used by
the caller. For caches, establish the origin and validity of entries through
their operations; do not assume arbitrary populated caches are correct.

Keep proof-oriented annotations and extra checks until their removal is
justified. Removing a check can change accepted programs even when it improves
benchmarks. Prove the new successful-acceptance theorem, then measure coverage
and performance independently.

For hashing and memoization, preserve structural identity or make the exact
finite collision condition explicit. For primitive accelerations, establish
the admitted operation's defining equations before enabling the shortcut.
For a foreign or VM implementation, prove the relevant refinement before
giving it the pure operation's certification claim.

Measure accepted workloads, rejection workloads, memory use, and cold/warm
cache behavior. Use retained baseline inputs and record configuration. A speed
improvement is not a reason to enlarge the logical or runtime trust boundary.

**Exit criterion for each addition:** its applicable promotion contract below
is complete, the public theorem still builds and applies, audits have no
unexplained changes, and tests cover the new externally observable behavior.

## 6. Promotion requirements

Certification attaches to a defined operation and its specification. It does
not follow from a directory name, absence of local `sorry`, or a count of
proved lemmas. Low-level components need their relevant correctness property;
they do not each need a separate logical consistency theorem.

| Component | Required mathematical contract |
| --- | --- |
| Data representation and operations | State/representation invariants and the advertised operation semantics |
| Equality or lookup used for checking | Successful equality/lookup identifies the intended object; hash equality alone is insufficient |
| Cache or optimized operation | Preservation/simulation relative to the certified operation and its admitted state invariant |
| Encoder/decoder | Supported-value round trip, successful decode validity, framing/canonicality as required, and source reading when used for acceptance |
| Source translator or compiler fragment | Successful translation preserves the stated source-to-target relation, including declared types, scopes, references, and subjects |
| Declaration/certificate validator | Successful execution constructs the required checked object and model or model extension |
| Witness/model generator | Outputs are treated as proposals; move the generator itself only when its advertised separate contract is proved |
| Claim validator | Accepted receipts establish the exact claim meaning under the recorded policy and assumptions |
| Foreign/backend implementation | A proved correspondence to the operation used in the mathematical theorem; otherwise an explicitly external backend |

Every promotion record contains:

1. The component's public API, supported inputs, and exact correctness theorem.
2. Its implementation and proof roots and their transitive dependencies.
3. Its explicit mathematical, representation, configuration, and runtime
   assumptions, and where executable validation establishes preconditions.
4. Provenance and the difference from any upstream implementation.
5. Relevant positive and adversarial verification results.
6. The composition point into the existing public semantics or acceptance API.

Library-internal helpers can be justified as part of their enclosing proved
algorithm; separate tautological theorems for every helper are unnecessary.
An exported new behavior needs a meaningful contract. Unfinished experiments
stay outside the certified module inventory and public imports.

## 7. Verification and continuous integration

Introduce the following targets and commands during implementation. They are
planned interfaces, not commands available in the fresh workspace today.

| Proposed command | Purpose |
| --- | --- |
| `lake build --wfail IxCertified` | Build the admitted library and public theorem roots strictly |
| `lake build --wfail IxCertifiedAudit IxCertifiedTests` | Build declaration/import/runtime audits and selected proof/executable tests |
| `lake run check-ix-certified` | Run the required certified build, audits, provenance checks, and supported regression suites |
| `lake run check-ix-certified --with-model` | Also build the separate Mathlib model package and its axiom guard |

Keep the spelling distinct from the old branch's `check-certified` adapter
gate. The new gate is about the new library's actual roots and cannot delegate
its success to an unrelated legacy target.

### Required evidence

- **Checked statements and logical dependencies:** every required root exists;
  record its elaborated type and exact axiom set. Traverse definitions and
  constructor fields as well as proof bodies. Include prerequisite predicates
  whose fields could hide a semantic assumption.
- **Module boundaries:** measure transitive imports, including public/private,
  meta, and `import all` forms. Reject the forbidden legacy dependencies and
  verify implementation/proof/test layering. Use parsed or elaborated module
  information where practical; a source scanner must have negative tests.
- **Runtime closure:** inventory compiler workers, computed fields, `csimp`
  replacements, `implemented_by`, unsafe/opaque execution, and foreign symbols
  reached by the actual public operations. Distinguish inherited Lean runtime
  mechanisms from new project execution dependencies.
- **Provenance and generated assets:** check complete source inventories,
  source/destination hashes, licenses, pin data, generator versions, and
  embedded file paths. A missing source or asset fails the gate.
- **Behavior:** run accepted controls and relevant rejections through the
  actual exposed operation. Include configuration/default-mode checks, pin
  variants, primitive declarations, annotations, and adversarial witnesses.
- **Concrete model:** check the exact foundation interface and retain the
  cardinal hypothesis in the theorem type.
- **Reproducibility:** run a clean checkout build at major milestones. Normal
  incremental builds must not rely on oleans, absolute source paths, or assets
  left in either sibling workspace.

Freeze expected reports only after inspecting measured results. Dependency
additions and removals both require an explained update; automatically
regenerating a manifest to make a failing gate pass defeats the audit. Preserve
exact theorem assumptions when moving or renaming roots. Root counts measure
inventory, not proof completion.

Use focused checks while developing a component and run the complete relevant
gate at each checkpoint. Broaden host regression testing when changing shared
data, Lake configuration, codecs, or host adapters. The initial isolated port
does not require repeated execution of the old unfinished checker proof gate.

## 8. Managing changes and scope

### Checkpoint contents

Each completed checkpoint should record:

- The revision and source manifest, plus the exact new public behavior.
- The theorem statements, assumptions, and component coverage established.
- The commands and authoritative final results used to verify it.
- Import, axiom, execution, and generated-data inventory changes.
- Remaining limitations and the next specific milestone.

Keep the branch based on main and integrate later main changes selectively
when needed. Preserve the original `ix` consistency workspace as reference
material. Do not rewrite its historical checkpoints to make the new library
appear to have completed the abandoned production-refinement objective.

The repository ignores `plans/` by default. Keep this roadmap versioned with
a narrow ignore exception; keep transient logs and scratch artifacts ignored.
Place durable public contracts and release instructions in `docs/` as the
implementation reaches them.

### Responses to common problems

| Problem | Response |
| --- | --- |
| A mechanical port fails on Lean `v4.33.1` | Isolate the compatibility fix, retain theorem statements, and compare with the source-toolchain baseline |
| A source file pulls in a large frontend or unverified tool | Select narrower theorem roots or split the assembly; preserve complete proof dependencies |
| An old Ix component imports legacy checker/FFI code | Separate its pure interface and proofs first; leave the host component outside the library |
| Two models use similar names with different definitions | Keep their interpretations explicit; reuse only through definitional equality or a proved adapter |
| A proposed optimization requires new metatheory | Retain the existing proved implementation and defer the optimization |
| An audit passes despite a known forbidden dependency | Repair the audit and add a failing control before accepting its report |
| A theorem needs an unproved callback/invariant premise | Keep the feature outside the closed acceptance API until that premise is derived |
| A wire format or source transformation lacks full fidelity | Expose only its completed subset and make unsupported cases decline |
| A host command can report success through another path | Route certified success through the public validator and prove/check that connection |

Feature restrictions are acceptable when accurately stated. Weakening the
meaning of the public acceptance theorem to make a feature fit is not a
completion strategy. Preserve a working certified release while larger work
continues outside its boundary.

### Decisions fixed by this plan

- Work in `~/projects/ix-certified` on `jcb/ix-certified`, starting from main.
- Use a top-level `IxCertified` library with enforced dependency rules.
- Port the con-leche implementation and its complete proof together.
- Keep representations and certification checks stable for the initial port.
- Keep the mathematical set-theory assumption explicit and provide its
  separate concrete relative construction.
- Reuse completed Ix results selectively, without resuming the old full-checker
  refinement project as a prerequisite.
- Promote only the completed, specified portions of Ixon and other components.

### Decisions resolved during the relevant milestone

- Exact imported file closure and any necessary library subdivision: P0–P1.
- Required toolchain compatibility edits and supported pin variants: P0–P1.
- Public naming of the two certified acceptance APIs: P2–P3.
- Definitional sharing or explicit adapters between their foundations: P3.
- The first useful Ix input profile and identifier representation: P4.
- The first supported Ixon wire subset and canonicality policy: P5.
- Optional host backends, cryptographic assumptions, and performance targets:
  P6–P7.

These are bounded implementation choices to record when evidence is available.
They do not require solving general Lean metatheory or imposing an early
equivalence proof between all existing Ix and con-leche representations.

## 9. Immediate execution sequence

When implementation begins:

1. Record and reproduce the pinned con-leche baseline and selected root types.
2. Inventory the full theorem/execution closure and generated assets.
3. Add the independent Lake and audit scaffold with meaningful failure controls.
4. Port one coherent dependency-ordered closure through the actual cached
   checker, model construction, and declaration-level no-False theorem.
5. Establish the public API, concrete model instance, and clean-build release
   gate. Publish the P2 checkpoint before expanding into Ix representation work.
6. Extract the already closed Ix certificate theory, then qualify the data,
   serialization, source, and claim components in the order above.

Success for the first delivery is a usable `IxCertified` library whose actual
acceptance function has a complete model-existence and relative-consistency
theorem. Success for subsequent deliveries is a larger useful API with that
same standard of proof, an explicit source/execution boundary, and no new
unproved semantic seam hidden in the public contract.
