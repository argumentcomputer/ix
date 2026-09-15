# Source contracts for the Aiur frontend

The frontend elaborates binder annotations into source contracts and resolves
their occurrences before canonicalization or sharing. It supports usage,
bound-value ownership, declaration region parameters, and measure proposals.

**Current boundary:** syntax, source binding, declaration telescope consistency,
persistent registration, and pure input export. Resource/borrow checking, the
Aiur DSL, Ixon contract emission, and artifact export remain subsequent work.
Both production environment compilers reject marked source before emission.
`compileLeanInput` also rejects contracts supplied separately from source
markers, after validating the explicit input.

## Pure input boundary

`Ix.Compile.CompileInput` contains selected `(Name × ConstantInfo)` entries, an
explicit array of `SourceContract` records, and optional `MeasureHint` records.
The semantic contract array has no default. `CompileInput.plain` is the explicit
convenience constructor for ordinary source without contracts.
Resolution rejects that constructor's result if the source contains annotations.

`CompileInput.resolve` validates this data without accessing a Lean environment:

- Selected names must match their constants and be unique.
- Each contract names a selected declaration through an exact source snapshot.
  Comparison includes the type, body, universe parameters, declaration fields,
  binder information, names, and metadata. A hash match alone is insufficient.
- A binder site is a type/body root and a structural expression path. It must
  identify an actual lambda or forall. Names and source offsets are not site IDs.
- Repeated sites, conflicting type/body usage, input ownership or region bounds,
  result ownership attached to a lambda, and unsupported telescope
  correspondences fail with a structured `SourceContractError`.
- Result ownership applies separately to each arrow. An unspecified result is
  shared; an unspecified binder usage is many. An implicit binder is not
  automatically erased.
- Bound-value ownership (`owned`) is independent of arrow-result ownership
  (`resultOwned`). Region references must name distinct declaration parameters
  and resolve to indices in binding order.
- Resolved records are sorted by declaration name and structural site, making
  registration order irrelevant to their presentation. Production semantic
  addressing must still be determined after actual mode emission.

Resolved records are data, not resource-validity proofs. This checker does not
establish linear use, unique ownership, nested function-type correspondence,
termination, source typechecking, or erasure safety. A compiler must validate its
accepted fragment and transport or reject every explicit contract through its
rewrites before emitting an artifact.

## Registering and exporting

`SourceContract.ofTelescope source requests` expands declaration shorthand to
separate type and body sites. Selectors can use a zero-based position or an
unambiguous binder name. Positions count implicit and instance arguments.
Metadata wrappers are traversed explicitly; the resolver does not normalize
types or bodies. In particular, a function alias requiring normalization to
expose a lambda receives `missingBodyBinder`.

For a closed identity declaration, this request specifies the first binder as
linear and its arrow result as unique:

```lean
SourceContract.ofTelescope source #[
  { binder := .position 0, uses := .linear, resultOwned := some .unique }
]
```

The resulting type site is `⟨.type, []⟩` and body site is `⟨.body, []⟩`. The
body site carries no result ownership. Selecting the second argument of a curried
declaration changes only that arrow's result ownership.

`registerSourceContract` and `registerMeasureHint` add checked records to
persistent environment extensions. Disjoint contract patches accumulate.
Imported patches are retained rather than overwritten by declaration name,
allowing `compileInputFromEnv env selected` to detect conflicting imported
registrations. It exports only the selected declarations' records and runs the
pure validator before returning the input.

Compiler loading must use the full-content Lean environment, including opaque
bodies and imported declarations. The imported-module fixture tests this in a
separate Lean process; annotations are not reconstructed by rerunning the
producer module's registration commands.

## Measure proposals

Measure hints carry a source snapshot, a selector resolved to an elaborated
input position, and an optional positive fixed-step proposal. Each declaration
has its own position; a single raw index is not shared across mutual members.
The hint adds no runtime argument, performs no decrement, and certifies neither
termination nor a target cycle bound. Measure hints remain separate from the
semantic binder contract array and can be registered on annotated declarations.
A production regression checks that a hint-only change preserves ordinary bytes.

## Surface syntax

The implemented usage spellings are `(0 x : A)` for erased, `(1 x : A)` for linear,
`(& x : A)` for affine, and `(x : A)` for many. `&` is the selected affine marker.
Import `Ix.Compile.SourceContract.Elab` to enable the syntax:

```lean
import Ix.Compile.SourceContract.Elab

regions 'a in
def keep (!&'a x : @& Nat) : Nat := x
```

The selected ownership spelling is `!` before the variable name, with shared
ownership implicit. Prefix components appear in ownership, usage, region order:

```lean
(! x : A)       -- unique, unrestricted use
(!1 x : A)      -- unique, exactly one use
(!& x : A)      -- unique, at most one use
(!&'a x : A)    -- unique, at most one use, bounded by region a
(&'a x : A)     -- shared, at most one use, bounded by region a
('a x : A)      -- shared, unrestricted use, bounded by region a
```

All these annotations belong to the binder. A region bound is independent of
ownership; a region-bounded value need not be a shared loan. Syntax does not
create a loan or establish uniqueness by itself. The annotation group is compact
and is separated from the variable name by a space, including `(! x : A)`.

The parser supports `def` header binders in explicit `(...)`, implicit `{...}`,
strict implicit `⦃...⦄`, and named instance `[...]` forms. Each annotated binder
has one name and an explicit type. Ordinary binders can be mixed with annotated
ones. Inferred return types, auto-implicit parameters, dependent binders, private
definitions, and declaration attributes are covered by fixtures. Annotations on
`fun`, `forall`, `let`, and other declaration commands remain unsupported.

`regions 'a 'b in <command>` introduces an ordered parameter table for that
command. Nested commands extend the table, which is restored afterward.
Duplicate parameters and unbound uses are errors. This introduces region
parameters, not a runtime borrow operation or lexical loan scope. Ordinary Lean
character literals and identifiers named `regions` retain their ordinary syntax.

Binder ownership requires a richer contract than the current Ixon v2
arrow-result field: `! x` must not silently set the ownership of the function's
result. Result ownership syntax, lexical borrow scopes, and the portable region
representation remain design work.

Lean already accepts `(x : @& A)` as a native borrowing annotation. Since Lean
4.30, the compiler can honor it on ordinary and local functions; it remains a
best-effort reference-counting hint that inference may override, not a checked
region or uniqueness contract. It stays orthogonal to our binder prefixes;
`(!&'a x : @& A)` retains the native annotation's singleton outer metadata
wrapper independently. See the
[Lean 4.30 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/).

## Region identity and alpha-invariance

Regions resolve to declaration-local indices: `regions 'a 'b in` binds `'a` at
0 and `'b` at 1. Consistently renaming the parameters and their uses preserves
the resolved assertions. Imported-module tests compare
`ResolvedSourceContract.semantics` for definitions with renamed region and term
binders, including multiple regions.

That projection contains the region parameter count, occurrence paths, usage,
input/result ownership, and indexed references. It excludes diagnostic names and
the source snapshot. Raw records deliberately retain names and the exact source
for stale-source detection; they must not become artifact hash inputs. The
projection also remains source data, with paths into the elaborated tree.

**Regions are not represented in emitted Ixon yet.** A future encoding needs
region binders and indexed references in a namespace separate from term
variables, with names kept as presentation data. Lexical borrow scopes need
binding and escape rules. Byte/address equality under alpha-renaming remains an
acceptance gate for that implementation.

## Elaboration markers

`SourceContract/Syntax.lean` parses annotated headers, and `Elab.lean` delegates
ordinary declaration elaboration to Lean. Versioned binder-domain markers use
the reserved `ix.source.binder` metadata namespace. `Marker.lean` rejects unknown
versions/fields, duplicate fields, malformed values, and overflowing modes.
Production guards detect reserved keys even if the marker is malformed.

`SourceContract.fromAnnotations` reconstructs records from actual elaborated
occurrences. Lean can preserve header metadata in the declaration type while
dropping it from generated lambdas. Pairing then requires a direct type/body
telescope with matching names, binder information, and domains. The resolver
does not infer mappings through normalization or other rewrites. Marked raw
recursor rules are explicitly unsupported.

## Validation

Run the focused build and executable behavior checks:

```sh
lake build --wfail Tests.SourceContractMain Tests.Main
lake exe source-contract-tests
cargo test --release -p ix-compile source_contract
```

The runtime suite covers mode/site expectations, repeated equal terms, curried
results, shadowed and implicit binders, source drift, conflicting records, and
measure resolution. Driver checks exercise missing or unsupported contracts and
the actual Rust FFI, including absence of output files when partial compilation
is enabled. Rust tests check deterministic rejection across worker counts and
native borrow metadata's semantic neutrality. The imported-module build gate
checks ordinary and opaque bodies, implicit/instance positions, conflicting patches,
registration accumulation, surface syntax, native borrowing metadata, invalid
syntax, and alpha-renaming of region and term parameters.

The same checks are registered with the primary `source-contract` test suite and
the dedicated `source-contract-tests` executable. They validate source-contract
resolution and export, not production Ixon mode bytes or backend certification.
