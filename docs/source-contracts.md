# Source contracts for the Ix frontend

The Ix frontend records three independent properties: usage, ownership, and
relative locality. Aiur is one consumer of this shared frontend.

The source frontend resolves exact binder occurrences before canonicalization
and sharing. Both environment compilers preserve those contracts in Ixon v4
and run resource and erased-type validation before emitting annotated output.
Persistent registrations and annotations survive imports. The decompiler
reconstructs committed contracts independently of optional presentation data.

The [native resource checker](resource-checking.md) also implements usage,
ownership, scopes, captures, and loan checks, with shared Lean/Rust fixtures
and proofs of the executed state invariants.

The admitted source fragment includes definitions, theorems, opaque bodies,
and explicitly admitted external interfaces. Annotated inductive/constructor/
recursor generation and nonidentity compiler surgery currently report an
unsupported transformation before emission. Ordinary source keeps its existing
compilation path. Source syntax alone does not establish resource validity.

The complete semantic and binary design is in [Ixon v4](Ixon-v4.md).

## Modes

| Axis | Source prefix | Meaning |
| --- | --- | --- |
| Usage | `0` | Erased |
| Usage | `1` | Exactly one computational consumption |
| Usage | `&` | At most one computational consumption |
| Usage | Unmarked | Any number of computational consumptions |
| Ownership | `!` | Unique ownership |
| Ownership | Unmarked | Shared access |
| Locality | `~` | Confined to an implicit scope |
| Locality | Unmarked | Unrestricted escape |

`~!` combines local scope with unique ownership. Neither property changes
usage. For example, `(! x : A)` means unique ownership with unrestricted
usage; the availability check must still prevent two unique transfers.

Prefix components must be adjacent, with a space before the binder name.
Each axis may appear at most once. The parser accepts both `!1` and `1!`,
and both `~!&` and `&~!`.

## Source syntax

Import `Ix.Compile.SourceContract.Elab`:

```lean
import Ix.Compile.SourceContract.Elab

def identityLocal {0 A : Type} (~!1 x : A) : ~! A := x

def curried (x y : Nat) : ~ Nat := x + y

def localArrow : (~ _x : Nat) → ~ Nat := fun x => x

def localLambda := fun (~1 x : Nat) => x

def localBinding (x : Nat) : Nat :=
  let (~!1 y : Nat) := x
  y
```

These are declarations of intent. The source layer records their contracts;
the resource checker determines which programs satisfy them.

Annotations work in `def` headers, nested `fun` and `forall` binders,
dependent arrows, ordinary arrows with annotated results, and lets. Explicit
`(...)`, implicit `{...}`, strict implicit `⦃...⦄`, and named instance
`[...]` binders are supported. An annotated binder has one name and an
explicit type. Ordinary binders may share a type or use Lean's existing
inference.

Results use `: ~! A`, `→ ~! A`, or `∀ ..., ~! A`; any ownership/locality
combination is available, and unmarked means shared and unrestricted.
The result contract belongs to one arrow. In the `curried` example, the
intermediate function after `x` has the ordinary result contract; only the
arrow after `y` has a local result.

A lambda's input annotation is separate from its expected arrow's result
contract. Use an annotated function type to state a nested lambda's result.
A final declaration binder with a default value currently needs an explicit
arrow type for its result contract; the shorthand reports this limitation.

Ordinary definitions, attributes, private declarations, auto-implicit
parameters, native borrowing metadata, and inferred result types retain Lean's
existing behavior. Named lifetime syntax and `regions ... in` are removed.

## Scoped shared borrowing

An explicit borrow let creates a temporary shared view:

```text
let count :=
  let borrow (~ view : Buffer) := owner
  inspect view

consumeUnique owner count
```

Its initializer identifies an owner binding or supported projection path. The
view is shared and local; it cannot be unique. The inner body's scope bounds
the loan. Creating a view does not consume its owner, and uses of the view
count against the view's own usage annotation.

The resource checker suspends unique access while the loan is active,
rejects escaped views and captures, and ends the loan when the body finishes.
Unique access returns only for an owner that remains live and exclusive.
Returning an independent result from `inspect` can end the loan; returning
`view` cannot.

The frontend records this as the existing Ixon let with
`LetKind.borrowShared`. An ordinary `let (~ x : A) := value` has
`LetKind.value`: locality by itself does not create a temporary loan.

Lean's `@&` remains an independent native calling-convention hint. For example,
`(~!& x : @& A)` preserves the native singleton metadata wrapper as well as
the source contract. That hint grants no ownership or locality facts.

## Pure input and source identity

`Ix.Compile.CompileInput` contains selected `(Name × ConstantInfo)` entries,
an explicit array of `SourceContract` records, and optional measure hints.
The semantic contract array has no default. `CompileInput.plain` explicitly
selects ordinary source; validation rejects it if that source contains markers.

`CompileInput.resolve` does not consult a Lean environment. It checks:

- Selected names and declarations agree, and selected entries are unique.
- Each contract matches the complete source snapshot, including types, bodies,
  universes, declaration fields, binder information, names, and metadata.
- Each site identifies an actual lambda, forall, or let. A site consists of a
  type/body root and a structural expression path, including metadata edges.
- Sites are unique, and corresponding declaration inputs agree on all axes.
- Only arrows carry result contracts, and only lets carry a borrow kind.
- Explicit shared-borrow views are shared and local.
- Source markers match supplied records exactly, including result and let kind.
- Unsupported telescope correspondences fail before canonicalization.

Source names and offsets help validate and diagnose annotations. Resolved
semantic records use structural sites; their meaning does not depend on
binder spelling. Expected arrow domains copied into alpha-renamed lambdas
must match the original validated marker. Source snapshots themselves still
compare exactly, so renaming invalidates a previously captured snapshot.

A marker annotates only the binder it was written on: its own domain, under
its original name, or the alpha-renamed lambda at the same body-telescope
position as a marked arrow of the declaration type. Lean copies marked domains
elsewhere during elaboration: numerals and instances elaborated against a
marked parameter type, matcher motives that generalize a marked index or let,
and the packed domain of a well-founded `_unary`. Such copies annotate
nothing. A copy must agree with its original when both are in one declaration;
a copy of another declaration's marker is ignored, and transport strips every
copy. Proof bodies of theorems contain only copies. So that ignoring copies
cannot drop a written contract, the declaration command fails with
`lostAnnotation` when a marker written in it keeps no binder site in the
declaration or the auxiliary definitions it generates.

Default inputs are many/shared/unrestricted. Default arrow results are
shared/unrestricted. An implicit or instance binder is not automatically erased.

## Unfolding equations

`ix compile --equations` realizes `f.eq_def : ∀ xs, f xs = rhs` for every
recursive definition in the closure. The statement's right side is elaborated
from `f`'s body, so contracts written inside the body reach it. Only Lean's
own unfolding theorem is associated with `f`: a theorem merely named
`f.eq_def` (a metaprogram can add one past the reserved-name check) whose
statement is not the one `ix compile` re-derives from the pre-definition
Lean recorded for `f` is not associated, and the sidecar lists `f` under
`failures` with `equation not genuine` ([resource
checking](resource-checking.md), unfolding equations). `f`'s header
input contracts are carried onto the equation: the statement's binder at the
same telescope position, and the proof's matching lambda, are registered with
the same input contract (usage, ownership, locality), so the exported theorem
reads `∀ (c₁ x₁ : A₁) … (cₙ xₙ : Aₙ), f x₁ … xₙ = rhs`. Result contracts are not
carried (the statement's arrows end in an equality). The association sidecar
(`ix/compile-equations/1`) lists, for an equation that carries any, a
`contracts` array of `{position, binder, uses, owned, locality}`; an equation
whose telescope does not match is left unchanged and listed under `failures`
with `contracts not carried`. Definitions without header contracts, and so all
unannotated closures, are unchanged.

### Checked pairs

Whenever resource admission runs (the closure carries a contract) or
`--profile` is given, `ix compile` writes the sidecar after a successful
compile (to `--equations-out`, default `<out>.equations.json`, with or
without `--equations`) with three more keys. The format id stays
`ix/compile-equations/1`: the new keys are optional additions, so a reader of
the association records is unaffected. Without resource admission and
without `--profile` the sidecar is unchanged (and written only with
`--equations`).

```json
{
  "format": "ix/compile-equations/1",
  "equations": [ … ], "failures": [ … ],
  "root": "<64-hex canonical consts merkle root of the closure>",
  "resourceProfile": {
    "address": "<64-hex BLAKE3 of bytes: the profile address a resource claim binds>",
    "bytes": "<hex canonical profile bytes (docs/resource-checking.md)>"
  },
  "resourceChecked": [
    { "definition": "revAcc", "equation": "revAcc.eq_def",
      "definitionAddress": "<64-hex>", "equationAddress": "<64-hex>",
      "profile": "<64-hex, = resourceProfile.address>",
      "contracts": [ { "position": 1, "binder": "acc", "uses": "many",
                       "owned": "unique", "locality": "unrestricted" } ] }
  ]
}
```

`resourceProfile` is absent when no resource admission ran (an unannotated
closure under `--profile`); `resourceChecked` is then empty. Each
`resourceChecked` entry is a pair through which resource admission checked
a definition: the profile binds `definition ↦ equation`, the definition is
resource-relevant and not assumed. `contracts` lists the header contracts
the equation's statement carries (above), possibly none. An annotated
recursive definition is never admitted otherwise ([resource
checking](resource-checking.md), unfolding equations).

The list carries a consumer obligation (obligation (c) of [resource
checking](resource-checking.md), "Consumer obligations"): **run exactly the
bound right-hand side, fetched by `equationAddress`.** A call `f a₁ … aₙ` of
a listed definition runs as the right-hand side `rhs` of the theorem at
`equationAddress`, whose statement is `∀ x₁ … xₙ, f x₁ … xₙ = rhs`, with
`aᵢ` for `xᵢ`; recursive calls in `rhs` run the same way. It never runs as
Lean's compiled code for `f` (the `_unsafe_rec` twin), as a recompilation of
`f`'s source or of another theorem about `f`, or as `f`'s kernel body
(`brecOn`, `WellFounded.fix`). Resource safety rests on this obligation
alone: the checked program is the program that runs, whatever theorem was
bound. That only Lean's own unfolding theorem is bound (above) is defense in
depth; it also gives functional agreement with Lean's compiled code.

`ix check-equations SIDECAR CLOSURE` (`Ix.Compile.CheckEquations.verify`)
re-verifies a sidecar against its closure, in Lean, independently of the
compile: the profile bytes are a valid canonical profile hashing to the
stated address (which every entry names) and `root` is the closure's root;
the closure is admitted under that profile (resources and erased typing:
the resource claim `(root, profile)`); the entries are exactly the bound
pairs of resource-relevant, unassumed definitions, by address; each theorem
is a theorem of the closure whose statement is `∀ xs, f xs = rhs` for the
stated definition, and carries each stated contract at its position. It
exits `0` and prints the claim and the pairs, or exits `1` with the first
discrepancy.

## Registration and imports

`SourceContract.ofTelescope source requests` expands declaration shorthand
into separate type and body sites. Positions are zero-based and include
implicit and instance arguments; a name selector must be unambiguous.

```lean
SourceContract.ofTelescope source #[
  { binder := .position 0, uses := .linear,
    value := .localUnique, result := some .localUnique }
]
```

The body binder receives the input contract. Only the corresponding forall
receives the result contract.

`registerSourceContract` and `registerMeasureHint` persist validated records.
Disjoint patches accumulate; duplicate sites and conflicting imported patches
are diagnosed. `compileInputFromEnv env selected` exports only selected
declarations and validates the resulting pure input. Compiler loading needs
the full-content Lean environment, including imported and opaque bodies.

Markers use schema 3 in the reserved `ix.source.binder` metadata namespace.
Input contracts use the same four mode bits as Ixon. Results and let kinds
are explicit fields. Unknown keys, duplicate keys, invalid bits, and older
schemas are rejected; optional optimization metadata cannot replace them.

## Measure proposals and verification

`compileLeanInput` and `rsCompileInput` accept an explicit `CompileInput` and
an optional resource profile. Environment-aware compiler entrypoints also
collect persistent registrations; constant-list entrypoints collect source
annotations. The native profile FFI decodes canonical profile bytes itself.
Raw Rust FFI entrypoints reject unresolved source markers.

The intermediate `ix.contract` namespace is reserved. Its fields are consumed
into semantic binder data before output; they are not optional metadata.
Malformed frames, metadata replay that would erase contracts, incomplete
closures, and resource-invalid bodies fail before annotated artifacts appear.
See [resource checking](resource-checking.md) for profile and claim rules.

Measure hints bind an exact source snapshot to an elaborated argument position
and an optional positive fixed-step proposal. They add no runtime parameter
and certify neither termination nor a cycle bound. They remain separate from
semantic contracts; a hint-only change preserves ordinary production bytes.

The focused `source-contract-tests` target checks source identity, distinct
occurrences of equal terms, every arrow contract, syntax, imported interfaces,
native metadata, result placement, both let kinds, and rejection of unadmitted
external interfaces before artifacts are written. Syntax fixtures also reject accidental
`sorryAx` insertion. The `ixon-v4-tests` target separately exercises binary
representations, FFI, accepted compilation and decompilation,
resource admission, VM execution, interpretation, and proving.
