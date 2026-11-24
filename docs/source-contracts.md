# Source contracts for the Ix frontend

The Ix source frontend maps scoped `@`-prefixed mode annotations and scoped
definition attributes directly onto the Ixon v5 mode vocabulary
(`IxCK/Ixon/Types/Modes.lean`):

- `Ixon.BinderMode` (7 modes)
- `Ixon.ResultMode` (4 modes)
- `Ixon.AllMode` (`BinderMode × ResultMode`, 28 modes)
- `Ixon.LetMode` (8 modes: 7 value `let` modes + `.borrow`)
- `Ixon.FieldMode` (`inherited` or `shared`)
- `Ixon.DefAsserts` (`unrestricted`/`noRc`/`noAlloc` × `boundedStack`, 6 values)

The source frontend resolves exact binder occurrences, constructor field modes,
and definition assertions before canonicalization and sharing. Persistent
registrations and annotations survive imports.

## Activation and lexer hygiene

```lean
import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes
```

All parsers and attributes are declared `scoped` under `namespace Ix.Modes`.
Importing `Ix.Compile.SourceContract.Elab` without `open scoped Ix.Modes` adds
no global parsers and activates no attributes.

Every `@`-keyword uses
`atomic ("@" >> checkNoWsBefore "no space after @" >> nonReservedSymbol w)` and
every attribute uses `nonReservedSymbol`, adding **zero** entries to Lean's
`TokenTable`. Identifiers and standard Lean syntax such as `@unique_fn`,
`@uniqueId`, `@id Nat x`, `(@unique x : @& Nat)`, `(unique x : Nat)`,
`let @Prod.mk _ _ a b := p`, and `let borrow v := owner + v` continue to parse
and elaborate identically while `open scoped Ix.Modes` is active.

## Mode table (1-to-1 bijection with `Ixon.Types.Modes`)

### Binder modes (7, composable, order-insensitive)

| Surface syntax | `Ixon.BinderMode` | Wire code |
| --- | --- | --- |
| *(unmarked)* | `.many` | 0 |
| `@borrowed` | `.borrowed` | 1 |
| `@unique` | `.unique` | 2 |
| `@unique @borrowed` / `@borrowed @unique` | `.uniqueBorrowed` | 3 |
| `@once` | `.once` | 4 |
| `@once @borrowed` / `@borrowed @once` | `.onceBorrowed` | 5 |
| `@erased` | `.erased` | 6 |

Supported in `(...)`, `{...}`, `⦃...⦄`, and `[...]` binders, including
multi-name groups (`(@unique x y : T)`) and optional `: T` in `fun`
(`fun (@unique x) => x + 1`). Illegal combinations (`@erased` with any other
mode, `@once @unique`, duplicates) are rejected with explicit elaborator errors.

### Result modes (4)

| Surface syntax | `Ixon.ResultMode` | Wire code |
| --- | --- | --- |
| *(unmarked)* | `.shared` | 0 |
| `@borrowed` | `.borrowed` | 1 |
| `@unique` | `.unique` | 2 |
| `@unique @borrowed` / `@borrowed @unique` | `.uniqueBorrowed` | 3 |

Supported after `:` in `def`, `abbrev`, `opaque`, and `axiom`, after `→`/`->`,
and after `∀ ...,`. Input modes stay bracketed (`(@borrowed x : α) → @unique β`)
so `A → @unique B → C` parses unambiguously as `A → (@unique (B → C))`.

### `let` and `do`-block `let` (8, unparenthesized, optional `: T`)

- `let x := e` → `.value .many` (0)
- `let @borrowed x := e` → `.value .borrowed` (1)
- `let @unique x := e` → `.value .unique` (2)
- `let @unique @borrowed x := e` → `.value .uniqueBorrowed` (3)
- `let @once f := e` → `.value .once` (4)
- `let @once @borrowed f := e` → `.value .onceBorrowed` (5)
- `let @erased h := p` → `.value .erased` (6)
- `let @borrow v := owner` → `.borrow` (7)

All 8 forms work in both expression `let` and `do`-block `let`, with or without
`: T`.

### Structure & inductive fields

```lean
structure Box (α : Type) where
  @shared item : α
  @erased inv : True
  count : Nat

inductive Tree (α : Type) where
  | leaf
  | node (@shared label : α) (@erased proof : True) (left right : Tree α)
```

- `@shared`: lowers to `FieldMode.shared` in `Ixon.Constructor.fieldModes`
- `@erased`: lowers to `.erased` on the constructor's binder in `c.binders`
- *(unmarked)*: `FieldMode.inherited`

Combining `@shared` and `@erased` on the same field is rejected.

### Definition assertions (6)

Native scoped Lean 4 attributes under `open scoped Ix.Modes`:

- `@[no_rc]` → `{ alloc := .noRc, boundedStack := false }` (code 1)
- `@[no_alloc]` → `{ alloc := .noAlloc, boundedStack := false }` (code 2)
- `@[bounded_stack]` → `{ alloc := .unrestricted, boundedStack := true }` (code 4)
- `@[no_rc, bounded_stack]` → code 5
- `@[no_alloc, bounded_stack]` → code 6

Rejected on `theorem`, `partial`, `unsafe`, and non-definition declarations, as
well as on conflicting (`@[no_rc, no_alloc]`) or duplicate attributes. Wired
through `Registry` → `Transport` → `CompileM` into `Ixon.Definition.asserts`.

## Pure input, markers, and verification

- `ix.source.binder` markers use schema version 4 (direct v5 codes).
- `ix.contract` semantic transport frames use schema version 4 (direct v5 wire
  codes across `.lam`, `.all`, `.letE`, `.field`, `.defAsserts`).
- `source-contract-tests` verifies `TokenTable` cleanliness, scoped activation,
  positive & negative syntax/elaboration, import persistence, resolution, and
  compilation with `ModeCheck`.
- `IxTests resource-modes` verifies end-to-end compilation of binders, `let @borrow`,
  constructor `fieldModes`, definition `asserts`, `BinderData.strip`/`apply`
  roundtrips, and `IxCK.Resource.check`.
