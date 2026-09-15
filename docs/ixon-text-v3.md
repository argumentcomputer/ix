# Ixon v3 text syntax

The Lean and Rust parsers use grammar version **3**. Whole files start with
`ixon 3`; missing headers and explicit older versions are rejected.
Canonical printing includes the header, a blank line between sections,
and a final newline. Standalone term parsing uses the current grammar
without a file header.

```text
ixon 3

def keep : (~!1 x : A) → ~! A := fun (~!1 x : A) => x

⊢ keep : (~!1 x : A) → ~! A
```

## Contracts

Binder prefixes use three independent axes:

| Axis | Prefixes | Default |
| --- | --- | --- |
| Quantity | `0`, `1`, `&` | Many |
| Ownership | `!` | Shared |
| Locality | `~` | Unrestricted |

Prefixes are adjacent to each other and separated from the binder name
by whitespace. Each axis occurs at most once. The parser accepts any
order; the printer uses locality, ownership, then quantity:

```text
fun (~!1 owner : A) => owner
fun (~& view : A) => view
fun (0 proof : P) => value
```

A binder group applies its input contract to every name in that group.
Bracket shapes retain the ordinary implicit/explicit information:

```text
fun {0 A : Type} (!1 x y : A) [~ instance : C] => body
```

A prefix on an unnamed instance binder is also preserved, for example
`[~ C]`.

## Arrow results

The independent result contract appears immediately after the arrow.
Results use only `!` and `~`; quantities belong to inputs.

```text
(!1 x : A) → ! B
(~ x : A) → ~ B
(~!1 x : A) → ~! B
A → ~! B
```

Arrows associate to the right. In a multi-binder group followed by one
arrow, the written result applies to the final arrow. Earlier arrows have
the shared, unrestricted result default. Nest arrows to spell each
intermediate result explicitly:

```text
(~!1 x : A) → ~! ((~& y : B) → ~ C)
```

The local interpretation and closure restrictions are specified in
[Ixon v3](Ixon-v3.md).

## Let and shared borrow

Ordinary unannotated bindings keep the compact syntax:

```text
let x : A := value; body
have x : A := value; body
```

A contracted let uses one explicit parenthesized binder. `have` sets the
non-dependent flag. `borrow` sets the shared-borrow kind:

```text
let (~!1 owner : A) := value; body
let borrow (~ view : A) := owner; body
have borrow (~& view : A) := owner; body
```

The body is the borrow's loan boundary. Ordinary locality annotations do
not create a temporary loan. Canonical printing starts the body on the
next line. The word `borrow` is reserved; a name with that spelling is
written `«borrow»`.

## Validation boundary and fixtures

The text AST retains input contracts, per-arrow results, and all let fields.
Parsing and printing do not establish typing, ownership, or loan validity.
In particular, the text grammar can represent every wire-level let
combination; the resource checker is responsible for rejecting a borrow
view whose contract is not shared and local.

The shared [contract fixtures](../Tests/Fixtures/ixon-v3/text.tsv) cover
all 16 lambda inputs, 64 dependent arrow input/result pairs, four
non-dependent arrow results, and 64 let flag/contract combinations.
Both implementations check the parsed fields and canonical text.
Property tests generate contracts throughout nested terms and files.
