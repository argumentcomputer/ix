# Ix.Kernel: certified kernel roadmap

Date: 2026-09-16, status updated 2026-09-17. K0 and K1 are complete and K2
is under way on `jcb/ix-certified`. K0: the model is ported to
`Ix.Kernel.Model`, the address split and Blake3 pin bump are in, the kernel
builds as a dependency-free package (`IxKernel/`) whose import closure is
Lean core plus the kernel, the syntax carries `letE`, and `Models/SetTheory`
builds against that package with Mathlib. K1: single definitions, theorems,
and opaques are checked by a proof-carrying inference, reduction, and
conversion core (`Ix.Kernel.Infer`) and installed with their model
extension. K2 so far: ordinary inductive blocks (a family with its
constructors and recursor, in Ixon's `muts` layout) are read, validated,
installed with the ported set-theoretic construction, and their recursors
reduce (iota) through published typed rules; `False`, `True`, `And`, `Or`,
`Nat`, `List`, and `Eq` are fixtures, with `Nat.rec` computing `1 + 1 = 2`
under `Eq.refl`; structures (`Prod`, `And`, a dependent subtype) publish
projection facts with eta and iota equations, so projections type, reduce
on constructors, and constructor applications convert to their eta
expansions; the `Nat` block is recognized by its shape and published with the
`natural` fact, so literals (which name their family) type at it, convert
with the constructors, and drive recursor iota. The three public theorems
keep their K0 statements. K-like reduction for `Eq` synthesizes the
constructor from the recursor's parameters; the quotient primitives are
installed one by one with their computation rules derived from published
facts at reduction time; `propext` and `Classical.choice` are admitted over
the `Eq`, `Iff`, and `Nonempty` interfaces. Every K2 route is connected and
`lake run check-kernel --with-model` passes. Next: the differential run
against `Ix.Tc`, `docs/kernel.md`, and CI, then K3.

## Revision note

This revision replaces the earlier `IxCertified` port plan. Three changes:

1. The certified checker is `Ix.Kernel`, inside the ordinary `Ix`
   namespace. There is no separate `IxCertified` library or namespace. The
   whole `Ix` namespace is the aspiration; certification status is tracked
   per component by a ledger and enforced by audits, not by a namespace wall.
2. The model is simplified. The kernel keeps the set-theoretic model, the
   binder regime annotations, and the collapse of definitional equality to
   set equality. It drops the machinery con-leche needed around them for a
   name-based, stream-parsed, cache-simulated checker with generated
   inductive models.
3. The kernel is built on Ix-native data: content addresses and block/member
   references instead of names, positional universe parameters, de Bruijn
   terms, and Ixon's declaration shapes. Con-leche supplies proof techniques
   and regression evidence, not code to port. The old Ix consistency branch
   supplies the semantic model, which is already written in this style.

Second pass, same day, three additions: the Blake3 package now ships a pure
Lean implementation, which becomes the certified hash wherever one is
needed; `Ix.Kernel` is planned to replace `Ix.Tc` completely rather than
coexist with it; and Ixon's substructural binder modes are carried from the
start and planned as a later performance lever.

## 1. Thesis and scope

`Ix.Kernel` is a reference type checker for Ixon-shaped declarations,
written in Lean, with a machine-checked theorem that every environment it
accepts has a model in an explicit set theory, and therefore contains no
proof of `False`. It is designed for the proof first: pure functions over
small inductive types, explicit fuel, structural equality, no caches, no
hashing, no foreign code in its execution closure. Performance comes later
through promotions that carry their own simulation theorems.

### Starting points

| Source | Pinned revision | Role |
| --- | --- | --- |
| `~/projects/ix-certified` | `main` at `cf77c957e50d64a5ed42330d3ae8c176296e7d1d` | jj workspace; branch `jcb/ix-certified`; destination |
| `~/projects/ix`, branch `jcb/ix-kernel-consistency` | `ad60e5f6dd23655da79cf9898d2b6b3fefbe8658` | `Ix.Theory`: address-native set model, semantic judgments, admission constructions, closed acceptance theorems; `Models/SetTheory`: Mathlib instance of the set theory |
| `~/projects/con-leche` | `c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0` | Proof style, checker soundness techniques, inductive/Nat/quotient constructions, audit and regression practice |

The destination and the old branch both use Lean `v4.33.1`; con-leche uses
`v4.33.0`. Because code is taken from the old branch and only techniques
from con-leche, no toolchain migration is on the critical path. The old
workspace's jj working-copy change sits above the pin; compare it with the
pin before extracting anything, and record which one was used.

Sizes that shape the choices (measured on the pinned trees):

| Tree | Lines | Notes |
| --- | --- | --- |
| con-leche `ConLeche/` | 220,971 in 486 modules | `Model/` 80K, `Verify/` 70K, `Semantics/` 23K, `Kernel/` 18K, `Frontend/` 16K, `Cached/` 5K, set theory and set model 5K |
| old branch `Ix/Theory/` without `Named/` | about 27K | model 9K, set theory and set model 4K, inductive support 1K, syntax 2K, `Certified/` 10K, `Certificate/` 1K |
| old branch `Ix/Theory/Named/` | 112K | lean4lean-derived named specification; excluded |
| main `Ix/Tc/` implementation | 16K | production pure-Lean checker mirroring `crates/kernel` |
| main `Ix/Tc/Verify/` | 181K in 404 modules | sorry-bearing verification against lean4lean; excluded |

The old branch's `Ix.Theory` imports nothing from the rest of `Ix` except
one audit helper, and nothing outside Lean, Std and Batteries. It is a
self-contained address-native model with closed theorems. That is the core
this plan builds on.

### What the first release contains

- `Ix.Kernel`: syntax, environment, levels, reduction, inference, conversion,
  declaration checking, and inductive validation for the profile in section 3.
- `Ix.Kernel.Model`: the set theory interface, set constructions, total
  interpretation, semantic judgments, and model-extension constructions.
- `Ix.Kernel.Verify`: soundness of the checker against the model.
- `Ix.Kernel.Consistency`: the public acceptance and no-False theorems.
- Audits, tests, positive and adversarial fixtures, and the separate Mathlib
  package instantiating the set theory under an explicit large-cardinal
  hypothesis.

### Not prerequisites for the first release

- Ixon byte decoding, filesystem transport, claims, receipts, and any theorem
  about bytes or hashes (K3 to K5 below).
- Replacement of `Ix.Tc` (K6) and parity or refinement claims about the Rust
  kernel or the IxVM kernel.
- Continuation of `Ix.Tc.Verify` or any lean4lean-based specification.
- Mutual and nested inductives, string literals, accelerated Nat operations,
  caches, interning, and parallel checking.
- Rust, IxVM, Aiur, circuit, or proof-system execution correctness.

## 2. Certification contract

### The public theorems

Target shapes, to be fixed at K0 on a kernel that rejects everything and
preserved by every later milestone:

```lean
namespace Ix.Kernel

/-- Check declarations in order against an environment that already has a
model. Every reference must resolve to an installed constant. -/
def checkDecls (cfg : Config) (env : Env) (decls : List Decl) : Except Error Env

/-- The closed entry point: start from the empty environment. -/
def check (cfg : Config) (decls : List Decl) : Except Error Env :=
  checkDecls cfg Env.empty decls

theorem checkDecls_has_model (V : Type w) [SetTheory V]
    (m : Model V env) (h : checkDecls cfg env decls = .ok env') :
    Nonempty (Model V env')

theorem check_has_model (V : Type w) [SetTheory V]
    (h : check cfg decls = .ok env) : Nonempty (Model V env)

/-- `A` denotes the empty set in every model of `env`. -/
def Env.EmptyType (env : Env) (universes : Nat) (A : AExpr) : Prop

/-- No accepted constant inhabits an empty type. The hypothesis is semantic,
so no pinned `False` is needed; K2 proves that a constructor-free inductive
with no indices is an `EmptyType` in any sort, which gives Lean's `False`
and `Empty` as corollaries with syntactic hypotheses. -/
theorem no_proof_of_False (V : Type w) [SetTheory V]
    (h : check cfg decls = .ok env) (hr : env.toEnvironment r = some entry)
    (hA : env.EmptyType entry.universes entry.type) : False
```

The conditional theorem extends an environment that is already modeled; the
closed theorem constructs its starting model itself. Both are about the
exact function the API executes. A caller never supplies checker soundness,
annotation agreement, a model of unchecked input, a dependency order proof,
or a witness.

`Model V env` is the old branch's notion: one assignment of a set to every
reference at every universe instance, under which every stored constant is
a member of what its type denotes, every stored body denotes the constant,
and every published equation holds. Definitional equalities need no clause
of their own: an accepted `rfl` theorem `a = b` is a constant inside the
truth value of `⟦a⟧ = ⟦b⟧`, so both sides denote the same set.

### Mathematical assumptions

Consistency is relative to an explicit `SetTheory V`: membership with
extensionality, pairing, union, power set, regularity, a replacement scheme,
and a countable tower of Grothendieck universes. This is the interface the
old branch ported from con-leche; it is retained unchanged. The separate
Mathlib package supplies an instance under `OmegaInaccessibles`.

The proof audit permits Lean's standard logical axioms, `propext`,
`Classical.choice`, and `Quot.sound`, with the exact set recorded per public
root. Reject `sorryAx`, `Lean.ofReduceBool`, new project axioms, and unnamed
semantic premises from the certified closure. Audit checked theorem types,
definition bodies, and inductive constructor types; an axiom list alone does
not reveal an impossible or overly strong hypothesis.
The executable entry points carry erased proof components and therefore
report the same three axioms; the compiler's computability check is what
guarantees that none sits in a computational position.

### Execution boundary

The theorem is about the specified Lean functions. The Lean kernel,
compiler, runtime, and standard data representations are the execution
foundation. The certified execution closure contains no `@[extern]`,
`implemented_by`, `unsafe`, `partial`, or `native_decide` reached from the
public operations, and no `ix_rs`, C, or Rust BLAKE3 symbol. An `Address`
inside the kernel is an opaque 32-byte key; the kernel never hashes.

Where a certified operation outside the kernel needs BLAKE3 (address
reconstruction after K4, authentication and subject roots in K5), it calls
`Blake3.Pure.hash` from the Blake3 package at revision
`18b4b1c8937e32f88463bb8f5ee16a7b5f24fcc1` or later: a total Lean function
for one-shot unkeyed hashing whose package audits 50 proof roots for the
standard axioms only and whose module imports neither FFI backend. The C
and Rust backends stay host accelerators, tied to the pure function by the
package's differential vectors and by our own corpus tests. The binding
between bytes and addresses is then a theorem about `Blake3.Pure.hash`, not
a hypothesis; only collision resistance remains an explicit assumption where
a claim needs uniqueness, and the consistency theorem never uses it. No
axiom asserts that equal digests imply equal values.

Data produced by search or generation is untrusted input. Proof
dependencies, imported modules, and compiled execution dependencies are
inventoried separately.

### Coverage and rejection

The kernel has three outcomes: accept, reject (the input is wrong), and
decline (the kernel does not support the input and says why). Only accept
carries the theorem. Fuel exhaustion declines. No certified command falls
back to `Ix.Tc` or the Rust kernel and reports their verdict as certified.

Positive accepted fixtures accompany every feature and every rejection
fixture. A kernel that rejects everything satisfies the no-False theorem and
fails the functionality requirements. Soundness, coverage, completeness, and
performance are reported separately.

## 3. Design of `Ix.Kernel`

### 3.1 Syntax

Kernel terms are the old branch's `VExpr`/`AExpr` over `ConstRef Address`,
extended with `let`:

```lean
inductive Level | zero | succ | max | imax | param (i : Nat)

inductive ConstRef (β)
  | member (block : β) (i : Nat)          -- i-th member of a block
  | ctor (block : β) (i c : Nat)          -- c-th constructor of member i

inductive Expr (β)
  | bvar (i : Nat)
  | sort (u : Level)
  | const (r : ConstRef β) (us : List Level)
  | app (f a : Expr β)
  | lam (uses : Uses) (dom body : Expr β)
  | forallE (uses : Uses) (owned : Owned) (dom body : Expr β)
  | letE (ty val body : Expr β)
  | proj (r : ConstRef β) (i : Nat) (e : Expr β)
  | natLit (n : Nat)
```

A natural-number literal names the reference of its family (`natLit r n`,
on raw and annotated syntax alike): with content addresses the `Nat` block
is unique, and the host that produces the literal knows its address.
Typing a literal requires that family to carry the `natural` fact, which
only the exact zero/successor block receives.

The annotated form `AExpr` adds a `PropWhen` regime condition to `lam` and
`forallE` and nothing else. `letE` carries no annotation: its meaning is
substitution, and the kernel zeta-reduces before any structural comparison,
as con-leche does. Annotations never steer reduction; they are written by
inference, compared during conversion, and read by the model.

`Uses` and `Owned` are Ixon v2's substructural binder modes
(`Ix/IxonMode.lean`): usage `erased`, `linear`, `affine`, or `many` on every
binder, and ownership `unique` or `shared` on a forall's result. They are
carried as data so ingress and egress lose nothing. The first release
accepts only the conservative fragment that ordinary Lean compilation
emits, `many` and `shared`, and declines other modes; conversion compares
modes structurally; the model ignores them. Mode checking and the
optimizations modes license are K7.

There are no names, no binder info, no metadata, no free variables, no
metavariables, and no string literals in the first release. Binders are
opened by extending a context list, as in the old branch's judgments.
Universe parameters are positional, matching Ixon `Univ.var`. The kernel is
parametric in the reference type `β` where that costs nothing, and the
public API fixes `β := Address`.

### 3.2 Declarations and environment

Declarations mirror Ixon constant shapes: axiom, definition/theorem/opaque,
quotient primitive, inductive with constructors, recursor with rules, and a
block (`muts`) of members that may refer to each other by index. Ixon
projection constants (`iPrj`, `cPrj`, `rPrj`, `dPrj`) are consumed at
ingress to build an alias map from their addresses to `ConstRef` values;
the kernel checks blocks, and a reference whose address is neither a block
nor an alias rejects. Production ingress reconstructs projection addresses
by hashing; the certified ingress requires them to be supplied and only
looks them up.

The environment is an ordered, `Address`-keyed finite map: a list of
installed blocks with their addresses and an index for lookup. Checking
folds over the input in the order supplied. A reference to an address that
is not yet installed rejects; a duplicate address rejects. Dependency order
is a property of the supplied list, not of hashes, so acceptance needs no
acyclicity proof and no collision assumption. Within a block, members refer
to each other by index and are checked together.

### 3.3 Semantics and model

Port the old branch's `Ix.Theory.Model` as `Ix.Kernel.Model`:

- `SetTheory V` and the derived constructions (`SetModel`: pairs, graphs,
  dependent products `piR`/`lamR` by regime, universes, numerals).
- The total interpretation `interp constants levels env : AExpr → V` with
  the separate hereditary predicate `WellDenoted`. A total function replaces
  con-leche's `Denotes` relation; functionality is by definition.
- `Environment`, `ConstantEntry` (universes, type, optional body, published
  equations, facts), `Realizes`, `Assignment`, and `Extends`.
- The semantic judgments `TypingClaim` and `ConversionClaim`, quantified over
  every compatible assignment, with their proved rule theorems (sort, bvar,
  const, app, lam, forallE, conversion, beta, eta, proof irrelevance, delta,
  equation, literal) and the projection and equation facts published by the
  admission constructions.

The `letE` clause (interpretation by substitution) with its rules
`TypingClaim.letE` and `ConversionClaim.zeta` is in (`Ix.Kernel.Model.LetRules`).

### 3.4 Checker

The checker is a reference algorithm in the shape of `Ix.Tc` and nanoda,
written for proof. K1 built its core (`Ix.Kernel.Infer`) in a
proof-carrying style: each operation returns its result together with a
proof of the semantic claim about it, the claims are propositions erased at
run time, and the public theorems are assembled from them rather than
proved about the functions afterwards.

- `annotate` (unverified, `Ix.Kernel.Annotate`): raw terms carry no binder
  regimes; this pass computes the zero condition of every binder's inferred
  codomain sort bottom up by calling the certified operations on the
  already annotated subterms. Nothing depends on its correctness: its
  output is validated by `inferA`, so a wrong annotation is rejected, never
  accepted. This is con-leche's arrangement, an unverified annotate pass
  under a verified validator, with the validator merged into inference.
- `inferA`: infers the type of an annotated term and returns
  `TypingClaim Γ e A`. Binder cases check that the recorded regime equals
  the zero condition of the inferred codomain sort.
- `whnf`/`step`: beta, zeta, delta by unfolding stored bodies, and
  reduction under an application head, returning `ReductionClaim`. Beta is
  typed: the argument is re-inferred and converted to the binder's domain
  before the redex fires, because the set model licenses substitution only
  when the argument denotes a member of the domain, and denotational typing
  cannot recover the domain of a function in the `Prop` regime. Fuel-bounded;
  no caches; no reducibility hints. K6 may annotate applications with their
  domains so that the re-inference becomes a lookup.
  Iota (K2): a recursor applied to a constructor reduces through the rule
  the inductive route published as an equation with typed endpoints; the
  target is converted to the typed instance of the left side (which checks
  the constructor's parameters and the indices against the recursor's by
  conversion), and the equation takes it to the typed instance of the right
  side. The arities come from a `ConstantFact.recursor` on the entry.
  Structures (K2): the family entry of a structure carries a
  `ConstantFact.structure` with its arities, one typed projection fact per
  field, and the eta and iota equations. `inferA` types `proj` by applying
  the field's projection fact to the parameters and the major; `whnf`
  reduces a projection of a constructor application through the iota
  equation; `isDefEq` converts a constructor application to a term of the
  structure's type through the eta equation. For structures the rule
  endpoints are typed by inference at reduction time rather than read from
  facts.
  Literals (K2): `inferA` types `natLit r n` at `r` when `r` carries the
  `natural` fact; `isDefEq` unfolds a literal against a constructor
  application one step (`0` to `zero`, `n + 1` to `succ n`), and recursor
  iota unfolds a literal major the same way. Whole literals stay literals
  in normal forms.
- `isDefEq`: syntactic equality, then `whnf` on both sides, then structural
  comparison (`sort` by level equivalence through `LevelEq.normalize`,
  `const` by reference and level lists, `bvar`, `app`, `lam`, `forallE`),
  eta on either side, and proof irrelevance for terms whose type is a
  proposition; returns `ConvClaim`. Regimes are compared syntactically;
  `PropWhen` is canonical (`PropWhen.eq_of_holds`), so this is semantic
  equality of conditions. Since every annotation is computed internally, a
  regime disagreement is a conversion failure like any other and can never
  redirect work.
- `checkDeclC`: for a single-member block holding a safe definition,
  theorem, or opaque: the address is fresh, the term forms are supported,
  every reference is installed, the annotated type and body are closed in
  their universe parameters and variables, the type is a sort, the body has
  the declared type, and a theorem's type is a proposition. It installs the
  entry with its body and returns the environment with `StepClaim`, the
  proof that every model of the input environment extends
  (`extend_definition` with `Environment.WF.insert`). Unsupported inputs
  decline by name: unsafe or partial definitions, non-definitions,
  multi-member blocks, projections and literals, fuel exhaustion.
  For a block holding an inductive and its recursor (K2), an unverified
  reader (`Ix.Kernel.Certified.Ordinary.Read`) recovers the `Shape`; the
  block is accepted only if it equals the block generated from that shape
  and `checkBlock` establishes formation, elimination mode, and rule
  typing; installation adds the family, constructors, and recursor with
  its rule equations and typed rule facts, and the model extension comes
  from the ported construction (`Ix.Kernel.Inductive.Ordinary`).

Two drivers sit on top of `checkDeclC`, both pure and both erasing the
proof component for the public API: the closed fold `check` is the subject
of `check_has_model`; `checkDecls` takes an assumed environment, whose model
is a hypothesis, and is the claim-shaped entry point behind
`checkDecls_has_model`. Because the executables carry proofs about models
in `Type v`, they take that universe as a parameter (`check.{u,v}`); it
does not affect computation, and `checkAddressed` fixes `v := 1`, the
universe of the `ZFSet.{0}` model. A parallel driver is con-leche's
install/check split: install the prefixes first, then run the same
`checkDeclC` on each declaration's own prefix concurrently, so its verdict
equals the sequential fold's by construction. The four operations the
compiler's auxiliary generator uses today through `Ix.Tc.Knot` (`whnf`,
`infer` with `ensureSort`, `isDefEq`, `isLargeEliminator`) are exported as
pure functions at K6.

Soundness is intrinsic, not extrinsic: con-leche proves theorems of the
shape `infer Γ e = some (e', A) → TypingClaim Γ e' A` after the fact, while
here the functions construct those claims as they run, consuming the rule
theorems of 3.3; `Ix.Kernel.Claims` packages them as `FormedClaim`,
`ConvClaim`, and `ReductionClaim` with the closure rules the checker needs.
The choice was made at K1 because it keeps each rule application next to
the code that relies on it and removes a second, parallel definition of
every operation.

`partial` is not used in certified code. Termination is by fuel or by
structural recursion; fuel exhaustion declines.

### 3.5 Inductive types and pinned blocks

The kernel validates an inductive declaration (universe and parameter
agreement across the block, manifest return types, strict positivity, field
sort bounds, elimination level) and computes the recursor it expects. A
stored recursor is accepted only if it is structurally equal to the
computed one. The model side is a construction per shape class, ported from
the old branch's admission routes:

| Profile item | Model construction (old branch source) | Release |
| --- | --- | --- |
| Ordinary strictly positive families: ordinary fields, then recursive fields whose domains and indices do not depend on other recursive fields | `Certified/Ordinary` (carriers, eliminators, rule equations, large elimination) | K2 |
| Structures with projections, eta, and the `Prop` field restriction | `Certified/Structure` | K2 |
| `Nat`: structural pin of zero and successor, numerals, literal typing | `Certified/Natural` | K2 |
| `Eq`: admitted as an ordinary indexed family; its meaning as set equality and K-like reduction through proof irrelevance | `Certified/Ordinary`, `Certified/Basis/Equality`, `Certified/Standard/Realization` | K2 |
| Quotient primitives and `Quot.sound` | `Certified/Quotient` | K2 |
| `propext`, `Classical.choice` | `Certified/Standard` | K2 |
| Constructor-free inductives (`False`, `Empty`) | follows from the ordinary construction | K2 |
| Mutual and nested blocks | `Certified/Modeled` uses checked companions; treat as a later promotion, not a first-release route | K6 |
| K for other families, reflexive blocks, string literals | none yet | K6 |

Status (2026-09-17): the ordinary route is implemented and connected
(`Ix.Kernel.Certified.Ordinary`, `Ix.Kernel.Inductive.Ordinary`), with the
recursor at member 1 of the family's block as Ixon's `muts` layout has it;
the K flag is accepted for a singleton proposition without fields, and K-like
reduction synthesizes the constructor from the recursor's parameters,
converting the major to it by proof irrelevance. The structure route is implemented
(`Ix.Kernel.Certified.Structure`, `Ix.Kernel.Inductive.Structure`): an
ordinary block with one constructor, no indices, and no recursive fields
whose fields are propositions whenever the family is one gets projections,
eta, and iota; otherwise it stays a plain inductive without projections, as
`Exists` does in Lean. The `Nat` route is implemented (`Ix.Kernel.Certified.Natural`,
`Ix.Kernel.Inductive.Natural`): a block whose shape is exactly zero and
successor gets the `natural` fact, whose meaning now includes that the
successor is a function on the carrier, which literal unfolding needs. The
quotient route is implemented (`Ix.Kernel.Certified.Quotient`): the former,
the constructor, the lift, and the eliminator are installed one by one from
their exact generated declarations, each publishing a `quotient` fact that
pins its value; no computation rule is published, since the lift's rule is
derived at reduction time from the published facts and the admitted `Eq`
interface and the eliminator's holds outright; `Quot.sound` is an axiom over
the admitted interfaces. The standard axioms are implemented
(`Ix.Kernel.Certified.Standard`): `propext` and `Classical.choice` are
admitted at their exact types once the `Eq`, `Iff`, and `Nonempty`
interfaces are installed as ordinary blocks, and realized by the point and
by a choice function. Every row of the table is implemented.

Pins exist only where a reduction rule must identify a block: `Nat` for
literals in the first release, `Bool`/`String` later. A pin is a structural
comparison of the stored block with the pinned declaration; the address is
only the lookup key. Nothing in the consistency theorem depends on a pin.
Unsupported shapes decline with the class named.

### 3.6 Simplifications and why each preserves the theorem

| Simplification | What it removes | Why consistency is preserved |
| --- | --- | --- |
| Addresses and `ConstRef` instead of names | `Name`, prefix scoping, reserved names, shadowing rules, "installed under its own name" theorems, name-injectivity encodings | The model indexes constants by reference; a reference resolves by key or rejects |
| Positional universe parameters | Named `LevelParam`, `substFn`, capture reasoning | Level assignments are lists; evaluation is unchanged |
| Ordered environment, order supplied by the host | Dependency walks with proved decreasing ranks, hash-based acyclicity | Acceptance requires every reference to be installed earlier |
| Total `interp` with `WellDenoted` | The `Denotes` relation and `Denotes_functional` | Same denotations; rewriting works directly |
| Annotations computed by an unverified pass and validated by certified inference | Annotation witnesses and readers | Acceptance depends only on the validated annotations; a wrong one is rejected |
| Direct checker soundness | `TypingWitness`/`ConversionWitness` trees, witness search, reject-on-search-failure | The witness rules are the rule theorems; the checker applies them in the proof |
| One fold, no cached tier | `Cached/` and its simulation proofs | The executed function is the theorem's subject |
| No parser in the closure | `Frontend/`, chunked byte theorems | Bytes get their own contract in K4 |
| Generated recursors and direct model constructions per shape class | Generated `_model` families, opaque installs, projection-function rewriting, companions | Each class has a proved model extension; other classes decline |
| No-False from constructor-free inductives | Pinned `False` basis block with a `false_empty` model field | The ordinary construction interprets a constructor-free inductive as the empty set |
| Structural pins, `Nat` only | Hardcoded address tables for dispatch, name-based basis pins | Pins identify content; addresses stay keys |
| Zeta by substitution | Let annotations, lazy zeta machinery | The regime is read on binders only |
| Strings and Nat acceleration deferred | `strLitToConstructor`, `NatOpPinSet`, division certificates | Coverage changes, soundness does not |
| Pure BLAKE3 outside the kernel | FFI hashing on certified paths and a refinement obligation against it | The kernel never hashes; hashing theorems are about a Lean function |

Kept deliberately: the `SetTheory` interface, the `PropWhen` regime on
binders, the collapse of definitional to propositional equality, and
level-polymorphic constants as functions of level assignments. The old
branch's refutation `CheckedTyping.annotations_not_determined` still
applies: identical erased syntax does not license interchangeable
annotations, which is why the kernel compares annotations in conversion
instead of assuming them.

### 3.7 Why addresses help the proof

- Lookup is a total function on keys. There is no resolution, no scope, and
  no rename; the environment invariant is a list invariant.
- Mutual blocks and constructors are structural positions. Block ownership
  and constructor membership are bounds checks, not name conventions.
- Content addressing gives the host a canonical dependency order for free,
  and the kernel only has to check it.
- The identity the rest of Ix certifies, `KId.addr`, subject roots,
  assumption trees, and claim payloads, is the same key the kernel's theorem
  is stated over. K3 to K5 compose without a translation layer.
- The old branch's model, judgments, and admission constructions were built
  over `ConstRef β` for exactly this reason and port without redesign.

## 4. Layout, layering and the certification ledger

### Module layout

```text
Ix/Kernel.lean                 Public API and theorem imports
Ix/Kernel/
  Level.lean                   Positional levels, equivalence, normalization
  Ref.lean                     ConstRef
  Expr.lean                    VExpr, AExpr, lift/inst/instL, scope
  Const.lean                   Declarations and blocks
  Env.lean                     Ordered Address-keyed environment
  Whnf.lean  Infer.lean  DefEq.lean  Inductive.lean  Check.lean
  Model/                       SetTheory, SetModel, Interpret, Judgment,
                               Environment, Inductive constructions
  Verify/                      Soundness proofs; imports the implementation
  Consistency.lean             check_has_model, no_proof_of_False
  Audit/                       Axiom, import, runtime, provenance audits
  Ingress.lean                 K3: Ixon constants to kernel declarations
Ix/Address/Core.lean           Pure address key (K0 split, see below)
Ix/Ixon/Types.lean             K3: pure Ixon data types split from codecs
IxKernel/lakefile.lean         The kernel as a dependency-free package over the sources above
Tests/Ix/Kernel/               Fixtures, soundness tests, audit controls, provenance
Models/SetTheory/              Mathlib instance package (ported), depends on IxKernel only
docs/kernel.md                 Public contract, coverage, trust boundary
```

`Tests/Ix/Kernel/` already holds the Rust kernel's FFI harnesses
(`CheckEnv`, `Arena`, and others). They keep that role, stay outside the
certified gate, and new modules take distinct names.

### Two small refactors on `main`

1. `Ix.Address` imports `Blake3.Rust`, whose package loads precompiled
   shared objects into any elaborating process. Add `Ix.Address.Core` with
   the structure, `BEq`, `DecidableEq`, `Ord`, `Hashable`, and hex
   conversion; keep `Ix.Address` as the existing API that re-exports `Core`
   and defines `Address.blake3`, the `ToExpr` instances, and the existing
   `Inhabited` value (blake3 of the empty input, unchanged: the kernel needs
   no default address). The kernel imports only `Core`. In the
   same change, bump the Blake3 pin to the pure-implementation revision and
   add `Address.blake3Pure`, defined by `Blake3.Pure.hash` in a module that
   imports only `Blake3.Pure`, with a test comparing it to the Rust backend
   on the fixture corpora. Host code keeps calling the Rust backend.
2. `Ix.Ixon` defines the Ixon data types alongside codecs and imports
   `Ix.Environment` (Blake3 name hashing) and `Ix.Merkle`. K3 moves the
   data types to `Ix.Ixon.Types`, importable by the kernel's ingress.

Both are mechanical, reviewed separately, and change no behavior.

### Layering rules

- `Ix.Kernel.*` imports Lean core (`Init`) and `Ix.Address.Core`, and from
  K3 `Ix.Ixon.Types`. Nothing else: no `Std`, `Lean`, or `Batteries`
  module, nothing else under `Ix`, no `Blake3`, no `lean4lean`, no `Ix.Tc`.
  The standalone package build enforces this structurally; the import audit
  records the exact closure.
- Implementation modules do not import `Model` or `Verify`. Proofs import the
  implementation. Audits and tests import the library; the library never
  imports them.
- Everything else in `Ix` may import `Ix.Kernel`.
- Mathlib stays in `Models/SetTheory`.

A `lean_lib` does not enforce these rules. An import-graph audit with an
explicit allowlist and negative controls does. The runtime audit inventories
`@[extern]`, `implemented_by`, `unsafe`, `partial`, computed fields, and
`csimp` replacements reachable from the public operations.

### Lake packages

The kernel is built for certification by its own Lake package, `IxKernel/`,
which reads the shared sources (`srcDir := ".."`, roots `Ix.Kernel` and
`Ix.Address.Core`) and requires nothing beyond the Lean toolchain. The root
`ix` package builds the same modules for its host consumers through its `Ix`
library; it does not require the kernel package, because Lake resolves
modules root-first by name prefix, so two packages cannot own `Ix.*`
modules in one workspace. `lake -d IxKernel build --wfail` is the strict
gate: a kernel module that imports anything outside the kernel fails there
even if it would build inside the root workspace. `Models/SetTheory`
depends on the kernel package only, so its workspace holds Mathlib and the
kernel. The root `check-kernel` script runs the standalone build, the
host-side tests, and provenance, with `--with-model` adding the Mathlib
package.

### The Ix certification ledger

Every component of `Ix` has a status: certified (theorem and audit), specified
(contract stated, proof pending), or host (execution boundary, explicitly
outside). The ledger lives in `docs/kernel.md` and is updated at every
checkpoint. Initial entries:

| Component | Modules | Status now | Route |
| --- | --- | --- | --- |
| Certified kernel | `Ix.Kernel.*` | K1: definitions, theorems, and opaques certified; inductives at K2 | K0 to K2 |
| Address key | `Ix.Address.Core` | pure data | K0 |
| BLAKE3 | `Blake3.Pure` (package), `Address.blake3Pure` | certified function once the pin is bumped and our runtime audit confirms its closure | K0 pin bump; used from K4 and K5; the C and Rust backends stay host accelerators |
| Ixon data types | `Ix.Ixon` types | host | K3 split, then certified data |
| Ixon codecs | `Ix.Ixon` encoders and decoders | host | K4, supported subset |
| Ixon to kernel ingress | `Ix.Tc.Ingress` today | host | K3 certified reading relation |
| Claims, assumption trees, Merkle roots, commitments | `Ix.Claim`, `Ix.AssumptionTree`, `Ix.Merkle`, `Ix.Commit` | host | K5, with explicit cryptographic assumptions |
| Lean reference checker | `Ix.Tc` | host; replaced by `Ix.Kernel` in K6 | every consumer migrates, then `Ix.Tc` is deleted |
| Rust kernel | `crates/kernel`, `Ix.KernelCheck` | host fast path | differential parity against `Ix.Kernel`; verdicts are not certified |
| In-circuit kernel | `Ix.IxVM.Kernel` (Aiur program) | separate implementation | refinement to `Ix.Kernel` is the long-term composition point; out of scope here |
| Lean4lean-based verification | `Ix.Tc.Verify`, `Ix.Compile.Verify`, `Benchmarks/Lean4Lean*`, one TruthMines driver, and the `lean4lean` dependency with its `IxTcVerify`, `IxCompileVerify`, `Lean4LeanBench`, `bench-lean4lean`, and `ix_native_decide_dynlib` targets | outside the closure | the dependency is removed from the repository entirely with these consumers, no later than K6; the audit helper `Ix.Tc.Verify.Audit.Basic` moves to `Ix.Kernel.Audit` first |
| Auxiliary generation | `Ix.AuxGen` | host consumer of the kernel's four operations | migrates to `Ix.Kernel` in K6 |
| Compiler and decompiler | `Ix.CompileM`, `Ix.CondenseM`, `Ix.GraphM`, `Ix.CanonM`, `Ix.Sharing`, `Ix.EnvScope`, `Ix.DecompileM`, `Ix.Environment` | host; `Ix.Compile.Verify` currently admits native-decision axioms for BLAKE3 and name hashing | source-fidelity contracts later; the pure BLAKE3 offers a way to drop those axioms |
| Transport and IO | `Ix.ImportIxe`, `Ix.Catalog`, `Ix.Replay`, `Ix.Watchdog`, `Ix.Iroh`, `Ix.Cli` | host | stays host |
| Proof systems | `Ix.Aiur`, `Ix.IxVM`, `Ix.MultiStark`, `Ix.Aggr` | separate obligations | out of scope |

## 5. Source selection and migration policy

### From the old branch

| Component | Treatment |
| --- | --- |
| `Ix/Theory/{Ref,VLevel,VLevelLemmas,Expr,ExprSubstitution,Const,Store,Rename,Quot}.lean` | Port as `Ix.Kernel.{Ref,Level,Expr,Const,...}`; add `letE` |
| `Ix/Theory/Model/*` including `SetTheory/`, `SetModel/`, `Inductive/` | Port as `Ix.Kernel.Model.*` with the namespace map recorded |
| `Ix/Theory/Certified/{Ordinary,Structure,Natural,Quotient,Standard,Basis}` | Port the model-extension constructions and shape checks; the kernel's inductive validation drives them instead of witnesses |
| `Ix/Theory/Certified/{Checker,Accept,Store,Admission,Signature,Source,Claims,ClaimComposition,Operations}` | Not carried as an API. Mine them for lemmas; the witness datatypes and the search-facing acceptance functions are not deliverables |
| `Ix/Theory/Certified/Modeled` | Reference for K6 mutual/nested work |
| `Ix/Theory/Certificate/*` | Excluded: witness search |
| `Ix/Theory/Named/*`, `Ix/Kernel/Verify/*`, `Ix/Certified/*` host adapters, execution histories | Excluded from the certified closure; `Ix/Certified/Ingress.lean` and `Store.lean` are reference material for K3 and K5 |
| `Models/SetTheory` | Port the package; retarget `carneiro_implies_ix` to `Ix.Kernel.Model.SetTheory`; keep the audit |
| `Tests/Theory/*` | Port fixtures that exercise the model and the admission constructions |
| The audit helper `Ix.Kernel.Verify.Audit.AxiomAudit` imported by `Ix.Theory` | Reimplement under `Ix.Kernel.Audit` |

### From con-leche

Techniques and evidence, each recorded with its origin:

- The unverified annotate pass under a verified validator. Con-leche's
  extrinsic verification style (certifying variants of `infer`, `whnf`,
  and `isDefEq` proved after the fact) was considered and not adopted;
  the K1 checker is proof-carrying (3.4).
- The annotation law that annotations never steer reduction. Con-leche's
  second law, that a mismatch declines, is moot here: annotations are
  internal (3.4), so a regime disagreement is an ordinary conversion failure.
- The decline/reject distinction and the exit-code discipline.
- The layering fence with negative tests, and the trust-surface allowlist.
- The iteration protocol: start from a kernel that rejects everything with
  the theorem proved, add one feature at a time, keep the theorem green.
- The measured lesson that no union-find conversion cache is sound with a
  non-transitive conversion; relevant to `Ix.Tc.Equiv` and to K6.
- Later, the `Nat.div`/`Nat.mod` well-founded-definition certificates and
  the interned-arena and memo designs, as source material for K6 promotions.
- Regression fixtures from the lean kernel arena tutorial set, re-encoded
  through the Ix compiler.

No con-leche Lean module is copied into the certified closure in K0 to K2.
If a specific lemma is later copied, it enters through the provenance
record like any other import.

### From `main`

- `Ix.Tc` is the behavioral reference for reduction order, inductive checks,
  and recursor generation, and the oracle for differential testing. Its
  verdicts are never certified evidence.
- `Ix.Tc.Ingress` is the reference for share expansion, table resolution,
  and projection reconstruction in K3; `Ix.Tc.CanonicalCheck` for the
  kernel-side canonical block order validation in K4; `Ix.Tc.Knot` for the
  public operation set; `Ix.Tc.ParCheck` for the parallel driver's
  reporting and worker layout.
- `Tests/Ix/Tc` holds the differential and scale tests (`AnonDiff`,
  `AccelDiff`, `TutorialTc`, `InitScale`, `Roundtrip`) that become the
  parity corpus for K6.
- `Ix.Ixon` types define the input shapes; `docs/Ixon.md` is the format
  specification for K4.
- The compiled fixture corpora under `Tests/` supply Ixon inputs.

### Provenance and transformation discipline

For each imported file record the repository, revision, original path,
source SHA-256, destination path, destination SHA-256, license, and the
transformations applied. Keep separate entries for imported and newly
authored modules. Preserve the con-leche Apache-2.0 attribution carried by
`Models/SetTheory` and by any copied lemma. The old branch's set theory came
from con-leche `86cd20a65660d757cedc81561a44579099b565d0`; do not claim a
newer origin.

Separate mechanical namespace and import changes from semantic changes into
reviewable checkpoints. Record theorem statements before and after each
semantic change. A namespace rewrite must not touch payload data such as
fixture bytes or pinned declarations.

## 6. Milestones

| Milestone | Outcome | Depends on |
| --- | --- | --- |
| K0 | Scaffold, audits with controls, ported model, trivial kernel with the public theorems proved | workspace |
| K1 | Definitions, theorems, opaques, axioms, universes, conversion core; theorem for the real fold | K0 |
| K2 | Inductive profile of 3.5; first release with the Mathlib model | K1 |
| K3 | Ixon ingress with a proved reading relation; `checkEnv` over Ixon-shaped input | K2 |
| K4 | Ixon byte decoding for the supported subset with round-trip and framing theorems | K3 |
| K5 | Claims, subject roots, receipts, and host commands routed through the kernel | K3, K4 |
| K6 | Optimize `Ix.Kernel` and replace `Ix.Tc` completely | K3, K4 |
| K7 | Substructural binder modes and the optimizations they license | K6 |

### K0: scaffold and foundation

1. Write the port manifest with the pinned revisions; verify the old
   branch's working copy against the pin.
2. Land the `Ix.Address.Core` split, the Blake3 pin bump, and
   `Address.blake3Pure`.
3. Port the old branch's syntax and `Model` modules to `Ix.Kernel.Model`
   under the recorded namespace map. Build with `--wfail`. Port the model
   fixtures from `Tests/Theory`.
4. Add `lean_lib IxKernel`, the `check-kernel` script, and the audits:
   per-root axiom sets over types, bodies, and constructor fields; import
   allowlist; runtime closure inventory; provenance hashes. Each audit gets
   a negative control that introduces the forbidden thing and observes the
   failure. Missing required roots fail.
5. Port `Models/SetTheory`, retarget it, and run its audit.
6. Define the environment, `Config`, `Error`, the public API, and a kernel
   that declines every declaration. Prove `checkDecls_has_model`,
   `check_has_model`, and `no_proof_of_False` for it. From here on the
   theorems must never be removed, weakened, or given new hypotheses.

Exit: clean-checkout build of `IxKernel` and the model package; every audit
fails on its control and passes on the tree; the public theorem statements
are fixed.

### K1: definitions and conversion core (complete, 2026-09-17)

1. Levels (`Ix.Kernel.Level`): equivalence and the zero test by
   `LevelEq.normalize`, with soundness lemmas; `VLevelLemmas` ported. The
   import trim measured at K0 is done: `Lean.Level` and
   `Batteries.Data.List.Basic` are gone (a local `Ix.Kernel.Forall₂`
   replaces `List.Forall₂`), so the closure of `Ix.Kernel` is Lean core
   plus the kernel.
2. Claims (`Ix.Kernel.Claims`): `FormedClaim`, `ConvClaim`, and
   `ReductionClaim` over the model's `TypingClaim`, with the closure rules
   the checker uses: congruences, eta, proof irrelevance, typed beta, delta,
   zeta.
3. The proof-carrying core (`Ix.Kernel.Infer`): `step`, `whnf`, `inferA`,
   `isDefEqCore`, and `isDefEq` as one fuel-bounded mutual block, and the
   unverified `annotate` (`Ix.Kernel.Annotate`) that feeds it. Beta, zeta,
   and delta; structural conversion with level equivalence, eta, and proof
   irrelevance. Projections, literals, lazy delta by hints, and caches are
   not in K1.
4. `checkDeclC` for single safe definitions, theorems, and opaques with
   installation and the `StepClaim` model extension; `Model` carries the
   environment's well-formedness (`Environment.WF`) so the extension
   theorem's hypotheses come from the checker's decidable checks. The
   standard axioms are not installable yet: as planned they decline until
   K2 admits their realization. `no_proof_of_False` keeps its statement and
   is vacuous until K2 installs inductives.
5. Fixtures (`Tests/Ix/Kernel/Fixtures.lean`, run by `check-kernel`):
   accepted polymorphic definitions, a theorem, dependent binders, `let`,
   universe instantiation with level equivalence, beta of an applied
   definition, delta of a declared type, an opaque; rejections for
   non-propositional theorems, ill-typed types and bodies, mismatched
   bodies, missing references, duplicate addresses, open universe
   parameters, open variables, wrong universe arity; declines for unsafe
   definitions, non-definitions, multi-member blocks, literals, and fuel
   exhaustion. Eta and proof-irrelevance fixtures need `Prop`-valued
   constants and move to K2. Annotation mismatches are no longer an input
   category, since annotations are internal. Binder modes arrive with K3.
6. Audits: the executables' axiom sets are the standard three, entering
   through erased proofs; the runtime audit walks compiled IR, so its
   closure is the code that executes (145 compiled functions and four
   inherited `Nat` externs at K1) rather than the proof terms embedded in
   definitions, and every audited root must have compiled code.

Exit met: the theorem covers the executed fold; positive fixtures accept;
the compiled-code audit reaches no foreign symbol; the K0 statements are
unchanged.

### K2: inductive profile and first release (routes complete, 2026-09-17)

1. Done for the ordinary class: shape reading, formation (telescopes, index
   fit, universe bounds, strict positivity by the shape), elimination mode
   with the singleton exception, recursor and rule typing, exact comparison
   with the stored block, iota in `whnf` through published typed rules, and
   the `Prop` restriction; structures with projections, eta, iota, and the
   `Prop` field restriction; `Nat` literals through the `natural` fact.
   `Prop` field restriction; `Nat` literals through the `natural` fact;
   K-like reduction for `Eq`; the quotient primitives with `Quot.sound`;
   `propext` and `Classical.choice`.
2. Constructions connected in order: ordinary families, structures, and
   `Nat`, `Eq` with K, quotients, and the standard axioms (done).
3. Model extension for every accepted declaration composed with K1 (done):
   inductive routes publish facts and equations, quotient primitives and
   the standard axioms are installed one entry at a time.
4. Fixtures (`Tests/Ix/Kernel/Inductives.lean`): `False`, `True`, `And`,
   `Or`, `Nat`, `List`, indexed `Eq`, generated from shapes, and `Nat`
   encoded by hand in Lean's recursor layout, which must equal the generated
   block; `False.rec`, constructor applications, `Eq.refl`, and `Nat.rec`
   arithmetic (`add 1 1 = 2` by `Eq.refl`); rejections for a negative
   occurrence, a universe violation, a duplicate address, large elimination
   from a two-constructor proposition, and a mismatched arithmetic theorem;
   a tampered recursor and an unsafe block decline. Structures
   (`Tests/Ix/Kernel/Structures.lean`): `Prod`, `And`, a dependent subtype,
   and a proposition with a data field that stays ordinary; projection
   typing including a dependent field, projection iota, structure eta, a
   projection out of a non-structure and a bad field index rejected, a wrong
   iota theorem rejected. Literals (`Tests/Ix/Kernel/Literals.lean`): a
   literal at `Nat`, `3 = succ 2` and `0 = zero` by `Eq.refl`, `add 2 2 = 4`
   through iota on literal majors, wrong equations rejected, a literal naming
   an uninstalled family a missing reference, one naming a non-`Nat` family
   ill-typed. `Eq` with K-like reduction (`kSubst` in `Inductives.lean`).
   Quotients (`Tests/Ix/Kernel/Quotients.lean`): the five primitives in
   order, `Quot.lift f h (Quot.mk a) = f a` by `Eq.refl`, the eliminator at
   a constructor application; a primitive before what it refers to, a
   duplicate, `f a` against `f b`, and soundness over a non-equality
   rejected; a non-primitive former and a non-standard axiom declined.
   Axioms (`Tests/Ix/Kernel/Axioms.lean`): `propext` over `Eq` and `Iff`,
   `Classical.choice` over `Nonempty`, each used; an axiom before its
   interfaces, an `Iff` with a small eliminator, and a duplicate rejected;
   other axioms decline.
5. Differential run against `Ix.Tc` on the accepted corpus (pending).
6. `docs/kernel.md` and CI (pending).

Exit: `lake build --wfail IxKernel` and `check-kernel` pass on a clean
checkout; the theorem applies to the fixtures; the release is usable
without Ixon bytes, `Ix.Tc`, or claims.

### K3: Ixon ingress

1. Land the `Ix.Ixon.Types` split.
2. `Ix.Kernel.Ingress`: expand `share`, resolve `refs` and `univs` tables,
   map projection constants to `ConstRef`, read Nat blobs to `Nat`, reject
   strings and unsupported binder modes, check reference bounds and block
   ownership.
3. State the reading relation between an Ixon constant and the kernel
   declaration; prove ingress success establishes it, including declared
   types, universe counts, mutual identities, and binder modes. Add the
   egress back to an Ixon constant with `egress (ingress c) = c` on the
   supported subset; this replaces the kernel round-trip phases of
   `ix validate-lean`.
4. `checkEnv` over a list of address-to-constant pairs and the blob bytes
   behind literals, composed with `check`; theorem for the Ixon-shaped
   in-memory input. The host supplies the order, the pairs, and the blobs;
   the kernel treats addresses as keys.
5. Tests on environments compiled by `Ix.CompileM` from the tutorial corpus,
   loaded by the ordinary host loader, which remains untrusted.

Exit: acceptance of Ixon-shaped input establishes the meaning of the
selected declarations; unsupported input declines explicitly.

### K4: Ixon bytes

Port the earlier plan's serialization milestone against the split types:
schema and version, pure encoders and bounded decoders for the supported
subset, `decode (encode x) = .ok x`, decode validity, canonical re-encoding,
full-input consumption, and adversarial mutation tests with the Rust codec
as a differential oracle. Compose with K3 so the statement names which
declarations the bytes describe. Port `Ix.Tc.CanonicalCheck` as the
canonical block order validation with its own contract: a stored mutual
block is accepted only in the order the kernel recomputes, so a permuted
block is rejected without trusting compiler metadata. With the certified
encoder and `Address.blake3Pure`, ingress may reconstruct projection
addresses exactly as production does instead of requiring them supplied.
Fuel and size limits are documented coverage boundaries.

### K5: claims and receipts

Port the earlier plan's claim milestone against the kernel: `CheckClaim`
subjects, assumption trees, subject roots, and receipts that bind checker,
format, and profile versions. The theorem for a claim states the exact
hypothesis under which an address stands for its bytes; the kernel result
is about the constants it was given. Host commands report certified success
only from the kernel's success. Cryptographic collision assumptions are
named, finite, and separate from the mathematical result.

### K6: optimize `Ix.Kernel` and replace `Ix.Tc`

`Ix.Tc` is a pure-Lean mirror of the Rust kernel. Its recorded runs
(`BENCHMARKS.md`, `ix check-lean` against `ix check-rs`, full verdict
parity) are the yardstick:

| Environment | Constants | Lean `check-lean` | Rust `check-rs` | Ratio |
| --- | --- | --- | --- | --- |
| InitStd | 105,492 | 64.8 s | 24.1 s | 2.7x |
| Lean | 188,999 | 78.1 s | 35.0 s | 2.2x |
| Mathlib, anon, 16 workers, caches cleared every 50 items | 640,658 | 1,014.7 s at about 42 GB | 234.0 s | 4.3x |

Meta mode exceeds memory at Mathlib scale. `Ix.Tc` is therefore not a
production checker; its value is formalization and specification, and that
is exactly what `Ix.Kernel` provides with a proof. The decision is to
replace `Ix.Tc` completely, not to keep two Lean kernels. The Rust kernel
stays the production fast path and is differentially tested against
`Ix.Kernel`; the IxVM kernel stays the in-circuit implementation.

Replacement is complete when every consumer runs on `Ix.Kernel` and the
parity corpus agrees:

| Consumer | What it needs from `Ix.Kernel` |
| --- | --- |
| `ix check-lean` (`Ix.Cli.CheckLeanCmd`) | K3 ingress, the subject driver over an assumed prefix, the install/check parallel driver, progress and fail-out reporting, labels from a name sidecar kept outside the kernel |
| `ix validate-lean` phases 3 and 4 | The K3 round trip for anon; the meta round trip is metadata plumbing and moves to the metadata modules, not into the kernel |
| `Ix.AuxGen.Kernel` | The four exported operations over kernel terms; provisional addresses are ordinary keys; the name bridge stays in `Ix.AuxGen` |
| `Ix.IxVM.ClaimHarness` | The primitive address table, re-homed as `Ix.Kernel.Primitive` |
| `Ix.Compile.Verify.Audit` | The audit helper, re-homed as `Ix.Kernel.Audit` |
| `Tests/Ix/Tc`, `Tests/Ix/Kernel/PrimAddrs` | Ported to `Tests/Ix/Kernel`; the differential tests run against `check-rs` |
| `Ix.lean` | Imports `Ix.Kernel` |

One parity caveat is deliberate. `check-lean` trusts every referenced
constant's declared type regardless of order, so an environment with a
reference cycle would be accepted by it and by the Rust kernel; the ordered
fold rejects the forward reference. Real environments have no cycles, and
the difference is the correct direction.

Optimizations land in this order, each with the contract from section 7
and measured on the retained workloads:

1. Interning and hash-consing with structural keys, as con-leche's arena;
   simulation against the reference operations.
2. Memo tables for `whnf`, `infer`, and `isDefEq` keyed by structural
   identity, with the state invariant that every entry came from an
   execution; no union-find conversion cache.
3. Lazy delta by reducibility hints and same-head shortcuts, with the
   verdict-preservation proof.
4. Nat and literal acceleration, each operation enabled only after its
   defining equations are proved in the model; con-leche's division
   certificates are the source for `Nat.div` and `Nat.mod`.
5. The install/check parallel driver and bounded per-worker memory, so
   Mathlib-scale anon runs fit without cache clearing tricks.
6. String literals, mutual and nested inductives, K beyond `Eq`, reflexive
   blocks, so the accepted corpus matches `Ix.Tc`'s.

The first target is `Ix.Tc` parity on the three recorded workloads with
bounded memory. After that, the Rust gap is narrowed with the same
discipline. When every consumer is migrated and the differential corpus
agrees, `Ix.Tc`, `Ix.Tc.Verify`, and the `lean4lean` dependency are
deleted in one change with the ledger updated.

### K7: binder modes and the optimizations they license

Ixon v2 carries usage and ownership on binders, and Ix's annotation
extensions to Lean are expected to surface them in source. The kernel
carries them from K1; this milestone gives them meaning and uses them:

1. Mode checking: usage accounting with the `Uses` algebra and `covers`,
   ownership on results, and a stated contract for what an accepted mode
   assignment guarantees. The set model ignores modes unless a mode-aware
   semantics is adopted; that choice is recorded here.
2. Optimizations licensed by checked modes, each a promotion with a
   verdict-preservation proof: skipping erased arguments in reduction and
   conversion where the model justifies irrelevance, and in-place update
   of uniquely owned data in the kernel's evaluator.
3. Using the same extensions in `Ix.Kernel`'s own implementation for better
   generated code where the Lean-level semantics is unchanged; a modified
   compiler is part of the execution boundary and is recorded as such.

Measure accepted workloads, rejection workloads, memory, and cold behavior on
retained baseline inputs. Speed never enlarges the trust boundary.

## 7. Promotion requirements

Certification attaches to a defined operation and its specification, not to
a directory name or the absence of `sorry`.

| Component | Required contract |
| --- | --- |
| Data representation and operations | Invariants and the advertised operation semantics |
| Equality or lookup used in checking | Successful lookup identifies the intended object; digest equality alone is insufficient |
| Cache or optimized operation | Simulation relative to the reference operation and its admitted state invariant |
| Encoder or decoder | Round trip, decode validity, framing and canonicality, reading relation when used for acceptance |
| Source translator | Successful translation preserves declared types, scopes, references, and subjects |
| Declaration or inductive validator | Success constructs the checked object and its model extension |
| Generator or search | Outputs are proposals; the generator moves inside only with its own proved contract |
| Claim validator | Accepted receipts establish the exact claim meaning under the recorded policy and named assumptions |
| Foreign or backend implementation | A proved correspondence to the operation in the theorem; otherwise an explicitly external backend |
| Hash function | The pure Lean definition is the specification; a native backend needs differential evidence; a theorem needing uniqueness names its collision assumption |

Every promotion record contains the public API and supported inputs, the
exact theorem, the implementation and proof roots with transitive
dependencies, explicit assumptions, provenance, positive and adversarial
results, and the composition point into the public theorems. Library-internal
helpers are justified by their enclosing proved algorithm.

## 8. Verification and continuous integration

| Command | Purpose |
| --- | --- |
| `lake -d IxKernel build --wfail` | Strict standalone build of the certified closure, its audits, and the public roots |
| `lake run check-kernel` | Build, audits, provenance, fixtures, differential tests |
| `lake run check-kernel --with-model` | Also build and audit `Models/SetTheory` |

Required evidence at every checkpoint:

- Every required root exists; its elaborated type and exact axiom set are
  recorded; the traversal covers definitions and constructor fields.
- Transitive imports of the certified closure match the allowlist; the
  scanner has negative tests.
- The compiled-code closure of the public operations, walked over the IR
  the code generator emits, lists every extern, `implemented_by`, unsafe,
  and `csimp` reached, distinguishing inherited Lean mechanisms from
  project code; a root without compiled code fails the audit.
- Provenance hashes and licenses for every imported file and asset.
- Accepted controls and rejections through the exposed operation, including
  configuration defaults and annotation mismatches.
- The model package's axiom guard with the cardinal hypothesis in the type.
- A clean-checkout build at K0, K2, and each release.

Freeze expected reports only after inspecting measured results. Regenerating
a manifest to make a gate pass defeats the audit.

## 9. Managing changes

### Checkpoint contents

The revision and manifest; the exact new public behavior; theorem
statements and assumptions; commands and final results; import, axiom,
runtime, and asset inventory changes; remaining limitations and the next
milestone; ledger updates.

Keep the branch based on `main` and integrate later `main` changes
selectively. Preserve the old consistency workspace as reference material
and do not rewrite its history. The repository ignores `plans/` except this
file; durable contracts go to `docs/`.

### Responses to common problems

| Problem | Response |
| --- | --- |
| A ported model module fails to build | Isolate the fix, keep statements, record the difference from the pin |
| An old-branch lemma assumes witness data | Restate it over the checker's output or reprove it; do not import the witness type |
| A production behavior of `Ix.Tc` has no simple sound counterpart | The kernel declines that input; record it as a coverage gap |
| A feature needs new metatheory | Keep the reference implementation and defer the feature |
| An audit passes despite a known violation | Repair the audit and add the failing control first |
| A theorem needs a callback or invariant premise | Keep the feature outside the public API until the premise is derived |
| A host command can succeed by another path | Route certified success through the kernel and check the connection |
| An optimization wants a hash assumption | Use structural identity, or state a finite collision condition on a separately labeled result |

Weakening the public theorem to fit a feature is never a completion
strategy.

### Decisions fixed by this plan

- The certified checker lives at `Ix.Kernel`; no `IxCertified` namespace or
  library exists.
- Kernel data is Ix-native: `Address` keys, `ConstRef`, positional levels,
  de Bruijn terms, Ixon declaration shapes.
- The semantic model is the old branch's set model, ported; con-leche is a
  source of techniques and evidence, not of code.
- One reference checker is the theorem's subject. Witness trees, certificate
  search, and a certificate API are not deliverables.
- Addresses are opaque keys inside the kernel; hash binding is a host
  property stated explicitly where a claim needs it.
- `Ix.Kernel` replaces `Ix.Tc` completely (K6). The Rust kernel remains the
  production fast path, differentially tested against `Ix.Kernel`; the IxVM
  kernel remains the in-circuit implementation. `Ix.Tc.Verify` and the
  lean4lean dependency leave with `Ix.Tc`.
- BLAKE3 is `Blake3.Pure.hash` wherever a certified operation hashes; the C
  and Rust backends are host accelerators.
- The kernel is certified as its own dependency-free Lake package
  (`IxKernel/`) over the shared `Ix/` sources, and `Models/SetTheory`
  depends on that package only.
- The `lean4lean` dependency is removed from the repository entirely,
  together with its consumers (`Ix.Tc.Verify`, `Ix.Compile.Verify`, the
  Lean4Lean benchmarks and test runner, and their Lake targets), no later
  than the K6 deletion of `Ix.Tc`; nothing new may depend on it.
- Standard logical axioms only; `SetTheory` explicit; the Mathlib instance
  in its own package.

### Decisions resolved during milestones

- `letE` is in the kernel syntax (decided 2026-09-17: interpreted by
  substitution, no regime annotation, typing rule `TypingClaim.letE`,
  unconditional zeta conversion). Annotation comparison in conversion
  (K1): syntactic equality of `PropWhen`, which is canonical.
- K1 (2026-09-17): the checker core is proof-carrying (intrinsic) rather
  than extrinsically verified; binder regimes come from an unverified
  `annotate` pass validated by `inferA`; beta re-infers the argument
  against the binder's domain; the executables take the model universe as
  a phantom parameter and `checkAddressed` fixes it to `1`; the runtime
  audit walks compiled IR; unsupported term forms and missing references
  are prechecked on raw terms so they decline or reject by name.
- K2, ordinary route (2026-09-17): an inductive block is the family with
  its recursor at member 1 (Ixon's `muts` layout), read by an unverified
  reader and accepted only when it equals the block generated from the read
  shape, otherwise declined; the old branch's witness validation is
  replaced by inference and its input store by the block; iota reduces
  through the published rule equation with typed endpoints
  (`ConstantFact.typed`) and arities (`ConstantFact.recursor`, a fact with
  trivial meaning), the constructor's parameters and indices being
  converted against the recursor's rather than trusted; the runtime
  closure inherits Lean's `Array`-backed `List.zipIdx` and `List.flatMap`.
- K2, structures (2026-09-17): a structure-like block (one constructor, no
  indices, no recursive fields) takes the structure route when its fields
  satisfy the `Prop` restriction and falls back to the plain ordinary route
  otherwise; the family entry publishes a `ConstantFact.structure` with the
  arities, the projection facts, and the eta and iota equations (eta first),
  and every rule is typed in the published environment; projection
  reduction and structure eta type the rule endpoints by inference at use;
  `annotate` reports fuel exhaustion and ill-typedness separately, so an
  ill-typed subterm rejects and only exhausted fuel declines; projections
  pass the supported-form precheck, literals still decline.
- K2, `Nat` (2026-09-17): literals name their family on raw and annotated
  syntax, so no pin lives in `Config` (which is not parametric in the
  address type and appears in the frozen statements) or in `Env`; the
  `natural` fact's meaning gains the successor's function membership
  (`NaturalMeaning.succApp`), proved from the constructor's realization,
  because unfolding `n + 1` to `succ n` must yield a well-denoted term; the
  supported-form precheck is gone since every form is checked.
- K2, `Eq` K, quotients, standard axioms (2026-09-17): K-like reduction
  fires when a recursor has a single rule without fields and its major is
  not a constructor application; the constructor is synthesized from the
  recursor's parameters and the major converts to it by proof
  irrelevance, which holds exactly when their types convert. Quotient
  primitives are installed one by one from their exact generated
  declarations (the former, the constructor, the lift, the eliminator,
  then `Quot.sound` as an axiom), each publishing a `quotient` fact that
  pins its value in the model; no computation rule is published: the
  lift's rule is derived at reduction time from the published facts and
  the admitted `Eq` interface (`liftRule_claim`), the eliminator's holds
  outright, so the kernel core imports the quotient syntax and readings,
  and the equality basis is split into a model-only module and its link
  to checked blocks. `propext` and `Classical.choice` are admitted from a
  `Spec` naming the `Eq`, `Iff`, and `Nonempty` blocks (family at member
  0, constructor 0, recursor at member 1), checked inline through the
  decidable interfaces and `checkSort`, and realized by the point and by
  a choice function; other axioms decline.
- The exact inductive shape class, elimination modes, and structure eta
  rules: K2.
- The Ixon subset, binder-mode handling, and canonicality policy: K3, K4.
- Cache designs, the Nat acceleration set, and where meta-mode round trips
  and name labels live after `Ix.Tc`: K6.
- The semantics of binder modes in the model: K7.

## 10. Immediate execution sequence

1. Record the pins and write the port manifest; compare the old branch's
   working copy with its pin.
2. Land `Ix.Address.Core`, the Blake3 pin bump, and `Address.blake3Pure`.
3. Port `Ix.Theory` model and syntax modules to `Ix.Kernel.Model`; build
   strictly; port the model fixtures.
4. Add the Lake target, the `check-kernel` script, and the audits with
   negative controls; port and retarget `Models/SetTheory`.
5. Define the API and the declining kernel; prove the public theorems; freeze
   their statements.
6. Proceed through K1 and K2 one feature at a time, keeping the theorems
   green, then publish the first release before starting K3.
7. After K3 and K4, run K6 to `Ix.Tc` parity, migrate every consumer,
   delete `Ix.Tc`, then start K7.

Success for the first release is a usable `Ix.Kernel` whose actual
acceptance function has a complete model-existence and relative-consistency
theorem over Ix-native declarations. Success afterwards is a growing part of
`Ix` with that standard of proof and an explicit, audited boundary around
what remains host code.
