# Ix.Kernel: certified kernel roadmap

Date: 2026-09-16, implementation plan updated 2026-09-29. K0, K1, and the
supported-profile K2 release gate are complete on `jcb/ix-certified`.
K0: the model is ported to
`Ix.Kernel.Model`, the address split and Blake3 pin bump are in, the kernel
builds as a dependency-free package (`IxKernel/`) whose import closure is
Lean core plus the kernel, the syntax carries `letE`, and `Models/SetTheory`
builds against that package with Mathlib. K1: single definitions, theorems,
and opaques are checked by a proof-carrying inference, reduction, and
conversion core (`Ix.Kernel.Infer`) and installed with their model
extension. K2 so far: ordinary inductive blocks (a family with its
constructors and recursor in one logical fixture block) are read, validated,
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
`lake run check-kernel --with-model` was recorded as passing on 2026-09-17.
The subsequent implementation completed P00–P03 and ran the full K2 gate
in a fresh jj workspace on 2026-09-29, including 38 host differential cases
and the Mathlib model audit. This is supported-profile coverage with the
explicit policies in `docs/kernel.md`, not whole-corpus Lean parity.
K3's pure production types, exact ingress readings, separate physical
inductive/recursor admission, `checkEnv`, and layout-preserving egress are now
implemented with 26 compiler ingress and byte-exact egress cases. K4 now has
isolated production codecs, the retained all-variant inverse proofs,
exact constant framing, aggregate universe bounds over complete records,
executable wire validation, canonical record decoding, and byte admission
with exact reading/acceptance domains, installed declarations, and model
guarantees. Successful production reads now have structural byte-consumption
bounds, composed with universe expansion and the byte-admission limits.
D01 is complete: both
lean4ix/Lean4Lean dependency paths, the old verification trees, and their build/benchmark/CI consumers
have been removed and validated in a fresh jj workspace and through Nix.
Pure projection-address reconstruction and canonical mutual-block ordering
are now implemented outside the hash-free kernel, composed with byte admission.
K4's complete abstract parser-work accounting is now implemented and validated,
including nested failures and aggregate admission limits, without adding
production counters. D02's final runtime Ix.Tc cutover remains required.

Takeover, 2026-09-29: work continues from `f499ccf2`, where the full gate was
re-run (`plans/review/t0-baseline`). That commit is the last Ixon v2 state,
bookmarked as `jcb/ix-certified-v2`. Ix `main` has emitted only Ixon v3 since
#636, and the Compilatr.ix consumer builds on Lean 4.34.0. Section 12's v3 and
Lean 4.34 sequence therefore precedes K5 and the remaining section 10 work.

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

Third pass, 2026-09-29: the ontology and performance review of `ade9216d`
becomes the implementation sequence in section 10. Failure reporting and
input fidelity come first, then reuse of checked information, environment
indexing, context representation, and structured computation rules. These
steps supersede the previous interning-first K6 order. Section 11 records
the complete `lean4ix` dependency and consumer removal, including build,
test, CI, Nix, and generated benchmark configuration. Implementation progress
is recorded in section 10; the full retirement remains required.

Fourth pass, 2026-09-29: the branch moves to Ixon v3 and Lean 4.34.0
(section 12). It merges ix `main` at `b413cd93` for v3, then
`jcb/ix-compilatrix` at `0a31c8db` for Lean 4.34.0. That second commit is the
producer that the Compilatr.ix consumer pins. The branch integrates these by
merging, not rebasing: conflicts are resolved once, and every earlier commit
keeps its recorded gate evidence.

Binder, forall-result, and let contracts are layout data. They are accepted,
retained for exact egress, and ignored by typing, conversion, and the model.
Section 3.1 and K7 are corrected accordingly. The second ontology review
(`c1536731`) adds four contract fixes (R1–R4) to section 12.

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
| `~/projects/ix-certified/plans/refs/con-leche` | `ae0c0c4e4ce6a0081648aff03fe9c39d002c4526` | Untracked reference for the 2026-09-29 review; 152 commits beyond the original pin; retain the exact origin of any subsequently adapted lemma |

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
| main `Ix/Tc/` implementation | 16K | pure-Lean reference checker mirroring `crates/kernel`; the Rust checker remains the production fast path |
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
- Continuation of `Ix.Tc.Verify` or any `lean4ix`/Lean4Lean-based specification;
  their repository-wide removal is planned in section 11.
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
Failed conversion search also declines unless an independent check
establishes a malformed input; failure of a conservative procedure is not
evidence of non-convertibility. P01 repairs the current nested-fuel reporting
that does not yet meet this contract. Fuel remains a recursive depth bound,
not a count of total work.

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
  | lam (dom body : Expr β)
  | forallE (dom body : Expr β)
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
as con-leche does. At the reviewed baseline, annotations do not steer
reduction; they are written by annotation, validated by inference, compared
during conversion, and read by the model. P09 explicitly revises that
operational rule for the proved `.never` beta shortcut.

Ixon's substructural contracts are layout data, not kernel syntax. Ixon v3
defines three kinds:
- a binder contract: usage `erased`, `linear`, `affine`, or `many`, plus an
  input value contract of ownership (`unique`/`shared`) and locality
  (`unrestricted`/`local`);
- a forall result contract;
- a let contract: dependency, value or shared borrow, and a binder contract.

Kernel terms carry none of them. Ingress reads the kernel term, and the egress
layout retains each contract, so records reproduce exactly. Typing,
conversion, and the model ignore contracts. Two terms that differ only in
their contracts are therefore the same kernel term.

The implementation first had this shape under Ixon v2, where it declined
non-default modes. Section 12 (V2) accepts every v3 contract. Mode checking,
and any optimization contracts license, operate on Ixon expressions or their
layouts (K7).

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
  already annotated subterms. Annotation validity is established by
  `inferA`, so acceptance does not trust the annotator to choose valid
  regimes. Fidelity to the supplied raw term is a separate obligation,
  made explicit in P02. P04 reuses the evidence obtained while annotating
  instead of validating the same subtrees repeatedly.
- `inferA`: infers the type of an annotated term and returns
  `TypingClaim Γ e A`. Binder cases check that the recorded regime equals
  the zero condition of the inferred codomain sort.
- `whnf`/`step`: beta, zeta, delta by unfolding stored bodies, and
  reduction under an application head, returning `ReductionClaim`. Beta is
  typed: the argument is re-inferred and converted to the binder's domain
  before the redex fires, because the set model licenses substitution only
  when the argument denotes a member of the domain, and denotational typing
  cannot recover the domain of a function in the `Prop` regime. Fuel-bounded;
  no caches; no reducibility hints. P07 shares typed rule arguments; P09
  eliminates argument rechecking in the non-Prop `.never` case by proof.
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
  equality of conditions. An unsuccessful comparison follows P01's search
  outcome policy; it is not by itself a proof of non-convertibility.
- `checkDeclC`: for a single-member block holding a safe definition,
  theorem, or opaque: the address is fresh, the term forms are supported,
  every reference is installed, the annotated type and body are closed in
  their universe parameters and variables, the declared type inhabits a sort, the body has
  the declared type, and a theorem's type is a proposition. It installs the
  entry with its body and returns the environment with `StepClaim`, the
  proof that every model of the input environment extends
  (`extend_definition` with `Environment.WF.insert`). Unsupported inputs
  decline by name, including unsafe or partial definitions, unsupported
  block shapes, and fuel exhaustion. Projections and Nat literals are
  supported by the K2 routes described above.
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
  Egress.lean                  K3: exact record reconstruction with retained layout
Ix/Address/Core.lean           Pure address key (K0 split, see below)
Ix/Ixon/Types.lean             K3: pure Ixon data types split from codecs
Ix/Ixon/Codec.lean             K4: pure production anonymous encoders/decoders
Ix/Ixon/Wire.lean              K4: structural wire representability
Ix/Ixon/Verify/                K4: retained codec and exact framing proofs
Ix/Ixon/Audit.lean             K4: independent codec/proof boundaries
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
- K4's `Ix.Ixon.Codec` and `Wire` likewise import only Lean core and the
  pure address/types. Their proof modules additionally use Lean/Std proof
  tooling, without host code, Lean4Lean, or foreign execution replacements.
  `Ix.Ixon.Audit` checks these separate boundaries; the kernel's narrower
  allowlist is unchanged.
- `Ix.Ixon.Admission` composes the pure codecs with `Ix.Kernel.Ingress`
  outside the kernel tree. Its implementation imports neither `Verify` nor
  host modules; `Verify.Admission` proves the byte contract separately.
  `Admission.Audit` checks its own closure without widening the kernel or
  codec allowlists.
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
| Ixon data types | `Ix.Ixon.Types` | pure production data in the standalone audited closure | K3 split complete |
| Ixon codecs | `Ix.Ixon.Codec`, `Wire`, `WireCheck`, `Bounded`, `Canonical`, `Verify` | production grammar and inverses, complete-record byte/universe limits, exact wire validation, canonical re-encoding, and all-outcome abstract parser-work bounds | K4 implemented |
| Ixon to kernel ingress and egress | `Ix.Kernel.Ingress`, `Ix.Kernel.Egress` | exact readings, physical-reference fidelity, model theorem for accepted in-memory input, and exact reconstruction with retained layout | K3 complete |
| Byte admission | `Ix.Ixon.Admission`, `Verify.Admission`, `Verify.WorkAdmission`, `Admission.Audit`; `Ix.Ixon.Projection`, `ProjectionProofs`, `ProjectionAudit`; `Ix.Ixon.BlockOrder`, `BlockOrderProofs`, `BlockOrderAudit` | exact canonical-byte reading, aggregate parser-work bound, bounded projection reconstruction, recomputed canonical block order, installed declarations, and model theorem for the executed checker | K4 implemented |
| Claims, assumption trees, Merkle roots, commitments | `Ix.Claim`, `Ix.AssumptionTree`, `Ix.Merkle`, `Ix.Commit` | host | K5, with explicit cryptographic assumptions |
| Lean reference checker | `Ix.Tc` | host; replaced by `Ix.Kernel` in K6 | every consumer migrates, then `Ix.Tc` is deleted |
| Rust kernel | `crates/kernel`, `Ix.KernelCheck` | host fast path | differential parity against `Ix.Kernel`; verdicts are not certified |
| In-circuit kernel | `Ix.IxVM.Kernel` (Aiur program) | separate implementation | refinement to `Ix.Kernel` is the long-term composition point; out of scope here |
| `lean4ix` / Lean4Lean verification | `Ix.Tc.Verify`, `Ix.Compile.Verify`, `Benchmarks/Lean4Lean*`, the test runner and TruthMines member, and the Lake dependency named `lean4lean` | outside the closure | section 11 removes the dependency, old proofs, targets, FFI proof loader, CI jobs, Nix override, and generated benchmark dependencies; useful contracts and audit behavior move to `Ix.Kernel` first, without importing the old specification |
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
- The baseline annotation law that annotations never steer reduction.
  P09 proposes a narrow, proved exception: a validated `.never` binder
  licenses omission of beta argument rechecking, with the same reduct.
  Any such change must update the operational policy explicitly. Internal
  annotation validation remains mandatory; failures follow P01's diagnostic
  contract rather than implying non-convertibility.
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
| K6 | Measured core improvements, all consumers on `Ix.Kernel`, and complete removal of `Ix.Tc` and `lean4ix` verification machinery | K3, K4 for final cutover; core changes can start after K2 |
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

### K2: inductive profile and first release (release gate complete, 2026-09-29)

1. Done for the ordinary class: shape reading, formation (telescopes, index
   fit, universe bounds, strict positivity by the shape), elimination mode
   with the singleton exception, recursor and rule typing, exact comparison
   with the stored block, iota in `whnf` through published typed rules, and
   the `Prop` restriction; structures with projections, eta, iota, and the
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
   projection out of a non-structure declined and a bad field index rejected,
   a wrong iota theorem declined by conversion search. Literals (`Tests/Ix/Kernel/Literals.lean`): a
   literal at `Nat`, `3 = succ 2` and `0 = zero` by `Eq.refl`, `add 2 2 = 4`
   through iota on literal majors, wrong equations declined, a literal naming
   an uninstalled family a missing reference, one naming a non-`Nat` family
   ill-typed. `Eq` with K-like reduction (`kSubst` in `Inductives.lean`).
   Quotients (`Tests/Ix/Kernel/Quotients.lean`): the five primitives in
   order, `Quot.lift f h (Quot.mk a) = f a` by `Eq.refl`, the eliminator at
   a constructor application; a primitive before what it refers to, a
   duplicate, and soundness over a non-equality rejected; `f a` against
   `f b`, a non-primitive former, and a non-standard axiom declined.
   Axioms (`Tests/Ix/Kernel/Axioms.lean`): `propext` over `Eq` and `Iff`,
   `Classical.choice` over `Nonempty`, each used; an axiom before its
   interfaces, an `Iff` with a small eliminator, and a duplicate rejected;
   other axioms decline.
5. Differential run against `Ix.Tc` (done): 38 categorized shared-input
   comparisons, including positive K2 routes, corruptions, and explicit
   policy differences. Raw input trees and verdicts are retained as JSONL;
   the test bridge is not certified Ixon ingress.
6. `docs/kernel.md` and CI (done), including P01's corrected failure
   contract, P02's fidelity statements, and the section 11 removal ledger.

Exit: `lake -d IxKernel build --wfail` and `check-kernel` pass on a clean
checkout; the theorem applies to the fixtures; the release is usable
without Ixon bytes, `Ix.Tc`, or claims.

### K3: Ixon ingress and exact egress (implemented)

1. Land the `Ix.Ixon.Types` split (done, `xztqxzxr`). Production codecs and
   the standalone kernel use the same pure data definitions. Hash-dependent
   projection defaults remain in the host compatibility module.
2. `Ix.Kernel.Ingress`: expand `share`, resolve `refs` and `univs` tables,
   map projection constants to `ConstRef`, read Nat blobs to `Nat`, reject
   strings and unsupported binder modes, check reference bounds and block
   ownership (done).
3. State the reading relation between an Ixon constant and the kernel
   declaration; prove ingress success establishes it, including declared
   types, universe counts, mutual identities, and binder modes (done, with
   deterministic expression readings and exact installed primary records).
   Egress is implemented with retained layout: `record_roundtrip` and
   `records_roundtrip` prove exact source recovery after successful reading
   at the same fuel/context. Expanded raw terms alone do not determine
   sharing, table order, unused entries, or let hints; layout retains those
   choices. The writer rebuilds payloads from raw terms and validates their
   complete reading, checks numeric bounds and exact list lengths, and
   validates reconstructed projection variants and owners. It uses a blank
   `Context.source`, with source tables retained in the layout. These are
   serialization contracts, independent of typing, key uniqueness, wire
   canonicality, and hashes. The CLI round-trip replacement uses these
   operations during the D02 consumer cutover.
4. `checkEnv` over a list of address-to-constant pairs and the blob bytes
   behind literals, composed with certified admission; theorem for the
   Ixon-shaped in-memory input (done: `checkEnv_reading` and
   `checkEnv_has_model`). The host supplies the order, pairs, and blobs;
   addresses remain keys and each physical record retains its own reading.
5. Tests on environments compiled by `Ix.CompileM` from the tutorial corpus,
   loaded by the ordinary host loader, which remains untrusted (done: 26
   cases including altered rules, field counts, header counts, and K flags;
   all also round-trip through the certified reader/writer with exact record
   and production-byte equality; CI retains exact inputs and outcomes).

The production-layout investigation corrected the K2 fixture assumption:
Ixon keeps inductives and recursors in separate records. `Ix.Tc.Ingress` and
Rust ingress preserve those identities; their recursor checkers recover the
family from the major premise before comparing the full generated candidate.
K3 therefore makes the model's recursor reference explicit, associates
separate records without renumbering them, and admits family/constructors
alone when no recursor is supplied. `Certified.Ordinary.Stage` shares Nat and
structure fact proofs between both admission stages. No absent recursor is
generated or checked. The ordinary profile uses syntactic major discovery;
future WHNF under binders must retain their local context. Mutual/nested
auxiliary recursors remain a later profile extension.

The initial pure association search scans remaining declarations. P04 should
add a proved index from major-family references to candidate recursors,
together with the checked environment index, preserving full validation and
input coverage. The current change removes unnecessary recursor checking
for family-only inputs; it makes no measured speedup claim.

Exit: acceptance of Ixon-shaped input establishes the meaning of the
selected declarations; unsupported input declines explicitly.

### K4: Ixon bytes (implemented and validated)

Implemented: production anonymous encoders/decoders moved unchanged into
`Ix.Ixon.Codec`, reexported by the host; structural count/address predicates
split into `Ix.Ixon.Wire`; all eight selected codec proof modules retained
under `Ix.Ixon.Verify`, with source revision/path headers. These proofs
use the pure universe wire predicate; D01 deleted the old copies. This removes the retained
chain's transitive `Catalog`/Lean4Lean dependency and preserves the full
all-variant domain, including expression spines, modes, and arbitrary side
tables. `deConstantExact` and its inverse/cursor/suffix theorems add whole-buffer
framing without changing the old prefix API. Dedicated audits freeze the
contracts and confirm the codec/data closure is Lean core only, the proofs
use only Lean/Std tooling, and execution reaches no project replacement.

`Ix.Ixon.Bounded.Universe` adds a separate entry point that checks a byte
limit, reserves an expanded-node charge before constructing
successor chains, and threads one budget through binary children. Proofs
establish exact accounting and production value/cursor agreement, plus the
converse for every successful production read within the node limit. The
full-buffer API has round-trip and suffix-rejection theorems; a node limit
below `UInt64.size` proves the universe wire invariant. Adversarial controls
include a ten-byte `UInt64.max` successor claim, rejected before reading its
base or constructing the chain. These are byte/tree-size limits, not a
runtime heap or wall-clock bound.

Complete records now use `getConstantWithUnivs`, a shared production grammar
whose equivalence to the old decoder is proved for all inputs and states.
`Bounded.Constant` threads one expansion budget through the entire universe
table using a tail loop without allocating the claimed array capacity.
Its exact successful domain is the production exact decoder intersected
with the input-byte and aggregate universe-node limits. All constant
variants retain round trips and nonempty-suffix rejection.

`WireCheck` checks exactly `Constant.wireWF`; its expression/universe results
carry telescope counts so recursive validation does not rescan tails.
`Canonical.deConstant` composes bounded decoding, wire validation, and
equality with production re-encoding. Its iff theorem characterizes success
as a wire-well-formed constant whose serialization is exactly the input and
which fits both limits. Canonicality here concerns byte spelling; it does
not establish mutual-block member order or typing. Directed controls reject
nonminimal integer tags, split successor prefixes, ignored universe-tag
sizes, and non-Boolean axiom flags that the production decoder accepts.

`Ix.Ixon.Admission.checkBytes` now composes canonical record decoding with
K3's actual checker. A short-circuiting preflight enforces record count, blob
count, and a total payload-byte limit shared across both lists before any
decoding. Per-record byte and universe limits are explicit, with one node
budget across each entire universe table. Tail-recursive decoding preserves
keys and order. Errors distinguish batch limits, record decoding at its
original position/address, and unchanged kernel rejection/decline outcomes.

`Verify.Admission` proves the preflight and decoder's exact successful
domains. Its `RecordsRead` relation names every complete canonical payload,
including unused side tables, without assuming a host decoding result.
`checkBytes_ok_iff` composes this reading with the same in-memory checker;
`checkBytes_of_reading` preserves every kernel outcome at the same fuel.
The reading and model theorems establish which declarations the bytes
describe and install, and successful admission proves both key lists unique.
Literal blobs retain their supplied bytes and K3 interpretation; no canonical
blob spelling or content-hash authentication is assumed.

The adapter lives outside `Ix.Kernel`. Its implementation imports no proof
module; the broad inverse proofs and Std bit-vector tooling stay in the
separate proof closure. `Admission.Audit` freezes the adapter independently
without widening either existing import allowlist. All 26 compiler fixtures
exercise both byte and in-memory admission and compare exact decoded inputs,
outcomes, and reasons. Production consumer migration remains D02.

`Verify.ReaderBounds` proves that successful production reads preserve their
buffer and advance within it, with at most two structural units per consumed
byte. The bound covers compressed expression telescopes, reference-index
vectors, all constant variants, and arbitrary noncanonical successful reads
from nonzero cursors. Counted-array errors decompose into a successful prefix
and one failing element; for byte-consuming elements, the successful prefix
is bounded by available bytes even when the declared count is `UInt64.max`.

`Constant.resourceSize` counts structural constructors and variable table
slots; expanded universe nodes use the existing separate budget.
`Verify.ConstantBounds` bounds every exact decoded record by twice its input
size and combines that result with the bounded universe table.
`checkBytes_resources` composes the same installed byte reading with an
aggregate limit of `2 * maxTotalBytes + maxRecords * maxRecordUnivNodes`.
The proofs add no parser traversal or admission operation. They do not bound
heap bytes, wall time, blob interpretation, or ingress/checker expansion.

`Ix.Ixon.Projection` now reconstructs all four projection variants from
physical mutual-block positions, using the certified projection writer and
`Address.blake3Pure` over complete production encodings. Its request limit
includes reused projections and is reserved before writing/hashing; index
overflow and non-32-byte owners fail explicitly. Existing exact records are
reused, fresh records are prepended, and conflicting payloads at computed
keys fail without assuming hash injectivity. Standalone definitions and
recursors retain their primary addresses.

`ProjectionProofs` characterizes the exact successful extension independently
of the loop: every required member/constructor projection is present, every
added record has a structural source and computed hash, all supplied records
and lookups are preserved, primary declaration order is unchanged, and output
count is bounded by input count plus the request limit. The new `checkBytes`
entry composes canonical reading, reconstruction, and the same kernel at the
same fuel and literal family, with exact outcome and model theorems.

The new adapter is outside the dependency-free kernel/codec package; its root
package audit allows exactly the shared Blake3 types and pure hash module,
and excludes both hash FFI backends. Existing import and execution boundaries
are unchanged. Primary/alias/blob key authentication remains K5.

`Ix.Ixon.BlockOrder` now compares the physical input directly: computed
projection keys for recursive references, supplied keys for external aliases,
decoded natural/string values, and universes rebuilt by the unchanged shared
ingress rules in `Ix.Ixon.ReduceUniverse`. Stable merge sort and consecutive
grouping refine one address-seeded class until an unchanged pass is observed.
Acceptance requires the resulting classes to be the original ordered
singletons. Exhaustion returns a distinct error; it never returns an
unfinished partition. Comparison descent and refinement passes have explicit
limits, independent of the existing byte, universe, and projection limits.

The implementation follows the production Rust lexicographic comparator,
including unequal vector lengths; the old Ix.Tc mirror compared lengths
first. It runs full refinement without the native strong-order/hash-equality
shortcut. `BlockOrderProofs` gives an independently counted derivation for
the exact successful loop domain, final fixed-point and fuel-monotonicity
theorems, and exact block/byte acceptance contracts. The byte entry executes
canonical decoding, projection reconstruction, ordering, and the same kernel;
all final kernel outcomes are preserved on ordered inputs and accepted byte
inputs have exact installed readings and models. It assumes neither compiler
ordering metadata nor hash injectivity. Rust agreement is differential
evidence, not a theorem of compiler or native-kernel equivalence.

`Verify.Work` through `WorkRecord` now account for the complete bounded record
grammar on both success and failure. The ghost interpreter erases exactly to
the production outcome, including error text, unchanged bytes, and cursor.
Compositional byte potential and transferable credits retain work spent before
an error, with only one terminal-failure allowance across nested binds. Units
count byte attempts/copies, tag reconstruction, expression/declaration and
collection construction, telescope folds, reserved universe expansion, and
record framing/byte checks. Declared counts never supply work credit or reserve
array capacity. The entire universe table shares one expansion allowance;
reserved construction is conservatively charged even if a descendant fails.

Every bounded record has work at most `16 * input.size + 2 * universeBudget + 3`.
`WorkAdmission` preserves the canonical parser stage's complete production
result and short-circuit behavior. Without a success premise, aggregate parser
work is at most `16 * maxTotalBytes + maxRecords * (2 * maxRecordUnivNodes + 3)`;
preflight failure performs no parsing. Production executes no counters and its
decoder/admission sources are unchanged. These are abstract parser units, not
heap bytes, wall time, or arithmetic bit complexity. Canonical validation and
re-encoding, batch administration, projection hashing, ordering, literal
interpretation, ingress, and checking are outside this decoder metric.

Port the earlier plan's serialization milestone against the split types:
schema and version, pure encoders and bounded decoders for the supported
subset, `decode (encode x) = .ok x`, decode validity, canonical re-encoding,
full-input consumption, and adversarial mutation tests with the Rust codec
as a differential oracle. Compose with K3 so the statement names which
declarations the bytes describe. Canonical block order validation now has
its own contract: a stored mutual
block is accepted only in the order the kernel recomputes, so a permuted
block is rejected without trusting compiler metadata. The certified encoder
and `Address.blake3Pure` now reconstruct projection addresses through the
separately audited adapter; production consumers will adopt this path during D02.
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
| `Ix.Compile.Verify.Audit` | Retain only audit behavior needed by the new contracts in `Ix.Kernel.Audit`; delete the old verification consumer in section 11 |
| `Tests/Ix/Tc`, `Tests/Ix/Kernel/PrimAddrs` | Ported to `Tests/Ix/Kernel`; the differential tests run against `check-rs` |
| `Ix.lean` | Imports `Ix.Kernel` |

One parity caveat is deliberate. `check-lean` trusts every referenced
constant's declared type regardless of order, so an environment with a
reference cycle would be accepted by it and by the Rust kernel; the ordered
fold rejects the forward reference. Real environments have no cycles, and
the difference is the correct direction.

The concrete work packets and exit checks are in section 10. The revised
order is:

1. P00–P03: reproducible baselines, failure/fidelity contracts, and reuse of
   already formed expected types; finish the K2 release gate.
2. P04–P06: combine annotation with checking, index addressed environments,
   and defer local-context lifting to lookup.
3. P07–P10: publish typed rules, traverse application spines once, use
   positive structural conversion before delta, integrate the proved
   `.never` beta shortcut, and improve level equivalence.
4. P11: consolidate validation traversals and narrow imports, keeping
   runtime schemas distinct from semantic predicates.
5. P12: only then promote interning, memoization, certified Nat shortcuts,
   and bounded parallel checking where retained workloads justify them.
   Complete string, mutual/nested, K, and reflexive-block coverage needed
   by the parity corpus. No union-find conversion cache.

Core changes can proceed without Ixon bytes; the final consumer cutover
still needs K3 and K4. Removal of the old verification dependency follows
section 11 and does not wait for every optional performance promotion.

The first target is `Ix.Tc` parity on the three recorded workloads with
bounded memory. After that, the Rust gap is narrowed with the same
discipline. When every consumer is migrated and the differential corpus
agrees, delete `Ix.Tc` and close the removal ledger. The `lean4ix` dependency
and verification trees must already be gone, or leave in that same cutover;
keeping an unused optional dependency or obsolete proof target does not
meet the milestone.

### K7: binder modes and the optimizations they license

Ixon v3 carries usage, ownership, and locality contracts on binders, results,
and lets. Ix's source-contract frontend surfaces them from Lean. The kernel
erases them at ingress, and the egress layout retains them (section 3.1). This
milestone gives them meaning and uses them:

1. Contract checking with a kernel-defined meaning: section 12, phase C,
   defines the semantics of usage, ownership, locality, and borrows, and
   certifies a checker against it. Upstream's resource admission
   (`Ix/Resource`) is the algorithm to port. The set model continues to
   ignore contracts; phase C's guarantee is stated against an instrumented
   evaluation that is compatible with that model.
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
| `lake run check-kernel` | Standalone and host builds, audits, provenance, certified fixtures, host differential and compiler-ingress cases, Rust codec and canonical-order comparisons |
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
  `lean4ix` dependency leave no later than `Ix.Tc`.
- BLAKE3 is `Blake3.Pure.hash` wherever a certified operation hashes; the C
  and Rust backends are host accelerators.
- The kernel is certified as its own dependency-free Lake package
  (`IxKernel/`) over the shared `Ix/` sources, and `Models/SetTheory`
  depends on that package only.
- The `argumentcomputer/lean4ix` dependency, named `lean4lean` by Lake and
  exporting `Lean4Lean.*`, is removed from the repository entirely,
  together with its consumers (`Ix.Tc.Verify`, `Ix.Compile.Verify`, the
  Lean4Lean benchmarks and test runner, their Lake/CI/Nix targets, and the
  separately pinned upstream TruthMines package), no later than the K6
  deletion of `Ix.Tc`; nothing new may depend on it. Section 11 is the
  concrete removal checklist and gate.
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

## 10. Concrete implementation sequence from the review

The checkpoint below distinguishes completed work from planned packets.
The reviewed baseline is `ade9216d` in the
Git-backed jj workspace `~/projects/ix-certified`. Use a small jj change
for each coherent implementation/proof/test unit; the larger packets need
several changes. Keep mechanical moves separate from behavioral changes.
Each change description records its packet, contract, validation, and
measured effect. The local review and experiments live under ignored
`plans/`; the implementation and its durable contracts must be tracked.

P00 → P01 → P02 → P03 and the K2 release gate are complete. Follow
P04–P11 in order, allowing the independent K3/K4 work to
proceed after K2. P12 and the K6 consumer cutover use those results. D00–D02
in section 11 remove the obsolete verification system as soon as their
replacement contracts are ready; they do not depend on caches or interning.

| Packet | Deliverable | Prerequisite |
| --- | --- | --- |
| P00 | Reproducible correctness and performance baselines | reviewed tree |
| P01 | Honest search outcomes and fuel reporting | P00 |
| P02 | Exact annotation/declaration fidelity and prefix preservation | P01 |
| P03 | Reuse formed expected types and context extensions | P01 |
| K2 gate | Supported-profile differential tests, docs, CI, model build | P00–P03 |
| P04 | Annotation and checking share inferred evidence | P02, P03 |
| P05 | Verified indexed environment for addressed checking | P02 |
| P06 | Local contexts that lift at lookup | P04 |
| P07 | Structured, typed published computation rules | P03, P02 |
| P08 | Single spine traversal and positive structural conversion | P01, P07 |
| P09 | Proved beta shortcut for `.never` binders | P01, P04 |
| P10 | Sound associative/commutative `max` normalization | P01 |
| P11 | Shared validation traversals and narrower module boundaries | P02, P04, P07 |
| P12 | Workload-driven promotions and complete consumer parity | K3, K4, retained measurements |

Implementation checkpoint (2026-09-29):

- P00's tracked native runner, seven fixture modules, and 37 baseline
  configurations are in jj change `xqrwovol` (`457591a8`). P03 adds isolated
  diagnostic operation counters and alternating native comparisons, completing
  P00's instrumentation gate. Counters exclude startup and fixture preparation;
  diagnostic timings are discarded. Commands and scope are in the benchmark README.
- P01 is implemented in `qlslmuxn`. The strict standalone build passes
  (132 jobs), including the frozen theorem/axiom/import/runtime checks and
  all seven fixture modules. The provenance executable passes with 97
  ported modules, 25 authored modules, and four license files. All 37 native
  configurations accept; the paired comparison and diagnostic overhead
  are recorded in `Benchmarks/Kernel/README.md`. The public theorem
  statements and axiom/import allowlists remain unchanged.
- P02 is implemented in `vqsxslky`: `annotate_erase`, reference transfer,
  exact installed-block readings through every route, and old-lookup
  preservation through the fold. The strict standalone build passes
  (134 jobs, eight fixture modules), as do the six new fidelity axiom
  audits. Runtime closure remains 899 compiled functions with the same
  16 inherited externs. Provenance passes with 97 ported and 26 authored
  modules. The pinned Mathlib model build and full dependency audit pass
  (981 jobs). This Nix toolchain needed a temporary overlay supplying
  Lean 4.33.1's pinned `leantar` 0.1.20; dependency revisions were unchanged.
- P03 is implemented in `pnnnlonx`: `checkAgainst` reuses formation for rule
  endpoints, `checkType_acceptance` preserves successful checking at the same
  fuel, and branches explicitly share context extensions. The strict standalone
  build passes (134 jobs), as does provenance (97 ported, 26 authored, four
  license files). Runtime grows by one helper to 900 functions, with the same
  16 inherited externs. The ten diagnostic probes retain outcomes and confirm
  reduced formation/inference/lifting work on admission. All 37 alternating
  native comparisons accept; small admission probes improve about 5–9%, with
  mixed larger-input timings and no separate context-sharing speedup claim.
  The full counts, timing ranges, and RSS are documented in the benchmark README.
- The K2 release gate and D00 ledger are implemented in `ulwuykwl`.
  `lake run check-kernel --with-model` passes in a fresh jj workspace with
  no project Lean artifacts (134 standalone, 144 host, 342 differential
  build, and 975 model jobs), reusing pinned dependency caches and unchanged
  Rust artifacts. All 38 differential cases pass with explicit outcomes,
  including the K-flag and opaque-transparency policies in `docs/kernel.md`.
  CI runs the same gate and retains exact raw inputs and verdicts as JSONL.
  D00 identifies the pure codec roots to preserve and the `Catalog` import
  that must be split before removing Lean4Lean transitively.
- K3's ingress checkpoint passes the incremental full gate: 144 standalone,
  154 host fixture/provenance, 457 runner build, and 975 model jobs; 38/38
  differential and 26/26 compiler ingress cases. The public theorem statements
  are unchanged. Runtime closures are 920 core and 961 ingress functions,
  with no additional foreign replacements beyond the documented Lean runtime
  array/byte accessors. Provenance covers 97 ported, 35 authored modules and
  four license files. The physical-layout correction and family-only stage
  are part of K3, not a claim of general mutual/nested support.
- K3 egress retains layout and proves complete record/list round trips at
  the same fuel/context, with writer fidelity independent of admission.
  The full incremental gate passes: 150 standalone, 160 host fixture/provenance,
  467 runner build, and 975 model jobs; 38 differential and 26 compiler
  ingress/byte-exact egress cases. Ten pure fixture modules include adversarial
  layout, projection, numeric-bound, and list-length controls. The public
  theorem statements are unchanged. Runtime is 920 core, 962 ingress, and
  202 reader/writer functions; the extra ingress helper resolves actual
  supplied records, and egress additionally uses bounded `UInt64.ofNat`.
  No project execution replacements are reached. Provenance covers 97
  ported, 40 authored modules and four license files.
- K4's codec extraction and preservation checkpoint passes the full gate:
  164 standalone, 173 host fixture/provenance, 529 runner build, and 975 model
  jobs; 38 differential cases, 26 compiler ingress/exact-egress cases, and the
  production codec unit/property suite with Rust serialization comparisons.
  Eleven pure fixture modules include exact framing, all constant variants,
  integer boundaries, and truncation tests. The temporary legacy codec chain
  also builds against the extracted predicates (71 jobs). Provenance covers
  97 ported, 53 repository-authored/reorganized modules and four license files.
  The codec runtime closure is frozen at 269 functions, 51 inherited externs,
  two inherited array accessors, and no project replacements; kernel/ingress/
  egress closures and public theorem statements are unchanged. The selected
  D00 codec contracts are preserved, so D01 can proceed independently of the
  K4 byte-admission work that was still pending at that checkpoint.
- D01 removes both lean4ix/Lean4Lean dependency paths, the two old proof
  trees, the proof-only FFI crate, replay benchmark/runner, backend dispatch,
  and obsolete Lake/CI/Nix targets. TruthMines source/output and all four
  affected Lake manifests are updated with unrelated pins retained. A
  tracked guard checks active references and runs in the certified and Nix
  gates. In a fresh jj workspace without project Lean artifacts or a
  Lean4Lean checkout, all 24 remaining targets build strictly, primary/CLI
  and generator tests pass, and the full kernel/model gate retains the
  38 differential and 26 ingress/exact-egress cases. Native x86_64-linux
  Nix checks and the distributable CLI pass; nextest reports 1,533 passed,
  14 skipped. The removal ledger in `docs/kernel.md` records exact scope,
  fixture dispositions, immutable source revision, and remaining limits.
- K4's bounded-universe checkpoint passes the incremental full gate:
  166 standalone, 175 host fixture/provenance, 531 runner, and 975 model
  jobs; 38 differential and 26 compiler ingress/exact-egress cases, plus
  the codec suite's generated bounded-universe/Rust serialization check.
  Six new exact axiom checks cover accounting, production-read completeness,
  bounded round trips, success limits, suffix rejection, and wire validity.
  The codec runtime closure is 282 functions with the same 51 inherited
  externs, two inherited unsafe accessors, and no project replacement.
  Core/ingress/egress theorem statements and execution closures are unchanged.
  Provenance covers 97 ported, 55 authored/reorganized modules and four
  license files. Evidence is in `plans/review/k4-universe-bounds/summary.json`.
- K4's bounded/canonical record checkpoint passes the incremental full gate:
  172 standalone, 181 host fixture/provenance, 539 runner, and 975 model
  jobs; 38 differential and 26 compiler ingress/exact-egress cases. The host
  codec suite includes generated aggregate-budget and canonical record
  checks against Rust serialization. Ten new exact axiom checks cover the
  grammar equivalence, table budgets, bounded domain, full wire validator,
  and canonical domain/round-trip/framing contracts. The codec runtime
  closure is 331 functions and 52 inherited externs; the added extern is
  Init's byte-array decidable equality. Unsafe/replacement counts and the
  core/ingress/egress boundaries remain unchanged. Provenance covers 97
  ported, 61 authored/reorganized modules and four license files. Evidence
  is in `plans/review/k4-canonical-records/summary.json`.
- K4's byte-admission checkpoint passes the incremental full gate:
  176 standalone, 184 host fixture/provenance, 541 runner, and 975 model
  jobs; 38 differential and 26 compiler ingress/byte-admission/exact-egress
  cases, plus the codec suite. Canonical byte admission preserves all 20
  accepted, five declined, and one rejected compiler-fixture outcomes and
  their exact reasons. Recorded inputs include ordered record/blob bytes,
  all limits, checker fuel, and the literal-family reference. Twelve new
  exact axiom checks cover batch accounting, exact readings, aggregate
  expansion, acceptance and outcome fidelity, key uniqueness, model
  existence, and the executable operation. The independent adapter runtime
  has 1,250 compiled functions, 56 inherited externs, and two inherited
  unsafe array accessors, all already present in the kernel/codec closures;
  there are no project replacements. The narrower existing import and
  runtime boundaries remain unchanged. Provenance passes with 97 ported,
  64 authored/reorganized modules, and four license files. Tested source:
  `d8f5ca265ed496b060c197dfaedf87a77cd4ce47`; evidence:
  `plans/review/k4-byte-admission/summary.json`.
- K4's reader-resource checkpoint passes the incremental full gate:
  179 standalone, 187 host fixture/provenance, 543 runner, and 975 model
  jobs; all 38 differential and 26 compiler ingress/byte-admission/exact-egress
  cases, plus generated resource checks against Rust serialization.
  Thirteen new exact axiom checks cover byte-consumption bounds, failed
  counted-array prefixes, complete-record structure, and the accepted batch's
  resource theorem. Tests include nonzero cursors, noncanonical successful
  reads, compressed telescopes, large index vectors, and huge counts that
  stop at the first malformed element. The parser/admission implementations,
  import allowlists, and runtime closures are unchanged. Provenance covers
  97 ported, 67 authored/reorganized modules, and four license files. Tested
  source: `e34c8cc3aad3f7d13fbc65a3c4f20351be3352e5`; evidence:
  `plans/review/k4-reader-bounds/summary.json`. At that checkpoint, complete
  parser-work accounting remained open, including nested failure paths and
  element-reader cost.
- K4's pure projection-reconstruction checkpoint passes the incremental full
  gate: 179 standalone, 197 host fixture/provenance, 550 runner, and 975 model
  jobs; all 38 differential and 26 compiler cases, plus the codec suite.
  Fifteen compiler cases omit 44 projection records in total, recovering
  every original key/value store and primary order; all 26 retain the same
  verdict and exact reason. Inputs retain the projection-free record list
  and request limit. Sixteen new exact axiom checks cover structural request
  enumeration, exact bounded extension, preservation, completeness, origin,
  byte admission, and model existence. The separately audited pure-hash
  adapter has 1,381 functions, 70 inherited externs, two inherited unsafe
  accessors, and no project replacement. All narrower existing boundaries
  remain unchanged. Provenance covers 97 ported, 70 authored/reorganized
  modules, and four licenses. Tested source:
  `19313f7ea597202ed3d544980d898ea6f5d8ba7c`; evidence:
  `plans/review/k4-projection-reconstruction/summary.json`.
- K4's canonical-block-order checkpoint passes the incremental full gate:
  179 standalone, 202 host fixture/provenance, 607 runner, and 975 model jobs;
  all 38 differential, 26 compiler, and 1,117 native Rust order comparisons,
  plus the codec suite and 44 directed order regressions. Compiler cases
  execute the new order-aware byte path and preserve every prior verdict and
  reason. The Rust oracle independently reconstructs projection keys and
  ingresses the original Ixon records; it compares both final classes and
  native acceptance, without consuming a Lean-produced order. Thirteen new
  exact axiom checks and six frozen signatures cover the refinement and
  admission contracts. The separate runtime closure has 1,509 functions,
  77 inherited externs, two inherited unsafe accessors, and no project
  replacement; all earlier boundaries remain unchanged. Provenance covers
  97 ported, 74 authored/reorganized modules, and four licenses. Tested source:
  `d0377deba61b6b57fe24b6a72bacaeb0b1098990`; evidence:
  `plans/review/k4-block-order/summary.json`. At that checkpoint, K4 still needed
  complete parser-work accounting, including nested failures and element-reader cost.
- K4's complete abstract parser-work checkpoint passes the incremental full
  gate: 188 standalone, 211 host fixture/provenance, 621 runner, and 975 model
  jobs; all 38 differential, 26 compiler, and 1,117 Rust order comparisons,
  plus the codec suite. Thirty-seven parser guard groups cover exact operation
  counts, every fixture truncation at nonzero cursors, all 256 one-byte tags,
  maximum declared counts, nested element failures, shared expansion budgets,
  and admission short-circuiting. Eighteen exact axiom checks and eight frozen
  contracts cover erasure, work composition, records, and batches. All prior
  import/runtime boundaries remain unchanged; nine production codec/admission
  files are byte-identical to the preceding checkpoint. Provenance covers
  97 ported, 82 authored/reorganized modules, and four licenses. Tested source:
  `5079c6edf77b88e2c267186a169998c36646b7e5`; evidence:
  `plans/review/k4-parser-work/summary.json`. This closes K4 under the stated
  parser metric and supported admission profile.
- P04–P12 and the remaining K5–K7 work stay open; whole-corpus parity has
  not been run. D02's runtime consumer cutover and deletion of Ix.Tc remain
  required.

### Ontology and contracts to preserve

The refactor gives the existing concepts explicit boundaries:

| Boundary | Runtime data | Evidence / responsibility |
| --- | --- | --- |
| Raw input | `Decl`, `Block`, `VExpr`, `VLevel`, `ConstRef` | Exact supplied identities, bodies, types, and universe counts |
| Reading | `AExpr`, `PropWhen` | Erases to that input; scope includes annotation conditions |
| Checking | `Typed`, `TypedSort`, `Reduced`, `Conv` | Semantic claims indexed by the exact environment and context |
| Candidate admission | Shape/description/primitive candidates | Recognition is separate from validation and checked publication |
| Storage | `ConstantEntry`, concrete store, functional `Environment` | Lookup agreement, old-entry preservation, `Realizes`, `WF` |
| Foundation | `SetTheory`, interpretation, `WellDenoted` | Existing mathematical model; no new project axioms |

Keep the three frozen public theorem statements, including the generic
`[DecidableEq β]` API and the explicit `SetTheory` assumption. Add fidelity
and representation lemmas alongside them. `StepClaim` alone does not state
input fidelity or old-entry preservation. `ConvClaim` composes only with
formed intermediate terms; it is not an unconditional equivalence relation.
Erased proofs are not a runtime storage optimization target.

Representation changes need lookup/erasure simulation and the existing
semantic claims. Search-strategy changes also need a stated coverage
comparison: preserve prior successes with an explicit fuel correspondence
or a proved fallback, and measure any new successes separately. Equal fuel
does not mean equal work. A successful model theorem alone cannot rule out
a checker that declines more inputs. Do not promise Lean completeness from
finite testing or require identical normal forms from different strategies.

### P00 — retain the baseline and expose the costs

Add `Tests/Ix/Kernel/SearchOutcomes.lean` and a native benchmark target
rooted at `Benchmarks/Kernel/Certified.lean`. Promote the useful inputs from
the local probes into tracked fixtures, without importing the reference
checkout. Wire correctness fixtures into `check-kernel`; keep timing runs
outside the pass/fail CI gate. Initially characterize the low-fuel defect,
then change its expected outcome in P01.

Retain the following baseline observations, all sequential Lean `--run`
measurements with `Nat` keys, not native corpus performance:

| Input | Sizes | Observed milliseconds |
| --- | --- | --- |
| Independent definitions | 1K / 2K / 4K / 8K | 77 / 278 / 1113 / 4531 |
| Nested lambdas | 16 / 32 / 64 / 128 | 5 / 40 / 310 / 4350 |
| Context pushes | 1K / 2K / 4K / 8K | 39 / 158 / 654 / 2531 |
| Typed stuck application spine | 400 / 800 / 1600 / 3200 | 15 / 44 / 221 / 623 |

The depth-128 phase probe spent 3974 ms annotating the body, versus 82 ms
inferring it afterward; annotation took about 98% of the measured phases.
Add addressed keys, rule-heavy inductive/structure/quotient workloads,
repeated references, and beta-heavy terms before optimizing those paths.

Exit: a reproducible native command records revision, Lean version, backend,
input size, fuel, outcome, median/range of five runs after warmup, and peak
RSS. Separate construction from checking, and force pure results inside
timed regions. Record operation counts in diagnostic runs for inference,
lookup/comparison, lifting, spine visits, and rule argument checking.
Native results establish a new baseline; do not compare them directly to
the interpreter numbers as a speedup.

### P01 — distinguish exhaustion, search failure, and invalid input

Change `Infer.lean`, `Annotate.lean`, `Certified/Checker.lean`, the ordinary
reader/checkers, and `Check.lean`. Introduce an internal structured search
failure type for exhausted, unsupported, unresolved, and independently
detected malformed input. Retain public `Error.rejected`/`Error.declined`
and `Config.fuel`. Carry causes through nested inference/conversion instead
of erasing them with `Option` or `.toOption`.

Separate a step that does not apply from a step blocked by search failure.
Return normalization progress together with why it stopped; a partial
`Reduced` is still sound, but is not evidence that normalization completed.
Completion means no rule in the supported strategy applies, not completeness
for all Lean reductions. Candidate mismatch permits the next strategy;
an exhausted optional strategy must not prevent a later proved success.
When no strategy succeeds, retain the exhaustion/unsupported cause rather
than treating it as malformed input. A positive conversion proof obtained
from partial reducts remains usable.

Exit: `A : Type 1 := Type; x : A := Prop` declines, never rejects, at
insufficient fuel and accepts at sufficient fuel (the P00 baseline rejects
at 1 and 2, then accepts at 3). Cover nested annotation exhaustion,
inductive-reader exhaustion, exhausted rule application, and conservative
level-equivalence failure. Duplicate addresses, out-of-scope variables,
wrong universe arity, and missing references still have direct diagnostics.
Update tests that currently assert rejection from unsuccessful conversion
to the documented unresolved outcome; they must still never accept.
Preserve the baseline successful paths and their semantic claims.

### P02 — prove exact reading and installation fidelity

In `Annotate.lean` and `Model/Annotated.lean`, prove the success law
`annotate fuel entries Γ raw = .ok a → a.erase = raw`. Package it with
scope/reference evidence when validated, reusing the existing `Reading`
concept rather than maintaining a second annotation-tree interface.
Prove reference transfer and scoped erasure separately: erasure alone does
not establish that `PropWhen`'s own universe parameters are in scope.

In `Check.lean`, `Env.lean`, and the admission adapters, add installation
lemmas for the exact supplied type, body, reference positions, and universe
count. For generated inductive declarations, use the existing exact block
comparison to connect installed entries to the supplied block. Prove an
accepted step and fold preserve every old lookup, separately from
`StepClaim`; describe newly published equations/facts explicitly. Keep the
current whole-input checks until equivalent evidence replaces them.

Exit: tracked fidelity fixtures cover definitions, let, projections,
literals, universe instances, and all K2 admission routes. Existing public
theorem types and assumptions remain unchanged. These new lemmas are the
composition points for K3 ingress and the P04/P05/P11 refactors.

### P03 — remove small, repeated formation checks

Add `Certified.checkAgainst` in `Certified/Checker.lean`: given an already
formed expected type (`TypedSort` or `FormedClaim`), infer the term once,
convert its inferred type, and return its `TypingClaim` via `convF`.
Implement `checkType` as the wrapper that first obtains formation evidence.
Use `checkAgainst` in `Certified/Signature.checkRule` and
`Certified/Ordinary/RuleChecks.checkRule` so the common rule type is checked
once for both endpoints. Bind and share repeated `Γ.push D` values inside
individual branches of `Infer` and `Annotate`.

Exit: rule formation drops from three common-type checks to one; endpoint
typing and conversion checks remain. The helper's evidence has the exact
same environment/context indices as its caller. Fixtures and the audits
pass, with no cache or entry-schema change in this packet.

### K2 release gate — close the current milestone

Add a host-only `Tests/Ix/Kernel/Differential.lean` bridge for the supported
raw declaration profile and run it against `Ix.Tc`; production ingress is
still K3. The bridge is test infrastructure and never a theorem assumption.
Include positives and corrupted variants for each K2 route. Report accept,
reject, decline, and failure causes separately, with explicit unsupported
cases and the intended ordered-reference difference. Preserve the oracle
inputs/results so the final oracle can become Rust after `Ix.Tc` is removed.
This gate requires supported-profile parity, not full Mathlib support.

Wire the new targets into `lake run check-kernel` and CI. Write
`docs/kernel.md` with the ontology, actual trust boundary, supported profile,
fuel behavior, transparency behavior, and the retirement ledger in section
11. Run `lake run check-kernel --with-model` from a clean checkout. This
closes K2; P04–P12 are not first-release prerequisites.

### P04 — make annotation reuse typing evidence

Replace the annotate-then-reinfer declaration path incrementally in
`Annotate.lean`, `Infer.lean`, and `Check.lean`. First return the exact
reading with the inferred type/evidence already obtained while processing
each binder. Then add an expected-type path for declaration bodies: check
the declared type once and use its formed Pi telescope while checking a
lambda. Use `Model/Checking.lean` (`CheckingClaim.lam`, `typing`, and
`TypingClaim.appChecking`) as proof building blocks.

A returned annotation must still erase to the raw binder domain. Do not
silently substitute the expected domain for the supplied one. Start with
the case where the annotated domain matches the expected domain exactly;
use the existing certified synthesis path otherwise. Supporting merely
convertible domains requires the appropriate context/codomain transport
proof before that fast path is enabled. The expected binder regime must
be justified by formation, including the empty-domain case. Share evidence
locally; do not retain an auxiliary proof-result tree for every node.

Exit: fully annotated subtrees are no longer re-inferred at every ancestor
on the optimized binder path. The nested-lambda benchmark improves, with
counts attributing the change to removed traversals and RSS reported.
Erasure, typing, and baseline acceptance are preserved; adversarial Prop
conditions, dependent binders, lets, and convertible domains stay covered.
No global memo table or wholesale rewrite of the mutual core is needed.

### P05 — index addressed environments behind a proved lookup view

Keep the generic list-backed API and frozen theorem signatures. Factor
admission through a small store interface with lookup, fresh insertion,
block insertion, a reference `Env` view, and proofs of agreement. Add an
addressed implementation in `Ix/Kernel/Store.lean` and
`Ix/Kernel/Store/Address.lean`; use a deterministic ordered index with full
`ConstRef` comparison and keep the entry list for publication.

Prove `Address.cmpBytes` agrees with the structural ordering, establish the
ordering laws, and extend them over member/constructor positions. Implement
the minimal verified balanced tree under the existing Init-only boundary;
do not silently add `Ord β` to public roots or import `Std.HashMap`. Give
lookup, insert, and atomic block insertion their view-agreement lemmas.
The addressed driver must actually use the index for freshness, reference
validation, and inference lookup, with no rebuilding or list scan per step.

Route `checkAddressed` in `Ix/Kernel.lean` through that store and add its
own acceptance theorem and audit roots, derived from the same checked
core/store simulation. Keep `check` as the generic reference instantiation;
share the search implementation between the two. A theorem about the old
list function does not certify a new function merely because their tests
agree. Test arbitrary byte-array keys as well as 32-byte addresses;
`Address`'s constructor does not enforce its documented width.

Exit: old/new lookup and accepted environment views agree, including
duplicate handling and multi-entry publication. Fresh independent
declarations stop making N(N−1)/2 key comparisons; measure index allocation
and scaling on both monotone and shuffled addressed inputs. Later host
adapters select the audited addressed entry point, not the slow reference.

### P06 — store local types relative to their introduction context

Add a concrete local-context representation in `Ix/Kernel/LocalContext.lean`
while retaining `Model.Context` as the semantic specification. Store each
type with its creation depth; pushing adds an unshifted entry, and lookup
lifts by the difference between current and creation depth. First use a
simple persistent representation; changing variable-lookup asymptotics can
be a separate measured step.

Prove the materialized view equals the existing eager context, especially
`view (push A Γ) = (view Γ).push A`, and prove lookup agreement and transport
of `Context.Valid`. Thread the representation through the checker without
materializing its view at runtime on every call. Use the P02/P04 evidence
indices to keep the proofs over that view.

Exit: pushing N constant-size domains performs O(N) additions and no
traversal/lifting of previous entries. Test dependent domains, shadowed
indices, lets, lookup at every depth, and substitution under binders.
Measure whole-checker behavior as well as the isolated push probe, since
work deferred to frequently used variables can offset the construction gain.

### P07 — publish typed rules as a single semantic object

Introduce a small runtime rule schema (`Ix/Kernel/Rule.lean`) containing a
selector, common telescope/type, and both endpoints. Reuse or subsume
`Certified.Signature.Rule` rather than adding a competing schema. Extend
`ConstantEntry`, `Realizes`, and `WF` in `Model/Environment.lean` and
`Model/Support.lean` with typing, formation, equality, scope, and reference
obligations for each published rule.

Migrate producers separately: ordinary recursors, structures, then quotient
primitives. Preserve each producer's admission stage; rule typing must not
be justified circularly by the equation it is publishing. Structure rules
currently check in their published environment, which needs an explicit
staging proof when the schema changes. Publish the checked quotient
interfaces/rules once instead of rediscovering them at every reduction.

Update `Infer.iota`, `reduceByRule`, `projIota`, and `etaStruct` to select the
structured rule, instantiate its certified telescope, and check arguments
once where the endpoint telescopes are proved to agree. Remove the parallel
`facts[1+2*j]`/`facts[2+2*j]` convention only after all producers migrate.
The current recursor/structure hints mean `True`; they cannot justify
removing endpoint checks until the stronger invariant is installed.

Exit: the rule-heavy benchmarks show no repeated endpoint inference or
duplicate argument checking for the migrated paths. Fixtures include
multiple constructors, dependent fields, universe instances, under- and
overapplication, malformed selectors/telescopes, and quotient computation.
Update the Mathlib model build and provenance for changed model files.

### P08 — traverse application spines once and delay delta when possible

Refactor `step` and the rule reducers in `Infer.lean` to carry one head and
argument stack. Prove decomposition/rebuilding and compose reduction claims
as arguments are consumed or reapplied. Dispatch iota/quotient rules using
the existing stack rather than recollecting every application prefix.

In a separate change, add a small positive congruence attempt to `isDefEq`
before delta: matching heads, universe instances, and arguments can yield
a `ConvClaim`; failure falls back to the existing strategy. Do not invoke
the full expensive eta/proof-irrelevance fallback twice. Bound speculative
work and preserve the fallback's fuel allowance. Keep current unfolding
policy for this optimization; separately document and test how definitions,
theorems, and opaques should compare against the external oracle before
changing their transparency or retaining fewer bodies.

Exit: the stuck-spine probe makes a linear number of spine visits. Beta,
iota, quotient, projection, partial applications, and extra arguments retain
their semantic claims and coverage. Matching-head benchmarks demonstrate
avoided unfolds, while a failed cheap comparison still reaches the previous
successful conversion path.

### P09 — integrate the proved `.never` beta shortcut

Move the checked local `BetaNever.lean` experiment into `Claims.lean` with
its exact provenance. Its target is a `ReductionClaim` from
`(.lam .never D b).app a` to `b.inst a`, with no argument-inference premise;
the source term's `WellDenoted` assumption supplies what the set model
needs through non-Prop function-domain uniqueness.

Use it in `Infer.step` for `.never` only. Keep typed beta for binders whose
codomain can be Prop, and retain complete input annotation/typing validation.
Record the operational-policy change from the baseline annotation rule:
the condition selects which checks are needed, not a different reduct.

Exit: the integrated lemma passes the same axiom guard, beta-heavy typed
terms skip the intended argument inference/conversion calls, and Prop-side
and malformed-annotation fixtures remain non-accepting where required.
The local proof is feasibility evidence; a speedup is still to be measured.

### P10 — canonicalize the supported `max` fragment

In `Certified/LevelEq.lean`, flatten nested `max`, order operands
structurally, eliminate duplicates, and remove zero, with a theorem that
evaluation is preserved under every level assignment. Keep existing sound
`imax` rules; do not extrapolate `max` laws to `imax`. Reuse the normal form
for level comparison without changing the mathematical universe model.

Exit: `max u v` and `max v u`, reassociation, idempotence, and zero laws
compare successfully. Valuations where an `imax` argument becomes zero
have explicit regressions. Unresolved comparisons follow P01. This is a
coverage improvement as well as a simplification; report its new successes
separately from runtime measurements.

### P11 — consolidate traversals and clarify module ownership

Replace append-heavy `VExpr.refs`/`AExpr.references` in `Expr.lean` and
`Model/Support.lean` with an accumulator or a direct short-circuit reference
check, proving membership/result agreement. Use P02 to remove duplicate
raw/annotated scans only when the new validation result proves all the
same scope, level, annotation-condition, and reference obligations.

Then make mechanical module moves: small executable syntax/entry/rule
schemas below the checker, semantic predicates in `Model`, candidate
readers distinct from admission, and an optional proof-support umbrella.
Use precise imports instead of the full `Ix.Kernel.Model` umbrella where
possible. Keep the useful Checking/ContextTransport/Substitution helpers;
P04–P07 may now use some of the eight previously unnecessary imports.
Do not introduce a generic syntax functor or rename the whole tree.

Exit: linear traversal counts on large left spines, unchanged validator
predicates, and a fresh source/import/runtime closure inventory. Report
downstream import/build effects separately: the standalone package's glob
still builds every kernel module. Preserve port headers and refresh only
the provenance hashes corresponding to inspected changes.

### P12 — use corpus evidence to finish K6

K3 supplies the proved Ixon reading and K4 the byte/round-trip contracts;
route the tutorial and then InitStd, Lean, and Mathlib workloads through
those APIs. The recorded `Ix.Tc`/Rust timings in section 6 are historical
yardsticks, not measurements of `Ix.Kernel`. Track coverage, runtime, and
peak memory separately for the certified Lean checker and Rust.

Only add interning or memo tables when the post-P04–P11 profiles show
remaining repeated work. Prove simulation and a cache-state invariant;
keys include structural terms, environment/context identity, universes,
and any active reduction policy. Transport evidence explicitly across
extension/weakening. Failed search at one fuel is not a reusable negative
conversion result, and conditional conversion never licenses union-find.
Nat accelerators need their defining-equation proofs before use. A parallel
driver must preserve checked dependency order and model extension, with a
fixed measured memory bound per worker.

Complete unsupported language features according to the actual parity
gaps, each with admission/reduction proofs and adversarial controls. Migrate
the consumer table in section 6, including all four AuxGen operations and
the two validate-lean round trips. For every command labeled certified,
test that success comes from the exact audited `Ix.Kernel` entry point.
Finish D02, delete `Ix.Tc`, and begin K7 only after these gates are met.

### Validation and promotion checklist

For each semantic change, run the strict standalone build and the relevant
tracked fixtures through `check-kernel`; inspect axiom, import, runtime,
and provenance differences before updating frozen reports. Run the model
gate when model statements/producers change and at release/cutover.
Mechanical documentation-only edits do not require rebuilding Lean.

For each performance change, retain before/after operation counts and native
median/range/RSS on its target workload and a small representative mixed
suite. Promote only with a demonstrated benefit and explained regressions;
do not add timing thresholds to CI or promise an unmeasured speedup. Keep
the reference path until simulation and coverage checks justify removing
it. Negative tests check meaningful invalid or unsupported inputs, not
implementation details or line-by-line copies of the new algorithm.

## 11. Eliminate lean4ix and the Ix.Tc verification machinery

This is a required outcome of `jcb/ix-certified`. At the reviewed revision,
the root `require lean4lean` fetches `argumentcomputer/lean4ix` at
`a4188d7c2979378d85c6bb41fdd96c3a48a71371`, and its modules are named
`Lean4Lean.*`. TruthMines separately pins upstream `digama0/lean4lean`.
Removing only the root URL would leave a buildable dependency and several
active consumers. The final repository must have neither dependency path.

### D00 — inventory the consumers and replacement contracts

Start after P00 and keep the inventory current while the branch integrates
main. Put a tracked removal/contract ledger in `docs/kernel.md`; each row
names the replacement, its proof/test gate, and when the old consumer leaves.

| Existing surface | Action and replacement |
| --- | --- |
| `Ix/Tc/Verify/**`, its statement/conditional/sorry-frontier audits | Replace checker acceptance claims with the executed `Ix.Kernel` claims and frozen roots; port useful adversarial inputs, then delete the tree |
| `Ix/Compile/Verify/**` and `Ix.Tc.Verify.Audit.Basic` | Salvage needed pure codec/reading lemmas into K3/K4 and reusable audit behavior into `Ix.Kernel.Audit`; delete the Lean4Lean-based translation/specification machinery and unused helpers |
| `lakefile.lean`, root `lake-manifest.json` | Remove `require lean4lean`, `IxTcVerify`, `IxCompileVerify`, `Lean4LeanBench`, `bench-lean4lean`, `ix_native_decide_dynlib`, and the obsolete `build-all` exception; regenerate the manifest |
| `ix_ffi_dyn`, `crates/ffi-dyn`, `Cargo.toml`, `Cargo.lock` | At baseline this crate's only Lake consumer is the old proof loader; remove it and its workspace/lock entries once the final consumer check confirms that, retaining the ordinary runtime FFI |
| `Benchmarks/Lean4Lean.lean`, `Lean4LeanMain.lean`, `Tests/Ix/Lean4Lean.lean`, `Tests/Main.lean` | Remove replay/smoke machinery and runner registration; preserve useful inputs in certified kernel fixtures |
| `Ix/Cli/BenchCmd.lean`, `Ix/BenchConstants.lean`, `docs/benchmarking.md` | Remove the backend dispatch, registry, help, and active instructions; measure `Ix.Kernel` and Rust through the replacement harness |
| `Benchmarks/TruthMinesSpec/{Catalog,Spec}.lean` | Remove the Lean4Lean package/member at its generator source so regeneration cannot restore it |
| `Benchmarks/TruthMines/{lakefile.lean,lake-manifest.json,Drivers/Lean4Lean.lean}`; `Benchmarks/Compile/TruthMines/Members/Lean4Lean.lean`; nested Compile manifests | Regenerate the corpus configuration and lockfiles without the package, driver, and member; retain unrelated benchmark packages |
| `.github/workflows/merge-tests.yml`, `.github/workflows/ci.yml`, other workflow callers | Replace old proof-library and sorry-frontier jobs with strict kernel/model/provenance/differential gates; remove the Lean4Lean runner entry |
| `flake.nix` and generated dependency closure | Remove the `lean4lean` target-name override and dependency build; validate the Nix build without a cached package masking its removal |
| `docs/ffi.md`, old Tc audit documentation, certification ledger | Retire obsolete commands/claims and explain which new theorem covers each retained guarantee |

Reusing a test case is not porting its proof. Kernel model existence does
not establish end-to-end correctness of the Lean-to-Ixon compiler. State
K3's reading and K4's codec guarantees exactly, and mark any stronger old
compiler claim as retired/unproved until a separate proof exists. This
prevents dependency removal from silently overstating certification.

Exit: every active import, target, package entry, runner, and generated
reference has a disposition. Inspect common audit helpers before moving
them; `Ix.Kernel.Audit` already provides axiom/import/runtime checks, so
obsolete allowances and sorry-frontier infrastructure need not survive.

### D01 — remove the dependency and proof system in one coherent change

Implemented and validated on 2026-09-29; see the D01 evidence and removal
ledger in `docs/kernel.md`. The following requirements remain the
recurrence checks for this completed milestone.

Prerequisites: K2's replacement proof/CI gates pass, and the useful
reading/codec contracts selected in D00 have their K3/K4 replacements.
This checkpoint can land before the final executable `Ix.Tc` migration:
the old runtime checker may remain temporarily as a differential oracle,
without `Ix.Tc.Verify`, `Ix.Compile.Verify`, or Lean4Lean dependencies.

Perform the deletions, import/runner updates, target/CI/Nix changes, and
manifest regeneration from the ledger together. Do not retain optional
Lean4Lean benchmark dependencies or make the ordinary build depend on the
untracked con-leche reference. Preserve required copyright/NOTICE material
and historical attribution; mentioning Lean4Lean in provenance is not a
runtime dependency. Port fixtures before deleting their only source.

Exit checks:

1. Scan tracked imports, including `public import` and `import all`, for
   `Lean4Lean`, `Ix.Tc.Verify`, and the removed `Ix.Compile.Verify` tree.
   There must be no active imports. Parse every tracked Lake manifest and
   generator catalog for the package name and both repository URLs;
   remove all dependency entries, not just the root lock entry.
2. Check active build/test/CI/Nix configuration for removed target names
   and backend dispatch. A repository check prevents their reintroduction;
   its scope excludes historical documentation and legal provenance.
3. Regenerate the benchmark configuration and verify it produces no
   removed package/member. Build/test from a fresh jj workspace or clean
   package directories, without stale `.olean` files or a local Lean4Lean
   checkout supplying missing imports.
4. Run the normal host build/tests, `lake run check-kernel --with-model`,
   affected benchmark/CLI tests, and the Nix gate. If `ffi-dyn` is removed,
   also validate the remaining Rust workspace build/tests and lockfile.
   Preserve existing audit negative controls and supported-profile parity.

### D02 — finish the Ix.Tc runtime cutover

After K3/K4 and the section 6 consumer migration/parity gates, port the
remaining `Tests/Ix/Tc` behavior tests, switch differential testing to Rust,
remove `Ix/Tc.lean` and `Ix/Tc/**`, and remove their Lake roots, runners,
imports, CLI adapters, and obsolete CI commands. Re-home primitive tables
and any still-needed audit helpers before deletion. The main umbrella,
AuxGen, IxVM claim harness, and validate/check commands must use their new
owners. Keep metadata/name bridges in host code.

Exit: no active source or build/test configuration depends on `Ix.Tc`,
`Ix.Tc.Verify`, `Ix.Compile.Verify`, `Lean4Lean.*`, or the `lean4ix` package;
the fresh host/kernel/model builds and consumer tests pass, the documented
parity corpus agrees subject to the explicit ordered-reference policy,
and the removal ledger is complete. This is required for K6 completion,
even if optional performance work is deferred.

## 12. Ixon v3 and Lean 4.34

Ix `main` has emitted only Ixon v3 since #636 (2026-09-16), one commit after
this branch's original base `cf77c957`. Until V1 below, K3 and K4 certified the
v2 grammar. The migration keeps the kernel, its public theorems, and the
supported profile unchanged. Contracts are layout data (section 3.1). Each step
below closes with the full `check-kernel --with-model` gate and evidence under
`plans/review/<step>/`.

### T0 — takeover baseline (complete, 2026-09-29)

The gate was re-run at `f499ccf2`, the last v2 state, bookmarked as
`jcb/ix-certified-v2`. Results: 188/211/621/975 jobs, 38 differential cases,
26 compiler cases, and 1,117 Rust order comparisons passed. Stale gate
workspaces were forgotten.

### V1 — merge ix `main` (`b413cd93`, Ixon v3) (complete, 2026-09-29)

Merge `main` into the branch. Resolve the conflicts as follows:
- The 17 D01 deletions that upstream edited stay deleted.
- Upstream's v3 hunks for the retained codec proofs go into the extracted
  `Ix/Ixon/Verify/*` modules. Each module's provenance header moves to the
  new revision.
- The v3 contract types go into the pure `Ix.Ixon.Types` closure. The host
  modules `Ix/IxonContract.lean` and `Ix/IxonMode.lean` become re-export
  shims.
- v3 reader/writer changes go into `Ix.Ixon.Codec`: contract bytes, the let
  flags plus binder byte, `checkCount`, canonical integer tags, and flag
  validation.
- The upstream `Ix/Resource/Audit` moves off the deleted `Ix.Tc.Verify` audit
  helper.

The K4-authored modules (`Bounded`, `WireCheck`, `Canonical`, `ReaderBounds`,
`ConstantBounds`, `Work*`) and the certified ingress/egress are ported by
hand. The supported profile is unchanged: default contracts are accepted, and
all others decline.

Exit: the gate passes on v3 with regenerated compiler fixtures, with verdicts
and reasons unchanged. Any statement the new `Ixon.Expr` forces to change is
re-frozen, with its reason recorded.

Result (`plans/review/v1-merge`):
- **Gate.** The full gate passed: 189/212/645/975 jobs, 38 differential cases,
  26 compiler cases (20 accept, 5 decline, 1 reject), and 1,117 Rust order
  comparisons.
- **Compiler cases.** 24 of the 26 inputs are re-encoded as v3, and no
  verdict or reason changed.
- **Ported code.**
  - All 26 upstream `Ix/Ixon.lean` hunks were routed into `Types`, `Codec`,
    and the host module.
  - Six extracted codec proof modules took upstream's v3 revisions.
  - The contract types moved to the pure `Ix.Ixon.Types.Contract`.
  - The K4 parser-work and reader-bound proofs were ported by hand for
    `checkCount`, canonical integer widths, strict Booleans, flag validation,
    and contract bytes.
- **Semantics.** Let contracts are erased by the reading, as at upstream
  `Ix.Tc`'s erased typing boundary, and retained by egress.
- **Frozen statements.** Frozen public statements are unchanged.
- **Runtime audits.** Five runtime-closure counts were re-recorded. The only
  new externs are `Nat.mul`, `UInt64.land`, and `UInt8.add`, all Lean core.
  Byte admission's extern subset claim is now enforced by a check.
- **Decoder behavior.** The v3 production decoder itself rejects nonminimal
  integers and non-Boolean flags. Canonical decoding still rejects
  noncanonical universe spellings.

### V2 — carry every v3 contract (complete, 2026-09-29)

Changes:
- `ExprLayout` retains binder, forall-result, and let contracts.
- Ingress accepts every contract value, and the reading relation ignores
  contracts.
- The record round-trip theorems cover exact contract recovery.
- `let borrow` has the ordinary let typing rule, confirmed against upstream
  `Ix.Tc` before it is accepted.

Tests:
- every binder, forall, and let contract spelling;
- upstream `Tests/Fixtures/ixon-v3`;
- the Compilatr.ix v3 fixtures.

Exit: every contract spelling is accepted and round-trips byte-exactly.

Result (`plans/review/v2-contracts`):
- **Semantics.** `ExprReads` erases every contract, and `ExprLayout` retains
  them. Upstream `Ix.Tc` confirms the erased-typing semantics, including that
  a `let borrow` types as an ordinary let.
- **Contract spellings.** Every binder, result, and let spelling reads as the
  default-contract term and round-trips.
- **Upstream fixtures.**
  - Upstream's `expressions.txt` bytes decode and re-encode exactly.
  - Both frozen handoff environments pass every route, including the one that
    native resource admission rejects. Kernel acceptance is erased typing,
    not resource validity.
- **Host cases.** 28 host cases passed.
- **Runtime closures.** They shrank, and externs are unchanged.
- **Deferred.** The Compilatr.ix `k1` closures come from the Lean 4.34
  producer and follow L1.

### V3 — the byte ladder against the v3 decoder

The v3 production decoder rejects several inputs itself: noncanonical integer
tags, counts larger than the remaining bytes, invalid kind/safety/recursor
flags, and non-Boolean flags. Restate the K4 ladder against this decoder:
- Prove or drop the runtime canonical re-encode check.
- Simplify the counted-array bounds.
- Settle the treatment of single-use sharing entries.
- Name the per-record canonical contract.
- Keep one wire-well-formedness predicate per sort, and delete the superseded
  milestone domains.

Exit: the ladder theorems and adversarial controls are restated for v3. Every
freeze or audit change is recorded with its reason.

### L1 — Lean 4.34.0

Merge `jcb/ix-compilatrix` at `0a31c8db`. That brings:
- the Lean 4.34.0 toolchain and Blake3 `c32002ee`;
- updated primitive addresses.

Also:
- Bump every `lean-toolchain`, and Mathlib to `v4.34.0`.
- Fix the 4.34 deprecations, so strict builds stay free of warnings.
- Re-run every exact axiom audit. `Std.HashMap` now reaches
  `Classical.choice`. A changed axiom set for a kernel public root is a
  finding, not a re-record.
- Regenerate the address-dependent fixtures.

Benchmark packages whose third-party dependencies lag Lean 4.34 are recorded
as such.

Exit: 4.34.0 throughout, and `IxKernel/` consumable at a pinned revision.

### R1–R4 — contract fixes from the second ontology review

**R1.** `EqInterface`, `propextSpec`, and `choiceSpec` take the Eq/Iff/Nonempty
recursor reference explicitly, instead of assuming `.member b 1`. Production
input stores recursors as separate records, which the positional form rejects.
Failed prerequisites decline. Add production-layout `Quot`, `propext`, and
`Classical.choice` host cases. R1 lands right after V1.

**R2.** The structure and Nat fallbacks propagate exhaustion instead of
installing a weaker entry.

**R3.** One admission fold over physical records:
- Freeze the `checkEnv` statements.
- Add a no-False theorem for `checkEnv`.
- Add the syntactic `EmptyType` corollary promised in section 2.

**R4.** Installed fidelity covers every supplied field: kinds, safety, arities,
rules, and the K flag. Also prove reading determinism and a
`checkEnv_ok_iff`.

### C — contract semantics and a certified contract checker (later)

The kernel defines what Ixon v3 contracts mean, and a checker is certified
against that definition. Upstream `Ix/Resource` is a deterministic checker
whose local invariants are proved: scope tree, outlives, and loans. It has no
semantic model; its own statement is that "kernel typechecking alone has no
resource meaning".

Phase C has four parts:
1. **Semantics.** Define in `Ix.Kernel.Model` a contract-aware judgment over
   kernel terms and their retained contracts, using the `Uses` semiring. It
   covers:
   - usage in runtime-relevant positions;
   - uniqueness of `unique` values;
   - non-escape of `local` values through results, captures, stores, and
     loans;
   - borrow scopes.
2. **Adequacy.** State the judgment's guarantee against an instrumented
   evaluation, compatible with the set model; erasing contracts already
   preserves meaning.
3. **Certified checker.** Port the `Ix/Resource` algorithm in the kernel's
   proof-carrying style, keeping accept/reject/decline.
4. **Relevance.** Combine erased usage with `PropWhen` Prop regimes into a
   certified relevance/erasure judgment. This is the annotation that
   compilers such as Compilatr.ix currently check untrusted.

K7's optimizations become promotions justified by this semantics. Phase C
depends on V2 and follows L1 and R1–R4.

The review's outcome vocabulary, byte pipeline composition, and glossary
renames go with P11, before the D02 consumers. K5 is then designed against
v3's format-3 environment header and constant-set Merkle root.
