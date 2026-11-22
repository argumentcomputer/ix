# Resource modes: the model, surface syntax, and the mode checker

Ixon v5 records carry **modes**: every `lam` and `all` binder an `AllMode` (the
bound variable's `BinderMode`: `many`, `borrowed`, `unique`, `uniqueBorrowed`,
`once`, `onceBorrowed`, or `erased`, and the result's `ResultMode`: `shared`,
`borrowed`, `unique`, or `uniqueBorrowed`), every `let` a `LetMode` (a value
`let` at any `BinderMode` or `.borrow`), every constructor field a `FieldMode`
(`inherited` or `shared`), and every non-theorem definition a `DefAsserts`
(`unrestricted`/`noRc`/`noAlloc` × `boundedStack`). They are data of the record,
hashed into its address. Kernel terms carry none: typing never sees modes, and
typing claims cover annotated constants without saying anything about their
modes.

## Surface syntax (`open scoped Ix.Modes`)

Import `Ix.Compile.SourceContract.Elab` and opt in locally with
`open scoped Ix.Modes`. All mode keywords are parsed with
`atomic ("@" >> checkNoWsBefore ... >> nonReservedSymbol w)`, adding **zero**
entries to Lean's `TokenTable` so `@unique_fn`, `@uniqueId`, `@id`, `@&`,
`(unique x : Nat)`, `let @Prod.mk _ _ a b := p`, and `let borrow v := owner + v`
remain unaffected.

* **Binder modes (7, composable, order-insensitive)** in `(...)`, `{...}`,
  `⦃...⦄`, `[...]` (multi-name groups `(@unique x y : T)` and optional `: T` in
  `fun` supported): unmarked (`many`), `@borrowed`, `@unique`,
  `@unique @borrowed` / `@borrowed @unique`, `@once`,
  `@once @borrowed` / `@borrowed @once`, `@erased`. Illegal pairs (`@erased`
  with anything, `@once @unique`, duplicates) are rejected at elaboration.
* **Result modes (4)** after `:` in `def`/`abbrev`/`opaque`/`axiom`, after
  `→`/`->`, or after `∀ ...,`: unmarked (`shared`), `@borrowed`, `@unique`,
  `@unique @borrowed` / `@borrowed @unique`. Input modes stay bracketed
  (`(@borrowed x : α) → @unique β`) so `A → @unique B → C` has no precedence
  ambiguity.
* **`let` & `do`-block `let` (8, unparenthesized, optional `: T`)**:
  `let @borrowed x := e`, `let @unique x := e`, `let @unique @borrowed x := e`,
  `let @once f := e`, `let @once @borrowed f := e`, `let @erased h := p`, and
  `let @borrow v := owner` (`LetMode.borrow`).
* **Structure & inductive fields**: `@shared field : T` (`FieldMode.shared` in
  `Ixon.Constructor.fieldModes`), `@erased field : T` (constructor binder
  `.erased`), unmarked (`FieldMode.inherited`). Note: when an inductive declares
  an `@erased` field, pattern matching through `casesOn` (a case shape) is
  accepted, while Lean's unannotated auto-generated auxiliaries (`*.rec`,
  `recOn`, `_sizeOf_1`, `brecOn`, `noConfusion*`) call the raw recursor without
  marking the corresponding minor-premise binder `@erased` (and `_sizeOf_1`
  genuinely reads non-`Prop` fields), so `Reading.recRules` strictly refuses
  closures that include them.
* **Definition assertions (6)**: scoped Lean 4 attributes `@[no_rc]`,
  `@[no_alloc]`, `@[bounded_stack]` (combinable, e.g.
  `@[no_alloc, bounded_stack]`; rejected on `theorem`/`partial`/`unsafe`),
  lowered to `Ixon.Definition.asserts`.

```lean
import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

structure Packet (α : Type) where
  @shared label : α
  @erased valid : True
  payload : Nat

@[no_alloc, bounded_stack]
def forward (@unique @borrowed x : Nat) : @unique @borrowed Nat := x

def borrowInDo (@unique owner : Nat) : Id Nat := do
  let @borrow v := owner
  return v + 1
```

Two things are in this repository:

* **The model and its statement** (`IxC/Resource/`, a library of the `IxC`
  package that no kernel module imports): run programs read from records
  (`Read.lean`), the reference evaluator `runR` with its four monitors
  (`Eval.lean`), and `ModeSafe` (`Statement.lean`), the statement a modes claim
  carries.
* **The certified mode checker**, `IxC.Resource.check` (`Check.lean`): an
  abstract run of `runR`, certified by `IxC/Resource/Proof/` (`DefaultOk`,
  `ReadsRespectErasure`, and `CheckSound`, audited in `IxC/Resource/Audit.lean`
  under strictly `[propext, Classical.choice, Quot.sound]`, zero sorries).
  `ix compile` runs it on every artifact compiled from annotated source
  (`Ix.ModeCheck.checkArtifact`, which the compile commands pass to
  `Ix.CompileM.compileAndFinalize`) and says so; a compile with no checker
  passed refuses annotated source. `IxCC`'s N5 ingress gate
  (`IxCC.Src.KernelFront.defaultModeCheck`) also invokes `IxC.Resource.check`
  (with `recordWellFormed` and the `allDefault` fast path over logical seeds)
  right after certified kernel acceptance. `ix verify` does not run it, its
  import closure does not contain it (`kernel-layering`'s mode fence), and no
  claim carries its verdict.

## The model

A **run program** (`IxC.Resource.Prog`) has one definition per constant of a
closure: a run body (a definition's value under its leading λs, or the right
side of an equation of the widened `Subject.runTable : List Address`, which
accepts per-definition `f.eq_def` theorems and/or `And` conjunctions), a
constructor, an inductive type, a case shape (recognised transparently through
sharing references for recursive, mutual, nested, and indexed inductives), a
`Nat` primitive, an extern, or a stuck constant (an axiom or opaque outside the
extern set, an unsafe or `partial` constant, a recursor outside a case shape).
Modes are read from the records by position; types and proofs are erased; every
relevant node carries its **class**, from the kernel's typing: `irr` (a type, a
type former, a proof), `imm` (an immediate: enumerations, `BitVec w` at a
literal width of at most 64, trivial wrappers of these such as `UInt8`…`UInt64`
and `Char`), `leaf` (a counted, immutable heap value: `Nat`, and trivial
wrappers of it such as `Fin n`; under finalized L1, a `leaf` is never confined
to a borrow region, whereas `.val` heap cells are), or `val`.

**`runR`** is call by value with fuel. A unique transfer gives every cell of a
value's ownership closure (`inherited` fields, captures; not `@shared` fields,
leaves or immediates) a fresh capability, so every other reference dies. A
borrowed binder confines its value to the binder's region. A once binder wraps
its value in a once view. Its four violations:

| Violation | When |
|---|---|
| `erasedRead` | an erased binding is read, or an erased field projected |
| `revokedUse` | a reference revoked by a unique transfer is used |
| `borrowEscape` | a value confined to a closing region is returned or let-bound past it; a confined value is given away |
| `onceReentry` | a once view is called a second time |

Runs that end `stuck` (a shape failure, a stuck constant) or out of fuel are not
violations, and nothing is claimed about them.

**`ModeSafe env s`**: the subject's records read as a run program, and for every
seed with a run body, every input meeting its declared modes (`InputsOk`) and
every extern behaving as declared (`ExternOk`), no run ends in a violation.
`env` is the environment the consistency statement's reading installs, so a
claim can carry both conclusions from one reading.

## The checker

`check` takes a fast path when every record of the closure has only default
modes (`IxC.Resource.Proof.defaultOk : DefaultOk` justifies it). Otherwise it
reads the constants that have or call non-default modes, with the kernel as
class oracle (positive answers only; a lack of fuel declines), and checks each
run body: binding states (live and unique, shared, consumed), regions, aliases,
once bindings, mode skeletons at every flow. Its verdict is accept, refuse with
a witness, or decline at a limit. `IxC/Resource/Proof/` certifies all three
soundness deliverables:

* `IxC.Resource.Proof.defaultOk : DefaultOk` (the all-default fast path is
  mode-safe);
* `IxC.Resource.Proof.readsRespectErasure : ReadsRespectErasure` (accepted
  erased bindings and fields are never read);
* `IxC.Resource.Proof.checkSound : ∀ KernelRead, (∀ env s, KernelRead env s → RolesDisjointFromInductives s) → CheckSound KernelRead`
  (checker acceptance implies `ModeSafe`).

`IxC/Resource/Audit.lean` fences the entire `IxC.Resource.Proof` subtree and
the five exported soundness theorems (`defaultOk`, `readsRespectErasure`,
`check_sound_modeOk`, `f4`, `checkSound`) strictly to
`[propext, Classical.choice, Quot.sound]`.

Tests: `lake -d IxC build IxC.Resource.Audit`, `lake exe IxTests resource-modes`,
`lake exe source-contract-tests`, and `ModeRepairTests/Main.lean` (348-case
differential harness).
