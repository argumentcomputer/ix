# Resource modes: the model and the mode checker

Ixon records carry **modes**: every `lam` and `all` binder an `AllMode` (the
bound variable's mode, `many`, `borrowed`, `unique`, `uniqueBorrowed`, `once`,
`onceBorrowed` or `erased`, and the result mode of the binder's own arrow,
`shared`, `borrowed`, `unique` or `uniqueBorrowed`), every `let` a `LetMode`,
every constructor field a `FieldMode` (`inherited` or `shared`). They are data of
the record, hashed into its address. Kernel terms carry none: typing never sees
modes, and typing claims cover annotated constants without saying anything
about their modes.

Two things are in this repository:

* **The model and its statement** (`IxC/Resource/`, a library of the `IxC`
  package that no kernel module imports): run programs read from records
  (`Read.lean`), the reference evaluator `runR` with its four monitors
  (`Eval.lean`), and `ModeSafe` (`Statement.lean`), the statement a modes claim
  would carry. It is a definition: nothing in this repository proves it of any
  checker.
* **The mode checker**, `IxC.Resource.check` (`Check.lean`): an abstract run of
  `runR`, **uncertified**. `ix compile` runs it on every artifact compiled from
  annotated source (`Ix.ModeCheck.checkArtifact`, which the compile commands
  pass to `Ix.CompileM.compileAndFinalize`) and says so; a compile with no
  checker passed refuses annotated source. `ix verify` does not run it, its
  import closure does not contain it (`kernel-layering`'s mode fence), and no
  claim carries its verdict.

## The model

A **run program** (`IxC.Resource.Prog`) has one definition per constant of a
closure: a run body (a definition's value under its leading λs, or the right
side of an equation of the run table), a constructor, an inductive type, a case
shape, a `Nat` primitive, an extern, or a stuck constant (an axiom or opaque
outside the extern set, an unsafe or `partial` constant, a recursor outside a
case shape). Modes are read from the records by position; types and proofs are
erased; every relevant node carries its **class**, from the kernel's typing:
`irr` (a type, a type former, a proof), `imm` (an immediate: enumerations,
`BitVec w` at a literal width of at most 64, trivial wrappers of these such as
`UInt8`…`UInt64` and `Char`), `leaf` (a counted, immutable heap value: `Nat`, and
trivial wrappers of it such as `Fin n`), or `val`.

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
modes (`DefaultOk`, to prove, justifies it). Otherwise it reads the constants
that have or call non-default modes, with the kernel as class oracle (positive
answers only; a lack of fuel declines), and checks each run body: binding
states (live and unique, shared, consumed), regions, aliases, once bindings,
mode skeletons at every flow. Its verdict is accept, refuse with a witness, or
decline at a limit. `CheckSound` (accept implies `ModeSafe`) is the theorem
left to prove.

Tests: `lake exe IxTests resource-modes` (small run programs, each run under
`runR` and checked).
