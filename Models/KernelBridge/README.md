# Kernel bridge: a conditional simulation lemma (`Models/KernelBridge`)

This standalone Lake package proves a **conditional simulation lemma** between IxCC's
source evaluator (`IxCC.Src.run`) and IxCK's kernel reduction (`Ix.Kernel.Rules.Red`),
relative to a relation that the user supplies, and composes it with set-theoretic
denotation (`Ix.Kernel.Denotes` in `Model.ofEnvModelM mp`) and with IxCC's own soundness
theorems (`IxCC.Recheck.sound_nat`, `IxCC.CompileClaim.verifyBytes_immortal_sound`).

It is **not** a source-adequacy theorem for compiled claims. The kernel environment and the
kernel term it speaks about are not derived from a claim's environment or target, and the
relation it needs can be built only for a very small fragment. Source adequacy against the
kernel model, the target theorem of [IxCC's roadmap](../../IxCC/docs/roadmap.md) and open
item S8 of IxCC's [certification design](../../IxCC/docs/certification-design.md), remains open.

**Not the route.** Its approach, a simulation of the source evaluator by kernel reduction,
cannot reach recursion and cannot pass type arguments, numerals, instance methods or `match`
as Lean elaborates them (below). IxCC's plan replaces it by a denotational relation over
IxCK's strong models
([certification design](../../IxCC/docs/certification-design.md#modelskernelbridge-not-the-route)).
The package stays, with its gate, as a record of the approach until that relation covers the
first grounded fragment; its layer that reads a literal's denotation off a reduction may be
reused; then the package and its gate are removed (a default, open decision DO-12 in the
[roadmap](../../IxCC/docs/roadmap.md#open-decisions)).

The package lives outside IxCC's production import root, so `IxCC` never imports IxCK's
model tier.

## What is proved

**Layer 1, `srcRun_to_red`.** Suppose the user supplies:

1. a kernel environment `env` with `natBasisStored env = true` (a decidable check that
   `Nat`, `Nat.zero`, `Nat.succ` and `Nat.rec` are stored exactly as IxCK's basis
   declarations; no lemma here derives it from `checkDecls`);
2. a relation `constSpec : Levels → CId → Expr → Prop` from Src constants to closed kernel
   terms, with `hconst : ∀ ls c e, constSpec ls c e → RelConstStep p env constSpec ls c e`.
   For every related constant this asks for the `RelConstStep` case of its resolution:
   - a definition, equation, csimp or allowlisted opaque: a proof of `Red env 0 e kbody`
     and a `RelTerm` image `kbody` of its Src body that mirrors it node for node, type
     arguments and motives included (only `sort` and `pi` positions are unconstrained);
   - a binary primitive: the per-operation agreement premise (below);
   - a constructor, recursor or `casesOn`: only `Nat.zero`, `Nat.succ`, `Nat.rec` and
     `Nat.casesOn` have cases;
3. a related root: `constSpec [] root eRoot`.

Then if `Src.run p k root (xs.map .lit) = .ok (.lit out)`, the term `eRoot` applied to the
literals `xs` reduces under `Red env 0` to a term whose raw `Nat` literal is `out`.

**Layer 2, `red_to_denotes_nat` and `infer_red_to_denotes_nat`.** If a closed term reduces
to a literal `out` and is readable in a model (`denoteMeta … = some ea`) and graded
(`Graded V [] ea`, or an `Infer env .full 0` derivation), it denotes the same value as
`.lit (.natVal out)` in `Model.ofEnvModelM mp`.

**Layer 3.** `srcRun_to_denotes_nat` and `srcRun_infer_to_denotes_nat` chain Layers 1 and 2.
`checkDecls_srcRun_denotes_nat` adds `Ix.Kernel.Cached.checkDecls_sound`: a
`checkDecls`-accepted `env` has a model, so the denotation clause applies in every model of
`env` in which the applied root is readable and graded.
`checkDecls_recheck_x86_denotes_nat` also conjoins `IxCC.Recheck.sound_nat`, and
`checkDecls_verifyBytes_immortal_denotes_nat` conjoins
`IxCC.CompileClaim.verifyBytes_immortal_sound`. Every Layer 3 theorem keeps the premises of
Layers 1 and 2.

**The kernel front end's classes** (`IxKernelBridge.KernelFront`, apart from the simulation
lemma). IxCC's front end over the certified kernel (`IxCC.Src.KernelFront`,
[design](../../IxCC/docs/kernel-front-end-design.md)) classifies a position as a proof from
the executed kernel core's runs. `infer_derives`, `whnf_derives` and `annotate_runs` package
the kernel's simulation of its specification by the cached core (`Ix.Kernel.Cached.ssimC`) and
its bridge to the relational judgements, for open, well-scoped terms from any invariant memo
state; `classifyTerm_derivations` turns a `proof` class into `Infer` and `Red` derivations of
the position's type and its sort, and `classifyTerm_sound` into their readings in every model
meeting `RulesInputs` (`infer_sound`, `red_sound`). They live here because this package is the
one that builds both IxCC and the kernel's proof tree.

## What is not proved

**The kernel side is not tied to the compiled claim.** In the Layer 3 theorems:

- `env` is any environment accepted by `checkDecls μ ev ds = .ok env` for any declaration
  stream `ds`. Nothing requires `ds` to be IxCK's Ixon reader output for the claim's
  environment bytes or `claim.env`; in `checkDecls_verifyBytes_immortal_denotes_nat`, `ds`
  and `env` occur only in `hchk` and `hbasis`, and `envBytes` only in `hver`.
- `eRoot` is any closed term that the user's `constSpec` relates to the Src root. It is not
  required to be the kernel constant of `claim.target`.
- The root index `i` is not tied to `claim.target`.

The theorems are conjunctions that share only the checked Src program `a.src` and the run
`hrun`. So nothing here says that `claim.target`, in the environment `claim.env`, denotes
`out`. Closing that gap would need at least: `ds` the reader's output on the claim's bytes,
`eRoot = .const (key of claim.target) []`, a `constSpec` derived from the two ingress
functions, and the fragment work below.

**The relation can be built only for a small fragment.** `RelTerm.app` relates an
application only if its argument is related, whatever its relevance; a constant is related
only through `constSpec`, and `RelConstStep` has no case for an inductive type (such as `Nat`
itself), an axiom or a theorem; there is no `RelTerm` rule for `.proj` or string literals;
and `RelHead` and `RelVal` know only the `Nat` constructors, `Nat.rec`, `Nat.casesOn`,
literals, closures and partial applications. So type arguments, numerals
(`@OfNat.ofNat Nat n _`), typeclass operations (`@HAdd.hAdd Nat Nat Nat …`), `match` (with
motive `fun _ => Nat`) and recursion, as Lean elaborates them, are all outside the fragment.
What fits is closed first-order `Nat` definitions with no type arguments: λ, variables,
explicit `Nat.succ`/`Nat.zero`, explicit binary `Nat.*` calls on relevant arguments for the
operations whose premise holds, raw `nat_lit` literals, and calls to other non-recursive
definitions of the same kind.

A survey of 17 of the repository's fixture packs (from the bench-k1, `k1`,
phase1-scalar, phase1-decline and phase1-abi families), as the loader builds them, found that of
their 69 roots after the front end, 65 are provably unrelatable, and only
`Abi.nat1 (a : Nat) : Nat := a` qualifies. Of the other three, two return `Bool` or `Tri`
constructors (no `RelHead` case, and the theorems need a `Nat` result) and one,
`Decline.applyArg`, is higher-order.

**Recursion is blocked independently of the fragment.** `RelConstStep.eqn`, `.csimp` and
`.defn` relate a constant through a `Red env 0 e kbody` step. Kernel `Red` is weak-head
(congruence only in function position and under projections), so from an honest root
`.const fKey []` the only reducts are the constant itself and its stored value. For a
recursive function the stored value is its compiled recursor form (`fib`:
`λ n. Nat.brecOn motive n fib.F`; well-founded recursion: `WellFounded.fix …`), while
IxCC's Src program evaluates the equation body (`λ n. fib.match_1 motive n …`), which `Red`
cannot reach. Only a non-normalising mirror term could be related, and it would not meet
Layer 2's typing premises. csimp pairs are linked by a theorem, not by reduction. Covering
them needs a denotational step: relate `eqn` and `csimp` resolutions through the checked
equation theorem's validity in every model of `env` (`Denotes`), not through `Red`.

**Primitive operations.** `RelHead.primBinNat` takes as a premise that Src's result agrees
with the kernel's `natOpResult` on every pair of literals. `IxCC.Src.PrimOp` has 14 binary
operations (`add sub mul div mod pow gcd beq ble land lor xor shiftLeft shiftRight`) and one
unary one (`pred`); the kernel accelerates 14 binary keys (`natBinOpNames`).
`IxKernelBridge.Examples` proves the premise for the 11 operations `add sub mul div mod gcd
land lor xor shiftLeft shiftRight` and proves it false for the other three: `pow` (the
kernel refuses exponents above 2^24) and `beq`/`ble` (their Src results are `Bool`, and
`RelVal` has no Boolean case). `pred` has no `RelHead` case.

## Instances (`IxKernelBridge.Examples`)

So that the lemma is not vacuous, `IxKernelBridge/Examples.lean` instantiates Layer 1 with
an honest root, `eRoot = .const k []` for a level-free definition `k` of `env` whose stored
value is the kernel image of the Src definition, for programs of the shape ingress gives:

| Theorem | Lean definition |
| --- | --- |
| `id_bridge` | `def f (a : Nat) : Nat := a` (the shape of `Abi.nat1`) |
| `succ_bridge` | `def f (a : Nat) : Nat := Nat.succ a` |
| `add_bridge` | `def f (a b : Nat) : Nat := Nat.add a b` |
| `addLit_bridge` | `def f (a : Nat) : Nat := Nat.add a (nat_lit 1)` (a raw literal, not a numeral) |
| `addLit_concrete` | the line above with every hypothesis closed: a two-constant Src program, a concrete `Env`, `natBasisStored`, and `Src.run … = .ok (.lit 42)` |

Their kernel-side values are hand transcriptions, not the output of IxCK's reader, and the
concrete `Env` is not a `checkDecls`-accepted environment (its `Nat.add` is a stand-in). That
the ingested `Abi.nat1` has exactly the shape `id_bridge` needs, before and after the front
end, and runs, was established in the review by evaluating the loader on its fixture, not
by a proof here.

## Axioms

`IxKernelBridge/Audit.lean` fences every theorem named above with an exact
`#guard_msgs in #print axioms` (27 fences) and checks, by walking the constant closure, that
`srcRun_to_red`, `red_to_denotes_nat`, `infer_red_to_denotes_nat`, `srcRun_to_denotes_nat`,
`srcRun_infer_to_denotes_nat`, `checkDecls_srcRun_denotes_nat`,
`checkDecls_recheck_x86_denotes_nat`, `checkDecls_verifyBytes_immortal_denotes_nat` (every
address IxCC computes is pure BLAKE3, so `IxCC.CompileClaim.verifyBytes_immortal_sound` rests on
the standard three as well) and the examples that use all three depend on exactly
`[propext, Classical.choice, Quot.sound]`. One exception, fenced: `ble_premise_false` and
`pow_premise_false` use only `propext` and `Quot.sound`.

The package has no `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or
`opaque`; the one `partial` is the elaboration-time closure walk in `Audit.lean`.

## Structure

- [`IxKernelBridge/NatBridge.lean`](IxKernelBridge/NatBridge.lean):
  - **Layer 1 (`srcRun_to_red`)**: simultaneous de Bruijn substitution (`subst`) commuting
    with `Expr.instantiate1`, the basis predicate `natBasisStored`, multi-step `Red` lemmas
    for δ-unfolding (`red_delta_const`), `Nat.rec` ι-reduction (`red_natRec_zero`,
    `red_natRec_succ`) and `Nat.casesOn` (`red_natCasesOn_zero`, `red_natCasesOn_succ`), the
    relations (`RelTerm`, `RelHead`, `RelConstStep`, `RelVal`, `RelSlot`, `RelSlots`), and
    fuel-strong simulation (`sim_all`: `eval_sim`, `apply_sim`, `force_sim`, `fire_sim`,
    `headValue_sim`, `evalConst_sim`).
  - **Layer 2 (`red_to_denotes_nat`, `infer_red_to_denotes_nat`)**: `RulesInputs.ofSem`,
    `red_sound`, `infer_sound`, `Denotes_of_denoteMeta` and `Denotes.natLit`.
  - **Layer 3** (`srcRun_to_denotes_nat`, `srcRun_infer_to_denotes_nat`,
    `checkDecls_srcRun_denotes_nat`, `checkDecls_recheck_x86_denotes_nat`,
    `checkDecls_verifyBytes_immortal_denotes_nat`): the conjunctions above.
- [`IxKernelBridge/Examples.lean`](IxKernelBridge/Examples.lean): the instances and the
  per-operation facts.
- [`IxKernelBridge/Audit.lean`](IxKernelBridge/Audit.lean): the axiom audit and fences.

## Build and gate

From the repository root, in ix's development shell (`nix develop`):

```sh
lake run check-kernel-bridge
```

This builds the package (`lake -d Models/KernelBridge build`) and checks that the theorems
fenced in `Audit.lean` are exactly the inventory recorded in the root `lakefile.lean`
(`kernelBridgeFences`). Merge tests run it in the certified-kernel partition on every merge
group, beside `lake run check-kernel --with-model`; CI Jobs runs it on pull requests whose
changes reach the package (the `kernel-bridge` path filter of `ci.yml`: IxCC's Lean
sources and Lake files, `IxCK/`, this package, the root `lean-toolchain` and `lakefile.lean`,
`ci.yml` and the local actions). `lake build` from this directory builds the same thing
without the inventory check.

A clean checkout needs nothing built beforehand. The package requires IxCK (`../../IxCK`)
and IxCC (`../../IxCC`) by path, and Blake3 through IxCC. Its `packagesDir` is IxCC's
(`IxCC/.lake/packages`), so the first build clones Blake3 at the revision of
`lake-manifest.json` there (network access) and builds it with Cargo, and later IxCC builds
reuse it. IxCK's objects go to the repository root's `.lake/kernel` (IxCK's `buildDir`),
IxCC's to `IxCC/.lake/build`. A cold build compiles IxCK's kernel and model tier, the IxCC
modules the bridge imports, Blake3 and this package.

Warnings in this package's modules are errors (`leanOptions` in `lakefile.toml`). The build
does not use `--wfail`, which would also fail on the deprecation warnings that IxCC's
modules emit today.

`lean-toolchain` must equal the root's (CI Jobs' toolchain check), and `update.yml` bumps it
with the others.
