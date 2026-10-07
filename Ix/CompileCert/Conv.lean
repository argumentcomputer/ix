import Ix.CompileCert.Conv.Tm
import Ix.CompileCert.Conv.Rel
import Ix.CompileCert.Conv.Erase
import Ix.CompileCert.Conv.Core
import Ix.CompileCert.Conv.Develop
import Ix.CompileCert.Conv.Typing
import Ix.CompileCert.Conv.Total
import Ix.CompileCert.Conv.Termination
import Ix.CompileCert.Conv.Stable
import Ix.CompileCert.Conv.Image

/-!
# M7 X1: conversion on the compiler's terms, the development lemma, the development's totality

The syntactic layer (framework F1 of the L2a scoping note) the proved-once packages L2a-syn,
L2a-nested, L3-def and L3-clq state their theorems in. Everything is about the compiler's own
`Ix.Expr` through its erasure (`er`, `Tm.lean`): hashes, binder names and infos, `letE` flags
and `mdata` are not seen.

## The relation (`Rel.lean`)

`Conv Γ` on `Tm` (and `ExprConv Γ` on `Ix.Expr`): the equivalence and congruence closure of
β, η, the projections of `PProd.mk`/`And.intro` (exactly `Ix.Compile.Image.projCtor?`'s test),
and the environment's rules `Γ.ax` (δ of the expansions, `Env.ofExpansions`; any rule schema a
later package adds, such as the canonical recursors' ι as the syntactic `IxBlockLaws`). Not
included: ι, ζ, literals, structure and unit η, proof irrelevance, universe equivalence (none
is a step of the image path; each is a kernel conversion, so `Conv` is finer than the checker's
conversion). Basic theory: `Conv.refl`/`symm`/`trans` (`Conv.equivalence`), congruence through
every constructor (the constructors `app`, `lam`, `pi`, `letE`, `proj`, and `Conv.appN`),
`Conv.mono`; stability under lifting (`Conv.lift`), substitution of the converted term
(`Conv.inst`) and of the substituted value (`Conv.inst_val`, `Conv.inst₂`), lowering
(`Conv.lower`), constant and level maps (`Conv.mapC`: `substLevels`, `canonicalizeConstNames`),
abstraction of free variables (`Conv.abstractF`: `abstractFVars`); the Canon proofs' term
equality is contained in it (`exprConv_of_eRen`).

## The development (`Core.lean`, `Develop.lean`, `Image.lean`)

`Ix.Compile.Image.Develop` without its hash tables (`hinstP`, `happP`, `instantiateP`,
`substFVarsP`; equality with the tabled executable is the refactor named in the report).

* `develop_conv`, `hinstP_conv`, `happP_conv`, `instantiateP_conv`: **the developed term is
  convertible to the plain substitution** (to the application, at a call site), in every
  environment;
* `inline_conv`, `expansion_inline_conv`, `imageInlineP_conv`: with the δ-rule of the image
  constant or expansion, the inline form at a full application is convertible to the
  occurrence: **δ then the development**;
* `substFVarsP_conv`, `etaReduce_conv`: the image construction's developments and η.

## The totality (`Typing.lean`, `Total.lean`, `Termination.lean`)

The domain: simple typability of the erased input (`Typ`, `TypArgs`), decided by first-order
unification (the census runs it on every development of the `pass3` fixtures: all typable).

* `develop_total` (`HinstTotalAt`), `happP_total`, `instantiate_total`: on the domain the
  development succeeds from some fuel on, with one result of the input's type;
* `fuel_mono`: a result at some fuel is the result at every larger fuel, so `defaultFuel`
  suffices exactly when the run's depth is within it (`instantiateP_of_total`).

## Map to the design's definitions (PLAN-B, `docs/compiler-passes.md` §4)

* **Def 3.4** (the image of a recursor, §4.2–§4.3): the image is built with `substFVars`
  (`substFVarsP_conv`: its motive substitutions into the canonical minor types are conversions
  of the plain substitution) and `etaReduce` (`etaReduce_conv`), under view names mapped back by
  `canonicalizeConstNames` (`er_canonicalizeConstNames`, `Conv.mapC`); its rule statements use
  `instantiate`/`substFVars` (`instantiateP_conv`, `substFVarsP_conv`). That the rules hold by
  conversion is L2a-syn's theorem, stated with `Conv` over `Env.ofExpansions` and the canonical
  recursors' rules.
* **Def 3.5** (Lean's auxiliaries over images, §4.6): their values are expansions;
  `Env.ofExpansions` is their δ (with the images'), closed under lifting and substitution when
  the values are closed (`ofExpansions_liftClosed`, `ofExpansions_instClosed`).
* **Def 3.6** (the baseline, §4.5–§4.6, "δβ-convertible to Lean's own term", §1.6): the inline
  rewrite at a full application is `expansion_inline_conv` (δ, then β/η/pair projections at the
  substituted positions, never ι); with congruence (`Conv.appN`, the constructors) the
  rewrite of a whole constant is a conversion of Lean's term over the expansions' δ (L3-def
  states it for `Ix.Compile.Pass.Translate.rw`).
-/
