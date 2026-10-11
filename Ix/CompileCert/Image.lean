import Ix.CompileCert.Image.Fuel
import Ix.CompileCert.Image.Build
import Ix.CompileCert.Image.SimRec
import Ix.CompileCert.Image.Post
import Ix.CompileCert.Image.Dom
import Ix.CompileCert.Image.Total

/-!
# M7 L2a-syn: the non-nested image construction, proved syntactically

Syntactic image construction over the conversion framework in `Ix/CompileCert/Conv/**`: fuel
bounds, totality on `Dom`, and preservation of the image's declared type. The computation rules
by conversion remain a separate obligation.

## The development's fuel (`Fuel.lean`, decision D-X1-1)

The constant `Ix.Compile.Image.defaultFuel = 2 ^ 16` bounded by the input's height for the
shapes the image construction develops: inert values (`hinstP_inert`), passive variables
(`hinstP_passive`), head β of a first-order value (`happP_passive`) or with inert arguments
(`happP_inert`), first-order values at motive sites (`hinstP_sites`), and the sequential
substitutions of `substFVars` (`substChain_sites`, `substChain_passive`).

## The construction, restated (`Build.lean`)

`buildRecAppW D`, `imageProgW D`, `imageOfW D`: the compiler's `buildRecApp` and `imageOf` with the two
development calls as a parameter; the executables are the instance at the tabled development by
`rfl` (`buildRecApp_eq`, `imageOf_eq`); `imageOfP` is the instance at X1's table-free core.

## The construction from shifted counters (`Ren` … `SimRec`)

The fresh-name counter is irrelevant: `Ren ρ` (the same term up to renaming free variables), the
equivariance of every helper (`Ren.lean`), the free-variable invariants (`Fv.lean`,
`SimBuild.lean`), the simulation of two runs from related states (`Sim.lean`), and the
construction's steps run from shifted counters: telescopes (`sim_telescope`), the analyses
(`sim_findElim`, `sim_analyzeCanonMinor`, `sim_elimMotiveTypes`) and the relocation step itself
with two related developments (`sim_buildRecAppW`).

## L2a-2: the image's type (`Post.lean`)

`imageOfW_type`, `imageOf_type` (the executable), `blockView_image_type` (the compiler's view):
the image's type is Lean's recursor type over the canonical constants.

## L2a-1: totality on `Dom` (`Dom.lean`, `Total.lean`)

`Dom` (decidable): the construction with the checking development `domDev` (every development in a
fuel class of `Fuel.lean`, within `2^16`) succeeds. `imageOfP_total`: on `Dom`, the construction at
X1's core with the constant fuel succeeds; `imageOf_total_of` (the executable, given R-1);
`blockView_expansion_total` (every auxiliary gets its expansion or a decline naming it).
-/
