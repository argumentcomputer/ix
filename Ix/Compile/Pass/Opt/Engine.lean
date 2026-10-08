/- # The occurrence-pass engine: fixed order (design document §1.4)

## Contract
Input: an occurrence `a.{us} args` of an image-kind auxiliary of a changed
block, at least fully applied, after `Translate.rw` has rewritten its
arguments left to right; and the block's `OptBlock`, built by `optBlockOf`
from Pass 1's canonical form and Pass 3a's images.

`engineFull` returns the first applicable pass's name, term and emitted
constants, or `none`. The production rewrite uses the developed image as
its fallback. The order is:

| stage | passes |
|---|---|
| definitional occurrence passes (`passes`) | O1, O11a, O2, O3, O4, O6 |
| proof-justified occurrence passes (`pjPasses`) | O8, O7 |
| proof-justified emitting passes (`emitPasses`) | O9, O10, O12 |

O5 is the universe rule used by the passes, not another list entry. O11b
and clique transport are separate unit-level operations; there is no
generic O13 occurrence pass here. O11a precedes O2 deliberately, and O10
precedes O12 so equal handlers use the simpler collapse.

## Rewrite and resource bounds
The engine is fused with `Translate.rw`: it sees the source head and the
rewritten arguments before the image is inlined. It does not repeatedly
run every pass over the developed term to test for a structural fixed
point. O2 can synthesize relocated calls and invokes `engineN` recursively
on them. `engineN 0` returns `none`; `engine` starts it with fuel 64.
`engineFull` tries the emitting passes if `engine` declines. The rewrite
and the hereditary development have their own bounds and error paths.

The generic `RwState.opt?` callback may return different results with and
without a definition site. Its fallback retry is part of that interface;
the production ordered-engine shortcut does not impose an order on every
possible callback. See `docs/compiler-passes.md` §1.4 and
`Ix/Compile/Pass/Translate.lean`.

## Faithfulness and canonicity obligations
O1–O6/O11a target conversion with the image baseline. O7, O8, O9, O10
and O12 target a provably equal canonical value. The production hook enables the latter
only at definition-value sites, and `Translate.rw` keeps the baseline at
the Lean name while arranging the canonical `_ix` form (decision 5, D1).
Each pass module gives its shape conditions and conversion/equality
argument. These arguments and finite controls do not establish the
general compiler theorem.

The original L3 target remains: total rewriting/passes on the stated
domain, denotation preservation under the pass side conditions, and
preservation of provability by clique transport. A general fixed-point or
idempotence argument must cover the actual traversal, synthesized O2
calls, fuel, fallback, and image construction. No confluence theorem here
makes the order immaterial: O11a and O2 have an intentional ordered
overlap. The more general canonical-form and compiler-composition targets
remain open; see `docs/compiler-certification.md` §1.7 and
`docs/compiler-passes.md` §§0.2, 3.5, 6.2.

## Evidence
The per-pass fixtures under `Tests/Ix/Compile/Pass/` and the `pass3` suite
exercise the implemented cases. The old switch-on/surgery comparison is
historical; surgery was removed at slice 6. Current gate assertions and
their limits are documented in `docs/compiler-gates.md`.
-/
module
public import Ix.Compile.Pass.Names
public import Ix.Compile.Pass.ImageView
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O1
public import Ix.Compile.Pass.Opt.O2
public import Ix.Compile.Pass.Opt.O3
public import Ix.Compile.Pass.Opt.O4
public import Ix.Compile.Pass.Opt.O5
public import Ix.Compile.Pass.Opt.O6
public import Ix.Compile.Pass.Opt.O11a
public import Ix.Compile.Pass.Opt.O7
public import Ix.Compile.Pass.Opt.O8
public import Ix.Compile.Pass.Opt.O11b
public import Ix.Compile.Pass.Opt.O9
public import Ix.Compile.Pass.Opt.O10
public import Ix.Compile.Pass.Opt.O12
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)

/-- The occurrence passes in their fixed order; `recur` rewrites the
occurrences O2 synthesises (its relocated calls). -/
def passes (recur : Occ → Option Expr) : List (String × (OptEnv → Occ → Option Expr)) :=
  [("O1", O1.apply), ("O11a", O11a.apply), ("O2", O2.apply recur), ("O3", O3.apply), ("O4", O4.apply), ("O6", O6.apply)]

/-- The proof-justified occurrence passes (A6), after the definitional ones:
they fire only in the value of a definition (`Opt.Packed.pjAllowed`), for its
canonical `_ix` form (D1). -/
def pjPasses : List (String × (OptEnv → Occ → Option Expr)) :=
  [("O8", O8.apply), ("O7", O7.apply)]

/-- The first pass that applies, with its name. Fuel bounds recursive
optimization of O2's relocated calls; zero returns `none`. Showing the
required bound for every input in the general domain is a separate
completeness obligation, not a consequence of this definition. -/
def engineN : Nat → OptEnv → Occ → Option (String × Expr)
  | 0, _, _ => none
  | fuel + 1, env, o =>
    let recur := fun o' => (engineN fuel env o').map (·.2)
    (passes recur ++ pjPasses).findSome? fun (nm, p) => (p env o).map (nm, ·)

/-- The engine at one occurrence. -/
def engine (env : OptEnv) (o : Occ) : Option (String × Expr) := engineN 64 env o

/-- The proof-justified occurrence passes that also emit canonical constants
(reserved `_ix` names, compiled with the block): O9's and O10's re-typed handlers,
O12's shared pair-valued helper. O10 before O12 (equal arms first). -/
def emitPasses : List (String × (OptEnv → Occ → Option (Expr × Array ConstantInfo))) :=
  [("O9", O9.apply), ("O10", O10.apply), ("O12", O12.apply)]

/-- The engine at one occurrence, with the canonical constants the rewrite
references: the occurrence passes, then the emitting ones. -/
def engineFull (env : OptEnv) (o : Occ) : Option (String × Expr × Array ConstantInfo) :=
  match engine env o with
  | some (nm, e) => some (nm, e, #[])
  | none => emitPasses.findSome? fun (nm, p) => (p env o).map fun (e, cs) => (nm, e, cs)

/-- One of the proof-justified passes (O7, O8, O9, O10 or O12): its
result goes to the canonical `_ix` form of the site only (D1). -/
def isProofJustified (nm : String) : Bool :=
  pjPasses.any (·.1 == nm) || emitPasses.any (·.1 == nm)

/-- The data of a changed block for the passes, from its view: Pass 1's
change kind and classes, and the shape of every Lean recursor's image. An
image that fails to build has no shape (its passes decline; the baseline
then reports the failure when it inlines). -/
def optBlockOf (inp : ViewInput) (v : BlockView) : OptBlock := Id.run do
  let mut classOf : Std.HashMap Name (Array Name) := {}
  for c in v.canon.components do
    for cls in c.classes do
      for m in cls do classOf := classOf.insert m cls
  let ixRecInfo : Name → Option RecursorVal := fun n =>
    match v.canonConsts.get? n with
    | some (.recInfo rv) => some rv
    | _ => none
  let mut shapes : Std.HashMap Name RecShape := {}
  let mut images : Std.HashMap Name (Array Name × Expr) := {}
  for r in imageKinds inp.const? v.all do
    let some (.recInfo rv) := inp.const? r | continue
    let .ok img := v.image inp r | continue
    images := images.insert r (img.levelParams, img.value)
    if let some s := readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors
        rv.numIndices img.value ixRecInfo then
      shapes := shapes.insert r s
  let ixRecs : Std.HashMap Name RecursorVal := v.canonConsts.fold (init := {}) fun m n c =>
    match c with
    | .recInfo rv => m.insert n rv
    | _ => m
  return { all := v.all, change := v.canon.change, classOf, shapes, images, ixRecs }

end Ix.Compile.Pass.Opt

end
