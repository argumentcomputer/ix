/- # The occurrence-pass engine: fixed order (design document §1.4)

## Contract
Input: an occurrence `a.{us} args` of an image-kind auxiliary of a changed
block, at least fully applied, after `Translate.rw` has rewritten its
arguments; and the block's `OptBlock`, built by `optBlockOf` from Pass 1's
canonical form and Pass 3a's images.

`engine` returns the first applicable pass's name and term, or `none`; the
rewrite then inlines the image (the baseline). The order is

  O11a → O2 → O3 → O4 → O6,

the definitional passes of CQ5.1 and CQ5.3a. O5 is the universe rule the passes use,
not a list entry. O1 is never ported: O6 builds the identical term on the
permutation-only blocks O1 covered (R04-07). O11a precedes O2 (CQ5.3a).
The proof-justified passes are deferred to CQ5.3b.

## Rewrite and resource bounds
The engine is fused with `Translate.rw`: it sees the source head and the
rewritten arguments before the image is inlined. O2 synthesises relocated
calls and invokes `engineN` on them; `engineN 0` returns `none` and `engine`
starts it with fuel 64.

## Faithfulness and canonicity obligations
O11a and O2–O6 target conversion with the image baseline (each pass module
gives its shape conditions and conversion argument). O11a's side-condition
declines are recorded by the driver's separate decline hook. The default
image rewrite has no hooks; a rewrite that records effects cannot publish a
shared rewritten expansion without retaining those effects.

## Evidence
The per-pass fixtures under `Tests/Ix/Compile/Pass/` and the `pass3` suite.
Donor: `jcb/ix-certify-compile` `a9cf3607`, `Ix/Compile/Pass/Opt/Engine.lean`.
-/
module
public import Ix.Compile.Pass.ImageView
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O2
public import Ix.Compile.Pass.Opt.O11a
public import Ix.Compile.Pass.Opt.O3
public import Ix.Compile.Pass.Opt.O4
public import Ix.Compile.Pass.Opt.O5
public import Ix.Compile.Pass.Opt.O6
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)

/-- The definitional occurrence passes in their fixed order; `recur`
rewrites the occurrences O2 synthesises (its relocated calls). -/
def passes (recur : Occ → Option Expr) : List (String × (OptEnv → Occ → Option Expr)) :=
  [("O11a", O11a.apply), ("O2", O2.apply recur), ("O3", O3.apply),
   ("O4", O4.apply), ("O6", O6.apply)]

/-- The first pass that applies, with its name. Fuel bounds the recursive
optimization of O2's relocated calls; zero returns `none`. -/
def engineN : Nat → OptEnv → Occ → Option (String × Expr)
  | 0, _, _ => none
  | fuel + 1, env, o =>
    let recur := fun o' => (engineN fuel env o').map (·.2)
    (passes recur).findSome? fun (nm, p) => (p env o).map (nm, ·)

/-- The engine at one occurrence. -/
def engine (env : OptEnv) (o : Occ) : Option (String × Expr) := engineN 64 env o

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
  for r in imageKinds inp.const? v.all do
    let some (.recInfo rv) := inp.const? r | continue
    let .ok img := v.image inp r | continue
    if let some s := readShape r img.levelParams rv.numParams rv.numMotives rv.numMinors
        rv.numIndices img.value ixRecInfo then
      shapes := shapes.insert r s
  return { all := v.all, change := changeOf v.canon, classOf, shapes }

end Ix.Compile.Pass.Opt

end
