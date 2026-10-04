/- # The definitional passes' engine: fixed order, fixed point (design document §1.4)

## Contract
Input: an occurrence `a.{us} args` of an image-kind auxiliary `a` of a
changed block, at least fully applied, met by the call-site rewrite
(`Ix.Compile.Pass.Translate.rw`) after its arguments were rewritten (the
traversal is bottom-up: arguments before the head, left to right); the
blocks' data (`OptBlock`, built here from Pass 1's canonical form and the
images of Pass 3a, `optBlockOf`).

Output: the rewrite of the **first** pass, in the fixed order below, whose
pattern and side condition hold, or `none`; on `none` the rewrite inlines the
image (the baseline, Def 3.6). The fixed order:

| slot | pass | pattern |
|---|---|---|
| 1 | O1 | `rec`/`recOn`, permuted block |
| 2 | O11a | `rec` of a split block that is Lean's mutual `sizeOf` family (cross fields through the instances); its references `T._sizeOf_inst` are scheduling edges (`O11a.addSizeOfEdges`, A6f) |
| 3 | O2 | `rec`, split block (relocated minors) |
| 4 | O3 | `casesOn`, permuted or split block |
| 5 | O4 | `below`/`brecOn`/`.go`/`.eq`, permuted block |
| — | O5 | the level rule inside O1-O4 (not a pattern) |
| 6 | O6 | `rec` whose image is `ρ` applied to its own variables |
| unit | O13a/b | cliques changed only by order, or by the fixed-parameter telescope: **A5's slot**, run once per clique after the occurrence passes; not implemented here |
| 6 | O8 | `casesOn` over a collapsed or lifted member: the Ix `casesOn` of the class (**proof-justified**, `pjPasses`) |
| 7 | O7 | `rec`/`recOn` over a collapsed block with identical motives and minors per class (**proof-justified**, `pjPasses`) |

**The engine is fused with the rewrite.** The design document's engine
traverses the baseline term and, at each image occurrence `img(a) args`,
applies the first pass. Pass 3b meets each occurrence exactly once, as
`a.{us} args` with `args` already rewritten, before it inlines `img(a)`. The
engine runs there: the occurrence is the pattern, and when no pass applies
the inline image *is* the baseline. Running the passes on the inlined term
instead would have to recognise `img(a)`'s developed body, which is the same
information read back from a less structured term.

## Faithfulness
O1-O6 are definitional (each module gives the conversion steps); a
composition of conversions is a conversion, so where only they fire the
engine's output is definitionally equal to the baseline. The
proof-justified passes (`pjPasses`: O8, O7; A6) give a term provably equal
to the occurrence's baseline (each module states the lemma Phase B
formalises); they fire only in the value of a definition, and the rewritten
constant equals its baseline by congruence (`funext`, `congrArg`) over the
rewritten occurrences. Arguments are rewritten before the head (each by its
own fixed point), and every pass copies its arguments unchanged.

## Canonicity
**Termination** [argued]. The measure is the number of image-kind
occurrences. A pass replaces its occurrence by a term over Ix auxiliaries
(`ρ`, `ρ.casesOn`, `ρ.below`, … are display names of Ix auxiliaries, never
image-kind heads) and copies the already-rewritten arguments, so it removes
one occurrence and introduces none; the baseline's inline image is itself
rewritten (Def 3.5 values) and contains no image-kind head. So one
bottom-up traversal reaches the fixed point.

**Confluence** [argued], so the fixed order is immaterial for the result:
* O1, O2, O3, O4 have pairwise disjoint patterns: O1 and O2 are `rec`/`recOn`
  with disjoint change kinds (permutation-only versus split), O3 is
  `casesOn`, O4 is the `below`/`brecOn` family.
* O5 is not a pattern: it is the level rule O1-O4 and O6 share.
* O11a's pattern is contained in O2's (a split block's `rec` whose minors
  are Lean's sizeOf family). On it the two outputs differ only in the minors
  of constructors with cross fields, where O11a puts `sizeOf f` through the
  instance and O2 the relocated recursor call: definitionally equal
  (O11a's faithfulness), not syntactically, so this overlap is ordered, not
  confluent: O11a runs first, because its output is the canonical one (the
  separately declared components' term).
* O6 overlaps O1 (a permutation-only block's `rec`) and O2 (a split
  component without cross fields). On the overlap both give `ρ` applied to
  `img(r)`'s body at the arguments, the same term (O1's `π, π′` and O6's
  `σ, σ′` are read off the same image).
* Every pass is left-linear and copies its arguments, so rewrites at nested
  positions commute; the bottom-up traversal rewrites inner occurrences
  first, so an outer pass's side condition (on the head, the block and the
  argument count) never depends on whether an inner one fired.
* The development cannot turn a bare occurrence into a full application
  here: the passes produce no λ-substitution (they only reorder arguments),
  and the baseline's development happens after the passes declined, on the
  occurrence that is being inlined.
The unit slot (O13) runs after the occurrence passes; O13 belongs to A5
(cliques are elaborated over the Ix auxiliaries, which the occurrence passes
restore, design document §1.4 order constraint 1).
* O8 and O7 come after O1-O6 and are disjoint from them: O8 needs a
  collapsed class, where O3 declines; O7 needs a collapsed, unsplit block,
  where O1 (permutation only) and O2 (split) decline and O6 cannot read a
  selection shape (a packed image's head is a projection). O8 (`casesOn`)
  and O7 (`rec`/`recOn`) have disjoint heads. Their side conditions compare
  arguments that are already rewritten (bottom-up), design document §1.4
  order constraint 3.

## Side condition and fallback
Per pass. The engine's own fallback is the baseline (`none`).

## Non-canonical set and evidence
See each pass. Evidence: the per-pass fixtures under `Tests/Ix/Compile/Pass/`
and the `pass3` suite's surgery comparison (constants the surgery rewrote,
byte-identical with the switch on or not).
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
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)

/-- The occurrence passes in their fixed order; `recur` rewrites the
occurrences O2 synthesises (its relocated calls). -/
def passes (recur : Occ → Option Expr) : List (String × (OptEnv → Occ → Option Expr)) :=
  [("O1", O1.apply), ("O11a", O11a.apply), ("O2", O2.apply recur), ("O3", O3.apply), ("O4", O4.apply), ("O6", O6.apply)]

/-- The proof-justified occurrence passes (A6), after the definitional ones:
they fire only in the value of a definition that no dependent demotes
(`Opt.Packed.pjAllowed`). -/
def pjPasses : List (String × (OptEnv → Occ → Option Expr)) :=
  [("O8", O8.apply), ("O7", O7.apply)]

/-- The first pass that applies, with its name. The bound is on the nesting of
O2's relocated calls (one level per component below the major's, in the
condensation DAG), far below it. -/
def engineN : Nat → OptEnv → Occ → Option (String × Expr)
  | 0, _, _ => none
  | fuel + 1, env, o =>
    let recur := fun o' => (engineN fuel env o').map (·.2)
    (passes recur ++ pjPasses).findSome? fun (nm, p) => (p env o).map (nm, ·)

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
