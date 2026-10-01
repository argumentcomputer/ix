module

public import ConLeche.Frontend.InModel.Nested

@[expose] public section

/-!
# The in-process modeller (task #200)

Entry point of the in-process construction of `_model` families for the
inductive blocks the direct routes do not install and the modeled
install expects a model for: **mutual** and **nested** blocks.  The
frontend calls `generate` at the block's record, before the block is
pushed, when the stream carries no model for it; the records it returns
are pushed ahead of the block and checked by the fold like any stream
declaration (the "certification tax"), and the block itself installs
through the modeled route.

Since task #207 this is the **only** model source: there is no
external preprocessor and no dependency, and every input is a raw
`lean4export` stream.  Soundness needs nothing from this module: a
wrong record is rejected or declined by the fold, never accepted.  Its
correctness decides only *coverage* — which blocks accept — and every
decline names its class, so the residual is exact and positive.

Rungs: `genMutual` (B1: index-free mutual; B2 adds indices), nested
(B3/B4) to follow.
-/

namespace ConLeche.Frontend.InModel

open ConLeche

/-- Is the block one this modeller is for: mutual (several types) or
nested (`numNested > 0`)? -/
def wants (b : BlockRec) : Bool :=
  b.types.length > 1 || b.types.any (·.numNested > 0)

/-- Generate the model records of a block, in stream order, or the
reason the block is declined. -/
def generate (ctx : Ctx) (b : BlockRec) : Except String (List Declaration) :=
  if b.types.any (·.numNested > 0) then
    genNested ctx b
  else
    genMutual ctx b

end ConLeche.Frontend.InModel
