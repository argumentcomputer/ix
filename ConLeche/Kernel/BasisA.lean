module

public import ConLeche.Kernel.Basis
public import ConLeche.Kernel.BasisGen

@[expose] public section

/-!
# The annotated basis blocks

The pinned basis declarations as the checker's own annotation pass
produces them, computed from the raw pins (`ConLeche/Kernel/Basis/*`)
while this module elaborates — see `ConLeche/Kernel/BasisGen.lean` for
the command and the recipe.  These are the constants the installation
stores (`installBasisDecl`) and the model proofs read.

The blocks are annotated in one run, in install order, so `Quot`'s
types are annotated over an environment that already holds the pinned
`Eq` — exactly the order `checkDecl` installs them in.

This module sits ABOVE `ConLeche.Kernel.TypeChecker` (it runs the
annotation), while `ConLeche.Kernel.Basis` — the raw pins, all the
kernel core needs — sits below it.  That is the whole reason the two
are separate modules.
-/

namespace ConLeche

#annotate_basis over []
  | eqA := eqRaw
  | eqReflA := eqReflRaw
  | eqRecA := eqRecRaw
  | natA := natRaw
  | natZeroA := natZeroRaw
  | natSuccA := natSuccRaw
  | natRecA := natRecRaw
  | punitA := punitRaw
  | punitUnitA := punitUnitRaw
  | punitRecA := punitRecRaw
  | emptyA := emptyRaw
  | emptyRecA := emptyRecRaw
  | falseA := falseRaw
  | falseRecA := falseRecRaw
  | quotA := quotRaw
  | quotMkA := quotMkRaw
  | quotLiftA := quotLiftRaw
  | quotIndA := quotIndRaw
  | quotSoundA := quotSoundRaw

/-- The annotated constants of one basis block, in dependency order. -/
def BasisKind.declsA : BasisKind → List ConstantInfo
  | .eqK => [eqA, eqReflA, eqRecA]
  | .natK => [natA, natZeroA, natSuccA, natRecA]
  | .punitK => [punitA, punitUnitA, punitRecA]
  | .emptyK => [emptyA, emptyRecA]
  | .falseK => [falseA, falseRecA]
  | .quotK => [quotA, quotMkA, quotLiftA, quotIndA, quotSoundA]

end ConLeche
