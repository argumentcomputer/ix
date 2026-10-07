/-! # Fixture: the library lemmas a value row uses (package V)

A value row's proof (`IxValueRows.proveWF`, `Ix/CompileCert/CliqueRows.lean`) is a
term over the artifact's own constants: `WellFounded.induction`,
`WellFounded.fix_eq`, `WellFounded.Nat.fix_eq`, `InvImage.wf`, `Nat.lt_wfRel`,
`funext`, `congrArg`, `Eq.trans`, `Eq.symm`, `id` (well-founded cliques); `congr`, `congrFun`,
`And.intro/left/right`, `True.intro` and the block's recursor (structural cliques). A library (Init+Std, Mathlib)
has them; the cone of a few cliques does not reach them by itself, so the
`changed-values` fixture adds this root, whose proof mentions each of them. -/

namespace Tests.Ix.CompileCert.ValueRowDefs

theorem lemmas : True := by
  have _ := @WellFounded.induction.{1}
  have _ := @WellFounded.fix_eq.{1, 1}
  have _ := @WellFounded.Nat.fix_eq.{1, 1}
  have _ := @InvImage.wf.{1, 1}
  have _ := Nat.lt_wfRel
  have _ := @funext.{1, 1}
  have _ := @congrArg.{1, 1}
  have _ := @Eq.trans.{1}
  have _ := @Eq.symm.{1}
  have _ := @Eq.mpr.{1}
  have _ := @id.{1}
  have _ := @congr.{1, 1}
  have _ := @congrFun.{1, 1}
  have _ := @And.intro
  have _ := @And.left
  have _ := @And.right
  have _ := True.intro
  trivial

end Tests.Ix.CompileCert.ValueRowDefs
