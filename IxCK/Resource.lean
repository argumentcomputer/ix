module

public import IxCK.Resource.ModeSource
public import IxCK.Resource.Syntax
public import IxCK.Resource.Eval
public import IxCK.Resource.Read
public import IxCK.Resource.Statement
public import IxCK.Resource.Oracle
public import IxCK.Resource.Check

/-!
# IxCK.Resource

The resource-mode model and the mode checker.

* `IxCK.Resource.ModeSource`: a record's modes, by position (the one module that
  knows how a record spells them).
* `IxCK.Resource.Syntax`: run programs (`Prog`), value classes (`Cls`), mode
  skeletons (`Skel`).
* `IxCK.Resource.Eval`: the reference evaluator `runR` and its four monitors.
* `IxCK.Resource.Read`: the reading, records to a run program, with a class
  oracle.
* `IxCK.Resource.Statement`: the canonical classes, `InputsOk`, `ExternOk`,
  `ModeSafe`, and the statements left to prove, as definitions.
* `IxCK.Resource.Oracle`: the checker's class oracle, the kernel's fueled
  answers.
* `IxCK.Resource.Check`: the uncertified mode checker `check`, its verdicts,
  and its soundness statement `CheckSound` (a definition).

Nothing in this library is imported by the kernel (`IxCK.Kernel`) or by the
claim verifier, and nothing here is proved about the checker: `ModeSafe` is a
definition, and the checker is uncertified.
-/
