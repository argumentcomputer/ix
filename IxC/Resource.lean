module

public import IxC.Resource.ModeSource
public import IxC.Resource.Syntax
public import IxC.Resource.Eval
public import IxC.Resource.Read
public import IxC.Resource.Statement
public import IxC.Resource.Oracle
public import IxC.Resource.Check

/-!
# IxC.Resource

The resource-mode model and the mode checker.

* `IxC.Resource.ModeSource`: a record's modes, by position (the one module that
  knows how a record spells them).
* `IxC.Resource.Syntax`: run programs (`Prog`), value classes (`Cls`), mode
  skeletons (`Skel`).
* `IxC.Resource.Eval`: the reference evaluator `runR` and its four monitors.
* `IxC.Resource.Read`: the reading, records to a run program, with a class
  oracle.
* `IxC.Resource.Statement`: the canonical classes, `InputsOk`, `ExternOk`,
  `ModeSafe`, and the statements left to prove, as definitions.
* `IxC.Resource.Oracle`: the checker's class oracle, the kernel's fueled
  answers.
* `IxC.Resource.Check`: the uncertified mode checker `check`, its verdicts,
  and its soundness statement `CheckSound` (a definition).

Nothing in this library is imported by the kernel (`IxC.Kernel`) or by the
claim verifier, and nothing here is proved about the checker: `ModeSafe` is a
definition, and the checker is uncertified.
-/
