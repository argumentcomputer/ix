module

public import IxC.Resource.ModeSource
public import IxC.Resource.Syntax
public import IxC.Resource.Eval

/-!
# IxC.Resource

The resource-mode model and the mode checker.

* `IxC.Resource.ModeSource`: a record's modes, by position (the one module that
  knows how a record spells them).
* `IxC.Resource.Syntax`: run programs (`Prog`), value classes (`Cls`), mode
  skeletons (`Skel`).
* `IxC.Resource.Eval`: the reference evaluator `runR` and its four monitors.

Nothing in this library is imported by the kernel (`IxC.Kernel`) or by the
claim verifier, and nothing here is proved about the checker: `ModeSafe` is a
definition, and the checker is uncertified.
-/
