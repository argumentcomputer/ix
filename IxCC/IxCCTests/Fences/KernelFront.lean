import IxCC.Src.KernelFront.Proof

/-! The kernel front end's statements: the acceptance (the kernel's tiered
entry ran on exactly the envelope's records, blobs and binding section, and
accepted them), and the
classifier at one position in both directions (a `proof` class is the zero
condition of the sort the kernel core's runs give, and such runs give that
class). -/

/-- info: 'IxCC.Src.KernelFront.accept_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.KernelFront.accept_spec

/-- info: 'IxCC.Src.KernelFront.Ctx.sortCond_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.KernelFront.Ctx.sortCond_spec

/-- info: 'IxCC.Src.KernelFront.Ctx.sortCond_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.KernelFront.Ctx.sortCond_of_runs

/-- info: 'IxCC.Src.KernelFront.Ctx.classifyTerm_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.KernelFront.Ctx.classifyTerm_proof

/-- info: 'IxCC.Src.KernelFront.Ctx.classifyTerm_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.KernelFront.Ctx.classifyTerm_of_runs

/-- info: 'IxCC.Src.KernelFront.Ctx.classifyType_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.KernelFront.Ctx.classifyType_proof

/-- info: 'IxCC.Src.KernelFront.Ctx.classifyType_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.KernelFront.Ctx.classifyType_of_runs
