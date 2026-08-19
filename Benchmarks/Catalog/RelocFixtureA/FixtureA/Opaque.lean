module

public section

namespace Collision

/- Relocation must recover this full body through `import all`, while keeping
its qualified public presentation opaque just as it is to source consumers. -/
@[no_expose] def concealedDefinition : Nat := 19

/- The logical body and executable implementation intentionally disagree.  A
   correct relocation must preserve both the opaque declaration and this
   compiler-only implementation edge. -/
unsafe def hiddenImpl : Nat := 1700

@[implemented_by hiddenImpl]
opaque hidden : Nat := 17

private unsafe def sealedImpl : Nat := 1701

@[implemented_by sealedImpl]
opaque sealed : Nat := 18

/- A foreign implementation is another compiler-only edge.  The fallback is
   deliberately wrong so the native consumer detects if `[extern]` is lost. -/
@[extern "lean_nat_add"]
opaque nativeAdd : (@& Nat) → (@& Nat) → Nat := fun _ _ => 9000

end Collision
