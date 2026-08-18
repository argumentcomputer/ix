module

public section

namespace Collision

/- Deliberately differs from package A while exporting the same declaration
   names and its own compiler-only implementation edge. -/
unsafe def hiddenImpl : Nat := 4100

@[implemented_by hiddenImpl]
opaque hidden : Nat := 41

private unsafe def sealedImpl : Nat := 4101

@[implemented_by sealedImpl]
opaque sealed : Nat := 42

@[extern "lean_nat_add"]
opaque nativeAdd : (@& Nat) → (@& Nat) → Nat := fun _ _ => 9001

end Collision
