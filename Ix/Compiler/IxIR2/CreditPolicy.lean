import Ix.Compiler.IxIR2.Basic

/-!
# Versioned credit boundaries

The original policy keeps credits local to a call. The second policy permits
only direct non-tail calls to suspend credits in their owning continuation.
Neither policy passes credits as arguments or permits a live credit at return,
tail call, partial application, dynamic application, or an extern boundary.
-/

namespace Ix.Compiler.IxIR2

inductive CreditPolicy where
  | callLocalV0
  | suspendedCallsV1
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- An explicit artifact input; changing a credit boundary changes this tag. -/
def CreditPolicy.tag : CreditPolicy → String
  | .callLocalV0 => "call-local/0"
  | .suspendedCallsV1 => "suspended-direct-calls/1"

end Ix.Compiler.IxIR2
