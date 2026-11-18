/-! # Lean sources of the value-records suite

Ordinary Lean declarations, checked by Lean's kernel, that `ixvm-value-records`
(`Tests.Ix.IxVM.ValueRecords`) reads from the test binary's environment and compiles with Ix's
compiler. None is bound by the default role table. -/

namespace Tests.Ix.IxVM.ValueRecordsDefs

/-- A theorem with no binder in its statement or its proof. -/
theorem proved : True := True.intro

/-- An opaque constant with no binder in its type or its value. -/
opaque sealed : True := True.intro

mutual
/-- The first of two definitions declared in one `mutual` block, each calling the other. -/
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
/-- The second. -/
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

end Tests.Ix.IxVM.ValueRecordsDefs
