import Compilatrix.Lir.Syntax
import Compilatrix.X86.Types

/-!
# Lir conditions as x86 conditions

The ten comparisons of `Lir.Cond` are x86 conditions on the low `w` bits
(`Lir.Cond.holds` mirrors `X86.Condition.holds`); `tz`/`tnz` test
`a &&& b`, which selection turns into a flag-setting `and` (and, once
M1.B1's rows land, `test`) followed by `je`/`jne`. Swapping a comparison's
operands swaps its condition. `Select.Lemmas` proves both facts.
-/

namespace Compilatrix.Xv.Select

/-- The x86 condition of a comparison; `none` for `tz`/`tnz`. -/
def condX86 : Lir.Cond → Option X86.Condition
  | .eq => some .eq
  | .ne => some .ne
  | .ult => some .unsignedLt
  | .ule => some .unsignedLe
  | .ugt => some .unsignedGt
  | .uge => some .unsignedGe
  | .slt => some .signedLt
  | .sle => some .signedLe
  | .sgt => some .signedGt
  | .sge => some .signedGe
  | .tz | .tnz => none

/-- The condition that holds of `(b, a)` exactly when `c` holds of `(a, b)`. -/
def swapCond : X86.Condition → X86.Condition
  | .eq => .eq
  | .ne => .ne
  | .unsignedLt => .unsignedGt
  | .unsignedLe => .unsignedGe
  | .unsignedGt => .unsignedLt
  | .unsignedGe => .unsignedLe
  | .signedLt => .signedGt
  | .signedLe => .signedGe
  | .signedGt => .signedLt
  | .signedGe => .signedLe

end Compilatrix.Xv.Select
