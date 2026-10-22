import Aiur
import IxVM
import LegacyAiur
import LegacyIxVM.Toplevel
import LegacyMultiStark

/-! Both implementations must be usable in one Lean environment during the
migration. In particular, their AST and compiler declarations must not collide. -/

example : IxVM.modulus = 18446744069414584321 := rfl

example : Type := Aiur.Program IxVM.F
example : Type := LegacyAiur.Source.Toplevel

example : Aiur.Program Nat := aiur% "fn identity(x: Field) -> Field { x }"
example : LegacyAiur.Source.Toplevel := ⟦
  pub fn identity(x: G) -> G { x }
⟧
