/-! The exact four applications retained from Tc.AccelDiff. All witnesses
are checked by Lean's kernel and force the expected value or constructor. -/

namespace Tests.Ix.Kernel.AccelSemanticsDefs

def bitNat : Nat := BitVec.toNat (BitVec.ofNat (nat_lit 8) (nat_lit 5))
def bitUlt : Bool := BitVec.ult (BitVec.ofNat (nat_lit 8) (nat_lit 3))
  (BitVec.ofNat (nat_lit 8) (nat_lit 7))
def natLe : Decidable (3 ≤ 5) := Nat.decLe (nat_lit 3) (nat_lit 5)
def natEq : Decidable (4 = 6) := Nat.decEq (nat_lit 4) (nat_lit 6)

theorem bitNat_value : bitNat = 5 := rfl
theorem bitUlt_value : bitUlt = true := rfl
theorem natLe_head : (match natLe with | .isTrue _ => true | .isFalse _ => false) = true := rfl
theorem natEq_head : (match natEq with | .isTrue _ => true | .isFalse _ => false) = false := rfl

end Tests.Ix.Kernel.AccelSemanticsDefs
