/-! Pass 3 negative control (`pass3` suite, not an aux-cert fixture): a Lean
name with the reserved component `_ix` (D14) must be rejected by the compiler
under `IX_PASS3=images`, and compiled as usual with the switch off. -/
namespace ReservedIx
def _ix.f : Nat := 1
theorem f_eq : _ix.f = 1 := rfl
end ReservedIx
