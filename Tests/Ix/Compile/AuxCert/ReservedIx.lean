/-! Pass 3 negative control (`pass3` suite, not an aux-cert fixture): a Lean
name with the reserved component `_ix` (D14) must be rejected by the compiler
under `IX_PASS3=images`, and compiled as usual with the switch off. With
several reserved names both compilers name the least by pretty form
(`ReservedIx.A._ix.g`; design document §11.6 item 3; the order-independence
of the Lean side is the `reserved-input` unit test's). -/
namespace ReservedIx
def _ix.f : Nat := 1
theorem f_eq : _ix.f = 1 := rfl
def Z._ix.h : Nat := 3
def A._ix.g : Nat := 2
end ReservedIx
