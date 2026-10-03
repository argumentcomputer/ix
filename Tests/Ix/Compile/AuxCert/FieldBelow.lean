/-! H3: a constant named `X.below` / `X.brecOn` that is not an auxiliary.
Lean generates `.below`/`.brecOn` only for recursive inductives, so for a
non-recursive inductive (or a structure) the names are free for user code.
aux-gen gates `.below` generation on the name being present with a type that
ends in `Sort _` (`is_below_shaped`, aux_gen.rs:1317), not on recursiveness. -/
namespace FieldBelow
structure S where
  below : Nat → Type

def useS (s : S) : Type := s.below 0

def sNat : S := ⟨fun _ => Nat⟩
theorem useS_nat : useS sNat = Nat := rfl

inductive T
  | a
  | b

def T.below (_ : T) : Type := Nat
def T.brecOn (_ : T) : Nat := 7

theorem t_below : T.below T.a = Nat := rfl
theorem t_brecOn : T.brecOn T.b = 7 := rfl

structure SP where
  below : Prop

theorem sp (s : SP) (h : s.below) : s.below := h
end FieldBelow
