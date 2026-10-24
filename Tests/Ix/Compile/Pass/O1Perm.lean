/- A4 per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O1, the recursor of a permuted block: `Src` declares the pair in Lean's order (Even, Odd),
`Can` in Ix's canonical order (Odd, Even; the image-gen fixture C1Perm), so `Can` is an identity
block and `Src` a pure permutation. With the switch on, `Src.Even.viaRec` and `Src.Odd.viaRecOn`
(full applications of `rec` and `recOn`) must compile to `Can`'s bytes (O1 fires; `recOn` goes to
the Ix `recOn`). `Col` is a collapsed block (`A`, `B` alpha-equivalent): O1 declines and the
baseline (the paired image) stays. Value pins by `rfl` over every constant. -/
set_option Elab.async false

namespace PassO1
namespace Src
mutual
inductive Even
  | zero : Even
  | s : Odd → Even
inductive Odd
  | s : Even → Odd
end

noncomputable def Even.viaRec (e : Even) : Nat :=
  @Even.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) (fun _ ih => ih + 1) e

noncomputable def Odd.viaRecOn (o : Odd) : Nat :=
  @Odd.recOn (fun _ => Nat) (fun _ => Nat) o 0 (fun _ ih => ih + 1) (fun _ ih => ih + 1)

theorem viaRec_two : Even.viaRec (.s (.s .zero)) = 2 := rfl
theorem viaRecOn_three : Odd.viaRecOn (.s (.s (.s .zero))) = 3 := rfl
end Src

namespace Can
mutual
inductive Odd
  | s : Even → Odd
inductive Even
  | zero : Even
  | s : Odd → Even
end

noncomputable def Even.viaRec (e : Even) : Nat :=
  @Even.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) e

noncomputable def Odd.viaRecOn (o : Odd) : Nat :=
  @Odd.recOn (fun _ => Nat) (fun _ => Nat) o (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1)

theorem viaRec_two : Even.viaRec (.s (.s .zero)) = 2 := rfl
theorem viaRecOn_three : Odd.viaRecOn (.s (.s (.s .zero))) = 3 := rfl
end Can

namespace Col
mutual
inductive A
  | a : B → A
  | nil : A
inductive B
  | b : A → B
  | nil : B
end

noncomputable def A.viaRec (x : A) : Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0 x

theorem viaRec_two : A.viaRec (.a (.b .nil)) = 2 := rfl
end Col
end PassO1
