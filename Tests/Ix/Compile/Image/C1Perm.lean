/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C1Perm.lean` without its commands. -/
/-! Case 1: pure permutation of a genuinely mutual pair. The canonical block is declared in Ix's
canonical order (Odd, Even) — checked with `IX_RECURSOR_DUMP` — so that Ix compiles it as an
identity block; the source block is declared the other way round. -/
set_option Elab.async false

namespace C1
namespace Src
mutual
inductive Even
  | zero : Even
  | s : Odd → Even
inductive Odd
  | s : Even → Odd
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .zero => 0
  | .s o => o.toNat + 1
end

theorem three : Odd.toNat (.s (.s (.s .zero))) = 3 := rfl

def Even.isZero : Even → Bool
  | .zero => true
  | .s _ => false

noncomputable def Even.viaRec : Even → Nat :=
  @Even.rec (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) (fun _ ih => ih + 1)
end Src

namespace Can
mutual
inductive Odd
  | s : Even → Odd
inductive Even
  | zero : Even
  | s : Odd → Even
end

mutual
def Odd.toNat : Odd → Nat
  | .s e => e.toNat + 1
def Even.toNat : Even → Nat
  | .zero => 0
  | .s o => o.toNat + 1
end

def Even.isZero : Even → Bool
  | .zero => true
  | .s _ => false

noncomputable def Even.viaRec : Even → Nat :=
  @Even.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1)
end Can
end C1

