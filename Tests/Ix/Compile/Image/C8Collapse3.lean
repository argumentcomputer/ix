/- image-gen fixture (`Tests/Ix/Compile/Image.lean`), elaborated at run time and in no Lake library:
   the prototype's `exp-prototype/CertProto/Cases/C8Collapse3.lean` without its commands. -/
/-! Case 8: a collapsed pair sharing a block with a third member (F1_Collapse2p1), and a
collapsed class of three. -/
set_option Elab.async false

namespace C8
namespace Src
mutual
inductive A where
  | z
  | s : C → A
inductive B where
  | z
  | s : C → B
inductive C where
  | n : A → B → C
  | e
end

mutual
def A.f : A → Nat
  | .z => 0
  | .s c => c.f + 1
def B.f : B → Nat
  | .z => 10
  | .s c => c.f + 2
def C.f : C → Nat
  | .n a b => a.f + b.f
  | .e => 5
end
theorem f_ex : C.f (.n (.s .e) (.s .e)) = 13 := rfl

mutual
def A.h : A → Nat
  | .z => 0
  | .s c => c.h + 1
def B.h : B → Nat
  | .z => 0
  | .s c => c.h + 1
def C.h : C → Nat
  | .n a b => a.h + b.h
  | .e => 5
end

noncomputable def viaRec : C → Nat :=
  @C.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) 0 (fun _ ih => ih + 1) 10 (fun _ ih => ih + 2)
    (fun _ _ iha ihb => iha + ihb) 5
theorem viaRec_ex : viaRec (.n (.s .e) (.s .e)) = 13 := rfl

def C.isE : C → Bool
  | .e => true
  | _ => false
end Src

namespace Can
mutual
inductive X where
  | z
  | s : C → X
inductive C where
  | n : X → X → C
  | e
end
mutual
def X.h : X → Nat
  | .z => 0
  | .s c => c.h + 1
def C.h : C → Nat
  | .n a b => a.h + b.h
  | .e => 5
end
def C.isE : C → Bool
  | .e => true
  | _ => false
end Can
end C8

namespace C8b
namespace Src
mutual
inductive A where
  | z
  | s : B → A
inductive B where
  | z
  | s : C → B
inductive C where
  | z
  | s : A → C
end
mutual
def A.f : A → Nat
  | .z => 1
  | .s b => b.f * 2
def B.f : B → Nat
  | .z => 3
  | .s c => c.f * 5
def C.f : C → Nat
  | .z => 7
  | .s a => a.f * 11
end
theorem f_ex : A.f (.s (.s (.s .z))) = 2 * 5 * 11 * 1 := rfl
noncomputable def viaRec : B → Nat :=
  @B.rec (fun _ => Nat) (fun _ => Nat) (fun _ => Nat) 1 (fun _ ih => ih * 2) 3 (fun _ ih => ih * 5) 7 (fun _ ih => ih * 11)
theorem viaRec_ex : viaRec (.s (.s (.s .z))) = 5 * 11 * 2 * 3 := rfl
def B.isZ : B → Bool
  | .z => true
  | .s _ => false
end Src
namespace Can
inductive X where
  | z
  | s : X → X
def X.isZ : X → Bool
  | .z => true
  | .s _ => false
end Can
end C8b

