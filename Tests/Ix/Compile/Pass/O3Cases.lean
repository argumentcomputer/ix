/- A4 per-pass fixture (`pass3` suite), elaborated at run time and in no Lake library.
O3, `casesOn` over a permuted or split block. `Src.Even.isZero` (a permuted pair) and
`Src.SA.isStop`, `Src.SB.isLeaf` (a split block: `SB` does not mention `SA`) must compile to the
bytes of `Can`, where the pair is in canonical order and the components are declared separately
(O3 fires: the Ix `casesOn` of the class, same arguments). `Col.A.isNil` is over a collapsed block:
O3 declines and the baseline stays. Value pins by `rfl`. -/
set_option Elab.async false

namespace PassO3
namespace Src
mutual
inductive Even
  | zero : Even
  | s : Odd → Even
inductive Odd
  | s : Even → Odd
end

def Even.isZero (e : Even) : Bool := @Even.casesOn (fun _ => Bool) e true (fun _ => false)
theorem isZero_zero : Even.isZero .zero = true := rfl

mutual
inductive SA
  | a : SB → SA
  | stop : SA
inductive SB
  | b : SB → SB
  | leaf : SB
end

def SA.isStop (x : SA) : Bool := @SA.casesOn (fun _ => Bool) x (fun _ => false) true
def SB.isLeaf (x : SB) : Bool := @SB.casesOn (fun _ => Bool) x (fun _ => false) true
theorem isStop_stop : SA.isStop .stop = true := rfl
theorem isLeaf_b : SB.isLeaf (.b .leaf) = false := rfl
end Src

namespace Can
mutual
inductive Odd
  | s : Even → Odd
inductive Even
  | zero : Even
  | s : Odd → Even
end

def Even.isZero (e : Even) : Bool := @Even.casesOn (fun _ => Bool) e true (fun _ => false)
theorem isZero_zero : Even.isZero .zero = true := rfl

inductive SB
  | b : SB → SB
  | leaf : SB
inductive SA
  | a : SB → SA
  | stop : SA

def SA.isStop (x : SA) : Bool := @SA.casesOn (fun _ => Bool) x (fun _ => false) true
def SB.isLeaf (x : SB) : Bool := @SB.casesOn (fun _ => Bool) x (fun _ => false) true
theorem isStop_stop : SA.isStop .stop = true := rfl
theorem isLeaf_b : SB.isLeaf (.b .leaf) = false := rfl
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

def A.isNil (x : A) : Bool := @A.casesOn (fun _ => Bool) x (fun _ => false) true
theorem isNil_nil : A.isNil .nil = true := rfl
end Col
end PassO3
