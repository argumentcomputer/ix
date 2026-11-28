import IxCC.Cfg.Rc.Markers

set_option autoImplicit false
namespace IxCC.Cfg.Rc

/-- **The raw 64-bit word layout** of a program on the reference-counted route: the registers
each function holds as untagged 64-bit words, and the functions whose result is one. A
function of the checked shape certificate (`Cfg.Rc.Raw.infer`, untrusted); what the native
lowering relies on is `Cfg.Rc.Raw.rawOk`, which it checks. -/
structure RawLayout where
  vars : Src.NatMap (List Nat) := .leaf
  rets : List Nat := []
  deriving Inhabited

namespace RawLayout

def isRaw (L : RawLayout) (f x : Nat) : Bool := (L.vars.getD f []).contains x

def retRaw (L : RawLayout) (f : Nat) : Bool := L.rets.contains f

end RawLayout

structure Program where
  base : Cfg.Program
  actions : Src.NatMap ActionTable
  raw : RawLayout := {}

end IxCC.Cfg.Rc
