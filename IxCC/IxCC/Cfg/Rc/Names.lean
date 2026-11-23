import IxCC.Own.Plain.Syntax

set_option autoImplicit false
namespace IxCC.Cfg.Rc


def paramBound (lo : Nat) : List Fir.Var → Nat
  | [] => lo
  | x :: xs => max (x + 1) (paramBound lo xs)

mutual
def names (lo : Nat) : Own.Plain.Code → Bool
  | .act _ k | .reset _ _ _ _ _ k | .dropSlot _ k => names lo k
  | .bind x _ k | .reuse x _ _ _ _ k => decide (lo ≤ x) && names (x + 1) k
  | .jp _ ps _ _ b k => ps.all (fun p => decide (lo ≤ p)) &&
      names (paramBound lo ps) b && names lo k
  | .case _ alts d => namesAlts lo alts && namesOpt lo d
  | .jmp .. | .ret .. | .tcall .. | .trap => true
def namesAlts (lo : Nat) : List Own.Plain.Alt → Bool
  | [] => true
  | .mk _ b :: rest => names lo b && namesAlts lo rest
def namesOpt (lo : Nat) : Option Own.Plain.Code → Bool
  | none => true
  | some c => names lo c
end

mutual
def varsBelow (hi : Nat) : Own.Plain.Code → Bool
  | .act _ k | .reset _ _ _ _ _ k | .dropSlot _ k => varsBelow hi k
  | .bind x _ k | .reuse x _ _ _ _ k => decide (x < hi) && varsBelow hi k
  | .jp _ ps _ _ b k => ps.all (fun p => decide (p < hi)) && varsBelow hi b && varsBelow hi k
  | .case _ alts d => varsBelowAlts hi alts && varsBelowOpt hi d
  | .jmp .. | .ret .. | .tcall .. | .trap => true
def varsBelowAlts (hi : Nat) : List Own.Plain.Alt → Bool
  | [] => true
  | .mk _ b :: rest => varsBelow hi b && varsBelowAlts hi rest
def varsBelowOpt (hi : Nat) : Option Own.Plain.Code → Bool
  | none => true
  | some c => varsBelow hi c
end

mutual
def reuseCtorsOk (ctors : List Lam.CtorInfo) : Own.Plain.Code → Bool
  | .act _ k | .bind _ _ k | .dropSlot _ k => reuseCtorsOk ctors k
  | .reset _ _ c _ _ k | .reuse _ _ c _ _ k =>
    decide (Fir.CtorInfo.ofKey ctors c.key = some c) && decide (0 < c.arity) && reuseCtorsOk ctors k
  | .jp _ _ _ _ b k => reuseCtorsOk ctors b && reuseCtorsOk ctors k
  | .case _ alts d => reuseCtorsOkAlts ctors alts && reuseCtorsOkOpt ctors d
  | .jmp .. | .ret .. | .tcall .. | .trap => true
def reuseCtorsOkAlts (ctors : List Lam.CtorInfo) : List Own.Plain.Alt → Bool
  | [] => true
  | .mk _ b :: rest => reuseCtorsOk ctors b && reuseCtorsOkAlts ctors rest
def reuseCtorsOkOpt (ctors : List Lam.CtorInfo) : Option Own.Plain.Code → Bool
  | none => true
  | some c => reuseCtorsOk ctors c
end

end IxCC.Cfg.Rc
