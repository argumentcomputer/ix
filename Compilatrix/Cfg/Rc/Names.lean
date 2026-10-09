import Compilatrix.Own.Plain.Syntax

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc


def paramBound (lo : Nat) : List Fir.Var → Nat
  | [] => lo
  | x :: xs => max (x + 1) (paramBound lo xs)

mutual
def names (lo : Nat) : Own.Plain.Code → Bool
  | .act _ k => names lo k
  | .bind x _ k => decide (lo ≤ x) && names (x + 1) k
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

end Compilatrix.Cfg.Rc
