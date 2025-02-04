
import Ix.Address
import Lean.Declaration
import Ix.Ixon.Serialize
import Ix.Ixon.Univ

namespace Ixon

-- 0xTTTT_LXXX
inductive Expr where
  -- 0x0, ^1
  | vari (idx: UInt64) : Expr 
  -- 0x1, {max (add 1 2) (var 1)}
  | sort (univ: Univ) : Expr
  -- 0x2 #dead_beef_cafe_babe {u1, u2, ... }
  | cnst (adr: Address) (lvls: List Univ) : Expr
  -- 0x3 #1.{u1, u2, u3}
  | rec_ (idx: UInt64) (lvls: List Univ) : Expr
  -- 0x4 (f x y z)
  | apps (func: Expr) (args: List Expr) : Expr
  -- 0x5 (λ A B C => body)
  | lams (types: List Expr) (body: Expr) : Expr
  -- 0x6 (∀ A B C -> body)
  | alls (types: List Expr) (body: Expr) : Expr
  -- 0x7 (let d : A in b)
  | let_ (type: Expr) (defn: Expr) (body: Expr) : Expr
  -- 0x8 .1 
  | proj : UInt64 -> Expr -> Expr
  -- 0x9 "foobar"
  | strl (lit: String) : Expr
  -- 0xA 0xdead_beef
  | natl (lit: Nat): Expr
-- array: 0xB
-- const: 0xC

def putExprTag (tag: UInt8) (val: UInt64) : PutM Unit := 
  let t := UInt8.shiftLeft tag 4
  if val < 8
  then putUInt8 (UInt8.lor t (Nat.toUInt8 (UInt64.toNat val))) *> pure ()
  else do
    let _ ← putUInt8 (UInt8.lor (UInt8.lor t 0b1000) (byteCount val - 1))
    let _ ← putTrimmedLE val
    pure ()

/- def putExpr : Expr -> PutM Unit -/
/- | .vari i => putExprTag 0x0 i -/
/- | .sort u => putExprTag 0x1 0 *> putUniv u -/
/- | .cnst a lvls => putExprTag 0x2 (Nat.toUInt64 <| lvls.length) -/
/- | _ => sorry -/

end Ixon
