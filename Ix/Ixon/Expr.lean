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
  | apps (func: Expr) (arg: Expr) (args: List Expr) : Expr
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

def putExprTag (tag: UInt8) (val: UInt64) : PutM :=
  let t := UInt8.shiftLeft tag 4
  if val < 8
  then putUInt8 (UInt8.lor t (UInt64.toUInt8 val)) *> pure ()
  else do
    putUInt8 (UInt8.lor (UInt8.lor t 0b1000) (byteCount val - 1))
    putTrimmedLE val

partial def putExpr : Expr -> PutM
| .vari i => putExprTag 0x0 i
| .sort u => putExprTag 0x1 0 *> putUniv u
| .cnst a lvls => do
  putExprTag 0x2 (Nat.toUInt64 lvls.length)
  putBytes a.adr *> List.forM lvls putUniv
| .rec_ i lvls => do
  putExprTag 0x3 (Nat.toUInt64 lvls.length)
  putUInt64LE i *> List.forM lvls putUniv
| .apps f a as => do
  putExprTag 0x4 (Nat.toUInt64 as.length)
  putExpr f *> putExpr a *> List.forM as putExpr
| .lams ts b => do
  putExprTag 0x5 (Nat.toUInt64 ts.length)
  List.forM ts putExpr *> putExpr b
| .alls ts b => do
  putExprTag 0x6 (Nat.toUInt64 ts.length) *>
  List.forM ts putExpr *> putExpr b
| .let_ t d b => do
  putExprTag 0x7 0
  putExpr t *> putExpr d *> putExpr b
| .proj n x => do
  putExprTag 0x8 n
  putExpr x
| .strl l => do
  let bytes := l.toUTF8
  putExprTag 0x9 (UInt64.ofNat bytes.size)
  putBytes bytes
| .natl l => do
  let bytes := natToBytesLE l
  putExprTag 0xA (UInt64.ofNat bytes.size)
  putBytes { data := bytes }




end Ixon
