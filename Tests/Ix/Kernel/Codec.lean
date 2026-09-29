/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify
import Tests.Ix.Kernel.Egress

open Tests.Ix.Kernel.Ingress Tests.Ix.Kernel.Egress

namespace Tests.Ix.Kernel.Codec

def exactConstant (value : Ixon.Constant) : Bool :=
  match Ixon.deConstantExact (Ixon.serConstant value) with
  | .ok decoded => decoded == value
  | .error _ => false

def exactExpr (value : Ixon.Expr) : Bool :=
  match Ixon.deExpr (Ixon.serExpr value) with
  | .ok decoded => decoded == value
  | .error _ => false

def exactUniv (value : Ixon.Univ) : Bool :=
  match Ixon.deUniv (Ixon.serUniv value) with
  | .ok decoded => decoded == value
  | .error _ => false

#guard variants.all fun (_, value) => exactConstant value
#guard falseStore.all fun (_, value) => exactConstant value
#guard separatedFalse.all fun (_, value) => exactConstant value
#guard exactConstant sharedIdentity
#guard exactConstant ⟨.muts #[], #[], #[], #[]⟩

def wordBoundaries : List UInt64 :=
  [0, 1, 7, 8, 31, 32, 127, 128, 255, 256, 65535, 65536, 18446744073709551615]

#guard wordBoundaries.all fun n =>
  [Ixon.Expr.var n, .sort n, .str n, .nat n, .share n,
    .ref n #[n], .recur n #[n], .prj n n (.var 0)].all exactExpr
#guard wordBoundaries.all fun n => exactUniv (.var n)
#guard [0, 1, 31, 32, 255, 256].all fun n =>
  exactUniv (.addSucc n (.max (.var 18446744073709551615) (.imax .zero (.var 1))))
#guard [Ixon.Uses.erased, .linear, .affine, .many].all fun uses =>
  [Ixon.Owned.shared, .unique].all fun owned =>
    exactExpr (.all uses owned (.sort 0)
      (.lam uses (.var 0) (.letE true (.var 1) (.var 0) (.var 0))))
#guard exactExpr (.letE false (.sort 0) (.app (.var 0) (.var 1)) (.var 2))
#guard [1, 7, 8, 31, 32, 128].all fun n =>
  exactExpr ((List.range n).foldl (fun e i => .app e (.var i.toUInt64)) (.ref 0 #[]))

-- Exact framing rejects suffixes even though the legacy prefix API succeeds.
#guard match Ixon.deConstant (Ixon.serConstant identity ++ ⟨#[255]⟩) with
  | .ok value => value == identity
  | _ => false
#guard !(Ixon.deConstantExact (Ixon.serConstant identity ++ ⟨#[255]⟩)).isOk
#guard !(Ixon.deConstantExact (Ixon.serConstant identity ++ Ixon.serConstant identity)).isOk
#guard !(Ixon.deExpr (Ixon.serExpr (.var 0) ++ ⟨#[0]⟩)).isOk
#guard !(Ixon.deUniv (Ixon.serUniv .zero ++ ⟨#[0]⟩)).isOk
#guard !(Ixon.deConstantExact ⟨#[]⟩).isOk
#guard !(Ixon.deConstantExact ⟨#[255]⟩).isOk
#guard !(Ixon.deExpr ⟨#[0x80, 0xff]⟩).isOk
#guard !(Ixon.runGet Ixon.getTag0 ⟨#[0x88, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩).isOk

-- Every proper prefix of a valid record is incomplete.
#guard (List.range (Ixon.serConstant variedBlock).size).all fun n =>
  !(Ixon.deConstantExact ((Ixon.serConstant variedBlock).extract 0 n)).isOk

example (value : Ixon.Constant) (h : value.wireWF) :
    Ixon.deConstantExact (Ixon.serConstant value) = .ok value :=
  Ix.Ixon.Verify.deConstantExact_serConstant value h

end Tests.Ix.Kernel.Codec
