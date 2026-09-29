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

def boundedUniverses : List Ixon.Univ :=
  [.zero, .var 18446744073709551615, .max .zero (.var 0),
    .imax (.succ .zero) (.max (.var 1) (.succ (.var 2))),
    .max (.addSucc 31 .zero) (.addSucc 31 .zero)] ++
    [0, 1, 31, 32, 255, 256].map fun n =>
      .addSucc n (.max (.var 18446744073709551615) (.imax .zero (.var 1)))

-- Both exact and surplus budgets preserve valid inputs. Each limit is
-- independently enforced, including a budget shared by binary children.
#guard boundedUniverses.all fun value =>
  let bytes := Ixon.serUniv value
  [0, 1, 16].all (fun surplus =>
    match Ixon.Bounded.deUniv (bytes.size + surplus) (value.nodeCount + surplus) bytes with
    | .ok decoded => decoded == value
    | .error _ => false) &&
  !(Ixon.Bounded.deUniv (bytes.size - 1) value.nodeCount bytes).isOk &&
  !(Ixon.Bounded.deUniv bytes.size (value.nodeCount - 1) bytes).isOk

-- Ten bytes can request UInt64.max successor nodes. Rejection must happen
-- before successor construction, even when the encoded base is present.
def successorBomb : ByteArray := ⟨#[0x27, 255, 255, 255, 255, 255, 255, 255, 255, 0]⟩

#guard match Ixon.Bounded.deUniv successorBomb.size 64 successorBomb with
  | .error reason => reason == "getUnivBounded: expanded-node budget exhausted"
  | .ok _ => false

-- Cursor evidence distinguishes preallocation rejection from a decoder
-- that reads or expands the base before checking the claimed chain size.
#guard match Ixon.Bounded.getUniv 64 { bytes := successorBomb } with
  | .error reason state =>
    reason == "getUnivBounded: expanded-node budget exhausted" && state.idx == 9
  | .ok _ _ => false

#guard !(Ixon.runGet (Ixon.Bounded.getUnivFuel 1 64) (Ixon.serUniv (.succ .zero))).isOk
#guard boundedUniverses.all fun value =>
  let bytes := Ixon.serUniv value
  !(Ixon.Bounded.deUniv (bytes.size + 1) value.nodeCount (bytes ++ ⟨#[0]⟩)).isOk &&
    (List.range bytes.size).all (fun n =>
      !(Ixon.Bounded.deUniv bytes.size value.nodeCount (bytes.extract 0 n)).isOk)

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
