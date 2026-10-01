/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.BlockOrderProofs
import Tests.Ix.Kernel.Projection

open Ix.Kernel
open Ix.Ixon.BlockOrder
open Tests.Ix.Kernel.IxonFixtures (address)

namespace Tests.Ix.Kernel.BlockOrder

local instance [BEq α] : BEq (Except Error α) where
  beq
    | .ok x, .ok y => x == y
    | .error x, .error y => decide (x = y)
    | _, _ => false

def owner : Address := address 42

def defn (value : Ixon.Expr) (typ : Ixon.Expr := .sort 0) : Ixon.MutConst :=
  .defn ⟨.defn, .safe, 0, typ, value⟩

def indc (params : UInt64) (ctors : Array Ixon.Constructor := #[]) : Ixon.MutConst :=
  .indc ⟨false, 0, params, 0, .sort 0, ctors⟩

def record (members : Array Ixon.MutConst) : Ixon.Constant :=
  ⟨.muts members, #[], #[], #[.zero, .succ .zero, .var 0]⟩

def classes (source : Ixon.Constant) (blobs : List (Address × ByteArray) := [])
    (limits : Limits := {}) : Except Error Classes := do
  canonicalClasses limits (← prepare owner source blobs)

def accepts (source : Ixon.Constant) (blobs : List (Address × ByteArray) := []) (limits : Limits := {}) : Bool :=
  (checkBlock limits owner source blobs).isOk

def compareIn (source : Ixon.Constant) (left right : Ixon.Expr)
    (blobs : List (Address × ByteArray) := []) (partition : Classes := []) (fuel : Nat := 32) : Except Error Ordering := do
  let block ← prepare owner source blobs
  let ctx ← localContext block partition
  compareRoot block ctx fuel left right

def simple : Ixon.Constant := record #[indc 0, indc 1, indc 2]
def reversed : Ixon.Constant := record #[indc 2, indc 1, indc 0]
def duplicate : Ixon.Constant := record #[indc 0, indc 0]

#guard classes simple == .ok [[0], [1], [2]]
#guard classes reversed == .ok [[2], [1], [0]]
#guard accepts simple
#guard !accepts reversed
#guard !accepts duplicate
#guard accepts (record #[])
#guard accepts (record #[indc 0])
#guard classes simple [] ⟨32, 0⟩ == .error (.exhausted .refinement)

-- Sorting has to refine a tentative equivalence class before distinguishing
-- the two recursive references; input positions cannot authorize the order.
def weak : Ixon.Constant := record #[defn (.var 0), defn (.recur 0 #[]), defn (.recur 2 #[])]
def weakPermuted : Ixon.Constant := record #[defn (.recur 0 #[]), defn (.recur 2 #[]), defn (.var 0)]
def alphaSelf : Ixon.Constant := record #[defn (.recur 0 #[]), defn (.recur 1 #[])]
def alphaCycle : Ixon.Constant := record #[defn (.recur 1 #[]), defn (.recur 0 #[])]

#guard classes weak == .ok [[0], [1], [2]]
#guard classes weakPermuted == .ok [[2], [1], [0]]
#guard accepts weak
#guard !accepts weakPermuted
#guard !accepts alphaSelf
#guard !accepts alphaCycle
#guard classes weak [] ⟨32, 2⟩ == .error (.exhausted .refinement)
#guard classes weak [] ⟨32, 3⟩ == .ok [[0], [1], [2]]
#guard compareIn simple (.var 0) (.var 0) (fuel := 0) == .error (.exhausted .comparison)

-- The old Lean comparator ordered by length before comparing elements.
-- The Rust comparator, and this path, compare unequal vectors lexically.
def external : Ixon.Constant := { record #[] with refs := #[address 1, address 2] }
#guard compareIn external (.ref 0 #[1]) (.ref 0 #[0, 0]) == .ok .gt
#guard compareIn external (.ref 0 #[0]) (.ref 0 #[0, 0]) == .ok .lt
#guard compareIn external (.ref 0 #[]) (.ref 1 #[]) == .ok .lt
#guard compareIn external (.ref 1 #[0]) (.ref 0 #[1]) == .ok .lt

-- Host ingress simplifies levels before canonical comparison.
def unreduced : Ixon.Constant := { record #[] with
  univs := #[.max .zero (.var 0), .var 0, .imax (.succ .zero) (.var 0)] }
#guard compareIn unreduced (.sort 0) (.sort 1) == .ok .eq
#guard compareIn unreduced (.sort 2) (.sort 1) == .ok .eq

def shared : Ixon.Constant := { record #[] with sharing := #[.var 3, .share 0] }
def cyclic : Ixon.Constant := { record #[] with sharing := #[.share 0] }
def forward : Ixon.Constant := { record #[] with sharing := #[.share 1, .var 3] }
#guard compareIn shared (.share 1) (.var 3) == .ok .eq
#guard compareIn shared (.share 1) (.share 1) == .ok .eq
#guard compareIn shared (.share 1) (.share 1) (fuel := 4) == .error (.exhausted .comparison)
#guard compareIn cyclic (.share 0) (.var 3) ==
  .error (.malformed "sharing reference is not earlier than its use")
#guard compareIn forward (.share 0) (.var 3) ==
  .error (.malformed "sharing reference is not earlier than its use")
#guard compareIn external (.sort 9) (.sort 0) == .error (.malformed "universe index outside table")
#guard compareIn external (.ref 9 #[]) (.ref 0 #[]) == .error (.malformed "reference index outside table")
#guard compareIn external (.recur 0 #[]) (.ref 0 #[]) == .error (.malformed "member index outside block")

-- Literal order is independent of the spelling/address of the backing blob.
def blobs : List (Address × ByteArray) := [(address 1, ⟨#[0, 1]⟩), (address 2, ⟨#[255]⟩)]
#guard compareIn external (.nat 0) (.nat 1) blobs == .ok .gt
#guard compareIn external (.str 0) (.str 1)
  [(address 1, "z".toUTF8), (address 2, "a".toUTF8)] == .ok .gt
#guard compareIn external (.str 0) (.str 1) blobs == .error (.malformed "literal is not UTF-8")

-- Ref and recur denote the same physical key; projection heads use the
-- local constructor offsets. Unequal external alias keys stay unequal.
def localAliases : Ixon.Constant :=
  { weak with refs := #[Ix.Ixon.Projection.address ⟨.dPrj ⟨1, owner⟩, #[], #[], #[]⟩, address 1] }
#guard compareIn localAliases (.ref 0 #[]) (.recur 1 #[]) [] [[0], [1], [2]] == .ok .eq
#guard compareIn localAliases (.recur 1 #[]) (.ref 1 #[]) [] [[0], [1], [2]] == .ok .lt
#guard compareIn localAliases (.prj 0 0 (.var 0)) (.prj 1 0 (.var 0)) [] [[0], [1], [2]] == .ok .lt

def ctor (index fields : UInt64) : Ixon.Constructor := ⟨false, 0, index, 0, fields, .sort 0⟩
def ctorBlock : Ixon.Constant := record #[indc 0 #[ctor 0 0, ctor 1 0], indc 0 #[ctor 0 1], indc 1 #[ctor 0 0]]
def ctorContext : Except Error (List (Option Nat)) := do
  let block ← prepare owner ctorBlock []
  let ctx ← localContext block [[0, 1], [2]]
  let keys := block.entries.toList.flatMap fun e => e.address :: e.constructors
  return keys.map (Ingress.lookup ctx)
#guard ctorContext == .ok [some 0, some 2, some 3, some 0, some 2, some 1, some 4]

-- Stable sorting and equal-class grouping retain all members, including ties.
#guard sortM (fun x y => pure (compare (x / 10) (y / 10))) [21, 10, 22, 11, 0] ==
  .ok [0, 10, 11, 21, 22]
#guard groupSorted (fun x y => pure (compare (x / 10) (y / 10))) [0, 10, 11, 21, 22] ==
  .ok [[0], [10, 11], [21, 22]]

-- A block of recursors is checked in motive order, not structurally: member
-- `j` must eliminate motive `j` (the head of its result, as the reader reads
-- it) and declare one motive per member. `motive j` is a recursor of a block
-- with `motives` motives (no parameters, minors or indices) whose type ends in
-- motive `j`; its structural order is the reverse of its motive order, as for
-- the compiler's `Rose.rec`/`Rose.rec_1` block.
def motive (j : Nat) (motives : UInt64 := 2) : Ixon.MutConst :=
  let binder (body : Ixon.Expr) : Ixon.Expr := .all .many .shared (.sort 0) body
  let depth := motives.toNat + 1
  .recr ⟨false, false, 0, 0, 0, motives, 0,
    (List.range depth).foldl (fun body _ => binder body) (.var (UInt64.ofNat (depth - 1 - j))), #[]⟩

def recordCheck (source : Ixon.Constant) : Except Error Unit := checkRecord {} [] owner source

def motiveOrdered : Ixon.Constant := record #[motive 0, motive 1]
def motiveSwapped : Ixon.Constant := record #[motive 1, motive 0]

#guard recursorMotive motiveOrdered (match motive 1 with | .recr r => r | _ => default) == some 1
-- structurally the motive-ordered block is out of order, and the swapped one in order
#guard !accepts motiveOrdered
#guard accepts motiveSwapped
#guard recordCheck motiveOrdered == .ok ()
#guard recordCheck motiveSwapped == .error (.motiveOrder owner 0 (some 1))
#guard recordCheck (record #[motive 0 3, motive 1 3, motive 2 3]) == .ok ()
#guard recordCheck (record #[motive 0 3, motive 2 3, motive 1 3]) == .error (.motiveOrder owner 1 (some 2))
-- a repeated motive, a missing recursor, a motive count that is not the block's
#guard recordCheck (record #[motive 0, motive 0]) == .error (.motiveOrder owner 1 (some 0))
#guard recordCheck (record #[motive 0]) == .error (.motiveOrder owner 0 (some 0))
#guard recordCheck (record #[motive 0 1]) == .ok ()
-- a type whose result is not a motive
#guard recordCheck (record #[.recr ⟨false, false, 0, 0, 0, 1, 0, .sort 0, #[]⟩]) ==
  .error (.motiveOrder owner 0 none)
-- inductive, definition and mixed blocks keep the structural order
#guard recordCheck simple == .ok ()
#guard recordCheck reversed == .error (.nonCanonical owner [[2], [1], [0]])
#guard (recordCheck (record #[motive 0, indc 0])).isOk == accepts (record #[motive 0, indc 0])
#guard (recordCheck (record #[indc 0, motive 0])).isOk == accepts (record #[indc 0, motive 0])
#guard checkConstants {} [] [(owner, motiveOrdered), (owner, simple)] == .ok ()
#guard checkConstants {} [] [(owner, simple), (owner, motiveSwapped)] ==
  .error (.motiveOrder owner 0 (some 1))
-- through the bytes: the motive-ordered block passes the order stage (and the
-- checker then declines recursors without their inductive block); the swapped
-- one stops at the order stage
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, motiveOrdered)]) [] with
  | .error (.checker _) => true
  | _ => false
#guard match checkBytes 16 ByteAdmission.limits {} (Projection.encode [(owner, motiveSwapped)]) [] with
  | .error (.order (.motiveOrder _ 0 (some 1))) => true
  | _ => false

-- The certified entry with canonical block order admits the separately
-- stored family/recursor fixture and derives its model through the same
-- checker success.
def byteAccepts : Bool := (checkBytes 16 ByteAdmission.limits {}
  (Projection.encode Projection.separatedInput) []).isOk
#guard byteAccepts

#guard match checkBytes 16 ByteAdmission.limits {}
    (Projection.encode [(owner, reversed)]) [] with
  | .error (.order (.nonCanonical _ _)) => true
  | _ => false
#guard match checkBytes 16 ByteAdmission.limits ⟨32, 2⟩
    (Projection.encode [(owner, weak)]) [] with
  | .error (.order (.exhausted .refinement)) => true
  | _ => false

example (V : Type) [Ix.Kernel.SetTheory V] {env : Ix.Kernel.Env}
    (h : checkBytes 16 ByteAdmission.limits {}
      (Projection.encode Projection.separatedInput) [] = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  checkBytes_has_model V h

end Tests.Ix.Kernel.BlockOrder
