import Ix.Ixon.BlockOrder.Theorems
import Tests.Ix.Kernel.Projection

/-! Recursor-block order (`Ixon.BlockOrder.checkRecord`): a block of
recursors must be in motive order; every other block is accepted in any
member order (the compiler stores it in its source's order). Checked at
elaboration. -/

open Ix.Kernel
open Ixon.BlockOrder
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

-- A block of recursors is checked in motive order: member `j` must eliminate
-- motive `j` (the head of its result, as the reader reads it) and declare one
-- motive per member. `motive j` is a recursor of a block with `motives`
-- motives (no parameters, minors or indices) whose type ends in motive `j`.
def motive (j : Nat) (motives : UInt64 := 2) : Ixon.MutConst :=
  let binder (body : Ixon.Expr) : Ixon.Expr := .all .many .shared (.sort 0) body
  let depth := motives.toNat + 1
  .recr ⟨false, false, 0, 0, 0, motives, 0,
    (List.range depth).foldl (fun body _ => binder body) (.var (UInt64.ofNat (depth - 1 - j))), #[]⟩

def recordCheck (source : Ixon.Constant) : Except Error Unit := checkRecord owner source

def motiveOrdered : Ixon.Constant := record #[motive 0, motive 1]
def motiveSwapped : Ixon.Constant := record #[motive 1, motive 0]

#guard recursorMotive motiveOrdered (match motive 1 with | .recr r => r | _ => default) == some 1
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
-- inductive, definition and mixed blocks are accepted in any member order
#guard recordCheck (record #[indc 0, indc 1, indc 2]) == .ok ()
#guard recordCheck (record #[indc 2, indc 1, indc 0]) == .ok ()
#guard recordCheck (record #[indc 0, indc 0]) == .ok ()
#guard recordCheck (record #[defn (.recur 1 #[]), defn (.recur 0 #[])]) == .ok ()
#guard recordCheck (record #[motive 0, indc 0]) == .ok ()
#guard recordCheck (record #[indc 0, motive 0]) == .ok ()
-- a record that is not a block is unconstrained
#guard recordCheck ⟨.defn ⟨.defn, .safe, 0, .sort 0, .sort 0⟩, #[], #[], #[]⟩ == .ok ()

end Tests.Ix.Kernel.BlockOrder
