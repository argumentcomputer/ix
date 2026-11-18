import IxVMRefinement.Assembly.TypingRecParentTie
import IxVMRefinement.Assembly.StoreArClauses
import IxVMRefinement.Assembly.NativeBlockAux
import IxVMRefinement.Decl.LateCtorRetHead

/-! # A registry entry's constructors return literally

`FamCtorRetHead t E fam` is the fact about a registry entry that the recursor comparison needs and
the recursor's own run does not check: at the member record the family's name is the key of, the
constructors' types return literally (`Decl.CtorRetHeadAt`). The native block's step has it from
`check_ctor_return_type` on its own loads, and the fold's clause carries it with the entry
(`FamRead.retHead`, through `famCtorRetHead_of_ixon`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam)

/-- **The constructors of a registry entry return literally**: at the member record whose
address the family's name is the key of (its projection record at `P`, of member `ip.idx` of the
block record at `ip.block`), every constructor's type is, through the block record's sharing
table, the member's parameters and the constructor's fields as literal binders, then an
application spine over a reference (`Decl.CtorRetHeadAt`). -/
def FamCtorRetHead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (fam : NativeFam .anon) : Prop :=
  ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
    fam.p.cvT.name = keyOf t P → Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip →
    Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
    ms[ip.idx.toNat]? = some (.indc ind) → Decl.CtorRetHeadAt cb ind

end IxVM.Refinement.Typing
