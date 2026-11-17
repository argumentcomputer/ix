import IxVMRefinement.Assembly.TypingRecLateStep
import IxVMRefinement.Assembly.NativeBlockRetHeadIxon

/-! # The registry entry's literal constructor returns, in the native block step's form

The native block step states the literal return of the constructors it admits as
`FamIxonRetHead` (`NativeBlockRetHeadIxon.lean`), the fold's form of the fact. The recursor step
reads it as `FamCtorRetHead` (`TypingRecLateStep.lean`); the two shapes are the same inductive
definitions under two names, so one gives the other.
-/

namespace IxVM.Refinement.Typing

open Ix.Kernel.Semantics (NativeFam)

/-- The block step's application spine over a reference is the recursor step's. -/
theorem ixonAppHeadRef_of_block {sharing : List Ixon.Expr} {e : Ixon.Expr}
    (h : BlockIxonAppHeadRef sharing e) : Decl.IxonAppHeadRef sharing e := by
  induction h with
  | ref => exact .ref
  | recur => exact .recur
  | app _ ih => exact .app ih
  | share hs _ ih => exact .share hs ih

/-- The block step's literal return shape is the recursor step's. -/
theorem ixonRetHead_of_block {sharing : List Ixon.Expr} {n : Nat} {e : Ixon.Expr}
    (h : BlockIxonRetHead sharing n e) : Decl.IxonRetHead sharing n e := by
  induction h with
  | zero ha => exact .zero (ixonAppHeadRef_of_block ha)
  | all _ ih => exact .all ih
  | share hs _ ih => exact .share hs ih

/-- **`FamCtorRetHead` from the native block step's `FamIxonRetHead`.** -/
theorem famCtorRetHead_of_ixon {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {fam : NativeFam .anon}
    (h : FamIxonRetHead t E fam) : FamCtorRetHead t E fam :=
  fun P cm ip cb ms ind hn hcm hcmi hcb hms hind j ct hct =>
    ixonRetHead_of_block (h P cm ip cb ms ind hn hcm hcmi hcb hms hind j ct hct)

end IxVM.Refinement.Typing
