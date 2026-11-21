import IxVMRefinement.Assembly.GuardRawSubst

/-! # Physical raw readings at a fixed global keying

A scoped semantic reading supplies a physical raw AST under any globally resolved keying.
Constant and projection names are read from their actual heap addresses, so no syntactic
equality with the original semantic term or inverse of its keying is assumed.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core

theorem RawExprRep.ofOpenTm_keyed (rawKey : _root_.Address → KKey)
    [∀ a, Resolved (rawKey a)] {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h : Heap F} {d k : Nat} {E : KExpr} {p : SourceValue F}
    (represented : Tm κ d Γ h k E p) : ∃ R, RawExprRep rawKey h (k + d) R p := by
  induction represented with
  | bvarLocal cell small inside => exact ⟨_, _, .bvarLocal cell small (by omega)⟩
  | bvarFree cell small lower upper => exact ⟨_, _, .bvarLocal cell small (by omega)⟩
  | sort cell level _ => exact ⟨_, _, .sort cell level⟩
  | const cell address levels _ => exact ⟨_, _, .const cell address levels⟩
  | app cell _ _ left right =>
    obtain ⟨RF, EF, func⟩ := left
    obtain ⟨RA, EA, arg⟩ := right
    exact ⟨_, _, .app cell func arg⟩
  | lam cell _ _ level dom body =>
    obtain ⟨RD, ED, domain⟩ := dom
    obtain ⟨RB, EB, tail⟩ := body
    exact ⟨_, _, .lam cell domain (by simpa only [Nat.add_right_comm] using tail) level⟩
  | forallE cell _ _ level dom body =>
    obtain ⟨RD, ED, domain⟩ := dom
    obtain ⟨RB, EB, tail⟩ := body
    exact ⟨_, _, .forallE cell domain (by simpa only [Nat.add_right_comm] using tail) level⟩
  | letE cell _ _ _ type value body =>
    obtain ⟨RT, ET, typeRep⟩ := type
    obtain ⟨RV, EV, valueRep⟩ := value
    obtain ⟨RB, EB, tail⟩ := body
    exact ⟨_, _, .letE cell typeRep valueRep (by simpa only [Nat.add_right_comm] using tail)⟩
  | litNat cell limbs canonical => exact ⟨_, _, .litNat cell limbs canonical⟩
  | litStr cell bytes string => exact ⟨_, _, .litStr cell bytes string⟩
  | proj cell address _ inner =>
    obtain ⟨RI, EI, rep⟩ := inner
    exact ⟨_, _, .proj cell address rep⟩

end IxVM.Refinement.Decl
