import Ix.Tc.Verify.Whnf.Iota.NatReduction
import Ix.Tc.Verify.InstL

/-!
# Typed registered recursor RHS instantiation

`RawRecursorRuleRel` previously ended at `RawExprRel`.  That relation is
deliberately syntax-only, so it could not soundly be supplied to
`TrKExprS.instL`, whose proof needs typing at every application and binder.
The admission certificate now retains a `TrKExprS` derivation for the same
closed concrete rule body and registered Theory RHS.

This slice carries that derivation through both the pure universe-instantiation
specification and a successful production `TcM.instantiateUnivParams` run.
The runtime theorem is stated for the nonempty path used by universe-polymorphic
recursors such as `Nat.rec`; production's parameter-free fast path remains a
separate case.

The result intentionally stops at `defeq.rhs.instL levels`.  It does not claim
that this unapplied registered body is already `pattern.rhs.apply`: ordinary
iota still applies the recursor prefix, constructor fields, and any trailing
arguments.  Modeling those applications is the next bridge, and conflating
the two terms here would be unsound.
-/

namespace Ix.Tc

open Lean4Lean (VDefEq VEnv VExpr)

namespace RegisteredRecursorRuleRhsRel

/-- Project the syntax-only relation retained for admission diagnostics. -/
theorem rhsRaw
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    (h : RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq) :
    RawExprRel env nameOf trProj [] rule.rhs defeq.rhs := by
  obtain ⟨_, _, _, _, _, _, _, hrhs, _⟩ := h
  exact hrhs

/-- Project the typed structural relation required by verified walkers. -/
theorem rhsStructural
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    (h : RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq) :
    TrKExprS env defeq.uvars nameOf trProj [] rule.rhs defeq.rhs := by
  obtain ⟨_, _, _, _, _, _, _, _, hrhs⟩ := h
  exact hrhs

/-- Instantiate a typed registered rule body through the pure walker spec.
The quotient translation is necessary because universe smart constructors
are Theory-equivalent rather than syntactically identical. -/
theorem instUnivSpec
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    (h : RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq)
    {U' : Nat}
    (henv : env.WF)
    (hlit : ∀ literal, env.ContainsLits literal →
      VExpr.WF env U' [] (VExpr.trLiteral literal))
    (htp : TrProjOK env U' trProj)
    {us : Array (KUniv .anon)}
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF U')
    (harity : defeq.uvars = us.size)
    {result : KExpr .anon}
    (hspec : KExpr.instUnivSpec rule.rhs us = .ok result)
    (hfaithful : ∀ left right,
      KExpr.LevelReach us rule.rhs left →
      KExpr.LevelReach us rule.rhs right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach us rule.rhs level →
      level.size < UInt64.size) :
    TrKExpr env U' nameOf trProj [] result
      (defeq.rhs.instL (us.toList.map KUniv.toVLevel)) := by
  have hresult := TrKExprS.instL henv hlit htp hus harity
    h.rhsStructural (by trivial) hspec hfaithful hsize
  simpa using hresult

/-- Carry the registered RHS through an observed successful production
universe-instantiation run.  The walker Hoare theorem supplies the exact pure
spec equation; `instUnivSpec` above supplies the Theory translation. -/
theorem instantiateUnivParams_nonempty
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    (h : RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq)
    {U' : Nat}
    (henv : env.WF)
    (hlit : ∀ literal, env.ContainsLits literal →
      VExpr.WF env U' [] (VExpr.trLiteral literal))
    (htp : TrProjOK env U' trProj)
    {us : Array (KUniv .anon)}
    (hnonempty : us.isEmpty = false)
    (hus : ∀ level ∈ us, (KUniv.toVLevel level).WF U')
    (harity : defeq.uvars = us.size)
    {S : KExpr .anon → Prop}
    (hcollision : KExpr.CollisionFree S)
    (hreach : ∀ expr, KExpr.InstUnivReach us rule.rhs expr → S expr)
    {s after : TcState .anon}
    (hintern : s.env.intern.WF ∧
      ∀ expr, s.env.intern.ExprSupport expr → S expr)
    {result : KExpr .anon}
    (hrun : TcM.instantiateUnivParams rule.rhs us s = .ok result after)
    (hfaithful : ∀ left right,
      KExpr.LevelReach us rule.rhs left →
      KExpr.LevelReach us rule.rhs right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach us rule.rhs level →
      level.size < UInt64.size) :
    TrKExpr env U' nameOf trProj [] result
      (defeq.rhs.instL (us.toList.map KUniv.toVLevel)) := by
  have hwalk := TcM.instantiateUnivParams_wf hcollision hreach hintern
  rw [hrun] at hwalk
  have hspec : KExpr.instUnivSpec rule.rhs us = .ok result := by
    simpa [KExpr.instantiateUnivParamsSpec, hnonempty] using hwalk.2.1
  exact h.instUnivSpec henv hlit htp hus harity hspec hfaithful hsize

end RegisteredRecursorRuleRhsRel

namespace RawRecursorRuleRel

/-- The existential rule certificate exposes a particular registered RHS
that is both structurally translated and Theory-typed. -/
theorem registeredRhsTyped
    {env : VEnv} {nameOf : Address → Option Lean.Name}
    {trProj : RawProjRel} {id : KId .anon} {c : KConst .anon}
    {rule : RecRule .anon}
    (h : RawRecursorRuleRel env nameOf trProj id c rule) :
    ∃ defeq,
      RegisteredRecursorRuleRhsRel env nameOf trProj id c rule defeq ∧
      TrKExprS env defeq.uvars nameOf trProj [] rule.rhs defeq.rhs ∧
      env.HasType defeq.uvars [] defeq.rhs defeq.type := by
  obtain ⟨defeq, hrhs⟩ := h.registeredRhs
  exact ⟨defeq, hrhs, hrhs.rhsStructural, hrhs.rhsTyped⟩

end RawRecursorRuleRel

end Ix.Tc
