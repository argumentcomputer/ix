/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BinderOpening

/-! Let opening allocates the same fresh representation as binder opening,
while retaining the value in the actual local declaration. The reader uses
the declaration's type; typing the value is a separate inference obligation. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u

theorem openLet_eq (name : Mode.anon.F Name) (type value body : KExpr .anon)
    (before : TcState .anon) :
    TcM.openLet name type value body before =
      if before.env.nextFVarId.toNat + 1 < UInt64.size then
        let fresh : FVarId := ⟨before.env.nextFVarId⟩
        let internedLocal := before.env.intern.internExpr (KExpr.mkFVar fresh name)
        let opened := instantiateRev body #[internedLocal.1] internedLocal.2
        .ok (opened.1, fresh) {before with
          env := {before.env with
            nextFVarId := before.env.nextFVarId + 1
            intern := opened.2}
          lctx := before.lctx.push fresh (.ldecl name type value)}
      else .error (.other "free-variable id space exhausted") before := by
  unfold TcM.openLet
  change EStateM.bind TcM.freshFVarId _ before = _
  rw [EStateM.bind, TcM.freshFVarId]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · simp only [room, if_true]
    rfl
  · simp only [room, if_false]

/-- Let opening changes the local context and intern table while preserving
both complete inference maps, loaded declarations, and checking policy. -/
theorem openLet_inference_state {name : Mode.anon.F Name} {type value body opened : KExpr .anon}
    {fresh : FVarId} {before after : TcState .anon}
    (accepted : TcM.openLet name type value body before = .ok (opened, fresh) after) :
    after.env.inferCache = before.env.inferCache ∧
      after.env.inferOnlyCache = before.env.inferOnlyCache ∧
      after.env.consts = before.env.consts ∧ after.inferOnly = before.inferOnly := by
  rw [openLet_eq] at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl, rfl, rfl⟩
  · contradiction

/-- The production let local and its opened body implement dependent
context extension, including bodies containing nested lets. -/
theorem openLet_sound {β : Type u}
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {context : Model.Context β} {type value body opened : KExpr .anon}
    {A : AExpr β} {b : VExpr β} {fresh : FVarId} {before after : TcState .anon}
    {name : Mode.anon.F Name}
    (support : BinderOpeningSupport before body)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (absent : (⟨before.env.nextFVarId⟩ : FVarId) ∉ locals)
    (typeReads : readScopedExpr? resolve locals type = some A.erase)
    (bodyReads : readScopedExpr? resolve locals body 1 = some b)
    (accepted : TcM.openLet name type value body before = .ok (opened, fresh) after) :
    fresh = ⟨before.env.nextFVarId⟩ ∧
      readScopedExpr? resolve (fresh :: locals) opened = some b ∧
      LocalContextReading resolve (fresh :: locals) after.lctx (context.push A) ∧
      after.env.intern.WF := by
  have nameUnit : name = () := Subsingleton.elim _ _
  subst name
  have interned : (before.env.intern.internExpr
      (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ())).1 =
        KExpr.mkFVar ⟨before.env.nextFVarId⟩ () := by
    have keyFaithful : KExpr.KeyCollisionFree (fun term =>
        before.env.intern.ExprSupport term ∨ term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()) :=
      KExpr.keyCollisionFree_anon.mpr
      (support.faithful.mono fun term h => h.elim Or.inl (fun equal => .inr (.inl equal)))
    simpa only [KExpr.eraseMeta_anon] using
      before.env.intern.internExpr_eraseMeta support.coherent keyFaithful
  have walk := instantiateRev_spec (fvars := #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()])
    support.faithful support.constructed (by simpa using support.bound)
    (fun _ reached => .inr (.inr reached))
    (support.coherent.internExpr (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()))
    (fun _ member => (InternTable.ExprSupport.of_internExpr member).elim
      Or.inl (fun equal => .inr (.inl equal)))
  rw [openLet_eq] at accepted
  split at accepted
  · simp only [interned] at accepted
    cases accepted
    refine ⟨rfl, ?_, agreement.push (decl := .ldecl () type value) absent typeReads, walk.2.1⟩
    rw [walk.1]
    exact readScopedExpr?_instantiateRevSpec absent (by simpa using support.bound) bodyReads
  · contradiction

end Ix.Kernel.Consistency
