/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.SynthesisMeaning

/-! The earlier checking interface also supplies the hereditary semantic
invariant, once its expected type has been formed by the caller. -/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u v

theorem BinderInference.hereditary {β : Type u} {resolve : Address → Option (ConstRef β)}
    {entries : Model.Environment β} {context : Model.Context β} {locals : List FVarId} {fuel : Nat}
    {before : TcState .anon} {source : KExpr .anon} {term type : AExpr β}
    (support : BinderInference resolve entries locals context fuel before source term type) :
    TypingClaim.{u,v} entries context term type →
    LocalContextReading resolve locals before.lctx context →
    readScopedExpr? resolve locals source = some term.erase →
    HereditaryTyping.{u,v} entries context term type :=
  match support with
  | .sort .. | .cachedSort .. | .const .. | .polymorphic .. | .cachedConst .. =>
      fun typed _ _ => .atom typed (by constructor)
  | .fvar _ _ atIndex => fun typed _ _ => .bvar typed atIndex
  | .forallE miss trace opening domainTree bodyTree .. => fun typed agreement reading => by
      obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_all_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReading, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.absent keyedAgreement)
          domainReading bodyReading trace.openRun
      have domainTyped := (BinderInference.sound.{u,v} domainTree keyedAgreement domainReading trace.domainRun).2.typing
        (TypingClaim.sort _)
      have bodyTyped := (BinderInference.sound.{u,v} bodyTree openedAgreement openedReading trace.bodyRun).2.typing
        (TypingClaim.sort _)
      exact .forallE typed (domainTree.hereditary domainTyped keyedAgreement domainReading)
        (bodyTree.hereditary bodyTyped openedAgreement openedReading) rfl
  | .app (a := a) (A := A) _ miss trace functionTree head argumentTree conditions hashPath comparisonFaithful _ _ _ _ _ _ =>
      fun _ agreement reading => by
        obtain ⟨functionReading, argumentReading⟩ := readScopedExpr?_app_parts reading
        have keyedAgreement := miss.localContext.symm ▸ agreement
        have argumentAgreement := keyedAgreement.congr trace.contextPreserved.symm
        obtain ⟨functionTypeReads, functionTyped⟩ :=
          BinderInference.synthesis.{u,v} functionTree head keyedAgreement functionReading trace.functionRun
        obtain ⟨argumentTypeReads, argumentChecked⟩ :=
          BinderInference.sound.{u,v} argumentTree argumentAgreement argumentReading trace.argumentRun
        have sameType := AExpr.eq_of_erase_annotations
          (Option.some.inj (argumentTypeReads.symm.trans
            ((beq_readScopedExpr? comparisonFaithful hashPath).trans
              (readScopedExpr?_all_parts functionTypeReads).1))) conditions
        have checked := sameType ▸ argumentChecked
        have argumentTyped : TypingClaim.{u,v} entries context a A := by
          intro V _ constants realizes levels env valid
          have domainValid := (functionTyped V constants realizes levels env valid).2.1.1
          have checkedAt := checked V constants realizes levels env valid domainValid
          exact ⟨checkedAt.1, domainValid, checkedAt.2⟩
        exact .app (functionTree.hereditary functionTyped keyedAgreement functionReading)
          (sameType ▸ argumentTree.hereditary (sameType.symm ▸ argumentTyped) argumentAgreement argumentReading)
  | .lam _ miss trace opening bodyTree _ _ _ _ _ => fun typed agreement reading => by
      obtain ⟨domainReading, bodyReading⟩ := readScopedExpr?_lam_parts reading
      have keyedAgreement := miss.localContext.symm ▸ agreement
      have domainAgreement := keyedAgreement.congr trace.contextPreserved.symm
      obtain ⟨_, openedReading, openedAgreement, _⟩ :=
        openBinder_sound opening domainAgreement (trace.absent keyedAgreement) domainReading bodyReading trace.openRun
      exact .lam typed (bodyTree.hereditary typed.lambdaBody openedAgreement openedReading)
termination_by structural support

end Ix.Kernel.Consistency
