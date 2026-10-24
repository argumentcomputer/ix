import Ix.CompileResource
import Ix.Cert.SourceAccounting

namespace Ix.Cert.SourceAccountingPost
open Ix.Compile.SourceGraph

/-- Invert the actual validated post-step. The fact map is the received
field; authenticity of arbitrary caller-supplied nodes is not claimed. -/
theorem checked {out : Ix.CompileM.LeanPipelineOut} {profile : Option Ix.Resource.Profile}
    (h : Ix.CompileM.resourcePostStep out profile = .ok ()) :
    ∃ nodes, out.sourceNodes? = some nodes ∧ Accounting.check nodes out.env.named out.cenv.ungrounded = .ok () := by
  let next : Except String Unit := match out.sourceNodes? with
    | some nodes => (Accounting.check nodes out.env.named out.cenv.ungrounded).mapError Accounting.Issue.message
    | _ => .error "source accounting: original input facts are unavailable"
  have done (tail : next = .ok ()) : ∃ nodes, out.sourceNodes? = some nodes ∧
      Accounting.check nodes out.env.named out.cenv.ungrounded = .ok () := by
    cases facts : out.sourceNodes? with
    | none => simp [next, facts] at tail
    | some nodes =>
      refine ⟨nodes, rfl, ?_⟩
      cases run : Accounting.check nodes out.env.named out.cenv.ungrounded with
      | error issue => simp [next, facts, run, Except.mapError] at tail
      | ok value => cases value; rfl
  by_cases required : (out.annotated || profile.isSome) = true
  · by_cases failures : (!out.cenv.ungrounded.isEmpty) = true
    · cases facts : out.sourceNodes? <;>
        simp [Ix.CompileM.resourcePostStep, required, failures, facts, bind, Except.bind, throw] at h
    · cases validated : Ix.Resource.validate out.env (profile.getD (Ix.Resource.standardProfile out.env)) with
      | error why =>
        cases facts : out.sourceNodes? <;>
          simp [Ix.CompileM.resourcePostStep, required, failures, validated, bind, Except.bind] at h
      | ok value =>
        apply done
        cases facts : out.sourceNodes? <;>
          simp [Ix.CompileM.resourcePostStep, required, failures, validated, next, facts,
            bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h ⊢
        exact h
  · apply done
    cases facts : out.sourceNodes? <;>
      simp [Ix.CompileM.resourcePostStep, required, next, facts, throw, throwThe, MonadExceptOf.throw] at h ⊢
    exact h

theorem accounted {out : Ix.CompileM.LeanPipelineOut} {profile : Option Ix.Resource.Profile}
    (h : Ix.CompileM.resourcePostStep out profile = .ok ()) :
    ∃ nodes, out.sourceNodes? = some nodes ∧
      SourceAccounting.Accounted nodes.contains out.env.named.contains out.cenv.ungrounded.contains := by
  obtain ⟨nodes, facts, run⟩ := checked h
  exact ⟨nodes, facts, (SourceAccounting.check_success_iff ..).mp run⟩

end Ix.Cert.SourceAccountingPost
