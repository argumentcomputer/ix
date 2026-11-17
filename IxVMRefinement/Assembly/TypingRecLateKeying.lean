import IxVMRefinement.Decl.LateWrapRel
import IxVMRefinement.Assembly.TypingDefnStep
import IxVMRefinement.Callees.FireAux
import IxVMRefinement.StatementRel.LoadedReadsBlockTrace
import IxVMRefinement.StatementRel.LoadedReadsCanon

/-! # The keying of a late recursor's rule comparison

The generated rules of a recursor apply the recursor itself (the induction hypotheses), so the
comparison of the rules is read under a keying where the recursor's address resolves as well as
the prefix's: `lateRuleKey c A` (the prefix keying `c.stored.κ` with `A` added). It keeps every
key the prefix keying resolves (`lateRuleKey_keep`), resolves `A` to its table key
(`lateRuleKey_self`), and its loads are the narrow contract `wrap_rel` needs
(`wrapLoads_late`): at a stored key the prefix's load contract; at `A` the record is a
recursor, so the load answers a `Rec`, which is not a definition. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.Core

/-- **The keying of the rule comparison**: the prefix's resolved addresses and the recursor's. -/
noncomputable def lateRuleKey (c : Core.Ctx) (A : _root_.Address) : _root_.Address → KKey :=
  resKey c.t (fun a => c.resolvesOver c.env a ∨ a = A)

/-- The rule keying keeps every key the prefix keying resolves. -/
theorem lateRuleKey_keep (c : Core.Ctx) (A : _root_.Address) :
    ∀ x, c.stored.κ x ≠ unresolvedKey → lateRuleKey c A x = c.stored.κ x := by
  intro x hx
  rw [Ctx.stored_κ] at hx ⊢
  have hr := res_of_resKey_ne hx
  unfold lateRuleKey
  rw [resKey_of_res (Or.inl hr), resKey_of_res hr]

/-- The rule keying resolves the recursor's address to its table key. -/
theorem lateRuleKey_self (c : Core.Ctx) (A : _root_.Address) :
    lateRuleKey c A A = keyOf c.t A :=
  resKey_of_res (Or.inr rfl)

/-- The recursor's key resolves under the rule keying. -/
theorem lateRuleKey_self_resolved (c : Core.Ctx) (A : _root_.Address) :
    Resolved (lateRuleKey c A A) :=
  ⟨by rw [lateRuleKey_self]; exact Resolved.ne⟩

/-- **The loads of the rule comparison**: under the rule keying, a `get_ci` at a stored key
answers the stored constant (the prefix's load contract, rekeyed), and at the recursor's own
address answers a `Rec`, not a definition (the record there is a recursor). -/
theorem wrapLoads_late {c : Core.Ctx} (hcS : ScopedCoreFacts c.stored)
    (hdec : L1.EnvDecoded c.E) {A : _root_.Address} {cr : Ixon.Constant} {rc : Ixon.Recursor}
    (hrecA : Ix.Cert.recordAt c.E A = some cr) (hinfo : cr.info = .recr rc) :
    Decl.WrapLoads c (lateRuleKey c A) c.env.find? := by
  intro addr ptr h h' cs a ev hgood ha hres
  have hr := res_of_resKey_ne hres
  rcases hr with hr | hA
  · left
    have hκ : c.stored.κ (ixAddr a) = keyOf c.t (ixAddr a) := by
      rw [Ctx.stored_κ]; exact resKey_of_res hr
    have hne : c.stored.κ (ixAddr a) ≠ unresolvedKey := by rw [hκ]; exact Resolved.ne
    obtain ⟨ci, hfind, hrep⟩ := hcS.loads.getCI addr ptr h h' cs a ev trivial hne
      (CoreGood.ofRaw hgood (fun _ _ => trivial)) ha
    have hκ₂ : lateRuleKey c A (ixAddr a) = c.stored.κ (ixAddr a) :=
      lateRuleKey_keep c A _ hne
    have hname : ci.name ≠ unresolvedKey := by
      rw [FireAux.env_find?_name hfind]; exact hne
    refine ⟨ci, ?_, hrep.rekey_mono (lateRuleKey_keep c A) hname⟩
    rw [hκ₂]
    exact hfind
  · right
    obtain ⟨rawB, c', hh, hba, hex, -, hres'⟩ := L1.get_ci_block_trace_spec hgood.2 ha ev
    have hrec : recordOf c.E (ixAddr a) = some cr := by
      rw [recordOf_eq_recordAt_of_decoded hdec, hA]
      exact hrecA
    obtain ⟨lc, hget, hdecl⟩ := LoadedReads.recordOf_inv hrec
    have hb : rawB = lc.rawBytes := Core.load_escape hget hgood.1 rawB hh hba
    have hcc : c' = cr := by
      rw [hb, hdecl] at hex
      exact (Except.ok.inj hex).symm
    rw [hcc] at hres'
    unfold L1.GetCIBlockTraceResult at hres'
    rw [hinfo] at hres'
    obtain ⟨blobs, tree, v, -, -, hldv, htr⟩ := hres'
    obtain ⟨-, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, bR, planT, -, -, hv, -⟩ := htr
    intro v' hld' xs hcon
    rw [hldv] at hld'
    injection hld' with hvv
    rw [← hvv, hv] at hcon
    injection hcon with _ hname _
    exact absurd hname (by decide)

end IxVM.Refinement.Typing
