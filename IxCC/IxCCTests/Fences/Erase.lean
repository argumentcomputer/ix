import IxCC.Lam.WordSem
import IxCC.Src.Proof.Mono
import IxCC.Src.Word
import IxCC.Lam.Proof.Mono
import IxCC.Lam.Erase.Proof.Correct
import IxCC.Src.Relevance.Proof.Sound
import IxCC.Src.Relevance.Proof.Canonical
import IxCC.Lam.Erase.Proof.ModesOk
import IxCC.Lam.Erase.Proof.WFProg

/-! Required axiom fences for the source-to-Lam theorems: clock
monotonicity of SrcEval and Lam, erasure's correctness, the relevance
checker's soundness, and the fixed-width words' lemmas (stage W1: the range lemma
`WordOp.eval_word_lt`, the width facts it uses, F6w's unfolding `fire_word`, and erasure's word
case).
Expected messages are preserved verbatim. -/

/-- info: 'IxCC.Src.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.eval_mono

/-- info: 'IxCC.Src.WordOp.eval_word_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.WordOp.eval_word_lt

/-- info: 'IxCC.Src.Width.size_pos' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.Width.size_pos

/-- info: 'IxCC.Src.Width.bits_pos' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.Width.bits_pos

/-- info: 'IxCC.Src.Width.size_le_of_bits_le' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.Width.size_le_of_bits_le

/-- info: 'IxCC.Src.fire_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.fire_word

/-- info: 'IxCC.Src.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.apply_mono

/-- info: 'IxCC.Src.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.applyAll_mono

/-- info: 'IxCC.Src.fire_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.fire_mono

/-- info: 'IxCC.Src.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.force_mono

/-- info: 'IxCC.Src.forceAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.forceAll_mono

/-- info: 'IxCC.Src.evalConst_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.evalConst_mono

/-- info: 'IxCC.Src.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.run_mono

/-- info: 'IxCC.Lam.eval_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.eval_mono

/-- info: 'IxCC.Lam.apply_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.apply_mono

/-- info: 'IxCC.Lam.force_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.force_mono

/-- info: 'IxCC.Lam.evalList_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.evalList_mono

/-- info: 'IxCC.Lam.applyAll_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.applyAll_mono

/-- info: 'IxCC.Lam.run_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.run_mono

/-! Erasure's simulation and correctness. -/

/-- info: 'IxCC.Lam.Erase.Proof.erase_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_correct

/-- info: 'IxCC.Lam.Erase.Proof.erase_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_refines

/-- info: 'IxCC.Lam.Erase.Proof.erase_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_spec

/-- info: 'IxCC.Lam.Erase.Proof.readback_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.readback_erase

/-- info: 'IxCC.Lam.Erase.Proof.readback_erase_nat' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.readback_erase_nat

/-- info: 'IxCC.Lam.Erase.Proof.vr_eraseVal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.vr_eraseVal

/-- info: 'IxCC.Lam.Erase.Proof.vr_obs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.vr_obs

/-- info: 'IxCC.Lam.Erase.Proof.Setting.level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.level

/-- info: 'IxCC.Lam.Erase.Proof.Setting.tr_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.tr_correct

/-- info: 'IxCC.Lam.Erase.Proof.Setting.apply_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.apply_correct

/-- info: 'IxCC.Lam.Erase.Proof.Setting.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.Setting.run_correct

/-- info: 'IxCC.Lam.Erase.Proof.sound_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.sound_term

/-- info: 'IxCC.Sem.SimUpTo.sim' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Sem.SimUpTo.sim

/-! The relevance checker's soundness (tier S). -/

/-- info: 'IxCC.Src.Relevance.Proof.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.check_sound

/-- info: 'IxCC.Src.Relevance.Proof.loop_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.loop_spec

/-- info: 'IxCC.Src.Relevance.Proof.visit_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.visit_spec

/-- info: 'IxCC.Src.Relevance.Proof.records_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.records_nil

/-- info: 'IxCC.Src.Relevance.Proof.term_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.term_nil

/-- info: 'IxCC.Src.Relevance.Proof.rest_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.rest_nil

/-- info: 'IxCC.Src.Relevance.Proof.subsingletonFields_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.subsingletonFields_nil

/-! C3's refusal of an eliminator away from a saturated spine only adds errors. -/

/-- info: 'IxCC.Src.Relevance.Proof.adds_partialElim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.adds_partialElim

/-- info: 'IxCC.Src.Relevance.Proof.bareHead_constHead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.bareHead_constHead

/-! The closure loop over any fact the term walk gives (`visit_spec` and `loop_spec` are its
tier-S instances, `check_soundC` its tier-C one). -/

/-- info: 'IxCC.Src.Relevance.Proof.visit_specQ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.visit_specQ

/-- info: 'IxCC.Src.Relevance.Proof.LoopInvQ.transfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.LoopInvQ.transfer

/-- info: 'IxCC.Src.Relevance.Proof.loop_visitQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.loop_visitQ

/-- info: 'IxCC.Src.Relevance.Proof.loop_specQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.loop_specQ

/-- info: 'IxCC.Src.Relevance.Proof.instsQ_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.instsQ_of_loop

/-- info: 'IxCC.Src.Relevance.Proof.check_instsQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.check_instsQ

/-! The relevance checks' facts as propositions (L1): tier C (`check_soundC`), the pairing C3
uses at a recursor, `checkCanonical`'s facts and the three facts about positions written erased. -/

/-- info: 'IxCC.Src.Relevance.Proof.term_nilC' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.term_nilC

/-- info: 'IxCC.Src.Relevance.Proof.check_soundC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.check_soundC

/-- info: 'IxCC.Src.Relevance.Proof.elimShape_recr_minors' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.elimShape_recr_minors

/-- info: 'IxCC.Src.Relevance.Proof.checkCanonical_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.checkCanonical_sound

/-- info: 'IxCC.Src.Relevance.Proof.param_erased_irr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.param_erased_irr

/-- info: 'IxCC.Src.Relevance.Proof.field_erased_dropped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.field_erased_dropped

/-- info: 'IxCC.Src.Relevance.Proof.arg_erased_irr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.arg_erased_irr

namespace IxCC.Src.Relevance.Proof.L1Repair

open IxCC.Src IxCC.Src.Relevance IxCC.Src.Relevance.Check IxCC.Src.Relevance.Check.Canonical
open IxCC.Src.Relevance.Proof

/-! L1's statements as first approved stated `CtorCanon` without the length of the classified
telescope past the parameters (`checkCanonical`'s `flds.length == nf`), and under that predicate
`field_erased_dropped` is false: a constructor declared with no fields whose type has one Π
binder, written erased, satisfies it. The repaired `CtorCanon` excludes that constructor. -/

/-- `CtorCanon` as first approved. -/
private def CtorCanonFirst (p : Program) (ann : Ann) (c : CId) (kr : CtorRel) : Prop :=
  ∃ sf lv ind cidx np nf ty, p.decl? c = some (.ctor sf lv ind cidx np nf ty) ∧
    kr.fields.length = nf ∧
    (∀ cr, ann.constRel? c = some cr → (cr.params.drop np).map FieldClass.ofRel = kr.fields) ∧
    ∀ (i : Nat) (actual : FieldClass) (b : Binder) (exp : Option Rel), kr.fields[i]? = some actual →
      ((classifyTelescope p [] (ty.piCount + 1) ty).1.drop np)[i]? = some (b, exp) →
      actual ≠ .proof .never ∧
      (if writtenErased b then actual.alwaysDropped = true
       else actual = (match exp with | some e => FieldClass.ofRel e | none => .keep))

/-- One Π binder, written erased. -/
private def cexTy : Term := .pi { contract := { uses := .erased } } {} (.sort .zero) (.sort .zero)

/-- No parameters, declared with no fields, the type `cexTy`. -/
private def cexP : Program :=
  Program.ofConsts [{ ref := default, addr := default, decl := .ctor true 0 0 0 0 0 cexTy }]

example : ¬ (∀ {p : Program} {ann : Ann} {k : CId} {kr : CtorRel}, CtorCanonFirst p ann k kr →
    ∀ {i : Nat}, fieldWrittenErased p k i = true →
      ∃ cls, kr.fields[i]? = some cls ∧ cls.alwaysDropped = true) := fun h => by
  have hc : CtorCanonFirst cexP {} 0 ⟨[]⟩ :=
    ⟨true, 0, 0, 0, 0, 0, cexTy, rfl, rfl, fun _ h => by simp [Ann.constRel?, NatMap.get?] at h,
      fun i _ _ _ h => by simp at h⟩
  obtain ⟨cls, hcls, _⟩ := h hc (i := 0) (by decide)
  simp at hcls

example : ¬ CtorCanon cexP {} 0 ⟨[]⟩ := by
  rintro ⟨sf, lv, ind, cidx, np, nf, ty, hd, hl, hf, -⟩
  have hd' : cexP.decl? 0 = some (.ctor true 0 0 0 0 0 cexTy) := rfl
  rw [hd'] at hd
  cases hd
  revert hf
  decide

end IxCC.Src.Relevance.Proof.L1Repair

/-! Erasure decides the declarations' well-formedness (`progWF`), so
`erase_correct` and `erase_refines` need no premise about them. -/

/-- info: 'IxCC.Lam.Erase.Proof.progWF_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.progWF_iff

/-- info: 'IxCC.Lam.Erase.Proof.erase_progWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_progWF

/-- info: 'IxCC.Src.NatMap.mem_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.NatMap.mem_toList

/-! Erasure's constructor table has a row for every key it emits. -/

/-- info: 'IxCC.Lam.Erase.Proof.erase_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_reg

/-! Registering the rows a root's result needs: a row for each constructor,
and nothing else of the state changes. -/

/-- info: 'IxCC.Lam.Erase.Proof.csound_registerResultRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.csound_registerResultRow

/-- info: 'IxCC.Lam.Erase.Proof.csound_registerRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.csound_registerRows

/-- info: 'IxCC.Lam.Erase.Proof.CtorsOnly.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.CtorsOnly.refl

/-- info: 'IxCC.Lam.Erase.Proof.CtorsOnly.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.CtorsOnly.trans

/-- info: 'IxCC.Lam.Erase.Proof.registerCtor_ctorsOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.registerCtor_ctorsOnly

/-- info: 'IxCC.Lam.Erase.Proof.registerResultRow_ctorsOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.registerResultRow_ctorsOnly

/-- info: 'IxCC.Lam.Erase.Proof.registerRows_ctorsOnly' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.registerRows_ctorsOnly

/-! Erasure's output is well formed. -/

/-- info: 'IxCC.Lam.Erase.Proof.erase_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_wellFormed

/-- info: 'IxCC.Lam.Erase.Proof.erase_spec_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_spec_run

/-- info: 'IxCC.Lam.Erase.Proof.tr_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.tr_wf

/-- info: 'IxCC.Lam.Erase.Proof.bodyR_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.bodyR_wf

/-! `ModesOk` as a proposition, its checker's soundness, and erasure's output
checked against it. -/

/-- info: 'IxCC.Lam.modesOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.modesOk_sound

/-- info: 'IxCC.Lam.ModesOk.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.ModesOk.check_sound

/-- info: 'IxCC.Lam.Erase.Proof.erase_modesOk' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_modesOk

/-- info: 'IxCC.Lam.Erase.Proof.erase_modesOkSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.erase_modesOkSpec

/-! Stage W1: the word primitives' meaning on literals (`IxCC.Lam.WordSem`). -/

/-- info: 'IxCC.Lam.Prim.sem_word' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Prim.sem_word

/-- info: 'IxCC.Lam.wordSem_ne_bool' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.wordSem_ne_bool

/-- info: 'IxCC.Lam.wordSem_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.wordSem_two

/-- info: 'IxCC.Lam.wordSem_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.wordSem_one


/-! Stage W1: erasure's word case (`IxCC.Lam.Erase.Proof.Word`, the producer cases `sound_wordForm`
and `reg_wordForm`). -/

/-- info: 'IxCC.Src.WordOp.eval_resultWidth' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.WordOp.eval_resultWidth

/-- info: 'IxCC.Lam.Erase.Proof.unboxesAt0_of_B' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.unboxesAt0_of_B

/-- info: 'IxCC.Lam.Erase.Proof.wordUnboxAt_of_B' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.wordUnboxAt_of_B

/-- info: 'IxCC.Lam.Erase.Proof.VR.unbox0_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.VR.unbox0_inv

/-- info: 'IxCC.Lam.Erase.Proof.VR.unbox0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.VR.unbox0

/-- info: 'IxCC.Lam.Erase.Proof.asWord?_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.asWord?_some

/-- info: 'IxCC.Lam.Erase.Proof.vr_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.vr_word

/-- info: 'IxCC.Lam.Erase.Proof.vr_mkWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.vr_mkWord

/-- info: 'IxCC.Lam.Erase.Proof.wordResult_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.wordResult_sim

/-- info: 'IxCC.Lam.Erase.Proof.wordResult_dec' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.wordResult_dec

/-- info: 'IxCC.Lam.Erase.Proof.primResult_word1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.primResult_word1

/-- info: 'IxCC.Lam.Erase.Proof.primResult_word2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.primResult_word2

/-- info: 'IxCC.Lam.Erase.Proof.word_value_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.word_value_sim

/-- info: 'IxCC.Lam.Erase.Proof.sound_wordForm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.sound_wordForm

/-- info: 'IxCC.Lam.Erase.Proof.reg_wordForm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Lam.Erase.Proof.reg_wordForm
