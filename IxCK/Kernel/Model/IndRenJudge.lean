module

public import IxCK.Kernel.Model.JudgeSound
public import IxCK.Kernel.Model.IndRename
public import IxCK.Kernel.Model.IndRenRecord
import IxCK.Kernel.Verify.Denote.IndFrame
import IxCK.Kernel.Verify.BridgeWfImp
import IxCK.Kernel.Verify.Leaves

public section

/-!
# The renamed judgements are sound where the renaming is invisible

`renameJ f J` (`Model/IndRenRecord.lean`) adjoins to `J` the typings of closed renamed subjects
and the conversions of renamed pairs. Where the renaming is invisible to the reading
(`RenameOk`, so `denoteMeta_renameConsts`), every claim `JudgeSound` makes of a judgement of
`renameJ f J` is the same claim of `J`'s judgement on the renamed terms:

* the renamed subject has the subject's scope, bound and leaf bound (`wscoped_renameConsts`,
  `Expr.looseBVarsBounded_renameConsts`, `leavesBounded_renameConsts`) and reads as it does;
* a context that suits a term suits its renaming (`ctxOk_renameConsts`): renaming rewrites each
  leaf's annotation only, and the annotation reads as before;
* the inferred type's frame: a closed subject's renaming has no leaves, so the inferred type has
  none either. (An open subject's renaming has renamed leaves, which is why `renameJ` adjoins
  typings of closed subjects only; the nested pins are handled apart.)

At the iota install the condition holds at the provisional environment (`blockRenameOk`), which
is the only model the rule laws read the package at.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key)

universe w

variable {V : Type w} [SetTheory V]

/-- Renaming constants keeps every free variable below the bound. -/
theorem fvarsBelow_renameConstsM {f : Key md → Key md} :
    ∀ (e : Expr md) {k : Nat}, Expr.fvarsBelow k e → Expr.fvarsBelow k (e.renameConsts f) := by
  intro e
  induction e <;> intro k h <;>
    simp_all [Expr.renameConsts, Expr.fvarsBelow]

/-- **A context that suits a term suits its renaming**, where the renaming is invisible to the
reading: the leaves keep their indices and their annotations read as before. -/
theorem ctxOk_renameConsts {env : Env md} {m : EnvModel V env} {f : Key md → Key md}
    (hro : RenameOk m.acval env f) {φ : LevelParam → Nat} {d : Nat} {Δa : List AnnotTerm}
    {e : Expr md} (h : CtxOk m φ d Δa e) : CtxOk m φ d Δa (e.renameConsts f) := by
  refine ⟨h.1, ?_⟩
  intro l hl
  rw [fvarLeaves_renameConstsE] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
  obtain ⟨hlt, hfb, tya, Aa, hden, hAa, hint, hok⟩ := h.2 l₀ hl₀
  exact ⟨hlt, fvarsBelow_renameConstsM _ hfb, tya, Aa,
    (denoteMeta_renameConsts hro l₀.2 d).trans hden, hAa, hint, hok⟩

/-- The renamed package keeps `J`'s annotations, so their scoping. -/
theorem judgeFrames_renameJ {J : Judgements md} {env : Env md} {f : Key md → Key md}
    (h : JudgeFrames J env) : JudgeFrames (renameJ f J) env :=
  ⟨h.annot_syntax, h.annot_wscoped, h.annot_bounded, h.annot_leaves⟩

/-- The shape package keeps `J`'s annotations, so their scoping. -/
theorem judgeFrames_shapeJ {J : Judgements md} {env : Env md} {f : Key md → Key md}
    (h : JudgeFrames J env) : JudgeFrames (shapeJ f J) env :=
  ⟨h.annot_syntax, h.annot_wscoped, h.annot_bounded, h.annot_leaves⟩

/-- **The renamed judgements are sound** where the renaming is invisible to the reading. -/
theorem judgeSound_renameJ {J : Judgements md} {env : Env md} {m : EnvModel V env}
    {f : Key md → Key md} (hro : RenameOk m.acval env f) (h : JudgeSound J m) :
    JudgeSound (renameJ f J) m where
  annot_syntax := h.annot_syntax
  annot_wscoped := h.annot_wscoped
  annot_bounded := h.annot_bounded
  annot_leaves := h.annot_leaves
  accepted := by
    intro φ d e t hj hws hb hL
    rcases hj with hj | ⟨-, hj⟩
    · exact h.accepted φ hj hws hb hL
    · obtain ⟨ea, hea⟩ := h.accepted φ hj (wscoped_renameConsts e hws)
        ((Expr.looseBVarsBounded_renameConsts f e 0).trans hb)
        (leavesBounded_renameConsts e hL)
      exact ⟨ea, (denoteMeta_renameConsts hro e d).symm.trans hea⟩
  infer := by
    intro φ d e t Δa hj hws hb hL ea ta hctx hea hta
    rcases hj with hj | ⟨-, hj⟩
    · exact h.infer φ hj hws hb hL hctx hea hta
    · exact h.infer φ hj (wscoped_renameConsts e hws)
        ((Expr.looseBVarsBounded_renameConsts f e 0).trans hb)
        (leavesBounded_renameConsts e hL) (ctxOk_renameConsts hro hctx)
        ((denoteMeta_renameConsts hro e d).trans hea) hta
  defeq := by
    intro φ d a b Δa hj hwsa hba hLa hwsb hbb hLb aa ba hca hcb hda hdb hga hgb
    rcases hj with hj | hj
    · exact h.defeq φ hj hwsa hba hLa hwsb hbb hLb hca hcb hda hdb hga hgb
    · exact h.defeq φ hj (wscoped_renameConsts a hwsa)
        ((Expr.looseBVarsBounded_renameConsts f a 0).trans hba)
        (leavesBounded_renameConsts a hLa) (wscoped_renameConsts b hwsb)
        ((Expr.looseBVarsBounded_renameConsts f b 0).trans hbb)
        (leavesBounded_renameConsts b hLb)
        (ctxOk_renameConsts hro hca) (ctxOk_renameConsts hro hcb)
        ((denoteMeta_renameConsts hro a d).trans hda)
        ((denoteMeta_renameConsts hro b d).trans hdb) hga hgb
  reads := by
    intro φ d e t Δa ea hj hws hb hL hctx hea
    rcases hj with hj | ⟨-, hj⟩
    · exact h.reads φ hj hws hb hL hctx hea
    · exact h.reads φ hj (wscoped_renameConsts e hws)
        ((Expr.looseBVarsBounded_renameConsts f e 0).trans hb)
        (leavesBounded_renameConsts e hL) (ctxOk_renameConsts hro hctx)
        ((denoteMeta_renameConsts hro e d).trans hea)
  frame := by
    intro φ d e t Δa ea hj hws hb hL hctx hea
    rcases hj with hj | ⟨hef, hj⟩
    · exact h.frame φ hj hws hb hL hctx hea
    · obtain ⟨hwst, hbt, hsub⟩ := h.frame φ hj (wscoped_renameConsts e hws)
        ((Expr.looseBVarsBounded_renameConsts f e 0).trans hb)
        (leavesBounded_renameConsts e hL) (ctxOk_renameConsts hro hctx)
        ((denoteMeta_renameConsts hro e d).trans hea)
      refine ⟨hwst, hbt, fun l hl => ?_⟩
      have hl' := hsub l hl
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
        ((hasFvar_renameConsts f e).trans hef)] at hl'
      exact nomatch hl'

/-! ## The block renaming is idempotent -/

/-- Renaming twice by an idempotent renaming is renaming once. -/
theorem renameConsts_idem {f : Key md → Key md} (hf : ∀ n, f (f n) = f n) :
    ∀ e : Expr md, (e.renameConsts f).renameConsts f = e.renameConsts f := by
  intro e
  induction e <;> simp_all [Expr.renameConsts]

/-- **The block renaming is idempotent** when no block name is a model's key. -/
theorem blockRen_idem {blockNames : List (Key md)}
    (hns : ∀ n, blockNames.contains n = true → n.isModelSuffix = false) :
    ∀ n, (fun n => if blockNames.contains n then auxKey n .model else n)
        ((fun n => if blockNames.contains n then auxKey n .model else n) n)
      = (fun n => if blockNames.contains n then auxKey n .model else n) n := by
  intro n
  dsimp only
  by_cases hn : blockNames.contains n = true
  · rw [if_pos hn]
    have hm : ¬ (blockNames.contains (auxKey n .model) = true) := by
      intro hc
      have h := hns _ hc
      simp [auxKey, Key.isModelSuffix] at h
    rw [if_neg hm]
  · rw [if_neg hn, if_neg hn]

end Ix.Kernel.Model
