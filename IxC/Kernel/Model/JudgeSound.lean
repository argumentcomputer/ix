module

public import IxC.Kernel.Model.Capstone
public import IxC.Kernel.Model.Tiers
public import IxC.Kernel.Semantics.DeclJ
public import IxC.Kernel.Model.ClaimsJ
import IxC.Kernel.Verify.InferLeaves

public section

/-!
# What the model tier needs of a judgement package (lane l5)

The value-kind harvests (`Model/Harvest.lean`) read the runs a declaration
record carries through five facts and nothing else: the annotation's scoping
(`annotate_syntax`), readability of an accepted subject (`acceptedReads_of`),
the inference and conversion claims (`checkSoundAt`), the inferred type's
reading (`inferReads_of`) and its scoping (`inferTypeCore_WScoped`,
`_looseBVars`, `_fvarLeaves`). `JudgeSound J m` names them for a judgement
package `J` (`Semantics/DeclJ.lean`) at an environment model `m`, with the
claims stated over `J`'s relations (`InferClaimJ`, `DefEqClaimJ`,
`InferReadsJ`: the bodies of `InferClaim`, `DefEqClaim`, `InferReads` with the
run replaced by the relation).

`judgeSound_runJ` is the kernel's instance: the facts above at `runJ μ F`.
A harvest stated over `J` and `JudgeSound J` serves the kernel's fold through it,
and the rules tier's derivations through their own instance.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key)

universe w

variable {V : Type w} [SetTheory V]

/-- **What the harvests need of a judgement package at a model**: the scoping of
its outputs (`JudgeFrames`) and the four model facts. -/
structure JudgeSound (J : Judgements md) {env : Env md} (m : EnvModel V env) : Prop
    extends JudgeFrames J env where
  /-- an accepted subject reads -/
  accepted : ∀ (φ : LevelParam → Nat) {d : Nat} {e t : Expr md}, J.infer env d e t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true → Expr.LeavesBounded e →
    ∃ ea, denoteMeta m.acval env φ d e = some ea
  /-- the inference claim -/
  infer : ∀ φ, InferClaimJ J m φ
  /-- the conversion claim -/
  defeq : ∀ φ, DefEqClaimJ J m φ
  /-- an accepted subject's inferred type reads -/
  reads : ∀ φ, InferReadsJ J m φ
  /-- an accepted subject's inferred type keeps its frame -/
  frame : ∀ φ, InferFrameJ J m φ

/-- **The kernel's runs keep scoping** at a well-formed environment. -/
theorem judgeFrames_runJ {μ : CheckMode} {env : Env md} (hwf : EnvWF env) (F : Nat) :
    JudgeFrames (runJ μ F) env where
  annot_syntax := fun hann hf hb => annotate_syntax hann hf hb
  annot_wscoped := fun hann hw => annotateCore_WScoped F _ hann hw
  annot_bounded := fun hann hb => annotateCore_looseBVars F _ hann hb
  annot_leaves := fun hann hw hb => annotateCore_leaves_sub F _ hann hw hb

/-- The kernel's runs keep the inferred type's frame unconditionally. -/
theorem inferFrame_runJ {μ : CheckMode} {env : Env md} (hwf : EnvWF env) (F : Nat)
    (m : EnvModel V env) (φ : LevelParam → Nat) : InferFrameJ (runJ μ F) m φ := by
  intro d e t Δa ea h hw hb hL _ _
  exact ⟨inferTypeCore_WScoped hwf F h hw, inferTypeCore_looseBVars hwf F h hw hb hL,
    inferTypeCore_fvarLeaves hwf F h hw⟩

/-- **The kernel's instance**: the runs at fuel `F` satisfy the package, at the
fold's invariant. -/
theorem judgeSound_runJ {μ : CheckMode} (hμ : μ.verifiedChecks = true) {env : Env md}
    (mp : EnvModelM V μ env) (F : Nat) : JudgeSound (runJ μ F) mp.base2 where
  toJudgeFrames := judgeFrames_runJ mp.base2.wf F
  accepted := fun φ _ _ _ h hws hb hL => acceptedReads_of mp.base2 φ h hws hb hL
  infer := fun φ => (checkSoundAt hμ (Rules.RulesInputs.ofSem mp φ) F).2.2.2
  defeq := fun φ => (checkSoundAt hμ (Rules.RulesInputs.ofSem mp φ) F).2.2.1
  reads := fun φ => inferReads_of hμ (Rules.RulesInputs.ofSem mp φ)
  frame := inferFrame_runJ mp.base2.wf F mp.base2

end Ix.Kernel.Model
