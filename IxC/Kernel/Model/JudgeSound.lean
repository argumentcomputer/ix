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

/-- **What the harvests need of a judgement package at a model.** -/
structure JudgeSound (J : Judgements md) {env : Env md} (m : EnvModel V env) : Prop where
  /-- an annotation of a closed, bounded term is closed and bounded -/
  annot_syntax : ∀ {e e' : Expr md}, J.annot env 0 e e' →
    e.hasFvar = false → e.looseBVarsBounded 0 = true →
    e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true
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
  /-- the inferred type's scoping -/
  wscoped : ∀ {d : Nat} {e t : Expr md}, J.infer env d e t → Expr.WScoped d e → Expr.WScoped d t
  bounded : ∀ {d : Nat} {e t : Expr md}, J.infer env d e t → Expr.WScoped d e →
    e.looseBVarsBounded 0 = true → Expr.LeavesBounded e → t.looseBVarsBounded 0 = true
  leaves : ∀ {d : Nat} {e t : Expr md}, J.infer env d e t → Expr.WScoped d e →
    ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves

/-- **The kernel's instance**: the runs at fuel `F` satisfy the package, at the
fold's invariant. -/
theorem judgeSound_runJ {μ : CheckMode} (hμ : μ.verifiedChecks = true) {env : Env md}
    (mp : EnvModelM V μ env) (F : Nat) : JudgeSound (runJ μ F) mp.base2 where
  annot_syntax := fun hann hf hb => annotate_syntax hann hf hb
  accepted := fun φ _ _ _ h hws hb hL => acceptedReads_of mp.base2 φ h hws hb hL
  infer := fun φ => (checkSoundAt hμ (Rules.RulesInputs.ofSem mp φ) F).2.2.2
  defeq := fun φ => (checkSoundAt hμ (Rules.RulesInputs.ofSem mp φ) F).2.2.1
  reads := fun φ => inferReads_of hμ (Rules.RulesInputs.ofSem mp φ)
  wscoped := fun h hw => inferTypeCore_WScoped mp.base2.wf F h hw
  bounded := fun h hw hb hL => inferTypeCore_looseBVars mp.base2.wf F h hw hb hL
  leaves := fun h hw => inferTypeCore_fvarLeaves mp.base2.wf F h hw

end Ix.Kernel.Model
