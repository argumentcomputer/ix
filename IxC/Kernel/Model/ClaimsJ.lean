module

public import IxC.Kernel.Model.Claims
public import IxC.Kernel.Model.Annot.EnvModel
public import IxC.Kernel.Model.Annot.Valid
public import IxC.Kernel.Semantics.DeclJ

public section

/-!
# The claims over a judgement package (lane l5)

`InferClaim`, `DefEqClaim` (`Model/Claims.lean`) and `InferReads`
(`Model/Tiers.lean`) with the checker's run replaced by a judgement package's
relation (`Semantics/DeclJ.lean`). At the kernel's runs (`runJ μ F`) each is the
original by `rfl`. Kept below `Model/Tiers.lean` so that the installs the
harvests call (`natOps_install`) can be stated over them.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key)

universe w

variable {V : Type w} [SetTheory V]

/-- `InferClaim` over a package's inference relation. -/
@[expose] def InferClaimJ (J : Judgements md) {env : Env md} (m : EnvModel V env)
    (φ : LevelParam → Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr md} {Δa : List AnnotTerm},
    J.infer env d e t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    ∀ {ea ta : AnnotTerm},
      CtxOk m φ d Δa e →
      denoteMeta m.acval env φ d e = some ea →
      denoteMeta m.acval env φ d t = some ta →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) ∧
        (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta) ∧
        ∀ ρ : Nat → V, Sat V Δa ρ →
          interp V ρ ea ∈ˢ interp V ρ ta

/-- `DefEqClaim` over a package's conversion relation. -/
@[expose] def DefEqClaimJ (J : Judgements md) {env : Env md} (m : EnvModel V env)
    (φ : LevelParam → Nat) : Prop :=
  ∀ {d : Nat} {a b : Expr md} {Δa : List AnnotTerm},
    J.defeq env d a b →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    ∀ {aa ba : AnnotTerm},
      CtxOk m φ d Δa a →
      CtxOk m φ d Δa b →
      denoteMeta m.acval env φ d a = some aa →
      denoteMeta m.acval env φ d b = some ba →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa) →
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba) →
      ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ aa = interp V ρ ba

/-- `InferReads` over a package's inference relation. -/
@[expose] def InferReadsJ (J : Judgements md) {env : Env md} (m : EnvModel V env)
    (φ : LevelParam → Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr md} {Δa : List AnnotTerm} {ea : AnnotTerm},
    J.infer env d e t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m φ d Δa e →
    denoteMeta m.acval env φ d e = some ea →
    ∃ ta, denoteMeta m.acval env φ d t = some ta

/-- **The scoping a package's outputs keep** (model-free): an annotation keeps its
input's scope, bound and leaves (an inferred type's frame is `InferFrameJ`). The kernel's
runs satisfy it at a well-formed environment (`judgeFrames_runJ`,
`Model/JudgeSound.lean`). -/
structure JudgeFrames (J : Judgements md) (env : Env md) : Prop where
  /-- an annotation of a closed, bounded term is closed and bounded -/
  annot_syntax : ∀ {e e' : Expr md}, J.annot env 0 e e' →
    e.hasFvar = false → e.looseBVarsBounded 0 = true →
    e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true
  annot_wscoped : ∀ {d : Nat} {e e' : Expr md}, J.annot env d e e' →
    Expr.WScoped d e → Expr.WScoped d e'
  annot_bounded : ∀ {d : Nat} {e e' : Expr md}, J.annot env d e e' →
    e.looseBVarsBounded 0 = true → e'.looseBVarsBounded 0 = true
  annot_leaves : ∀ {d : Nat} {e e' : Expr md}, J.annot env d e e' →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    ∀ l ∈ e'.fvarLeaves, l ∈ e.fvarLeaves

/-- **An accepted subject's inferred type keeps its frame**, where the subject
reads (the kernel's runs keep it unconditionally, `inferTypeCore_WScoped` and
its siblings; a derivation keeps it by its soundness motive, `InferSemFull`). -/
@[expose] def InferFrameJ (J : Judgements md) {env : Env md} (m : EnvModel V env)
    (φ : LevelParam → Nat) : Prop :=
  ∀ {d : Nat} {e t : Expr md} {Δa : List AnnotTerm} {ea : AnnotTerm},
    J.infer env d e t →
    Expr.WScoped d e → e.looseBVarsBounded 0 = true →
    Expr.LeavesBounded e →
    CtxOk m φ d Δa e →
    denoteMeta m.acval env φ d e = some ea →
    Expr.WScoped d t ∧ t.looseBVarsBounded 0 = true ∧
      ∀ l ∈ t.fvarLeaves, l ∈ e.fvarLeaves

end Ix.Kernel.Model
