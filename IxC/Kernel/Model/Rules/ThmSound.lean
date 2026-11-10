module

public import IxC.Kernel.Model.Rules.Inputs
import IxC.Kernel.Model.Rules.Reads
import IxC.Kernel.Model.CtxOkKit
import IxC.Kernel.Model.Annot.BitInst
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Leaves

public section

/-!
# The theorem-unfolding rule is sound

`Red.deltaThm` replaces a theorem constant by its stored value. The model keeps
no equation between a theorem's leaf and its value's reading, so the rule
carries the facts its soundness reads instead of a model input: the value has
the theorem's type and that type is a proposition at every assignment. Then the
constant (a member of its type by `ConstType`) and the value (a member by its
inference) are members of one truth value, hence both the one proof `pt`
(`mem_univ_zero`). The reduct is closed, reads (`infer_reads`) and is graded (its
inference).

This keeps the kernel's own rules inputs (`RulesInputs.ofEnvModelM`) as they are:
the kernel stores a theorem's raw value, which need not read, so it could not
supply a model input equating a theorem's value with its leaf.
-/

namespace Ix.Kernel.Model.Rules
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (Env Expr Key ConstantVal ConstantInfo)
open Ix.Kernel.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {m : EnvModel V env}
  {φ : LevelParam → Nat}

/-- **`Red.deltaThm` is sound.** -/
theorem Red.deltaThm_sound (hin : RulesInputs V m φ) {d : Nat} {n : Key md}
    {us : List Level} {cv : ConstantVal md} {value vt s : Expr md} {u : Level}
    (hf : env.find? n = some (.thmInfo cv value))
    (hlen : us.length = cv.levelParams.length)
    (hvf : value.hasFvar = false) (hvb : value.looseBVarsBounded 0 = true)
    (hinf : Infer env .full d (value.instantiateLevelParams cv.levelParams us) vt)
    (sinf : InferSemFull m φ d (value.instantiateLevelParams cv.levelParams us) vt)
    (sde : DefEqSem m φ d vt (cv.type.instantiateLevelParams cv.levelParams us))
    (sinfT : InferSemFull m φ d (cv.type.instantiateLevelParams cv.levelParams us) s)
    (sred : RedSem m φ d s (.sort u)) (hz : ∀ φ : LevelParam → Nat, Level.eval φ u = 0) :
    RedSem m φ d (.const n us) (value.instantiateLevelParams cv.levelParams us) := by
  intro _ Δa ea hC hea _
  -- the subject reads to the theorem's leaf
  rw [denoteMeta, hf] at hea
  dsimp only at hea
  rw [if_pos (show us.length = (ConstantInfo.thmInfo cv value).toConstantVal.levelParams.length
    from hlen)] at hea
  obtain rfl : ea = m.acval n (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hea).symm
  -- the reduct is closed, reads and is graded
  have hnf : (value.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hvf
  have hnl := Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf
  have hfv : Frame d (value.instantiateLevelParams cv.levelParams us) :=
    ⟨Expr.WScoped.of_not_hasFvar hnf,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hvb,
      Expr.LeavesBounded.of_not_hasFvar hnf⟩
  have hCv : CtxOk m φ d Δa (value.instantiateLevelParams cv.levelParams us) :=
    hC.of_subset (fun l hl => by rw [hnl] at hl; cases hl)
  obtain ⟨va, hva⟩ := Ix.Kernel.Model.infer_reads m φ hinf rfl hfv.1 hfv.2.1 hfv.2.2
  obtain ⟨hfvt, hsubvt, vta, hvta, hgV, hgVT, hmemV⟩ := sinf hfv hCv hva
  have hCvt : CtxOk m φ d Δa vt := hCv.of_subset hsubvt
  -- the theorem's type reads, closed, with the constant a member
  obtain ⟨ta, hta, hokT, hmemC⟩ := hin.const_ty d n _ us hf rfl hlen
  obtain ⟨htc, -, -, htb, -⟩ := m.wf _ (Env.find?_mem hf)
  have hnT : (cv.type.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact htc
  have hfT : Frame d (cv.type.instantiateLevelParams cv.levelParams us) :=
    ⟨Expr.WScoped.of_not_hasFvar hnT,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact htb,
      Expr.LeavesBounded.of_not_hasFvar hnT⟩
  have hCT : CtxOk m φ d Δa (cv.type.instantiateLevelParams cv.levelParams us) :=
    hC.of_subset (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnT] at hl; cases hl)
  have hgT : Graded V Δa ta := fun ρ _ => hokT ρ
  -- the value's type is the theorem's
  have heqT := sde hfvt hfT hCvt hCT hvta hta hgVT hgT
  -- the theorem's type is a proposition
  obtain ⟨hfs, hsubs, sta, hsta, -, hgS, hmemT⟩ := sinfT hfT hCT hta
  have hCs : CtxOk m φ d Δa s := hCT.of_subset hsubs
  obtain ⟨-, -, sa, hsa, -, heqS⟩ := sred hfs hCs hsta hgS
  rw [denoteMeta_sort] at hsa
  obtain rfl : sa = AnnotTerm.sort (u.eval φ) := (Option.some.inj hsa).symm
  refine ⟨hfv, (fun l hl => by rw [hnl] at hl; cases hl), va, hva, hgV, fun ρ hρ => ?_⟩
  have hT0 := hmemT ρ hρ
  rw [heqS ρ hρ, interp_sort, hz φ] at hT0
  have h1 : interp V ρ va ∈ˢ interp V ρ ta := heqT ρ hρ ▸ hmemV ρ hρ
  exact (mem_univ_zero hT0 (hmemC ρ)).trans (mem_univ_zero hT0 h1).symm

end Ix.Kernel.Model.Rules
