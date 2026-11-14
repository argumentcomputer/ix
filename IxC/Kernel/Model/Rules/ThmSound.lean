module

public import IxC.Kernel.Model.Rules.Inputs
import IxC.Kernel.Model.Rules.Reads
import IxC.Kernel.Model.Rules.IotaSoundKit
import IxC.Kernel.Model.CtxOkKit
import IxC.Kernel.Model.Annot.BitInst
import IxC.Kernel.Model.Annot.BitLevels
import IxC.Kernel.Model.Annot.BitClosed
import IxC.Kernel.Verify.InstLevels
import IxC.Kernel.Verify.Leaves

public section

/-!
# The theorem-unfolding rule is sound

`Red.deltaThm` replaces a theorem constant `n.{us}` by its stored value at the use's
levels. The model keeps no equation between a theorem's leaf and its value's reading,
so the rule carries the theorem's own check instead of a model input: at the theorem's
level parameters and in the empty context, the value has the theorem's type and that
type is a proposition at every assignment.

Read at `φ' = Level.substFn φ cv.levelParams us`, the assignment the use's levels
induce, the check says that the value reads and is a member of the type's reading, and
that the type's reading is a truth value. The constant (a member of its type by
`ConstType`) and the value are then both its one proof (`mem_univ_zero`). The reduct
reads at `φ` as the value reads at `φ'` (`denotePInstLevels`), at any depth since it is
closed (`denoteMeta_depth_of_closed`).

The premises' soundness is used at `φ'`, not at the conclusion's `φ`, so the master
induction (`Sound.lean`) takes the inputs at every assignment.

This keeps the kernel's own rules inputs (`RulesInputs.ofEnvModelM`) as they are: the
kernel stores a theorem's raw value, which need not read, so it could not supply a model
input equating a theorem's value with its leaf.
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

/-- **`Red.deltaThm` is sound.** The premises' motives are read at the assignment the
use's levels induce. -/
theorem Red.deltaThm_sound (hin : RulesInputs V m φ) {d : Nat} {n : Key md}
    {us : List Level} {cv : ConstantVal md} {value vt s : Expr md} {u : Level}
    (hf : env.find? n = some (.thmInfo cv value))
    (hlen : us.length = cv.levelParams.length)
    (hvf : value.hasFvar = false) (hvb : value.looseBVarsBounded 0 = true)
    (hinf : Infer env .full 0 value vt)
    (sinf : InferSemFull m (Level.substFn φ cv.levelParams us) 0 value vt)
    (sde : DefEqSem m (Level.substFn φ cv.levelParams us) 0 vt cv.type)
    (sinfT : InferSemFull m (Level.substFn φ cv.levelParams us) 0 cv.type s)
    (sred : RedSem m (Level.substFn φ cv.levelParams us) 0 s (.sort u))
    (hz : ∀ φ : LevelParam → Nat, Level.eval φ u = 0) :
    RedSem m φ d (.const n us) (value.instantiateLevelParams cv.levelParams us) := by
  intro _ Δa ea hC hea _
  -- the subject reads to the theorem's leaf at the induced assignment
  rw [denoteMeta, hf] at hea
  dsimp only at hea
  rw [if_pos (show us.length = (ConstantInfo.thmInfo cv value).toConstantVal.levelParams.length
    from hlen)] at hea
  obtain rfl : ea = m.acval n (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hea).symm
  -- the value, closed, read in the empty context at the induced assignment
  obtain ⟨hfv, hCv⟩ := frame_of_not_hasFvar (m := m)
    (φ := Level.substFn φ cv.levelParams us) (d := 0) (Δa := []) hvf hvb rfl
  obtain ⟨va, hva⟩ := Ix.Kernel.Model.infer_reads m (Level.substFn φ cv.levelParams us)
    hinf rfl hfv.1 hfv.2.1 hfv.2.2
  obtain ⟨hfvt, hsubvt, vta, hvta, hgV, hgVT, hmemV⟩ := sinf hfv hCv hva
  have hCvt : CtxOk m (Level.substFn φ cv.levelParams us) 0 [] vt := hCv.of_subset hsubvt
  -- the theorem's type: closed, read at the induced assignment, the leaf a member
  obtain ⟨htc, -, -, htb, -⟩ := m.wf _ (Env.find?_mem hf)
  have hnT : cv.type.hasFvar = false := htc
  have hbT : cv.type.looseBVarsBounded 0 = true := htb
  obtain ⟨ta, hta, hokT, hmemC, -, -⟩ := constTy_pkg hin.const_ty hf rfl hlen
  have hta0 : denoteMeta m.acval env (Level.substFn φ cv.levelParams us) 0 cv.type
      = some ta := by
    rw [← denotePInstLevels m φ cv.levelParams us 0 cv.type]; exact hta 0
  obtain ⟨hfT, hCT⟩ := frame_of_not_hasFvar (m := m)
    (φ := Level.substFn φ cv.levelParams us) (d := 0) (Δa := []) hnT hbT rfl
  have hgT : Graded V [] ta := fun ρ _ => hokT ρ
  -- the value's type is the theorem's
  have heqT := sde hfvt hfT hCvt hCT hvta hta0 hgVT hgT
  -- the theorem's type is a proposition
  obtain ⟨hfs, hsubs, sta, hsta, -, hgS, hmemT⟩ := sinfT hfT hCT hta0
  have hCs : CtxOk m (Level.substFn φ cv.levelParams us) 0 [] s := hCT.of_subset hsubs
  obtain ⟨-, -, sa, hsa, -, heqS⟩ := sred hfs hCs hsta hgS
  rw [denoteMeta_sort] at hsa
  obtain rfl : sa = AnnotTerm.sort (u.eval (Level.substFn φ cv.levelParams us)) :=
    (Option.some.inj hsa).symm
  -- the reduct reads at `φ`, at every depth, as the value at the induced assignment
  have hnf : (value.instantiateLevelParams cv.levelParams us).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hvf
  have hnl := Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf
  have hfr : Frame d (value.instantiateLevelParams cv.levelParams us) :=
    ⟨Expr.WScoped.of_not_hasFvar hnf,
      by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hvb,
      Expr.LeavesBounded.of_not_hasFvar hnf⟩
  have hvaD : denoteMeta m.acval env φ d (value.instantiateLevelParams cv.levelParams us)
      = some va := by
    rw [denotePInstLevels m φ cv.levelParams us d value]
    exact denoteMeta_depth_of_closed m.acval_closed hvf
      (fun k => denoteMeta_closed m.acval_erase m.cval_closed hvf hvb hva 1 k) hva d
  refine ⟨hfr, (fun l hl => by rw [hnl] at hl; cases hl), va, hvaD,
    fun ρ _ => hgV ρ (Sat_nil V ρ), fun ρ _ => ?_⟩
  have hρ := Sat_nil V ρ
  have hT0 := hmemT ρ hρ
  rw [heqS ρ hρ, interp_sort, hz (Level.substFn φ cv.levelParams us)] at hT0
  have h1 : interp V ρ va ∈ˢ interp V ρ ta := heqT ρ hρ ▸ hmemV ρ hρ
  exact (mem_univ_zero hT0 (hmemC ρ)).trans (mem_univ_zero hT0 h1).symm

end Ix.Kernel.Model.Rules
