import IxVMRefinement.Decl.ModeledLevels
import IxVMRefinement.Decl.NativeEnv
import IxVMRefinement.Decl.NativeRunMap
import IxVMRefinement.Infer.Close

/-! # Positional typing for native declaration stages

The native model also reads structural inference inversions. Positional evidence therefore
retains the level scope of stored types, which is available from the actual store invariant.
No rule is assumed closed under arbitrary universe substitution.
-/

universe u

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Ix.Kernel.Rules (Infer Red)
open Core (KExpr KKey posOf posLevels)

/-- Stored types mention only their declared universe parameters. -/
def StoredTypeLevels (env : Env .anon) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ci.toConstantVal.type.allLevelParamsDefined ci.toConstantVal.levelParams = true

theorem StoredTypeLevels.of_store {env : Env .anon} (h : Open.StoreInv env) :
    StoredTypeLevels env :=
  fun _ ci hf => (h.wf ci (Ix.Kernel.Semantics.Env.find?_mem hf)).2.1

/-- Raw inference remains available. Positional inference records the stored type scope needed
to invert constant-headed spines in the native model. Other relations reuse `posRulesJ`. -/
def nativePosRulesJ : Judgements .anon :=
  { posRulesJ with
    infer := fun env d e t => Infer env .full d e t ∨
      (StoredTypeLevels env ∧ posRulesJ.infer env d e t) }

private theorem raw_infer_pos {env : Env .anon} {d : Nat} {e t : KExpr}
    (h : Infer env .full d e t) : posRulesJ.infer env d e t :=
  ⟨[], .nil, by rw [show posOf [] e = e from posOf_range 0 e,
    show posOf [] t = t from posOf_range 0 t]; exact h⟩

/-- The guarded native package is interpreted by the already certified positional package. -/
def nativePosToPos : JudgementsMap nativePosRulesJ posRulesJ where
  annot := id
  infer := fun h => h.elim raw_infer_pos And.right
  defeq := id
  sort := id
  isZero := id

/-- Existing raw certificates embed without changing any expression or environment. -/
def rulesToNativePos : JudgementsMap rulesJ nativePosRulesJ where
  annot := id
  infer := Or.inl
  defeq := by
    intro env d a b h
    exact ⟨[], .nil, by rw [show posOf [] a = a from posOf_range 0 a,
      show posOf [] b = b from posOf_range 0 b]; exact h⟩
  sort := by
    intro env d t level h
    refine ⟨[], .nil, ?_⟩
    have hu : Level.subst [] (posLevels []) level = level :=
      Expr.sort.inj (posOf_range 0 (.sort level))
    rw [show posOf [] t = t from posOf_range 0 t, hu]
    exact h
  isZero := id

theorem judgeFrames_nativePosRulesJ (env : Env .anon) : JudgeFrames nativePosRulesJ env :=
  judgeFrames_posRulesJ env

/-- Native positional typing has the same semantic interpretation as the certified package. -/
theorem judgeSound_nativePosRulesJ_of {V : Type u} [SetTheory V]
    {mode : CheckMode} {env : Env .anon} (m : EnvModelM V mode env) :
    JudgeSound nativePosRulesJ m.base2 where
  toJudgeFrames := judgeFrames_nativePosRulesJ env
  accepted := by
    intro φ d e t hi
    exact (judgeSound_posRulesJ_of m).accepted φ (nativePosToPos.infer hi)
  infer := by
    intro φ d e t Δa hi
    exact (judgeSound_posRulesJ_of m).infer φ (nativePosToPos.infer hi)
  defeq := (judgeSound_posRulesJ_of m).defeq
  reads := by
    intro φ d e t Δa ea hi
    exact (judgeSound_posRulesJ_of m).reads φ (nativePosToPos.infer hi)
  frame := by
    intro φ d e t Δa ea hi
    exact (judgeSound_posRulesJ_of m).frame φ (nativePosToPos.infer hi)

/-- The positional sort certificate denotes the stated universe even when inference and
reduction use different permutations. -/
theorem sortClaim_nativePosRulesJ_of {V : Type u} [SetTheory V]
    {mode : CheckMode} {env : Env .anon} (m : EnvModelM V mode env) (φ : LevelParam → Nat) :
    SortClaimJ nativePosRulesJ m.base2 φ := by
  intro d e t level Δa ea hi hs hws hb hL hC hea
  have sound := judgeSound_nativePosRulesJ_of m
  obtain ⟨ta, hta⟩ := sound.reads φ hi hws hb hL hC hea
  obtain ⟨hwt, hbt, hsub⟩ := sound.frame φ hi hws hb hL hC hea
  obtain ⟨hgE, hgT, hmem⟩ := sound.infer φ hi hws hb hL hC hea hta
  have hLt : Expr.LeavesBounded t := fun l hl => hL l (hsub l hl)
  obtain ⟨ps, hp, hr⟩ := hs
  have hwtp := (wscoped_instantiateLevelParams ps (posLevels ps) t d).mpr hwt
  have hbtp : (posOf ps t).looseBVarsBounded 0 = true := by
    rw [posOf, Expr.looseBVarsBounded_instantiateLevelParams]; exact hbt
  have hLtp := (leavesBounded_instantiateLevelParams ps (posLevels ps) t).mpr hLt
  have hCp := ctxOk_posOf hp (hC.of_subset hsub)
  have htap : denoteMeta m.base2.acval env (posVal ps φ) d (posOf ps t) = some ta := by
    rw [denoteMeta_posOf m.base2 hp]; exact hta
  have red := Rules.red_sound (fun ψ => Rules.RulesInputs.ofSem m ψ) hr
  obtain ⟨_, _, sa, hsa, _, heq⟩ := red ⟨hwtp, hbtp, hLtp⟩ hCp htap hgT
  rw [denoteMeta_sortQ] at hsa
  obtain rfl := Option.some.inj hsa
  intro ρ hρ
  refine ⟨hgE ρ hρ, ?_⟩
  have hm := hmem ρ hρ
  rw [heq ρ hρ, interp_sort, Level.eval_subst, substFn_posVal hp] at hm
  exact hm

end IxVM.Refinement.Decl
