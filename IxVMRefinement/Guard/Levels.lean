import IxC.Kernel.Model.GuardSignature
import IxVMRefinement.Nat.Levels
import IxVMRefinement.Obs.KernelGuard

/-! # Functional refinement of the projection guard's zero-signature computation

These theorems concern the registered KernelGuard functions in the current observed world.
They are data specifications: no typed environment, role context or validation limit is needed.
-/

namespace IxVM.Refinement.Guard

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Core
open Core.LevelsAux
open KernelLevels
open Ix.Kernel (Level)

set_option maxHeartbeats 4000000

macro "guard_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

private theorem stored_one (h : Heap F) :
    RepKLevel ((h ++ [.construct KernelLevels.klevelEnum "Zero" []]) ++
      [.construct KernelLevels.klevelEnum "Succ" [.ptr (.enum KernelLevels.klevelEnum) h.length]])
      (.succ .zero) (.ptr (.enum KernelLevels.klevelEnum) ((h ++ [.construct KernelLevels.klevelEnum "Zero" []]) : Heap F).length) :=
  .succ List.getElem?_concat_length
    ((RepKLevel.zero List.getElem?_concat_length).mono (Heap.Extends.snoc _ _))

private theorem flags_add_zero {a b : Bool}
    (h : evalBinOp .add (.field (if a then 1 else 0) : SourceValue F)
      (.field (if b then 1 else 0)) = .ok (.field 0)) : a = false ∧ b = false := by
  have htwo : (1 : F) + 1 ≠ 0 := by decide +kernel
  cases a <;> cases b <;> simp_all [evalBinOp]


theorem signature_pair_spec_aux :
    ∀ (name : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W name args h r h' cs →
      name = "KernelGuard::signature_pair" →
      ∀ (l : Level) (p : SourceValue F), args = [p] → RepKLevel h l p →
        ∃ sp, r = .tuple [.field (if (Level.guardSignature l).isNone then 1 else 0), sp] ∧
          RepKLevel h' (Level.guardSignatureLevel l) sp :=
  ObsFn.strong_induction (world := W)
    (fun name args h r h' cs => name = "KernelGuard::signature_pair" →
      ∀ (l : Level) (p : SourceValue F), args = [p] → RepKLevel h l p →
        ∃ sp, r = .tuple [.field (if (Level.guardSignature l).isNone then 1 else 0), sp] ∧
          RepKLevel h' (Level.guardSignatureLevel l) sp)
    (fun name args h r h' cs ev ih hn l p hargs hrep => by
      subst hn hargs
      rcases Obs.«KernelGuard::signature_pair».obs ev with
        ⟨ld, hr, hh, hcs⟩ |
        ⟨x, ld, hr, hh, hcs⟩ |
        ⟨x, m0, m1, ld, hr, hm0, hm1, hh, hcs⟩ |
        ⟨x, b, csb, ld, evb, hcs⟩ |
        ⟨a, b, m0, csa, na, sa, m1, csb, nb, sb, m2, ld, eva, evb, hop, hr, hm, hh, hcs⟩ |
        ⟨a, b, m0, csa, na, sa, m1, csb, nb, sb, sum, m2, m3, ld, eva, evb, hop, hne,
          hr, hm2, hm3, hh, hcs⟩
      · obtain rfl := zero_of_load hrep ld
        subst hr hh
        exact ⟨_, rfl, hrep⟩
      · obtain ⟨k, rfl, _, _⟩ := param_of_load hrep ld
        subst hr hh
        exact ⟨_, rfl, hrep⟩
      · obtain ⟨u, rfl, _⟩ := succ_of_load hrep ld
        subst hr hh hm0 hm1
        exact ⟨_, rfl, stored_one h⟩
      · obtain ⟨u, v, rfl, _, hv⟩ := imax_of_load hrep ld
        subst hcs
        exact ih _ _ _ _ _ _ (by guard_lt_calls) evb rfl v b rfl hv
      · obtain ⟨u, v, rfl, hu, hv⟩ := max_of_load hrep ld
        subst hcs
        obtain ⟨spa, hra, hsa⟩ := ih _ _ _ _ _ _ (by guard_lt_calls) eva rfl u a rfl hu
        obtain ⟨rfl, rfl⟩ := pair_inj hra
        obtain ⟨spb, hrb, hsb⟩ := ih _ _ _ _ _ _ (by guard_lt_calls) evb rfl v b rfl
          (hv.mono eva.heap_extends)
        obtain ⟨rfl, rfl⟩ := pair_inj hrb
        subst hr hh hm
        have hab := flags_add_zero hop
        cases hgu : Level.guardSignature u with
        | none => simp [hgu] at hab
        | some su =>
          cases hgv : Level.guardSignature v with
          | none => simp [hgv] at hab
          | some sv =>
            refine ⟨.ptr (.enum KernelLevels.klevelEnum) m1.length, ?_, ?_⟩
            · simp [Level.guardSignature, hgu, hgv]
            · have haRep : RepKLevel m0 su _ := by simpa [Level.guardSignatureLevel, hgu] using hsa
              have hbRep : RepKLevel m1 sv _ := by simpa [Level.guardSignatureLevel, hgv] using hsb
              simpa [Level.guardSignatureLevel, Level.guardSignature, hgu, hgv] using
                (RepKLevel.max List.getElem?_concat_length
                  (haRep.mono (evb.heap_extends.trans (Heap.Extends.snoc _ _)))
                  (hbRep.mono (Heap.Extends.snoc _ _)))
      · obtain ⟨u, v, rfl, hu, hv⟩ := max_of_load hrep ld
        subst hcs
        obtain ⟨spa, hra, hsa⟩ := ih _ _ _ _ _ _ (by guard_lt_calls) eva rfl u a rfl hu
        obtain ⟨rfl, rfl⟩ := pair_inj hra
        obtain ⟨spb, hrb, hsb⟩ := ih _ _ _ _ _ _ (by guard_lt_calls) evb rfl v b rfl
          (hv.mono eva.heap_extends)
        obtain ⟨rfl, rfl⟩ := pair_inj hrb
        subst hr hh hm2 hm3
        have hnone : Level.guardSignature (.max u v) = none := by
          cases hgu : Level.guardSignature u <;> cases hgv : Level.guardSignature v
          all_goals try solve | simp [Level.guardSignature, hgu, hgv]
          simp [hgu, hgv, evalBinOp] at hop
          subst sum
          exact (hne rfl).elim
        refine ⟨.ptr (.enum KernelLevels.klevelEnum)
          ((m1 ++ [.construct KernelLevels.klevelEnum "Zero" []]) : Heap F).length, ?_, ?_⟩
        · simp [hnone]
        · simpa [Level.guardSignatureLevel, hnone] using stored_one m1)

/-- The actual signature function returns precisely the signature level of its input. -/
theorem signature_level_spec {l : Level} {p r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hrep : RepKLevel h l p)
    (ev : ObsFn W "KernelGuard::signature_level" [p] h r h' cs) :
    RepKLevel h' (Level.guardSignatureLevel l) r := by
  obtain ⟨m, cs', flag, sp, evp, hr, hh, _⟩ := Obs.«KernelGuard::signature_level».obs ev
  obtain ⟨sp', heq, hsp⟩ := signature_pair_spec_aux _ _ _ _ _ _ evp rfl l p rfl hrep
  obtain ⟨_, hsp'⟩ := pair_inj heq
  subst hsp' hr hh
  exact hsp

end IxVM.Refinement.Guard
