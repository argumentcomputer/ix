import IxVMRefinement.Core.Rep
import IxVM.Obs.KernelCheck

/-! # Actual conversion evidence for the alias former telescope

The program checks the built telescope's scoping and typing, then its conversion with the
declared former. The observations below produce the interface consumed by the alias stages.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- The actual telescope-check paths, including the asserted conversion event. -/
def FormerTeleConv : Prop :=
  ∀ (rc ty k nl s : SourceValue F) (h : Heap F) (r : SourceValue F) (h' : Heap F)
    (cs : List (Call F)),
    ObsFn Core.W "KernelCheck::former_tele_typed" [rc, ty, k, nl, s] h r h' cs →
    (∃ (m2 : Heap F) (cs13 : List (Call F)),
      ObsFn Core.W "KernelCheck::former_is_tele" [ty, k] h (.field 1) m2 cs13 ∧
      r = .tuple [] ∧ h' = m2 ∧ cs = (⟨"KernelCheck::former_is_tele", [ty, k], h⟩ : Call F) :: cs13) ∨
    (∃ (v1 : SourceValue F) (m2 : Heap F) (cs13 : List (Call F)) (tele : SourceValue F)
        (m46 : Heap F) (cs56 : List (Call F)) (v105 : SourceValue F) (m106 : Heap F)
        (cs116 : List (Call F)) (v142 : SourceValue F) (m143 : Heap F) (cs153 : List (Call F))
        (mD : Heap F) (csD : List (Call F)),
      ObsFn Core.W "KernelCheck::former_is_tele" [ty, k] h v1 m2 cs13 ∧ v1 ≠ .field 1 ∧
      ObsFn Core.W "KernelCheck::former_tele_at"
        [rc, ty, k, .ptr (.enum Core.kexprListEnum) m2.length, s]
        (m2 ++ [.construct Core.kexprListEnum "Nil" []]) tele m46 cs56 ∧
      ObsFn Core.W "KernelCheck::validate_expr_well_scoped" [tele, .field 0, nl]
        m46 v105 m106 cs116 ∧
      ObsFn Core.W "KernelInfer::k_ensure_sort"
        [rc, tele, .ptr (.enum Core.kexprListEnum) m106.length]
        (m106 ++ [.construct Core.kexprListEnum "Nil" []]) v142 m143 cs153 ∧
      ObsFn Core.W "KernelDefEq::k_is_def_eq"
        [rc, ty, tele, .ptr (.enum Core.kexprListEnum) m143.length]
        (m143 ++ [.construct Core.kexprListEnum "Nil" []]) (.field 1) mD csD ∧
      r = .tuple [] ∧ h' = mD ∧
      cs = (⟨"KernelCheck::former_is_tele", [ty, k], h⟩ : Call F) :: (cs13 ++
        ((⟨"KernelCheck::former_tele_at", [rc, ty, k, .ptr (.enum Core.kexprListEnum) m2.length, s],
            m2 ++ [.construct Core.kexprListEnum "Nil" []]⟩ : Call F) :: (cs56 ++
        ((⟨"KernelCheck::validate_expr_well_scoped", [tele, .field 0, nl], m46⟩ : Call F) ::
          (cs116 ++
        ((⟨"KernelInfer::k_ensure_sort", [rc, tele, .ptr (.enum Core.kexprListEnum) m106.length],
            m106 ++ [.construct Core.kexprListEnum "Nil" []]⟩ : Call F) :: (cs153 ++
        ((⟨"KernelDefEq::k_is_def_eq",
            [rc, ty, tele, .ptr (.enum Core.kexprListEnum) m143.length],
            m143 ++ [.construct Core.kexprListEnum "Nil" []]⟩ : Call F) :: csD)))))))))

/-- The current program discharges the conversion-event interface. -/
theorem formerTeleConv_of_program : FormerTeleConv := by
  intro rc ty k nl s h r h' cs ev
  match Obs.«KernelCheck::former_tele_typed».obs ev with
  | .n1 (m2 := m2) (cs13 := cs13) (ev15 := test) (he38 := hr) (he39 := hh) (hc40 := hc) =>
    exact Or.inl ⟨m2, cs13, test, hr, hh, hc⟩
  | .other (v1 := v1) (m2 := m2) (cs13 := cs13) (v45 := tele) (m46 := m46) (cs56 := cs56)
      (m86 := m86) (v105 := v105) (m106 := m106) (cs116 := cs116) (v142 := v142)
      (m143 := m143) (cs153 := cs153) (m174 := m174) (v186 := result) (m187 := final)
      (cs197 := convCalls) (m226 := m226) (ev15 := test) (hne41 := hn)
      (hm94 := nil1) (ev58 := build) (ev118 := scope) (hm182 := nil2) (ev155 := typed)
      (hm234 := nil3) (ev199 := conv) (heq264 := one) (he267 := hr) (he268 := hh)
      (hc269 := hc) =>
    subst m86 m174 m226 result
    exact Or.inr ⟨v1, m2, cs13, tele, m46, cs56, v105, m106, cs116, v142, m143, cs153,
      final, convCalls, test, hn, build, scope, typed, conv, hr, hh, hc⟩

end IxVM.Refinement.Typing
