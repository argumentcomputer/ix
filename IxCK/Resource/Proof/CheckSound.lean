import IxCK.Resource.Proof.DefaultOk
import IxCK.Resource.Proof.F4
import IxCK.Resource.Proof.F5

/-!
# Mode-Checker Soundness (`CheckSound`)

Combines:
* `IxCK.Resource.Proof.defaultOk : DefaultOk` (fast path / all-default programs never violate),
* `IxCK.Resource.Proof.readsRespectErasure : ReadsRespectErasure` (supplied run behaviours
  never read an interface-erased position),
* `IxCK.Resource.Proof.check_sound_modeOk` (`check = .accept → ∃ P, Reads ∧ ModeOk P`), and
* `IxCK.Resource.Proof.f4 : ∀ P, ModeOk P → Safe P`

into the end-to-end soundness theorem `checkSound` matching `IxCK.Resource.CheckSound`.
-/

namespace IxCK.Resource.Proof

open IxCK.Resource Ixon

/-- **Mode-checker soundness (`CheckSound`)**: whenever `IxCK.Resource.check`
accepts a subject, its runtime `rolesDisjointOk` check establishes
`RolesDisjointFromInductives` and the subject is `ModeSafe` at `lim.oracle`. -/
theorem checkSound (KernelRead : Ix.Kernel.Env .anon → Subject → Prop) :
    CheckSound KernelRead := by
  intro lim env s n fp _hkr hchk
  obtain ⟨P, hReads, hModeOk⟩ := check_sound_modeOk hchk
  refine ⟨⟨P, hReads⟩, fun P' hReads' _ _ r _ params res rc rs t hfind ext hext h args hinp fuel k => ?_⟩
  have hEq : P' = P := by
    unfold Reads at hReads hReads'
    rw [hReads] at hReads'
    exact Except.ok.inj hReads'.symm
  subst hEq
  exact f4 P' hModeOk r params res rc rs t hfind ext hext h args hinp fuel k

end IxCK.Resource.Proof
