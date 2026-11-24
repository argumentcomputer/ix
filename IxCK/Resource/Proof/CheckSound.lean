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

/-- **Mode-checker soundness (`CheckSound`)**: for any `KernelRead` guaranteeing that
role-bound primitives are disjoint from inductives (`RolesDisjointFromInductives`),
whenever `IxCK.Resource.check` accepts a subject, the subject is `ModeSafe` at
`lim.oracle`. -/
theorem checkSound (KernelRead : Ix.Kernel.Env .anon → Subject → Prop)
    (hroles : ∀ env s, KernelRead env s → RolesDisjointFromInductives s) :
    CheckSound KernelRead := by
  intro lim env s n fp hkr hchk
  obtain ⟨P, hReads, hModeOk⟩ := check_sound_modeOk (hroles env s hkr) hchk
  refine ⟨⟨P, hReads⟩, fun P' hReads' _ _ r _ params res rc rs t hfind ext hext h args hinp fuel k => ?_⟩
  have hEq : P' = P := by
    unfold Reads at hReads hReads'
    rw [hReads] at hReads'
    exact Except.ok.inj hReads'.symm
  subst hEq
  exact f4 P' hModeOk r params res rc rs t hfind ext hext h args hinp fuel k

end IxCK.Resource.Proof
