import Ix.LeanIngress.Theorems

/-! # Source mode at the pinned bundle evidence (owner, 2026-10-20)

`SourceAccepts` runs `Ix.LeanIngress.checkSourceBundled`: the committed prelude and
the committed bundle's evidence (`Ix.RoleEvidence.bundleEvidence`), whatever the
input carries. These are its readings, from the explicit-evidence entry's
(`checkSourceWith_reading`): the ingress succeeded, the fold accepted at the bundle
evidence, at the reference level too; no proof of `False`; and every group of the
environment converted. Each is stated over a source of preludes first, so that no
proof unfolds the committed prelude's data. -/

namespace Ix.LeanIngress

universe u

theorem checkSourceBundledUsing_with {prelude : Except String (Ix.Kernel.Reader.Prelude .source)}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source}
    (h : checkSourceBundledUsing prelude env blocks = .ok kenv) :
    ∃ pre, prelude = .ok pre ∧ checkSourceWith pre (Ix.RoleEvidence.bundleEvidence ()) env blocks = .ok kenv := by
  unfold checkSourceBundledUsing at h
  cases hp : prelude with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pre =>
    simp only [hp, Except.mapError, bind, Except.bind] at h
    exact ⟨pre, rfl, h⟩

/-- **The bundled check is the explicit-evidence check** at the committed prelude
and the bundle's evidence. -/
theorem checkSourceBundled_with {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (h : checkSourceBundled env blocks = .ok kenv) :
    ∃ pre, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      checkSourceWith pre (Ix.RoleEvidence.bundleEvidence ()) env blocks = .ok kenv :=
  checkSourceBundledUsing_with h

/-- **The reading of an accepted bundled check**: the committed prelude, the
ingress's declarations behind it, and the fold's acceptance of them at the
bundle's evidence. -/
theorem checkSourceBundled_reading {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (h : checkSourceBundled env blocks = .ok kenv) :
    ∃ pre decls, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.checkDecls .verified (Ix.RoleEvidence.bundleEvidence ())
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) = .ok kenv := by
  obtain ⟨pre, hp, hw⟩ := checkSourceBundled_with h
  obtain ⟨decls, hi, hc⟩ := checkSourceWith_reading hw
  exact ⟨pre, decls, hp, hi, hc⟩

/-- **An accepted bundled check is a reference accept** (step 7,
`Ix.Kernel.Cached.checkDecls_refines_ref`). -/
theorem checkSourceBundled_refines_ref (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source} (h : checkSourceBundled env blocks = .ok kenv) :
    ∃ pre decls, Ix.Kernel.Reader.builtinPrelude = .ok pre ∧
      leanIngress env blocks pre.state = .ok decls ∧
      Ix.Kernel.Cached.AcceptsRef .verified (Ix.RoleEvidence.bundleEvidence ())
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList kenv := by
  obtain ⟨pre, decls, hp, hi, hc⟩ := checkSourceBundled_reading h
  exact ⟨pre, decls, hp, hi, Ix.Kernel.Cached.checkDecls_refines_ref V rfl hc⟩

/-- **No proof of `False`** for the bundled check. -/
theorem checkSourceBundled_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V] {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {kenv : Ix.Kernel.Env .source} (h : checkSourceBundled env blocks = .ok kenv) :
    ∀ ci ∈ kenv.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, hw⟩ := checkSourceBundled_with h
  exact checkSourceWith_no_proof_of_False V hw

/-- **An accepted bundled check converted every group** of its environment. -/
theorem checkSourceBundled_converts {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {kenv : Ix.Kernel.Env .source} (h : checkSourceBundled env blocks = .ok kenv) :
    ∀ grp ∈ groupsOf env blocks, ∃ conv, convert grp = .ok conv := by
  obtain ⟨pre, decls, _, hi, _⟩ := checkSourceBundled_reading h
  intro grp hg
  obtain ⟨i, hlt, rfl⟩ := Array.getElem_of_mem hg
  have hi' : i < (graph env blocks).groups.size := by rw [graph_groups]; exact hlt
  obtain ⟨conv, hc⟩ := leanIngress_converts hi hi'
  have same : (graph env blocks).converted[i]! = convert (groupsOf env blocks)[i] := by
    rw [graph_converted]
    simp [hlt]
    rfl
  exact ⟨conv, same ▸ hc⟩

end Ix.LeanIngress
