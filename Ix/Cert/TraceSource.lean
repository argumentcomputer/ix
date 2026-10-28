import Ix.Cert.TraceSegments
import Ix.Cert.DefinitionPremises

/-! # Quotient Source's side of the trace's segments

`TraceSegments.TraceNeeds` collects what the trace's segments need. This module proves the parts
that come from quotient Source's acceptance of its prepared stream.

* `kept_mem`: every declaration the trace keeps is in the prepared stream, which the checker
  accepted.
* `kept_levels` (`TraceNeeds.levels`): so a kept definition, theorem or opaque has distinct
  level positions (`DefinitionPremises.accepted_nodup`).
* `accepted_axiom`: an accepted axiom has distinct level positions, or is the pinned quotient
  soundness axiom's record and has one level parameter (its canonical comparison with the pin).
* `axiom_nodup` (`HeaderNeeds.nodup` for axioms): a kept axiom's level parameters are distinct. -/

namespace Ix.Cert.TraceSource

open Ix.Kernel Ix.Kernel.Reader
open Ix.Cert.TraceSegments (LoweredAt)
open Ix.LeanIngress (Converted Graph FiberMap)
open Ix.Cert.SourcePrelude (Scheduled)

/-! ## Kept declarations are accepted -/

/-- **Every declaration quotient Source's trace keeps is in the prepared stream.** -/
theorem kept_mem {pre : Prelude .source} {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {ℓ : Nat} {r : Read .source} (hr : rs[ℓ]? = some r) {d : Declaration .source} (hd : d ∈ r.decls.toList) :
    d ∈ ds.toList := by
  have hmem : d ∈ decls := by
    rw [← Array.mem_toList_iff, hflat]
    exact List.mem_flatMap.mpr ⟨r, List.mem_of_getElem? hr, hd⟩
  rw [hds]
  exact Array.mem_toList_iff.mpr (Frontend.mem_preparePrelude hmem)

/-- **The trace's kept definitions, theorems and opaques have distinct level positions**, when
the prepared stream is accepted. -/
theorem kept_levels {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls) :
    ∀ (ℓ : Nat) (r : Read .source), rs[ℓ]? = some r → ∀ d ∈ r.decls.toList, DefinitionBlockReads.DeclNodup d :=
  fun _ _ hr d hd => DefinitionPremises.accepted_nodup acc d (kept_mem hflat hds hr hd)

/-! ## Axioms -/

/-- **An accepted axiom's level positions are distinct**, or it is the pinned quotient soundness
axiom's record, which the checker compares with the pin canonically, so it has the pin's one
level parameter. -/
theorem accepted_axiom {md : Mode} {μ : CheckMode} {ev : Evidences md} {ds : List (Declaration md)}
    {env : Env md} (h : Cached.AcceptsRef μ ev ds env) {cv : Ix.Kernel.ConstantVal md} (hd : .axiomDecl cv ∈ ds) :
    LevelParam.nodup cv.levelParams = true ∨ cv.levelParams.length = 1 := by
  obtain ⟨F, hF⟩ := h
  unfold checkDeclsPure at hF
  obtain ⟨e, e', he⟩ := DefinitionPremises.foldlM_steps _ ds _ env hF _ hd
  by_cases hq : cv.name = quotSoundName
  · right
    simp only [checkDecl, hq, ↓reduceIte] at he
    split at he
    · rename_i hc
      have hc' := of_decide_eq_true hc
      have hlp := congrArg (fun c => c.toConstantVal.levelParams.length) hc'
      simpa [Ix.Kernel.ConstantInfo.canon, Ix.Kernel.ConstantVal.canon, Ix.Kernel.quotBasis, Ix.Kernel.quotSoundRaw,
        Ix.Kernel.ConstantInfo.toConstantVal] using hlp
    · cases he
  · left
    have run := Semantics.checkDeclRun_ofEnvFactsE he
    rcases run with ⟨hn, -⟩ | ⟨type', hcv, -⟩
    · exact absurd hn hq
    · exact hcv.2.2.2.1

/-- **A kept axiom's level parameters are distinct**, when the prepared stream is accepted. -/
theorem axiom_nodup {μ : CheckMode} {ev : Evidences .source} {envS : Env .source} {pre : Prelude .source}
    {decls ds : Array (Declaration .source)} {rs : List (Read .source)}
    (acc : Cached.AcceptsRef μ ev ds.toList envS)
    (hflat : decls.toList = rs.flatMap (·.decls.toList)) (hds : ds = Frontend.preparePrelude pre.ix decls)
    {g : Graph} {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint} {start : State .source}
    {ls : List Scheduled} {ℓ : Nat} {y : Scheduled} {v : Ix.AxiomVal} {c : Converted} {stS : State .source}
    {raw rd : Read .source} (low : LoweredAt g ρ hints start ls rs ℓ y (.axiom v) c stS raw rd) :
    rd = raw → v.cnst.levelParams.toList.Nodup := by
  intro e
  obtain ⟨-, hr, -, hconv, -, -, hl, -⟩ := low
  obtain ⟨cv0, rfl, hlps⟩ : ∃ cv0 : CVal .source, c = .axiom cv0 ∧
      cv0.levelParams = (Ix.LeanIngress.Numbering.mk v.cnst.levelParams false).params := by
    obtain ⟨_, -, -, rfl⟩ := RecordReadings.convert_axiom hconv
    exact ⟨_, rfl, rfl⟩
  have unfolded : Ix.LeanIngress.lower stS (((Converted.axiom cv0).withHints hints).quotient ρ) =
      .ok { decls := #[.axiomDecl (RecordReadings.quotientHeader ρ cv0)] } := rfl
  have hraw := Except.ok.inj (unfolded.symm.trans hl)
  subst e
  have hmem := kept_mem hflat hds hr (d := .axiomDecl (RecordReadings.quotientHeader ρ cv0))
    (by rw [← hraw]; simp)
  rcases accepted_axiom acc hmem with h | h
  · rw [RecordReadings.quotientHeader_eq, hlps] at h
    exact DefinitionBlockReads.nodup_of_params h
  · rw [RecordReadings.quotientHeader_eq, hlps] at h
    generalize v.cnst.levelParams = lps at h ⊢
    have hlen : lps.toList.length = 1 := by simpa [Ix.LeanIngress.Numbering.params] using h
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx]
    simp

/--
info: 'Ix.Cert.TraceSource.kept_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms kept_levels

/--
info: 'Ix.Cert.TraceSource.axiom_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms axiom_nodup

end Ix.Cert.TraceSource
