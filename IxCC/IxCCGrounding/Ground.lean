import IxCCGrounding.Fundamental
import IxCCGrounding.Runs
import IxCCGrounding.Check
import IxCCGrounding.CaseFire
import IxCCGrounding.Direct.Sites
import IxCCGrounding.CaseBlind

/-!
# The fundamental lemma from the check (`IxCCGrounding.Ground`)

The landed form of the fundamental lemma: for every program, kernel reading, key map, level
parameters, certificate annotation and finite `Sl` that pass the check (`groundCheck`, run on
closure bytes by `tests-grounding`), every set theory and every model with the laws, under the
typing hypothesis `SitesOk` at the sites the direct route refuses only (`SitesOkRes`,
`IxCCGrounding.Direct.Sites`), each of SrcEval's eight mutual functions returns values related to
what their kernel counterparts denote, at every clock (`allP_of_check`), and in particular a
constant SrcEval unfolds at an `Ok` instance returns a value related to the constant's denotation
(`const_of_check`). F5's meaning at each `case` constant is no longer a hypothesis: the check
decides each `case` entry's shape (`caseFacts_of_check`) and the generic `case` lemma derives it
(`caseFires_of_shape`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **F5's meaning at every `case` constant of `Sl`, from the check.** -/
theorem caseFires_of_check (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) :
    ∀ c r, c ∈ Sl → p.table.resolveOf c = some (.case r) →
      CaseFires M p κ lpsOf (· ∈ Sl) (Ok p ann) c := by
  intro c r hc hr
  have hG := groundFacts_of_check hchk
  obtain ⟨sh, hst, hpr⟩ := caseFacts_of_check hchk c r hc hr
  exact caseFires_of_shape hL hG.faith hG.natBasis hc hr hst hpr

/-- **The fundamental lemma, from the check**, under typing at the sites the direct route refuses
only (`SitesOkRes`). -/
theorem allP_of_check (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl)) :
    ∀ k, AllP M p κ lpsOf (· ∈ Sl) (Ok p ann) k :=
  allP (fundHyps_of hL (groundFacts_of_check hchk)
    (sitesOk_of_res (lawsCore_of_laws hL) (groundFacts_of_check hchk) hT) (caseFires_of_check hL hchk))

/-- The landed form, under `SitesOk`. -/
theorem allP_of_check_of_sitesOk (hL : Laws M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl)) :
    ∀ k, AllP M p κ lpsOf (· ∈ Sl) (Ok p ann) k :=
  allP_of_check hL hchk (sitesOkRes_of_sitesOk hT)

theorem const_of_check (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {ls : Levels} {c : CId} {v : Value} {φ : LevelParam → Nat}
    (hrun : IxCC.Src.evalConst p k ls c = .ok v) (hc : c ∈ Sl) (hOk : Ok p ann c ls)
    (hlv : LvAt φ (lpsOf c) ls) :
    RelV M κ lpsOf (· ∈ Sl) (Ok p ann) v (M.cval (κ c) φ) :=
  (allP_of_check hL hchk hT k).evalConst ls c v φ hrun hc hOk hlv

theorem const_of_check_of_sitesOk (hL : Laws M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {ls : Levels} {c : CId} {v : Value} {φ : LevelParam → Nat}
    (hrun : IxCC.Src.evalConst p k ls c = .ok v) (hc : c ∈ Sl) (hOk : Ok p ann c ls)
    (hlv : LvAt φ (lpsOf c) ls) :
    RelV M κ lpsOf (· ∈ Sl) (Ok p ann) v (M.cval (κ c) φ) :=
  const_of_check hL hchk (sitesOkRes_of_sitesOk hT) hrun hc hOk hlv

/-! ## The canonicity-free family

On a program where the check and `noCanonB` hold, the same conclusions over `LawsNoCanon` (δ, ι in
#678's guarded form, level-parameter irrelevance, the projection law, the `Nat` accelerations) in
place of `Laws`: no canonicity law. -/

/-- **The fundamental lemma's hypotheses without canonicity**: the recursors' half from `NoCanon`,
F5 at every `case` entry from `caseFires_of_noCanon`. -/
theorem fundHyps_of_noCanon (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    (hG : GroundFacts p env κ lpsOf ann S) (hC : CaseFacts p env κ S) (hNC : NoCanon p env κ S)
    (hT : SitesOk M p κ lpsOf ann S) : FundHyps M p κ lpsOf S (Ok p ann) :=
  fundHyps_of_core hL.core (.inr hNC.recs) hG hT
    (caseFires_of_noCanon hL.defn_value hL.iota_rule hL.cval_params hG.faith hG.natBasis hC hNC)

/-- **The fundamental lemma, from the check, without canonicity** (`allP_of_check` over
`LawsNoCanon`, for a program that also passes `noCanonB`). -/
theorem allP_of_check_noCanon (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonB p env κ Sl = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl)) :
    ∀ k, AllP M p κ lpsOf (· ∈ Sl) (Ok p ann) k :=
  allP (fundHyps_of_noCanon hL (groundFacts_of_check hchk) (caseFacts_of_check hchk)
    (noCanon_of_check hnc) (sitesOk_of_res hL.core (groundFacts_of_check hchk) hT))

/-- `const_of_check` without canonicity. -/
theorem const_of_check_noCanon (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonB p env κ Sl = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {ls : Levels} {c : CId} {v : Value} {φ : LevelParam → Nat}
    (hrun : IxCC.Src.evalConst p k ls c = .ok v) (hc : c ∈ Sl) (hOk : Ok p ann c ls)
    (hlv : LvAt φ (lpsOf c) ls) :
    RelV M κ lpsOf (· ∈ Sl) (Ok p ann) v (M.cval (κ c) φ) :=
  (allP_of_check_noCanon hL hchk hnc hT k).evalConst ls c v φ hrun hc hOk hlv

end IxCC.Grounding
