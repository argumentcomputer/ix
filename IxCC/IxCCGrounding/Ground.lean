import IxCCGrounding.Fundamental
import IxCCGrounding.Runs
import IxCCGrounding.Check

/-!
# The fundamental lemma from the check (`IxCCGrounding.Ground`)

The landed form of the fundamental lemma: for every program, kernel reading, key map, level
parameters, certificate annotation and finite `Sl` that pass the check (`groundCheck`, run on
closure bytes by `tests-grounding`), every set theory and every model with the laws, under the
typing hypothesis `SitesOk` and F5's meaning at each `case` constant of `Sl` (`CaseFires`; the
generic `case` lemma discharges it from a checked shape), each of SrcEval's eight mutual functions
returns values related to what their kernel counterparts denote, at every clock
(`allP_of_check`), and in particular a constant SrcEval unfolds at an `Ok` instance returns a
value related to the constant's denotation (`const_of_check`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

/-- **The fundamental lemma, from the check.** -/
theorem allP_of_check (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    (hcases : ∀ c r, c ∈ Sl → p.table.resolveOf c = some (.case r) →
      CaseFires M p κ lpsOf (· ∈ Sl) (Ok p ann) c) :
    ∀ k, AllP M p κ lpsOf (· ∈ Sl) (Ok p ann) k :=
  allP (fundHyps_of hL (groundFacts_of_check hchk) hT hcases)

/-- **A constant SrcEval unfolds**, at an `Ok` instance, returns a value related to the
constant's denotation. -/
theorem const_of_check (hL : Laws M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true)
    (hT : SitesOk M p κ lpsOf ann (· ∈ Sl))
    (hcases : ∀ c r, c ∈ Sl → p.table.resolveOf c = some (.case r) →
      CaseFires M p κ lpsOf (· ∈ Sl) (Ok p ann) c)
    {k : Nat} {ls : Levels} {c : CId} {v : Value} {φ : LevelParam → Nat}
    (hrun : IxCC.Src.evalConst p k ls c = .ok v) (hc : c ∈ Sl) (hOk : Ok p ann c ls)
    (hlv : LvAt φ (lpsOf c) ls) :
    RelV M κ lpsOf (· ∈ Sl) (Ok p ann) v (M.cval (κ c) φ) :=
  (allP_of_check hL hchk hT hcases k).evalConst ls c v φ hrun hc hOk hlv

end IxCC.Grounding
