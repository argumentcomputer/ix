import IxVMRefinement.Claim.TopWalk
import IxVMRefinement.Claim.TopWalkEnv

/-! # The claim layer's walk export for both typing claims

`claimPhase_typing_walk`: an accepted typing claim in scope (`check` or `checkEnv`, its table
validated or assumed) under a table that admits at its context's address hashed a collision,
or its walk at the run's top-level limit exports `TopWalkCore`. A `check` claim's walk is
`claimPhase_typing_check`'s; a `checkEnv` claim's is `walk_leaves_owned_lim_spec`'s, closed by
`topWalkCore_of_recs`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-- **The claim layer's walk export for a typing run** (A0-A3 for `check` and `checkEnv`, both
modes). -/
theorem claimPhase_typing_walk
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls)
    {bytes : ByteArray} {c : Ix.Claim} (hde : Ix.Claim.de bytes = .ok c)
    (hpack : packDigest (Address.blake3Pure bytes) = d)
    (hscope : InScopeTyping c)
    {V : View} {seeds : List _root_.Address} (hseeds : ClaimSeeds c V seeds)
    {ctx : Ix.ClaimContext} (hctx : c.context? = some ctx) {tb : ByteArray}
    {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ = .ok t) :
    V.HashedCollision (bytes :: tb :: committedFootprint) calls ∨
    ∃ (lim : Option Nat) (E₀ : Ixon.Env) (Top : _root_.Address → Prop)
      (rank : _root_.Address → Nat), TopWalkCore calls ctx.binding t seeds E₀ lim Top rank := by
  rcases claimPhase_typing_check ev hde hpack hscope hseeds hctx hadm with
    hcoll | ⟨lim, hlim, ⟨E₀, Top, rank, hcore⟩ | henv⟩
  · exact .inl hcoll
  · exact .inr ⟨lim, E₀, Top, rank, hcore⟩
  · obtain ⟨as, h₁, h₂, x_rc, x_leaves, v₁, cs₁, -, hmap, hrc, hl, ev_w, -, hsub⟩ := henv
    rcases noColl_or_hashedCollision V (bytes :: tb :: committedFootprint) calls with
      hcoll | hnoColl
    · exact .inl hcoll
    rcases walk_leaves_owned_lim_spec (V := V) (extra := bytes :: tb :: committedFootprint)
        (b := ⟨ctx.binding, tb⟩) hadm (by simp) hlim as hrc hl ev_w with
      hcoll | ⟨-, hseedOk, recs, hmem, hcl, -⟩
    · exact .inl (IxVM.Refinement.Claim.hashedCollision_mono hsub hcoll)
    · refine .inr ⟨lim, _, _, _, topWalkCore_of_recs (b := ⟨ctx.binding, tb⟩) hnoColl hadm hlim
        (recs.map (TopRec.mono hsub)) (hcl.mono hsub) (seeds := seeds) ?_ ?_⟩
      · intro x hx
        rw [← hmap] at hx
        simpa only [map_addr_topRec_mono] using hmem x hx
      · intro x hx
        rw [← hmap] at hx
        exact (hseedOk x hx).mono hsub

end IxVM.Refinement.Claim
