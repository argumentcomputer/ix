import IxVMRefinement.Claim.TopWalkTyping
import IxVMRefinement.Claim.TopProj

/-! # The claim layer's export to the typing skeleton

`TopWalk calls` is the `Walk` that `Typing.typing_skeleton` takes: a typing run's walk export
(`TopWalkCore`, with its check evidence at the run's top-level limit) together with the part the
assembly reads (`Typing.TopGraph`). `TopWalkCore.graph` builds the second from the first and the
standing clause (an axiom or quotient record walked at the top level stands at a standard
axiom's role or a quotient role); `claimPhase_typing_of_standing` is `Typing.ClaimExport` for
every accepted bounded run, given that clause. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false

/-- **The standing clause** of `Typing.TopGraph` at a walk. -/
def StandingAt (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Top : _root_.Address → Prop) : Prop :=
  ∀ a c, Top a → recordOf E₀ a = some c →
    ((∃ ax, c.info = .axio ax) ∨ ∃ q, c.info = .quot q) →
    ∃ r ∈ Typing.standingRoles, t.addressOf? r = some a

/-- **The assembly's reading of a walk** from the walk export (A1, A3, A4, A5) and the standing
clause. -/
theorem TopWalkCore.graph {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) (hstand : StandingAt t E₀ Top) :
    Typing.TopGraph t E₀ seeds Top rank where
  seedsTop := hW.seedsTop
  record := hW.record
  closed := hW.closed
  owner := hW.owner
  members := hW.members
  projMember := hW.projMember
  standing := hstand
  seedLogic := hW.seedLogic

/-- **The claim layer's walk**, the `Walk` of `Typing.ClaimExport`: at some binding, the walk
export and the assembly's reading of it. -/
def TopWalk (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat) : Prop :=
  ∃ bAddr, TopWalkCore calls bAddr t seeds E₀ lim Top rank ∧ Typing.TopGraph t E₀ seeds Top rank

/-- **The claim layer for the typing half**, given the standing clause of every walk export:
`Typing.ClaimExport (TopWalk calls) calls d` for an accepted run. -/
theorem claimPhase_typing_of_standing
    (hstand : ∀ {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
      {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
      {Top : _root_.Address → Prop} {rank : _root_.Address → Nat},
      TopWalkCore calls bAddr t seeds E₀ lim Top rank → StandingAt t E₀ Top)
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls) :
    Typing.ClaimExport (TopWalk calls) calls d := by
  intro bytes c hde hpack hscope V seeds hseeds ctx hctx tb t hadm
  rcases claimPhase_typing_walk ev hde hpack hscope hseeds hctx hadm with
    hcoll | ⟨lim, E₀, Top, rank, hW⟩
  · exact .inl hcoll
  · exact .inr ⟨E₀, lim, Top, rank, hW.runStore, ctx.binding, hW, hW.graph (hstand hW)⟩

end IxVM.Refinement.Claim
