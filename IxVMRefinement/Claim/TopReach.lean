import IxVMRefinement.Claim.TopExport
import IxVMRefinement.Claim.SafetyAt

/-! # Restricting a typing walk to records reached from its seeds

The restriction retains every seed, uncovered used-reference edge and projection-owner
edge, with the original rank. It supplies explicit origins independently of how a recursive
walk spec represents its record list. In particular a reached non-block record is a seed
or a used reference, so the existing refusal facts show that it is not an inert axiom.

The safety lemmas below isolate the actual source-guard obligation: an edge from a source
whose record and owner are in logic has a target whose record and owner are in logic. They
do not infer that obligation from a bare `TopWalkCore`, which records checks but not the new
guard observations. `claimPhase_typing_reachable` is the concrete origin-producing walk export.
-/

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- The seed-generated portion of a top walk. Covered roles are supplied by the valid table. -/
inductive TopReach (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (seeds : List _root_.Address) :
    _root_.Address → Prop where
  | seed {a : _root_.Address} : a ∈ seeds → TopReach t E₀ seeds a
  | ref {a x : _root_.Address} : TopReach t E₀ seeds a → Typing.UsedRef E₀ a x →
      ¬ Typing.Covered t x → TopReach t E₀ seeds x
  | owner {a : _root_.Address} {c : Ixon.Constant} : TopReach t E₀ seeds a →
      recordOf E₀ a = some c → Typing.IsProj c → TopReach t E₀ seeds (Ix.Cert.ownerOf a c)

section Walk
variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- Every seed-generated record belongs to the original top walk. -/
theorem TopWalkCore.reach_subset
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {a : _root_.Address}
    (ha : TopReach t E₀ seeds a) : Top a := by
  induction ha with
  | seed hm => exact hW.seedsTop _ hm
  | ref _ hu hn ih =>
    rcases hW.closed _ _ ih hu with ⟨hx, -⟩ | hc
    · exact hx
    · exact (hn hc).elim
  | owner _ hc hp ih => exact (hW.owner _ _ ih hc hp).1

/-- Restrict a walk to its seed-generated portion without changing the store or rank. -/
theorem TopWalkCore.restrictReach
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) :
    TopWalkCore calls bAddr t seeds E₀ lim (TopReach t E₀ seeds) rank := by
  classical
  refine {
    topLim := hW.topLim
    table := hW.table
    runStore := hW.runStore
    hashedStored := hW.hashedStored
    seedsTop := fun _ ha => .seed ha
    record := fun a ha => hW.record a (hW.reach_subset ha)
    closed := ?_
    owner := ?_
    seedLogic := hW.seedLogic
    seedNotInert := hW.seedNotInert
    checked := fun a ha => hW.checked a (hW.reach_subset ha)
    refsNotInert := fun a x ha hu => hW.refsNotInert a x (hW.reach_subset ha) hu
    refsNotBlock := fun a x ha hu hn => hW.refsNotBlock a x (hW.reach_subset ha) hu hn }
  · intro a x ha hu
    by_cases hc : Typing.Covered t x
    · exact Or.inr hc
    · rcases hW.closed a x (hW.reach_subset ha) hu with ⟨-, hr⟩ | hc'
      · exact Or.inl ⟨.ref ha hu hc, hr⟩
      · exact (hc hc').elim
  · intro a c ha hc hp
    exact ⟨.owner ha hc hp, (hW.owner a c (hW.reach_subset ha) hc hp).2⟩

/-- The owner of a checked top projection is a block, not another standalone record. -/
theorem TopWalkCore.owner_isBlock
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    {a : _root_.Address} {c cb : Ixon.Constant}
    (ha : Top a) (hc : recordOf E₀ a = some c) (hp : Typing.IsProj c)
    (hb : recordOf E₀ (Ix.Cert.ownerOf a c) = some cb) : Typing.IsBlock cb := by
  obtain ⟨cb', hb', haddr⟩ := hW.projMember a c ha hc hp
  have heq : cb' = cb := Option.some.inj (hb'.symm.trans hb)
  subst cb'
  rcases haddr with ⟨heq, -⟩ | ⟨ms, i, m, hm, -⟩
  · have hr := (hW.owner a c ha hc hp).2
    rw [← heq] at hr
    exact (Nat.lt_irrefl _ hr).elim
  · exact ⟨ms, hm⟩

/-- A reached non-block record cannot be an inert axiom: its origin is a seed or a used
reference. The projection-owner origin would force it to be a block. -/
theorem TopWalkCore.reach_not_inert_of_not_block
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    {a : _root_.Address} {c : Ixon.Constant} (ha : TopReach t E₀ seeds a)
    (hc : recordOf E₀ a = some c) (hn : ¬ Typing.IsBlock c) : ¬ InertAt t a := by
  cases ha with
  | seed hm => exact hW.seedNotInert _ hm
  | ref hp hu _ => exact hW.refsNotInert _ _ (hW.reach_subset hp) hu
  | owner hp hrec hproj =>
    exact (hn (hW.owner_isBlock (hW.reach_subset hp) hrec hproj hc)).elim

end Walk

/-- Every installation unit is its own owner. -/
theorem ownerOf_unit (a : _root_.Address) {c : Ixon.Constant} (hk : Typing.UnitKind c) :
    Ix.Cert.ownerOf a c = a := by
  rcases hk with ⟨d, hd⟩ | ⟨r, hr⟩ | ⟨ms, hm⟩
  · simp only [Ix.Cert.ownerOf, hd]
  · simp only [Ix.Cert.ownerOf, hr]
  · simp only [Ix.Cert.ownerOf, hm]

/-- For a unit source, the existing in-logic premise supplies both source safety clauses. -/
theorem SourceSafe.of_unit {E₀ : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E₀ a = some c) (hk : Typing.UnitKind c) (hl : InLogic c) :
    SourceSafe E₀ a := by
  intro c' hc'
  have heq : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  refine ⟨hl, fun cb hb => ?_⟩
  rw [ownerOf_unit a hk] at hb
  have heq : cb = c := Option.some.inj (hb.symm.trans hc)
  simpa only [heq] using hl

section Safety
variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- Safety propagates from seeds through the actual guarded edges. Owner edges use the
already-proved block provenance. The edge premise is to be produced from guard observations. -/
theorem TopWalkCore.reach_safe
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    (hedge : ∀ a x, Top a → SourceSafe E₀ a → Typing.UsedRef E₀ a x →
      ¬ Typing.Covered t x → SourceSafe E₀ x)
    {a : _root_.Address} (ha : TopReach t E₀ seeds a) : SourceSafe E₀ a := by
  induction ha with
  | seed hm => exact hW.seedLogic _ hm
  | ref hp hu hn ih => exact hedge _ _ (hW.reach_subset hp) ih hu hn
  | @owner a c hp hc hproj ih =>
    obtain ⟨cb, hb⟩ := hW.record _ (hW.owner a c (hW.reach_subset hp) hc hproj).1
    exact SourceSafe.of_unit hb
      (Or.inr (Or.inr (hW.owner_isBlock (hW.reach_subset hp) hc hproj hb)))
      ((ih c hc).2 cb hb)

/-- The exact NeedOk producer for an in-logic installation unit. No safety is demanded of
unrelated unsafe-origin sources or of a projection wrapper merely because its flag is absent. -/
theorem TopWalkCore.needOk_of_safe_edges
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    (hedge : ∀ a x, Top a → SourceSafe E₀ a → Typing.UsedRef E₀ a x →
      ¬ Typing.Covered t x → SourceSafe E₀ x)
    {a x : _root_.Address} {c : Ixon.Constant}
    (ha : Top a) (hc : recordOf E₀ a = some c) (hk : Typing.UnitKind c) (hl : InLogic c)
    (hu : Typing.UsedRef E₀ a x) (hn : ¬ Typing.Covered t x) : Typing.NeedOk E₀ x := by
  have hx : Top x := (hW.closed a x ha hu).resolve_right hn |>.1
  obtain ⟨cx, hcx⟩ := hW.record x hx
  have hs := hedge a x ha (SourceSafe.of_unit hc hk hl) hu hn
  exact ⟨cx, hcx, hW.refsNotBlock a x ha hu hn cx hcx, (hs cx hcx).1, (hs cx hcx).2⟩

/-- The reference-index form consumed by the definition/block cover adapters. -/
theorem TopWalkCore.need_of_safe_edges
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    (hedge : ∀ a x, Top a → SourceSafe E₀ a → Typing.UsedRef E₀ a x →
      ¬ Typing.Covered t x → SourceSafe E₀ x)
    {a : _root_.Address} {c : Ixon.Constant}
    (ha : Top a) (hc : recordOf E₀ a = some c) (hk : Typing.UnitKind c) (hl : InLogic c) :
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      inertKey (IxVM.Consistency.keyOf t x) = false → ¬ Typing.Covered t x → Typing.NeedOk E₀ x := by
  intro i hi x hx _ hn
  exact hW.needOk_of_safe_edges hedge ha hc hk hl (Typing.usedRef_of_idx hc hi hx) hn

end Safety

/-- The concrete walk export with origins: the reached set is built here from the observed
walk, with no external origin or standing premise. -/
theorem claimPhase_typing_reachable
    {d : Digest} {value : SourceValue F} {heap : Heap F} {calls : List (Call F)}
    (ev : ObsFn W verifyClaim [digestValue d] [] value heap calls)
    {bytes : ByteArray} {c : Ix.Claim} (hde : Ix.Claim.de bytes = .ok c)
    (hpack : packDigest (Address.blake3Pure bytes) = d) (hscope : InScopeTyping c)
    {V : View} {seeds : List _root_.Address} (hseeds : ClaimSeeds c V seeds)
    {ctx : Ix.ClaimContext} (hctx : c.context? = some ctx) {tb : ByteArray}
    {t : Ix.Kernel.RoleTable}
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨ctx.binding, tb⟩ = .ok t) :
    V.HashedCollision (bytes :: tb :: committedFootprint) calls ∨
      ∃ (lim : Option Nat) (E₀ : Ixon.Env) (rank : _root_.Address → Nat),
        TopWalkCore calls ctx.binding t seeds E₀ lim (TopReach t E₀ seeds) rank := by
  rcases claimPhase_typing_walk ev hde hpack hscope hseeds hctx hadm with
    hc | ⟨lim, E₀, Top, rank, hW⟩
  · exact Or.inl hc
  · exact Or.inr ⟨lim, E₀, rank, hW.restrictReach⟩

end IxVM.Refinement.Claim
