import Ix.Cert.SourceCommit

/-! # Stable replay on the production Source trace

A successful converted-array lookup comes from a real source group through
both hint and quotient maps; the missing-element error default is excluded.
Actual scheduled traces therefore supply the classification and basis facts
needed to preserve StableOwned through every retained commit.

The lowering and preparation wrappers discharge scheduled membership and
stability from successful execution alone. These are Source context facts:
declaration-stream acceptance, Source/Ixon unit correspondence, target context
coverage and the final compiler theorem remain separate obligations.
-/

namespace Ix.Cert.SourceTrace

open Ix.Kernel Ix.Kernel.Reader Ix.LeanIngress Ix.Cert.SourcePrelude Ix.Cert.SourceReplay

/-- Successful lookup through both converted-array maps comes from an actual
group conversion. The missing-element bang default is an error, not success. -/
theorem graph_conversion {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint}
    {env : Ix.Environment} {blocks : Ix.CondensedBlocks} {i : Nat} {conv : Converted}
    (h : (graphCollapsed ρ hints env blocks).converted[i]! = .ok conv) :
    ∃ gr c, (graph env blocks).groups[i]? = some gr ∧ convert gr = .ok c ∧
      conv = (c.withHints hints).quotient ρ := by
  change (((graph env blocks).converted.map (fun c => c.map (Converted.withHints hints))).map
    (fun c => c.map (Converted.quotient ρ)))[i]! = .ok conv at h
  rw [ReaderUnits.graph_converted] at h
  simp only [getElem!_def, Array.getElem?_map] at h
  cases hg : (groupsOf env blocks)[i]? with
  | none => simp [hg] at h
  | some gr =>
    cases hc : convert gr with
    | error e => simp [hg, hc, Except.map] at h
    | ok c =>
      have eq : (c.withHints hints).quotient ρ = conv := by simpa [hg, hc, Except.map] using h
      exact ⟨gr, c, by simpa only [ReaderUnits.graph_groups] using hg, hc, eq.symm⟩

variable {ixe : Ixon.Env} {roles : Std.HashMap Address Role}
  {hints : CName .source → Option ReducibilityHint} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}

/-- Membership is an internal trace condition. The actual-function wrappers
below discharge it using the schedule they really execute. -/
theorem trace_stable {start st : State .source} {xs rs s kb}
    (h : Trace (graphCollapsed (fiberAliasAt ixe roles) hints env blocks) start xs rs st s kb)
    (inside : ∀ x ∈ xs, x ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).zipIdx.toList) :
    StableOwned s st := by
  revert inside
  induction h with
  | nil => intro _ i d hd; simp at hd
  | «alias» ht _ ih =>
    intro inside
    exact ih fun x hx => inside x (List.mem_append_left _ hx)
  | @lowered xs rs st s kb x s' kb' conv raw r dropped ht hc hl hr hg ih =>
    intro inside
    have prior := ih fun y hy => inside y (List.mem_append_left _ hy)
    have hx : x.1 ∈ (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).toList := by
      have member := inside x (List.mem_append_right _ List.mem_cons_self)
      exact List.fst_mem_of_mem_zipIdx (by simpa only [Array.toList_zipIdx] using member)
    obtain ⟨gr, c, _, converted, eq⟩ := graph_conversion (ReaderUnits.scheduleOf_ok hx hc)
    subst conv
    exact (SourceCommit.collapseRead_commit (trace_ownerExact ht) (trace_keptNoBasis ht) prior
      (SourceCommit.quotient_lower_classified converted hints hl) (lower_noBasis _ _ _ hl) hr).2.2.1

/-- Actual production lowering supplies its kept-read trace and stable replay
without a caller-supplied classification, membership or stability premise. -/
theorem lowerAllCollapsed_stable {start fin : State .source} {decls : Array (Declaration .source)}
    (h : lowerAllCollapsed start (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)
      (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)) = .ok (fin, decls)) :
    ∃ rs s kb, Trace (graphCollapsed (fiberAliasAt ixe roles) hints env blocks) start
      (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).zipIdx.toList rs fin s kb ∧
      s.kept = decls ∧ fin = rs.foldl State.commit start ∧
      decls.toList = rs.flatMap (·.decls.toList) ∧ StableOwned s fin := by
  obtain ⟨rs, s, kb, ht, hs, hf, hd⟩ := lowerAllCollapsed_trace h
  exact ⟨rs, s, kb, ht, hs, hf, hd, trace_stable ht (fun _ h => h)⟩

/-- Successful production preparation retains the same actual trace and its
stable replay invariant. This is a context fact, not an acceptance theorem. -/
theorem prepareSourceCollapsed_stable {pre : Prelude .source} {ds : Array (Declaration .source)}
    (h : prepareSourceCollapsed (fiberAliasAt ixe roles) hints pre env blocks = .ok ds) :
    ∃ rs fin decls s kb,
      Trace (graphCollapsed (fiberAliasAt ixe roles) hints env blocks) pre.state
        (scheduleOf (graphCollapsed (fiberAliasAt ixe roles) hints env blocks)).zipIdx.toList rs fin s kb ∧
      s.kept = decls ∧ fin = rs.foldl State.commit pre.state ∧
      decls.toList = rs.flatMap (·.decls.toList) ∧
      ds = Frontend.preparePrelude pre.ix decls ∧ StableOwned s fin := by
  obtain ⟨fin, decls, hl, _, hp⟩ := prepareSourceCollapsed_keepsPrelude h
  obtain ⟨rs, s, kb, ht, hs, hf, hd, stable⟩ := lowerAllCollapsed_stable hl
  exact ⟨rs, fin, decls, s, kb, ht, hs, hf, hd, hp, stable⟩

end Ix.Cert.SourceTrace
