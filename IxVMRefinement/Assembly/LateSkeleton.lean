import IxVMRefinement.Assembly.TypingSkeleton

/-! # The typing skeleton with a store-relative extra clause

`typing_skeleton` folds the steps with one extra clause `X t (fun _ => True) R`, a predicate on
the environment that does not see the record store the steps run against. A clause that says
what a stored constant is in terms of the records the circuit reads (the registry of native
families, `LateRegistry t E`) is relative to that store, as the prefix invariant is.

`typing_skeleton_core_at` and `typing_skeleton_at` are the two skeleton theorems with the extra
clause indexed by the store: the fold carries `X E` for the store `E` the steps run against; the
witness's internal part carries it for every store for its records (`RecordsFor R E`), as its
prefix invariant does. The proofs are those of `typing_skeleton_core` and `typing_skeleton`,
with the clause chosen once the store is.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo)

section Skeleton

variable {t : Ix.Kernel.RoleTable} {R E₀ : Ixon.Env} {envT : Ix.Kernel.Env .anon}
  {seeds : List _root_.Address} {calls : List (Call F)}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- **The typing conclusion, from the walk and the steps, with a store-relative extra clause**,
where the run hashed no collision: `typing_skeleton_core` with the clause `X E` at the store `E`
the steps run against. -/
theorem typing_skeleton_core_at {V : View} {extra : List ByteArray}
    {X : Ixon.Env → Ix.Kernel.Env .anon → Prop} {lim : Option Nat}
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hfacts : Facts.{u} t (fun _ => True) R envT) (hX : ∀ E, RecordsFor R E → X E envT)
    (ht : t.check = .ok ())
    (hb : Bounded calls) (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnc : ¬ CollisionWith V extra R calls) (hS : LoadedReads.RunStore calls E₀)
    (hG : TopGraph t E₀ seeds Top rank)
    (hstep : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → recordOf E₀ A = some c →
      InLogic c → UnitKind c → UnitStep.{u} (X E) t envT E₀ E lim A c) :
    ConsistentReadOver.{u} calls t R envT seeds := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hload : LoadedBy calls E₀ := hS.loaded
  have hdec : Ingress.EnvDecoded E₀ := hS.decoded
  obtain ⟨E, hM⟩ := merged_exists E₀ R
  have hrf : RecordsFor R E := hM.recordsFor hload hdec hshape.committed hextra hnc
  have hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c :=
    fun a c h => hM.run_record hload hdec hextra hnc h
  have hctx : StepCtx.{u} calls t R envT E₀ E :=
    ⟨hshape, hrf, hrun, fun a b h => hM.run_blob hload hnc h,
      fun env lim => hM.good hload hshape.zeroFree hextra hnc hb env t lim⟩
  have hrec := records_agree hload hnc
  have hblob := blobs_agree hload hnc
  have hinvT : Decl.PrefixInv.{u} E t lim envT := hfacts.inv E hrf lim (limWithin_all t lim)
  have hwhole := hfacts.whole E hrf
  obtain ⟨us, hus⟩ := exists_list_of_records E₀ (IsAnchor t envT E₀ Top)
    (fun A hA => hG.record A hA.1)
  have h₀ : FoldInv.{u} (X E) t E₀ R E lim envT :=
    ⟨hshape.reading.nodup, hinvT, hX E hrf,
      provenance_over_witness hrec hblob hshape.reading.provenance⟩
  have hown : (typingFold.{u} (X E) t E₀ R E lim rank).OwnsApart us := by
    intro A hA A' hA' x hx hx'
    obtain ⟨c, hc, hca⟩ := hx
    obtain ⟨c', hc', hca'⟩ := hx'
    exact hG.owns_apart ((hus A).mp hA).1 ((hus A').mp hA').1 hc hc' hca hca'
  have hfreshT : (typingFold.{u} (X E) t E₀ R E lim rank).FreshAt envT us := by
    intro A hA x hx hst
    obtain ⟨c, hc, hca⟩ := hx
    exact anchor_fresh hG hwhole hrun ((hus A).mp hA) hc hca hst
  obtain ⟨env, hinv, hext, hdone, -⟩ :=
    (typingFold.{u} (X E) t E₀ R E lim rank).run h₀ hown hfreshT
      (needs_earlier hG hshape htwf hus)
      (fold_steps hG hshape htwf hroles hwhole hrun hus (hstep E hctx))
  have hFI : FoldInv.{u} (X E) t E₀ R E lim env := hinv
  have hextT : ∀ ci ∈ envT.consts, ci ∈ env.consts := hext
  refine ⟨E₀, env, hload, hFI.nodup, hextT, hFI.prov, ?_,
    claimedEnv_models_of_prefixInv hFI.inv hFI.nodup hFI.prov⟩
  intro a ha a' hsc
  have hTa := hG.seedsTop a ha
  obtain ⟨c, hc⟩ := hG.record a hTa
  obtain ⟨hlogc, hlogB⟩ := hG.seedLogic a ha c hc
  have hpost : ∀ (A : _root_.Address) (cA : Ixon.Constant) (y : _root_.Address), A ∈ us →
      recordOf E₀ A = some cA → ConstAddrOf A cA y →
      ∃ ci, env.find? (keyOf t y) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) y ci) := by
    intro A cA y hA hcA hca
    have hP : ∀ c, recordOf E₀ A = some c → ∀ x, ConstAddrOf A c x →
        ∃ ci ∈ env.consts, ci.name = keyOf t x ∧
          KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci := (hdone A hA).2
    obtain ⟨ci, hci, hname, hk⟩ := hP cA hcA y hca
    have hf := find_of_mem_nodup hFI.nodup hci
    rw [hname] at hf
    exact ⟨ci, hf, Or.inr hk⟩
  by_cases hst : StoredAt t envT a'
  · obtain ⟨ci, hci, hname⟩ := hst
    have hfT := find_of_mem_nodup hshape.reading.nodup hci
    rw [hname] at hfT
    have hf := find_of_mem_nodup hFI.nodup (hextT ci hci)
    rw [hname] at hf
    exact ⟨ci, hf, stored_provenance hroles hrec hblob hshape.reading.provenance hfT⟩
  · rcases hsc with ⟨haa, hnm⟩ | ⟨c', ms, i, m, hc', hms, hm, hx⟩
    · rw [haa] at hst
      rw [haa]
      rcases kind_cases c with hsa | hpr | hbl
      · exact hpost a c a ((hus a).mpr ⟨hTa, c, hc, hlogc, a, Or.inl ⟨rfl, hsa⟩, hst⟩) hc
          (Or.inl ⟨rfl, hsa⟩)
      · obtain ⟨hTB, -⟩ := hG.owner a c hTa hc hpr
        obtain ⟨cb, hcb, hconst⟩ := hG.projMember a c hTa hc hpr
        exact hpost _ cb a ((hus _).mpr ⟨hTB, cb, hcb, hlogB cb hcb, a, hconst, hst⟩) hcb hconst
      · obtain ⟨ms, hms⟩ := hbl
        exact absurd hms (hnm c ms hc)
    · rw [hc] at hc'
      have hcc : c = c' := Option.some.inj hc'
      rw [← hcc] at hms
      have hca : ConstAddrOf a c a' := Or.inr ⟨ms, i, m, hms, hm, hx⟩
      exact hpost a c a' ((hus a).mpr ⟨hTa, c, hc, hlogc, a', hca, hst⟩) hc hca

end Skeleton

/-- **The typing statement over explicit interfaces, with a store-relative extra clause**:
`typing_skeleton` for the witness's internal part `FactsWith` of the clause "`X t E` at every
store `E` for the witness's records", from steps that keep `X t E` at the store they run
against. -/
theorem typing_skeleton_at
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstep : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} calls t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t E) t envT E₀ E lim A c) :
    TypingSpecOn.{u}
      (FactsWith.{u} (fun t _ R env => ∀ E, RecordsFor R E → X t E env)) calls d := by
  intro bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT hW
  by_cases hnc : CollisionWith V (bytes :: tb :: committedFootprint) R calls
  · exact Or.inl hnc
  · refine Or.inr ?_
    have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
    have hextra : ∀ x ∈ committedFootprint, x ∈ bytes :: tb :: committedFootprint :=
      fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
    rcases hclaim bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm with
      hcol | ⟨E₀, lim, Top, rank, hS, hWalk⟩
    · exact (hnc (Or.inl hcol)).elim
    · have hF : Facts.{u} t (fun _ => True) R envT := hW.facts.1
      have hX : ∀ E, RecordsFor R E → X t E envT := hW.facts.2
      exact typing_skeleton_core_at hW.shape hF hX ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank hWalk)
        (fun E hE => hstep t seeds E₀ lim Top rank hWalk R envT E hE)

end IxVM.Refinement.Typing
