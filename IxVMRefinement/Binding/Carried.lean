import IxVMRefinement.Binding.Fold
import IxVMRefinement.Assembly.LateSkeleton

/-! # The composed statement with the internal part at the carried limits

`composed_skeleton` composes the two halves through `FactsWith X`, whose prefix invariant is at
every limit. The binding fold reaches the carried limits only (`Carried`: no limit, the group
count, a group's validation limit), and lowering to the others needs the projection guard
there. This file composes the halves through `BW X` instead (`BFacts`: the prefix invariant at
the carried limits), so the binding half is the fold's invariant on the 77 groups as it stands.

* `typing_skeleton_core_lim`: `typing_skeleton_core_at` with the witness's prefix invariant read
  at the walk's limit only, and block wholeness, in place of `Facts` (the body is that theorem's,
  which reads `Facts` at those two places only).
* `typing_skeleton_carried`: the typing half for `BW X`, from a walk whose limit is one a typing
  claim's context carries (`WalkLim`: `some 77` for a claim that validates its table, none for
  one that assumes it). The claim layer's walk export carries it (`TopWalkCore.topLim`).
* `bfacts_all_groups`, `bw_of_bnd`, `binding_skeleton_bw`: the binding half for `BW X`, from the
  fold's invariant on the 77 groups, with no lowering.
* `composed_skeleton_carried`: the composed statement from the binding fold's hypotheses, the
  typing walk and its limit, and the typing steps.

The extra clause is store-relative on the typing side (`X t E`, as `typing_skeleton_at` and the
native block step's carried clause `NativeBlockX t E` are), and the binding fold carries it as
`StoreX X` (the clause at every record store for its records).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-! ## The limits of a typing claim -/

/-- **The limits a typing claim's context carries**: the group count for a claim that validates
its table (validator 3, `Mk(tbl, 77, _)`), none for one that assumes it (validator 4,
`Assumed`). -/
def TypingLim (lim : Option Nat) : Prop := lim = some 77 ∨ lim = none

theorem carried_of_typingLim {lim : Option Nat} (h : TypingLim lim) : Carried lim := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

/-- **Every limit is within the 77 groups.** -/
theorem limWithin_77 (t : Ix.Kernel.RoleTable) (lim : Option Nat) :
    LimWithin (· < 77) t lim :=
  fun r _ _ => RoleVal.groupOf_lt_77 r

/-- **The walk's limit is one a typing claim's context carries** (claim layer: the walk export's
`topLim` field). -/
def WalkLim
    (Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop) : Prop :=
  ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank → TypingLim lim

/-! ## The typing half, with the prefix invariant at the walk's limit -/

section Skeleton

variable {t : Ix.Kernel.RoleTable} {R E₀ : Ixon.Env} {envT : Ix.Kernel.Env .anon}
  {seeds : List _root_.Address} {calls : List (Call F)}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- **The typing conclusion, from the walk and the steps, with the witness's prefix invariant at
the walk's limit only**, where the run hashed no collision: `typing_skeleton_core_at` with its
two reads of `Facts` (the prefix invariant at `lim`, block wholeness) taken as inputs. -/
theorem typing_skeleton_core_lim {V : View} {extra : List ByteArray}
    {X : Ixon.Env → Ix.Kernel.Env .anon → Prop} {lim : Option Nat}
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hinvL : ∀ E, RecordsFor R E → Decl.PrefixInv.{u} E t lim envT)
    (hwholeL : ∀ E, RecordsFor R E →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb →
        cb.info = .muts ms → BlockStored t envT B ms)
    (hX : ∀ E, RecordsFor R E → X E envT)
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
  have hinvT : Decl.PrefixInv.{u} E t lim envT := hinvL E hrf
  have hwhole := hwholeL E hrf
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

/-- **The extra clause at every record store for the witness's records**: the binding fold's
form of a store-relative clause `X t E`. It does not read the group set. -/
def StoreX (X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop)
    (t : Ix.Kernel.RoleTable) (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  ∀ E, RecordsFor R E → X t E env

theorem xAllGroups_storeX (X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop) :
    XAllGroups (StoreX X) :=
  fun _ _ _ h => h

/-- **The typing half for the internal part `BW`**: the witness's prefix invariant is read at
the walk's limit, which a typing claim's context carries (`WalkLim`), so `BFacts` (the prefix
invariant at the carried limits) suffices. Steps keep the store-relative clause `X t E`. -/
theorem typing_skeleton_carried
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstep : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} calls t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t E) t envT E₀ E lim A c) :
    TypingSpecOn.{u} (BW.{u} (StoreX X)) calls d := by
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
    · have hF : BFacts.{u} t (fun _ => True) R envT := hW.facts.1
      have hX : ∀ E, RecordsFor R E → X t E envT := hW.facts.2
      have hc : Carried lim := carried_of_typingLim (hlim t seeds E₀ lim Top rank hWalk)
      exact typing_skeleton_core_lim hW.shape
        (fun E hE => hF.inv E hE lim hc (limWithin_all t lim)) hF.whole hX ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank hWalk)
        (fun E hE => hstep t seeds E₀ lim Top rank hWalk R envT E hE)

/-! ## The binding half, with no lowering -/

/-- `Shapes` on a group set holds on any set whose groups of roles are in it. -/
theorem Shapes.mono {G G' : Nat → Prop} {env : Ix.Kernel.Env .anon}
    (hG : ∀ r : Ix.Kernel.Role, G' (Ix.SpecDigest.groupOf r) → G (Ix.SpecDigest.groupOf r))
    (h : Shapes G env) : Shapes G' env where
  bool := fun hg => h.bool (hG _ hg)
  char := fun hg => h.char (hG _ hg)
  string := fun hg => h.string (hG _ hg)
  list := fun hg => h.list (hG _ hg)
  charOfNat := fun hg => h.charOfNat (hG _ hg)
  stringOfList := fun hg => h.stringOfList (hG _ hg)
  iff := fun hg => h.iff (hG _ hg)
  nonempty := fun hg => h.nonempty (hG _ hg)
  eqns := fun r h46 hg => h.eqns r h46 (hG r hg)

/-- **The internal invariant on the 77 groups is the internal invariant on every group**: every
limit is within the 77 groups, and every role's group is one of them. -/
theorem bfacts_all_groups {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (h : BFacts.{u} t (· < 77) R env) : BFacts.{u} t (fun _ => True) R env where
  inv := fun E hE lim hc _ => h.inv E hE lim hc (limWithin_77 t lim)
  whole := h.whole
  opsPinned := h.opsPinned
  opsAdmitted := fun _ _ _ => trivial
  shapes := Shapes.mono (fun r _ => RoleVal.groupOf_lt_77 r) h.shapes

/-- **The invariant on the 77 groups gives a table witness on every group for `BW X`**, with
no lowering of the limit. -/
theorem bw_of_bnd
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hX : X t (· < 77) R env → X t (fun _ => True) R env) (h : Bnd.{u} X t (· < 77) R env) :
    TableWitness.{u} (BW.{u} X) t (fun _ => True) R env := by
  have hs : TableShape.{u} t (fun g => g < Ix.SpecDigest.groups.length) R env := by
    rw [groups_length]
    exact h.shape
  exact ⟨hs.of_all_groups, bfacts_all_groups h.facts, hX h.extra⟩

/-- **The binding half for the internal part `BW X`** over the fold's interfaces
(`binding_skeleton` with `bw_of_bnd` in place of `witness_of_bnd`). -/
theorem binding_skeleton_bw
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {calls : List (Call F)} {d : Digest}
    (hclaim : BindingClaimExport Run calls d) (hbase : BasisBase.{u} X Run)
    (hadm : AdmitsChain Run) (hstep : GroupSteps.{u} X Run) (hX : XAllGroups X) :
    BindingSpecOn.{u} (BW.{u} X) calls d := by
  intro bytes spec a hde hdig V
  rcases hclaim bytes spec a hde hdig V with hcol | ⟨tb, t, htb, hadmt, hall, ρ, Rs, hload, hrun⟩
  · exact Or.inl hcol
  · obtain ⟨env₆, hb6⟩ := hbase t ρ Rs hrun hall
    obtain ⟨env, -, hb⟩ := fold_groups hall hb6 (hadm t ρ Rs hrun)
      (hstep t ρ Rs hrun hall) 77 (by omega) (Nat.le_refl 77)
    have hlast := hadm t ρ Rs hrun 76 (by omega) (by omega)
    exact Or.inr ⟨tb, t, Rs 77, env, htb, hadmt, hall,
      loadedBy_sub hload hlast.loaded hlast.loadedBlobs, bw_of_bnd (hX t (Rs 77) env) hb⟩

/-! ## The composed statement -/

/-- **The composed statement through `BW`** (module docstring): the binding fold's hypotheses
with the extra clause `StoreX X`, and the typing walk, its limit and the steps keeping `X t E`,
give `ComposedSpec`. -/
theorem composed_skeleton_carried
    {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (hclaimB : BindingClaimExport Run callsB dB) (hbase : BasisBase.{u} (StoreX X) Run)
    (hadm : AdmitsChain Run) (hstepB : GroupSteps.{u} (StoreX X) Run)
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepA : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} callsA t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (X t E) t envT E₀ E lim A c) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_bw hclaimB hbase hadm hstepB (xAllGroups_storeX X))
    (typing_skeleton_carried hb hclaimA hlim hgraph hstepA)

end IxVM.Refinement.Binding
