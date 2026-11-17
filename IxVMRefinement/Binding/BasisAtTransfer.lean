import IxVMRefinement.Binding.Defs

/-! # The load contract of a prefix under another role table

The scoped load contract `Core.ScopedLoadFacts` of a prefix context (`Core.Ctx.stored`) reads
the role table through the context's keying, which resolves exactly the addresses whose key
the environment stores (and the markers of those addresses), through `roleRes`, and through
the guard's role context. Two tables whose keys agree wherever the environment stores one
(`KeysAgree`) give keyings that agree at every address that is no marker and resolve the same
addresses. So every field of the contract but `roleRes` and the guard carries over from one
table to the other (`scopedLoadFacts_table`).

* `ciRep_rekey_off`: a loaded constant represented under one keying is represented under
  another that agrees with it off the markers and permits the same projections (the markers'
  keys are read only through their resolution).
* `KeysAgree`, `KeysAgree.key_nm`, `KeysAgree.unres`, `KeysAgree.key_find`: the two prefix
  keyings agree off the markers, resolve the same addresses, and agree where the environment
  stores.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-! ## Represented constants under a keying that agrees off the markers -/

/-- **A loaded constant under another keying** that agrees with the first at every address
that is no marker and permits the projections the first permits. -/
theorem ciRep_rekey_off {κ₁ κ₂ : _root_.Address → Core.KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (rep : Core.CIRep κ₁ h v ci)
    (nm : ∀ x, ¬ Core.IsProjMarker x → κ₂ x = κ₁ x)
    (perm : ∀ a, Core.ProjPermitted κ₁ a → Core.ProjPermitted κ₂ a) :
    Core.CIRep κ₂ h v ci := by
  have ag : ∀ {p : SourceValue F} (a : Bytes.Address), Core.AddrIn h p a →
      κ₂ (Core.ixAddr a) = κ₁ (Core.ixAddr a) := fun a _ => nm _ (Core.ixAddr_not_marker a)
  have pm : ∀ {p : SourceValue F} (a : Bytes.Address), Core.ProjIn h p a →
      Core.ProjPermitted κ₁ (Core.ixAddr a) → Core.ProjPermitted κ₂ (Core.ixAddr a) :=
    fun a _ => perm _
  cases rep with
  | axio hv => exact .axio (hv.rekey ag pm)
  | opaq hv => exact .opaq (hv.rekey ag pm)
  | defn hv hV => exact .defn (hv.rekey ag pm) (Core.TmC.rekey hV ag pm)
  | thm hv hV => exact .thm (hv.rekey ag pm) (Core.TmC.rekey hV ag pm)
  | quot hv hk => exact .quot (hv.rekey ag pm) hk
  | induct hv hcounts hkey =>
    obtain ⟨b, i, hb, hidx, hname⟩ := hkey
    exact .induct (hv.rekey ag pm) hcounts
      ⟨b, i, hb, hidx, hname.trans (nm _ (Core.iprjAddr_not_marker _ _)).symm⟩
  | ctor hv hnp hnf hcounts hkey =>
    obtain ⟨b, i, j, hb, hind, hcidx, hname⟩ := hkey
    exact .ctor (hv.rekey ag pm) hnp hnf hcounts
      ⟨b, i, j, hb, hind, hcidx, hname.trans (nm _ (Core.cprjAddr_not_marker _ _ _)).symm⟩
  | recr hv hnp hni hnm hnmi hrP hmI hcounts hrules hk hkey =>
    obtain ⟨b, i, hb, hidx, hname⟩ := hkey
    refine .recr (hv.rekey ag pm) hnp hni hnm hnmi hrP hmI hcounts
      (hrules.rekey (fun a => perm _) fun a _ => nm _ (Core.ixAddr_not_marker a)) hk
      ⟨b, i, hb, hidx, ?_⟩
    rcases hname with hname | hname
    · exact .inl (hname.trans (nm _ (Core.ixAddr_not_marker _)).symm)
    · exact .inr (hname.trans
        (nm (Core.rprjAddr (Core.ixAddr b) (ZMod.val i)) (Core.projAddr_not_marker _)).symm)

theorem ciPtrRep_rekey_off {κ₁ κ₂ : _root_.Address → Core.KKey} {h : Heap F}
    {p : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon} (rep : Core.CIPtrRep κ₁ h p ci)
    (nm : ∀ x, ¬ Core.IsProjMarker x → κ₂ x = κ₁ x)
    (perm : ∀ a, Core.ProjPermitted κ₁ a → Core.ProjPermitted κ₂ a) :
    Core.CIPtrRep κ₂ h p ci := by
  obtain ⟨v, hld, hr⟩ := rep
  exact ⟨v, hld, ciRep_rekey_off hr nm perm⟩

/-! ## Two tables whose keys agree where the environment stores -/

/-- **The keys of `t₁` and `t₂` agree wherever `env` stores one of them.** -/
def KeysAgree (env : Ix.Kernel.Env .anon) (t₁ t₂ : Ix.Kernel.RoleTable) : Prop :=
  ∀ x ci, env.find? (Core.keyOf t₁ x) = some ci ∨ env.find? (Core.keyOf t₂ x) = some ci →
    Core.keyOf t₁ x = Core.keyOf t₂ x

section KeysAgree

variable {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {t₁ t₂ : Ix.Kernel.RoleTable}
  {lim : Option Nat}

theorem KeysAgree.find (hk : KeysAgree env t₁ t₂) (x : _root_.Address) :
    env.find? (Core.keyOf t₁ x) = env.find? (Core.keyOf t₂ x) := by
  cases h1 : env.find? (Core.keyOf t₁ x) with
  | some ci =>
    exact h1.symm.trans (congrArg (fun k => env.find? k) (hk x ci (Or.inl h1)))
  | none =>
    cases h2 : env.find? (Core.keyOf t₂ x) with
    | none => rfl
    | some ci =>
      rw [hk x ci (Or.inr h2), h2] at h1
      cases h1

theorem KeysAgree.resolves (hk : KeysAgree env t₁ t₂) (x : _root_.Address) :
    Core.Ctx.resolvesOver ⟨E, env, t₁, lim⟩ env x ↔
      Core.Ctx.resolvesOver ⟨E, env, t₂, lim⟩ env x := by
  show ((∃ ci, env.find? (Core.keyOf t₁ x) = some ci) ∨
      ∃ y, x = Core.projMarker y ∧ ∃ ci, env.find? (Core.keyOf t₁ y) = some ci) ↔
    ((∃ ci, env.find? (Core.keyOf t₂ x) = some ci) ∨
      ∃ y, x = Core.projMarker y ∧ ∃ ci, env.find? (Core.keyOf t₂ y) = some ci)
  simp only [hk.find]

theorem stored_κ_eq (t : Ix.Kernel.RoleTable) (x : _root_.Address) :
    (Core.Ctx.stored ⟨E, env, t, lim⟩).κ x =
      Core.resKey t (Core.Ctx.resolvesOver ⟨E, env, t, lim⟩ env) x := rfl

/-- **The two prefix keyings agree at every address that is no marker.** -/
theorem KeysAgree.key_nm (hk : KeysAgree env t₁ t₂) {x : _root_.Address}
    (hx : ¬ Core.IsProjMarker x) :
    (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ x = (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ x := by
  rw [stored_κ_eq, stored_κ_eq]
  by_cases hr : Core.Ctx.resolvesOver ⟨E, env, t₁, lim⟩ env x
  · have hr2 := (hk.resolves (E := E) (lim := lim) x).mp hr
    rw [Core.resKey_of_res hr, Core.resKey_of_res hr2]
    rcases hr with ⟨ci, hci⟩ | ⟨y, hy, -⟩
    · exact (hk x ci (Or.inl hci)).symm
    · exact (hx ⟨y, hy⟩).elim
  · have hr2 : ¬ Core.Ctx.resolvesOver ⟨E, env, t₂, lim⟩ env x :=
      fun h2 => hr ((hk.resolves (E := E) (lim := lim) x).mpr h2)
    rw [Core.resKey_of_not_res hr, Core.resKey_of_not_res hr2]

/-- **The two prefix keyings resolve the same addresses.** -/
theorem KeysAgree.unres (hk : KeysAgree env t₁ t₂) (x : _root_.Address) :
    (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ x = Core.unresolvedKey ↔
      (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ x = Core.unresolvedKey := by
  rw [stored_κ_eq, stored_κ_eq]
  by_cases hr : Core.Ctx.resolvesOver ⟨E, env, t₁, lim⟩ env x
  · have hr2 := (hk.resolves (E := E) (lim := lim) x).mp hr
    rw [Core.resKey_of_res hr, Core.resKey_of_res hr2]
    exact ⟨fun e => absurd e Core.Resolved.ne, fun e => absurd e Core.Resolved.ne⟩
  · have hr2 : ¬ Core.Ctx.resolvesOver ⟨E, env, t₂, lim⟩ env x :=
      fun h2 => hr ((hk.resolves (E := E) (lim := lim) x).mpr h2)
    rw [Core.resKey_of_not_res hr, Core.resKey_of_not_res hr2]

/-- **The two prefix keyings agree where the environment stores.** -/
theorem KeysAgree.key_find (hk : KeysAgree env t₁ t₂) {x : _root_.Address}
    {ci : Ix.Kernel.ConstantInfo .anon}
    (hf : env.find? ((Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ x) = some ci) :
    (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ x = (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ x := by
  rw [stored_κ_eq] at hf
  rw [stored_κ_eq, stored_κ_eq]
  by_cases hr2 : Core.Ctx.resolvesOver ⟨E, env, t₂, lim⟩ env x
  · rw [Core.resKey_of_res hr2] at hf
    have e := hk x ci (Or.inr hf)
    have hr : Core.Ctx.resolvesOver ⟨E, env, t₁, lim⟩ env x :=
      Or.inl ⟨ci, (congrArg (fun k => env.find? k) e).trans hf⟩
    rw [Core.resKey_of_res hr, Core.resKey_of_res hr2]
    exact e.symm
  · have hr : ¬ Core.Ctx.resolvesOver ⟨E, env, t₁, lim⟩ env x :=
      fun h1 => hr2 ((hk.resolves (E := E) (lim := lim) x).mp h1)
    rw [Core.resKey_of_not_res hr, Core.resKey_of_not_res hr2]

theorem KeysAgree.perm (hk : KeysAgree env t₁ t₂) (a : _root_.Address)
    (h : Core.ProjPermitted (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ a) :
    Core.ProjPermitted (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ a :=
  ⟨fun e => h.ne ((hk.unres _).mp e)⟩

theorem KeysAgree.permBack (hk : KeysAgree env t₁ t₂) (a : _root_.Address)
    (h : Core.ProjPermitted (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ a) :
    Core.ProjPermitted (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ a :=
  ⟨fun e => h.ne ((hk.unres _).mpr e)⟩

theorem KeysAgree.ptrRep (hk : KeysAgree env t₁ t₂) {hp : Heap F} {p : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon}
    (h : Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ hp p ci) :
    Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ hp p ci :=
  ciPtrRep_rekey_off h (fun _ hx => hk.key_nm hx) (fun a => hk.perm a)

theorem KeysAgree.famAt (hk : KeysAgree env t₁ t₂) {b : _root_.Address} {i : Nat}
    (h : (Core.Ctx.stored ⟨E, env, t₂, lim⟩).FamAt b i) :
    (Core.Ctx.stored ⟨E, env, t₁, lim⟩).FamAt b i := by
  rcases h with ⟨cv, caps, hf⟩ | ⟨j, cv, nP, nF, hf⟩
  · rw [hk.key_nm (Core.iprjAddr_not_marker b i)] at hf
    exact Or.inl ⟨cv, caps, hf⟩
  · rw [hk.key_nm (Core.cprjAddr_not_marker b i j)] at hf
    exact Or.inr ⟨j, cv, nP, nF, hf⟩

end KeysAgree

/-! ## The load contract under another table -/

/-- **The load contract of a prefix under another role table** whose keys agree with the
first's wherever the environment stores: every field but `roleRes` and the guard carries
over. -/
theorem scopedLoadFacts_table {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {t₁ t₂ : Ix.Kernel.RoleTable} {lim : Option Nat} (hk : KeysAgree env t₁ t₂)
    (h : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env, t₁, lim⟩))
    (hres : RoleResAt (Core.Ctx.stored ⟨E, env, t₂, lim⟩))
    (hguard : ProjGuard (Core.Ctx.stored ⟨E, env, t₂, lim⟩)) :
    Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env, t₂, lim⟩) := by
  have hI : ∀ a : Bytes.Address, (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ (Core.ixAddr a) =
      (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ (Core.ixAddr a) :=
    fun a => hk.key_nm (Core.ixAddr_not_marker a)
  have hIP : ∀ (b : _root_.Address) (i : Nat),
      (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ (Core.iprjAddr b i) =
        (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ (Core.iprjAddr b i) :=
    fun b i => hk.key_nm (Core.iprjAddr_not_marker b i)
  have hCP : ∀ (b : _root_.Address) (i j : Nat),
      (Core.Ctx.stored ⟨E, env, t₂, lim⟩).κ (Core.cprjAddr b i j) =
        (Core.Ctx.stored ⟨E, env, t₁, lim⟩).κ (Core.cprjAddr b i j) :=
    fun b i j => hk.key_nm (Core.cprjAddr_not_marker b i j)
  exact {
    getCI := by
      intro addr ptr h₀ h₁ cs a ev hal hne hg ha
      rw [hI] at hne ⊢
      obtain ⟨ci, hf, hr⟩ := h.getCI addr ptr h₀ h₁ cs a ev hal hne
        ⟨hg.noCollision, hg.bounded, hg.allAllowed⟩ ha
      exact ⟨ci, hf, hk.ptrRep hr⟩
    getCprj := by
      intro bp ptr i j h₀ h₁ cs b ev hal hfm hg hb
      obtain ⟨⟨ci₀, hr₀⟩, hall⟩ := h.getCprj bp ptr i j h₀ h₁ cs b ev hal (hk.famAt hfm)
        ⟨hg.noCollision, hg.bounded, hg.allAllowed⟩ hb
      refine ⟨⟨ci₀, hk.ptrRep hr₀⟩, fun cv nP nF hf => ?_⟩
      rw [hCP] at hf
      exact hk.ptrRep (hall cv nP nF hf)
    getIprj := by
      intro bp ptr i h₀ h₁ cs b ev hal hfm hg hb
      obtain ⟨ci, hf, hr⟩ := h.getIprj bp ptr i h₀ h₁ cs b ev hal (hk.famAt hfm)
        ⟨hg.noCollision, hg.bounded, hg.allAllowed⟩ hb
      rw [hIP]
      exact ⟨ci, hf, hk.ptrRep hr⟩
    indRecord := h.indRecord
    inductRecord := by
      intro addr ptr h₀ h₁ cs a nl ty np ni nc u blk idx ev hal hne hg ha hld
      rw [hI] at hne
      exact h.inductRecord addr ptr h₀ h₁ cs a nl ty np ni nc u blk idx ev hal hne hg ha hld
    projTables := by
      intro bp ip ptr h₀ h₁ cs b i ev hal hg hb hip hfm hpm
      obtain ⟨⟨ci, hf, hr⟩, hrest⟩ := h.projTables bp ip ptr h₀ h₁ cs b i ev hal hg hb hip
        (hk.famAt hfm) (hk.permBack _ hpm)
      refine ⟨⟨ci, by rw [hCP]; exact hf, hk.ptrRep hr⟩, ?_⟩
      intro sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hctor hstrip
      rw [hCP] at hctor
      rw [hIP, hCP]
      exact hrest sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hctor
        hstrip
    projTablesAt := by
      intro bp sap ptr nl ty np u blk h₀ h₁ h1 h2 cs cs1 b s i evM gM hb evG gG hs hld hblk
        j cvC nP nF hctor hnF
      rw [hCP] at hctor
      rw [hIP, hCP]
      exact h.projTablesAt bp sap ptr nl ty np u blk h₀ h₁ h1 h2 cs cs1 b s i evM gM hb evG gG
        hs hld hblk j cvC nP nF hctor hnF
    unitLike := by
      intro ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps cvC nPc ev hg ha hld hb hfind hfew hfC
      rw [hI] at hfind ⊢
      rw [hCP] at hfC
      exact h.unitLike ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps cvC nPc ev hg ha hld hb
        hfind hfew hfC
    unitLikeRaw := by
      intro ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps ev hal hne hg ha hld hb hfind hfew hz
        hnr
      rw [hI] at hne hfind ⊢
      exact h.unitLikeRaw ap ptr h₀ h₁ cs a nl ty u blk p i b cvT caps ev hal hne hg ha hld hb
        hfind hfew
        ⟨hz.bp, hz.ptr, hz.before, hz.after, hz.calls, hz.observed, hz.allowed, hz.good,
          hz.blockRep, hz.zeroFields⟩
        ⟨hnr.ap, hnr.before, hnr.after, hnr.calls, hnr.observed, hnr.allowed, hnr.good,
          hnr.parentRep⟩
    eta := by
      intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1 hC hname
        hpos ev good hb hld hT hmod hsort hnz hrec haddr
      rw [hI] at hC ⊢
      rw [hCP] at hname
      rw [hIP] at hT ⊢
      exact h.eta ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1 hC
        hname hpos ev good hb hld hT hmod hsort hnz hrec haddr
    etaIota := by
      intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev good hpa hld hblk
        hT hC hmul hrec hsort hnz
      rw [hI] at hT ⊢
      rw [hCP] at hC ⊢
      exact h.etaIota pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev good
        hpa hld hblk hT hC hmul hrec hsort hnz
    recordShape := h.recordShape
    inductBlock := by
      intro addr ptr h₀ h₁ cs a b nl ty np ni nc u blk i ev hal hne hg ha hld hblk
      rw [hI] at hne
      exact h.inductBlock addr ptr h₀ h₁ cs a b nl ty np ni nc u blk i ev hal hne hg ha hld hblk
    projTablesGuard := hguard
    canonical := h.canonical
    storedRes := fun a ci hf => by
      rw [Core.Ctx.stored_key_of_find (c := ⟨E, env, t₂, lim⟩) hf]
      exact Core.Resolved.ne
    findRes := fun a ci hf => by
      have e := hk.key_find hf
      rw [e] at hf ⊢
      exact h.findRes a ci hf
    ctorIndRes := fun b i j cv nP nF hb hf => by
      rw [hCP] at hf
      rw [hIP]
      exact h.ctorIndRes b i j cv nP nF hb hf
    ctorIndPerm := fun a b i j cvT caps cv nP nF hb hf hn hc => by
      have e := hk.key_find hf
      rw [e] at hf
      rw [hIP] at hn
      rw [hCP] at hc
      exact hk.perm _ (h.ctorIndPerm a b i j cvT caps cv nP nF hb hf hn hc)
    roleRes := hres }

end IxVM.Refinement.Binding
