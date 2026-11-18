import IxVMRefinement.TwinFamily.Step
import IxVMRefinement.TwinFamily.StoreAr
import IxVMRefinement.Assembly.NativeBlockLoads
import IxVMRefinement.Assembly.FoldClause
import IxVMRefinement.L1.Hashed

/-! # The carried clause across the twin record

The twin's unit step (`unitStepTwin_of_installed`) takes the keeping of the prefix invariant and
of the clause beside it across IxC's twin record (`TwinStepKeeps`). This module proves it at
the fold's clause (`FoldExtra`), from the role and record companions of the scoped core after
the step (which the target gives) and one fact about the step's new constants that the twin
record does not carry: each new constant at the key of an address reloads as itself
(`Decl.ReloadsAs`).

Everything else is the twin record's: the arity of the stored terms (`twinKeepsStoreAr`,
`StoreAr.lean`), the model in every set theory (`envModelN_twinStep`), the
store facts (`declStoreInv_twinStep`), the theorems' level parameters (`thmLevels_twinStep`),
the strong store facts and the η facts (the step adds no projection table and no inductive),
the registry (the extension keeps every registered family's reading and adds no inductive), the
store keys (twin recursors at the keys of 32-byte addresses, model copies at derived keys), the
roots (a model copy's root is its twin recursor), η stability, and the load contract (no new
constant is an inductive, a constructor or a projection table, so every load fact but the
reload of a new constant at its key is the prefix's: `newLoads_noFam`).

* `newLoads_noFam`, `etaStable_append_noFam`: the load contract's new part and η stability for
  constants that are no inductive, constructor or projection table;
* `foldClauseWith_twinStep`: the clause after the twin record;
* `twinStepKeeps_foldExtra`: `TwinStepKeeps` at `FoldExtra`. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core (Ctx KKey unresolvedKey ixAddr CIPtrRep W kciEnum addrTy)
open IxVM.Refinement.Decl (twinPosRulesJ)
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (DeclRecTwinRunJ TwinRecPart twinModels twinRecs NativeFam)
open Ix.Kernel.Model (HasModel StoreArR)

set_option linter.unusedVariables false

/-! ## Constants that are no inductive, constructor or projection table -/

/-- **A constant that adds no family**: no inductive, no constructor, no projection table. -/
def NoFamConst (ci : ConstantInfo .anon) : Prop :=
  (∀ cv caps, ci ≠ .indInfo cv caps) ∧ (∀ cv nP nF, ci ≠ .ctorInfo cv nP nF) ∧
    ∀ tbl, ci ≠ .projInfo tbl

/-- **The load facts that reach constants adding no family**: a load at the key of a new
constant is its reload; every other field of `NewLoads` asks of a new inductive, constructor or
table, of which there is none. -/
theorem newLoads_noFam {c : Ctx} {new : List (ConstantInfo .anon)}
    (hnd : (new.map (·.name)).Nodup) (hkind : ∀ ci ∈ new, NoFamConst ci)
    (hreload : ∀ cn ∈ new, ∀ x, cn.name = Core.keyOf c.t x →
      Decl.ReloadsAs c.E c.t (appCtx c new).env cn) :
    NewLoads (appCtx c new).stored new := by
  have nind : ∀ cv caps, ConstantInfo.indInfo cv caps ∉ new :=
    fun cv caps hm => (hkind _ hm).1 cv caps rfl
  have nctor : ∀ cv nP nF, ConstantInfo.ctorInfo cv nP nF ∉ new :=
    fun cv nP nF hm => (hkind _ hm).2.1 cv nP nF rfl
  have nproj : ∀ tbl, ConstantInfo.projInfo tbl ∉ new :=
    fun tbl hm => (hkind _ hm).2.2 tbl rfl
  have nofam : ∀ {b : _root_.Address} {i : Nat}, ¬ FamNew (appCtx c new).stored new b i := by
    intro b i h
    rcases h with ⟨cv, caps, -, hm⟩ | ⟨j, cv, nP, nF, -, hm⟩
    · exact nind cv caps hm
    · exact nctor cv nP nF hm
  have notInduct : ∀ {cn : ConstantInfo .anon} {h' : Heap F}
      {ptr nl ty np ni nc u blk idx : SourceValue F},
      cn ∈ new → CIPtrRep (appCtx c new).stored.κ h' ptr cn →
      loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
        False := by
    intro cn h' ptr nl ty np ni nc u blk idx hm hrep hld
    obtain ⟨v, hv, hci⟩ := hrep
    rw [hld] at hv
    injection hv with hv
    subst hv
    obtain ⟨cv, caps, _, _, _, e, _⟩ := Core.WhnfAux.ind_inv hci
    exact nind cv caps (e ▸ hm)
  have reload : ∀ {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {a : Bytes.Address},
      ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef addrTy h a addr → (∃ cn ∈ new, cn.name = Core.keyOf c.t (ixAddr a)) →
      ∃ cn ∈ new, (appCtx c new).env.find? (Core.keyOf c.t (ixAddr a)) = some cn ∧
        CIPtrRep (appCtx c new).stored.κ h' ptr cn := by
    intro addr ptr h h' cs a ev good ha hn
    obtain ⟨cn, hcn, hname⟩ := hn
    refine ⟨cn, hcn, ?_, hreload cn hcn (ixAddr a) hname addr ptr h h' cs a ev good ha
      hname.symm⟩
    rw [← hname]
    exact Ix.Kernel.Semantics.find?_mem_of_nodup hnd hcn
  exact
    { getCI := by
        intro addr ptr h h' cs a ev good ha hn
        obtain ⟨cn, -, hf, hrep⟩ := reload ev good ha hn
        refine ⟨cn, ?_, hrep⟩
        rw [Ctx.stored_key_of_find hf]
        exact hf
      getCprj := fun bp ptr i j h h' cs b ev hfam _ _ => (nofam hfam).elim
      getIprj := fun bp ptr i h h' cs b ev hfam _ _ => (nofam hfam).elim
      inductRecord := by
        intro addr ptr h h' cs a nl ty np ni nc u blk idx ev hn good ha hld
        obtain ⟨cn, hcn, -, hrep⟩ := reload ev good ha hn
        exact (notInduct hcn hrep hld).elim
      projTables := fun bp ip ptr h h' cs b i _ _ _ _ hfam _ => (nofam hfam).elim
      projTablesAt := fun bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i _ _ _ _ _ _ _ _
        j cvC nP nF _ hm _ => (nctor _ _ _ hm).elim
      unitLike := fun ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc _ _ _ _ _ _ _ _ hm =>
        hm.elim (fun hm => (nind _ _ hm).elim) (fun hm => (nctor _ _ _ hm).elim)
      unitLikeRaw := fun ap ptr h h' cs a nl ty u blk p i b cvT caps _ _ _ _ _ _ hm _ _ _ =>
        (nind _ _ hm).elim
      eta := fun ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1
        _ _ _ _ _ _ _ _ _ _ _ _ _ hm =>
        hm.elim (fun hm => (nctor _ _ _ hm).elim) (fun hm => (nind _ _ hm).elim)
      etaIota := fun pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l
        _ _ _ _ _ _ _ _ _ _ _ hm =>
        hm.elim (fun hm => (nind _ _ hm).elim) (fun hm => (nctor _ _ _ hm).elim)
      inductBlock := by
        intro addr ptr h h' cs a b nl ty np ni nc u blk i ev hn good ha hld _
        obtain ⟨cn, hcn, -, hrep⟩ := reload ev good ha hn
        exact (notInduct hcn hrep hld).elim
      projCtorTele := fun bp ip ptr h h' cs b i _ _ _ _ j cvC nP nF tbl _ _ hm =>
        hm.elim (fun hm => (nctor _ _ _ hm).elim) (fun hm => (nproj _ hm).elim)
      projFire := fun k tbl hm _ _ => (nproj _ hm).elim
      ctorIndRes := fun b i j cv nP nF _ _ hm => (nctor _ _ _ hm).elim }

/-- **η stability after constants that add no family**: an η family and its constructor stored
after the step are the prefix's. -/
theorem etaStable_append_noFam {env : Ix.Kernel.Env .anon} (h : Decl.EtaStable env)
    {new : List (ConstantInfo .anon)} (hext : Ix.Kernel.EnvExt env ⟨new ++ env.consts⟩)
    (hkind : ∀ ci ∈ new, NoFamConst ci) : Decl.EtaStable ⟨new ++ env.consts⟩ := by
  intro T kc cvT cvc caps nP nF hT heta hkc hC env' hext'
  have hold : ∀ {k : KKey} {x : ConstantInfo .anon},
      (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some x → x ∉ new →
        env.find? k = some x :=
    fun hf hn => (find?_append_cases new hf).resolve_left hn
  exact h T kc cvT cvc caps nP nF (hold hT fun hm => (hkind _ hm).1 cvT caps rfl) heta hkc
    (hold hC fun hm => (hkind _ hm).2.1 cvc nP nF rfl) env' (hext.trans hext')

/-! ## The clause after the twin record -/

section Clause

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {E : Ixon.Env} {lim : Option Nat} {env env₂ : Ix.Kernel.Env .anon}
  {Reg : NativeFam .anon → Prop}

/-- **The fold's clause after a twin record** (module docstring), from the clause before, the
block's names at the keys of 32-byte addresses, the arity facts after the step, the companions
after the step, and the reload of each new constant at the key of an address. -/
theorem foldClauseWith_twinStep (hL : LinkLaws L) (h : FoldClauseWith.{u} L t E lim env Reg)
    {blk : List (ConstantInfo .anon)} (hrun : DeclRecTwinRunJ twinPosRulesJ env blk env₂)
    (hkeys : ∀ ci ∈ blk, ∃ x : _root_.Address, ci.name = keyOf t x ∧ x.hash.size = 32)
    (hAr : StoreArR env₂) (hcomp : Decl.CoreCompanions ⟨E, env₂, t, lim⟩)
    (hreload : ∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
      ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) :
    FoldClauseWith.{u} L t E lim env₂ Reg := by
  have hext : Ix.Kernel.EnvExt env env₂ := Ix.Kernel.Semantics.declRecTwinRunJ_envExt hrun
  have hDS : Decl.DeclStoreInv env₂ :=
    declStoreInv_twinStep hrun (Decl.declStoreInv_of_foldStoreInv h.foldStore)
  have hTL : Ix.Kernel.ThmLevels env₂ := thmLevels_twinStep hrun h.thmLevels
  have hstrong : Decl.StrongEnvProps env₂ :=
    Decl.strongEnvProps_step_noProj hext.find h.strong
      (Ix.Kernel.Model.twin_newSat (Q := Ix.Kernel.Model.NotProj)
        (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hrun)
  have heta := Decl.etaShape_step_noEta hext h.etaCtorStored h.etaShape
    (Ix.Kernel.Model.twin_newSat (Q := Decl.NoEtaInd)
      (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) hrun)
  have hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V],
      Ix.Kernel.Model.EnvModelN V .verified env₂ Reg :=
    fun V _ => envModelN_twinStep hrun V (h.model V)
  obtain ⟨ws, henv, hnd, hfr, hnames, hrecs, hmods⟩ := twinRun_parts hrun
  subst henv
  have hrecKey : ∀ ci ∈ twinRecs ws,
      ∃ x : _root_.Address, ci.name = keyOf t x ∧ x.hash.size = 32 := by
    intro ci hci
    have hm : ci.name ∈ blk.map (·.name) := by
      rw [← hnames]
      exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    obtain ⟨ci₀, hci₀, he⟩ := List.mem_map.mp hm
    obtain ⟨x, hx, hsz⟩ := hkeys ci₀ hci₀
    exact ⟨x, he.symm.trans hx, hsz⟩
  have hrecBase : ∀ ci ∈ twinRecs ws, ci.name.base = ci.name := by
    intro ci hci
    obtain ⟨x, hx, -⟩ := hrecKey ci hci
    rw [hx]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t x)
  have hkind : ∀ ci ∈ twinRecs ws ++ twinModels ws, NoFamConst ci := by
    intro ci hci
    rcases List.mem_append.mp hci with hr | hm
    · obtain ⟨cv, mI, rP, rules, rfl⟩ := hrecs ci hr
      unfold NoFamConst
      refine ⟨fun a b h => ?_, fun a b d h => ?_, fun a h => ?_⟩ <;> cases h
    · obtain ⟨-, -, -, cv, v, hint, rfl⟩ := hmods ci hm
      unfold NoFamConst
      refine ⟨fun a b h => ?_, fun a b d h => ?_, fun a h => ?_⟩ <;> cases h
  have hnres : ∀ cn ∈ twinRecs ws ++ twinModels ws, cn.name ≠ unresolvedKey := by
    intro cn hcn
    rcases List.mem_append.mp hcn with hr | hm
    · obtain ⟨x, hx, -⟩ := hrecKey cn hr
      rw [hx]
      exact (Core.Resolved.ne : Core.keyOf t x ≠ unresolvedKey)
    · obtain ⟨ci', -, hk, -⟩ := hmods cn hm
      rw [hk]
      intro he
      injection he with h1 h2
      cases h2
  have hold : ∀ {k : KKey} {x : ConstantInfo .anon},
      (⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some x →
        x ∉ twinRecs ws ++ twinModels ws → env.find? k = some x :=
    fun hf hn => (find?_append_cases _ hf).resolve_left hn
  have hkeyed : HashKeyed t ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ := by
    refine HashKeyed.append h.tableWf h.hashKeyed fun ci hci => ?_
    rcases List.mem_append.mp hci with hr | hm
    · exact Or.inl (hrecKey ci hr)
    · obtain ⟨ci', -, hk, -⟩ := hmods ci hm
      exact Or.inr fun y he => keyOf_nonAux t y ci'.name .model (he.symm.trans hk)
  have haux : Decl.AuxRootSynced ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ := by
    refine h.auxRoot.of_prepend fun ci hci => ?_
    rcases List.mem_append.mp hci with hr | hm
    · rw [hrecBase ci hr]
      exact Decl.env_find?_isSome_of_mem_prefix hci
    · obtain ⟨ci', hci', hk, -⟩ := hmods ci hm
      rw [hk]
      show (Ix.Kernel.Env.find? _ ci'.name.base).isSome = true
      rw [hrecBase ci' hci']
      exact Decl.env_find?_isSome_of_mem_prefix (List.mem_append_left _ hci')
  have hunres : (⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      unresolvedKey = none := by
    cases hf : (⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
        unresolvedKey with
    | none => rfl
    | some ci =>
      rcases find?_append_cases _ hf with hm | ho
      · exact absurd (Core.WhnfAux.name_of_find hf) (hnres ci hm)
      · rw [h.unresolved] at ho
        cases ho
  have hloads := storedLoads_append (c := ⟨E, env, t, lim⟩) h.loads hext hnres h.etaStable
    (newLoads_noFam hnd hkind fun cn hcn x hx =>
      hreload cn (Ix.Kernel.Semantics.find?_mem_of_nodup hnd hcn) (hfr cn hcn) x
        (hx.trans (LoadedReads.keyOf_eq t x)))
  exact
    { model := hmodel
      store := hDS.store
      recShape := hDS.recShape
      recK := hDS.recK
      thmTyped := hDS.thmTyped
      etaTowers := hDS.etaTowers
      thmLevels := hTL
      storeArR := hAr
      strong := hstrong
      fams := fun f hf => (h.fams f hf).ext hL hext
      complete := fun P cm ip cv caps hf hr hcm hinfo hnat =>
        h.complete P cm ip cv caps (hold hf fun hm => (hkind _ hm).1 cv caps rfl) hr hcm hinfo
          hnat
      hashKeyed := hkeyed
      auxRoot := haux
      etaCtorStored := heta.1
      etaShape := heta.2
      etaStable := etaStable_append_noFam h.etaStable hext hkind
      unresolved := hunres
      tableWf := h.tableWf
      companions := hcomp
      loads := hloads }

end Clause

/-! ## The keeping the twin's step takes -/

/-- **The keeping of the fold's clause across the twin record**, from,
at every environment the twin's step is handed, the reload of each new constant at the key of
an address (the companions after the step are the target's). -/
theorem twinStepKeeps_foldExtra {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} (hsz : ∀ x, ConstAddrOf A c x → x.hash.size = 32)
    (hreload : ∀ (env env₂ : Ix.Kernel.Env .anon) (blk : List (ConstantInfo .anon)),
      Decl.PrefixInv.{u} E t lim env → TwinDeclReads t E₀ A c blk →
      DeclRecTwinRunJ twinPosRulesJ env blk env₂ →
      (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
      ∀ ci, env₂.find? ci.name = some ci → env.find? ci.name = none →
        ∀ x, ci.name = keyOf t x → Decl.ReloadsAs E t env₂ ci) :
    TwinStepKeeps.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c := by
  intro env env₂ blk hext hnd hinv hX href hfresh hreads hrun hstored hmodel hcomp
  obtain ⟨⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hC : FoldClauseWith.{u} L t E lim env Reg :=
    FoldClauseWith.of_prefix hinv hR hkeys haux hlv
  have hkeyed : ∀ ci ∈ blk, ∃ x : _root_.Address, ci.name = keyOf t x ∧ x.hash.size = 32 := by
    intro ci hci
    obtain ⟨x, hx, hn, -⟩ := hreads.2.1 ci hci
    exact ⟨x, hn, hsz x hx⟩
  have hC' : FoldClauseWith.{u} L t E lim env₂ Reg :=
    foldClauseWith_twinStep hL hC hrun hkeyed (twinKeepsStoreAr env env₂ blk hrun hC.storeArR)
      hcomp (hreload env env₂ blk hinv hreads hrun hstored)
  exact ⟨hC'.prefixInv, hC'.extra⟩

/-- **A constant address of a block record is the key of a 32-byte address**: it is the BLAKE3
address of a projection record. -/
theorem constAddr_hash_size_of_block {A : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hmuts : c.info = .muts ms) {x : _root_.Address}
    (hx : ConstAddrOf A c x) : x.hash.size = 32 := by
  have hb : ∀ b : ByteArray, (Address.blake3Pure b).hash.size = 32 := by
    intro b
    cases b with
    | mk arr =>
      have h := L1.blake3Pure_eq arr.toList
      simp only [Array.toArray_toList] at h
      rw [h]
      exact (Blake3.Pure.digest arr.toList).size_toArray
  rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, -, -, hxm | ⟨ind, j, -, -, hxc⟩⟩
  · exact (standalone_not_block hs ⟨ms, hmuts⟩).elim
  · rw [hxm]
    exact hb _
  · rw [hxc]
    exact hb _

end IxVM.Refinement.Typing.TwinFamily
