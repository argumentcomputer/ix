import IxVMRefinement.Assembly.PointNewLoads
import IxVMRefinement.Assembly.PointUseSites
import IxVMRefinement.Assembly.NativeBlockStage

/-! # The constructor stage of a block on the constructors-only route

Each constructor type of a modeled block is checked while every former of the block is
loadable: at the stage `Decl.Point.stage env formers` (the prefix with the formers stored at the
empty capability record), under the keying of the stage over the prefix
(`Ctx.stagedOver env`: what the stage stores resolves; a projection is permitted only at the
prefix's addresses). This file gives that stage's scoped core facts.

* `stagedLoads_append_formers`: the load contract of a stage that stores a list of inductives in
  front of a prefix, from the prefix's contract and the load facts at the new inductives
  (`FormersLoads`): the generalisation of `Decl.stagedLoads_cons_former` from one former to a
  list. Every clause that does not reach a new inductive is the prefix's; a projection is never
  permitted at a new inductive, and no constructor is new.
* `PointStageInput`: the block record's facts the point stage reads (the former half of
  `PointReads`, the formers' front doors, and the record facts of `PointInstall`).
* `PointStageInput.formersLoads`: the load facts at the formers, from the block record. A load at a
  former's key represents the former under the stage's keying (the canonical annotation of its
  reading, at the empty capability record); a unit-like raw load at a former is refuted by the
  block's shape (`PointShape`).
* `pointStage_envFacts`: the environment half, from the fold's store invariant along the formers'
  run (`Decl.Point.formers_run`, `foldStoreInv_run`) and the companions (no recursor is stored).
* `pointStage_coreFacts`: both halves.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

section Generic

open IxVM.Refinement.Core

/-- **The context of a stage that stores the constants `newF` in front of the prefix `c`**, keyed
over the prefix: what the stage stores resolves, and a projection is permitted at the addresses
the prefix stores. -/
noncomputable abbrev formersStage (c : Ctx) (newF : List (ConstantInfo .anon)) : ScopedCtx :=
  (appCtx c newF).stagedOver c.env

/-- **The load facts at the staged inductives**: the clauses of the stage's load contract at the
key of a new inductive, which are facts about the block's records and are not derived from the
prefix (the list analogue of `Decl.FormerLoads`). The unit-like raw clause is stated as refuted:
the stage's inductives are never asked for it. -/
structure FormersLoads (c : Ctx) (newF : List (ConstantInfo .anon)) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr →
    ∀ (cv : ConstantVal .anon) (caps : IndCaps .anon), ConstantInfo.indInfo cv caps ∈ newF →
      keyOf c.t (ixAddr a) = cv.name →
      CIPtrRep (formersStage c newF).κ h' ptr (.indInfo cv caps)
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp →
    ∀ (cv : ConstantVal .anon) (caps : IndCaps .anon), ConstantInfo.indInfo cv caps ∈ newF →
      keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cv.name →
      CIPtrRep (formersStage c newF).κ h' ptr (.indInfo cv caps)
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp →
    (∃ y ∈ newF, y.name = keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i))) →
    ∃ ci₀, CIPtrRep (formersStage c newF).κ h' ptr ci₀
  inductRecord : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty np ni nc u blk idx : SourceValue F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr → (∃ y ∈ newF, y.name = keyOf c.t (ixAddr a)) →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (ixAddr a) = some cm ∧ Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩
  inductBlock : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a b : Bytes.Address) (nl ty np ni nc u blk : SourceValue F) (i : F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr → (∃ y ∈ newF, y.name = keyOf c.t (ixAddr a)) →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    ∃ (cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt c.E (ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind)
  unitLikeRaw : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a ap → (∃ y ∈ newF, y.name = keyOf c.t (ixAddr a)) →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk → FewInductives c (ixAddr b) →
    ZeroFieldCtorLoad (formersStage c newF) b i → NonrecursiveLoad (formersStage c newF) a →
    False

/-- **The load contract of a stage that stores inductives in front of a prefix.** Over a prefix
whose contract holds, storing the inductives `newF` (each at the fresh key of an address that is
no marker, where no marker's key is stored) gives the contract of the stage over the prefix,
given the load facts at the new inductives (`hformer`). -/
theorem stagedLoads_append_formers {c : Ctx} (h₁ : ScopedLoadFacts c.stored)
    {newF : List (ConstantInfo .anon)} (htwf : c.t.wf = true)
    (hind : ∀ y ∈ newF, ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon), y = .indInfo cv caps)
    (haddr : ∀ y ∈ newF, ∃ f : _root_.Address, ¬ IsProjMarker f ∧ y.name = keyOf c.t f)
    (hfresh : ∀ y ∈ newF, c.env.find? y.name = none)
    (hmark : ∀ f : _root_.Address, c.env.find? (keyOf c.t (projMarker f)) = none)
    (hext : Ix.Kernel.EnvExt c.env (appCtx c newF).env) (heta : Decl.EtaStable c.env)
    (hformer : FormersLoads c newF) :
    ScopedLoadFacts (formersStage c newF) := by
  have keep : ∀ x, c.stored.κ x ≠ unresolvedKey →
      (formersStage c newF).κ x = c.stored.κ x := fun x hx =>
    Decl.stagedOver_keep (c₁ := c) (c₂ := appCtx c newF) (pre₁ := c.env) (pre₂ := c.env) rfl
      (fun hf => ⟨_, hext.find hf⟩) (fun hf => ⟨_, hf⟩) x hx
  have newRes : ∀ y ∈ newF, y.name ≠ unresolvedKey := by
    intro y hy
    obtain ⟨f, -, hf⟩ := haddr y hy
    rw [hf]
    exact Resolved.ne
  -- A key some new inductive has is found among the new constants.
  have findNew : ∀ {k : KKey} {y : ConstantInfo .anon}, y ∈ newF → y.name = k →
      ∃ y' ∈ newF, (appCtx c newF).env.find? k = some y' := by
    intro k y hy hk
    have hs := Decl.env_find?_isSome_of_mem_prefix (tail := c.env.consts) hy
    rw [hk] at hs
    obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp hs
    rcases find?_append_cases (env := c.env) newF hy' with hm | ho
    · exact ⟨y', hm, hy'⟩
    · exfalso
      have hn := hfresh y hy
      rw [hk, ho] at hn
      cases hn
  -- An address the stage resolves, one a record can have: a new inductive's or the prefix's.
  have splitKey : ∀ x, ¬ IsProjMarker x → (formersStage c newF).κ x ≠ unresolvedKey →
      (∃ y ∈ newF, y.name = keyOf c.t x) ∨ c.stored.κ x ≠ unresolvedKey := by
    intro x hm h
    obtain ⟨ci, hci⟩ := Ctx.stagedOver_key_ne (c := appCtx c newF) (pre := c.env) h hm
    have hci' : (appCtx c newF).env.find? (keyOf c.t x) = some ci := hci
    rcases find?_append_cases (env := c.env) newF hci' with hn | ho
    · exact Or.inl ⟨ci, hn, WhnfAux.name_of_find hci'⟩
    · exact Or.inr (by rw [Ctx.stored_key_of_find (c := c) ho]; exact Resolved.ne)
  -- A constant the stage stores that is not new is the prefix's, at the same key.
  have old : ∀ {x : _root_.Address} {y : ConstantInfo .anon},
      (formersStage c newF).env.find? ((formersStage c newF).κ x) = some y → y ∉ newF →
      c.env.find? (c.stored.κ x) = some y ∧ (formersStage c newF).κ x = c.stored.κ x := by
    intro x y hf hne
    have hfo : c.env.find? ((formersStage c newF).κ x) = some y := by
      rcases find?_append_cases (env := c.env) newF hf with hm | ho
      · exact absurd hm hne
      · exact ho
    by_cases hr₂ : (formersStage c newF).κ x = unresolvedKey
    · exfalso
      have hr₁ : c.stored.κ x = unresolvedKey := by
        by_contra hr
        exact hr ((keep x hr).symm.trans hr₂)
      rw [hr₂, ← hr₁] at hfo
      exact h₁.findRes x y hfo hr₁
    · have e₂ : (formersStage c newF).κ x = keyOf c.t x := (formersStage c newF).key_eq hr₂
      rw [e₂] at hfo
      have e₁ : c.stored.κ x = keyOf c.t x := Ctx.stored_key_of_find hfo
      exact ⟨by rw [e₁]; exact hfo, e₂.trans e₁.symm⟩
  have ctorOld : ∀ {x : _root_.Address} {cv : ConstantVal .anon} {nP nF : Nat},
      (formersStage c newF).env.find? ((formersStage c newF).κ x) =
        some (.ctorInfo cv nP nF) →
      c.env.find? (c.stored.κ x) = some (.ctorInfo cv nP nF) ∧
        (formersStage c newF).κ x = c.stored.κ x := by
    intro x cv nP nF hf
    refine old hf (fun hm => ?_)
    obtain ⟨cv', caps', e⟩ := hind _ hm
    cases e
  -- A new inductive is stored at its own key only.
  have formerKey : ∀ {x : _root_.Address} {y : ConstantInfo .anon},
      (formersStage c newF).env.find? ((formersStage c newF).κ x) = some y → y ∈ newF →
      keyOf c.t x = y.name := by
    intro x y hf hy
    have hn : y.name = (formersStage c newF).κ x := WhnfAux.name_of_find hf
    have hr : (formersStage c newF).κ x ≠ unresolvedKey := by
      rw [← hn]
      exact newRes y hy
    exact ((formersStage c newF).key_eq hr).symm.trans hn.symm
  -- A key the prefix resolves, at an address a record can have, is no new inductive's.
  have notFormer : ∀ {x : _root_.Address}, ¬ IsProjMarker x → c.stored.κ x ≠ unresolvedKey →
      ∀ y ∈ newF, keyOf c.t x ≠ y.name := by
    intro x hm hr y hy e
    obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hr hm
    rw [e, hfresh y hy] at hci
    cases hci
  -- A load of an address keyed by a new inductive names the member it is the inductive of.
  have formerMember : ∀ {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {a : Bytes.Address} {nl ty np ni nc u blk : SourceValue F} {b : Bytes.Address} {i : F}
      {cv : ConstantVal .anon} {caps : IndCaps .anon},
      ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c cs →
      Bytes.RepAddressRef addrTy h a ap → ConstantInfo.indInfo cv caps ∈ newF →
      keyOf c.t (ixAddr a) = cv.name →
      loadValue h' ptr =
        .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
      Bytes.RepAddressRef addrTy h' b blk →
      keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cv.name := by
    intro ap ptr h h' cs a nl ty np ni nc u blk b i cv caps ev good ha hmem hnew hld hb
    obtain ⟨v, hv, hci⟩ := hformer.getCI ap ptr h h' cs a ev good ha cv caps hmem hnew
    have hv' := Except.ok.inj (hld.symm.trans hv)
    subst hv'
    obtain ⟨cv', caps', nP, nI, nC, e, -, -, -, -, -, -, -, b', i', hb', hidx, hn⟩ :=
      WhnfAux.ind_inv hci
    have e1 : cv = cv' := (ConstantInfo.indInfo.inj e).1
    have hbb : b' = b := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb' hb
    have hii : i = i' := Value.field.inj hidx
    rw [hbb, ← hii, ← e1] at hn
    have hr : (formersStage c newF).κ (iprjAddr (ixAddr b) (ZMod.val i)) ≠ unresolvedKey := by
      rw [← hn]
      exact newRes _ hmem
    exact ((formersStage c newF).key_eq hr).symm.trans hn.symm
  have fam : ∀ {b : _root_.Address} {i : Nat}, (formersStage c newF).FamAt b i →
      (∀ y ∈ newF, keyOf c.t (iprjAddr b i) ≠ y.name) → c.stored.FamAt b i := by
    intro b i hfam hne
    rcases hfam with ⟨cv, caps', hf⟩ | ⟨j, cv, nP, nF, hf⟩
    · refine Or.inl ⟨cv, caps', (old hf fun hm => ?_).1⟩
      exact hne _ hm (formerKey hf hm)
    · exact Or.inr ⟨j, cv, nP, nF, (ctorOld hf).1⟩
  have famPerm : ∀ {b : _root_.Address} {i : Nat}, HashedBlockAt c.E b → c.stored.FamAt b i →
      ProjPermitted c.stored.κ (iprjAddr b i) := by
    intro b i hbh hfam
    have hr : c.stored.κ (iprjAddr b i) ≠ unresolvedKey := by
      rcases hfam with ⟨cv, caps', hf⟩ | ⟨j, cv, nP, nF, hf⟩
      · exact h₁.findRes _ _ hf
      · exact h₁.ctorIndRes _ _ _ _ _ _ hbh hf
    obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hr (iprjAddr_not_marker _ _)
    exact Ctx.stored_projPermitted_of_find hci
  -- No projection is permitted at a new inductive.
  have formerNoProj : ∀ {x : _root_.Address}, (∃ y ∈ newF, y.name = keyOf c.t x) →
      ¬ IsProjMarker x → ¬ ProjPermitted (formersStage c newF).κ x := by
    rintro x ⟨y, hy, hyx⟩ hm
    have hpre : c.env.find? (keyOf c.t x) = none := by
      rw [← hyx]
      exact hfresh y hy
    have hmk : (appCtx c newF).env.find? (keyOf c.t (projMarker x)) = none := by
      cases hf : (appCtx c newF).env.find? (keyOf c.t (projMarker x)) with
      | none => rfl
      | some z =>
        exfalso
        rcases find?_append_cases (env := c.env) newF hf with hz | ho
        · obtain ⟨f, hf₀, hzf⟩ := haddr z hz
          have hzn : z.name = keyOf c.t (projMarker x) := WhnfAux.name_of_find hf
          have hfx : f = projMarker x := keyOf_inj htwf (hzf.symm.trans hzn)
          exact hf₀ ⟨x, hfx⟩
        · rw [hmark x] at ho
          cases ho
    exact Ctx.stagedOver_not_projPermitted (c := appCtx c newF) (pre := c.env) hpre hmk
  have good₁ : ∀ {cs : List (Call F)}, CoreGood (formersStage c newF) cs →
      CoreGood c.stored cs :=
    fun g => ⟨g.noCollision, g.bounded, fun _ _ => trivial⟩
  exact
    { getCI := by
        intro addr ptr h h' cs a ev _ res good ha
        rcases splitKey (ixAddr a) (ixAddr_not_marker a) res with ⟨y, hy, hyn⟩ | hold
        · obtain ⟨y', hy', hf0⟩ := findNew hy hyn
          obtain ⟨cv, caps, rfl⟩ := hind y' hy'
          have hn0 : cv.name = keyOf c.t (ixAddr a) := WhnfAux.name_of_find hf0
          refine ⟨.indInfo cv caps, ?_,
            hformer.getCI addr ptr h h' cs a ev good.raw ha cv caps hy' hn0.symm⟩
          rw [(formersStage c newF).key_eq res]
          exact hf0
        · obtain ⟨ci, hf, hrep⟩ := h₁.getCI addr ptr h h' cs a ev trivial hold (good₁ good) ha
          refine ⟨ci, ?_, hrep.rekey_mono keep (Decl.stored_name_ne h₁ hf)⟩
          rw [keep _ hold]
          exact hext.find hf
      getCprj := by
        intro bp ptr i j h h' cs b ev _ hfam good hb
        by_cases hnew : ∃ y ∈ newF, y.name = keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i))
        · refine ⟨hformer.getCprj bp ptr i j h h' cs b ev good.raw hb hnew,
            fun cv nP nF hf => ?_⟩
          exfalso
          obtain ⟨y, hy, hyn⟩ := hnew
          obtain ⟨hf₁, -⟩ := ctorOld hf
          exact notFormer (iprjAddr_not_marker _ _)
            (h₁.ctorIndRes _ _ _ _ _ _ (L1.hashedBlockAt_of_get_ci_cprj good.raw hb ev) hf₁)
            y hy hyn.symm
        · have hne : ∀ y ∈ newF, keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) ≠ y.name :=
            fun y hy e => hnew ⟨y, hy, e.symm⟩
          obtain ⟨⟨ci₀, hrep₀⟩, hall⟩ :=
            h₁.getCprj bp ptr i j h h' cs b ev trivial (fam hfam hne) (good₁ good) hb
          refine ⟨hrep₀.rekey_exists keep, fun cv nP nF hf => ?_⟩
          obtain ⟨hf₁, -⟩ := ctorOld hf
          exact (hall cv nP nF hf₁).rekey_mono keep (Decl.stored_name_ne h₁ hf₁)
      getIprj := by
        intro bp ptr i h h' cs b ev _ hfam good hb
        by_cases hnew : ∃ y ∈ newF, y.name = keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i))
        · obtain ⟨y, hy, hyn⟩ := hnew
          obtain ⟨y', hy', hf0⟩ := findNew hy hyn
          obtain ⟨cv, caps, rfl⟩ := hind y' hy'
          have hn0 : cv.name = keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) :=
            WhnfAux.name_of_find hf0
          have e : (formersStage c newF).κ (iprjAddr (ixAddr b) (ZMod.val i)) =
              keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) :=
            Ctx.stagedOver_key_of_find (c := appCtx c newF) (pre := c.env) hf0
          refine ⟨.indInfo cv caps, ?_,
            hformer.getIprj bp ptr i h h' cs b ev good.raw hb cv caps hy' hn0.symm⟩
          rw [e]
          exact hf0
        · have hne : ∀ y ∈ newF, keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) ≠ y.name :=
            fun y hy e => hnew ⟨y, hy, e.symm⟩
          obtain ⟨ci, hf, hrep⟩ :=
            h₁.getIprj bp ptr i h h' cs b ev trivial (fam hfam hne) (good₁ good) hb
          refine ⟨ci, ?_, hrep.rekey_mono keep (Decl.stored_name_ne h₁ hf)⟩
          rw [keep _ (h₁.findRes _ _ hf)]
          exact hext.find hf
      indRecord := h₁.indRecord
      inductRecord := by
        intro addr ptr h h' cs a nl ty np ni nc u blk idx ev _ res good ha hld
        rcases splitKey (ixAddr a) (ixAddr_not_marker a) res with hnew | hold
        · exact hformer.inductRecord addr ptr h h' cs a nl ty np ni nc u blk idx ev good ha hnew
            hld
        · exact h₁.inductRecord addr ptr h h' cs a nl ty np ni nc u blk idx ev trivial hold good
            ha hld
      projTables := by
        intro bp ip ptr h h' cs b i ev _ good hb hip hfam hperm
        by_cases hnew : ∃ y ∈ newF, y.name = keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i))
        · exact absurd hperm (formerNoProj hnew (iprjAddr_not_marker _ _))
        · have hne : ∀ y ∈ newF, keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) ≠ y.name :=
            fun y hy e => hnew ⟨y, hy, e.symm⟩
          obtain ⟨⟨ci, hf, hrep⟩, htab⟩ :=
            h₁.projTables bp ip ptr h h' cs b i ev trivial good hb hip (fam hfam hne)
              (famPerm (L1.hashedBlockAt_of_proj_ctor good ev hb hip) (fam hfam hne))
          refine ⟨⟨ci, ?_, hrep.rekey_mono keep (Decl.stored_name_ne h₁ hf)⟩, ?_⟩
          · rw [keep _ (h₁.findRes _ _ hf)]
            exact hext.find hf
          · intro sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hctor' hbind
            obtain ⟨hc₁, ek⟩ := ctorOld hctor'
            obtain ⟨tbl, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11⟩ :=
              htab sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hc₁ hbind
            have ei := keep _
              (h₁.ctorIndRes _ _ _ _ _ _ (L1.hashedBlockAt_of_proj_ctor good ev hb hip) hc₁)
            refine ⟨tbl, ?_, ?_, ?_, ht4, ht5, ht6, ht7, ?_, ht9, ht10, ht11⟩
            · rw [ei]
              exact hext.find ht1
            · rw [ei]
              exact ht2
            · rw [ek]
              exact ht3
            · intro f' hf'
              obtain ⟨hp, hth⟩ := ht8 f' hf'
              exact ⟨hext.findProj? hp, hth.mono (fun _ _ _ hfind => hext.find hfind)⟩
      projTablesAt := by
        intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG hs hld hblk
          j cvC nP nF hctor' hnF
        obtain ⟨hc₁, ek⟩ := ctorOld hctor'
        obtain ⟨tbl, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11⟩ :=
          h₁.projTablesAt bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG
            hs hld hblk j cvC nP nF hc₁ hnF
        have ei := keep _ (h₁.ctorIndRes _ _ _ _ _ _
          (L1.hashedBlockAt_of_get_ci_induct hgG evG hs hld hblk) hc₁)
        refine ⟨tbl, ?_, ?_, ?_, ht4, ht5, ht6, ht7, ?_, ht9, ht10, ht11⟩
        · rw [ei]
          exact hext.find ht1
        · rw [ei]
          exact ht2
        · rw [ek]
          exact ht3
        · intro f' hf'
          obtain ⟨hp, hth⟩ := ht8 f' hf'
          exact ⟨hext.findProj? hp, hth.mono (fun _ _ _ hfind => hext.find hfind)⟩
      unitLike := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps' cvC nPc ev good ha hld hb hfT hfew hfC
        obtain ⟨hC₁, -⟩ := ctorOld hfC
        have hne : (ConstantInfo.indInfo cvT caps') ∉ newF := by
          intro hm
          exact notFormer (iprjAddr_not_marker _ _)
            (h₁.ctorIndRes _ _ _ _ _ _ (L1.hashedBlockAt_of_get_ci_induct good ev ha hld hb) hC₁)
            _ hm (formerMember ev good ha hm (formerKey hfT hm) hld hb)
        obtain ⟨hT₁, eT⟩ := old hfT hne
        obtain ⟨hu1, hu2, hu3⟩ := h₁.unitLike ap ptr h h' cs a nl ty u blk p i b cvT caps' cvC
          nPc ev good ha hld hb hT₁ hfew hC₁
        refine ⟨hu1, hu2, ?_⟩
        rw [eT]
        exact hu3.imp id (fun hr => ⟨hr.1, fun us => hext.isUnitLikeTy_mono (hr.2 us)⟩)
      unitLikeRaw := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps' ev al res good ha hld hb hfT hfew hz hn
        by_cases e : (ConstantInfo.indInfo cvT caps') ∈ newF
        · exact (hformer.unitLikeRaw ap ptr h h' cs a nl ty u blk p i b ev good ha
            ⟨_, e, (formerKey hfT e).symm⟩ hld hb hfew hz hn).elim
        · obtain ⟨hT₁, eT⟩ := old hfT e
          obtain ⟨hu1, hu2, hu3⟩ := h₁.unitLikeRaw ap ptr h h' cs a nl ty u blk p i b cvT caps'
            ev trivial (h₁.findRes _ _ hT₁) good ha hld hb hT₁ hfew
            ⟨hz.bp, hz.ptr, hz.before, hz.after, hz.calls, hz.observed, trivial, hz.good,
              hz.blockRep, hz.zeroFields⟩
            ⟨hn.ap, hn.before, hn.after, hn.calls, hn.observed, trivial, hn.good, hn.parentRep⟩
          refine ⟨hu1, hu2, ?_⟩
          rw [eT]
          exact hu3.imp id (fun hr => ⟨hr.1, fun us => hext.isUnitLikeTy_mono (hr.2 us)⟩)
      eta := by
        intro ac b sa i j cvc cvT caps' cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1
          hfC hnm hpos ev good hb hld hfT hmod hsort hnz hrec hsa
        obtain ⟨hC₁, eC⟩ := ctorOld hfC
        have hnC : cvc.name = (formersStage c newF).κ (ixAddr ac) := WhnfAux.name_of_find hfC
        have hfC' : (formersStage c newF).env.find?
            ((formersStage c newF).κ (cprjAddr (ixAddr b) (ZMod.val i) j)) =
              some (.ctorInfo cvc cnP cnF) := by
          rw [← hnm, hnC]
          exact hfC
        obtain ⟨hCj, eN⟩ := ctorOld hfC'
        have hrI := h₁.ctorIndRes _ _ _ _ _ _ (L1.hashedBlockAt_of_get_ci_iprj good hb ev) hCj
        have hne : (ConstantInfo.indInfo cvT caps') ∉ newF := by
          intro hm
          exact notFormer (iprjAddr_not_marker _ _) hrI _ hm (formerKey hfT hm)
        obtain ⟨hT₁, eT⟩ := old hfT hne
        obtain ⟨⟨he1, he2, he3, he4, he5⟩, huse⟩ := h₁.eta ac b sa i j cvc cvT caps' cnP cnF us
          l bp ptr nl ty np u blk idx h1 h2 cs1 hC₁ (hnm.trans eN) hpos ev good hb hld hT₁ hmod
          hsort hnz hrec hsa
        refine ⟨⟨he1, by rw [eC]; exact he2, he3, he4, he5⟩, ?_⟩
        rw [eT, eC]
        exact ⟨(hext.towerSlotsAll_eq hT₁ _).trans huse.towers, huse.sort,
          heta _ _ cvT cvc caps' cnP cnF hT₁ he1 he2 hC₁ _ hext⟩
      etaIota := by
        intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps' cnP cnF us l ev good hpa hld hb
          hfT hfC hmul hrec hsort hnz
        obtain ⟨hC₁, eC⟩ := ctorOld hfC
        have hne : (ConstantInfo.indInfo cvT caps') ∉ newF := by
          intro hm
          exact notFormer (iprjAddr_not_marker _ _)
            (h₁.ctorIndRes _ _ _ _ _ _ (L1.hashedBlockAt_of_get_ci_induct good ev hpa hld hb) hC₁)
            _ hm (formerMember ev good hpa hm (formerKey hfT hm) hld hb)
        obtain ⟨hT₁, eT⟩ := old hfT hne
        obtain ⟨⟨he1, he2, he3, he4, he5, he6⟩, huse⟩ := h₁.etaIota pp ptr nl ty u blk h1 h2 cs1
          pa b i m cvT cvc caps' cnP cnF us l ev good hpa hld hb hT₁ hC₁ hmul hrec hsort hnz
        refine ⟨⟨he1, by rw [eC]; exact he2, he3, he4, he5, he6⟩, ?_⟩
        rw [eT, eC]
        exact ⟨(hext.towerSlotsAll_eq hT₁ _).trans huse.towers, huse.sort,
          heta _ _ cvT cvc caps' cnP cnF hT₁ he1 he2 hC₁ _ hext⟩
      recordShape := h₁.recordShape
      inductBlock := by
        intro addr ptr h h' cs a b nl ty np ni nc u blk i ev _ res good ha hld hblk
        rcases splitKey (ixAddr a) (ixAddr_not_marker a) res with hnew | hold
        · exact hformer.inductBlock addr ptr h h' cs a b nl ty np ni nc u blk i ev good ha hnew
            hld hblk
        · exact h₁.inductBlock addr ptr h h' cs a b nl ty np ni nc u blk i ev trivial hold good
            ha hld hblk
      projTablesGuard := by
        intro bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hctor' htbl
        obtain ⟨hc₁, -⟩ := ctorOld hctor'
        have ei := keep _
          (h₁.ctorIndRes _ _ _ _ _ _ (L1.hashedBlockAt_of_proj_ctor good ev hb hip) hc₁)
        rw [ei] at htbl
        have htbl₁ : c.env.find? (Ix.Kernel.projTableName
            (c.stored.κ (iprjAddr (ixAddr b) (ZMod.val i)))) = some (.projInfo tbl) := by
          rcases find?_append_cases (env := c.env) newF htbl with hm | ho
          · obtain ⟨cv, caps, e⟩ := hind _ hm
            cases e
          · exact ho
        exact h₁.projTablesGuard bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hc₁ htbl₁
      canonical := h₁.canonical
      storedRes := by
        intro a ci hf
        have e : (formersStage c newF).κ a = keyOf c.t a :=
          Ctx.stagedOver_key_of_find (c := appCtx c newF) (pre := c.env) hf
        rw [e]
        exact Resolved.ne
      findRes := by
        intro a ci hf
        by_cases e : ci ∈ newF
        · rw [← WhnfAux.name_of_find hf]
          exact newRes ci e
        · rw [(old hf e).2]
          exact h₁.findRes a ci (old hf e).1
      ctorIndRes := by
        intro b i j cv nP nF hbh hf
        obtain ⟨hf₁, -⟩ := ctorOld hf
        have hr := h₁.ctorIndRes b i j cv nP nF hbh hf₁
        rw [keep _ hr]
        exact hr
      ctorIndPerm := by
        intro a b i j cvT caps' cv nP nF hbh hf hnI hfC
        obtain ⟨hC₁, -⟩ := ctorOld hfC
        have hrI := h₁.ctorIndRes b i j cv nP nF hbh hC₁
        have hne : (ConstantInfo.indInfo cvT caps') ∉ newF := by
          intro hm
          apply notFormer (iprjAddr_not_marker b i) hrI _ hm
          have e3 : (formersStage c newF).κ (iprjAddr b i) = keyOf c.t (iprjAddr b i) :=
            (keep _ hrI).trans (c.stored.key_eq hrI)
          exact e3.symm.trans hnI.symm
        obtain ⟨hT₁, -⟩ := old hf hne
        exact ProjPermitted.of_keep keep
          (h₁.ctorIndPerm a b i j cvT caps' cv nP nF hbh hT₁ (hnI.trans (keep _ hrI)) hC₁)
      roleRes := by
        intro r a hf hi hb
        have hr := h₁.roleRes r a hf hi hb
        rw [keep _ hr]
        exact hr }

end Generic

/-! ## The point stage -/

section Point

open IxVM.Consistency
open IxVM.Refinement.Decl.Point (FormerRec)

/-- The formers as the stage stores them, newest first. -/
abbrev pointNew (formers : List FormerRec) : List (ConstantInfo .anon) :=
  (formers.map (·.stored)).reverse

/-- **What the point stage reads of the block record.** The store `E` (decoded, holding at a
hashed block's projection addresses that block's projections) holds the block `cb` at `B` with
the members `ms`, all inductive, and their member projection records; the prefix `env` stores
the references the block uses; every constructor has its position as stored index and a reading
of its type. The formers are the block's (the former half of `PointReads`), with distinct names,
each passing its front door at the prefix (`ConstantValRunJ`), at an input key, its annotated
type a telescope into a sort. -/
structure PointStageInput (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (t : Ix.Kernel.RoleTable)
    (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (formers : List FormerRec) : Prop where
  check : t.check = .ok ()
  decoded : L1.EnvDecoded E
  held : HashedBlockProjectionsHeld E
  block : recordOf E B = some cb
  muts : cb.info = .muts ms
  inds : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m → ∃ ind : Ixon.Inductive, m = .indc ind
  formerRec : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
    recordOf E (Core.iprjAddr B i) = some (memberProjection B i (.indc ind))
  used : Decl.UsedRefsStored t env cb
  ctorRead : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
    ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        blockRead t E B cb ms ct.typ = .ok cty ∧ cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true
  formerOf : ∀ f ∈ formers, ∃ (i : Nat) (ind : Ixon.Inductive) (ty₀ ty' : Ix.Kernel.Expr .anon)
      (caps : IndCaps .anon),
    ms[i]? = some (.indc ind) ∧ f = pointFormer t B i ind ty₀ caps ty' ∧
    FormerRead t E B cb ms i ind ty₀ ty'
  formerAt : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
    ∃ (ty₀ ty' : Ix.Kernel.Expr .anon) (caps : IndCaps .anon),
      pointFormer t B i ind ty₀ caps ty' ∈ formers ∧ FormerRead t E B cb ms i ind ty₀ ty'
  nodup : (formers.map (·.cv.name)).Nodup
  front : ∀ f ∈ formers,
    Ix.Kernel.Semantics.ConstantValRunJ Ix.Kernel.Model.rulesJ env f.cv f.type'
  key : ∀ f ∈ formers, ∃ a, f.cv.name = .id a
  sort : ∀ f ∈ formers, ∃ l, f.type'.resultSort = some l

/-- Two formers of a list with distinct names, of one name, are one. -/
theorem formerRec_eq_of_name : ∀ {fs : List FormerRec}, (fs.map (·.cv.name)).Nodup →
    ∀ {f g : FormerRec}, f ∈ fs → g ∈ fs → f.cv.name = g.cv.name → f = g
  | [], _, _, _, hf, _, _ => nomatch hf
  | x :: xs, hnd, f, g, hf, hg, h => by
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hf with rfl | hf'
    · rcases List.mem_cons.mp hg with rfl | hg'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨g, hg', h.symm⟩) hnd'.1
    · rcases List.mem_cons.mp hg with rfl | hg'
      · exact absurd (List.mem_map.mpr ⟨f, hf', h⟩) hnd'.1
      · exact formerRec_eq_of_name hnd'.2 hf' hg' h

section
variable {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}
  {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
  {formers : List FormerRec} {lim : Option Nat}

theorem PointStageInput.wf (hP : PointStageInput E env t B cb ms formers) : t.wf = true := by
  unfold Ix.Kernel.RoleTable.wf
  rw [hP.check]
  rfl

/-- A former's key is fresh in the prefix. -/
theorem PointStageInput.fresh (hP : PointStageInput E env t B cb ms formers) {f : FormerRec}
    (hf : f ∈ formers) : env.find? f.cv.name = none :=
  Option.isNone_iff_eq_none.mp (hP.front f hf).1

/-- **Every former is the former of a member at an index below `2 ^ 64`**: a former of member `i`
has the key of member `i.toUInt64.toNat`, whose former it therefore is (the names are distinct). -/
theorem PointStageInput.former_norm (hP : PointStageInput E env t B cb ms formers)
    {f : FormerRec} (hf : f ∈ formers) :
    ∃ (i : Nat) (ind : Ixon.Inductive) (ty₀ ty' : Ix.Kernel.Expr .anon) (caps : IndCaps .anon),
      ms[i]? = some (.indc ind) ∧ i < UInt64.size ∧ f = pointFormer t B i ind ty₀ caps ty' ∧
      FormerRead t E B cb ms i ind ty₀ ty' := by
  obtain ⟨i₀, ind₀, ty₀₀, ty'₀, caps₀, hi₀, hf₀, -⟩ := hP.formerOf f hf
  have hlt : i₀.toUInt64.toNat < ms.size :=
    Nat.lt_of_le_of_lt (toNat_toUInt64_le i₀) (Array.getElem?_eq_some_iff.mp hi₀).1
  obtain ⟨ind, hind⟩ := hP.inds _ _ (Array.getElem?_eq_getElem hlt)
  have hk : ms[i₀.toUInt64.toNat]? = some (.indc ind) := by
    rw [Array.getElem?_eq_getElem hlt, hind]
  obtain ⟨ty₀, ty', caps, hmem, hread⟩ := hP.formerAt _ ind hk
  refine ⟨_, ind, ty₀, ty', caps, hk, (i₀.toUInt64).toNat_lt, ?_, hread⟩
  refine formerRec_eq_of_name hP.nodup hf hmem ?_
  rw [hf₀]
  show Core.keyOf t (Core.iprjAddr B i₀) = Core.keyOf t (Core.iprjAddr B i₀.toUInt64.toNat)
  rw [iprjAddr_toNat]

/-- **A staged former, as stored**: the former of member `k` (below `2 ^ 64`) at its key, with
the canonical annotation of its reading and the empty capability record. -/
theorem PointStageInput.newMem (hP : PointStageInput E env t B cb ms formers)
    {y : ConstantInfo .anon} (hy : y ∈ pointNew formers) :
    ∃ (k : Nat) (ind : Ixon.Inductive) (ty₀ ty' : Ix.Kernel.Expr .anon),
      ms[k]? = some (.indc ind) ∧ k < UInt64.size ∧
      y = .indInfo ⟨Core.keyOf t (Core.iprjAddr B k), List.range ind.lvls.toNat, ty'⟩ {} ∧
      FormerRead t E B cb ms k ind ty₀ ty' := by
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hy)
  obtain ⟨k, ind, ty₀, ty', caps, hk, hlt, rfl, hread⟩ := hP.former_norm hf
  exact ⟨k, ind, ty₀, ty', hk, hlt, rfl, hread⟩

/-- The references the block uses resolve at the stage as the table keys them, with a projection
permitted there (the prefix stores them). -/
theorem PointStageInput.stageUsed (hP : PointStageInput E env t B cb ms formers)
    (hext : Ix.Kernel.EnvExt env (Decl.Point.stage env formers)) :
    ∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
      (formersStage ⟨E, env, t, lim⟩ (pointNew formers)).κ x = Core.keyOf t x ∧
      Core.ProjPermitted (formersStage ⟨E, env, t, lim⟩ (pointNew formers)).κ x := by
  intro i hi x hx
  obtain ⟨ci, hci⟩ := hP.used i hi x hx
  have hci' : (appCtx ⟨E, env, t, lim⟩ (pointNew formers)).env.find? (Core.keyOf t x) =
      some ci := hext.find hci
  exact ⟨Core.Ctx.stagedOver_key_of_find (c := appCtx ⟨E, env, t, lim⟩ (pointNew formers))
      (pre := env) hci',
    Core.Ctx.stagedOver_projPermitted_of_find
      (c := appCtx ⟨E, env, t, lim⟩ (pointNew formers)) (pre := env) hci⟩

/-- The block's member addresses resolve at the stage as the table keys them: every member has
its former staged. -/
theorem PointStageInput.stageRecur (hP : PointStageInput E env t B cb ms formers) :
    ∀ x ∈ L1.blockRecurAddrs B ms.toList,
      (formersStage ⟨E, env, t, lim⟩ (pointNew formers)).κ x = Core.keyOf t x := by
  intro x hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨m, hm, rfl⟩ := LoadedReads.blockRecurAddrs_get hk
  obtain ⟨ind, rfl⟩ := hP.inds k m hm
  rw [LoadedReads.memberAddr_indc]
  obtain ⟨ty₀, ty', caps, hmemF, -⟩ := hP.formerAt k ind hm
  have hfind : (appCtx ⟨E, env, t, lim⟩ (pointNew formers)).env.find?
      (Core.keyOf t (Core.iprjAddr B k)) = some _ := Decl.Point.stage_find hP.nodup hmemF
  exact Core.Ctx.stagedOver_key_of_find (c := appCtx ⟨E, env, t, lim⟩ (pointNew formers))
    (pre := env) hfind

/-- **The load facts at the staged formers**, from the block record. A unit-like raw load at a
former is refuted by the block's shape: at two or more inductives `FewInductives` fails; at one,
the member's one constructor makes the gate's `struct_is_rec` answer `1`, not the `0` observed. -/
theorem PointStageInput.formersLoads (hP : PointStageInput E env t B cb ms formers)
    (hext : Ix.Kernel.EnvExt env (Decl.Point.stage env formers)) (hgate : PointShape E B ms) :
    FormersLoads ⟨E, env, t, lim⟩ (pointNew formers) := by
  have htwf := hP.wf
  refine { getCI := ?_, getIprj := ?_, getCprj := ?_, inductRecord := ?_, inductBlock := ?_,
    unitLikeRaw := ?_ }
  · intro addr ptr h h' cs a ev good ha cv caps hmem hkey
    obtain ⟨k, ind, ty₀, ty', hk, hlt, hy, hread⟩ := hP.newMem hmem
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj hy
    obtain ⟨hty, hlbb, hdef, hcan⟩ := hread
    have hx : Core.ixAddr a = Core.iprjAddr B k := Core.keyOf_inj htwf hkey
    have hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B k (.indc ind)) := by
      rw [hx]
      exact hP.formerRec k ind hk
    have hkk : k.toUInt64.toNat = k := toNat_toUInt64_of_lt hlt
    have hk' : ms[k.toUInt64.toNat]? = some (.indc ind) := by
      rw [hkk]
      exact hk
    obtain ⟨ty'', hcT, hrep⟩ := LoadedReads.get_ci_iprj_at (p := ⟨k.toUInt64, B⟩) hP.check
      good.1 good.2 ha ev hrecA rfl hP.block hP.muts hk' hty hlbb hdef
    have hcT' : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) ind.typ ty₀ = some ty'' := hcT
    rw [hkk] at hcT'
    have e : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcan)
    subst e
    have hr := hrep _ (hP.stageUsed (lim := lim) hext) (hP.stageRecur (lim := lim)) {}
    rw [hx] at hr
    exact hr
  · intro bp ptr i h h' cs b ev good hb cv caps hmem hkey
    obtain ⟨k, ind, ty₀, ty', hk, hlt, hy, hread⟩ := hP.newMem hmem
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj hy
    obtain ⟨hty, hlbb, hdef, hcan⟩ := hread
    have hkey' : Core.keyOf t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) =
        Core.keyOf t (Core.iprjAddr B k) := hkey
    have hbh := L1.hashedBlockAt_of_get_ci_iprj (c := ⟨E, env, t, lim⟩) good hb ev
    obtain ⟨hbB, hik⟩ := iprj_key_member htwf hP.decoded hP.held (hP.formerRec k ind hk) hbh hkey'
    have hik' : ZMod.val i = k := toUInt64_inj_of_lt (val_lt_uint64 i) hlt hik
    have hblock' : recordOf E (Core.ixAddr b) = some cb := by
      rw [hbB]
      exact hP.block
    have hmem' : ms[ZMod.val i]? = some (.indc ind) := by
      rw [hik']
      exact hk
    have hty' : (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t (Core.ixAddr b) ms)).read ind.typ = .ok ty₀ := by
      rw [hbB]
      exact hty
    obtain ⟨ty'', hcT, hrep⟩ := LoadedReads.get_ci_iprj_load_at hP.check good.1 good.2 hb ev
      hblock' hP.muts hmem' hty' hlbb hdef
    have hcT' : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList (ZMod.val i) : Nat) : F) ind.typ ty₀ = some ty'' := hcT
    rw [hik'] at hcT'
    have e : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcan)
    subst e
    have hrecur' : ∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) ms.toList,
        (formersStage ⟨E, env, t, lim⟩ (pointNew formers)).κ x = Core.keyOf t x := by
      rw [hbB]
      exact hP.stageRecur
    have hr := hrep _ (hP.stageUsed (lim := lim) hext) hrecur' {}
    rw [hbB, hik'] at hr
    exact hr
  · rintro bp ptr i j h h' cs b ev good hb ⟨y, hy, hyn⟩
    obtain ⟨k, ind, ty₀, ty', hk, hlt, rfl, -⟩ := hP.newMem hy
    have hkey' : Core.keyOf t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) =
        Core.keyOf t (Core.iprjAddr B k) := hyn.symm
    have hbh := L1.hashedBlockAt_of_get_ci_cprj (c := ⟨E, env, t, lim⟩) good hb ev
    obtain ⟨hbB, hik⟩ := iprj_key_member htwf hP.decoded hP.held (hP.formerRec k ind hk) hbh hkey'
    have hik' : ZMod.val i = k := toUInt64_inj_of_lt (val_lt_uint64 i) hlt hik
    have hblock' : recordOf E (Core.ixAddr b) = some cb := by
      rw [hbB]
      exact hP.block
    have hmem' : ms[ZMod.val i]? = some (.indc ind) := by
      rw [hik']
      exact hk
    have hctys : ∀ (k' : Nat) (ct : Ixon.Constructor), ind.ctors[k']? = some ct →
        ct.cidx.toNat = k' ∧ ∃ cty : Ix.Kernel.Expr .anon,
          (exprReader t (fun x => E.blobs.get? x) cb id
            (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty ∧
          cty.looseBVarsBounded 0 = true ∧
          cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true := by
      rw [hbB]
      exact hP.ctorRead k ind hk
    have hrecur' : ∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) ms.toList,
        (formersStage ⟨E, env, t, lim⟩ (pointNew formers)).κ x = Core.keyOf t x := by
      rw [hbB]
      exact hP.stageRecur
    obtain ⟨ct, ty'', -, hrep⟩ := LoadedReads.get_ci_cprj_load_at hP.check good.1 good.2 hb ev
      hblock' hP.muts hmem' hctys
    exact ⟨_, hrep _ (hP.stageUsed (lim := lim) hext) hrecur'⟩
  · rintro addr ptr h h' cs a nl ty np ni nc u blk idx ev good ha ⟨y, hy, hyn⟩ hld
    obtain ⟨k, ind, ty₀, ty', hk, hlt, rfl, -⟩ := hP.newMem hy
    have hx : Core.ixAddr a = Core.iprjAddr B k := Core.keyOf_inj htwf hyn.symm
    have hrec : recordOf E (Core.ixAddr a) = some (memberProjection B k (.indc ind)) := by
      rw [hx]
      exact hP.formerRec k ind hk
    obtain ⟨b, i, hrecA, hb, hidx, hinfo⟩ :=
      get_ci_induct_record hP.decoded good.1 good.2 ev ha hld hrec
    exact ⟨_, b, i, hrecA, hb, hidx, hinfo⟩
  · rintro addr ptr h h' cs a b nl ty np ni nc u blk i ev good ha ⟨y, hy, hyn⟩ hld hb
    obtain ⟨k, ind, ty₀, ty', hk, hlt, rfl, -⟩ := hP.newMem hy
    have hxa : Core.ixAddr a = Core.iprjAddr B k := Core.keyOf_inj htwf hyn.symm
    have hx := get_ci_induct_addr ev good.2 ha hld hb
    have hbh := L1.hashedBlockAt_of_get_ci_induct (c := ⟨E, env, t, lim⟩) good ev ha hld hb
    obtain ⟨hbB, hik⟩ := iprj_key_member (i := ZMod.val i) htwf hP.decoded hP.held
      (hP.formerRec k ind hk) hbh (by rw [← hx, hxa])
    have hik' : ZMod.val i = k := toUInt64_inj_of_lt (val_lt_uint64 i) hlt hik
    refine ⟨cb, ms, ind, ?_, hP.muts, by rw [hik']; exact hk⟩
    rw [hbB]
    exact recordAt_of_recordOf hP.decoded hP.block
  · rintro ap ptr h h' cs a nl ty u blk p i b ev good ha ⟨y, hy, hyn⟩ hld hb hfew hz hn
    obtain ⟨k, ind, ty₀, ty', hk, hlt, rfl, -⟩ := hP.newMem hy
    have hxa : Core.ixAddr a = Core.iprjAddr B k := Core.keyOf_inj htwf hyn.symm
    have hx := get_ci_induct_addr ev good.2 ha hld hb
    have hbh := L1.hashedBlockAt_of_get_ci_induct (c := ⟨E, env, t, lim⟩) good ev ha hld hb
    obtain ⟨hbB, -⟩ := iprj_key_member (i := ZMod.val i) htwf hP.decoded hP.held
      (hP.formerRec k ind hk) hbh (by rw [← hx, hxa])
    rcases hgate with h2 | ⟨ind₁, hms, hN⟩
    · exact few_not_multi (c := ⟨E, env, t, lim⟩)
        ⟨cb, ms, recordAt_of_recordOf hP.decoded hP.block, hP.muts, h2⟩
        (by rw [← hbB]; exact hfew)
    · subst hms
      have hk0 : k = 0 := by
        have h1 : k < (#[.indc ind₁] : Array Ixon.MutConst).size :=
          (Array.getElem?_eq_some_iff.mp hk).1
        have h1' : (#[.indc ind₁] : Array Ixon.MutConst).size = 1 := rfl
        omega
      subst hk0
      have hii : ind = ind₁ := by
        have e : (Ixon.MutConst.indc ind₁ : Ixon.MutConst) = .indc ind := Option.some.inj hk
        exact (Ixon.MutConst.indc.inj e).symm
      subst hii
      have hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
        rw [hxa]
        exact hP.formerRec 0 ind hk
      obtain ⟨tyPtr, blkPtr, hld₀, -, -, hc56⟩ :=
        former_get_ci_value good.1 good.2 ha ev hrecA hP.block hP.muts
      rw [hld₀] at hld
      have hv := Except.ok.inj hld
      simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
      obtain ⟨-, -, -, -, hn1, -⟩ := hv
      have hsz : ind.ctors.size = 1 := by
        have e := field_count_eq hc56 hn1
        rw [ZMod.val_one] at e
        exact e.symm
      have hv1 := hN.recursive hsz hn.ap _ hn.before hn.after hn.calls a hn.observed hn.good.1
        hn.good.2 hn.parentRep hxa
      exact absurd (Value.field.inj hv1) (by decide)

/-- The formers' run from the prefix to the stage, and the extension. -/
theorem PointStageInput.stageRun (hP : PointStageInput E env t B cb ms formers) :
    Decl.Point.PointRun (formers.map (·.cv.name)) env (formers.map (·.declared))
        (Decl.Point.stage env formers) ∧
      Ix.Kernel.EnvExt env (Decl.Point.stage env formers) :=
  Decl.Point.formers_run _ formers env (Ix.Kernel.EnvExt.refl env)
    (fun f hf => ⟨hP.front f hf, hP.key f hf, hP.sort f hf⟩) hP.nodup (fun f hf => hP.fresh hf)

/-- **The environment half of the stage's core facts**: the fold's store invariant along the
formers' run, and the companions (the stage stores no recursor). -/
theorem pointStage_envFacts (hinv : Decl.PrefixInv.{u} E t lim env)
    (hP : PointStageInput E env t B cb ms formers) :
    Core.CoreEnvFacts ⟨E, Decl.Point.stage env formers, t, lim⟩ := by
  obtain ⟨hrun, hext⟩ := hP.stageRun
  have hS : Decl.FoldStoreInv (Decl.Point.stage env formers) :=
    Decl.Point.foldStoreInv_run _ hrun hinv.store
  have hno : Ix.Kernel.Model.NewSat env (Decl.Point.stage env formers)
      Ix.Kernel.Model.NotRec := by
    intro n x hf
    rcases find?_append_cases (env := env) (pointNew formers) hf with hm | ho
    · obtain ⟨f, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hm)
      exact Or.inr (fun _ _ _ _ hh => nomatch hh)
    · exact Or.inl ho
  have hR : Decl.CoreCompanions ⟨E, Decl.Point.stage env formers, t, lim⟩ :=
    Decl.Point.coreCompanions_of_noRec (c := ⟨E, env, t, lim⟩) hinv.companions
      hinv.store.store hext hno
  exact Decl.FoldStoreInv.toCoreEnvFacts (c := ⟨E, Decl.Point.stage env formers, t, lim⟩) hS
    hinv.tableWf hR

/-- **The load half of the stage's core facts.** -/
theorem pointStage_loads (hinv : Decl.PrefixInv.{u} E t lim env) (hkeys : HashKeyed t env)
    (hP : PointStageInput E env t B cb ms formers) (hgate : PointShape E B ms) :
    Core.ScopedLoadFacts
      ((⟨E, Decl.Point.stage env formers, t, lim⟩ : Core.Ctx).stagedOver env) := by
  obtain ⟨-, hext⟩ := hP.stageRun
  exact stagedLoads_append_formers (c := ⟨E, env, t, lim⟩) hinv.loads hinv.tableWf
    (fun y hy => by
      obtain ⟨k, ind, ty₀, ty', -, -, rfl, -⟩ := hP.newMem hy
      exact ⟨_, _, rfl⟩)
    (fun y hy => by
      obtain ⟨k, ind, ty₀, ty', -, -, rfl, -⟩ := hP.newMem hy
      exact ⟨Core.iprjAddr B k, Core.iprjAddr_not_marker _ _, rfl⟩)
    (fun y hy => by
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hy)
      exact hP.fresh hf)
    (fun f => hkeys.marker_none f) hext hinv.etaStable (hP.formersLoads hext hgate)

/-- **The scoped core facts of the constructor stage of a block on the constructors-only
route**: at the prefix with the block's formers stored at the empty capability record, keyed
over the prefix. -/
theorem pointStage_coreFacts (hinv : Decl.PrefixInv.{u} E t lim env) (hkeys : HashKeyed t env)
    (hP : PointStageInput E env t B cb ms formers) (hgate : PointShape E B ms) :
    Core.ScopedCoreFacts
      ((⟨E, Decl.Point.stage env formers, t, lim⟩ : Core.Ctx).stagedOver env) :=
  ⟨pointStage_envFacts hinv hP, pointStage_loads hinv hkeys hP hgate⟩

end

end Point

end IxVM.Refinement.Typing
