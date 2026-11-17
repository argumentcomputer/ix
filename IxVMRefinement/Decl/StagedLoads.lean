import IxVMRefinement.Decl.PrefixInv

/-! # The load contract of the stages of a native block

A native inductive block is checked in stages over the prefix `c`:

* **The former stage.** The former's type is checked against the prefix itself, so the load
  contract is the prefix's (`stagedLoads_former`, the invariant's `loads`).
* **The constructor stage.** The constructors' types are checked against the prefix with the
  former stored. Its context is `ctorStage c cvF caps`: the stage over the prefix whose
  environment also stores the former `.indInfo cvF caps` (`Ctx.stagedOver`). The former's
  address resolves there; a projection is permitted only at the addresses the prefix stores, so
  not at the former (`Ctx.stagedOver_not_projPermitted`).

`stagedLoads_cons_former` gives the constructor stage's contract from the prefix's, from the
freshness of the former's key and of the key of its address's marker, and from `FormerLoads`:
the load facts about the block's own record at the former, which the native route produces.
Every other clause is derived. A load at a key the prefix resolves answers as before; a fact
about a stored constructor or projection table speaks of the prefix's constants, and so does a
fact about a stored inductive that is a stored constructor's (the former has no constructor
stored at this stage); the projection-table clause at the former is refuted by the missing
permission. -/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (ConstantVal ConstantInfo IndCaps)

universe u

set_option linter.unusedVariables false

/-! ## The former stage -/

/-- **The load contract of the former stage** is the prefix's: the former's type is checked
against the prefix. Its producers are those of the invariant: `prefixInv_empty`,
`PrefixInv.cons_value` and the walked-constant step. -/
theorem stagedLoads_former {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (h : PrefixInv.{u} E t lim env) :
    ScopedLoadFacts (Ctx.stored ⟨E, env, t, lim⟩) :=
  h.loads

/-! ## The constructor stage -/

/-- **The context of the constructor stage** over the prefix `c` with the former
`.indInfo cvF caps`: what the longer environment stores resolves, and a projection is permitted
at the addresses the prefix stores. -/
noncomputable abbrev ctorStage (c : Ctx) (cvF : ConstantVal .anon) (caps : IndCaps .anon) :
    ScopedCtx :=
  (consCtx c (.indInfo cvF caps)).stagedOver c.env

/-- **The load facts at the staged former**: the clauses of the constructor stage's load
contract at the former's own key, which are facts about the block's record and are not derived
from the prefix. Each is produced by the native route from the walked block record:

* `getCI`, `getIprj`: a load at the former's key represents the former under the stage's keying
  (`Assembly.native_former_getCI_reload`, `Assembly.native_former_reload`,
  `Assembly/NativeFormerInputs.lean`, at the table's keying; rekeyed to the stage by
  `CIPtrRep.rekey` since the cells of the former's type are used references of the block, which
  the prefix stores);
* `getCprj`: a constructor load at the former's member represents a constant under the stage's
  keying (`Decl.CtorLoadAtIndex` and the conversion of the constructor record: its cells are used
  references and the former, its `Proj` heads used references by `L1.RawConvExpr.projIn_used`);
* `inductRecord`, `inductBlock`: the record at the former's address is the inductive projection
  of the block (the walked record);
* `unitLikeRaw`: the staged capability record is the final one
  (`Assembly.NativeFormerRunInput.unitLikeRaw_current`, `Assembly/NativeCapabilities.lean`). -/
structure FormerLoads (c : Ctx) (cvF : ConstantVal .anon) (caps : IndCaps .anon) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr → keyOf c.t (ixAddr a) = cvF.name →
    CIPtrRep (ctorStage c cvF caps).κ h' ptr (.indInfo cvF caps)
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp → keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cvF.name →
    CIPtrRep (ctorStage c cvF caps).κ h' ptr (.indInfo cvF caps)
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h b bp → keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cvF.name →
    ∃ ci₀, CIPtrRep (ctorStage c cvF caps).κ h' ptr ci₀
  inductRecord : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty np ni nc u blk idx : SourceValue F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr → keyOf c.t (ixAddr a) = cvF.name →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (ixAddr a) = some cm ∧ Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩
  inductBlock : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a b : Bytes.Address) (nl ty np ni nc u blk : SourceValue F) (i : F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a addr → keyOf c.t (ixAddr a) = cvF.name →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    ∃ (cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt c.E (ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind)
  unitLikeRaw : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c cs →
    Bytes.RepAddressRef addrTy h a ap → keyOf c.t (ixAddr a) = cvF.name →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk → FewInductives c (ixAddr b) →
    ZeroFieldCtorLoad (ctorStage c cvF caps) b i → NonrecursiveLoad (ctorStage c cvF caps) a →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains cvF.name = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (consCtx c (.indInfo cvF caps)).env
          (.const cvF.name us) = true))

/-- **The key of a marker is not stored where every stored key at an address is at an address
of 32 bytes**: the form in which the block step's freshness gives the stage's marker input.
A record's address is a hash (`ixAddr_size`, `projAddr_size`); a marker has more bytes. -/
theorem find?_projMarker_none {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}
    (hsz : ∀ ci ∈ env.consts, ∀ y, ci.name = keyOf t y → y.hash.size = 32)
    (f : _root_.Address) : env.find? (keyOf t (projMarker f)) = none := by
  cases hf : env.find? (keyOf t (projMarker f)) with
  | none => rfl
  | some ci =>
    exfalso
    have hf' := hf
    unfold Ix.Kernel.Env.find? at hf'
    have hmem := List.mem_of_find?_eq_some hf'
    have hn : ci.name = keyOf t (projMarker f) := WhnfAux.name_of_find hf
    exact not_isProjMarker_of_size (hsz ci hmem _ hn) ⟨f, rfl⟩

/-- **The load contract of the constructor stage.** Over a prefix whose contract holds, storing
the former `.indInfo cvF caps` at the fresh key of the address `f` gives the contract of the
constructor stage, given the load facts at the former (`hformer`) and that the key of `f`'s
marker is not stored (`hmark`, beside the freshness of the former's key `hfresh` and `hnt`).
`hmark` is the one input the projection permission adds; `find?_projMarker_none` produces it
from the prefix's keys being keys of record addresses. -/
theorem stagedLoads_cons_former {c : Ctx} (h₁ : ScopedLoadFacts c.stored)
    {cvF : ConstantVal .anon} {caps : IndCaps .anon} {f : _root_.Address}
    (htwf : c.t.wf = true) (hname : cvF.name = keyOf c.t f)
    (hfresh : c.env.find? cvF.name = none)
    (hmark : c.env.find? (keyOf c.t (projMarker f)) = none)
    (hnt : ∀ T : KKey, cvF.name ≠ Ix.Kernel.projTableName T) (heta : EtaStable c.env)
    (hformer : FormerLoads c cvF caps) :
    ScopedLoadFacts (ctorStage c cvF caps) := by
  have hext : Ix.Kernel.EnvExt c.env (consCtx c (.indInfo cvF caps)).env :=
    consCtx_ext (c := c) (cn := .indInfo cvF caps) hfresh hnt
  have keep : ∀ x, c.stored.κ x ≠ unresolvedKey →
      (ctorStage c cvF caps).κ x = c.stored.κ x := fun x hx =>
    stagedOver_keep (c₁ := c) (c₂ := consCtx c (.indInfo cvF caps)) (pre₁ := c.env)
      (pre₂ := c.env) rfl (fun hf => ⟨_, hext.find hf⟩) (fun hf => ⟨_, hf⟩) x hx
  have hFres : cvF.name ≠ unresolvedKey := by
    rw [hname]
    exact Resolved.ne
  have findFormer : (consCtx c (.indInfo cvF caps)).env.find? cvF.name =
      some (.indInfo cvF caps) :=
    Ix.Kernel.Env.find?_cons_self (ConstantInfo.indInfo cvF caps) c.env
  -- An address the stage resolves, one a record can have: the former's or the prefix's.
  have splitKey : ∀ x, ¬ IsProjMarker x → (ctorStage c cvF caps).κ x ≠ unresolvedKey →
      keyOf c.t x = cvF.name ∨ c.stored.κ x ≠ unresolvedKey := by
    intro x hm h
    obtain ⟨ci, hci⟩ := Ctx.stagedOver_key_ne (c := consCtx c (.indInfo cvF caps))
      (pre := c.env) h hm
    by_cases e : cvF.name = keyOf c.t x
    · exact Or.inl e.symm
    · have hci' : c.env.find? (keyOf c.t x) = some ci :=
        (Ix.Kernel.EnvExt.find?_cons_ne (env := c.env) (c := ConstantInfo.indInfo cvF caps)
          e).symm.trans hci
      exact Or.inr (by rw [Ctx.stored_key_of_find hci']; exact Resolved.ne)
  -- A constant the stage stores that is not the former is the prefix's, at the same key.
  have old : ∀ {x : _root_.Address} {y : ConstantInfo .anon},
      (ctorStage c cvF caps).env.find? ((ctorStage c cvF caps).κ x) = some y →
      y ≠ .indInfo cvF caps →
      c.env.find? (c.stored.κ x) = some y ∧ (ctorStage c cvF caps).κ x = c.stored.κ x := by
    intro x y hf hne
    have hfo := consCtx_find_old (c := c) (cn := .indInfo cvF caps) hf hne
    by_cases hr₂ : (ctorStage c cvF caps).κ x = unresolvedKey
    · exfalso
      have hr₁ : c.stored.κ x = unresolvedKey := by
        by_contra hr
        exact hr ((keep x hr).symm.trans hr₂)
      rw [hr₂, ← hr₁] at hfo
      exact h₁.findRes x y hfo hr₁
    · have e₂ : (ctorStage c cvF caps).κ x = keyOf c.t x := (ctorStage c cvF caps).key_eq hr₂
      rw [e₂] at hfo
      have e₁ : c.stored.κ x = keyOf c.t x := Ctx.stored_key_of_find hfo
      exact ⟨by rw [e₁]; exact hfo, e₂.trans e₁.symm⟩
  have ctorOld : ∀ {x : _root_.Address} {cv : ConstantVal .anon} {nP nF : Nat},
      (ctorStage c cvF caps).env.find? ((ctorStage c cvF caps).κ x) =
        some (.ctorInfo cv nP nF) →
      c.env.find? (c.stored.κ x) = some (.ctorInfo cv nP nF) ∧
        (ctorStage c cvF caps).κ x = c.stored.κ x :=
    fun hf => old hf (fun e => by cases e)
  -- The former is stored at its own key only.
  have formerKey : ∀ {x : _root_.Address},
      (ctorStage c cvF caps).env.find? ((ctorStage c cvF caps).κ x) =
        some (.indInfo cvF caps) → keyOf c.t x = cvF.name := by
    intro x hf
    have hn : cvF.name = (ctorStage c cvF caps).κ x := WhnfAux.name_of_find hf
    have hr : (ctorStage c cvF caps).κ x ≠ unresolvedKey := by
      rw [← hn]
      exact hFres
    exact ((ctorStage c cvF caps).key_eq hr).symm.trans hn.symm
  -- A key the prefix resolves, at an address a record can have, is not the former's.
  have notFormer : ∀ {x : _root_.Address}, ¬ IsProjMarker x → c.stored.κ x ≠ unresolvedKey →
      keyOf c.t x ≠ cvF.name := by
    intro x hm hr e
    obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hr hm
    rw [e, hfresh] at hci
    cases hci
  -- A load of an address keyed by the former names the member the former is the inductive of.
  have formerMember : ∀ {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {a : Bytes.Address} {nl ty np ni nc u blk : SourceValue F} {b : Bytes.Address} {i : F},
      ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c cs →
      Bytes.RepAddressRef addrTy h a ap → keyOf c.t (ixAddr a) = cvF.name →
      loadValue h' ptr =
        .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
      Bytes.RepAddressRef addrTy h' b blk →
      keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cvF.name := by
    intro ap ptr h h' cs a nl ty np ni nc u blk b i ev good ha hnew hld hb
    obtain ⟨v, hv, hci⟩ := hformer.getCI ap ptr h h' cs a ev good ha hnew
    have hv' := Except.ok.inj (hld.symm.trans hv)
    subst hv'
    obtain ⟨cv, caps', nP, nI, nC, e, -, -, -, -, -, -, -, b', i', hb', hidx, hn⟩ :=
      WhnfAux.ind_inv hci
    have e1 : cvF = cv := (ConstantInfo.indInfo.inj e).1
    have hbb : b' = b := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb' hb
    have hii : i = i' := Value.field.inj hidx
    rw [hbb, ← hii, ← e1] at hn
    have hr : (ctorStage c cvF caps).κ (iprjAddr (ixAddr b) (ZMod.val i)) ≠ unresolvedKey := by
      rw [← hn]
      exact hFres
    exact ((ctorStage c cvF caps).key_eq hr).symm.trans hn.symm
  have fam : ∀ {b : _root_.Address} {i : Nat}, (ctorStage c cvF caps).FamAt b i →
      keyOf c.t (iprjAddr b i) ≠ cvF.name → c.stored.FamAt b i := by
    intro b i hfam hne
    rcases hfam with ⟨cv, caps', hf⟩ | ⟨j, cv, nP, nF, hf⟩
    · refine Or.inl ⟨cv, caps', (old hf fun e => ?_).1⟩
      rw [e] at hf
      exact hne (formerKey hf)
    · exact Or.inr ⟨j, cv, nP, nF, (ctorOld hf).1⟩
  have famPerm : ∀ {b : _root_.Address} {i : Nat}, c.stored.FamAt b i →
      ProjPermitted c.stored.κ (iprjAddr b i) := by
    intro b i hfam
    have hr : c.stored.κ (iprjAddr b i) ≠ unresolvedKey := by
      rcases hfam with ⟨cv, caps', hf⟩ | ⟨j, cv, nP, nF, hf⟩
      · exact h₁.findRes _ _ hf
      · exact h₁.ctorIndRes _ _ _ _ _ _ hf
    obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hr (iprjAddr_not_marker _ _)
    exact Ctx.stored_projPermitted_of_find hci
  -- No projection is permitted at the former.
  have formerNoProj : ∀ {x : _root_.Address}, keyOf c.t x = cvF.name → ¬ IsProjMarker x →
      ¬ ProjPermitted (ctorStage c cvF caps).κ x := by
    intro x hx hm
    have hxf : x = f := keyOf_inj htwf (hx.trans hname)
    have hne : (ConstantInfo.indInfo cvF caps).name ≠ keyOf c.t (projMarker x) := by
      intro e
      exact hm ⟨x, keyOf_inj htwf (hx.trans e)⟩
    have hpre : c.env.find? (keyOf c.t x) = none := by
      rw [hx]
      exact hfresh
    have hmk : (consCtx c (.indInfo cvF caps)).env.find? (keyOf c.t (projMarker x)) = none := by
      refine (Ix.Kernel.EnvExt.find?_cons_ne (env := c.env) hne).trans ?_
      rw [hxf]
      exact hmark
    exact Ctx.stagedOver_not_projPermitted (c := consCtx c (.indInfo cvF caps)) (pre := c.env)
      hpre hmk
  have good₁ : ∀ {cs : List (Call F)}, CoreGood (ctorStage c cvF caps) cs →
      CoreGood c.stored cs :=
    fun g => ⟨g.noCollision, g.bounded, fun _ _ => trivial⟩
  exact
    { getCI := by
        intro addr ptr h h' cs a ev _ res good ha
        rcases splitKey (ixAddr a) (ixAddr_not_marker a) res with hnew | hold
        · have hf0 : (consCtx c (.indInfo cvF caps)).env.find? (keyOf c.t (ixAddr a)) =
              some (.indInfo cvF caps) := by
            rw [hnew]
            exact findFormer
          refine ⟨.indInfo cvF caps, ?_, hformer.getCI addr ptr h h' cs a ev good.raw ha hnew⟩
          rw [(ctorStage c cvF caps).key_eq res]
          exact hf0
        · obtain ⟨ci, hf, hrep⟩ := h₁.getCI addr ptr h h' cs a ev trivial hold (good₁ good) ha
          refine ⟨ci, ?_, hrep.rekey_mono keep (stored_name_ne h₁ hf)⟩
          rw [keep _ hold]
          exact hext.find hf
      getCprj := by
        intro bp ptr i j h h' cs b ev _ hfam good hb
        by_cases hnew : keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cvF.name
        · refine ⟨hformer.getCprj bp ptr i j h h' cs b ev good.raw hb hnew,
            fun cv nP nF hf => ?_⟩
          exfalso
          obtain ⟨hf₁, -⟩ := ctorOld hf
          exact notFormer (iprjAddr_not_marker _ _) (h₁.ctorIndRes _ _ _ _ _ _ hf₁) hnew
        · obtain ⟨⟨ci₀, hrep₀⟩, hall⟩ :=
            h₁.getCprj bp ptr i j h h' cs b ev trivial (fam hfam hnew) (good₁ good) hb
          refine ⟨hrep₀.rekey_exists keep, fun cv nP nF hf => ?_⟩
          obtain ⟨hf₁, -⟩ := ctorOld hf
          exact (hall cv nP nF hf₁).rekey_mono keep (stored_name_ne h₁ hf₁)
      getIprj := by
        intro bp ptr i h h' cs b ev _ hfam good hb
        by_cases hnew : keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cvF.name
        · have hf0 : (consCtx c (.indInfo cvF caps)).env.find?
              (keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvF caps) := by
            rw [hnew]
            exact findFormer
          have e : (ctorStage c cvF caps).κ (iprjAddr (ixAddr b) (ZMod.val i)) =
              keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) :=
            Ctx.stagedOver_key_of_find (c := consCtx c (.indInfo cvF caps)) (pre := c.env) hf0
          refine ⟨.indInfo cvF caps, ?_, hformer.getIprj bp ptr i h h' cs b ev good.raw hb hnew⟩
          rw [e]
          exact hf0
        · obtain ⟨ci, hf, hrep⟩ :=
            h₁.getIprj bp ptr i h h' cs b ev trivial (fam hfam hnew) (good₁ good) hb
          refine ⟨ci, ?_, hrep.rekey_mono keep (stored_name_ne h₁ hf)⟩
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
        by_cases hnew : keyOf c.t (iprjAddr (ixAddr b) (ZMod.val i)) = cvF.name
        · exact absurd hperm (formerNoProj hnew (iprjAddr_not_marker _ _))
        · obtain ⟨⟨ci, hf, hrep⟩, htab⟩ :=
            h₁.projTables bp ip ptr h h' cs b i ev trivial good hb hip (fam hfam hnew)
              (famPerm (fam hfam hnew))
          refine ⟨⟨ci, ?_, hrep.rekey_mono keep (stored_name_ne h₁ hf)⟩, ?_⟩
          · rw [keep _ (h₁.findRes _ _ hf)]
            exact hext.find hf
          · intro sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hctor'
            obtain ⟨hc₁, ek⟩ := ctorOld hctor'
            obtain ⟨tbl, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11⟩ :=
              htab sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hc₁
            have ei := keep _ (h₁.ctorIndRes _ _ _ _ _ _ hc₁)
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
          j cvC nP nF hctor'
        obtain ⟨hc₁, ek⟩ := ctorOld hctor'
        obtain ⟨tbl, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, ht11⟩ :=
          h₁.projTablesAt bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG
            hs hld hblk j cvC nP nF hc₁
        have ei := keep _ (h₁.ctorIndRes _ _ _ _ _ _ hc₁)
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
        have hne : (ConstantInfo.indInfo cvT caps') ≠ .indInfo cvF caps := by
          intro e
          rw [e] at hfT
          exact notFormer (iprjAddr_not_marker _ _) (h₁.ctorIndRes _ _ _ _ _ _ hC₁)
            (formerMember ev good ha (formerKey hfT) hld hb)
        obtain ⟨hT₁, eT⟩ := old hfT hne
        obtain ⟨hu1, hu2, hu3⟩ := h₁.unitLike ap ptr h h' cs a nl ty u blk p i b cvT caps' cvC
          nPc ev good ha hld hb hT₁ hfew hC₁
        refine ⟨hu1, hu2, ?_⟩
        rw [eT]
        exact hu3.imp id (fun hr => ⟨hr.1, fun us => hext.isUnitLikeTy_mono (hr.2 us)⟩)
      unitLikeRaw := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps' ev al res good ha hld hb hfT hfew hz hn
        by_cases e : (ConstantInfo.indInfo cvT caps') = .indInfo cvF caps
        · obtain ⟨e1, e2⟩ := ConstantInfo.indInfo.inj e
          rw [e1, e2] at hfT
          rw [e2]
          have hnm : cvF.name = (ctorStage c cvF caps).κ (ixAddr a) := WhnfAux.name_of_find hfT
          rw [← hnm]
          exact hformer.unitLikeRaw ap ptr h h' cs a nl ty u blk p i b ev good ha (formerKey hfT)
            hld hb hfew hz hn
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
        have hnC : cvc.name = (ctorStage c cvF caps).κ (ixAddr ac) := WhnfAux.name_of_find hfC
        have hfC' : (ctorStage c cvF caps).env.find?
            ((ctorStage c cvF caps).κ (cprjAddr (ixAddr b) (ZMod.val i) j)) =
              some (.ctorInfo cvc cnP cnF) := by
          rw [← hnm, hnC]
          exact hfC
        obtain ⟨hCj, eN⟩ := ctorOld hfC'
        have hrI := h₁.ctorIndRes _ _ _ _ _ _ hCj
        have hne : (ConstantInfo.indInfo cvT caps') ≠ .indInfo cvF caps := by
          intro e
          rw [e] at hfT
          exact notFormer (iprjAddr_not_marker _ _) hrI (formerKey hfT)
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
        have hne : (ConstantInfo.indInfo cvT caps') ≠ .indInfo cvF caps := by
          intro e
          rw [e] at hfT
          exact notFormer (iprjAddr_not_marker _ _) (h₁.ctorIndRes _ _ _ _ _ _ hC₁)
            (formerMember ev good hpa (formerKey hfT) hld hb)
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
        have ei := keep _ (h₁.ctorIndRes _ _ _ _ _ _ hc₁)
        rw [ei] at htbl
        exact h₁.projTablesGuard bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hc₁
          (consCtx_find_old (c := c) (cn := .indInfo cvF caps) htbl (fun e => by cases e))
      canonical := h₁.canonical
      storedRes := by
        intro a ci hf
        have e : (ctorStage c cvF caps).κ a = keyOf c.t a :=
          Ctx.stagedOver_key_of_find (c := consCtx c (.indInfo cvF caps)) (pre := c.env) hf
        rw [e]
        exact Resolved.ne
      findRes := by
        intro a ci hf
        by_cases e : ci = .indInfo cvF caps
        · rw [← WhnfAux.name_of_find hf, e]
          exact hFres
        · rw [(old hf e).2]
          exact h₁.findRes a ci (old hf e).1
      ctorIndRes := by
        intro b i j cv nP nF hf
        obtain ⟨hf₁, -⟩ := ctorOld hf
        have hr := h₁.ctorIndRes b i j cv nP nF hf₁
        rw [keep _ hr]
        exact hr
      ctorIndPerm := by
        intro a b i j cvT caps' cv nP nF hf hnI hfC
        obtain ⟨hC₁, -⟩ := ctorOld hfC
        have hrI := h₁.ctorIndRes b i j cv nP nF hC₁
        have hne : (ConstantInfo.indInfo cvT caps') ≠ .indInfo cvF caps := by
          intro e
          have e1 : cvT = cvF := (ConstantInfo.indInfo.inj e).1
          rw [e1] at hnI
          apply notFormer (iprjAddr_not_marker b i) hrI
          have e3 : (ctorStage c cvF caps).κ (iprjAddr b i) = keyOf c.t (iprjAddr b i) :=
            (keep _ hrI).trans (c.stored.key_eq hrI)
          exact e3.symm.trans hnI.symm
        obtain ⟨hT₁, -⟩ := old hf hne
        exact ProjPermitted.of_keep keep
          (h₁.ctorIndPerm a b i j cvT caps' cv nP nF hT₁ (hnI.trans (keep _ hrI)) hC₁)
      roleRes := by
        intro r a hf hi hb
        have hr := h₁.roleRes r a hf hi hb
        rw [keep _ hr]
        exact hr }

/-- **The constructor stage's contract over a prefix that keeps the invariant**: what remains are
the freshness of the former's key and of its marker's key, and the load facts at the former. -/
theorem PrefixInv.ctorStageLoads {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (h : PrefixInv.{u} E t lim env)
    {cvF : ConstantVal .anon} {caps : IndCaps .anon} {f : _root_.Address}
    (hname : cvF.name = keyOf t f) (hfresh : env.find? cvF.name = none)
    (hmark : env.find? (keyOf t (projMarker f)) = none)
    (hnt : ∀ T : KKey, cvF.name ≠ Ix.Kernel.projTableName T)
    (hformer : FormerLoads ⟨E, env, t, lim⟩ cvF caps) :
    ScopedLoadFacts (ctorStage ⟨E, env, t, lim⟩ cvF caps) :=
  stagedLoads_cons_former (c := ⟨E, env, t, lim⟩) h.loads h.tableWf hname hfresh hmark hnt
    h.etaStable hformer

end IxVM.Refinement.Decl
