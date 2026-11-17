import IxVMRefinement.Assembly.PointUseSites
import IxVMRefinement.Assembly.NativeBlockNewLoads

/-! # The load facts a constructors-only family is never asked

The load contract's fields `projTables`, `projTablesAt`, `unitLike`, `unitLikeRaw`, `eta` and
`etaIota` speak of a stored family with a projection table, a unit-like flag or an η flag. A
family the constructors-only install stores has none of them (empty capability record, no
table), and none of these fields is asked at it: each premise is an observation the circuit
makes only at a block it treats as native (`block_is_modeled = 0`, through `proj_ctor`'s
assertion), or at a block of at most one inductive (`FewInductives`, `block_is_multi = 0`), or at
a structure that is not recursive (`struct_is_rec ≠ 1`). At the installed block these fail:

* at two or more inductives (`PointShape`'s first case) from the record and the dispatch's
  specification (`few_not_multi`, `multi_not_zero`) and `ModeledAt`;
* at one inductive (`NestedGate`) from the gate's three facts.

The family a premise names is the installed block's where a new constant witnesses it (`hfam`,
the install's `FamNew` fact) at a block a run hashed (the L1 lemmas `hashedBlockAt_of_*`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

section

variable {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
  {cb : Ixon.Constant} {ms : Array Ixon.MutConst}

/-- **The install's family fact**, the hypothesis every theorem here takes: a family a new
constant witnesses at a block a run hashed is a member of the installed block. -/
def PointFamNew (c : Core.Ctx) (new : List (ConstantInfo .anon)) (B : _root_.Address)
    (ms : Array Ixon.MutConst) : Prop :=
  ∀ (b : _root_.Address) (i : Nat), Core.HashedBlockAt c.E b → i < UInt64.size →
    FamNew (appCtx c new).stored new b i → b = B ∧ ∃ ind : Ixon.Inductive, ms[i]? = some (.indc ind)

/-- The record at the installed block, as the store's decoding. -/
theorem PointInstall.recordAt (hI : PointInstall c new B cb ms) :
    Ix.Cert.recordAt c.E B = some cb :=
  recordAt_of_recordOf hI.decoded hI.block

/-- **A load of a one-member block's former reads the record's counts.** -/
theorem PointInstall.counts_one (hI : PointInstall c new B cb ms) {ind : Ixon.Inductive}
    (hms : ms = #[.indc ind]) {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {a : Bytes.Address} {nl ty u blk : SourceValue F} {p m n i : F}
    (ev : ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs) (good : Core.Good (appCtx c new) cs)
    (ha : Bytes.RepAddressRef Core.addrTy h a ap)
    (hld : loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, ty, .field p, .field m, .field n, u, blk, .field i]))
    (hxa : Core.ixAddr a = Core.iprjAddr B 0) :
    ZMod.val m = ind.indices.toNat ∧ ZMod.val n = ind.ctors.size := by
  subst hms
  have hrecA : recordOf c.E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hxa]
    exact hI.formerRec 0 ind rfl
  obtain ⟨tyPtr, blkPtr, hld₀, -, hi56, hc56⟩ :=
    former_get_ci_value good.1 good.2 ha ev hrecA hI.block hI.muts
  rw [hld₀] at hld
  have hv := Except.ok.inj hld
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨-, -, -, hm, hn, -⟩ := hv
  exact ⟨field_count_eq hi56 hm, field_count_eq hc56 hn⟩

/-- The member index of a one-member block is `0`. -/
theorem idx_zero_of_one {ind ind' : Ixon.Inductive} {i : Nat}
    (h : (#[.indc ind] : Array Ixon.MutConst)[i]? = some (.indc ind')) : i = 0 := by
  have h1 : i < (#[.indc ind] : Array Ixon.MutConst).size := (Array.getElem?_eq_some_iff.mp h).1
  have h2 : (#[.indc ind] : Array Ixon.MutConst).size = 1 := rfl
  omega

/-! ## The four fields -/

/-- **`NewLoads.projTables`, never asked**: an observed projection makes its block native. -/
theorem PointInstall.newProjTables (hI : PointInstall c new B cb ms) (hmod : ModeledAt c.E B)
    (hfam : PointFamNew c new B ms) :
    ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address) (i : F),
      ObsFn Core.W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs →
      Core.Good (appCtx c new) cs → Bytes.RepAddressRef Core.addrTy h b bp → ip = .field i →
      FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) →
      Core.ProjPermitted (appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) →
      (∃ ci, (appCtx c new).env.find? ((appCtx c new).stored.κ
          (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) = some ci ∧
        Core.CIPtrRep (appCtx c new).stored.κ h' ptr ci) ∧
      ∀ (sap sptr nl ty np u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
        (s : Bytes.Address),
        ObsFn Core.W "Ingress::get_ci" [sap] h1 sptr h2 cs1 → Core.Good (appCtx c new) cs1 →
        Bytes.RepAddressRef Core.addrTy h1 s sap →
        loadValue h2 sptr =
          .ok (.construct Core.kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
        Bytes.RepAddressRef Core.addrTy h2 b blk →
        ∀ (j : Nat) (cvC : ConstantVal .anon) (nP nF : Nat),
          (appCtx c new).env.find? ((appCtx c new).stored.κ
            (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
          (cvC.type.stripPis 1).isSome = true →
          ∃ tbl : Ix.Kernel.ProjTable .anon,
            (appCtx c new).env.find? (Ix.Kernel.projTableName
              ((appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
              some (.projInfo tbl) ∧
            tbl.structName = (appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) ∧
            tbl.ctor = (appCtx c new).stored.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j) ∧
            tbl.numParams = nP ∧ tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
            (∀ cb' xs ind', Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb' → cb'.info = .muts xs →
              xs[ZMod.val i]? = some (.indc ind') → nP = ind'.params.toNat) ∧
            (∀ f, f < nF → (appCtx c new).env.findProj? tbl.structName f = some (tbl.entry f) ∧
              Ix.Kernel.TowerHead (appCtx c new).env (tbl.entry f)) ∧
            Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
            (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
              tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
            ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
              ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort := by
  intro bp ip ptr h h' cs b i ev good hb hip hfam' hperm
  exfalso
  subst hip
  have hbh := L1.hashedBlockAt_of_proj_ctor (c := appCtx c new) good ev hb rfl
  obtain ⟨hbB, -⟩ := hfam _ _ hbh (val_lt_uint64 _) hfam'
  have hn := nativeAt_of_projCtor (c := appCtx c new) ev good hb
  rw [hbB] at hn
  exact hmod hn

/-- **`NewLoads.projTablesAt`, never asked**: its premise observes the dispatch answering `0`. -/
theorem PointInstall.newProjTablesAt (hI : PointInstall c new B cb ms) (hmod : ModeledAt c.E B)
    (hfam : PointFamNew c new B ms) :
    ∀ (bp sap ptr nl ty np u blk : SourceValue F) (h h' h1 h2 : Heap F)
      (cs cs1 : List (Call F)) (b s : Bytes.Address) (i : F),
      ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' cs →
      Core.Good (appCtx c new) cs → Bytes.RepAddressRef Core.addrTy h b bp →
      ObsFn Core.W "Ingress::get_ci" [sap] h1 ptr h2 cs1 → Core.Good (appCtx c new) cs1 →
      Bytes.RepAddressRef Core.addrTy h1 s sap →
      loadValue h2 ptr =
        .ok (.construct Core.kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
      Bytes.RepAddressRef Core.addrTy h2 b blk →
      ∀ (j : Nat) (cvC : ConstantVal .anon) (nP nF : Nat),
        (appCtx c new).env.find? ((appCtx c new).stored.κ
          (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
        ConstantInfo.ctorInfo cvC nP nF ∈ new → 0 < nF →
        ∃ tbl : Ix.Kernel.ProjTable .anon,
          (appCtx c new).env.find? (Ix.Kernel.projTableName
            ((appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
            some (.projInfo tbl) ∧
          tbl.structName = (appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) ∧
          tbl.ctor = (appCtx c new).stored.κ (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j) ∧
          tbl.numParams = nP ∧ tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
          (∀ cb' xs ind', Ix.Cert.recordAt c.E (Core.ixAddr b) = some cb' → cb'.info = .muts xs →
            xs[ZMod.val i]? = some (.indc ind') → nP = ind'.params.toNat) ∧
          (∀ f, f < nF → (appCtx c new).env.findProj? tbl.structName f = some (tbl.entry f) ∧
            Ix.Kernel.TowerHead (appCtx c new).env (tbl.entry f)) ∧
          Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
          (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
            tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
          ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
            ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort := by
  intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG hs hld hblk
    j cvC nP nF hctor hm hnF
  exfalso
  have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) hgG evG hs hld hblk
  obtain ⟨hbB, -⟩ := hfam _ _ hbh (val_lt_uint64 _) (Or.inr ⟨j, cvC, nP, nF, hctor, hm⟩)
  have hn := nativeAt_of_obs (c := appCtx c new) evM hgM hb
  rw [hbB] at hn
  exact hmod hn

/-- **`NewLoads.unitLike`, never asked**: the family is the installed block's, which has two or
more inductives (no `FewInductives`) or one with no field-less single constructor. -/
theorem PointInstall.newUnitLike (hI : PointInstall c new B cb ms) (hshape : PointShape c.E B ms)
    (hfam : PointFamNew c new B ms) :
    ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : ConstantVal .anon) (caps' : IndCaps .anon) (cvC : ConstantVal .anon) (nPc : Nat),
      ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a ap →
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
      Bytes.RepAddressRef Core.addrTy h' b blk →
      (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.ixAddr a)) =
        some (.indInfo cvT caps') →
      Core.FewInductives (appCtx c new) (Core.ixAddr b) →
      (appCtx c new).env.find? ((appCtx c new).stored.κ
        (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvC nPc 0) →
      (ConstantInfo.indInfo cvT caps' ∈ new ∨ ConstantInfo.ctorInfo cvC nPc 0 ∈ new) →
      caps'.unitlike = true ∧ caps'.unitParams = ZMod.val p ∧
        (Ix.Kernel.reservedBasisNames.contains ((appCtx c new).stored.κ (Core.ixAddr a)) = false ∨
          (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (appCtx c new).env
            (.const ((appCtx c new).stored.κ (Core.ixAddr a)) us) = true)) := by
  intro ap ptr h h' cs a nl ty u blk p i b cvT caps' cvC nPc ev good ha hld hb hfT hfew hfC hm
  exfalso
  have hx := get_ci_induct_addr ev good.2 ha hld hb
  have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) good ev ha hld hb
  have hfamAt : FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) := by
    rcases hm with hm | hm
    · refine Or.inl ⟨cvT, caps', ?_, hm⟩
      rw [← hx]
      exact hfT
    · exact Or.inr ⟨0, cvC, nPc, 0, hfC, hm⟩
  obtain ⟨hbB, ind₀, hmem⟩ := hfam _ _ hbh (val_lt_uint64 _) hfamAt
  rcases hshape with h2 | ⟨ind, hms, hN⟩
  · exact few_not_multi (c := appCtx c new) ⟨cb, ms, hI.recordAt, hI.muts, h2⟩ (by rw [← hbB]; exact hfew)
  · subst hms
    have hi0 : ZMod.val i = 0 := idx_zero_of_one hmem
    have hxa : Core.ixAddr a = Core.iprjAddr B 0 := by rw [hx, hbB, hi0]
    obtain ⟨hidx, hsz⟩ := hI.counts_one rfl ev good ha hld hxa
    rw [ZMod.val_zero] at hidx
    rw [ZMod.val_one] at hsz
    obtain ⟨ct, cty, cty', hct, -, -, -, -, -, hfC₀⟩ := hI.ctor 0 ind rfl 0 (by omega)
    rw [hbB, hi0, appCtx_key_of_find hfC₀, hfC₀] at hfC
    injection hfC with hfC
    injection hfC with hcvC hnpC hnf
    exact hN.noUnit hidx.symm hsz.symm ct hct hnf

/-- **`NewLoads.unitLikeRaw`, never asked**: as `unitLike`, the one-member case through the
observed `struct_is_rec = 0`. -/
theorem PointInstall.newUnitLikeRaw (hI : PointInstall c new B cb ms)
    (hshape : PointShape c.E B ms) (hfam : PointFamNew c new B ms) :
    ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : ConstantVal .anon) (caps' : IndCaps .anon),
      ObsFn Core.W "Ingress::get_ci" [ap] h ptr h' cs → Core.Good (appCtx c new) cs →
      Bytes.RepAddressRef Core.addrTy h a ap →
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
      Bytes.RepAddressRef Core.addrTy h' b blk →
      (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.ixAddr a)) =
        some (.indInfo cvT caps') →
      ConstantInfo.indInfo cvT caps' ∈ new → Core.FewInductives (appCtx c new) (Core.ixAddr b) →
      Core.ZeroFieldCtorLoad (appCtx c new).stored b i → Core.NonrecursiveLoad (appCtx c new).stored a →
      caps'.unitlike = true ∧ caps'.unitParams = ZMod.val p ∧
        (Ix.Kernel.reservedBasisNames.contains ((appCtx c new).stored.κ (Core.ixAddr a)) = false ∨
          (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy (appCtx c new).env
            (.const ((appCtx c new).stored.κ (Core.ixAddr a)) us) = true)) := by
  intro ap ptr h h' cs a nl ty u blk p i b cvT caps' ev good ha hld hb hfT hm hfew hz hnr
  exfalso
  have hx := get_ci_induct_addr ev good.2 ha hld hb
  have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) good ev ha hld hb
  have hfamAt : FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) := by
    refine Or.inl ⟨cvT, caps', ?_, hm⟩
    rw [← hx]
    exact hfT
  obtain ⟨hbB, ind₀, hmem⟩ := hfam _ _ hbh (val_lt_uint64 _) hfamAt
  rcases hshape with h2 | ⟨ind, hms, hN⟩
  · exact few_not_multi (c := appCtx c new) ⟨cb, ms, hI.recordAt, hI.muts, h2⟩ (by rw [← hbB]; exact hfew)
  · subst hms
    have hi0 : ZMod.val i = 0 := idx_zero_of_one hmem
    have hxa : Core.ixAddr a = Core.iprjAddr B 0 := by rw [hx, hbB, hi0]
    obtain ⟨-, hsz⟩ := hI.counts_one rfl ev good ha hld hxa
    rw [ZMod.val_one] at hsz
    have hv := hN.rec hsz.symm hnr.ap _ hnr.before hnr.after hnr.calls a hnr.observed
      hnr.good.1 hnr.good.2 hnr.parentRep hxa
    exact absurd (Value.field.inj hv) (by decide)

/-! ## The two η fields -/

/-- **The two η fields, never asked** (`BlockEta`): `eta`'s premise observes the dispatch
answering `0`; `etaIota`'s observes `block_is_multi = 0` (two or more inductives: refused by the
dispatch's specification) and `struct_is_rec ≠ 1` (one inductive: the gate). -/
theorem PointInstall.blockEta (hI : PointInstall c new B cb ms)
    (hinv : Decl.PrefixInv.{u} c.E c.t c.lim c.env) (hshape : PointShape c.E B ms)
    (hmod : ModeledAt c.E B) (hfam : PointFamNew c new B ms) : BlockEta c new where
  eta := by
    intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1 hC hname hnF
      ev hg hb hld hT hmodeled hpi hnz hrec haddr hm
    exfalso
    have hbh := L1.hashedBlockAt_of_get_ci_iprj (c := appCtx c new) hg hb ev
    have hfamAt : FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) := by
      rcases hm with hm | hm
      · refine Or.inr ⟨j, cvc, cnP, cnF, ?_, hm⟩
        have hn : cvc.name = (appCtx c new).stored.κ (Core.ixAddr ac) :=
          Ix.Kernel.Semantics.Env.find?_name hC
        rw [← hname, hn]
        exact hC
      · exact Or.inl ⟨cvT, caps, hT, hm⟩
    obtain ⟨hbB, -⟩ := hfam _ _ hbh (val_lt_uint64 _) hfamAt
    obtain ⟨bq, h3, h4, cs3, evM, hgM, hbq⟩ := hmodeled
    have hn := nativeAt_of_obs (c := appCtx c new) evM hgM hbq
    rw [hbB] at hn
    exact hmod hn
  etaIota := by
    intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev hg hpa hld hb hT hC
      hmulti hrec hpi hnz hm
    exfalso
    have hx := get_ci_induct_addr ev hg.2 hpa hld hb
    have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) hg ev hpa hld hb
    have hfamAt : FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i) := by
      rcases hm with hm | hm
      · refine Or.inl ⟨cvT, caps, ?_, hm⟩
        rw [← hx]
        exact hT
      · exact Or.inr ⟨0, cvc, cnP, cnF, hC, hm⟩
    obtain ⟨hbB, ind₀, hmem⟩ := hfam _ _ hbh (val_lt_uint64 _) hfamAt
    rcases hshape with h2 | ⟨ind, hms, hN⟩
    · obtain ⟨bq, h3, h4, cs3, evM, hgM, hbq⟩ := hmulti
      exact multi_not_zero hinv ⟨cb, ms, hI.recordAt, hI.muts, h2⟩ evM hgM.1 hgM.2 hbq hbB
    · subst hms
      have hi0 : ZMod.val i = 0 := idx_zero_of_one hmem
      have hxa : Core.ixAddr pa = Core.iprjAddr B 0 := by rw [hx, hbB, hi0]
      obtain ⟨-, hsz⟩ := hI.counts_one rfl ev hg hpa hld hxa
      rw [ZMod.val_one] at hsz
      obtain ⟨sp, v, h5, h6, cs5, evR, hne, hgR, hpR⟩ := hrec
      exact hne (hN.rec hsz.symm sp v h5 h6 cs5 pa evR hgR.1 hgR.2 hpR hxa)

end

end IxVM.Refinement.Typing
