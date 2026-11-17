import IxVMRefinement.Assembly.NativeBlockNewFacts

/-! # The new family's projection-table facts after a native block's install

At a structure-like block (one constructor, no index) the install also stores the family's
projection table. `BlockTable` is what the table fields of `NewLoads` read of it:

* `table`: the table at the family's table name, its structure and constructor keys, and at the
  stored constructor `0` its counts, level parameters, entries (found, with their head data),
  bodies, guards and the constructor's binder zero-ness;
* `newTable`: a new table is the family's;
* `ctorTele`: each new constructor's telescope ends in the family;
* `ctorAt`: every constructor the new environment stores at a constructor key of the block is new
  (the prefix stores none: it does not store the former's key);
* `guard`: **the guard conjunct of `projTablesGuard` at the new table** — the circuit's
  `proj_guard` recomputes the field's sort (`k_ensure_sort` on the loaded constructor's field
  domains) and folds the sorts of earlier fields the later binders use; the table's guard is
  `structProjGuards` of the field sorts IxC's constructor stage read (`FieldSortsJ`). Relating
  the two needs that two inferred sorts of one domain agree at every valuation (no such lemma for
  `Rules.Infer` in IxC); it is kept as this named clause.

The fields: `BlockInstall.newGetCprjFound`, `BlockInstall.newProjTables`,
`BlockInstall.newProjTablesAt`, `BlockInstall.newProjTablesGuard`.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The new projection table, as the table fields read it** (module docstring). -/
structure BlockTable (c : Core.Ctx) (new : List (ConstantInfo .anon)) (B : _root_.Address)
    (ind : Ixon.Inductive) : Prop where
  table : ind.indices.toNat = 0 → ind.ctors.size = 1 →
    ∃ tbl : Ix.Kernel.ProjTable .anon,
      (appCtx c new).env.find? (Ix.Kernel.projTableName (Core.keyOf c.t (Core.iprjAddr B 0))) =
        some (.projInfo tbl) ∧
      tbl.structName = Core.keyOf c.t (Core.iprjAddr B 0) ∧
      tbl.ctor = Core.keyOf c.t (Core.cprjAddr B 0 0) ∧
      ∀ (cvC : ConstantVal .anon) (nP nF : Nat),
        (appCtx c new).env.find? (Core.keyOf c.t (Core.cprjAddr B 0 0)) =
          some (.ctorInfo cvC nP nF) →
        tbl.numParams = nP ∧ tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
        nP = ind.params.toNat ∧
        (∀ f, f < nF → (appCtx c new).env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead (appCtx c new).env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort
  newTable : ∀ tbl, ConstantInfo.projInfo tbl ∈ new →
    tbl.structName = Core.keyOf c.t (Core.iprjAddr B 0)
  ctorTele : ∀ j < ind.ctors.size, ∀ (cvC : ConstantVal .anon) (nP nF : Nat),
    (appCtx c new).env.find? (Core.keyOf c.t (Core.cprjAddr B 0 j)) =
      some (.ctorInfo cvC nP nF) →
    Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true
  ctorAt : Core.HashedBlockAt c.E B → ∀ (j : Nat) (cv : ConstantVal .anon) (nP nF : Nat),
    (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.cprjAddr B 0 j)) =
      some (.ctorInfo cv nP nF) →
    ConstantInfo.ctorInfo cv nP nF ∈ new
  guard : ∀ (i : F), ZMod.val i = 0 → ∀ (j : Nat) (cvC : ConstantVal .anon) (nP nF : Nat)
      (tbl : Ix.Kernel.ProjTable .anon),
    (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.cprjAddr B 0 j)) =
      some (.ctorInfo cvC nP nF) →
    (appCtx c new).env.find?
        (Ix.Kernel.projTableName ((appCtx c new).stored.κ (Core.iprjAddr B 0))) =
      some (.projInfo tbl) →
    Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
    ∀ (f : F) (rc bp' rg : SourceValue F) (hg hg' : Heap F) (csg : List (Call F))
      (g : Core.KLevel) (us : List Core.KLevel) (b : Bytes.Address),
      ZMod.val f < nF → us.length = tbl.levelParams.length →
      ObsFn Core.W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg →
      Core.Good (appCtx c new) csg → Core.RCRep c.t c.lim hg rc →
      Bytes.RepAddressRef Core.addrTy hg b bp' → Core.ixAddr b = B →
      IxVM.Refinement.KernelLevels.RepKLevel hg' g rg →
      (∀ φ, Ix.Kernel.Level.eval φ
        (Ix.Kernel.Level.subst (List.range us.length) us g) = 0) →
      ∀ φ, Ix.Kernel.Level.eval φ
        (Ix.Kernel.Level.subst tbl.levelParams us (tbl.entry (ZMod.val f)).fieldSort) = 0

section
variable {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
  {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}

/-- **A constructor load of the new family finds the stored constructor** and represents it. -/
theorem BlockInstall.newGetCprjFound (hI : BlockInstall c new B cb ind caps)
    {bp ptr : SourceValue F} {i j : F} {h h' : Heap F} {cs : List (Call F)} {b : Bytes.Address}
    (ev : ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs)
    (hfam : FamNew (appCtx c new).stored new (Core.ixAddr b) (ZMod.val i))
    (good : Core.Good (appCtx c new) cs) (hb : Bytes.RepAddressRef Core.addrTy h b bp) :
    ∃ ci, (appCtx c new).env.find? ((appCtx c new).stored.κ
        (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) = some ci ∧
      Core.CIPtrRep (appCtx c new).stored.κ h' ptr ci := by
  have hbh := L1.hashedBlockAt_of_get_ci_cprj (c := appCtx c new) good hb ev
  obtain ⟨hbB, hi0⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
  have hblock' : recordOf c.E (Core.ixAddr b) = some cb := by
    rw [hbB]
    exact hI.block
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    -⟩ := L1.get_ci_cprj_origin_spec good.2 hb ev
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock'
  have hbB' : blkBytes = lcB.rawBytes := Core.load_escape hgetB good.1 blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB', hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : (#[.indc ind] : Array Ixon.MutConst) = ms' :=
    Ixon.ConstantInfo.muts.inj (hI.muts.symm.trans hcb)
  subst hmsEq
  have hiEq : ind = ind' := by
    have hms0 : (#[.indc ind] : Array Ixon.MutConst).toList[ZMod.val i]? = some (.indc ind') := hms
    rw [hi0] at hms0
    exact Ixon.MutConst.indc.inj (Option.some.inj hms0)
  subst hiEq
  have hct : ind.ctors[ZMod.val j]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hcts
  have hjs : ZMod.val j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  obtain ⟨ct, cty, cty', -, -, -, -, -, -, hfC⟩ := hI.ctor (ZMod.val j) hjs
  have hfA : (appCtx c new).env.find?
      (Core.keyOf c.t (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) =
      some (.ctorInfo ⟨Core.keyOf c.t (Core.cprjAddr B 0 (ZMod.val j)), List.range ct.lvls.toNat,
        cty'⟩ ct.params.toNat ct.fields.toNat) := by
    rw [hbB, hi0]
    exact hfC
  have hκ := appCtx_key_of_find hfA
  have hfA' : (appCtx c new).env.find? ((appCtx c new).stored.κ
      (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) (ZMod.val j))) =
      some (.ctorInfo ⟨Core.keyOf c.t (Core.cprjAddr B 0 (ZMod.val j)), List.range ct.lvls.toNat,
        cty'⟩ ct.params.toNat ct.fields.toNat) := by
    rw [hκ]
    exact hfA
  exact ⟨_, hfA', (hI.newGetCprj bp ptr i j h h' cs b ev hfam good hb).2 _ _ _ hfA'⟩

/-- A new constant other than a table, found at an address's key, is at the table's key. -/
theorem BlockInstall.newFoundKey (hI : BlockInstall c new B cb ind caps) {x : _root_.Address}
    {ci : ConstantInfo .anon}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some ci) (hm : ci ∈ new)
    (hnt : ∀ tbl, ci ≠ .projInfo tbl) : (appCtx c new).stored.κ x = Core.keyOf c.t x := by
  have hn : ci.name = (appCtx c new).stored.κ x := Core.WhnfAux.name_of_find hf
  apply (appCtx c new).stored.key_eq
  rw [← hn]
  rcases hI.newName ci hm with hT | ⟨j, hj, hC⟩ | ⟨tbl, htbl⟩
  · rw [hT]
    exact Core.Resolved.ne
  · rw [hC]
    exact Core.Resolved.ne
  · exact absurd htbl (hnt tbl)

/-- A constructor the new environment stores at a constructor key of the new block, at a block
of one constructor, is constructor `0`. -/
theorem BlockInstall.ctorKey_zero (hI : BlockInstall c new B cb ind caps)
    (hT : BlockTable c new B ind) (hbh : Core.HashedBlockAt c.E B) (hsz : ind.ctors.size = 1)
    {j : Nat} {cv : ConstantVal .anon} {nP nF : Nat}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.cprjAddr B 0 j)) =
      some (.ctorInfo cv nP nF)) :
    (appCtx c new).stored.κ (Core.cprjAddr B 0 j) = Core.keyOf c.t (Core.cprjAddr B 0 0) := by
  have hm := hT.ctorAt hbh j cv nP nF hf
  obtain ⟨j', hj', hk⟩ := hI.newCtor hf hm
  have hj0 : j' = 0 := by omega
  subst hj0
  rw [hI.newFoundKey hf hm (fun tbl h => by cases h)]
  exact hk


/-- **The table conclusion at the new family**, from an inductive load that names the new block's
member `0` with no index and one constructor, and a constructor stored at a constructor key of
the block. -/
theorem BlockInstall.tableAt (hI : BlockInstall c new B cb ind caps) (hT : BlockTable c new B ind)
    {sap sptr nl ty np u blk : SourceValue F} {h1 h2 : Heap F} {cs1 : List (Call F)}
    {s b : Bytes.Address} {i : F}
    (evS : ObsFn Core.W "Ingress::get_ci" [sap] h1 sptr h2 cs1) (gS : Core.Good (appCtx c new) cs1)
    (hsS : Bytes.RepAddressRef Core.addrTy h1 s sap)
    (hldS : loadValue h2 sptr =
      .ok (.construct Core.kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]))
    (hbS : Bytes.RepAddressRef Core.addrTy h2 b blk) (hbB : Core.ixAddr b = B)
    (hi0 : ZMod.val i = 0) {j : Nat} {cvC : ConstantVal .anon} {nP nF : Nat}
    (hctor : (appCtx c new).env.find? ((appCtx c new).stored.κ
      (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF)) :
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
  have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) gS evS hsS hldS hbS
  have hxs := get_ci_induct_addr evS gS.2 hsS hldS hbS
  have hxs' : Core.ixAddr s = Core.iprjAddr B 0 := by rw [hxs, hbB, hi0]
  obtain ⟨tyPtr, blkPtr, hld₀, hp56, hi56, hc56⟩ := former_get_ci_value gS.1 gS.2 hsS evS
    (by rw [hxs']; exact hI.formerRec) hI.block hI.muts
  rw [hld₀] at hldS
  have hv := Except.ok.inj hldS
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
  obtain ⟨-, -, -, hm, hn, -⟩ := hv
  have hidx0 : ind.indices.toNat = 0 := by
    have e := field_count_eq hi56 hm
    rw [ZMod.val_zero] at e
    exact e.symm
  have hsz : ind.ctors.size = 1 := by
    have e := field_count_eq hc56 hn
    rw [ZMod.val_one] at e
    exact e.symm
  have hbhB : Core.HashedBlockAt c.E B := by
    rw [← hbB]
    exact hbh
  rw [hbB, hi0] at hctor ⊢
  have hk0 := hI.ctorKey_zero hT hbhB hsz hctor
  rw [hk0] at hctor ⊢
  obtain ⟨tbl, hft, hsn, hct, hall⟩ := hT.table hidx0 hsz
  obtain ⟨h1', h2', h3', h4', h5', h6', h7', h8'⟩ := hall cvC nP nF hctor
  obtain ⟨ty₀, ty', -, -, -, -, hfT⟩ := hI.former
  rw [appCtx_key_of_find hfT]
  refine ⟨tbl, hft, hsn, hct, h1', h2', h3', ?_, h5', h6', h7', h8'⟩
  intro cb' xs ind' hcb' hxs0 hmem
  have e1 : cb' = cb := Option.some.inj (hcb'.symm.trans (recordAt_of_recordOf hI.decoded hI.block))
  subst e1
  have e2 : xs = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hxs0.symm.trans hI.muts)
  subst e2
  have e3 : ind' = ind := (Ixon.MutConst.indc.inj (Option.some.inj hmem)).symm
  subst e3
  exact h4'

/-- **`NewLoads.projTables`.** -/
theorem BlockInstall.newProjTables (hI : BlockInstall c new B cb ind caps)
    (hT : BlockTable c new B ind) :
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
  intro bp ip ptr h h' cs b i ev good hb hip hfam hperm
  subst hip
  have hbh := L1.hashedBlockAt_of_proj_ctor (c := appCtx c new) good ev hb rfl
  obtain ⟨hbB, hi0⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
  obtain ⟨v, mid, cs_assert, cs_load, ev_assert, ev_load, hcalls⟩ :=
    Obs.«KernelModeled::proj_ctor».obs ev
  have hfound := hI.newGetCprjFound ev_load hfam (good.sub fun cl hcl => by simp [hcalls, hcl])
    (Bytes.repAddressRef_heapMono₂ Core.addrTy ev_assert.heap_extends hb)
  rw [ZMod.val_zero] at hfound
  refine ⟨hfound, ?_⟩
  intro sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hctor hbind
  exact hI.tableAt hT evS gS hsS hldS hbS hbB hi0 hctor

/-- **`NewLoads.projTablesAt`.** -/
theorem BlockInstall.newProjTablesAt (hI : BlockInstall c new B cb ind caps)
    (hT : BlockTable c new B ind) :
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
  have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx c new) hgG evG hs hld hblk
  obtain ⟨j', hj', hk⟩ := hI.newCtor hctor hm
  obtain ⟨hbB, hi0, -⟩ := cprj_key_block hI.wf hI.decoded hI.held (hI.ctorRec j' hj') hbh hk
  exact hI.tableAt hT evG hgG hs hld hblk hbB (toUInt64_zero_of_lt (val_lt_uint64 i) hi0) hctor

/-- **`NewLoads.projTablesGuard`**, its guard conjunct being `BlockTable.guard`. -/
theorem BlockInstall.newProjTablesGuard (hI : BlockInstall c new B cb ind caps)
    (hT : BlockTable c new B ind) :
    ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address) (i : F),
      ObsFn Core.W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs →
      Core.Good (appCtx c new) cs → Bytes.RepAddressRef Core.addrTy h b bp → ip = .field i →
      ∀ (j : Nat) (cvC : ConstantVal .anon) (nP nF : Nat) (tbl : Ix.Kernel.ProjTable .anon),
        (appCtx c new).env.find? ((appCtx c new).stored.κ
          (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
        (appCtx c new).env.find? (Ix.Kernel.projTableName
          ((appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) →
        (ConstantInfo.ctorInfo cvC nP nF ∈ new ∨ ConstantInfo.projInfo tbl ∈ new) →
        Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true ∧
        (Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
          ∀ (f : F) (rc bp' rg : SourceValue F) (hg hg' : Heap F) (csg : List (Call F))
            (g : Core.KLevel) (us : List Core.KLevel),
            ZMod.val f < nF → us.length = tbl.levelParams.length →
            ObsFn Core.W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg →
            Core.Good (appCtx c new) csg → Core.RCRep c.t c.lim hg rc →
            Bytes.RepAddressRef Core.addrTy hg b bp' →
            IxVM.Refinement.KernelLevels.RepKLevel hg' g rg →
            (∀ φ, Ix.Kernel.Level.eval φ
              (Ix.Kernel.Level.subst (List.range us.length) us g) = 0) →
            ∀ φ, Ix.Kernel.Level.eval φ
              (Ix.Kernel.Level.subst tbl.levelParams us (tbl.entry (ZMod.val f)).fieldSort) = 0) := by
  intro bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hctor htbl hm
  subst hip
  have hbh := L1.hashedBlockAt_of_proj_ctor (c := appCtx c new) good ev hb rfl
  have hBi : Core.ixAddr b = B ∧ ZMod.val i = 0 := by
    rcases hm with hm | hm
    · obtain ⟨j', hj', hk⟩ := hI.newCtor hctor hm
      obtain ⟨hbB, hi0, -⟩ := cprj_key_block hI.wf hI.decoded hI.held (hI.ctorRec j' hj') hbh hk
      exact ⟨hbB, toUInt64_zero_of_lt (val_lt_uint64 i) hi0⟩
    · have hn : (ConstantInfo.projInfo tbl).name = Ix.Kernel.projTableName
          ((appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i))) :=
        Core.WhnfAux.name_of_find htbl
      have hsn : tbl.structName =
          (appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) :=
        Ix.Kernel.projTableName_inj hn
      have hκ : (appCtx c new).stored.κ (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) =
          Core.keyOf c.t (Core.iprjAddr B 0) := hsn.symm.trans (hT.newTable tbl hm)
      have hκ' := (appCtx c new).stored.key_eq
        (a := Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) (by rw [hκ]; exact Core.Resolved.ne)
      exact iprj_key_block hI.wf hI.decoded hI.held hI.formerRec hbh (val_lt_uint64 i)
        (hκ'.symm.trans hκ)
  obtain ⟨hbB, hi0⟩ := hBi
  have hbhB : Core.HashedBlockAt c.E B := by
    rw [← hbB]
    exact hbh
  have hctorB : (appCtx c new).env.find? ((appCtx c new).stored.κ (Core.cprjAddr B 0 j)) =
      some (.ctorInfo cvC nP nF) := by
    rw [← hbB, ← hi0]
    exact hctor
  have hmC := hT.ctorAt hbhB j cvC nP nF hctorB
  obtain ⟨j', hj', hk⟩ := hI.newCtor hctorB hmC
  have hκC := hI.newFoundKey hctorB hmC (fun tbl h => by cases h)
  have hfC' : (appCtx c new).env.find? (Core.keyOf c.t (Core.cprjAddr B 0 j')) =
      some (.ctorInfo cvC nP nF) := by
    rw [← hk, ← hκC]
    exact hctorB
  refine ⟨hT.ctorTele j' hj' cvC nP nF hfC', fun hprop f rc bp' rg hg hg' csg g us hf hus evg gg
    hrc hbp' hg' hzero => ?_⟩
  have htblB : (appCtx c new).env.find?
      (Ix.Kernel.projTableName ((appCtx c new).stored.κ (Core.iprjAddr B 0))) =
      some (.projInfo tbl) := by
    rw [← hbB, ← hi0]
    exact htbl
  exact hT.guard i hi0 j cvC nP nF tbl hctorB htblB hprop f rc bp' rg hg hg' csg g us b hf hus evg
    gg hrc hbp' hbB hg' hzero

end

end IxVM.Refinement.Typing
