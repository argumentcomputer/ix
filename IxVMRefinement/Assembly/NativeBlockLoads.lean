import IxVMRefinement.Assembly.NativeBlockEta

/-! # The load contract after constants are put in front of a prefix

The install of a native block puts the former, the constructors and possibly a projection table
in front of the prefix. The load contract of the prefix context at the longer environment splits
by whether a load reaches one of the new constants:

* a load at an address the prefix resolved, or a fact about constants the prefix stores, is the
  prefix's (the keying agrees on the addresses the prefix resolved, `appCtx_keep`; a constant
  stored at a key that is not new is the prefix's, `appCtx_old`);
* a load that reaches a new constant is the family's own fact: `NewLoads`, each field of the
  contract at the longer environment with the premise that a new constant is involved (at the
  load's key, as the family `FamNew`, or as the inductive, constructor or table the field reads).

`storedLoads_append`: the contract at the longer environment from the prefix's, η stability of
the prefix (for the η use facts of an old family in the extension), the extension, the new names
being resolved keys, and `NewLoads`. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (ConstantVal ConstantInfo IndCaps)

set_option linter.unusedVariables false

/-- The context after the constants `new` are put in front of the prefix. -/
abbrev appCtx (c : Ctx) (new : List (ConstantInfo .anon)) : Ctx :=
  ⟨c.E, ⟨new ++ c.env.consts⟩, c.t, c.lim⟩

/-- **The family at `(b, i)` is witnessed by a new constant**: the inductive at the member's key,
or a constructor at one of its constructors' keys, is one of `new`. -/
def FamNew (c : ScopedCtx) (new : List (ConstantInfo .anon)) (b : _root_.Address) (i : Nat) :
    Prop :=
  (∃ cv caps, c.env.find? (c.κ (iprjAddr b i)) = some (.indInfo cv caps) ∧
      ConstantInfo.indInfo cv caps ∈ new) ∨
    ∃ j cv nP nF, c.env.find? (c.κ (cprjAddr b i j)) = some (.ctorInfo cv nP nF) ∧
      ConstantInfo.ctorInfo cv nP nF ∈ new

/-- **The load facts that reach a new constant**: each field of `ScopedLoadFacts c` whose load or
stored constant is one of `new` (the premise added to each field), with the call-coverage
premises dropped (a prefix context allows every call). -/
structure NewLoads (c : ScopedCtx) (new : List (ConstantInfo .anon)) : Prop where
  getCI : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr → (∃ cn ∈ new, cn.name = keyOf c.t (ixAddr a)) →
      ∃ ci, c.env.find? (c.κ (ixAddr a)) = some ci ∧ CIPtrRep c.κ h' ptr ci
  getCprj : ∀ (bp ptr : SourceValue F) (i j : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field j] h ptr h' cs →
      FamNew c new (ixAddr b) (ZMod.val i) → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp →
      (∃ ci₀, CIPtrRep c.κ h' ptr ci₀) ∧
      ∀ cv nP nF, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) (ZMod.val j))) =
          some (.ctorInfo cv nP nF) → CIPtrRep c.κ h' ptr (.ctorInfo cv nP nF)
  getIprj : ∀ (bp ptr : SourceValue F) (i : F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address),
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs →
      FamNew c new (ixAddr b) (ZMod.val i) → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp →
      ∃ ci, c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some ci ∧ CIPtrRep c.κ h' ptr ci
  inductRecord : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty np ni nc u blk idx : SourceValue F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
      (∃ cn ∈ new, cn.name = keyOf c.t (ixAddr a)) → Good c.toCtx cs →
      Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, idx]) →
    ∃ (cm : Ixon.Constant) (b : Bytes.Address) (i : F),
      Ix.Cert.recordAt c.E (ixAddr a) = some cm ∧ Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cm.info = .iPrj ⟨(ZMod.val i).toUInt64, ixAddr b⟩
  projTables : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp → ip = .field i →
    FamNew c new (ixAddr b) (ZMod.val i) →
    ProjPermitted c.κ (iprjAddr (ixAddr b) (ZMod.val i)) →
    (∃ ci, c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some ci ∧
      CIPtrRep c.κ h' ptr ci) ∧
    ∀ (sap sptr nl ty np u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (s : Bytes.Address),
    ObsFn W "Ingress::get_ci" [sap] h1 sptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 s sap →
    loadValue h2 sptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      (cvC.type.stripPis 1).isSome = true →
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) ∧
        tbl.structName = c.κ (iprjAddr (ixAddr b) (ZMod.val i)) ∧
        tbl.ctor = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) ∧ tbl.numParams = nP ∧
        tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
        (∀ cb xs ind, Ix.Cert.recordAt c.E (ixAddr b) = some cb → cb.info = .muts xs →
          xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
        (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort
  projTablesAt : ∀ (bp sap ptr nl ty np u blk : SourceValue F) (h h' h1 h2 : Heap F)
      (cs cs1 : List (Call F)) (b s : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp →
    ObsFn W "Ingress::get_ci" [sap] h1 ptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 s sap →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      ConstantInfo.ctorInfo cvC nP nF ∈ new → 0 < nF →
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
          some (.projInfo tbl) ∧
        tbl.structName = c.κ (iprjAddr (ixAddr b) (ZMod.val i)) ∧
        tbl.ctor = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) ∧ tbl.numParams = nP ∧
        tbl.numFields = nF ∧ tbl.levelParams = cvC.levelParams ∧
        (∀ cb xs ind, Ix.Cert.recordAt c.E (ixAddr b) = some cb → cb.info = .muts xs →
          xs[ZMod.val i]? = some (.indc ind) → nP = ind.params.toNat) ∧
        (∀ f, f < nF → c.env.findProj? tbl.structName f = some (tbl.entry f) ∧
          Ix.Kernel.TowerHead c.env (tbl.entry f)) ∧
        Ix.Kernel.structProjBodies tbl.structName nP nF cvC.type = some tbl.bodies ∧
        (∃ sorts : List Ix.Kernel.Level, sorts.length = nF ∧
          tbl.guards = Ix.Kernel.structProjGuards cvC.type nP nF sorts) ∧
        ∃ bs body, cvC.type.stripPis (nP + nF) = some (bs, body) ∧
          ∀ bm ∈ bs, bm.2.pw = Ix.Kernel.Level.zeronessOf tbl.structSort
  unitLike : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (a : Bytes.Address)
      (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cvC : Ix.Kernel.ConstantVal .anon) (nPc : Nat),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs → Good c.toCtx cs → Bytes.RepAddressRef addrTy h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    c.env.find? (c.κ (ixAddr a)) = some (.indInfo cvT caps) →
    FewInductives c.toCtx (ixAddr b) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvC nPc 0) →
    (ConstantInfo.indInfo cvT caps ∈ new ∨ ConstantInfo.ctorInfo cvC nPc 0 ∈ new) →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (c.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const (c.κ (ixAddr a)) us) = true))
  unitLikeRaw : ∀ (ap ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address) (nl ty u blk : SourceValue F) (p i : F) (b : Bytes.Address)
      (cvT : Ix.Kernel.ConstantVal .anon) (caps : Ix.Kernel.IndCaps .anon),
    ObsFn W "Ingress::get_ci" [ap] h ptr h' cs →
    Good c.toCtx cs → Bytes.RepAddressRef addrTy h a ap →
    loadValue h' ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field p, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    c.env.find? (c.κ (ixAddr a)) = some (.indInfo cvT caps) →
    ConstantInfo.indInfo cvT caps ∈ new → FewInductives c.toCtx (ixAddr b) →
    ZeroFieldCtorLoad c b i → NonrecursiveLoad c a →
    caps.unitlike = true ∧ caps.unitParams = ZMod.val p ∧
      (Ix.Kernel.reservedBasisNames.contains (c.κ (ixAddr a)) = false ∨
        (ZMod.val p = 0 ∧ ∀ us, Ix.Kernel.isUnitLikeTy c.env (.const (c.κ (ixAddr a)) us) = true))
  eta : ∀ (ac b sa : Bytes.Address) (i : F) (j : Nat) (cvc cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel)
      (bp ptr nl ty np u blk idx : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F)),
    c.env.find? (c.κ (ixAddr ac)) = some (.ctorInfo cvc cnP cnF) →
    cvc.name = c.κ (cprjAddr (ixAddr b) (ZMod.val i) j) → 0 < cnF →
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h1 ptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 b bp →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, idx]) →
    c.env.find? (c.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_modeled" [bq] h3 (.field 0) h4 cs3 ∧ Good c.toCtx cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    piSortAt cnP (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c.toCtx cs5 ∧
        Bytes.RepAddressRef addrTy h5 sa sp) →
    ixAddr sa = iprjAddr (ixAddr b) (ZMod.val i) →
    (ConstantInfo.ctorInfo cvc cnP cnF ∈ new ∨ ConstantInfo.indInfo cvT caps ∈ new) →
    (caps.eta = true ∧ caps.etaCtor = some (c.κ (ixAddr ac)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts c.env (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))
      (c.κ (ixAddr ac)) cvT caps cnP cnF
  etaIota : ∀ (pp ptr nl ty u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (pa b : Bytes.Address) (i m : F) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel),
    ObsFn W "Ingress::get_ci" [pp] h1 ptr h2 cs1 → Good c.toCtx cs1 →
    Bytes.RepAddressRef addrTy h1 pa pp →
    loadValue h2 ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field m, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    c.env.find? (c.κ (ixAddr pa)) = some (.indInfo cvT caps) →
    c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvc cnP cnF) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧ Good c.toCtx cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good c.toCtx cs5 ∧
        Bytes.RepAddressRef addrTy h5 pa sp) →
    piSortAt (ZMod.val m) (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (ConstantInfo.indInfo cvT caps ∈ new ∨ ConstantInfo.ctorInfo cvc cnP cnF ∈ new) →
    (caps.eta = true ∧
      caps.etaCtor = some (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cnP = ZMod.val m ∧ cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts c.env (c.κ (ixAddr pa))
      (c.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) cvT caps cnP cnF
  inductBlock : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a b : Bytes.Address) (nl ty np ni nc u blk : SourceValue F) (i : F),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
      (∃ cn ∈ new, cn.name = keyOf c.t (ixAddr a)) → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h a addr →
    loadValue h' ptr = .ok (.construct kciEnum "Induct" [nl, ty, np, ni, nc, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h' b blk →
    ∃ (cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt c.E (ixAddr b) = some cb ∧ cb.info = .muts xs ∧
      xs[ZMod.val i]? = some (.indc ind)
  projTablesGuard : ∀ (bp ip ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (b : Bytes.Address) (i : F),
    ObsFn W "KernelModeled::proj_ctor" [bp, ip] h ptr h' cs → Good c.toCtx cs →
    Bytes.RepAddressRef addrTy h b bp → ip = .field i →
    ∀ (j : Nat) (cvC : Ix.Kernel.ConstantVal .anon) (nP nF : Nat)
      (tbl : Ix.Kernel.ProjTable .anon),
      c.env.find? (c.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvC nP nF) →
      c.env.find? (Ix.Kernel.projTableName (c.κ (iprjAddr (ixAddr b) (ZMod.val i)))) =
        some (.projInfo tbl) →
      (ConstantInfo.ctorInfo cvC nP nF ∈ new ∨ ConstantInfo.projInfo tbl ∈ new) →
      Ix.Kernel.Expr.ctorTeleOk cvC.type (nP + nF) = true ∧
      (Ix.Kernel.Level.isEquiv tbl.structSort .zero = some true →
        ∀ (f : F) (rc bp' rg : SourceValue F) (hg hg' : Heap F) (csg : List (Call F))
          (g : KLevel) (us : List KLevel),
          ZMod.val f < nF → us.length = tbl.levelParams.length →
          ObsFn W "KernelInfer::proj_guard" [rc, bp', .field i, .field f] hg rg hg' csg →
          Good c.toCtx csg → RCRep c.t c.lim hg rc → Bytes.RepAddressRef addrTy hg b bp' →
          IxVM.Refinement.KernelLevels.RepKLevel hg' g rg →
          (∀ φ, Ix.Kernel.Level.eval φ
            (Ix.Kernel.Level.subst (List.range us.length) us g) = 0) →
          ∀ φ, Ix.Kernel.Level.eval φ
            (Ix.Kernel.Level.subst tbl.levelParams us (tbl.entry (ZMod.val f)).fieldSort) = 0)
  ctorIndRes : ∀ (b : _root_.Address) (i j : Nat) (cv : Ix.Kernel.ConstantVal .anon)
      (nP nF : Nat), HashedBlockAt c.E b →
    c.env.find? (c.κ (cprjAddr b i j)) = some (.ctorInfo cv nP nF) →
    ConstantInfo.ctorInfo cv nP nF ∈ new → c.κ (iprjAddr b i) ≠ unresolvedKey

section
variable {c : Ctx} {new : List (ConstantInfo .anon)}

/-- A key the prefix resolves is kept by the longer environment. -/
theorem appCtx_keep (hext : Ix.Kernel.EnvExt c.env (appCtx c new).env) (x : _root_.Address)
    (h : c.stored.κ x ≠ unresolvedKey) : (appCtx c new).stored.κ x = c.stored.κ x :=
  Decl.stagedOver_keep (c₁ := c) (c₂ := appCtx c new) (pre₁ := c.env)
    (pre₂ := (appCtx c new).env) rfl (fun hf => ⟨_, hext.find hf⟩)
    (fun hf => ⟨_, hext.find hf⟩) x h

/-- An address the longer environment resolves, one a record can have, has the key of a new
constant or one the prefix resolves. -/
theorem appCtx_split (x : _root_.Address) (hm : ¬ IsProjMarker x)
    (h : (appCtx c new).stored.κ x ≠ unresolvedKey) :
    (∃ cn ∈ new, cn.name = keyOf c.t x) ∨ c.stored.κ x ≠ unresolvedKey := by
  obtain ⟨ci, hci⟩ := Ctx.stored_key_ne h hm
  rcases find?_append_cases (env := c.env) new hci with hm' | ho
  · exact Or.inl ⟨ci, hm', WhnfAux.name_of_find hci⟩
  · refine Or.inr ?_
    rw [Ctx.stored_key_of_find ho]
    exact Resolved.ne

/-- **What the longer environment stores at a context key, other than a new constant, the prefix
stores at the same key.** -/
theorem appCtx_old (h₁ : ScopedLoadFacts c.stored)
    (hext : Ix.Kernel.EnvExt c.env (appCtx c new).env) {x : _root_.Address}
    {y : ConstantInfo .anon}
    (hf : (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some y) (hne : y ∉ new) :
    c.env.find? (c.stored.κ x) = some y ∧ (appCtx c new).stored.κ x = c.stored.κ x := by
  have hfo : c.env.find? ((appCtx c new).stored.κ x) = some y := by
    rcases find?_append_cases (env := c.env) new hf with hm | ho
    · exact absurd hm hne
    · exact ho
  by_cases hr₂ : (appCtx c new).stored.κ x = unresolvedKey
  · exfalso
    have hr₁ : c.stored.κ x = unresolvedKey := by
      by_contra hr
      exact hr ((appCtx_keep hext x hr).symm.trans hr₂)
    rw [hr₂, ← hr₁] at hfo
    exact h₁.findRes x y hfo hr₁
  · have e₂ : (appCtx c new).stored.κ x = keyOf c.t x := (appCtx c new).stored.key_eq hr₂
    rw [e₂] at hfo
    have e₁ : c.stored.κ x = keyOf c.t x := Ctx.stored_key_of_find hfo
    exact ⟨by rw [e₁]; exact hfo, e₂.trans e₁.symm⟩

/-- **A family at the longer environment is the prefix's or is witnessed by a new constant.** -/
theorem appCtx_fam (h₁ : ScopedLoadFacts c.stored)
    (hext : Ix.Kernel.EnvExt c.env (appCtx c new).env) {b : _root_.Address} {i : Nat}
    (hfam : (appCtx c new).stored.FamAt b i) :
    c.stored.FamAt b i ∨ FamNew (appCtx c new).stored new b i := by
  rcases hfam with ⟨cv, caps, hf⟩ | ⟨j, cv, nP, nF, hf⟩
  · by_cases hm : ConstantInfo.indInfo cv caps ∈ new
    · exact Or.inr (Or.inl ⟨cv, caps, hf, hm⟩)
    · exact Or.inl (Or.inl ⟨cv, caps, (appCtx_old h₁ hext hf hm).1⟩)
  · by_cases hm : ConstantInfo.ctorInfo cv nP nF ∈ new
    · exact Or.inr (Or.inr ⟨j, cv, nP, nF, hf, hm⟩)
    · exact Or.inl (Or.inr ⟨j, cv, nP, nF, (appCtx_old h₁ hext hf hm).1⟩)

end

/-- **The load contract after constants are put in front of a prefix** (module docstring). -/
theorem storedLoads_append {c : Ctx} {new : List (ConstantInfo .anon)}
    (h₁ : ScopedLoadFacts c.stored) (hext : Ix.Kernel.EnvExt c.env (appCtx c new).env)
    (hnres : ∀ cn ∈ new, cn.name ≠ unresolvedKey) (heta : Decl.EtaStable c.env)
    (hnew : NewLoads (appCtx c new).stored new) :
    ScopedLoadFacts (appCtx c new).stored := by
  have keep : ∀ x, c.stored.κ x ≠ unresolvedKey → (appCtx c new).stored.κ x = c.stored.κ x :=
    appCtx_keep hext
  have old : ∀ {x : _root_.Address} {y : ConstantInfo .anon},
      (appCtx c new).env.find? ((appCtx c new).stored.κ x) = some y → y ∉ new →
        c.env.find? (c.stored.κ x) = some y ∧ (appCtx c new).stored.κ x = c.stored.κ x :=
    fun hf hne => appCtx_old h₁ hext hf hne
  have famPerm : ∀ {b : _root_.Address} {i : Nat}, HashedBlockAt c.E b → c.stored.FamAt b i →
      ProjPermitted c.stored.κ (iprjAddr b i) := by
    intro b i hbh hfam
    have hr : c.stored.κ (iprjAddr b i) ≠ unresolvedKey := by
      rcases hfam with ⟨cv, caps, hf⟩ | ⟨j, cv, nP, nF, hf⟩
      · exact h₁.findRes _ _ hf
      · exact h₁.ctorIndRes _ _ _ _ _ _ hbh hf
    obtain ⟨ci, hci⟩ := Ctx.stored_key_ne hr (iprjAddr_not_marker _ _)
    exact Ctx.stored_projPermitted_of_find hci
  have good₁ : ∀ {cs : List (Call F)}, CoreGood (appCtx c new).stored cs → CoreGood c.stored cs :=
    fun g => ⟨g.noCollision, g.bounded, fun _ _ => trivial⟩
  have findRes₂ : ∀ (a : _root_.Address) (ci : ConstantInfo .anon),
      (appCtx c new).env.find? ((appCtx c new).stored.κ a) = some ci →
        (appCtx c new).stored.κ a ≠ unresolvedKey := by
    intro a ci hf
    by_cases e : ci ∈ new
    · rw [← WhnfAux.name_of_find hf]
      exact hnres ci e
    · rw [(old hf e).2]
      exact h₁.findRes a ci (old hf e).1
  exact
    { getCI := by
        intro addr ptr h h' cs a ev _ res good ha
        rcases appCtx_split (c := c) (new := new) (ixAddr a) (ixAddr_not_marker a) res with
          hn | hold
        · exact hnew.getCI addr ptr h h' cs a ev good.raw ha hn
        · obtain ⟨ci, hf, hrep⟩ := h₁.getCI addr ptr h h' cs a ev trivial hold (good₁ good) ha
          refine ⟨ci, ?_, hrep.rekey_mono keep (Decl.stored_name_ne h₁ hf)⟩
          rw [keep _ hold]
          exact hext.find hf
      getCprj := by
        intro bp ptr i j h h' cs b ev _ hfam good hb
        rcases appCtx_fam h₁ hext hfam with hold | hn
        · obtain ⟨⟨ci₀, hrep₀⟩, hall⟩ :=
            h₁.getCprj bp ptr i j h h' cs b ev trivial hold (good₁ good) hb
          refine ⟨hrep₀.rekey_exists keep, fun cv nP nF hf => ?_⟩
          by_cases hm : ConstantInfo.ctorInfo cv nP nF ∈ new
          · exact (hnew.getCprj bp ptr i j h h' cs b ev
              (Or.inr ⟨_, cv, nP, nF, hf, hm⟩) good.raw hb).2 cv nP nF hf
          · obtain ⟨hf₁, -⟩ := old hf hm
            exact (hall cv nP nF hf₁).rekey_mono keep (Decl.stored_name_ne h₁ hf₁)
        · exact hnew.getCprj bp ptr i j h h' cs b ev hn good.raw hb
      getIprj := by
        intro bp ptr i h h' cs b ev _ hfam good hb
        rcases appCtx_fam h₁ hext hfam with hold | hn
        · obtain ⟨ci, hf, hrep⟩ :=
            h₁.getIprj bp ptr i h h' cs b ev trivial hold (good₁ good) hb
          refine ⟨ci, ?_, hrep.rekey_mono keep (Decl.stored_name_ne h₁ hf)⟩
          rw [keep _ (h₁.findRes _ _ hf)]
          exact hext.find hf
        · exact hnew.getIprj bp ptr i h h' cs b ev hn good.raw hb
      indRecord := h₁.indRecord
      inductRecord := by
        intro addr ptr h h' cs a nl ty np ni nc u blk idx ev _ res good ha hld
        rcases appCtx_split (c := c) (new := new) (ixAddr a) (ixAddr_not_marker a) res with
          hn | hold
        · exact hnew.inductRecord addr ptr h h' cs a nl ty np ni nc u blk idx ev hn good ha hld
        · exact h₁.inductRecord addr ptr h h' cs a nl ty np ni nc u blk idx ev trivial hold good
            ha hld
      projTables := by
        intro bp ip ptr h h' cs b i ev _ good hb hip hfam hperm
        rcases appCtx_fam h₁ hext hfam with hold | hn
        · obtain ⟨⟨ci, hf, hrep⟩, htab⟩ :=
            h₁.projTables bp ip ptr h h' cs b i ev trivial good hb hip hold
              (famPerm (L1.hashedBlockAt_of_proj_ctor good ev hb hip) hold)
          refine ⟨⟨ci, ?_, hrep.rekey_mono keep (Decl.stored_name_ne h₁ hf)⟩, ?_⟩
          · rw [keep _ (h₁.findRes _ _ hf)]
            exact hext.find hf
          · intro sap sptr nl ty np u blk h1 h2 cs1 s evS gS hsS hldS hbS j cvC nP nF hctor' hbind
            by_cases hm : ConstantInfo.ctorInfo cvC nP nF ∈ new
            · exact (hnew.projTables bp ip ptr h h' cs b i ev good hb hip
                (Or.inr ⟨j, cvC, nP, nF, hctor', hm⟩) hperm).2 sap sptr nl ty np u blk h1 h2 cs1 s
                evS gS hsS hldS hbS j cvC nP nF hctor' hbind
            · obtain ⟨hc₁, ek⟩ := old hctor' hm
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
              · intro f hf'
                obtain ⟨hp, hth⟩ := ht8 f hf'
                exact ⟨hext.findProj? hp, hth.mono (fun _ _ _ hfind => hext.find hfind)⟩
        · exact hnew.projTables bp ip ptr h h' cs b i ev good hb hip hn hperm
      projTablesAt := by
        intro bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb evG hgG hs hld hblk
          j cvC nP nF hctor' hnF
        by_cases hm : ConstantInfo.ctorInfo cvC nP nF ∈ new
        · exact hnew.projTablesAt bp sap ptr nl ty np u blk h h' h1 h2 cs cs1 b s i evM hgM hb
            evG hgG hs hld hblk j cvC nP nF hctor' hm hnF
        · obtain ⟨hc₁, ek⟩ := old hctor' hm
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
          · intro f hf'
            obtain ⟨hp, hth⟩ := ht8 f hf'
            exact ⟨hext.findProj? hp, hth.mono (fun _ _ _ hfind => hext.find hfind)⟩
      unitLike := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc ev good ha hld hb hfT hfew hfC
        by_cases hm : ConstantInfo.indInfo cvT caps ∈ new ∨ ConstantInfo.ctorInfo cvC nPc 0 ∈ new
        · exact hnew.unitLike ap ptr h h' cs a nl ty u blk p i b cvT caps cvC nPc ev good ha hld
            hb hfT hfew hfC hm
        · obtain ⟨hT₁, eT⟩ := old hfT (fun e => hm (Or.inl e))
          obtain ⟨hC₁, -⟩ := old hfC (fun e => hm (Or.inr e))
          obtain ⟨hu1, hu2, hu3⟩ := h₁.unitLike ap ptr h h' cs a nl ty u blk p i b cvT caps cvC
            nPc ev good ha hld hb hT₁ hfew hC₁
          refine ⟨hu1, hu2, ?_⟩
          rw [eT]
          exact hu3.imp id (fun hr => ⟨hr.1, fun us => hext.isUnitLikeTy_mono (hr.2 us)⟩)
      unitLikeRaw := by
        intro ap ptr h h' cs a nl ty u blk p i b cvT caps ev _ _ good ha hld hb hfT hfew hz hn
        by_cases hm : ConstantInfo.indInfo cvT caps ∈ new
        · exact hnew.unitLikeRaw ap ptr h h' cs a nl ty u blk p i b cvT caps ev good ha hld hb
            hfT hm hfew hz hn
        · obtain ⟨hT₁, eT⟩ := old hfT hm
          obtain ⟨hu1, hu2, hu3⟩ := h₁.unitLikeRaw ap ptr h h' cs a nl ty u blk p i b cvT caps ev
            trivial (h₁.findRes _ _ hT₁) good ha hld hb hT₁ hfew
            ⟨hz.bp, hz.ptr, hz.before, hz.after, hz.calls, hz.observed, trivial, hz.good,
              hz.blockRep, hz.zeroFields⟩
            ⟨hn.ap, hn.before, hn.after, hn.calls, hn.observed, trivial, hn.good, hn.parentRep⟩
          refine ⟨hu1, hu2, ?_⟩
          rw [eT]
          exact hu3.imp id (fun hr => ⟨hr.1, fun us => hext.isUnitLikeTy_mono (hr.2 us)⟩)
      eta := by
        intro ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1
          hfC hnm hpos ev good hb hld hfT hmod hsort hnz hrec hsa
        by_cases hm : ConstantInfo.ctorInfo cvc cnP cnF ∈ new ∨ ConstantInfo.indInfo cvT caps ∈ new
        · exact hnew.eta ac b sa i j cvc cvT caps cnP cnF us l bp ptr nl ty np u blk idx h1 h2 cs1
            hfC hnm hpos ev good hb hld hfT hmod hsort hnz hrec hsa hm
        · obtain ⟨hC₁, eC⟩ := old hfC (fun e => hm (Or.inl e))
          obtain ⟨hT₁, eT⟩ := old hfT (fun e => hm (Or.inr e))
          have hnC : cvc.name = (appCtx c new).stored.κ (ixAddr ac) := WhnfAux.name_of_find hfC
          have hfC' : (appCtx c new).env.find?
              ((appCtx c new).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) j)) =
                some (.ctorInfo cvc cnP cnF) := by
            rw [← hnm, hnC]
            exact hfC
          obtain ⟨-, eN⟩ := old hfC' (fun e => hm (Or.inl e))
          obtain ⟨⟨he1, he2, he3, he4, he5⟩, huse⟩ := h₁.eta ac b sa i j cvc cvT caps cnP cnF us
            l bp ptr nl ty np u blk idx h1 h2 cs1 hC₁ (hnm.trans eN) hpos ev good hb hld hT₁ hmod
            hsort hnz hrec hsa
          refine ⟨⟨he1, by rw [eC]; exact he2, he3, he4, he5⟩, ?_⟩
          rw [eT, eC]
          exact ⟨(hext.towerSlotsAll_eq hT₁ _).trans huse.towers, huse.sort,
            heta _ _ cvT cvc caps cnP cnF hT₁ he1 he2 hC₁ _ hext⟩
      etaIota := by
        intro pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev good hpa hld hb
          hfT hfC hmul hrec hsort hnz
        by_cases hm : ConstantInfo.indInfo cvT caps ∈ new ∨ ConstantInfo.ctorInfo cvc cnP cnF ∈ new
        · exact hnew.etaIota pp ptr nl ty u blk h1 h2 cs1 pa b i m cvT cvc caps cnP cnF us l ev
            good hpa hld hb hfT hfC hmul hrec hsort hnz hm
        · obtain ⟨hT₁, eT⟩ := old hfT (fun e => hm (Or.inl e))
          obtain ⟨hC₁, eC⟩ := old hfC (fun e => hm (Or.inr e))
          obtain ⟨⟨he1, he2, he3, he4, he5, he6⟩, huse⟩ := h₁.etaIota pp ptr nl ty u blk h1 h2
            cs1 pa b i m cvT cvc caps cnP cnF us l ev good hpa hld hb hT₁ hC₁ hmul hrec hsort hnz
          refine ⟨⟨he1, by rw [eC]; exact he2, he3, he4, he5, he6⟩, ?_⟩
          rw [eT, eC]
          exact ⟨(hext.towerSlotsAll_eq hT₁ _).trans huse.towers, huse.sort,
            heta _ _ cvT cvc caps cnP cnF hT₁ he1 he2 hC₁ _ hext⟩
      recordShape := h₁.recordShape
      inductBlock := by
        intro addr ptr h h' cs a b nl ty np ni nc u blk i ev _ res good ha hld hblk
        rcases appCtx_split (c := c) (new := new) (ixAddr a) (ixAddr_not_marker a) res with
          hn | hold
        · exact hnew.inductBlock addr ptr h h' cs a b nl ty np ni nc u blk i ev hn good ha hld
            hblk
        · exact h₁.inductBlock addr ptr h h' cs a b nl ty np ni nc u blk i ev trivial hold good
            ha hld hblk
      projTablesGuard := by
        intro bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hctor' htbl
        by_cases hm : ConstantInfo.ctorInfo cvC nP nF ∈ new ∨ ConstantInfo.projInfo tbl ∈ new
        · exact hnew.projTablesGuard bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hctor'
            htbl hm
        · obtain ⟨hc₁, -⟩ := old hctor' (fun e => hm (Or.inl e))
          have ei := keep _
            (h₁.ctorIndRes _ _ _ _ _ _ (L1.hashedBlockAt_of_proj_ctor good ev hb hip) hc₁)
          rw [ei] at htbl
          have htbl₁ : c.env.find? (Ix.Kernel.projTableName
              (c.stored.κ (iprjAddr (ixAddr b) (ZMod.val i)))) = some (.projInfo tbl) := by
            rcases find?_append_cases (env := c.env) new htbl with hm' | ho
            · exact absurd hm' (fun e => hm (Or.inr e))
            · exact ho
          exact h₁.projTablesGuard bp ip ptr h h' cs b i ev good hb hip j cvC nP nF tbl hc₁ htbl₁
      canonical := h₁.canonical
      storedRes := by
        intro a ci hf
        rw [Ctx.stored_key_of_find (c := appCtx c new) hf]
        exact Resolved.ne
      findRes := findRes₂
      ctorIndRes := by
        intro b i j cv nP nF hbh hf
        by_cases hm : ConstantInfo.ctorInfo cv nP nF ∈ new
        · exact hnew.ctorIndRes b i j cv nP nF hbh hf hm
        · obtain ⟨hf₁, -⟩ := old hf hm
          have hr := h₁.ctorIndRes b i j cv nP nF hbh hf₁
          rw [keep _ hr]
          exact hr
      ctorIndPerm := by
        intro a b i j cvT caps cv nP nF _ hf _ _
        have hr := findRes₂ a _ hf
        have e₂ : (appCtx c new).stored.κ a = keyOf c.t a := (appCtx c new).stored.key_eq hr
        rw [e₂] at hf
        exact Ctx.stored_projPermitted_of_find (c := appCtx c new) hf
      roleRes := by
        intro r a hf hi hb
        have hr := h₁.roleRes r a hf hi hb
        rw [keep _ hr]
        exact hr }

end IxVM.Refinement.Typing
