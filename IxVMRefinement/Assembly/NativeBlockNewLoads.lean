import IxVMRefinement.Assembly.NativeBlockNewTable

/-! # The load facts that reach the new family, assembled

`BlockInstall.newLoads`: the field `NewLoads` (`NativeBlockLoads.lean`) asks at the environment
after a native block's install, from

* `BlockInstall` (the new constants as the store reads them): `getCI`, `getCprj`, `getIprj`,
  `inductRecord`, `inductBlock`, `ctorIndRes`, `unitLike`, `unitLikeRaw`
  (`NativeBlockNewFacts.lean`);
* `BlockTable` (the new projection table): `projTables`, `projTablesAt`, `projCtorTele`,
  `projFire` (`NativeBlockNewTable.lean`; the firing is the table's named clause `fire`);
* `BlockEta`: the two η fields at the new family, as named inputs. What they need beyond the
  install: the capability conjunct reads `caps.eta = true`, i.e. that the family is not a
  proposition (from the use's never-zero sort) and that IxCK's recursion flag `nativeIsRec kinds`
  is false, which only the circuit's `struct_is_rec` verdict can give; the use facts are
  `NativeNoRecFacts.etaUseFacts`.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option linter.unusedVariables false

/-- **The two η fields of `NewLoads` at the new family** (module docstring). -/
structure BlockEta (c : Ctx) (new : List (ConstantInfo .anon)) : Prop where
  eta : ∀ (ac b sa : Bytes.Address) (i : F) (j : Nat) (cvc cvT : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel)
      (bp ptr nl ty np u blk idx : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F)),
    (appCtx c new).env.find? ((appCtx c new).stored.κ (ixAddr ac)) = some (.ctorInfo cvc cnP cnF) →
    cvc.name = (appCtx c new).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) j) → 0 < cnF →
    ObsFn W "Ingress::get_ci_iprj" [bp, .field i] h1 ptr h2 cs1 → Good (appCtx c new) cs1 →
    Bytes.RepAddressRef addrTy h1 b bp →
    loadValue h2 ptr =
      .ok (.construct kciEnum "Induct" [nl, ty, np, .field 0, .field 1, u, blk, idx]) →
    (appCtx c new).env.find? ((appCtx c new).stored.κ (iprjAddr (ixAddr b) (ZMod.val i))) = some (.indInfo cvT caps) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_modeled" [bq] h3 (.field 0) h4 cs3 ∧ Good (appCtx c new) cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    piSortAt cnP (posOf cvT.levelParams cvT.type) = some l →
    (¬ ∀ φ, Ix.Kernel.Level.eval φ (Ix.Kernel.Level.subst (List.range us.length) us l) = 0) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good (appCtx c new) cs5 ∧
        Bytes.RepAddressRef addrTy h5 sa sp) →
    ixAddr sa = iprjAddr (ixAddr b) (ZMod.val i) →
    (ConstantInfo.ctorInfo cvc cnP cnF ∈ new ∨ ConstantInfo.indInfo cvT caps ∈ new) →
    (caps.eta = true ∧ caps.etaCtor = some ((appCtx c new).stored.κ (ixAddr ac)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts (appCtx c new).env ((appCtx c new).stored.κ (iprjAddr (ixAddr b) (ZMod.val i)))
      ((appCtx c new).stored.κ (ixAddr ac)) cvT caps cnP cnF
  etaIota : ∀ (pp ptr nl ty u blk : SourceValue F) (h1 h2 : Heap F) (cs1 : List (Call F))
      (pa b : Bytes.Address) (i m : F) (cvT cvc : Ix.Kernel.ConstantVal .anon)
      (caps : Ix.Kernel.IndCaps .anon) (cnP cnF : Nat) (us : List KLevel) (l : KLevel),
    ObsFn W "Ingress::get_ci" [pp] h1 ptr h2 cs1 → Good (appCtx c new) cs1 →
    Bytes.RepAddressRef addrTy h1 pa pp →
    loadValue h2 ptr = .ok (.construct kciEnum "Induct"
      [nl, ty, .field m, .field 0, .field 1, u, blk, .field i]) →
    Bytes.RepAddressRef addrTy h2 b blk →
    (appCtx c new).env.find? ((appCtx c new).stored.κ (ixAddr pa)) = some (.indInfo cvT caps) →
    (appCtx c new).env.find? ((appCtx c new).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) = some (.ctorInfo cvc cnP cnF) →
    (∃ (bq : SourceValue F) (h3 h4 : Heap F) (cs3 : List (Call F)),
      ObsFn W "KernelModeled::block_is_multi" [bq] h3 (.field 0) h4 cs3 ∧ Good (appCtx c new) cs3 ∧
        Bytes.RepAddressRef addrTy h3 b bq) →
    (∃ (sp v : SourceValue F) (h5 h6 : Heap F) (cs5 : List (Call F)),
      ObsFn W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5 ∧ v ≠ .field 1 ∧ Good (appCtx c new) cs5 ∧
        Bytes.RepAddressRef addrTy h5 pa sp) →
    piSortAt (ZMod.val m) (posOf cvT.levelParams cvT.type) = some l →
    (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true →
    (ConstantInfo.indInfo cvT caps ∈ new ∨ ConstantInfo.ctorInfo cvc cnP cnF ∈ new) →
    (caps.eta = true ∧
      caps.etaCtor = some ((appCtx c new).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) ∧ caps.etaFields = cnF ∧
      caps.etaParams = cnP ∧ cnP = ZMod.val m ∧ cvc.levelParams = cvT.levelParams) ∧
      EtaUseFacts (appCtx c new).env ((appCtx c new).stored.κ (ixAddr pa))
      ((appCtx c new).stored.κ (cprjAddr (ixAddr b) (ZMod.val i) 0)) cvT caps cnP cnF

/-- **The load facts that reach the new family** (module docstring). -/
theorem BlockInstall.newLoads {c : Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}
    (hI : BlockInstall c new B cb ind caps) (hT : BlockTable c new B ind)
    (hE : BlockEta c new) : NewLoads (appCtx c new).stored new :=
  { getCI := hI.newGetCI
    getCprj := hI.newGetCprj
    getIprj := hI.newGetIprj
    inductRecord := hI.newInductRecord
    projTables := hI.newProjTables hT
    projTablesAt := hI.newProjTablesAt hT
    unitLike := hI.newUnitLike
    unitLikeRaw := hI.newUnitLikeRaw
    eta := hE.eta
    etaIota := hE.etaIota
    inductBlock := hI.newInductBlock
    projCtorTele := hI.newProjCtorTele hT
    projFire := hT.newProjFire
    ctorIndRes := hI.newCtorIndRes }

end IxVM.Refinement.Typing
