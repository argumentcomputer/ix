import IxVMRefinement.Decl.EtaOpen
import IxVMRefinement.Assembly.NativeBlockFacts

/-! # η typing after a native block's install without its recursor

At the environment IxC's no-recursor install of a block produces (`NativeNoRecFacts`), from the
fold invariant at the prefix:

* `NativeNoRecFacts.etaStableC`, `NativeNoRecFacts.etaUseFactsC`: η typing at closed parameters,
  in every extension (so after a later projection table or recursor), for every stored η-capable
  family, the new one included;
* `NativeNoRecFacts.etaStable_noParams`, `NativeNoRecFacts.etaUseFacts_noParams`: the forms the
  invariant states, where the families have no parameter;
* `NativeNoRecFacts.not_etaStable`: the forms the invariant states fail where the new family has
  a parameter and a second binder never-zero at some levels.
-/

namespace IxVM.Refinement.Typing

open IxVM.Refinement.Core IxVM.Refinement.Decl
open Ix.Kernel (Env ConstantInfo ConstantVal IndCaps NativeParts Level BinderMeta)
open Ix.Kernel.Semantics (NativeFam)

section
variable {env env₂ : Env .anon} {blk : List (ConstantInfo .anon)} {nP : Nat}
  {p₀ : NativeParts .anon} {fam : NativeFam .anon}

/-- **η typing at closed parameters after the install**, in every extension. -/
theorem NativeNoRecFacts.etaStableC (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env) : EtaStableC env₂ :=
  (h.foldStoreInv hpin hna hS).etaStableC

/-- **The η use facts at closed parameters after the install**, at any stored η-capable family. -/
theorem NativeNoRecFacts.etaUseFactsC (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env) {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon}
    {nPc nFc : Nat} (hT : env₂.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env₂.find? kc = some (.ctorInfo cvc nPc nFc)) :
    EtaUseFactsC env₂ T kc cvT caps nPc nFc :=
  (h.foldStoreInv hpin hna hS).etaUseFactsC hT heta hctor hkc

/-- **`EtaStable` as stated after the install**, where no stored η-capable family has a
parameter. -/
theorem NativeNoRecFacts.etaStable_noParams (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env)
    (h0 : ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → caps.eta = true →
      caps.etaParams = 0) : EtaStable env₂ :=
  etaStable_of_etaShape_noParams (h.foldStoreInv hpin hna hS).etaShape h0

/-- **`EtaStable` as stated after the install, from the prefix's**, where every family with a
parameter is the prefix's (the install adds one with none). -/
theorem NativeNoRecFacts.etaStable_of_prefix (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env) (hη : EtaStable env) (hext : Ix.Kernel.EnvExt env env₂)
    (hold : ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → caps.eta = true →
      caps.etaParams ≠ 0 → env.find? T = some (.indInfo cvT caps) ∧
        ∀ kc c, caps.etaCtor = some kc → env₂.find? kc = some c → env.find? kc = some c) :
    EtaStable env₂ :=
  hη.of_ext_noParams hext (h.foldStoreInv hpin hna hS).etaShape hold

/-- **`EtaUseFacts` as stated after the install**, at a family with no parameter. -/
theorem NativeNoRecFacts.etaUseFacts_noParams (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env) {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon}
    {nFc : Nat} (hT : env₂.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env₂.find? kc = some (.ctorInfo cvc 0 nFc)) :
    EtaUseFacts env₂ T kc cvT caps 0 nFc :=
  (h.foldStoreInv hpin hna hS).etaUseFacts_noParams hT heta hctor hkc

/-- **`EtaStable` and `EtaUseFacts` as stated fail after the install of a family with a parameter
and a second binder**, whose constructor's binder data is the zero-ness of a level never zero at
some levels `us`. -/
theorem NativeNoRecFacts.not_etaStable (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env) {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon}
    {nPc nFc : Nat} (hT : env₂.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env₂.find? kc = some (.ctorInfo cvc nPc nFc))
    {cbs : List (KExpr × BinderMeta)} {res : KExpr} {l : KLevel}
    (hstrip : cvc.type.stripPis (nPc + nFc) = some (cbs, res))
    (hz : ∀ b ∈ cbs, b.2.pw = Level.zeronessOf l)
    {us : List KLevel} (hus : us.length = cvc.levelParams.length)
    (hnz : (Level.subst cvc.levelParams us l).isNeverZero = true)
    (hP : 1 ≤ nPc) (hn : 2 ≤ nPc + nFc) :
    ¬ EtaStable env₂ ∧ ¬ EtaUseFacts env₂ T kc cvT caps nPc nFc :=
  (h.foldStoreInv hpin hna hS).not_etaStable hT heta hctor hkc hstrip hz hus hnz hP hn

end

end IxVM.Refinement.Typing
