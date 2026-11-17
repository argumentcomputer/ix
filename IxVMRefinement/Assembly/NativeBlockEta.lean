import IxVMRefinement.Decl.EtaOpenExample
import IxVMRefinement.Assembly.NativeBlockRegister

/-! # η typing after a native block's install without its recursor

At the environment IxC's no-recursor install of any native block produces (`NativeNoRecFacts`),
from the fold invariant at the prefix and the install's own inputs only:

* `NativeNoRecFacts.etaStable`: `EtaStable` at the new environment (every stored η-capable
  family, the new one included, in every extension: a later projection table or recursor);
* `NativeNoRecFacts.etaUseFacts`: the η use facts (tower slots, sort, typing clause) at every
  stored η-capable family of the new environment;
* `PrefixInv.nativeNoRec_eta`: the prefix invariant after the install from its load contract
  alone, `EtaStable` being the theorem above;
* `NativeNoRecFacts.not_etaClauseOpen`: the typing clause without the closedness premise fails
  where the new family has a parameter and a second binder never-zero at some levels;
* `not_etaTypeOpen`: `EtaTypeOpen` is false.
-/

namespace IxVM.Refinement.Typing

open IxVM.Refinement.Core IxVM.Refinement.Decl
open Ix.Kernel (Env ConstantInfo ConstantVal IndCaps NativeParts Level BinderMeta)
open Ix.Kernel.Semantics (NativeFam)

universe u

/-- **`EtaTypeOpen` is false**: it is `Decl.EtaTypeOpenStmt`, refuted at a one-parameter
structure (`Decl.EtaOpenExample.not_etaTypeOpen`). -/
theorem not_etaTypeOpen : ¬ EtaTypeOpen := Decl.EtaOpenExample.not_etaTypeOpen

section
variable {env env₂ : Env .anon} {blk : List (ConstantInfo .anon)} {nP : Nat}
  {p₀ : NativeParts .anon} {fam : NativeFam .anon}

/-- **`EtaStable` after the install.** -/
theorem NativeNoRecFacts.etaStable (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env) : EtaStable env₂ :=
  (h.foldStoreInv hpin hna hS).etaStable

/-- **The η use facts after the install**, at any stored η-capable family. -/
theorem NativeNoRecFacts.etaUseFacts (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : FoldStoreInv env) {T kc : KKey} {cvT cvc : ConstantVal .anon} {caps : IndCaps .anon}
    {nPc nFc : Nat} (hT : env₂.find? T = some (.indInfo cvT caps)) (heta : caps.eta = true)
    (hctor : caps.etaCtor = some kc) (hkc : env₂.find? kc = some (.ctorInfo cvc nPc nFc)) :
    EtaUseFacts env₂ T kc cvT caps nPc nFc :=
  (h.foldStoreInv hpin hna hS).etaUseFacts hT heta hctor hkc

/-- **The prefix invariant after the install from its load contract**: `PrefixInv.nativeNoRec`
with its `EtaStable` premise discharged by `NativeNoRecFacts.etaStable`. -/
theorem PrefixInv.nativeNoRec_eta {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    (h : Decl.PrefixInv.{u} E t lim env) (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hpin : Ix.Kernel.basisPinHit blk = none) (hna : Decl.DeclNonAux (.indDecl blk nP))
    (hres : ∀ (k : KKey) (ci : ConstantInfo .anon), env₂.find? k = some ci →
      env.find? k = none → k ≠ unresolvedKey)
    (hloads : ScopedLoadFacts (Ctx.stored ⟨E, env₂, t, lim⟩)) :
    Decl.PrefixInv.{u} E t lim env₂ := by
  have hnaKeys : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci =>
    (hna.1 ci (by simpa [IxVM.Consistency.installs, hpin] using hci)).1
  exact PrefixInv.nativeNoRec h hfacts hpin hna hres hloads
    (hfacts.etaStable hpin hnaKeys h.store)

/-- **The typing clause without the closedness premise fails after the install of a family with
a parameter and a second binder**, whose constructor's binder data is the zero-ness of a level
never zero at some levels `us`. -/
theorem NativeNoRecFacts.not_etaClauseOpen (hpin : Ix.Kernel.basisPinHit blk = none)
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
    ¬ EtaClauseOpen env₂ T kc nPc nFc ∧ ¬ EtaStableOpen env₂ :=
  (h.foldStoreInv hpin hna hS).not_etaClauseOpen hT heta hctor hkc hstrip hz hus hnz hP hn

end

end IxVM.Refinement.Typing
