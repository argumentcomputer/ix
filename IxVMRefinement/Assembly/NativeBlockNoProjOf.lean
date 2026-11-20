import IxVMRefinement.Assembly.NativeBlockNoProj
import IxVMRefinement.Assembly.NativeBlockOutsRaw
import IxVMRefinement.Assembly.NativeBlockInstallOf
import IxVMRefinement.Assembly.NativeBlockNewFacts

/-! # No stored constructor type of a native block's family projects out of it

`blockFamCtorNoProj_of_member`: `BlockFamCtorNoProj` at the family the native install names
(`lateFamAt_of_install`, `famIxonRetHead_of_member`). The constructor stage of the member check
(`ctorOuts_of_member_raw`) gives, per slot, a constructor admission (`Decl.NativeCtorOut`) whose
stored constructor has no projection out of the family (`noProj`); that constructor's type is the
canonical annotation of the slot's reading, and so is the type the install stores at the slot's
key (`BlockInstall.ctor`), which is the install's constructor at the slot (`NativeInstallOut.ctors`,
`NativeInstallOut.ctorFind`).
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (NativeFam)

universe u

/-- **No stored constructor type of the installed family projects out of it** (module
docstring). -/
theorem blockFamCtorNoProj_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps) :
    BlockFamCtorNoProj
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ := by
  obtain ⟨ty₀', tyR, cvS, bsT, ctorsR, rawTypes, -, -, -, -, -, -, -, -, hlenP, hper, -, -, -, -,
    hout, -, -, -, -⟩ :=
    ctorOuts_of_member_raw ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP hkeys hfresh
      hfree hcov haux
  obtain ⟨sortss, -, hsorts⟩ := hout false
  have hI := hO.install
  intro j cA hcA
  have hjI : j < ind.ctors.size := by
    have h := (List.getElem?_eq_some_iff.mp hcA).1
    rw [hO.lenA] at h
    exact h
  have hjP : j < p₀.ctors.length := by
    rw [hlenP]
    exact hjI
  -- the admission at slot `j`
  obtain ⟨c, cR, sorts, hc, hcR, -, hNCO⟩ := hsorts j hjP
  obtain ⟨ct, cty', hct, hcidx, -, -, -, -, -, hread, -, -, hcanonR, hcRj⟩ := hper j c hc
  have hcReq : cR = (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) :=
    Option.some.inj (hcR.symm.trans hcRj)
  have hnp := hNCO.noProj
  rw [hcReq] at hnp
  -- the install's constructor at slot `j`
  obtain ⟨ctI, ctyI, ctyI', hctI, -, hreadI, -, -, hcanonI, hfindI⟩ := hI.ctor j hjI
  have e1 : ctI = ct := Option.some.inj (hctI.symm.trans hct)
  subst e1
  have e2 : ctyI = c.1.type := Except.ok.inj (hreadI.symm.trans hread)
  subst e2
  rw [ZMod.val_zero] at hcanonR
  have e3 : ctyI' = cty' := Option.some.inj (hcanonI.symm.trans hcanonR)
  subst e3
  obtain ⟨ct₀, cty₀, -, -, -, hA⟩ := hO.ctors j hjI
  rw [hA] at hcA
  injection hcA with hcA
  subst hcA
  have hfindA := hO.ctorFind _ (List.mem_of_getElem? hA)
  have hEq := Option.some.inj (hfindA.symm.trans hfindI)
  injection hEq with hcv hnP' hnF'
  have h3 : cty₀ = ctyI' := congrArg ConstantVal.type hcv
  show Decl.noProjAt p.cvT.name cty₀ = true
  rw [hO.cvT, h3]
  exact hnp

end IxVM.Refinement.Typing
