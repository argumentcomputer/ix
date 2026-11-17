import IxVMRefinement.Assembly.NativeBlockFinalRetHead
import IxVMRefinement.Assembly.NativeBlockGuardZero
import IxVMRefinement.Assembly.NativeBlockGuardWalk

/-! # The native block step with the projection guard produced where the fields are in the class

* `blockGuard_of_step_z`: `BlockGuard` at a one-constructor, index-free install from the step's
  data and the zero-ness class of the constructor's field domains: the circuit's guard spec
  (`projGuardWalkAt_of_step`, at the constructor stage) and `blockGuard_of_install_z`;
* `unitStep_nativeBlock_struct_z`: `unitStep_nativeBlock_struct_rh` with its guard input `hguard`
  replaced by: at a `Prop` structure, the constructor's field domains are in the zero-ness class
  (`CtorFieldsSortZ`, which contains the class `C`, `CtorFieldsSortSyn.sortZ`), or the guard holds
  (the named residue).
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

universe u

/-- **`BlockGuard` from the step's data where the field domains are in the zero-ness class.** -/
theorem blockGuard_of_step_z {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hsize : ind.ctors.size = 1) (hidx : ind.indices.toNat = 0)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hkeys : HashKeyed t env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hsyn : ∀ cA ∈ ctorsA, CtorFieldsSortZ env cA.1.type p.nP cA.2) :
    BlockGuard ⟨E, env, t, some n⟩ new B :=
  blockGuard_of_install_z hO hsize hidx hfreshT (ctorStageEnv_find hfreshT)
    (projGuardWalkAt_of_step hO hsize hinv hkeys hstored hfreshT) hsyn

/-- **`UnitStep` for a one-type native inductive block without its recursor, carrying the
registered families' constructors' literal return, with the projection guard produced where the
fields are in the zero-ness class**: `unitStep_nativeBlock_struct_rh` with `hguard` replaced by
`hguardZ`: at a one-constructor, index-free family whose sort tests zero, the constructor's field
domains are in the class or the guard holds. -/
theorem unitStep_nativeBlock_struct_z {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n) (hlim : lim = some n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hkey : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : L1.CanonicalHashCoverage E calls)
    (hguardZ : ind.ctors.size = 1 → ind.indices.toNat = 0 →
      ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
        (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
        (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
        NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
        Ix.Kernel.Level.isEquiv p.resSort .zero = some true →
        (∀ cA ∈ ctorsA, CtorFieldsSortZ env cA.1.type p.nP cA.2) ∨
          BlockGuard ⟨E, env, t, some n⟩ new B) :
    UnitStep.{u} (NativeBlockXR.{u} t E) t envT E₀ E lim B cb := by
  subst hlim
  have hP : HashedBlockProjectionsHeld E := hashedBlockProjectionsHeld_of_decoded hst.decoded
  intro env hext hnd hinv hXe href hfresh
  obtain ⟨⟨⟨hreg, hkeys⟩, haux⟩, hlv⟩ := hXe
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  obtain ⟨ty₀, cs, -, -, -, hall⟩ := blockReads_of_member ht hbound hS hrec hchk
  obtain ⟨hblk, hpin, hna⟩ := hall {}
  obtain ⟨p₀, hp₀, -⟩ := nativeParts_of_member ht hbound hS hrec hchk htele hblk hkey
  obtain ⟨new, p, ty', ctorsA, caps, hO⟩ := nativeInstallOut_of_member ht hS hst hrec hchk hnat
    htele hblk hp₀ hinv hstored hP hkeys hfresh hkey hcov haux hnd
  have hI := hO.install
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hcvT : p₀.cvT = ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat,
      p₀.cvT.type⟩ := by
    rw [← hO.cvT₀.1, ← hO.cvT₀.2]
  have hctorsA : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
      cA.1.name = Core.keyOf t (Core.cprjAddr B 0 j) ∧
        cA.1.levelParams = List.range ind.lvls.toNat := by
    intro j cA hcA
    have hj : j < ind.ctors.size := by
      have := (List.getElem?_eq_some_iff.mp hcA).1
      rw [hO.lenA] at this
      exact this
    obtain ⟨ct, cty', -, hcl, -, hA⟩ := hO.ctors j hj
    rw [hA] at hcA
    injection hcA with hcA
    subst hcA
    exact ⟨rfl, by rw [hcl]⟩
  have hG : BlockGuard ⟨E, env, t, some n⟩ new B := by
    by_cases hs : ind.ctors.size = 1 ∧ ind.indices.toNat = 0 ∧
        Ix.Kernel.Level.isEquiv p.resSort .zero = some true
    · rcases hguardZ hs.1 hs.2.1 env new _ p₀ p ty' ctorsA caps hO hs.2.2 with hz | hg
      · exact blockGuard_of_step_z hO hs.1 hs.2.1 hinv hkeys hstored hfreshT hz
      · exact hg
    · exact blockGuard_of_install_off hO haux hfreshT hs
  have hT : BlockTable ⟨E, env, t, some n⟩ new B ind :=
    blockTable_of_install hI hinv hpin hna hO.facts hcvT hO.nP₀ hO.nIdx₀ hO.lenA hctorsA hfreshT
      hG
  have hE : BlockEta ⟨E, env, t, some n⟩ new :=
    blockEta_of_install hrec hinv hkeys hstored hpin hna hO
  -- the names of the new constants
  have hnres : ∀ cn ∈ new, cn.name ≠ Core.unresolvedKey := by
    intro cn hcn
    rcases hI.newName cn hcn with h | ⟨j, -, h⟩ | ⟨tbl, rfl⟩
    · rw [h]; exact keyOf_ne_unresolvedKey t _
    · rw [h]; exact keyOf_ne_unresolvedKey t _
    · show Ix.Kernel.projTableName tbl.structName ≠ Core.unresolvedKey
      rw [hO.tableName tbl hcn]
      exact projTableName_keyOf_ne_unresolvedKey t _
  have hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon),
      (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci → env.find? k = none →
      k ≠ Core.unresolvedKey := by
    intro k ci hf hnone
    rcases find?_append_cases new hf with hm | hold
    · rw [← Core.WhnfAux.name_of_find hf]
      exact hnres ci hm
    · rw [hnone] at hold
      cases hold
  -- the load contract and the invariant after the install
  have hloads := storedLoads_append (c := ⟨E, env, t, some n⟩) hinv.loads hO.facts.envExt hnres
    hinv.etaStable (hI.newLoads hT hE)
  have hinv₂ : Decl.PrefixInv.{u} E t (some n) ⟨new ++ env.consts⟩ :=
    PrefixInv.nativeNoRec_eta hinv hO.facts hpin hna hres hloads
  -- the carried clause after the install: the family registered with its constructors' return
  have hrh := famIxonRetHead_of_member ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP
    hkeys hfresh hkey hcov haux hO
  have hreg₂ : RetHeadRegistry.{u} t E ⟨new ++ env.consts⟩ :=
    hreg.nativeNoRec hO.facts (lateFamAt_of_install hrec hO) hrh
  have hkeys₂ : HashKeyed t ⟨new ++ env.consts⟩ := by
    refine HashKeyed.append htwf hkeys fun ci hci => ?_
    rcases hI.newName ci hci with h | ⟨j, hj, h⟩ | ⟨tbl, rfl⟩
    · exact Or.inl ⟨Core.iprjAddr B 0, h, address_size_of_record hS hrec.former⟩
    · exact Or.inl ⟨Core.cprjAddr B 0 j, h, address_size_of_record hS (hrec.ctors j hj)⟩
    · exact Or.inr fun y h =>
        Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t y) h.symm
  have haux₂ : Decl.AuxRootSynced ⟨new ++ env.consts⟩ :=
    NativeNoRecFacts.auxRootSynced hpin hna hO.facts haux
  have hlv₂ : LvClauses ⟨new ++ env.consts⟩ := NativeNoRecFacts.lvClauses hpin hO.facts hlv
  exact ⟨new, hO.nodup, hO.fresh, hinv₂, ⟨⟨⟨hreg₂, hkeys₂⟩, haux₂⟩, hlv₂⟩, hO.reads, hO.named⟩

end IxVM.Refinement.Typing
