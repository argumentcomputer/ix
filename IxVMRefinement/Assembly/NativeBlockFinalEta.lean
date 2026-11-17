import IxVMRefinement.Assembly.NativeBlockEtaFields

/-! # The per-record step of a native inductive block, with its η fields produced

`unitStep_nativeBlock_eta`: `unitStep_nativeBlock` without its input `heta`. The two η fields of
the load contract at the new family (`BlockEta`) are produced in the step's body by
`blockEta_of_install`, from the install read off the member check, the block's record, the
prefix invariant, the carried store-key clause, the used references the cover gives, and the
recogniser's pin and key facts. The step is otherwise `unitStep_nativeBlock`'s, line for line.

The input `heta` of `unitStep_nativeBlock` is stated for every prefix `env`; it does not hand the
producer the store keys and used references at that prefix, which `struct_is_rec_doms` reads, so
this step is stated anew rather than derived from that one.

One input remains: the projection guard of the new table (`hguard`, `BlockGuard`).
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

/-- **`UnitStep` for a one-type native inductive block without its recursor, its η fields
produced** (module docstring). -/
theorem unitStep_nativeBlock_eta {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
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
    (hP : HashedBlockProjectionsHeld E) (hcov : L1.CanonicalHashCoverage E calls)
    (hguard : ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
      (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
      (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
      BlockGuard ⟨E, env, t, some n⟩ new B) :
    UnitStep.{u} (NativeBlockX.{u} t E) t envT E₀ E lim B cb := by
  subst hlim
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
  have hT : BlockTable ⟨E, env, t, some n⟩ new B ind :=
    blockTable_of_install hI hinv hpin hna hO.facts hcvT hO.nP₀ hO.nIdx₀ hO.lenA hctorsA hfreshT
      (hguard env new _ p₀ p ty' ctorsA caps hO)
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
  -- the carried clause after the install
  have hreg₂ : LateRegistry.{u} t E ⟨new ++ env.consts⟩ :=
    LateRegistry.nativeNoRec' hreg hO.facts (lateFamAt_of_install hrec hO)
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
