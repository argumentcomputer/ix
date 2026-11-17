import IxVMRefinement.Assembly.NativeBlockFinal
import IxVMRefinement.Assembly.NativeBlockRecScan

/-! # The η fields of the load contract at a native block's new family

`blockEta_of_install`: the two η fields of `NewLoads` at the family a native block's install
stores (`BlockEta`), from the install read off the member check (`NativeInstallOut`), the block's
record, the prefix invariant, the store keys and used references of the prefix, and the
recogniser's pin and key facts.

Both fields read a load whose family is new. That family is the new block's member `0`
(`BlockInstall.famNew`, `iprj_key_block`, `cprj_key_block`), whose record has no index and one
constructor (`iprj_get_ci_value`, `BlockInstall.formerLoad`). The constructor a field names is the
block's constructor `0`: a constructor of the prefix at one of the block's constructor keys would
have its inductive stored in the prefix (`PrefixInv.ctor_ind_stored`), and the former's key is
fresh there. The capability record is `nativeCaps` of the family (`NativeInstallOut.caps_eq`),
whose η flag reads three facts:

* no index, one constructor: the load's counts;
* not a proposition: the sort the use reads, never zero at some levels, is the family's result
  sort substituted twice (`isEquiv_zero_false_of_subst_subst`);
* not recursive: the circuit's `struct_is_rec` answer other than `1` at the former
  (`nativeIsRec_false_of_struct_is_rec`), over the stored constructors, each the canonical
  annotation of its slot's reading (`NativeInstallOut.ctorsCanon`).

The use facts are `NativeNoRecFacts.etaUseFacts`.
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

/-! ## Two load facts -/

/-- A level never zero at some levels after two substitutions is not equivalent to `0`. -/
theorem isEquiv_zero_false_of_subst_subst {ps₁ ps₂ : List Ix.Kernel.LevelParam}
    {us₁ us₂ : List Ix.Kernel.Level} {s : Ix.Kernel.Level}
    (hnz : (Ix.Kernel.Level.subst ps₂ us₂ (Ix.Kernel.Level.subst ps₁ us₁ s)).isNeverZero = true) :
    (Ix.Kernel.Level.isEquiv s .zero == some true) = false := by
  cases heq : (Ix.Kernel.Level.isEquiv s .zero == some true) with
  | false => rfl
  | true =>
    have h0 := Decl.eval_zero_of_isEquiv_zero heq
      (Ix.Kernel.Level.substFn (Ix.Kernel.Level.substFn (fun _ => 0) ps₂ us₂) ps₁ us₁)
    rw [← Ix.Kernel.Level.eval_subst (Ix.Kernel.Level.substFn (fun _ => 0) ps₂ us₂) ps₁ us₁ s,
      ← Ix.Kernel.Level.eval_subst (fun _ => 0) ps₂ us₂] at h0
    exact absurd h0 (Ix.Kernel.Level.isNeverZero_sound (fun _ => 0) _ hnz)

/-- **A direct load of a one-inductive block's member**: its value is the block's inductive with
the record's counts (the twin of `former_get_ci_value` for `Ingress::get_ci_iprj`). -/
theorem iprj_get_ci_value {E : Ixon.Env} {bp ptr : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {b : Bytes.Address} {i : F}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (ev : ObsFn Core.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs)
    {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf E (Core.ixAddr b) = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hi : ZMod.val i = 0) :
    ∃ tyPtr blkPtr : SourceValue F,
      loadValue h' ptr = .ok (.construct Core.kciEnum "Induct"
        [.field (ind.lvls.toNat : F), tyPtr, .field (ind.params.toNat : F),
          .field (ind.indices.toNat : F), .field (ind.ctors.size : F), L1.repBoolField ind.isUnsafe,
          blkPtr, .field ((ZMod.val i : Nat) : F)]) ∧
      ind.params.toNat < 72057594037927936 ∧ ind.indices.toNat < 72057594037927936 ∧
      ind.ctors.size < 72057594037927936 := by
  obtain ⟨-, -, blkBytes, cb', ms', ind', blobs, v, hhB, haB, hexB, -, hcb, hms, -, hld,
    hraw, -⟩ := L1.get_ci_iprj_origin_spec hbound hb ev
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : (#[.indc ind] : Array Ixon.MutConst) = ms' :=
    Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  have hiEq : ind = ind' := by
    have hms0 : (#[.indc ind] : Array Ixon.MutConst).toList[ZMod.val i]? = some (.indc ind') :=
      hms
    rw [hi] at hms0
    exact Ixon.MutConst.indc.inj (Option.some.inj hms0)
  subst hiEq
  obtain ⟨-, hp56, hi56, hc56, -, tyPtr, blkPtr, b', -, -, hv, -⟩ := hraw
  subst hv
  exact ⟨tyPtr, blkPtr, hld, hp56, hi56, hc56⟩

/-! ## The new family's constructors -/

section
variable {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
  {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
  {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
  {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
  {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}

/-- The family's constructors are the recognised block's. -/
theorem NativeInstallOut.ctors_eq
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps) :
    p.ctors = p₀.ctors := by
  obtain ⟨-, -, isRec, cvS', cvTa, caps', p₁, q, ctorsB, sortss, kinds, tfvs, trest, isorts, hfam,
    hInd, hp, -⟩ := hO.facts
  injection hfam with h1 h2 h3 h4
  rw [← h1] at hp
  obtain ⟨cvTa₀, s, bs, cvS'', -, -, -, -, hp₁, -⟩ := hInd
  subst hp₁
  exact (congrArg (fun q : Ix.Kernel.NativeParts .anon => q.ctors) hp).trans rfl

/-- **Each stored constructor is the canonical annotation of its slot's reading** (the input
`hctorsA` of `nativeIsRec_false_of_struct_is_rec`). -/
theorem NativeInstallOut.ctorsCanon
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps) :
    ∀ cA ∈ ctorsA, ∃ (j : Nat) (ct : Ixon.Constructor) (cty : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧
      (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
      cty.looseBVarsBounded 0 = true ∧
      cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) + 1 +
          ((j : Nat) : F)) ct.typ cty = some cA.1.type := by
  have hI := hO.install
  intro cA hcA
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcA
  have hjs : j < ind.ctors.size := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    rw [hO.lenA] at this
    exact this
  obtain ⟨ct, cty', hct, -, -, hAj⟩ := hO.ctors j hjs
  rw [hAj] at hj
  injection hj with hj
  subst hj
  obtain ⟨ct', cty, cty'', hct', hcidx, hty, hlbb, hdef, hcan, hfC⟩ := hI.ctor j hjs
  rw [hct] at hct'
  injection hct' with e
  subst e
  have hfA : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      (Core.keyOf t (Core.cprjAddr B 0 j)) =
      some (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B 0 j), List.range ct.lvls.toNat, cty'⟩
        p.nP ct.fields.toNat) := hO.ctorFind _ hcA
  have hfC' : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      (Core.keyOf t (Core.cprjAddr B 0 j)) =
      some (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B 0 j), List.range ct.lvls.toNat, cty''⟩
        ct.params.toNat ct.fields.toNat) := hfC
  rw [hfA] at hfC'
  injection hfC' with e1
  injection e1 with e2 e3 e4
  injection e2 with e5 e6 e7
  refine ⟨j, ct, cty, hct, hcidx, hty, hlbb, hdef, ?_⟩
  rw [hcan]
  exact congrArg some e7.symm

/-- **A one-constructor new family**: the family's one constructor is at the key of the block's
constructor `0`, and the constructor stored there has the record's parameter count, the
family's field count and level parameters. -/
theorem NativeInstallOut.ctorZero
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hrec : BlockUnitRecord E₀ B cb ind) (hsz : ind.ctors.size = 1) :
    ∃ c : ConstantVal .anon × Nat, p.ctors = [c] ∧
      c.1.name = Core.keyOf t (Core.cprjAddr B 0 0) ∧
      ∀ (cvc : ConstantVal .anon) (cnP cnF : Nat),
        (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? (Core.keyOf t (Core.cprjAddr B 0 0)) =
          some (.ctorInfo cvc cnP cnF) →
        cnP = ind.params.toNat ∧ cnF = c.2 ∧ cvc.levelParams = List.range ind.lvls.toNat := by
  have hL := lateFamAt_of_install hrec hO
  have hlenA : ctorsA.length = p.ctors.length := hL.stored.lenA
  have hcf : ∀ (j : Nat) (c cA : ConstantVal .anon × Nat), p.ctors[j]? = some c →
      ctorsA[j]? = some cA → cA.2 = c.2 := hL.ctorFields
  obtain ⟨c, hpc⟩ : ∃ c, p.ctors = [c] :=
    List.length_eq_one_iff.mp (by rw [← hlenA, hO.lenA, hsz])
  obtain ⟨ct, cty', hct, hcl, hcp, hA⟩ := hO.ctors 0 (by omega)
  have hcA0 : ctorsA = [(⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat, cty'⟩,
      ct.fields.toNat)] := by
    obtain ⟨cA, hcA⟩ : ∃ cA, ctorsA = [cA] := List.length_eq_one_iff.mp (by rw [hO.lenA, hsz])
    rw [hcA] at hA ⊢
    simpa using hA
  have hnames : p.ctors.map (·.1.name) = ctorsA.map (·.1.name) := by
    rw [hO.ctors_eq]
    exact hO.ctorNames
  rw [hpc, hcA0] at hnames
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hnames
  have h2 := hcf 0 c (⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat, cty'⟩,
    ct.fields.toNat) (by simp [hpc]) (by simp [hcA0])
  refine ⟨c, hpc, hnames, fun cvc cnP cnF hfC => ?_⟩
  have hfA : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
      (Core.keyOf t (Core.cprjAddr B 0 0)) =
      some (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat, cty'⟩
        p.nP ct.fields.toNat) :=
    hO.ctorFind (⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat, cty'⟩,
      ct.fields.toNat) (by rw [hcA0]; exact List.mem_singleton_self _)
  rw [hfA] at hfC
  injection hfC with hfC
  injection hfC with e1 e2 e3
  subst cvc
  subst cnP
  subst cnF
  refine ⟨hO.nP, h2, ?_⟩
  show List.range ct.lvls.toNat = List.range ind.lvls.toNat
  rw [hcl]

/-! ## The capability record -/

/-- **The new family's capability record is η-capable**, where its record has no index and one
constructor, the sort its former ends in after the parameters is never zero at some levels, and
the circuit's `struct_is_rec` answers other than `1` at the former. -/
theorem NativeInstallOut.etaCaps
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hkeys : HashKeyed t env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hidx : ind.indices.toNat = 0)
    {l : Ix.Kernel.Level} {us : List Ix.Kernel.Level}
    (hl : Core.piSortAt ind.params.toNat (Core.posOf (List.range ind.lvls.toNat) ty') = some l)
    (hnz : (Ix.Kernel.Level.subst (List.range us.length) us l).isNeverZero = true)
    {sp v : SourceValue F} {h5 h6 : Heap F} {cs5 : List (Call F)} {sa : Bytes.Address}
    (ev : ObsFn Core.W "KernelWhnf::struct_is_rec" [sp] h5 v h6 cs5) (hv : v ≠ .field 1)
    (good : Core.Good ⟨E, env, t, some n⟩ cs5)
    (hsa : Bytes.RepAddressRef Core.addrTy h5 sa sp)
    (hsaB : Core.ixAddr sa = Core.iprjAddr B 0)
    (c : ConstantVal .anon × Nat) (hpc : p.ctors = [c]) :
    caps.eta = true ∧ caps.etaCtor = some c.1.name ∧ caps.etaFields = c.2 ∧
      caps.etaParams = ind.params.toNat := by
  have hI := hO.install
  have hL := lateFamAt_of_install hrec hO
  have hnIdx : p.nIdx = 0 := by rw [hO.nIdx, hidx]
  -- not a proposition
  have hisProp : p.isProp = (Ix.Kernel.Level.isEquiv p.resSort .zero == some true) := hL.isProp
  obtain ⟨bs, hsort⟩ : ∃ bs, ty'.stripPis (p.nP + p.nIdx) = some (bs, .sort p.resSort) := hL.sort
  rw [hnIdx, Nat.add_zero, hO.nP] at hsort
  have hps := Core.WhnfAux.piSortAt_ilp_of_strip (List.range ind.lvls.toNat)
    (Core.posLevels (List.range ind.lvls.toNat)) _ _ _ _ hsort
  have hl' : Core.piSortAt ind.params.toNat (ty'.instantiateLevelParams
      (List.range ind.lvls.toNat) (Core.posLevels (List.range ind.lvls.toNat))) = some l := hl
  rw [hps] at hl'
  have hle := Option.some.inj hl'
  rw [← hle] at hnz
  have hprop : p.isProp = false := by
    rw [hisProp]
    exact isEquiv_zero_false_of_subst_subst hnz
  -- not recursive
  have hkinds : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) p.cvT.name
      p.cvT.levelParams p.nP p.nIdx ctorsA = .ok p.kinds := hL.kinds
  have hrecF : Ix.Kernel.nativeIsRec p.kinds = false :=
    nativeIsRec_false_of_struct_is_rec hI.check hI.decoded hinv hkeys hI.block hI.muts
      hI.formerRec hstored hfreshT ev hv good hsa hsaB (by rw [hO.cvT]; exact hO.cvT₀.1) hO.nP
      hkinds hO.ctorsCanon
  obtain ⟨he1, he2, he3, he4⟩ := Decl.nativeCaps_eta_true hpc hnIdx hprop hrecF
  rw [hO.caps_eq]
  exact ⟨he1, he2, he3, he4.trans hO.nP⟩

/-! ## The two fields -/

/-- **The two η fields of the load contract at the new family** (module docstring). Every
hypothesis is in hand in the body of `unitStep_nativeBlock`: `hrec` (the block's record), `hinv`
(the fold's invariant at the prefix), `hkeys` (the carried store-key clause), `hstored`
(`usedRefsStored_of_cover`), `hpin` and `hna` (`blockReads_of_member`), and the install `hO`
(`nativeInstallOut_of_member`). -/
theorem blockEta_of_install (hrec : BlockUnitRecord E₀ B cb ind)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hkeys : HashKeyed t env)
    (hstored : Decl.UsedRefsStored t env cb) (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : Decl.DeclNonAux (.indDecl blk ind.params.toNat))
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps) :
    BlockEta ⟨E, env, t, some n⟩ new := by
  have hI := hO.install
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none := by
    obtain ⟨ci, hci, ci₀, hname, -⟩ :=
      hO.reads (Core.iprjAddr B 0) (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
    have h := hO.fresh ci hci
    rw [hname] at h
    exact h
  have hnaKeys : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci =>
    (hna.1 ci (by simpa [IxVM.Consistency.installs, hpin] using hci)).1
  have hκT : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.iprjAddr B 0) =
      Core.keyOf t (Core.iprjAddr B 0) :=
    appCtx_key_of_find (c := ⟨E, env, t, some n⟩) (new := new) hO.formerFind
  refine ⟨?_, ?_⟩
  · -- `eta`: a direct load of the member
    intro ac b sa i j cvc cvT caps' cnP cnF us l bp ptr nl ty np u blk' idx h1 h2 cs1 hfC hname
      hpos ev good hb hld hfT hmod hpi hnz hsr hsa hm
    have hbh := L1.hashedBlockAt_of_get_ci_iprj (c := appCtx ⟨E, env, t, some n⟩ new) good hb ev
    have hnC : cvc.name = (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.ixAddr ac) :=
      Core.WhnfAux.name_of_find hfC
    -- the member is the new block's member `0`
    have hfam : FamNew (appCtx ⟨E, env, t, some n⟩ new).stored new (Core.ixAddr b)
        (ZMod.val i) := by
      rcases hm with hm | hm
      · have hfC' : (appCtx ⟨E, env, t, some n⟩ new).env.find?
            ((appCtx ⟨E, env, t, some n⟩ new).stored.κ
              (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) j)) = some (.ctorInfo cvc cnP cnF) := by
          rw [← hname, hnC]
          exact hfC
        exact Or.inr ⟨j, cvc, cnP, cnF, hfC', hm⟩
      · exact Or.inl ⟨cvT, caps', hfT, hm⟩
    obtain ⟨hbB, hi0⟩ := hI.famNew hbh (val_lt_uint64 i) hfam
    have hbhB : Core.HashedBlockAt E B := by
      rw [← hbB]
      exact hbh
    -- its counts: no index, one constructor
    have hblock' : recordOf E (Core.ixAddr b) = some cb := by
      rw [hbB]
      exact hI.block
    obtain ⟨tyPtr, blkPtr, hld₀, hp56, hi56, hc56⟩ :=
      iprj_get_ci_value good.1 good.2 hb ev hblock' hI.muts hi0
    rw [hld₀] at hld
    have hv := Except.ok.inj hld
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hv
    obtain ⟨-, -, -, hm0, hn1, -⟩ := hv
    have hidx : ind.indices.toNat = 0 := by
      have e := field_count_eq hi56 hm0
      rw [ZMod.val_zero] at e
      exact e.symm
    have hsz : ind.ctors.size = 1 := by
      have e := field_count_eq hc56 hn1
      rw [ZMod.val_one] at e
      exact e.symm
    -- the inductive is the former with the install's capability record
    have hfT₁ := hfT
    rw [hbB, hi0, hκT] at hfT₁
    have hfT' : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
        (Core.keyOf t (Core.iprjAddr B 0)) = some (.indInfo cvT caps') := hfT₁
    rw [hO.formerFind] at hfT'
    injection hfT' with hfT'
    injection hfT' with ecv ecaps
    subst cvT
    subst caps'
    -- the constructor is new: a prefix constructor at the block's key would store its inductive
    have hname' := hname
    rw [hbB, hi0] at hname'
    have hctorNew : ConstantInfo.ctorInfo cvc cnP cnF ∈ new := by
      rcases find?_append_cases (env := env) new hfC with hm' | ho
      · exact hm'
      · exfalso
        have hn : cvc.name = (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.ixAddr ac) :=
          Core.WhnfAux.name_of_find ho
        have ho' : env.find? ((appCtx ⟨E, env, t, some n⟩ new).stored.κ
            (Core.cprjAddr B 0 j)) = some (.ctorInfo cvc cnP cnF) := by
          rw [← hname', hn]
          exact ho
        by_cases hu : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.cprjAddr B 0 j) =
            Core.unresolvedKey
        · rw [hu, hinv.unresolved] at ho'
          cases ho'
        · have hk := (appCtx ⟨E, env, t, some n⟩ new).stored.key_eq hu
          rw [hk] at ho'
          obtain ⟨ci, hci⟩ := hinv.ctor_ind_stored hbhB ho'
          rw [hfreshT] at hci
          cases hci
    -- it is the block's constructor `0`
    obtain ⟨j', hj', hkj⟩ := hI.newCtor hfC hctorNew
    have hj0 : j' = 0 := by omega
    subst hj0
    have hres : (ConstantInfo.ctorInfo cvc cnP cnF).name ≠ Core.unresolvedKey := by
      rcases hI.newName _ hctorNew with h | ⟨j'', -, h⟩ | ⟨tbl, h⟩
      · rw [h]
        exact keyOf_ne_unresolvedKey t _
      · rw [h]
        exact keyOf_ne_unresolvedKey t _
      · cases h
    have hκac : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.ixAddr ac) =
        Core.keyOf t (Core.cprjAddr B 0 0) :=
      (appCtx_key_of_new hfC hres).trans hkj
    have hfC0 : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
        (Core.keyOf t (Core.cprjAddr B 0 0)) = some (.ctorInfo cvc cnP cnF) := by
      rw [← hκac]
      exact hfC
    obtain ⟨c, hpc, hcname, hc0⟩ := hO.ctorZero hrec hsz
    obtain ⟨hcnP, hcnF, hcvcL⟩ := hc0 cvc cnP cnF hfC0
    -- the capability record
    obtain ⟨sp, v, h5, h6, cs5, ev5, hv5, good5, hsa5⟩ := hsr
    have hsaB : Core.ixAddr sa = Core.iprjAddr B 0 := by
      rw [hsa, hbB, hi0]
    have hpi' : Core.piSortAt ind.params.toNat
        (Core.posOf (List.range ind.lvls.toNat) ty') = some l := by
      rw [← hcnP]
      exact hpi
    obtain ⟨he1, he2, he3, he4⟩ := hO.etaCaps hrec hinv hkeys hstored hfreshT hidx hpi' hnz ev5
      hv5 ⟨good5.1, good5.2⟩ hsa5 hsaB c hpc
    have hctor : caps.etaCtor =
        some ((appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.ixAddr ac)) := by
      rw [he2, hcname, hκac]
    refine ⟨⟨he1, hctor, he3.trans hcnF.symm, he4.trans hcnP.symm, hcvcL⟩, ?_⟩
    exact NativeNoRecFacts.etaUseFacts hpin hnaKeys hO.facts hinv.store hfT he1 hctor hfC
  · -- `etaIota`: a load of the former's projection
    intro pp ptr nl ty u blk' h1 h2 cs1 pa b i m cvT cvc caps' cnP cnF us l ev good hpa hld hb
      hfT hfC hmulti hsr hpi hnz hm
    have hx := get_ci_induct_addr ev good.2 hpa hld hb
    have hbh := L1.hashedBlockAt_of_get_ci_induct (c := appCtx ⟨E, env, t, some n⟩ new) good ev
      hpa hld hb
    -- the member is the new block's member `0`
    have hBi : Core.ixAddr b = B ∧ ZMod.val i = 0 := by
      rcases hm with hm | hm
      · obtain ⟨hk, -⟩ := hI.newInd hfT hm
        exact iprj_key_block hI.wf hI.decoded hI.held hI.formerRec hbh (val_lt_uint64 i)
          (by rw [← hx]; exact hk)
      · obtain ⟨j', hj', hk⟩ := hI.newCtor hfC hm
        obtain ⟨hbB, hi0, -⟩ := cprj_key_block hI.wf hI.decoded hI.held (hI.ctorRec j' hj') hbh hk
        exact ⟨hbB, toUInt64_zero_of_lt (val_lt_uint64 i) hi0⟩
    obtain ⟨hbB, hi0⟩ := hBi
    have hxa : Core.ixAddr pa = Core.iprjAddr B 0 := by
      rw [hx, hbB, hi0]
    -- its counts
    obtain ⟨hpv, hiv, hsz⟩ := hI.formerLoad ev good hpa hld hxa
    have hidx : ind.indices.toNat = 0 := by
      rw [← hiv, ZMod.val_zero]
    -- the inductive is the former with the install's capability record
    have hfA : (appCtx ⟨E, env, t, some n⟩ new).env.find? (Core.keyOf t (Core.ixAddr pa)) =
        some (.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
          caps) := by
      rw [hxa]
      exact hO.formerFind
    have hκa : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.ixAddr pa) =
        Core.keyOf t (Core.ixAddr pa) :=
      appCtx_key_of_find (c := ⟨E, env, t, some n⟩) (new := new) hfA
    have hfT' : (appCtx ⟨E, env, t, some n⟩ new).env.find? (Core.keyOf t (Core.ixAddr pa)) =
        some (.indInfo cvT caps') := by
      rw [← hκa]
      exact hfT
    rw [hfA] at hfT'
    injection hfT' with hfT'
    injection hfT' with ecv ecaps
    subst cvT
    subst caps'
    -- the constructor at slot `0`
    obtain ⟨c, hpc, hcname, hc0⟩ := hO.ctorZero hrec hsz
    have hκc : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.cprjAddr B 0 0) =
        Core.keyOf t (Core.cprjAddr B 0 0) := by
      obtain ⟨ct, cty, cty', -, -, -, -, -, -, hfC₀⟩ := hI.ctor 0 (by omega)
      exact appCtx_key_of_find hfC₀
    have hκc' : (appCtx ⟨E, env, t, some n⟩ new).stored.κ
        (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0) = Core.keyOf t (Core.cprjAddr B 0 0) := by
      rw [hbB, hi0]
      exact hκc
    have hfC0 : (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
        (Core.keyOf t (Core.cprjAddr B 0 0)) = some (.ctorInfo cvc cnP cnF) := by
      rw [← hκc']
      exact hfC
    obtain ⟨hcnP, hcnF, hcvcL⟩ := hc0 cvc cnP cnF hfC0
    -- the capability record
    obtain ⟨sp, v, h5, h6, cs5, ev5, hv5, good5, hsa5⟩ := hsr
    have hpi' : Core.piSortAt ind.params.toNat
        (Core.posOf (List.range ind.lvls.toNat) ty') = some l := by
      rw [← hpv]
      exact hpi
    obtain ⟨he1, he2, he3, he4⟩ := hO.etaCaps hrec hinv hkeys hstored hfreshT hidx hpi' hnz ev5
      hv5 ⟨good5.1, good5.2⟩ hsa5 hxa c hpc
    have hctor : caps.etaCtor = some ((appCtx ⟨E, env, t, some n⟩ new).stored.κ
        (Core.cprjAddr (Core.ixAddr b) (ZMod.val i) 0)) := by
      rw [he2, hcname, hκc']
    refine ⟨⟨he1, hctor, he3.trans hcnF.symm, he4.trans hcnP.symm, hcnP.trans hpv.symm,
      hcvcL⟩, ?_⟩
    exact NativeNoRecFacts.etaUseFacts hpin hnaKeys hO.facts hinv.store hfT he1 hctor hfC

end

end IxVM.Refinement.Typing
