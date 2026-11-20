import IxVMRefinement.Assembly.NativeBlockInstallLim
import IxVMRefinement.Assembly.NativeBlockFinalRetHead
import IxVMRefinement.Assembly.NativeAliasStep
import IxVMRefinement.Assembly.NativeAliasRetHead
import IxVMRefinement.Assembly.FoldClauseSteps
import IxVMRefinement.Binding.Raise

/-! # The unit step of a one-type native block whose former is declared at its telescope

The ordinary inductive type: a block of one inductive member whose stored former's type is a
syntactic telescope of the parameters and indices ending in a sort. Its check installs the
former, the constructors and, at one constructor and no index, the projection table; the fold's
clause registers the family.

The step is stated once, for both folds (`NativeUnitStep`): the clause is asked at the store
and the limit the block's check is read at, and is kept at every store of a family `Stores`, at
every limit and every registry, with the registry extended by the one family. The typing fold
reads it at its one store (`NativeUnitStep.unitStep`); the binding fold reads it at every
record store for its witness store.

* `BlockInstall.withLim`, `BlockInstall.atStore`: the new constants as the store reads them,
  at another limit and at another store that holds the block's records. Neither reads a run.
* `famRead_of_install`: the family the install names, read off the store at the environment
  after the install.
* `FoldClauseWith.nativeNoRec`: the install keeps the clause at one store, limit and registry,
  from IxC's record of the install, the load contract, the store keys and the family read
  off the store at the new environment.
* `NativeInstallOut.keeps`: the install's output at a store gives the clause there after the
  install, at every limit and registry. The projection table of a structure-like proposition
  fires by its certificate over the store (`BlockCert`, an input) and the reading of a
  projection guard's run (`Core.ProjGuardRunReading`, a premise); elsewhere no table is
  certified. The two η fields
  of the load contract are read at the empty limit, which every prefix invariant lowers to;
  neither they nor the table's fields read the limit.
* `nativeInstall_of_member`: the install's output from the walk's member check at either role
  context, with the constructors' literal return, the absence of projections out of the
  family, the sorts the table stage ran at as the classifier checked them, and the block's
  types read over the run's store. At the store of the check those sorts and the reading of
  the classifier's field loop over it, which the run store gives, give the certificate.
* `NativeUnitStep`, `NativeUnitStep.unitStep`, `nativeUnitStep_of_install`,
  `nativeUnitStep_of_member`, `unitStep_nativeBlockTele`.
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
open Ix.Kernel.Semantics (NativeFam NativeFamStored)

universe u

/-! ## The new constants at another limit and at another store -/

/-- **The new constants as the store reads them do not read the limit.** -/
theorem BlockInstall.withLim {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {t : Ix.Kernel.RoleTable} {lim lim' : Option Nat} {new : List (ConstantInfo .anon)}
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}
    (h : BlockInstall ⟨E, env, t, lim⟩ new B cb ind caps) :
    BlockInstall ⟨E, env, t, lim'⟩ new B cb ind caps :=
  { check := h.check
    decoded := h.decoded
    held := h.held
    block := h.block
    muts := h.muts
    formerRec := h.formerRec
    ctorRec := h.ctorRec
    bounds := h.bounds
    used := h.used
    former := h.former
    ctor := h.ctor
    newName := h.newName
    newFind := h.newFind
    unit := h.unit
    free := h.free }

/-- **The new constants as another store reads them**: a store that holds the block's records
and the run's blobs reads the former's and the constructors' types as the store of the check
does, where the run's store reads them (`hty`, `hcty`) and the store of the check holds the
run's blobs. -/
theorem BlockInstall.atStore {t : Ix.Kernel.RoleTable} {E₀ Ec E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lc lim : Option Nat} {new : List (ConstantInfo .anon)}
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {caps : IndCaps .anon}
    (h : BlockInstall ⟨Ec, env, t, lc⟩ new B cb ind caps)
    (hEc : ∀ a b, E₀.blobs.get? a = some b → Ec.blobs.get? a = some b)
    (hH : HoldsBlock E₀ E B cb ind)
    (hty : ∃ ty₀, (exprReader t (fun x => E₀.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀)
    (hcty : ∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
      ∃ tyj, (exprReader t (fun x => E₀.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ct.typ = .ok tyj) :
    BlockInstall ⟨E, env, t, lim⟩ new B cb ind caps :=
  { check := h.check
    decoded := hH.decoded
    held := hashedBlockProjectionsHeld_of_decoded hH.decoded
    block := hH.block
    muts := h.muts
    formerRec := hH.former
    ctorRec := hH.ctors
    bounds := h.bounds
    used := h.used
    former := by
      obtain ⟨ty₀, ty', hrd, hlbb, hdef, hcan, hfind⟩ := h.former
      obtain ⟨ty, hty⟩ := hty
      have hrdc := ReaderReads.exprReader_mono (fun x b hb => hEc x b hb) hty
      have e : ty = ty₀ := Except.ok.inj (hrdc.symm.trans hrd)
      subst e
      exact ⟨ty, ty', ReaderReads.exprReader_mono (fun x b hb => hH.blobs x b hb) hty, hlbb,
        hdef, hcan, hfind⟩
    ctor := by
      intro j hj
      obtain ⟨ct, cty, cty', hct, hcidx, hrd, hlbb, hdef, hcan, hfind⟩ := h.ctor j hj
      obtain ⟨tyj, htyj⟩ := hcty j ct hct
      have hrdc := ReaderReads.exprReader_mono (fun x b hb => hEc x b hb) htyj
      have e : tyj = cty := Except.ok.inj (hrdc.symm.trans hrd)
      subst e
      exact ⟨ct, tyj, cty', hct, hcidx,
        ReaderReads.exprReader_mono (fun x b hb => hH.blobs x b hb) htyj, hlbb, hdef, hcan, hfind⟩
    newName := h.newName
    newFind := h.newFind
    unit := h.unit
    free := h.free }

/-! ## The clause after the install, from its parts -/

/-- **The install of a block whose former is declared at its telescope keeps the clause**,
registering its family, at one store, limit and registry. From the clause before and IxC's
record of the install (`NativeNoRecFacts`): the model step registers the family, the prefix
invariant is `PrefixInv.nativeNoRec_eta`, the roots and the level clauses are IxC's. What the
step reads off its run: the load contract at the new environment, that the new keys resolve
and are keys of 32-byte addresses or of none, and the family read off the store there. -/
theorem FoldClauseWith.nativeNoRec {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {lim : Option Nat}
    {env env₂ : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : NativeFam .anon}
    (h : FoldClauseWith.{u} L t E lim env Reg)
    (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hpin : Ix.Kernel.basisPinHit blk = none) (hna : Decl.DeclNonAux (.indDecl blk nP))
    (hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env₂.find? k = some ci →
      env.find? k = none → k ≠ Core.unresolvedKey)
    (hloads : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env₂, t, lim⟩))
    (hkeys₂ : HashKeyed t env₂) (hread : FamRead L t E env₂ fam)
    (hnewCtor : ∀ (C : _root_.Address) (cm : Ixon.Constant) (cp : Ixon.ConstructorProj)
      (cv : ConstantVal .anon) (nP nF : Nat),
      env₂.find? (keyOf t C) = some (.ctorInfo cv nP nF) → env.find? (keyOf t C) = none →
      Ix.Cert.recordAt E C = some cm → cm.info = .cPrj cp →
      ∃ j cA, fam.p.cvT.name = keyOf t (Core.iprjAddr cp.block cp.idx.toNat) ∧
        fam.ctorsA[j]? = some cA ∧ cA.1.name = keyOf t C ∧ cp.cidx.toNat = j) :
    FoldClauseWith.{u} L t E lim env₂ (fun f => Reg f ∨ f = fam) := by
  have hinv₂ : Decl.PrefixInv.{u} E t lim env₂ :=
    PrefixInv.nativeNoRec_eta h.prefixInv hfacts hpin hna hres hloads
  have hno := hfacts.noRecNoDefn
  exact FoldClauseWith.of_prefix hinv₂
    (h.registry.install hL (fun V _ hm => hfacts.register V hm) hfacts.envExt hread
      hfacts.newInd hnewCtor
      (fun hp => recRhsPwNoModel_append_noRec hfacts.envExt hp (let ⟨new, heq, hn⟩ := hno; ⟨new, heq, fun ci hci => (hn ci hci).1⟩))
      (fun hm => recHasModelNotNative_append_noRecNoDefn hfacts.envExt hm hno))
    hkeys₂ (NativeNoRecFacts.auxRootSynced hpin hna hfacts h.auxRoot)
    (NativeNoRecFacts.lvClauses hpin hfacts ⟨h.thmLevels, h.storeArR⟩)

/-! ## The new family read off the store -/

/-- **The family the install names is read off the store at the environment after the
install**: the stored former is the telescope constant, so the link holds by the link laws; the
telescope constant's facts are the stored former's, at a well-formed, arity-correct store. The
constructors' literal return and the absence of projections out of the family are inputs. -/
theorem famRead_of_install {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hwf : Ix.Kernel.EnvWF ⟨new ++ env.consts⟩) (hA : Ix.Kernel.Model.StoreArR ⟨new ++ env.consts⟩)
    (hrh : FamIxonRetHead t E
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩)
    (hnp : BlockFamCtorNoProj
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩) :
    FamRead L t E ⟨new ++ env.consts⟩
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ := by
  have hI := hO.install
  have hnd₀ : (p₀.ctors.map (·.1.name)).Nodup := hO.facts.2.1
  have hpT : p.cvT.name = Core.keyOf t (Core.iprjAddr B 0) := by rw [hO.cvT]; exact hO.cvT₀.1
  have hpL : p.cvT.levelParams = List.range ind.lvls.toNat := by rw [hO.cvT]; exact hO.cvT₀.2
  have hctor : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
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
  obtain ⟨-, -, isRec, cvS', cvTa, caps', p₁, q, ctorsB, sortss, kinds, tfvs, trest, isorts, hfam,
    hInd, hp, hCtors, hK, -, -, -, -, -, -⟩ := hO.facts
  injection hfam with h1 h2 h3 h4
  subst h2 h3
  rw [← h4] at hCtors hK
  rw [← h1] at hp hCtors hK
  obtain ⟨cvTa₀, s, bs, cvS'', -, -, hstrip, -, hp₁, -⟩ := hInd
  subst hp₁
  have hpnP : p.nP = p₀.nP := by rw [hp]; rfl
  have hpnIdx : p.nIdx = p₀.nIdx := by rw [hp]; rfl
  have hpres : p.resSort = s := by rw [hp]; rfl
  have hpk : p.kinds = kinds := by rw [hp]; rfl
  obtain ⟨hlA, -, hall⟩ := hCtors
  have hlps : List.range ind.lvls.toNat = p.cvT.levelParams := hpL.symm
  have hsort : ∃ bs, ty'.stripPis (p.nP + p.nIdx) = some (bs, .sort p.resSort) :=
    ⟨bs, by rw [hpnP, hpnIdx, hpres]; exact hstrip⟩
  have htc : TeleChecked ⟨new ++ env.consts⟩
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ :=
    TeleChecked.of_stored hO.formerFind rfl hlps hwf hA
  refine {
    stored := ?stored
    lps := hlps
    tele := htc
    sort := hsort
    isProp := by rw [hp]; rfl
    kinds := by rw [hpk]; exact hK
    nodup := by rw [← hO.ctorNames]; exact hnd₀
    ctorFields := fun j c cA hc hcA => (hall j c cA hc hcA).1
    record := ?record
    retHead := hrh
    noProj := hnp
    link := hL.ofTele rfl hsort htc }
  case stored =>
    refine { former := ?_, ctor := ?_, lenA := hlA, lenK := ?_ }
    · rw [hpT, ← hO.caps_eq]
      exact hO.formerFind
    · intro j cA hcA
      replace hcA : ctorsA[j]? = some cA := hcA
      have hjc : j < p.ctors.length := by
        have := (List.getElem?_eq_some_iff.mp hcA).1
        omega
      obtain ⟨c, hc⟩ : ∃ c, p.ctors[j]? = some c :=
        ⟨p.ctors[j]'hjc, List.getElem?_eq_getElem hjc⟩
      obtain ⟨hf2, sorts, -, hrun⟩ := hall j c cA hc hcA
      obtain ⟨-, -, -, -, ⟨cbs, es, hst, hes⟩, -⟩ := Decl.sumCtorRunJ_struct_facts hrun
      refine ⟨hO.ctorFind cA (List.mem_of_getElem? hcA), ?_, cbs, es, ?_, hes⟩
      · rw [(hctor j cA hcA).2, hpL]
      · rw [hf2]
        exact hst
    · rw [hpk]
      exact (Ix.Kernel.classifyFixKinds_inv hK).2.2.2.symm
  case record =>
    have hrecA : Ix.Cert.recordAt E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
      (recordOf_eq_recordAt_of_decoded hI.decoded _).symm.trans hI.formerRec
    have hrecB : Ix.Cert.recordAt E B = some cb :=
      (recordOf_eq_recordAt_of_decoded hI.decoded _).symm.trans hI.block
    have h0 : ((0 : Nat).toUInt64).toNat = 0 := by decide
    refine ⟨Core.iprjAddr B 0, memberProjection B 0 (.indc ind), ⟨(0 : Nat).toUInt64, B⟩, cb,
      #[.indc ind], ind, hpT, hrecA, rfl, hrecB, hI.muts, ?_, hO.nP, hO.nIdx, hO.lenA, ?_,
      hrec.logic, hpL⟩
    · show (#[Ixon.MutConst.indc ind])[((0 : Nat).toUInt64).toNat]? = some (.indc ind)
      rw [h0]
      rfl
    · intro j cA hcA
      show cA.1.name = Core.keyOf t (Core.cprjAddr B ((0 : Nat).toUInt64).toNat j)
      rw [h0]
      exact (hctor j cA hcA).1

/-! ## The install's output keeps the clause -/

/-- **The install's output at a store keeps the fold's clause there**, at every limit and
every registry, registering its family (module docstring). `hO` is the output at the store `E`
with the empty limit index; `hH` says `E` holds the block's records; `hret` and `hnp` are the
two facts about the block's constructors; `hcert` is the certificate of the new projection
table over `E`, asked only at one constructor, no index and a sort that tests zero. -/
theorem NativeInstallOut.keeps {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (ht : t.check = .ok ()) (hread : Core.ProjGuardRunReading)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hO : NativeInstallOut t E₀ E 0 env B cb ind blk p₀ new p ty' ctorsA caps)
    (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : Decl.DeclNonAux (.indDecl blk ind.params.toNat))
    (hstored : Decl.UsedRefsStored t env cb)
    (hret : BlockCtorIxonRetHead cb ind)
    (hnp : BlockFamCtorNoProj
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩)
    (hH : HoldsBlock E₀ E B cb ind)
    (hcert : ind.ctors.size = 1 → ind.indices.toNat = 0 →
      Ix.Kernel.Level.isEquiv p.resSort .zero = some true →
      BlockCert t E ⟨new ++ env.consts⟩ B)
    {lim : Option Nat} {Reg : NativeFam .anon → Prop}
    (hC : FoldClauseWith.{u} L t E lim env Reg) :
    FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩
      (fun f => Reg f ∨ f =
        ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
          ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩) := by
  have htwf : t.wf = true := hC.tableWf
  have hinv : Decl.PrefixInv.{u} E t lim env := hC.prefixInv
  have hkeys : HashKeyed t env := hC.hashKeyed
  have haux : Decl.AuxRootSynced env := hC.auxRoot
  have hI : BlockInstall ⟨E, env, t, lim⟩ new B cb ind caps := hO.install.withLim
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none := by
    obtain ⟨ci, hci, ci₀, hname, -⟩ :=
      hO.reads (Core.iprjAddr B 0) (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
    have h := hO.fresh ci hci
    rw [hname] at h
    exact h
  have hbaseT : (Core.keyOf t (Core.iprjAddr B 0)).base = Core.keyOf t (Core.iprjAddr B 0) :=
    Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hfreshTbl : env.find?
      (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) = none :=
    haux.fresh_of_base_none (by
      show env.find? (Core.keyOf t (Core.iprjAddr B 0)).base = none
      rw [hbaseT]
      exact hfreshT)
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
  -- the certificate of the table the new environment stores at the family's table name
  have hcertAll : BlockCert t E ⟨new ++ env.consts⟩ B := by
    by_cases hs : ind.ctors.size = 1 ∧ ind.indices.toNat = 0 ∧
        Ix.Kernel.Level.isEquiv p.resSort .zero = some true
    · exact hcert hs.1 hs.2.1 hs.2.2
    · intro tbl hTb hz
      exfalso
      rcases find?_append_cases (env := env) new hTb with hm | hold
      · obtain ⟨h1, h2, h3⟩ := hO.table_struct hm
        rw [h3] at hz
        exact hs ⟨h1, h2, hz⟩
      · rw [hfreshTbl] at hold
        cases hold
  have hG : BlockFire ⟨E, env, t, lim⟩ new B := blockFire_of_cert hread hI hcertAll
  have hT : BlockTable ⟨E, env, t, lim⟩ new B ind :=
    blockTable_of_install hI hinv hpin hna hO.facts hcvT hO.nP₀ hO.nIdx₀ hO.lenA hctorsA hfreshT
      hG
  -- the η fields, read at the empty limit
  have hinv0 : Decl.PrefixInv.{u} E t (some 0) env :=
    Binding.prefixInv_lower hinv (fun r hr => absurd (hr.2 0 rfl) (Nat.not_lt_zero _))
  have hE0 : BlockEta ⟨E, env, t, some 0⟩ new :=
    blockEta_of_install hrec hinv0 hkeys hstored hpin hna hO
  have hE : BlockEta ⟨E, env, t, lim⟩ new := ⟨hE0.eta, hE0.etaIota⟩
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
  have hloads := storedLoads_append (c := ⟨E, env, t, lim⟩) hinv.loads hO.facts.envExt hnres
    hinv.etaStable (hI.newLoads hT hE)
  have hinv₂ : Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ :=
    PrefixInv.nativeNoRec_eta hinv hO.facts hpin hna hres hloads
  have hkeys₂ : HashKeyed t ⟨new ++ env.consts⟩ := by
    refine HashKeyed.append htwf hkeys fun ci hci => ?_
    rcases hI.newName ci hci with h | ⟨j, hj, h⟩ | ⟨tbl, rfl⟩
    · exact Or.inl ⟨Core.iprjAddr B 0, h, address_size_of_record hS hrec.former⟩
    · exact Or.inl ⟨Core.cprjAddr B 0 j, h, address_size_of_record hS (hrec.ctors j hj)⟩
    · exact Or.inr fun y h =>
        Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t y) h.symm
  have hlv₂ : LvClauses ⟨new ++ env.consts⟩ :=
    NativeNoRecFacts.lvClauses hpin hO.facts ⟨hC.thmLevels, hC.storeArR⟩
  -- the family read off the store
  have hfamT : p.cvT.name = Core.keyOf t (Core.iprjAddr B 0) := by
    rw [hO.cvT]
    exact hO.cvT₀.1
  have hreadF : FamRead L t E ⟨new ++ env.consts⟩
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ :=
    famRead_of_install hL hrec hO hinv₂.store.store.wf hlv₂.2
      (famIxonRetHead_of_holds ht hH hrec.muts hret hfamT) hnp
  have hnewCtor := newCtor_of_blockInstall (E := E) (B := B) (ind := ind) htwf hI.decoded
    hI.ctorRec hI.bounds.2.2 hO.lenA hfamT (fun j cA hcA => (hctorsA j cA hcA).1)
    hO.facts.newCtor
  exact hC.nativeNoRec hL hO.facts hpin hna hres hloads hkeys₂ hreadF hnewCtor

/-! ## The install's output from the walk's member check -/

/-- **The install of a block whose former is declared at its telescope, read off the walk's
member check** at either role context, at an environment that satisfies the clause at the
check's store and limit: the install's output at the empty limit index, the recogniser's pin
and key facts, the used references, the constructors' literal return, the absence of
projections out of the family, that the table stage ran at sorts the classifier checked, and
the block's types as the run's store reads them. -/
theorem nativeInstall_of_member {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : L1.CanonicalHashCoverage E calls)
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts) (hnd : (env.consts.map (·.name)).Nodup)
    (hC : FoldClauseWith.{u} L t E lim env Reg)
    (href : ∀ x, UsedRef E₀ B x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf B cb x ∨ ¬ NeedOk E₀ x)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none) :
    ∃ (blk : List (ConstantInfo .anon)) (p₀ : Ix.Kernel.NativeParts .anon)
      (new : List (ConstantInfo .anon)) (p : Ix.Kernel.NativeParts .anon)
      (ty' : Ix.Kernel.Expr .anon) (ctorsA : List (ConstantVal .anon × Nat))
      (caps : IndCaps .anon),
      NativeInstallOut t E₀ E 0 env B cb ind blk p₀ new p ty' ctorsA caps ∧
      Ix.Kernel.basisPinHit blk = none ∧
      Decl.DeclNonAux (.indDecl blk ind.params.toNat) ∧
      Decl.UsedRefsStored t env cb ∧
      BlockCtorIxonRetHead cb ind ∧
      BlockFamCtorNoProj
        ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
          ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ ∧
      InstallSortsCheckedLim calls t E lim env B
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA ∧
      (∃ ty₀, (exprReader t (fun x => E₀.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀) ∧
      (∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
        ∃ tyj, (exprReader t (fun x => E₀.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok tyj) := by
  have hP : HashedBlockProjectionsHeld E := hashedBlockProjectionsHeld_of_decoded hst.decoded
  have hinv : Decl.PrefixInv.{u} E t lim env := hC.prefixInv
  have hkeys : HashKeyed t env := hC.hashKeyed
  have haux : Decl.AuxRootSynced env := hC.auxRoot
  have hbound : Bounded calls := (hst.good env none).2
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  obtain ⟨ty₀, cs, hty, hlen, hcs, hall⟩ := blockReads_of_member_lim ht hbound hS hrec hchk
  obtain ⟨hblk, hpin, hna⟩ := hall {}
  obtain ⟨p₀, hp₀, -⟩ := nativeParts_of_member_lim ht hbound hS hrec hchk htele hblk hfree
  obtain ⟨new, p, ty', ctorsA, caps, hO, hSorts⟩ := nativeInstallOut_of_member_checked_lim
    (n := 0) ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP hkeys hfresh hfree hcov haux
    hnd
  have hRaw := blockRawRetHead_of_member_lim ht hS hst hrec hchk hnat htele hblk hp₀ hinv
    hstored hP hkeys hfresh hfree hcov haux
  have hret : BlockCtorIxonRetHead cb ind := blockCtorIxonRetHead_of_raw ht hS hst hrec hchk hRaw
  have hnp := blockFamCtorNoProj_of_member_lim ht hS hst hrec hchk hnat htele hblk hp₀ hinv
    hstored hP hkeys hfresh hfree hcov haux hO
  refine ⟨_, p₀, new, p, ty', ctorsA, caps, hO, hpin, hna, hstored, hret, hnp, hSorts,
    ⟨ty₀, hty⟩, ?_⟩
  intro j ct hct
  have hj : j < cs.length := by
    rw [hlen]
    exact (Array.getElem?_eq_some_iff.mp hct).1
  obtain ⟨ct', tyj, hct', -, -, -, htyj, -⟩ := hcs j cs[j] (List.getElem?_eq_getElem hj)
  have e : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  subst e
  exact ⟨tyj, htyj⟩

/-! ## The step, stated once -/

/-- **The unit step of a one-type native block that registers one family, stated once**
(module docstring). `Ec` and `lc` are the store and the limit the block's check is read at;
`Stores` are the stores the clause is kept at. At every environment that extends `envT`, has
distinct names, satisfies the clause at `Ec` and `lc` with a registry `Reg`, stores every used
reference of the record that is not one of its own constant addresses (unless the reference is
no in-logic constant address of the run's store) and stores none of the record's constant
addresses: there are fresh constants `new` with distinct names and one family `fam` such that,
at every store in `Stores`, every limit and every registry `Reg'`, the clause at `env` with
`Reg'` gives the clause at `new ++ env` with `Reg'` extended by `fam`; every constant of `new`
is at the key of a constant address of the record or at a derived key; and at each constant
address of the record `new` holds a constant at that address's key that stores a reading of
the address over the run's records. -/
def NativeUnitStep (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (Stores : Ixon.Env → Prop) (Ec : Ixon.Env) (lc : Option Nat) (B : _root_.Address)
    (cb : Ixon.Constant) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    FoldClauseWith.{u} L t Ec lc env Reg →
    (∀ x, UsedRef E₀ B x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf B cb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none) →
    ∃ (new : List (ConstantInfo .anon)) (fam : NativeFam .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ (E : Ixon.Env) (lim : Option Nat) (Reg' : NativeFam .anon → Prop), Stores E →
        FoldClauseWith.{u} L t E lim env Reg' →
        FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ (fun f => Reg' f ∨ f = fam)) ∧
      (∀ ci ∈ new, (∃ x, ConstAddrOf B cb x ∧ ci.name = keyOf t x) ∨
        ∃ k s, ci.name = .aux k s) ∧
      (∀ x, ConstAddrOf B cb x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      Ix.Kernel.EnvExt env ⟨new ++ env.consts⟩

/-- **The typing fold's step**: the step of the unit against a store the clause is kept at, at
the limit of its check, for the part of the fold's clause beside the prefix invariant. -/
theorem NativeUnitStep.unitStep {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    {E₀ E : Ixon.Env} {Stores : Ixon.Env → Prop} {lim : Option Nat} {B : _root_.Address}
    {cb : Ixon.Constant} (hE : Stores E)
    (h : NativeUnitStep.{u} L t envT E₀ Stores E lim B cb) :
    UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim B cb := by
  intro env hext hnd hinv hX href hfresh
  obtain ⟨⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hC : FoldClauseWith.{u} L t E lim env Reg :=
    FoldClauseWith.of_prefix hinv hR hkeys haux hlv
  obtain ⟨new, fam, hnd', hfr, hkeep, hnamed, hreads, -⟩ := h env Reg hext hnd hC href hfresh
  have hC' := hkeep E lim Reg hE hC
  exact ⟨new, hnd', hfr, hC'.prefixInv, hC'.extra, hreads, hnamed⟩

/-- **The step from the install's output at every store the clause is kept at.** At each
environment the step is asked at, `hout` gives the install's output at the store of the check,
the facts about the block that no store reads, and at every store in `Stores` the output there
and the certificate of the new projection table over it. -/
theorem nativeUnitStep_of_install {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ Ec : Ixon.Env} {Stores : Ixon.Env → Prop}
    {lc : Option Nat} {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (ht : t.check = .ok ()) (hread : Core.ProjGuardRunReading)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hholds : ∀ E, Stores E → HoldsBlock E₀ E B cb ind)
    (hout : ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
      (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
      FoldClauseWith.{u} L t Ec lc env Reg →
      (∀ x, UsedRef E₀ B x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf B cb x ∨ ¬ NeedOk E₀ x) →
      (∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none) →
      ∃ (blk : List (ConstantInfo .anon)) (p₀ : Ix.Kernel.NativeParts .anon)
        (new : List (ConstantInfo .anon)) (p : Ix.Kernel.NativeParts .anon)
        (ty' : Ix.Kernel.Expr .anon) (ctorsA : List (ConstantVal .anon × Nat))
        (caps : IndCaps .anon),
        NativeInstallOut t E₀ Ec 0 env B cb ind blk p₀ new p ty' ctorsA caps ∧
        Ix.Kernel.basisPinHit blk = none ∧
        Decl.DeclNonAux (.indDecl blk ind.params.toNat) ∧
        Decl.UsedRefsStored t env cb ∧
        BlockCtorIxonRetHead cb ind ∧
        BlockFamCtorNoProj
          ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
            ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ ∧
        ∀ E, Stores E →
          NativeInstallOut t E₀ E 0 env B cb ind blk p₀ new p ty' ctorsA caps ∧
          (ind.ctors.size = 1 → ind.indices.toNat = 0 →
            Ix.Kernel.Level.isEquiv p.resSort .zero = some true →
            BlockCert t E ⟨new ++ env.consts⟩ B)) :
    NativeUnitStep.{u} L t envT E₀ Stores Ec lc B cb := by
  intro env Reg hext hnd hC href hfresh
  obtain ⟨blk, p₀, new, p, ty', ctorsA, caps, hO, hpin, hna, hstored, hret, hnp, hat⟩ :=
    hout env Reg hext hnd hC href hfresh
  refine ⟨new,
    ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩,
    hO.nodup, hO.fresh, ?_, hO.named, hO.reads, hO.facts.envExt⟩
  intro E lim Reg' hE hC'
  obtain ⟨hOE, hcertE⟩ := hat E hE
  exact hOE.keeps hL ht hread hS hrec hpin hna hstored hret hnp (hholds E hE) hcertE hC'

/-- **The step from the walk's member check, kept at the store of the check**: the form the
typing fold reads. `hread` is the reading of a projection guard's run. The certificate of the
new projection table over the step's store is read from the sorts the table stage ran at and
the reading of the classifier's field loop over that store, which the run store gives
(`blockCert_of_reading_lim`, `Guard.checkedSortsReadingAt_of_stepStore`; `hrecs` says the run's
store holds the run's hashed records). -/
theorem nativeUnitStep_of_member {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : L1.CanonicalHashCoverage E calls)
    (hrecs : LoadedReads.HashedRecordsStored calls E₀) (hread : Core.ProjGuardRunReading) :
    NativeUnitStep.{u} L t envT E₀ (fun E' => E' = E) E lim B cb := by
  refine nativeUnitStep_of_install hL ht hread hS hrec
    (fun E' hE' => hE' ▸ HoldsBlock.of_stepStore hst hrec) ?_
  intro env Reg hext hnd hC href hfresh
  obtain ⟨blk, p₀, new, p, ty', ctorsA, caps, hO, hpin, hna, hstored, hret, hnp, hSorts, -, -⟩ :=
    nativeInstall_of_member ht hS hst hrec hchk hnat htele hfree hinert hcover hcov hext hnd hC
      href hfresh
  refine ⟨blk, p₀, new, p, ty', ctorsA, caps, hO, hpin, hna, hstored, hret, hnp, ?_⟩
  intro E' hE'
  subst hE'
  exact ⟨hO, fun h1 h0 hz =>
    blockCert_of_reading_lim ((Guard.checkedSortsReadingAt_of_stepStore hS hrecs hst).block _) hO hSorts h1
      h0 hz⟩

/-- **`UnitStep` for a one-type native inductive block whose former is declared at its
telescope, for the fold's clause**, at the walk's limit under either role context. The inputs
are what a checked unit's step is handed, the kind's three facts, and the reading of a
projection guard's run `hread` (`nativeUnitStep_of_member`). -/
theorem unitStep_nativeBlockTele {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : L1.CanonicalHashCoverage E calls)
    (hrecs : LoadedReads.HashedRecordsStored calls E₀) (hread : Core.ProjGuardRunReading) :
    UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim B cb :=
  NativeUnitStep.unitStep (Stores := fun E' => E' = E) rfl
    (nativeUnitStep_of_member hL ht hS hst hrec hchk hnat htele hfree hinert hcover hcov hrecs
      hread)

end IxVM.Refinement.Typing
