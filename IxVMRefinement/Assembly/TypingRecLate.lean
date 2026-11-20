import IxVMRefinement.Assembly.LateRegistry
import IxC.Kernel.Model.StoreLate

/-! # The step of a recursor record for a registered native family

A standalone recursor record whose family is an ordinary inductive family the circuit treats
as native is installed by IxC's late step (`DeclNativeRecLateRunJ`): the recursor for a family
already stored, at the record's own position. This module proves the refinement's side of that
step from the step's relation:

* `LateRegistryWith.at_parent`: **the registered summary is the one the circuit reads**. At a
  stored former whose record in the store is an inductive projection of a block the circuit
  treats as native, under no basis name, the registry holds a family of that name, read off the
  same record: the same member of the same block, its parameter and index counts, as many
  constructors as the member has, constructor `j` at the key of constructor projection `j`.
  The registry's completeness gives a family of the name; its tie gives a projection address
  with that key, which is the parent's (keys identify addresses), and the record there is the
  one the circuit read (one store).
* `late_head`: the head the late step conses is the recursor, fresh, and no table's name.
* `CoreCompanions.cons_rec`: the role and record companions of the scoped core kept by a
  recursor, given its own four facts (major premise's record, rule constructors, plain rules,
  rule heads); `late_companions`: those four facts for the late step's recursor, from the family
  read off the parent's record and the relation (the major premise is the family, whose key is
  the parent's; the rules are at the family's constructors in order).
* `late_prefixInv_step`: the prefix invariant and the registry at the environment with the
  recursor, from the relation, the companions there and the recursor's reload. The model step
  is IxC's `EnvModelN.late`; the store facts are `storeFacts_declNativeRecLateRunJ`; the
  refinement's own store fields (`StrongEnvProps`, `EtaCtorStored`, `EtaShape`,
  `AuxRootSynced`) hold because the head is a recursor at a base key; the load contract is
  `storedLoads_cons_value` (a recursor is none of the excluded kinds).
* `unitStep_recLate_of`: the skeleton's `UnitStep` for the record, with the clause
  `LateRegistry t E`, from two interfaces of the circuit's check of the record: the parent
  family it read (`RecParent`), and, for a registered family read off the same records, the
  relation with the stored constant and the recursor's reload (`RecLateOut`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key RecRule)
open Ix.Kernel.Semantics (NativeFam NativeFamStored DeclNativeRecLateRunJ Judgements)
open Ix.Kernel.Model (rulesJ EnvModelN EnvModelT)

/-! ## The registered summary is the one the circuit reads -/

/-- **The family the registry holds at a parent the circuit read**: a stored former whose
record in `E` is an inductive projection of a block a good run treats as native, under no basis
name. The family is registered, is read off the store, and is read off this record: the same
member of the same block, its counts, its constructor count and constructor keys. -/
theorem LateRegistryWith.at_parent {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    (h : LateRegistryWith.{u} t E env Reg) (ht : t.check = .ok ())
    {P : _root_.Address} {cm : Ixon.Constant} {ip : Ixon.InductiveProj}
    {cv : ConstantVal .anon} {caps : IndCaps .anon}
    (hf : env.find? (keyOf t P) = some (.indInfo cv caps))
    (hres : Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false)
    (hcm : Ix.Cert.recordAt E P = some cm) (hinfo : cm.info = .iPrj ip)
    (hnat : NativeAt E ip.block) :
    ∃ fam, Reg fam ∧ LateFamAt t E env fam ∧ fam.p.cvT.name = keyOf t P ∧
      ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
        Ix.Cert.recordAt E ip.block = some cb ∧ cb.info = .muts ms ∧
        ms[ip.idx.toNat]? = some (.indc ind) ∧
        fam.p.nP = ind.params.toNat ∧ fam.p.nIdx = ind.indices.toNat ∧
        fam.ctorsA.length = ind.ctors.size ∧
        ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
          cA.1.name = keyOf t (Core.cprjAddr ip.block ip.idx.toNat j) := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨fam, hReg, hname⟩ := h.complete P cm ip cv caps hf hres hcm hinfo hnat
  have hat := h.fams fam hReg
  obtain ⟨P', cm', ip', cb, ms, ind, hn', hcm', hinfo', hcb, hms, hind, hp, hi, hlen, hctors,
    -, -⟩ := hat.record
  have hPP : P' = P := keyOf_inj hroles (hn'.symm.trans hname)
  rw [hPP, hcm] at hcm'
  have hcc : cm' = cm := (Option.some.inj hcm').symm
  rw [hcc, hinfo] at hinfo'
  have hii : ip' = ip := (Ixon.ConstantInfo.iPrj.inj hinfo').symm
  rw [hii] at hcb hind hctors
  exact ⟨fam, hReg, hat, hname, cb, ms, ind, hcb, hms, hind, hp, hi, hlen, hctors⟩

/-- **A registered family read off the parent's record** (`LateRegistryWith.at_parent`'s
conclusion, without the registry). -/
def MatchedAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (P : _root_.Address) (ip : Ixon.InductiveProj) (fam : NativeFam .anon) : Prop :=
  LateFamAt t E env fam ∧ fam.p.cvT.name = keyOf t P ∧
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E ip.block = some cb ∧ cb.info = .muts ms ∧
      ms[ip.idx.toNat]? = some (.indc ind) ∧
      fam.p.nP = ind.params.toNat ∧ fam.p.nIdx = ind.indices.toNat ∧
      fam.ctorsA.length = ind.ctors.size ∧
      ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
        cA.1.name = keyOf t (Core.cprjAddr ip.block ip.idx.toNat j)

/-- **The block's logic and the family's level parameters, read at a record of the family's
name**: the registered family's own record is this one (keys identify addresses, one store), so
its block is in Lean's logic and its level parameters are the positions below the member's level
count. -/
theorem LateFamAt.logic_lvls {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon} (hat : LateFamAt t E env fam)
    (ht : t.check = .ok ()) {P : _root_.Address} {cm : Ixon.Constant} {ip : Ixon.InductiveProj}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hname : fam.p.cvT.name = keyOf t P) (hcm : Ix.Cert.recordAt E P = some cm)
    (hinfo : cm.info = .iPrj ip) (hcb : Ix.Cert.recordAt E ip.block = some cb)
    (hms : cb.info = .muts ms) (hind : ms[ip.idx.toNat]? = some (.indc ind)) :
    InLogic cb ∧ fam.p.cvT.levelParams = List.range ind.lvls.toNat := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨P', cm', ip', cb', ms', ind', hn', hcm', hinfo', hcb', hms', hind', -, -, -, -,
    hlog, hlps⟩ := hat.record
  have hPP : P' = P := keyOf_inj hroles (hn'.symm.trans hname)
  rw [hPP, hcm] at hcm'
  have hcc : cm' = cm := (Option.some.inj hcm').symm
  rw [hcc, hinfo] at hinfo'
  have hii : ip' = ip := (Ixon.ConstantInfo.iPrj.inj hinfo').symm
  rw [hii, hcb] at hcb'
  have hbb : cb' = cb := (Option.some.inj hcb').symm
  rw [hbb, hms] at hms'
  injection hms' with hmm
  rw [← hmm, hii, hind] at hind'
  injection hind' with h1
  injection h1 with hdd
  rw [hbb] at hlog
  rw [← hdd] at hlps
  exact ⟨hlog, hlps⟩

/-- **The block's logic and the family's level parameters at the matched parent.** -/
theorem MatchedAt.logic_lvls {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {P : _root_.Address} {ip : Ixon.InductiveProj}
    {fam : NativeFam .anon} (hm : MatchedAt t E env P ip fam) (ht : t.check = .ok ())
    {cm : Ixon.Constant} (hcm : Ix.Cert.recordAt E P = some cm) (hinfo : cm.info = .iPrj ip) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E ip.block = some cb ∧ cb.info = .muts ms ∧
      ms[ip.idx.toNat]? = some (.indc ind) ∧
      InLogic cb ∧ fam.p.cvT.levelParams = List.range ind.lvls.toNat := by
  obtain ⟨hat, hname, cb, ms, ind, hcb, hms, hind, -⟩ := hm
  exact ⟨cb, ms, ind, hcb, hms, hind,
    hat.logic_lvls ht hname hcm hinfo hcb hms hind⟩

/-! ## The head of the late step -/

/-- **The late step conses the recursor**: fresh, no table's name, named after the declared
record. -/
theorem late_head {J : Judgements .anon} {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    {cvR : ConstantVal .anon} {mI rP : Nat} {rules : List (RecRule .anon)}
    {cn : ConstantInfo .anon}
    (h : DeclNativeRecLateRunJ J env fam cvR mI rP rules ⟨cn :: env.consts⟩) :
    env.find? cn.name = none ∧ (∀ T : Key .anon, cn.name ≠ Ix.Kernel.projTableName T) ∧
      cn.name = cvR.name ∧ ∃ cv a b rs, cn = .recInfo cv a b rs := by
  obtain ⟨elim, large, pR, cvRa, rhss, hpR, -, -, -, -, -, -, -, hRec, henv⟩ := h
  obtain ⟨hnR, -, hfR, hshR⟩ := hRec.recursor
  injection henv with h1
  injection h1 with hcn _
  have hpc : pR.cvR = cvR := by rw [hpR]; rfl
  have hname : cn.name = cvR.name := by
    rw [hcn, ← hpc]
    exact hnR
  refine ⟨?_, ?_, hname, _, _, _, _, hcn⟩
  · rw [hcn]
    show env.find? cvRa.name = none
    rw [hnR]
    exact hfR
  · intro T
    rw [hcn]
    show cvRa.name ≠ Ix.Kernel.projTableName T
    rw [hnR]
    exact Ix.Kernel.Semantics.ne_projTableName_of_shape hshR T

/-! ## The companions after a recursor -/

/-- **The role and record companions after a recursor**, from those before and the recursor's
own four facts at the longer environment. -/
theorem CoreCompanions.cons_rec {c : Core.Ctx} (h : Decl.CoreCompanions c)
    {cv : ConstantVal .anon} {mI rP : Nat} {rls : List (RecRule .anon)}
    (hfresh : c.env.find? cv.name = none)
    (hnt : ∀ T : Key .anon, cv.name ≠ Ix.Kernel.projTableName T)
    (hmaj : ∀ (p : _root_.Address) (us : List Core.KLevel), rls ≠ [] →
      (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
      ∃ cm, Ix.Cert.recordAt c.E p = some cm)
    (hrules : (rls.map (·.ctor)).Nodup ∧
      ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
        (us : List Core.KLevel),
        (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (c.κ p) us) →
        Ix.Cert.recordAt c.E p = some cm → cm.info = .iPrj ip →
        ∀ j rl, rls[j]? = some rl → rl.ctor = c.κ (Core.cprjAddr ip.block ip.idx.toNat j))
    (hplain : ∀ (rl : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat), rl ∈ rls →
      rl.fire = .plain →
      (⟨.recInfo cv mI rP rls :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? rl.ctor =
        some (.ctorInfo cvj nP nF) →
      ∃ D T, Core.piDomAt mI cv.type = some D ∧
        D.getAppFn = .const T (cvj.levelParams.map .param) ∧
        D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
        D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i))
    (hhead : ∀ (rl : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat) (T : Key .anon)
      (us : List Core.KLevel), rl ∈ rls →
      (⟨.recInfo cv mI rP rls :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? rl.ctor =
        some (.ctorInfo cvj nP nF) →
      (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const T us) →
      ∃ tus, (Ix.Kernel.Expr.piResult cvj.type).getAppFn = .const T tus) :
    Decl.CoreCompanions ⟨c.E, ⟨.recInfo cv mI rP rls :: c.env.consts⟩, c.t, c.lim⟩ := by
  have hext : Ix.Kernel.EnvExt c.env ⟨.recInfo cv mI rP rls :: c.env.consts⟩ :=
    Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
  have hold : ∀ {k : Key .anon} {x : ConstantInfo .anon},
      (⟨.recInfo cv mI rP rls :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? k = some x →
        x ≠ .recInfo cv mI rP rls → c.env.find? k = some x := by
    intro k x hf hne
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · exact absurd (Option.some.inj hf).symm hne
    · exact hf
  have hctor_old : ∀ {k : Key .anon} {cvj : ConstantVal .anon} {nP nF : Nat},
      (⟨.recInfo cv mI rP rls :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? k =
        some (.ctorInfo cvj nP nF) → c.env.find? k = some (.ctorInfo cvj nP nF) :=
    fun hf => hold hf (fun e => nomatch e)
  have hsplit : ∀ {k : Key .anon} {cv' : ConstantVal .anon} {mI' rP' : Nat}
      {rls' : List (RecRule .anon)},
      (⟨.recInfo cv mI rP rls :: c.env.consts⟩ : Ix.Kernel.Env .anon).find? k =
        some (.recInfo cv' mI' rP' rls') →
      (cv' = cv ∧ mI' = mI ∧ rP' = rP ∧ rls' = rls) ∨
        c.env.find? k = some (.recInfo cv' mI' rP' rls') := by
    intro k cv' mI' rP' rls' hf
    rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · injection hf with hf'
      injection hf' with e1 e2 e3 e4
      exact Or.inl ⟨e1.symm, e2.symm, e3.symm, e4.symm⟩
    · exact Or.inr hf
  exact
    { natLit := fun h1 h2 h3 => hext.natLitSupported_mono (h.natLit h1 h2 h3)
      strLit := fun h1 => hext.strLitSupported_mono (h.strLit h1)
      natOps := fun r hr hm => hext.natOpStored_mono (h.natOps r hr hm)
      natAdd := fun h1 => hext.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (h.natAdd h1) rfl
      eqStored := fun h1 =>
        let ⟨ci', hci'⟩ := h.eqStored h1
        ⟨ci', hext.find hci'⟩
      quotBasis := fun h1 ci' hm => hext.find (h.quotBasis h1 ci' hm)
      recMajorRecord := by
        intro k cv' mI' rP' rls' p us hf hne hdom
        rcases hsplit hf with ⟨rfl, rfl, rfl, rfl⟩ | hf'
        · exact hmaj p us hne hdom
        · exact h.recMajorRecord k cv' mI' rP' rls' p us hf' hne hdom
      recRulesNodupAndProj := by
        intro k cv' mI' rP' rls' hf
        rcases hsplit hf with ⟨rfl, rfl, rfl, rfl⟩ | hf'
        · exact hrules
        · exact h.recRulesNodupAndProj k cv' mI' rP' rls' hf'
      recPlain := by
        intro k cv' mI' rP' rls' rl cvj nP nF hf hrl hfire hc
        rcases hsplit hf with ⟨rfl, rfl, rfl, rfl⟩ | hf'
        · exact hplain rl cvj nP nF hrl hfire hc
        · exact h.recPlain k cv' mI' rP' rls' rl cvj nP nF hf' hrl hfire (hctor_old hc)
      ruleCtorHead := by
        intro k cv' mI' rP' rls' hf
        rcases hsplit hf with ⟨rfl, rfl, rfl, rfl⟩ | hf'
        · exact Or.inl (fun rl cvj nP nF T us hrl hc hdom => hhead rl cvj nP nF T us hrl hc hdom)
        · exact (h.ruleCtorHead k cv' mI' rP' rls' hf').imp
            (fun hh rl cvj nP nF T us hrl hc hdom => hh rl cvj nP nF T us hrl (hctor_old hc) hdom)
            id }

/-! ## The recursor's own companion facts -/

/-- The rule constructors of `sumRules` are the constructors' names, position by position. -/
theorem sumRules_ctor_getElem? {find? : Key .anon → Option (ConstantInfo .anon)}
    {recName : Key .anon} {nP mI rP : Nat} {recTy : Ix.Kernel.Expr .anon} :
    ∀ {ctorsA : List (ConstantVal .anon × Nat)} {rhss : List (Ix.Kernel.Expr .anon)} {j : Nat}
      {r : RecRule .anon},
      (Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA rhss)[j]? = some r →
      ∃ cA, ctorsA[j]? = some cA ∧ r.ctor = cA.1.name
  | [], _, _, _, h => by simp [Ix.Kernel.sumRules] at h
  | _ :: _, [], _, _, h => by simp [Ix.Kernel.sumRules] at h
  | c :: cs, rhs :: rhss, 0, r, h => by
    simp only [Ix.Kernel.sumRules, List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨c, rfl, by rw [← h]; rfl⟩
  | c :: cs, rhs :: rhss, j + 1, r, h => by
    simp only [Ix.Kernel.sumRules, List.getElem?_cons_succ] at h
    obtain ⟨cA, hcA, hr⟩ := sumRules_ctor_getElem? (ctorsA := cs) (rhss := rhss) h
    exact ⟨cA, by simpa using hcA, hr⟩

/-- The rule constructors of `sumRules` are a sublist of the constructors' names. -/
theorem sumRules_ctors_sublist {find? : Key .anon → Option (ConstantInfo .anon)}
    {recName : Key .anon} {nP mI rP : Nat} {recTy : Ix.Kernel.Expr .anon} :
    ∀ {ctorsA : List (ConstantVal .anon × Nat)} {rhss : List (Ix.Kernel.Expr .anon)},
      ((Ix.Kernel.sumRules find? recName nP mI rP recTy ctorsA rhss).map (·.ctor)).Sublist
        (ctorsA.map (·.1.name))
  | [], _ => by simp [Ix.Kernel.sumRules]
  | _ :: _, [] => by simp [Ix.Kernel.sumRules]
  | c :: cs, rhs :: rhss => by
    simp only [Ix.Kernel.sumRules, List.map_cons, Ix.Kernel.recRuleBits_ctor]
    exact (sumRules_ctors_sublist (ctorsA := cs) (rhss := rhss)).cons_cons _

/-- **The companions after the late step**: the role and record companions of the scoped core
at the environment with the recursor, from those before, the family read off the parent's
record, and the step's relation. The recursor's major premise is the family (`majorOf`), whose
key is the parent's; its rules are at the family's constructors in order, whose keys are the
constructor projections of the parent's member; a rule fires and its constructor builds the
family by the stored constructor's residual. -/
theorem late_companions {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {P : _root_.Address} {ip : Ixon.InductiveProj}
    {cm : Ixon.Constant} {fam : NativeFam .anon} {cvR : ConstantVal .anon} {mI rP : Nat}
    {rules : List (RecRule .anon)} {cn : ConstantInfo .anon}
    (ht : t.check = .ok ()) (hcomp : Decl.CoreCompanions ⟨E, env, t, lim⟩)
    (hm : MatchedAt t E env P ip fam) (hcm : Ix.Cert.recordAt E P = some cm)
    (hcmi : cm.info = .iPrj ip)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩) :
    Decl.CoreCompanions ⟨E, ⟨cn :: env.consts⟩, t, lim⟩ := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨hat, hTP, cb, ms, ind, -, -, -, -, -, -, hnames⟩ := hm
  obtain ⟨elim, large, pR, cvRa, rhss, hpR, -, -, -, -, hst, -, -, hRec, henv⟩ := hrun
  obtain ⟨hfT, hctor, hlenA, hk⟩ := hst.atRec hpR
  obtain ⟨hnR, -, hfR, hshR⟩ := hRec.recursor
  have hfreshR : env.find? cvRa.name = none := by rw [hnR]; exact hfR
  injection henv with h1
  injection h1 with hcn _
  subst hcn
  obtain ⟨bs, B, m, hmaj⟩ := hRec.majorOf ⟨fam.cvS, _, hfT⟩ hk hlenA
  have hdom : Core.piDomAt pR.majorIdx cvRa.type = some (Ix.Kernel.structFamI pR.cvT.name
      pR.cvT.levelParams pR.nP pR.nIdx (pR.ctors.length + 1) 0) :=
    (Decl.piDomAt_eq_some_iff _ _ _).mpr ⟨bs, B, m, hmaj⟩
  have hT : pR.cvT.name = Core.keyOf t P := by
    rw [hpR]
    exact hTP.trans (LoadedReads.keyOf_eq t P).symm
  have hhead : ∀ (T : Key .anon) (us : List Core.KLevel),
      (Core.piDomAt pR.majorIdx cvRa.type).map (·.getAppFn) = some (.const T us) →
      T = pR.cvT.name := by
    intro T us h
    rw [hdom] at h
    have h2 : (Ix.Kernel.structFamI pR.cvT.name pR.cvT.levelParams pR.nP pR.nIdx
        (pR.ctors.length + 1) 0).getAppFn = .const T us := Option.some.inj h
    rw [Ix.Kernel.Semantics.structFamI_getAppFn] at h2
    injection h2 with hT' _
    exact hT'.symm
  have hparent : ∀ (p : _root_.Address) (us : List Core.KLevel),
      (Core.piDomAt pR.majorIdx cvRa.type).map (·.getAppFn) =
        some (.const (Core.keyOf t p) us) → p = P := by
    intro p us h
    exact Core.keyOf_inj htwf ((hhead _ us h).trans hT)
  have hrule : ∀ r ∈ Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix
      cvRa.type fam.ctorsA rhss, ∃ (j : Nat) (cA : ConstantVal .anon × Nat),
        fam.ctorsA[j]? = some cA ∧ r.ctor = cA.1.name ∧ r.ctorParams = pR.nP := by
    intro r hr
    obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
    exact ⟨j, cA, hj, rfl, rfl⟩
  have hctorAt : ∀ (r : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat),
      r ∈ Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix cvRa.type
        fam.ctorsA rhss →
      (⟨.recInfo cvRa pR.majorIdx pR.rulePrefix (Ix.Kernel.sumRules env.find? cvRa.name pR.nP
        pR.majorIdx pR.rulePrefix cvRa.type fam.ctorsA rhss) :: env.consts⟩ :
          Ix.Kernel.Env .anon).find? r.ctor = some (.ctorInfo cvj nP nF) →
      ∃ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA ∧
        cvj = cA.1 ∧ nP = pR.nP ∧ r.ctorParams = pR.nP := by
    intro r cvj nP nF hr hc
    obtain ⟨j, cA, hj, hctorEq, hcp⟩ := hrule r hr
    obtain ⟨hfC, -, -⟩ := hctor j cA hj
    have hc' : (⟨.recInfo cvRa pR.majorIdx pR.rulePrefix (Ix.Kernel.sumRules env.find? cvRa.name
        pR.nP pR.majorIdx pR.rulePrefix cvRa.type fam.ctorsA rhss) :: env.consts⟩ :
          Ix.Kernel.Env .anon).find? cA.1.name = some (.ctorInfo cA.1 pR.nP cA.2) :=
      Ix.Kernel.Env.find?_cons_of_fresh hfreshR hfC
    rw [← hctorEq, hc] at hc'
    obtain ⟨rfl, rfl, -⟩ := Ix.Kernel.ConstantInfo.ctorInfo.inj (Option.some.inj hc')
    exact ⟨j, cA, hj, rfl, rfl, hcp⟩
  have hmr : pR.majorIdx - pR.rulePrefix = pR.nIdx :=
    Nat.add_sub_cancel_left pR.rulePrefix pR.nIdx
  refine CoreCompanions.cons_rec (c := ⟨E, env, t, lim⟩) hcomp hfreshR
    (fun T => by rw [hnR]; exact Ix.Kernel.Semantics.ne_projTableName_of_shape hshR T)
    (fun p us _ h => ⟨cm, by rw [hparent p us h]; exact hcm⟩) ⟨?_, ?_⟩ ?_ ?_
  · exact List.Nodup.sublist sumRules_ctors_sublist hat.nodup
  · intro p cm' ip' us h hcm' hcmi' j rl hrl
    have hp := hparent p us h
    subst hp
    rw [hcm] at hcm'
    have hcc : cm = cm' := Option.some.inj hcm'
    subst hcc
    rw [hcmi] at hcmi'
    have hii : ip = ip' := Ixon.ConstantInfo.iPrj.inj hcmi'
    subst hii
    obtain ⟨cA, hcA, hrc⟩ := sumRules_ctor_getElem? hrl
    rw [hrc]
    exact hnames j cA hcA
  · intro rl cvj nP nF hrl hfire hc
    obtain ⟨j, cA, hj, rfl, rfl, -⟩ := hctorAt rl cvj nP nF hrl hc
    obtain ⟨-, hlps, -⟩ := hctor j cA hj
    refine ⟨_, pR.cvT.name, hdom, ?_, ?_, ?_⟩
    · rw [Ix.Kernel.Semantics.structFamI_getAppFn, hlps]
    · have hps : Ix.Kernel.structPsAt (md := .anon) (0 + (pR.ctors.length + 1) + pR.nIdx) pR.nP =
          (List.range pR.nP).map (fun k => Ix.Kernel.Expr.bvar (pR.majorIdx - 1 - k)) := by
        unfold Ix.Kernel.structPsAt
        refine List.map_congr_left fun k _ => ?_
        congr 1
        show _ = pR.nP + 1 + pR.ctors.length + pR.nIdx - 1 - k
        omega
      rw [Ix.Kernel.Semantics.structFamI_getAppArgs,
        List.take_left' Ix.Kernel.Semantics.length_structPsAt, hps]
    · rw [hmr]
      exact Ix.Kernel.Semantics.structFamI_args_drop
  · intro rl cvj nP nF T us hrl hc hdom'
    obtain ⟨j, cA, hj, rfl, rfl, -⟩ := hctorAt rl cvj nP nF hrl hc
    obtain ⟨-, -, cbs, es, hres, -⟩ := hctor j cA hj
    rw [hhead T us hdom']
    exact ⟨_, Ix.Kernel.Model.family_of_residual hres⟩

/-! ## The invariant at the environment with the recursor -/

/-- **The prefix invariant and the registry after the late step.** From the invariant and the
registry before, a registered family, the step's relation at the environment with the recursor
`cn` in front, `cn` at the key of an address, the companions at the new environment and the
recursor's reload. -/
theorem late_prefixInv_step {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop} {fam : NativeFam .anon}
    {cvR : ConstantVal .anon} {mI rP : Nat} {rules : List (RecRule .anon)}
    {cn : ConstantInfo .anon} {a₀ : _root_.Address}
    (hinv : Decl.PrefixInv.{u} E t lim env) (hR : LateRegistryWith.{u} t E env Reg)
    (hfam : Reg fam)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩)
    (hname : cn.name = Core.keyOf t a₀)
    (hcomp : Decl.CoreCompanions ⟨E, ⟨cn :: env.consts⟩, t, lim⟩)
    (hreload : Decl.ReloadsAs E t ⟨cn :: env.consts⟩ cn) :
    Decl.PrefixInv.{u} E t lim ⟨cn :: env.consts⟩ ∧
      LateRegistryWith.{u} t E ⟨cn :: env.consts⟩ Reg := by
  obtain ⟨hfresh, hnt, -, cv, a, b, rs, hcn⟩ := late_head hrun
  have hind : ∀ cv' caps, cn ≠ .indInfo cv' caps := by
    intro cv' caps h
    rw [hcn] at h
    cases h
  have hctor : ∀ cv' nP nF, cn ≠ .ctorInfo cv' nP nF := by
    intro cv' nP nF h
    rw [hcn] at h
    cases h
  have hproj : ∀ tbl, cn ≠ .projInfo tbl := by
    intro tbl h
    rw [hcn] at h
    cases h
  have hext : Ix.Kernel.EnvExt env ⟨cn :: env.consts⟩ :=
    Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
  have hR' : LateRegistryWith.{u} t E ⟨cn :: env.consts⟩ Reg :=
    hR.step (fun V _ hm => Ix.Kernel.Model.EnvModelN.late V hm hfam hrun) hext
      (fun P cm ip cv' caps hf hold => by
        rw [find_ind_cons_old hind hf] at hold
        cases hold)
  have hS := hinv.store
  obtain ⟨hSI, hRS, hRK, hTT, hET, -⟩ :=
    Ix.Kernel.Model.storeFacts_declNativeRecLateRunJ hrun hS.store hS.recShape hS.recK
      hS.thmTyped hS.etaTowers hS.tableBodies
  have heta := Decl.etaShape_step_noEta hext hS.etaCtorStored hS.etaShape
    (Ix.Kernel.Model.nativeRecLate_newSat (Q := Decl.NoEtaInd)
      (fun _ _ _ _ _ _ h => nomatch h) hrun)
  have hS' : Decl.FoldStoreInv ⟨cn :: env.consts⟩ :=
    { store := hSI
      thmTyped := hTT
      defnTyped := Decl.defnTyped_step_noBaseDefn hext hS.defnTyped
        (Ix.Kernel.Model.nativeRecLate_newSat (Q := Decl.NotBaseDefn)
          (fun _ _ _ _ _ _ _ _ h => nomatch h) hrun)
      recK := hRK
      etaTowers := hET
      strongProps := Decl.strongEnvProps_step_noProj hext.find hS.strongProps
        (Ix.Kernel.Model.nativeRecLate_newSat (Q := Ix.Kernel.Model.NotProj)
          (fun _ _ _ _ _ h => nomatch h) hrun)
      recShape := hRS
      etaCtorStored := heta.1
      etaShape := heta.2 }
  have hbase : cn.name.base = cn.name := by
    rw [hname]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t a₀)
  have hne : cn.name ≠ Core.unresolvedKey := by
    rw [hname]
    exact Core.Resolved.ne
  refine ⟨{ decl := fun V _ => Decl.FullDeclInv.ofFoldInv ⟨hR'.envModelT V, hS'⟩
              ((hinv.decl V).declInvM.auxSynced.cons_of_root_stored (Or.inl hbase))
            store := hS'
            unresolved := ?_
            tableWf := hinv.tableWf
            companions := hcomp
            loads := Decl.storedLoads_cons_value (c := ⟨E, env, t, lim⟩) hinv.loads hname hfresh
              hnt hind hctor hproj hinv.etaStable hreload
            etaStable := hinv.etaStable.cons_value hfresh hnt hind hctor }, hR'⟩
  show (⟨cn :: env.consts⟩ : Ix.Kernel.Env .anon).find? Core.unresolvedKey = none
  rw [Ix.Kernel.Env.find?_cons, ite_eq_right hne]
  exact hinv.unresolved

/-! ## The step of the record -/

/-- **A block the circuit's native recursor route tested is native at the store**: the route's
`block_is_modeled` run answered `0` (`Assembly.native_rec_actual_parent_route`), and its calls,
within the run's, are good for the store. -/
theorem nativeAt_of_route {c : Core.Ctx} {bq : SourceValue F} {h h' : Heap F}
    {cs calls : List (Call F)} {b : Bytes.Address}
    (ev : ObsFn Core.W "KernelModeled::block_is_modeled" [bq] h (.field 0) h' cs)
    (hsub : ∀ x ∈ cs, x ∈ calls) (hg : Core.Good c calls)
    (hb : Bytes.RepAddressRef Core.addrTy h b bq) : NativeAt c.E (Core.ixAddr b) :=
  let g := hg.sub hsub
  ⟨bq, h, h', cs, b, ev, g.1, g.2, hb, rfl⟩

/-- **What the skeleton hands a step at an environment** (`UnitStep`'s premises, without the
extra clause). -/
structure StepAt (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env)
    (lim : Option Nat) (A : _root_.Address) (c : Ixon.Constant) (env : Ix.Kernel.Env .anon) :
    Prop where
  ext : ∀ ci ∈ envT.consts, ci ∈ env.consts
  nodup : (env.consts.map (·.name)).Nodup
  inv : Decl.PrefixInv.{u} E t lim env
  refs : ∀ x, UsedRef E₀ A x →
    (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x
  fresh : ∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none

/-- **The parent family the circuit read at the recursor record**, at a step's environment: a
stored former under no basis name, whose record in the store is an inductive projection of a
block a good run treats as native. -/
def RecParent (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (P : _root_.Address) (ip : Ixon.InductiveProj) : Prop :=
  (∃ cv caps, env.find? (keyOf t P) = some (.indInfo cv caps)) ∧
    Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false ∧
    (∃ cm, Ix.Cert.recordAt E P = some cm ∧ cm.info = .iPrj ip) ∧ NativeAt E ip.block

/-- **What the circuit's check of the recursor record gives at a matched family**: the late
relation with the recursor `cn` in front, `cn` at the record's key and stored as a reading of
the record, and its reload. -/
def RecLateOut (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (A : _root_.Address)
    (env : Ix.Kernel.Env .anon) (fam : NativeFam .anon) : Prop :=
  ∃ (cvR : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon))
    (cn : ConstantInfo .anon) (ci₀ : ConstantInfo .anon),
    DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩ ∧
    cn.name = keyOf t A ∧ Reads t E₀ A ci₀ ∧ StoredAs cn ci₀ ∧
    Decl.ReloadsAs E t ⟨cn :: env.consts⟩ cn

/-- **`UnitStep` for a standalone recursor record of a native family, with the registry**,
from the two interfaces of the circuit's check of the record: at every environment the
skeleton hands the step, the parent family it read (`hparent`), and, for every registered
family read off that parent's record, the late relation and the recursor's facts (`hout`). -/
theorem unitStep_recLate_of {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hinfo : c.info = .recr rc)
    (hparent : ∀ env, StepAt.{u} t envT E₀ E lim A c env →
      ∃ P ip, RecParent t E env P ip)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → RecParent t E env P ip →
      MatchedAt t E env P ip fam → RecLateOut t E₀ E A env fam) :
    UnitStep.{u} (LateRegistry.{u} t E) t envT E₀ E lim A c := by
  intro env hext hnd hinv hX href hfresh
  have hstep : StepAt.{u} t envT E₀ E lim A c env := ⟨hext, hnd, hinv, href, hfresh⟩
  obtain ⟨Reg, hR⟩ := hX
  obtain ⟨P, ip, hpar⟩ := hparent env hstep
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam, hReg, hat, hnameP, hmatch⟩ := hR.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ ⟨hat, hnameP, hmatch⟩
  have hcomp := late_companions ht hinv.companions ⟨hat, hnameP, hmatch⟩ hcm hcmi hrun
  obtain ⟨hinv', hR'⟩ := late_prefixInv_step hinv hR hReg hrun
    (hname.trans (LoadedReads.keyOf_eq t A).symm) hcomp hreload
  obtain ⟨hfreshN, -, -, -⟩ := late_head hrun
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  refine ⟨[cn], List.nodup_singleton _, ?_, hinv', ⟨Reg, hR'⟩, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshN
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hstored⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

end IxVM.Refinement.Typing
