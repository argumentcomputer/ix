import IxVMRefinement.Assembly.NativeBlockFinalRetHead
import IxC.Kernel.Model.Inductives.NativeAtRecLate

/-! # The one clause the declaration folds carry

A fold over accepted declaration steps carries one proposition from step to step. This module
states it once, with the model held once.

* `TeleChecked env fam`: what IxC's former stage establishes of a registered family's telescope
  constant (`SumIndRunJ`): its type is arity-correct and resolves at the environment, is closed
  and bounded, and mentions only the family's level parameters. It holds whether or not the
  telescope constant is the stored former, and it is kept along lookups.
* `FamRead L t E env fam`: a registered family as the store `E` and the table `t` read it. The
  stored former and the telescope constant are related only by `link : L env fam`, where `L` is
  the link a recursor run reads between the two (`LinkLaws` is what the clause asks of it). No
  field identifies the two constants.
* `FoldClauseWith L t E lim env Reg`, `FoldClause L t E lim env`: the clause. Its first part is
  IxC's: one model in every set theory keeping every registered family's data (`EnvModelN`), and
  the store facts IxC keeps along every declaration step. The rest is what the refinement reads
  beside them: the registry read off the store, the keys, and the circuit's loads against the
  store at the limit.
* `FoldExtra L t E env` and `foldClause_iff`: the clause is the prefix invariant together with
  the part beside it, in the shape a unit step takes its extra clause. The prefix invariant's own
  model is rebuilt from the clause (`FoldClauseWith.prefixInv`), so it is not a second datum.

Also here: the registry's reading at a parent (`FamRegistryWith.at_parent`), its steps
(`FamRegistryWith.step`, `.install`), the empty registry (`famRegistryWith_of_noFamily`), the
passage from the clause with the telescope equality (`foldExtra_of_nativeBlockXR`), and the fact
that the clause with the telescope equality has no inhabitant at an environment that stores a
former declared at a definition (`not_nativeBlockXR_of_aliasFormer`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key RecRule)
open Ix.Kernel.Semantics (NativeFam NativeFamStored DeclRunJ IndRoutesJ SumIndRunJ)
open Ix.Kernel.Model (rulesJ EnvModelN EnvModelT ArRes StoreArR)

/-! ## The telescope constant -/

/-- **The telescope constant of a registered family, as the former's stage checked it**: its
type is arity-correct and resolves at the environment, is closed and bounded, and mentions only
the family's level parameters. -/
structure TeleChecked (env : Ix.Kernel.Env .anon) (fam : NativeFam .anon) : Prop where
  arRes : ArRes env fam.cvTa.type
  closed : fam.cvTa.type.hasFvar = false
  bounded : fam.cvTa.type.looseBVarsBounded 0 = true
  levels : fam.cvTa.type.allLevelParamsDefined fam.p.cvT.levelParams = true

/-- The facts are kept along lookups. -/
theorem TeleChecked.ext {env env₂ : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    (h : TeleChecked env fam)
    (hf : ∀ {k : Key .anon} {ci : ConstantInfo .anon},
      env.find? k = some ci → env₂.find? k = some ci) : TeleChecked env₂ fam :=
  { h with arRes := h.arRes.mono hf }

/-- **Where the telescope constant is the stored former**, the store facts give them: the
stored constant is well formed and its type arity-correct. -/
theorem TeleChecked.of_stored {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    {k : Key .anon} {caps : IndCaps .anon}
    (hf : env.find? k = some (.indInfo fam.cvS caps)) (htele : fam.cvTa = fam.cvS)
    (hlps : fam.cvS.levelParams = fam.p.cvT.levelParams) (hwf : Ix.Kernel.EnvWF env)
    (hA : StoreArR env) : TeleChecked env fam := by
  have hc := hwf _ (Ix.Kernel.Semantics.Env.find?_mem hf)
  have hfv : fam.cvS.type.hasFvar = false := hc.1
  have hlp : fam.cvS.type.allLevelParamsDefined fam.cvS.levelParams = true := hc.2.1
  have hlb : fam.cvS.type.looseBVarsBounded 0 = true := hc.2.2.2.1
  have har : ArRes env fam.cvS.type := (hA.const hf).type
  rw [hlps] at hlp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [htele]
    exact har
  · rw [htele]
    exact hfv
  · rw [htele]
    exact hlb
  · rw [htele]
    exact hlp

/-- **The former's stage gives the facts of its telescope constant** at the stage's
environment, at either branch of the stage (the declared former, or a constant checked from
scratch at another type). -/
theorem sumIndRunJ_tele {env envI : Ix.Kernel.Env .anon}
    {sh p' : Ix.Kernel.InductiveShape .anon}
    {capsOf : Ix.Kernel.InductiveShape .anon → IndCaps .anon} {cvTa : ConstantVal .anon}
    (h : SumIndRunJ rulesJ env sh capsOf envI cvTa p') :
    ArRes env cvTa.type ∧ cvTa.type.hasFvar = false ∧ cvTa.type.looseBVarsBounded 0 = true ∧
      cvTa.type.allLevelParamsDefined sh.cvT.levelParams = true := by
  have har := Ix.Kernel.Model.arRes_sumIndRunJ h
  obtain ⟨cvT, s, -, hlps, hck, -⟩ := h.shape
  obtain ⟨-, -, -, -, hlb, hfv, type, stype, lv, hann, hlp, -, -, -, hcv⟩ := hck.inv
  obtain ⟨hfv', hlb'⟩ := (Ix.Kernel.Model.judgeFrames_rulesJ env).annot_syntax hann hfv hlb
  rw [hlps] at hlp
  rw [hcv]
  exact ⟨by rw [hcv] at har; exact har, hfv', hlb', hlp⟩

/-! ## The link between the stored former and the telescope constant -/

/-- **What the clause asks of the link** between a registered family's stored former and its
telescope constant: it is kept along lookups, and it holds where the two are one constant whose
type is a syntactic telescope into the family's sort. -/
structure LinkLaws (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop where
  mono : ∀ {env env₂ : Ix.Kernel.Env .anon} {fam : NativeFam .anon},
    (∀ {k : Key .anon} {ci : ConstantInfo .anon},
      env.find? k = some ci → env₂.find? k = some ci) →
    L env fam → L env₂ fam
  ofTele : ∀ {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}, fam.cvTa = fam.cvS →
    (∃ bs, fam.cvTa.type.stripPis (fam.p.nP + fam.p.nIdx) = some (bs, .sort fam.p.resSort)) →
    ArRes env fam.cvTa.type → L env fam

/-- The laws hold of the link that says nothing. -/
theorem linkLaws_true : LinkLaws (fun _ _ => True) :=
  ⟨fun _ _ => trivial, fun _ _ _ => trivial⟩

/-! ## A registered family -/

/-- **A registered family as the store `E` and the table `t` read it.** The family is stored;
the stored former has the family's level parameters; the telescope constant is as its stage
checked it (`TeleChecked`) and its type is a syntactic telescope into the family's sort; the
sort's `Prop` flag, the fields' kinds, the distinct constructor names and each constructor's
field count are the family's; the former's key is the key of an address whose record in `E` is
the inductive projection of a member of a block `E` holds, with the family's counts and
constructor keys, the block in Lean's logic; the constructors return literally and no stored
constructor type projects out of the family; and the stored former and the telescope constant
are linked by `L`. -/
structure FamRead (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (fam : NativeFam .anon) : Prop where
  stored : NativeFamStored env fam
  lps : fam.cvS.levelParams = fam.p.cvT.levelParams
  tele : TeleChecked env fam
  sort : ∃ bs, fam.cvTa.type.stripPis (fam.p.nP + fam.p.nIdx) = some (bs, .sort fam.p.resSort)
  isProp : fam.p.isProp = (Ix.Kernel.Level.isEquiv fam.p.resSort .zero == some true)
  kinds : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) fam.p.cvT.name
    fam.p.cvT.levelParams fam.p.nP fam.p.nIdx fam.ctorsA = .ok fam.p.kinds
  nodup : (fam.ctorsA.map (·.1.name)).Nodup
  ctorFields : ∀ (j : Nat) (c cA : ConstantVal .anon × Nat), fam.p.ctors[j]? = some c →
    fam.ctorsA[j]? = some cA → cA.2 = c.2
  record : ∃ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
    fam.p.cvT.name = keyOf t P ∧ Ix.Cert.recordAt E P = some cm ∧ cm.info = .iPrj ip ∧
    Ix.Cert.recordAt E ip.block = some cb ∧ cb.info = .muts ms ∧
    ms[ip.idx.toNat]? = some (.indc ind) ∧
    fam.p.nP = ind.params.toNat ∧ fam.p.nIdx = ind.indices.toNat ∧
    fam.ctorsA.length = ind.ctors.size ∧
    (∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
      cA.1.name = keyOf t (Core.cprjAddr ip.block ip.idx.toNat j)) ∧
    InLogic cb ∧ fam.p.cvT.levelParams = List.range ind.lvls.toNat
  retHead : FamIxonRetHead t E fam
  noProj : BlockFamCtorNoProj fam
  link : L env fam

section Family

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {E : Ixon.Env} {env env₂ : Ix.Kernel.Env .anon} {fam : NativeFam .anon}

/-- **A registered family is read off the store at every extension.** -/
theorem FamRead.ext (hL : LinkLaws L) (h : FamRead L t E env fam)
    (hext : Ix.Kernel.EnvExt env env₂) : FamRead L t E env₂ fam :=
  { h with
    stored := h.stored.ext hext
    tele := h.tele.ext hext.find
    link := hL.mono hext.find h.link }

/-- **A family read with the telescope constant its stored former is read without that
equality**, where the stored constants are well formed and arity-correct, given the two entry
facts. -/
theorem FamRead.of_late (hL : LinkLaws L) (h : LateFamAt t E env fam)
    (hwf : Ix.Kernel.EnvWF env) (hA : StoreArR env) (hrh : FamIxonRetHead t E fam)
    (hnp : BlockFamCtorNoProj fam) : FamRead L t E env fam := by
  have htc : TeleChecked env fam := TeleChecked.of_stored h.stored.former h.tele h.lps hwf hA
  exact
    { stored := h.stored
      lps := h.lps
      tele := htc
      sort := h.sort
      isProp := h.isProp
      kinds := h.kinds
      nodup := h.nodup
      ctorFields := h.ctorFields
      record := h.record
      retHead := hrh
      noProj := hnp
      link := hL.ofTele h.tele h.sort htc.arRes }

/-- **A registered family read off a parent's record**: the family of the parent's name, with
the member the parent's record names, its counts, its constructor count and constructor keys. -/
def FamReadAt (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E : Ixon.Env) (env : Ix.Kernel.Env .anon) (P : _root_.Address) (ip : Ixon.InductiveProj)
    (fam : NativeFam .anon) : Prop :=
  FamRead L t E env fam ∧ fam.p.cvT.name = keyOf t P ∧
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E ip.block = some cb ∧ cb.info = .muts ms ∧
      ms[ip.idx.toNat]? = some (.indc ind) ∧
      fam.p.nP = ind.params.toNat ∧ fam.p.nIdx = ind.indices.toNat ∧
      fam.ctorsA.length = ind.ctors.size ∧
      ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
        cA.1.name = keyOf t (Core.cprjAddr ip.block ip.idx.toNat j)

/-- **A family of a parent's name is read off the parent's record**: keys identify addresses
and the store holds one record at an address. -/
theorem FamRead.readAt (hat : FamRead L t E env fam) (ht : t.check = .ok ())
    {P : _root_.Address} {cm : Ixon.Constant} {ip : Ixon.InductiveProj}
    (hname : fam.p.cvT.name = keyOf t P) (hcm : Ix.Cert.recordAt E P = some cm)
    (hinfo : cm.info = .iPrj ip) : FamReadAt L t E env P ip fam := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨P', cm', ip', cb, ms, ind, hn', hcm', hinfo', hcb, hms, hind, hp, hi, hlen, hctors,
    -, -⟩ := hat.record
  have hPP : P' = P := keyOf_inj hroles (hn'.symm.trans hname)
  rw [hPP, hcm] at hcm'
  have hcc : cm' = cm := (Option.some.inj hcm').symm
  rw [hcc, hinfo] at hinfo'
  have hii : ip' = ip := (Ixon.ConstantInfo.iPrj.inj hinfo').symm
  rw [hii] at hcb hind hctors
  exact ⟨hat, hname, cb, ms, ind, hcb, hms, hind, hp, hi, hlen, hctors⟩

end Family

/-! ## The registry -/

/-- **The registry read off the store, at a given registry**: every registered family is read
off the store; every stored family the circuit treats as native, under no basis name, is
registered; and in every set theory one model keeps every registered family's data. -/
structure FamRegistryWith (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (Reg : NativeFam .anon → Prop) : Prop where
  fams : ∀ fam, Reg fam → FamRead L t E env fam
  complete : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? (keyOf t P) = some (.indInfo cv caps) →
    Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false →
    Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
    ∃ fam, Reg fam ∧ fam.p.cvT.name = keyOf t P
  model : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelN V .verified env Reg

/-- **The registry**: some registry, chosen before the set theory. -/
def FamRegistry (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∃ Reg : NativeFam .anon → Prop, FamRegistryWith.{u} L t E env Reg

section Registry

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {E : Ixon.Env} {env env₂ : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}

/-- **The family the registry holds at a parent the circuit read**, read off the parent's
record. -/
theorem FamRegistryWith.at_parent (h : FamRegistryWith.{u} L t E env Reg)
    (ht : t.check = .ok ()) {P : _root_.Address} {cm : Ixon.Constant}
    {ip : Ixon.InductiveProj} {cv : ConstantVal .anon} {caps : IndCaps .anon}
    (hf : env.find? (keyOf t P) = some (.indInfo cv caps))
    (hres : Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false)
    (hcm : Ix.Cert.recordAt E P = some cm) (hinfo : cm.info = .iPrj ip)
    (hnat : NativeAt E ip.block) : ∃ fam, Reg fam ∧ FamReadAt L t E env P ip fam := by
  obtain ⟨fam, hReg, hname⟩ := h.complete P cm ip cv caps hf hres hcm hinfo hnat
  exact ⟨fam, hReg, (h.fams fam hReg).readAt ht hname hcm hinfo⟩

/-- **A step that extends the model it is given and stores no new family the circuit treats as
native keeps the registry.** -/
theorem FamRegistryWith.step (hL : LinkLaws L) (h : FamRegistryWith.{u} L t E env Reg)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelN V .verified env Reg →
      EnvModelN V .verified env₂ Reg)
    (hext : Ix.Kernel.EnvExt env env₂)
    (hnew : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env₂.find? (keyOf t P) = some (.indInfo cv caps) → env.find? (keyOf t P) = none →
      Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
      Ix.Kernel.reservedBasisNames.contains (keyOf t P) = true) :
    FamRegistryWith.{u} L t E env₂ Reg where
  fams fam hf := (h.fams fam hf).ext hL hext
  complete := by
    intro P cm ip cv caps hf hr hcm hinfo hnat
    cases hold : env.find? (keyOf t P) with
    | none =>
      rw [hnew P cm ip cv caps hf hold hcm hinfo hnat] at hr
      cases hr
    | some ci =>
      have h₂ := hext.find hold
      rw [hf] at h₂
      have hci : ci = .indInfo cv caps := (Option.some.inj h₂).symm
      rw [hci] at hold
      exact h.complete P cm ip cv caps hold hr hcm hinfo hnat
  model V _ := hmodel V (h.model V)

/-- **A step that installs a native family registers it**: the step's model extension registers
the family in every set theory, the family is read off the store at the new environment, and
the only inductive type the step stores new is the family's stored former. -/
theorem FamRegistryWith.install (hL : LinkLaws L) {fam : NativeFam .anon}
    (h : FamRegistryWith.{u} L t E env Reg)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelN V .verified env Reg →
      EnvModelN V .verified env₂ (fun f => Reg f ∨ f = fam))
    (hext : Ix.Kernel.EnvExt env env₂) (hread : FamRead L t E env₂ fam)
    (hnewInd : ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, ∀ cv caps, ci = .indInfo cv caps → cv = fam.cvS) :
    FamRegistryWith.{u} L t E env₂ (fun f => Reg f ∨ f = fam) where
  fams f hf := by
    rcases hf with hf | rfl
    · exact (h.fams f hf).ext hL hext
    · exact hread
  complete := by
    intro P cm ip cv caps hf hr hcm hinfo hnat
    cases hold : env.find? (keyOf t P) with
    | none =>
      obtain ⟨new, henv, hind⟩ := hnewInd
      have hf' := hf
      rw [henv] at hf'
      rcases find?_append_cases new hf' with hm | ho
      · have hcv := hind _ hm cv caps rfl
        have hname : cv.name = keyOf t P := Core.WhnfAux.name_of_find hf
        have hname₂ : fam.cvS.name = fam.p.cvT.name :=
          Core.WhnfAux.name_of_find hread.stored.former
        rw [hcv] at hname
        exact ⟨fam, Or.inr rfl, hname₂.symm.trans hname⟩
      · rw [hold] at ho
        cases ho
    | some ci =>
      have h₂ := hext.find hold
      rw [hf] at h₂
      have hci : ci = .indInfo cv caps := (Option.some.inj h₂).symm
      rw [hci] at hold
      obtain ⟨f, hRf, hname⟩ := h.complete P cm ip cv caps hold hr hcm hinfo hnat
      exact ⟨f, Or.inl hRf, hname⟩
  model V _ := hmodel V (h.model V)

/-- **The empty registry**, where the environment has a model in every set theory and every
stored family has a basis name. -/
theorem famRegistryWith_of_noFamily
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelT V .verified env)
    (hres : ∀ (k : Key .anon) (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env.find? k = some (.indInfo cv caps) → Ix.Kernel.reservedBasisNames.contains k = true) :
    FamRegistryWith.{u} L t E env (fun _ => False) := by
  refine ⟨fun _ h => h.elim, ?_, ?_⟩
  · intro P cm ip cv caps hf hr _ _ _
    rw [hres _ _ _ hf] at hr
    cases hr
  · intro V _
    obtain ⟨⟨mp, hT⟩, hE⟩ := hmodel V
    exact ⟨⟨mp, hT, fun _ h => h.elim⟩, hE⟩

end Registry

/-- **The empty registry at the environment of the pins**, for every table and every store. -/
theorem famRegistryWith_basis (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    FamRegistryWith.{u} L t E IxVM.Refinement.TableInhabit.basisEnv (fun _ => False) :=
  famRegistryWith_of_noFamily (fun V _ => ((basisEnv_decl V).toFoldInv).model)
    (fun _ _ _ hf => basisEnv_find_ind_reserved hf)

/-! ## The clause -/

/-- **The clause a declaration fold carries, at a given registry.** `E` is the record store the
steps run against, `lim` the limit of the role context. -/
structure FoldClauseWith (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (lim : Option Nat) (env : Ix.Kernel.Env .anon)
    (Reg : NativeFam .anon → Prop) : Prop where
  /-- IxC: in every set theory, one model keeps every registered family's data. -/
  model : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelN V .verified env Reg
  /-- IxC: the store invariant. -/
  store : Ix.Kernel.Open.StoreInv env
  /-- IxC: the stored recursors' shape facts. -/
  recShape : Ix.Kernel.Model.RecShape env
  /-- IxC: the stored recursors' K facts. -/
  recK : Ix.Kernel.Model.RecK env
  /-- IxC: the stored theorems are typed. -/
  thmTyped : Ix.Kernel.Model.ThmTyped env
  /-- IxC: the η families' tables. -/
  etaTowers : Ix.Kernel.Model.EtaTowers env
  /-- IxC: a stored theorem's value mentions only its own level parameters. -/
  thmLevels : Ix.Kernel.ThmLevels env
  /-- IxC: the stored terms are arity-correct and resolve. -/
  storeArR : StoreArR env
  /-- IxC's `TableBodies`, with the constructor keys of the projection tables of kept
  structures. -/
  strong : Decl.StrongEnvProps env
  /-- Every registered family is read off the store. -/
  fams : ∀ fam, Reg fam → FamRead L t E env fam
  /-- Every stored family the circuit treats as native, under no basis name, is registered. -/
  complete : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? (keyOf t P) = some (.indInfo cv caps) →
    Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false →
    Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
    ∃ fam, Reg fam ∧ fam.p.cvT.name = keyOf t P
  /-- A stored key that is the key of an address is the key of an address of 32 bytes. -/
  hashKeyed : HashKeyed t env
  /-- Every stored key has its root stored. -/
  auxRoot : Decl.AuxRootSynced env
  /-- Every η-capable family's constructor is stored. -/
  etaCtorStored : Decl.EtaCtorStored env
  /-- The shape of every stored η-capable family and its constructor. -/
  etaShape : Decl.EtaShape env
  /-- η typing of the stored η-capable families holds in every extension. -/
  etaStable : Decl.EtaStable env
  /-- The unresolved key is not stored. -/
  unresolved : env.find? Core.unresolvedKey = none
  /-- The role table is well formed. -/
  tableWf : t.wf = true
  /-- The role and record companions of the scoped core's environment facts, at the limit. -/
  companions : Decl.CoreCompanions ⟨E, env, t, lim⟩
  /-- The scoped load contract at the prefix context. -/
  loads : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env, t, lim⟩)

/-- **The clause a declaration fold carries**: some registry, chosen before the set theory. -/
def FoldClause (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E : Ixon.Env) (lim : Option Nat) (env : Ix.Kernel.Env .anon) : Prop :=
  ∃ Reg : NativeFam .anon → Prop, FoldClauseWith.{u} L t E lim env Reg

/-- **The part of the clause beside the prefix invariant**, in the shape a unit step takes its
extra clause: the registry, the store keys, the roots and the level clauses. -/
abbrev FoldExtra (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ((FamRegistry.{u} L t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧ LvClauses env

section Clause

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {E : Ixon.Env} {lim : Option Nat} {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}

/-- The store facts of the clause, as the declaration layer bundles them. -/
theorem FoldClauseWith.foldStore (h : FoldClauseWith.{u} L t E lim env Reg) :
    Decl.FoldStoreInv env :=
  { store := h.store
    thmTyped := h.thmTyped
    recK := h.recK
    etaTowers := h.etaTowers
    strongProps := h.strong
    recShape := h.recShape
    etaCtorStored := h.etaCtorStored
    etaShape := h.etaShape }

/-- **The clause gives the prefix invariant.** Its model in each set theory is the clause's
(`EnvModelN.toT`); nothing else is read. -/
theorem FoldClauseWith.prefixInv (h : FoldClauseWith.{u} L t E lim env Reg) :
    Decl.PrefixInv.{u} E t lim env :=
  { decl := fun V _ =>
      Decl.FullDeclInv.ofFoldInv ⟨Ix.Kernel.Model.EnvModelN.toT V (h.model V), h.foldStore⟩
        h.auxRoot
    store := h.foldStore
    unresolved := h.unresolved
    tableWf := h.tableWf
    companions := h.companions
    loads := h.loads
    etaStable := h.etaStable }

/-- The registry of the clause. -/
theorem FoldClauseWith.registry (h : FoldClauseWith.{u} L t E lim env Reg) :
    FamRegistryWith.{u} L t E env Reg :=
  ⟨h.fams, h.complete, h.model⟩

/-- The part of the clause beside the prefix invariant. -/
theorem FoldClauseWith.extra (h : FoldClauseWith.{u} L t E lim env Reg) :
    FoldExtra.{u} L t E env :=
  ⟨⟨⟨⟨Reg, h.registry⟩, h.hashKeyed⟩, h.auxRoot⟩, h.thmLevels, h.storeArR⟩

/-- **The clause from the prefix invariant and the part beside it.** The prefix invariant's own
model is not read. -/
theorem FoldClauseWith.of_prefix (hinv : Decl.PrefixInv.{u} E t lim env)
    (hR : FamRegistryWith.{u} L t E env Reg) (hkeys : HashKeyed t env)
    (haux : Decl.AuxRootSynced env) (hlv : LvClauses env) :
    FoldClauseWith.{u} L t E lim env Reg :=
  { model := hR.model
    store := hinv.store.store
    recShape := hinv.store.recShape
    recK := hinv.store.recK
    thmTyped := hinv.store.thmTyped
    etaTowers := hinv.store.etaTowers
    thmLevels := hlv.1
    storeArR := hlv.2
    strong := hinv.store.strongProps
    fams := hR.fams
    complete := hR.complete
    hashKeyed := hkeys
    auxRoot := haux
    etaCtorStored := hinv.store.etaCtorStored
    etaShape := hinv.store.etaShape
    etaStable := hinv.etaStable
    unresolved := hinv.unresolved
    tableWf := hinv.tableWf
    companions := hinv.companions
    loads := hinv.loads }

/-- **The clause is the prefix invariant together with the part beside it.** -/
theorem foldClause_iff :
    FoldClause.{u} L t E lim env ↔ Decl.PrefixInv.{u} E t lim env ∧ FoldExtra.{u} L t E env := by
  constructor
  · rintro ⟨Reg, h⟩
    exact ⟨h.prefixInv, h.extra⟩
  · rintro ⟨hinv, ⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩
    exact ⟨Reg, FoldClauseWith.of_prefix hinv hR hkeys haux hlv⟩

end Clause

/-! ## From the clause with the telescope equality -/

/-- **The clause with the telescope equality gives the part beside the prefix invariant**,
where the stored constants are well formed: every registered family is read without the
equality (`FamRead.of_late`). -/
theorem foldExtra_of_nativeBlockXR {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hwf : Ix.Kernel.EnvWF env) (h : NativeBlockXR.{u} t E env) : FoldExtra.{u} L t E env := by
  obtain ⟨⟨⟨⟨Reg, hR, hH⟩, hkeys⟩, haux⟩, hlv⟩ := h
  exact ⟨⟨⟨⟨Reg, fun fam hf =>
    FamRead.of_late hL (hR.fams fam hf) hwf hlv.2 (hH fam hf).1 (hH fam hf).2,
    hR.complete, hR.model⟩, hkeys⟩, haux⟩, hlv⟩

/-- **The clause with the telescope equality has no inhabitant at an environment that stores a
former declared at a definition.** At a stored former under no basis name, whose record is an
inductive projection of a block the circuit treats as native, and whose stored type is not a
syntactic telescope into a sort at the member's parameter and index counts, the registry's
completeness names a family read with the telescope constant its stored former, whose type
would be such a telescope. -/
theorem not_nativeBlockXR_of_aliasFormer {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (ht : t.check = .ok ()) {P : _root_.Address}
    {cm : Ixon.Constant} {ip : Ixon.InductiveProj} {cv : ConstantVal .anon}
    {caps : IndCaps .anon} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive}
    (hf : env.find? (keyOf t P) = some (.indInfo cv caps))
    (hres : Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false)
    (hcm : Ix.Cert.recordAt E P = some cm) (hinfo : cm.info = .iPrj ip)
    (hnat : NativeAt E ip.block)
    (hcb : Ix.Cert.recordAt E ip.block = some cb) (hms : cb.info = .muts ms)
    (hind : ms[ip.idx.toNat]? = some (.indc ind))
    (halias : ∀ bs s,
      cv.type.stripPis (ind.params.toNat + ind.indices.toNat) ≠ some (bs, .sort s)) :
    ¬ NativeBlockXR.{u} t E env := by
  rintro ⟨⟨⟨⟨Reg, hR, -⟩, -⟩, -⟩, -⟩
  obtain ⟨fam, -, hat, hname, cb', ms', ind', hcb', hms', hind', hp, hi, -, -⟩ :=
    hR.at_parent ht hf hres hcm hinfo hnat
  have hcbe : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
  rw [hcbe] at hms'
  have hmse : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  rw [hmse] at hind'
  have hinde : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj (hind'.symm.trans hind))
  rw [hinde] at hp hi
  have hformer := hat.stored.former
  rw [hname, hf] at hformer
  have hcv : cv = fam.cvS := (Ix.Kernel.ConstantInfo.indInfo.inj (Option.some.inj hformer)).1
  obtain ⟨bs, hs⟩ := hat.sort
  rw [hat.tele, ← hcv, hp, hi] at hs
  exact halias bs _ hs

/-- **A type that is one binder over an application is no telescope into a sort at two or more
binders.** The declared type of `inductive R (α : Type) : Rel α`, with
`Rel α := α → α → Prop`, has this shape at the family's three binders. -/
theorem stripPis_binder_app_ne {dom f a : Ix.Kernel.Expr .anon} {bm : Ix.Kernel.BinderMeta}
    (n : Nat) (bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)) (s : Ix.Kernel.Level) :
    (Ix.Kernel.Expr.forallE dom (.app f a) bm).stripPis (n + 2) ≠ some (bs, .sort s) := by
  intro h
  simp [Ix.Kernel.Expr.stripPis] at h

end IxVM.Refinement.Typing
