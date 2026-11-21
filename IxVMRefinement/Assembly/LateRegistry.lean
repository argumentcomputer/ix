import IxVMRefinement.Assembly.TypingBasisInv
import IxVMRefinement.Assembly.TypingDefnStep
import IxC.Kernel.Model.FoldLate
import IxC.Kernel.Semantics.Inductives.DeclNativeRecLateExtJ

/-! # The native families registered so far

A recursor for an ordinary inductive family is installed at its own record, after the family
(`Ix.Kernel.Semantics.DeclNativeRecLateRunJ`). IxC's model step for it
(`Ix.Kernel.Model.EnvModelN.late`) needs the family's data kept at the model the fold carries
(`NativeFamOk`), so the fold keeps a ghost set of family summaries, the registry, and one model
that keeps the data of every registered family (`EnvModelN`).

`LateRegistry t E env` is that clause of the refinement's fold, at the role table `t` and the
record store `E` the steps run against: there is a registry `Reg`, chosen before the set
theory, such that

* every registered family is stored and is read off the store as the circuit reads it
  (`LateFamAt`): the former at the key of a projection address whose record in `E` is an
  inductive projection of a block in Lean's logic, the constructors at the keys of that
  member's constructor projection addresses, as many as the member has, each with its declared
  field count; the telescope constant is the stored former; and the family's counts, sort,
  kinds and level parameters (the positions below the member's level count);
* every stored family the circuit treats as native is registered (`complete`): at a stored
  former whose key is no basis name, whose record in `E` is an inductive projection, and whose
  block a good run of `KernelModeled::block_is_modeled` answered `0` for;
* in every set theory, `EnvModelN` holds with `Reg`.

The clause is relative to the store, as the prefix invariant is: what a registered summary is
can only be read against the records a run reads (the store records no constructor list, and
the projection address of a member does not determine the member without its record).

Proved here:

* `lateRegistry_of_noFamily`, `lateRegistry_basis`: the clause with the empty registry where
  every stored family has a basis name, in particular at the environment of the pins;
* `LateRegistryWith.step`, `.declRunJ`, `LateRegistry.cons_declRunJ`: a step that extends the
  model it is given and stores no new family the circuit treats as native keeps the registry;
  every declaration step over the derivation package does (`EnvModelN.declRunJ`);
* `LateRegistryWith.register`: what a step that installs a native family must conclude to add
  it (the interface for the inductive block's step);
* `KeepsValuesJ`, `keepsValuesJ_lateRegistry`: the clause is kept by storing a value constant
  along its declaration step. It is not kept by storing a value constant alone (`KeepsValues`):
  the clause says the environment has a model, and an axiom of an empty type has none.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key)
open Ix.Kernel.Semantics (NativeFam NativeFamStored DeclRunJ IndRoutesJ)
open Ix.Kernel.Model (rulesJ EnvModelN EnvModelT)
open IxVM.Refinement.TableInhabit (basisEnv)

/-! ## The clause -/

/-- **A good run of `KernelModeled::block_is_modeled` at `b` answered `0`**: the circuit treats
the block at `b` as one ordinary inductive family. The run is bounded and hashes no collision
with the store `E`. -/
def NativeAt (E : Ixon.Env) (b : _root_.Address) : Prop :=
  ∃ (bq : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (bb : Bytes.Address),
    ObsFn Core.W "KernelModeled::block_is_modeled" [bq] h (.field 0) h' cs ∧
    ¬ View.HashedCollision { env := E } [] cs ∧ Bounded cs ∧
    Bytes.RepAddressRef Core.addrTy h bb bq ∧ Core.ixAddr bb = b

/-- **A registered family as the store `E` and the table `t` read it.** The family is stored
(`NativeFamStored`); the telescope constant is the stored former; the former's level
parameters, its telescope into the family's sort, the sort's `Prop` flag and the fields' kinds
are the family's; the constructors' names are distinct; each stored constructor has its
declared constructor's field count (`ctorFields`); and the former's key is the key of an address
`P` whose record in `E` is the inductive projection of member `i` of a block `B` that `E` holds,
with the family's parameter and index counts, as many constructors as the family, constructor
`j` at the key of the constructor projection address `(B, i, j)`, the block in Lean's logic, and
the family's level parameters the positions below the member's level count. -/
structure LateFamAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (fam : NativeFam .anon) : Prop where
  stored : NativeFamStored env fam
  tele : fam.cvTa = fam.cvS
  lps : fam.cvS.levelParams = fam.p.cvT.levelParams
  sort : ∃ bs, fam.cvTa.type.stripPis (fam.p.nP + fam.p.nIdx) = some (bs, .sort fam.p.resSort)
  isProp : fam.p.isProp = (Ix.Kernel.Level.isEquiv fam.p.resSort .zero == some true)
  kinds : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) fam.p.cvT.name
    fam.p.cvT.levelParams fam.p.nP fam.p.nIdx fam.ctorsA = .ok fam.p.kinds
  nodup : (fam.ctorsA.map (·.1.name)).Nodup
  /-- Each stored constructor has its declared constructor's field count. -/
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

/-- **The registry clause at a given registry** (module docstring). -/
structure LateRegistryWith (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon)
    (Reg : NativeFam .anon → Prop) : Prop where
  /-- Every registered family is read off the store as the circuit reads it. -/
  fams : ∀ fam, Reg fam → LateFamAt t E env fam
  /-- Every stored family the circuit treats as native, under no basis name, is registered. -/
  complete : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? (keyOf t P) = some (.indInfo cv caps) →
    Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false →
    Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
    ∃ fam, Reg fam ∧ fam.p.cvT.name = keyOf t P
  /-- In every set theory, one model keeps every registered family's data. -/
  model : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelN V .verified env Reg

/-- **The registry clause**: some registry, chosen before the set theory. -/
def LateRegistry (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∃ Reg : NativeFam .anon → Prop, LateRegistryWith.{u} t E env Reg

/-- The clause forgets to the model invariant the declaration layer carries. -/
theorem LateRegistryWith.envModelT {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    (h : LateRegistryWith.{u} t E env Reg) (V : Type u) [Ix.Kernel.SetTheory V] :
    EnvModelT V .verified env :=
  Ix.Kernel.Model.EnvModelN.toT V (h.model V)

/-! ## A family along an extension -/

/-- **A registered family is read off the store at every extension**: its lookups are kept,
and the rest speaks of the summary and of `E`. -/
theorem LateFamAt.ext {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {fam : NativeFam .anon} (h : LateFamAt t E env fam)
    (hext : Ix.Kernel.EnvExt env env₂) : LateFamAt t E env₂ fam :=
  { h with stored := h.stored.ext hext }

/-! ## The start -/

/-- **The empty registry**, where the environment has a model in every set theory and every
stored family has a basis name. -/
theorem lateRegistry_of_noFamily {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon}
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelT V .verified env)
    (hres : ∀ (k : Key .anon) (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env.find? k = some (.indInfo cv caps) → Ix.Kernel.reservedBasisNames.contains k = true) :
    LateRegistry.{u} t E env := by
  refine ⟨fun _ => False, fun _ h => h.elim, ?_, ?_⟩
  · intro P cm ip cv caps hf hr _ _ _
    rw [hres _ _ _ hf] at hr
    cases hr
  · intro V _
    obtain ⟨⟨mp, hT⟩, hE⟩ := hmodel V
    exact ⟨⟨mp, hT, fun _ h => h.elim⟩, hE⟩

/-- Every family stored at the environment of the pins has a basis name (decided). -/
theorem basisEnv_ind_reserved :
    basisEnv.consts.all (fun ci => match ci with
      | .indInfo cv _ => Ix.Kernel.reservedBasisNames.contains cv.name
      | _ => true) = true := by
  decide +kernel

theorem basisEnv_find_ind_reserved {k : Key .anon} {cv : ConstantVal .anon}
    {caps : IndCaps .anon} (h : basisEnv.find? k = some (.indInfo cv caps)) :
    Ix.Kernel.reservedBasisNames.contains k = true := by
  obtain ⟨hmem, hname⟩ := basisEnv_find_mem h
  have hall := List.all_eq_true.mp basisEnv_ind_reserved _ hmem
  have hcv : Ix.Kernel.reservedBasisNames.contains cv.name = true := hall
  have hk : cv.name = k := hname
  rw [← hk]
  exact hcv

/-- **The registry clause at the environment of the pins**, with the empty registry, for every
table and every store. -/
theorem lateRegistry_basis (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    LateRegistry.{u} t E basisEnv :=
  lateRegistry_of_noFamily (fun V _ => ((basisEnv_decl V).toFoldInv).model)
    (fun _ _ _ hf => basisEnv_find_ind_reserved hf)

/-! ## Steps -/

/-- **A step that extends the model it is given and stores no new family the circuit treats as
native keeps the registry.** A family stored new must have a basis name (`hnew`); every value
constant, recursor and projection table stores none. -/
theorem LateRegistryWith.step {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    (h : LateRegistryWith.{u} t E env Reg)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelN V .verified env Reg →
      EnvModelN V .verified env₂ Reg)
    (hext : Ix.Kernel.EnvExt env env₂)
    (hnew : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env₂.find? (keyOf t P) = some (.indInfo cv caps) → env.find? (keyOf t P) = none →
      Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
      Ix.Kernel.reservedBasisNames.contains (keyOf t P) = true) :
    LateRegistryWith.{u} t E env₂ Reg where
  fams fam hf := (h.fams fam hf).ext hext
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

/-- **A step that registers a family** (what an inductive block's step concludes to add one).
Given the registry at `env`: the step's model extension registers `fam` in every set theory
(`hmodel`, IxC's `EnvModelN.nativeCore` for a native install); the step extends the
environment; `fam` is read off the store at the new environment (`hat`); and the only family
the circuit treats as native that the step stores new, under no basis name, is `fam`'s
(`hnew`). -/
theorem LateRegistryWith.register {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop} {fam : NativeFam .anon}
    (h : LateRegistryWith.{u} t E env Reg)
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelN V .verified env Reg →
      EnvModelN V .verified env₂ (fun f => Reg f ∨ f = fam))
    (hext : Ix.Kernel.EnvExt env env₂) (hat : LateFamAt t E env₂ fam)
    (hnew : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env₂.find? (keyOf t P) = some (.indInfo cv caps) → env.find? (keyOf t P) = none →
      Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
      Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false →
      keyOf t P = fam.p.cvT.name) :
    LateRegistryWith.{u} t E env₂ (fun f => Reg f ∨ f = fam) where
  fams f hf := by
    rcases hf with hf | rfl
    · exact (h.fams f hf).ext hext
    · exact hat
  complete := by
    intro P cm ip cv caps hf hr hcm hinfo hnat
    cases hold : env.find? (keyOf t P) with
    | none =>
      exact ⟨fam, Or.inr rfl, (hnew P cm ip cv caps hf hold hcm hinfo hnat hr).symm⟩
    | some ci =>
      have h₂ := hext.find hold
      rw [hf] at h₂
      have hci : ci = .indInfo cv caps := (Option.some.inj h₂).symm
      rw [hci] at hold
      obtain ⟨f, hRf, hname⟩ := h.complete P cm ip cv caps hold hr hcm hinfo hnat
      exact ⟨f, Or.inl hRf, hname⟩
  model V _ := hmodel V (h.model V)

/-- **Every declaration step over the derivation package keeps the registry**, when it stores
no new family the circuit treats as native (IxC's `EnvModelN.declRunJ`). -/
theorem LateRegistryWith.declRunJ {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    {d : Ix.Kernel.Declaration .anon} (h : LateRegistryWith.{u} t E env Reg)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂)
    (hext : Ix.Kernel.EnvExt env env₂)
    (hnew : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env₂.find? (keyOf t P) = some (.indInfo cv caps) → env.find? (keyOf t P) = none →
      Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
      Ix.Kernel.reservedBasisNames.contains (keyOf t P) = true) :
    LateRegistryWith.{u} t E env₂ Reg :=
  h.step (fun V _ hm => Ix.Kernel.Model.EnvModelN.declRunJ V hm hd) hext hnew

/-- A constant stored in front that is no inductive type stores no new family. -/
theorem find_ind_cons_old {env : Ix.Kernel.Env .anon} {ci : ConstantInfo .anon}
    (hind : ∀ cv caps, ci ≠ .indInfo cv caps) {k : Key .anon} {cv : ConstantVal .anon}
    {caps : IndCaps .anon}
    (hf : (⟨ci :: env.consts⟩ : Ix.Kernel.Env .anon).find? k = some (.indInfo cv caps)) :
    env.find? k = some (.indInfo cv caps) := by
  rw [Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · exact absurd (Option.some.inj hf) (hind cv caps)
  · exact hf

/-- **A declaration step that stores one constant that is no inductive type keeps the
registry.** -/
theorem LateRegistry.cons_declRunJ {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {ci : ConstantInfo .anon} {d : Ix.Kernel.Declaration .anon}
    (h : LateRegistry.{u} t E env)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d ⟨ci :: env.consts⟩)
    (hfresh : env.find? ci.name = none)
    (hnt : ∀ T : Key .anon, ci.name ≠ Ix.Kernel.projTableName T)
    (hind : ∀ cv caps, ci ≠ .indInfo cv caps) :
    LateRegistry.{u} t E ⟨ci :: env.consts⟩ := by
  obtain ⟨Reg, hR⟩ := h
  refine ⟨Reg, hR.declRunJ hd (Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)) ?_⟩
  intro P cm ip cv caps hf hold
  rw [find_ind_cons_old hind hf] at hold
  cases hold

/-! ## Value constants -/

/-- **The extra clause is kept by storing a definition, a theorem or an axiom at a fresh key
along its declaration step.** The typed form of `KeepsValues`: the step also hands the
declaration step over the derivation package that installs the constant. -/
def KeepsValuesJ (X : Ix.Kernel.Env .anon → Prop) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (ci : ConstantInfo .anon) (d : Ix.Kernel.Declaration .anon),
    X env → env.find? ci.name = none → IsValueConst ci →
    (∀ T : Key .anon, ci.name ≠ Ix.Kernel.projTableName T) →
    DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d ⟨ci :: env.consts⟩ → X ⟨ci :: env.consts⟩

theorem KeepsValues.toJ {X : Ix.Kernel.Env .anon → Prop} (h : KeepsValues X) :
    KeepsValuesJ X :=
  fun env ci _ hX hfresh hval _ _ => h env ci hX hfresh hval

theorem KeepsValuesJ.and {X Y : Ix.Kernel.Env .anon → Prop} (hX : KeepsValuesJ X)
    (hY : KeepsValuesJ Y) : KeepsValuesJ (fun env => X env ∧ Y env) :=
  fun env ci d h hfresh hval hnt hd =>
    ⟨hX env ci d h.1 hfresh hval hnt hd, hY env ci d h.2 hfresh hval hnt hd⟩

theorem IsValueConst.not_ind {ci : ConstantInfo .anon} (h : IsValueConst ci) :
    ∀ cv caps, ci ≠ .indInfo cv caps := by
  intro cv caps he
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> (rw [h] at he; cases he)

/-- **The registry is kept by a value constant along its declaration step.** -/
theorem keepsValuesJ_lateRegistry (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    KeepsValuesJ (LateRegistry.{u} t E) :=
  fun _ _ _ h hfresh hval hnt hd => h.cons_declRunJ hd hfresh hnt hval.not_ind

end IxVM.Refinement.Typing
