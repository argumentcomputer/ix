import IxVMRefinement.Assembly.NativeBlockRetHeadIxon
import IxVMRefinement.Assembly.NativeBlockNoProj
import IxVMRefinement.Assembly.NativeBlockRegister
import IxVMRefinement.Assembly.TypingRecLate
import IxVMRefinement.Assembly.LateValueStep

/-! # The registry with the literal return of every registered family's constructors

A recursor's late step compares the recursor against its family's constructors, and reads that
each constructor's type returns literally: at the member record the family's name is the key of,
every constructor's type is, through the block record's sharing table, the parameters and fields
as literal binders and then an application spine over a reference (`FamIxonRetHead`). The
recursor's own run does not check this; the native block's step does, on its own loads
(`famIxonRetHead_of_member`). The comparison also reads that no stored constructor type
projects out of the family (`BlockFamCtorNoProj`), which the block's constructor stage gives. So
the fold carries both (`LateEntryFacts`) for every registered family, beside the registry:

* `RetHeadRegistry t E env`: some registry, chosen before the set theory, with the registry
  clause (`LateRegistryWith`) and `LateEntryFacts` for each of its families. The facts speak of
  the store and the family only, so a step that keeps the registry's families keeps them.
  `RetHeadRegistry.lateRegistry` forgets them; `RetHeadRegistry.entry_of_matched` gives them for
  every family the late step matches at a parent (`MatchedAt`, `RecParent`).

Kept by every step that keeps the registry:

* `retHeadRegistry_of_noFamily`, `retHeadRegistry_basis`: the empty registry;
* `RetHeadRegistry.step`, `.declRunJ`, `.cons_declRunJ`, `keepsValuesJ_retHeadRegistry`,
  `keepsValuesKeyed_retHeadKeyed`: a step that stores no new family the circuit treats as
  native, every value step;
* `RetHeadRegistry.nativeNoRec`: a native block's install, which registers its family, given
  the family's two facts;
* `late_prefixInv_step_rh`, `unitStep_recLate_rh`: the late recursor's step, whose registry is
  the one it was handed; the step's second interface receives the family's two facts.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps Key RecRule)
open Ix.Kernel.Semantics (NativeFam DeclRunJ IndRoutesJ DeclNativeRecLateRunJ)
open Ix.Kernel.Model (rulesJ EnvModelN EnvModelT)
open IxVM.Refinement.TableInhabit (basisEnv)

/-! ## The clause -/

/-- **The registry entry's facts the late recursor step reads and its run does not check**: the
constructors return literally (`FamIxonRetHead`) and no stored constructor type projects out of
the family (`BlockFamCtorNoProj`). -/
def LateEntryFacts (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (fam : NativeFam .anon) : Prop :=
  FamIxonRetHead t E fam ∧ BlockFamCtorNoProj fam

/-- **The registry clause with the literal return of every registered family's constructors**
(module docstring). -/
def RetHeadRegistry (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  ∃ Reg : NativeFam .anon → Prop, LateRegistryWith.{u} t E env Reg ∧
    ∀ fam, Reg fam → LateEntryFacts t E fam

/-- The clause forgets to the registry clause. -/
theorem RetHeadRegistry.lateRegistry {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (h : RetHeadRegistry.{u} t E env) : LateRegistry.{u} t E env :=
  let ⟨Reg, hR, _⟩ := h
  ⟨Reg, hR⟩

/-- **The family the registry holds at a parent the circuit read has the entry's facts**
(`LateRegistryWith.at_parent` with the carried facts). -/
theorem RetHeadRegistry.at_parent {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (h : RetHeadRegistry.{u} t E env) (ht : t.check = .ok ())
    {P : _root_.Address} {cm : Ixon.Constant} {ip : Ixon.InductiveProj}
    {cv : ConstantVal .anon} {caps : IndCaps .anon}
    (hf : env.find? (keyOf t P) = some (.indInfo cv caps))
    (hres : Ix.Kernel.reservedBasisNames.contains (keyOf t P) = false)
    (hcm : Ix.Cert.recordAt E P = some cm) (hinfo : cm.info = .iPrj ip)
    (hnat : NativeAt E ip.block) :
    ∃ fam, MatchedAt t E env P ip fam ∧ LateEntryFacts t E fam := by
  obtain ⟨Reg, hR, hH⟩ := h
  obtain ⟨fam, hReg, hat, hname, hm⟩ := hR.at_parent ht hf hres hcm hinfo hnat
  exact ⟨fam, ⟨hat, hname, hm⟩, hH fam hReg⟩

/-- **The entry's facts pass between two families read off the same parent record**: their
names are the parent's key (`FamIxonRetHead` reads only the name) and their constructors are
the constants stored at the same keys (`BlockFamCtorNoProj` reads their types). -/
theorem lateEntryFacts_of_matched {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {P : _root_.Address} {ip : Ixon.InductiveProj}
    {fam fam' : NativeFam .anon} (hm : MatchedAt t E env P ip fam)
    (hm' : MatchedAt t E env P ip fam') (h' : LateEntryFacts t E fam') :
    LateEntryFacts t E fam := by
  obtain ⟨hat, hname, cb, ms, ind, hcb, hms, hind, -, -, hlen, hct⟩ := hm
  obtain ⟨hat', hname', cb', ms', ind', hcb', hms', hind', -, -, hlen', hct'⟩ := hm'
  have hcbe : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
  subst hcbe
  have hmse : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  subst hmse
  have hinde : ind' = ind := by
    have h := hind'.symm.trans hind
    injection h with h
    injection h
  subst hinde
  have hnn : fam.p.cvT.name = fam'.p.cvT.name := hname.trans hname'.symm
  refine ⟨?_, ?_⟩
  · intro P₁ cm₁ ip₁ cb₁ ms₁ ind₁ hn₁ hP₁ hcm₁ hb₁ hms₁ hm₁
    exact h'.1 P₁ cm₁ ip₁ cb₁ ms₁ ind₁ (hnn.symm.trans hn₁) hP₁ hcm₁ hb₁ hms₁ hm₁
  · intro j cA hcA
    have hj : j < fam'.ctorsA.length := by
      rw [hlen', ← hlen]
      exact (List.getElem?_eq_some_iff.mp hcA).1
    obtain ⟨cA', hcA'⟩ : ∃ cA', fam'.ctorsA[j]? = some cA' :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    have hk : cA.1.name = cA'.1.name := (hct j cA hcA).trans (hct' j cA' hcA').symm
    have hf := (hat.stored.ctor j cA hcA).1
    have hf' := (hat'.stored.ctor j cA' hcA').1
    rw [hk, hf'] at hf
    have he : cA'.1 = cA.1 := by
      injection hf with h
      injection h
    rw [hnn, ← he]
    exact h'.2 j cA' hcA'

/-- **The entry's facts for every family the late step matches at its parent**: the registry
holds a family read off the parent (`at_parent`, from `RecParent`), whose facts pass to the
matched family (`lateEntryFacts_of_matched`). The late step's two named entry hypotheses, at the
step's environment, from the clause there. -/
theorem RetHeadRegistry.entry_of_matched {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} (h : RetHeadRegistry.{u} t E env) (ht : t.check = .ok ())
    {P : _root_.Address} {ip : Ixon.InductiveProj} {fam : NativeFam .anon}
    (hpar : RecParent t E env P ip) (hm : MatchedAt t E env P ip fam) :
    FamIxonRetHead t E fam ∧ BlockFamCtorNoProj fam := by
  obtain ⟨⟨cv, caps, hf⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam', hm', hE'⟩ := h.at_parent ht hf hres hcm hcmi hnat
  exact lateEntryFacts_of_matched hm hm' hE'

/-! ## The start -/

/-- **The empty registry**, where the environment has a model in every set theory and every
stored family has a basis name. -/
theorem retHeadRegistry_of_noFamily {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon}
    (hmodel : ∀ (V : Type u) [Ix.Kernel.SetTheory V], EnvModelT V .verified env)
    (hres : ∀ (k : Key .anon) (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env.find? k = some (.indInfo cv caps) → Ix.Kernel.reservedBasisNames.contains k = true) :
    RetHeadRegistry.{u} t E env := by
  refine ⟨fun _ => False, ⟨fun _ h => h.elim, ?_, ?_⟩, fun _ h => h.elim⟩
  · intro P cm ip cv caps hf hr _ _ _
    rw [hres _ _ _ hf] at hr
    cases hr
  · intro V _
    obtain ⟨⟨mp, hT⟩, hE⟩ := hmodel V
    exact ⟨⟨mp, hT, fun _ h => h.elim⟩, hE⟩

/-- **The clause at the environment of the pins**, with the empty registry, for every table and
every store. -/
theorem retHeadRegistry_basis (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    RetHeadRegistry.{u} t E basisEnv :=
  retHeadRegistry_of_noFamily (fun V _ => ((basisEnv_decl V).toFoldInv).model)
    (fun _ _ _ hf => basisEnv_find_ind_reserved hf)

/-! ## Steps that keep the registry's families -/

/-- **A step that extends every model it is given and stores no new family the circuit treats
as native keeps the clause** (`LateRegistryWith.step`, the families and their facts unchanged). -/
theorem RetHeadRegistry.step {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} (h : RetHeadRegistry.{u} t E env)
    (hmodel : ∀ (Reg : NativeFam .anon → Prop) (V : Type u) [Ix.Kernel.SetTheory V],
      EnvModelN V .verified env Reg → EnvModelN V .verified env₂ Reg)
    (hext : Ix.Kernel.EnvExt env env₂)
    (hnew : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env₂.find? (keyOf t P) = some (.indInfo cv caps) → env.find? (keyOf t P) = none →
      Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
      Ix.Kernel.reservedBasisNames.contains (keyOf t P) = true) :
    RetHeadRegistry.{u} t E env₂ :=
  let ⟨Reg, hR, hH⟩ := h
  ⟨Reg, hR.step (hmodel Reg) hext hnew, hH⟩

/-- **Every declaration step over the derivation package keeps the clause**, when it stores no
new family the circuit treats as native. -/
theorem RetHeadRegistry.declRunJ {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {d : Ix.Kernel.Declaration .anon}
    (h : RetHeadRegistry.{u} t E env)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂)
    (hext : Ix.Kernel.EnvExt env env₂)
    (hnew : ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (cv : ConstantVal .anon) (caps : IndCaps .anon),
      env₂.find? (keyOf t P) = some (.indInfo cv caps) → env.find? (keyOf t P) = none →
      Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip → NativeAt E ip.block →
      Ix.Kernel.reservedBasisNames.contains (keyOf t P) = true) :
    RetHeadRegistry.{u} t E env₂ :=
  let ⟨Reg, hR, hH⟩ := h
  ⟨Reg, hR.declRunJ hd hext hnew, hH⟩

/-- **A declaration step that stores one constant that is no inductive type keeps the
clause.** -/
theorem RetHeadRegistry.cons_declRunJ {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {ci : ConstantInfo .anon} {d : Ix.Kernel.Declaration .anon}
    (h : RetHeadRegistry.{u} t E env)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d ⟨ci :: env.consts⟩)
    (hfresh : env.find? ci.name = none)
    (hnt : ∀ T : Key .anon, ci.name ≠ Ix.Kernel.projTableName T)
    (hind : ∀ cv caps, ci ≠ .indInfo cv caps) :
    RetHeadRegistry.{u} t E ⟨ci :: env.consts⟩ := by
  refine h.declRunJ hd (Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)) ?_
  intro P cm ip cv caps hf hold
  rw [find_ind_cons_old hind hf] at hold
  cases hold

/-- **The clause is kept by a value constant along its declaration step.** -/
theorem keepsValuesJ_retHeadRegistry (t : Ix.Kernel.RoleTable) (E : Ixon.Env) :
    KeepsValuesJ (RetHeadRegistry.{u} t E) :=
  fun _ _ _ h hfresh hval hnt hd => h.cons_declRunJ hd hfresh hnt hval.not_ind

/-- **The clause and the store clause together** are kept by a value step at the key of a
32-byte address. -/
theorem keepsValuesKeyed_retHeadKeyed {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    (E : Ixon.Env) :
    KeepsValuesKeyed t (fun env => RetHeadRegistry.{u} t E env ∧ HashKeyed t env) :=
  ((keepsValuesJ_retHeadRegistry t E).keyed t).and (keepsValuesKeyed_hashKeyed htwf)

/-! ## The native block's install -/

/-- **A native block's install keeps the clause**, registering its family, given that the family
is read off the store at the new environment (`LateFamAt`) and has the entry's facts
(`FamIxonRetHead`, `BlockFamCtorNoProj`). -/
theorem RetHeadRegistry.nativeNoRec {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {env env₂ : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)} {nP : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon} (h : RetHeadRegistry.{u} t E env)
    (hfacts : NativeNoRecFacts env env₂ blk nP p₀ fam) (hat : LateFamAt t E env₂ fam)
    (hrh : FamIxonRetHead t E fam) (hnp : BlockFamCtorNoProj fam) :
    RetHeadRegistry.{u} t E env₂ := by
  obtain ⟨Reg, hR, hH⟩ := h
  refine ⟨_, hR.nativeNoRec hfacts hfacts.envExt hat, ?_⟩
  intro f hf
  rcases hf with hf | rfl
  · exact hH f hf
  · exact ⟨hrh, hnp⟩

/-! ## The late recursor's step -/

/-- **The prefix invariant and the clause after the late step**: `late_prefixInv_step`, whose
registry is the one it was handed, with the carried facts unchanged. -/
theorem late_prefixInv_step_rh {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop} {fam : NativeFam .anon}
    {cvR : ConstantVal .anon} {mI rP : Nat} {rules : List (RecRule .anon)}
    {cn : ConstantInfo .anon} {a₀ : _root_.Address}
    (hinv : Decl.PrefixInv.{u} E t lim env) (hR : LateRegistryWith.{u} t E env Reg)
    (hH : ∀ f, Reg f → LateEntryFacts t E f) (hfam : Reg fam)
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩)
    (hname : cn.name = Core.keyOf t a₀)
    (hcomp : Decl.CoreCompanions ⟨E, ⟨cn :: env.consts⟩, t, lim⟩)
    (hreload : Decl.ReloadsAs E t ⟨cn :: env.consts⟩ cn) :
    Decl.PrefixInv.{u} E t lim ⟨cn :: env.consts⟩ ∧
      RetHeadRegistry.{u} t E ⟨cn :: env.consts⟩ := by
  obtain ⟨hinv', hR'⟩ := late_prefixInv_step hinv hR hfam hrun hname hcomp hreload
  exact ⟨hinv', Reg, hR', hH⟩

/-- **`UnitStep` for a standalone recursor record of a native family, with the clause**:
`unitStep_recLate_of` whose second interface also receives the matched family's two entry
facts. -/
theorem unitStep_recLate_rh {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hinfo : c.info = .recr rc)
    (hparent : ∀ env, StepAt.{u} t envT E₀ E lim A c env →
      ∃ P ip, RecParent t E env P ip)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → RecParent t E env P ip →
      MatchedAt t E env P ip fam → FamIxonRetHead t E fam → BlockFamCtorNoProj fam →
      RecLateOut t E₀ E A env fam) :
    UnitStep.{u} (RetHeadRegistry.{u} t E) t envT E₀ E lim A c := by
  intro env hext hnd hinv hX href hfresh
  have hstep : StepAt.{u} t envT E₀ E lim A c env := ⟨hext, hnd, hinv, href, hfresh⟩
  obtain ⟨Reg, hR, hH⟩ := hX
  obtain ⟨P, ip, hpar⟩ := hparent env hstep
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam, hReg, hat, hnameP, hmatch⟩ := hR.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩
      ⟨hat, hnameP, hmatch⟩ (hH fam hReg).1 (hH fam hReg).2
  have hcomp := late_companions ht hinv.companions ⟨hat, hnameP, hmatch⟩ hcm hcmi hrun
  obtain ⟨hinv', hX'⟩ := late_prefixInv_step_rh hinv hR hH hReg hrun
    (hname.trans (LoadedReads.keyOf_eq t A).symm) hcomp hreload
  obtain ⟨hfreshN, -, -, -⟩ := late_head hrun
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  refine ⟨[cn], List.nodup_singleton _, ?_, hinv', hX', ?_, ?_⟩
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
