import IxVMRefinement.Claim.TopValue
import IxVMRefinement.Assembly.TypingDefnBlock
import IxVMRefinement.Assembly.FoldClauseSteps

/-! # The step of a value record, stated once for both folds

A value record is a standalone definition, theorem or opaque record, or a block every member of
which is one. Its step installs one constant for each constant address of the record, each
along one step of the declaration judgement, and registers no family.

The step is stated once (`ValueUnitStep`): from the fold's clause at the store and the limit of
the record's check (`FoldClauseWith L t Ec lc env Reg`), new constants such that the clause is
kept, with the same registry, at every store of a given family of stores, every limit and
every registry. The limit of the check is an `Option Nat`: a validating role context or an
assuming one. Two forms follow:

* the typing fold's `UnitStep (FoldExtra L t E) … lim` (`ValueUnitStep.unitStep`), at the store
  and the limit of the check;
* the binding fold's `OverUnitStep` (`Binding/ClauseValueSteps.lean`), at every record store of
  its witness store and every carried limit within its groups.

Contents:

* `valueInstall`, `memberInstall`: the install of one checked value constant, standalone or a
  member of a block, at the store and limit of its check: the constant, its reading, the
  declaration step that installs it, and the transport of the prefix invariant to every store
  that holds the record and every limit.
* `FoldClauseWith.consValue`: a value constant at the key of a 32-byte address, installed
  along its declaration step, keeps the clause at the same registry.
* `valueUnitStep_defn`: **the step of a standalone definition, theorem or opaque record.**
* `valueUnitStep_defnBlock`: **the step of a block of definitions**, its members installed in
  index order.
* `unitStep_value_foldExtra`, `unitStep_defnBlock_foldExtra`: the typing fold's two steps.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo)
open Ix.Kernel.Semantics (NativeFam DeclRunJ IndRoutesJ)
open Ix.Kernel.Model (rulesJ)

/-! ## The step, stated once -/

/-- **The unit step of a value record, stated once** (module docstring). `Ec` and `lc` are the
store and the limit the record's check is read at; `Stores` are the stores the clause is kept
at. At every environment that extends `envT`, has distinct names, satisfies the clause at `Ec`
and `lc` with a registry `Reg`, stores every used reference of the record that is not one of
its own constant addresses (unless the reference is no in-logic constant address of the run's
store) and stores none of the record's constant addresses: there are fresh constants `new` with
distinct names such that, at every store in `Stores`, every limit and every registry `Reg'`,
the clause at `env` with `Reg'` gives the clause at `new ++ env` with `Reg'`; every constant of
`new` is at the key of a constant address of the record; and at each constant address of the
record `new` holds a constant at that address's key that stores a reading of the address over
the run's records. -/
def ValueUnitStep (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env) (Stores : Ixon.Env → Prop) (Ec : Ixon.Env)
    (lc : Option Nat) (A : _root_.Address) (c : Ixon.Constant) : Prop :=
  ∀ (env : Ix.Kernel.Env .anon) (Reg : NativeFam .anon → Prop),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    FoldClauseWith.{u} L t Ec lc env Reg →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    ∃ new : List (ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      (∀ (E : Ixon.Env) (lim : Option Nat) (Reg' : NativeFam .anon → Prop), Stores E →
        FoldClauseWith.{u} L t E lim env Reg' →
        FoldClauseWith.{u} L t E lim ⟨new ++ env.consts⟩ Reg') ∧
      (∀ ci ∈ new, ∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∧
      (∀ x, ConstAddrOf A c x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀)

/-- **The typing fold's step**: the step of the unit against a store the clause is kept at, at
the limit of its check, for the part of the fold's clause beside the prefix invariant. -/
theorem ValueUnitStep.unitStep {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    {Stores : Ixon.Env → Prop} {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    (hE : Stores E) (h : ValueUnitStep.{u} L t envT E₀ Stores E lim A c) :
    UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c := by
  intro env hext hnd hinv hX href hfresh
  obtain ⟨⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hC : FoldClauseWith.{u} L t E lim env Reg :=
    FoldClauseWith.of_prefix hinv hR hkeys haux hlv
  obtain ⟨new, hnd', hfr, hkeep, hnamed, hreads⟩ := h env Reg hext hnd hC href hfresh
  have hC' := hkeep E lim Reg hE hC
  refine ⟨new, hnd', hfr, hC'.prefixInv, hC'.extra, hreads, ?_⟩
  intro ci hci
  obtain ⟨x, hx, hn⟩ := hnamed ci hci
  exact Or.inl ⟨x, hx, hn⟩

/-! ## The install of one value constant -/

/-- **The install of a checked standalone definition, theorem or opaque record**, at the store
`Ec` and the limit `lc` of its check (a validating role context or an assuming one). At a
prefix with the invariant there, the record's used references stored and the record's key
fresh: one value constant `cn` at the record's key that stores a reading of the record over
the run's records, the step of the declaration judgement that installs it, and the transport
of the prefix invariant past it at every store that holds the record and the run's blobs, at
every limit. -/
theorem valueInstall {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ Ec : Ixon.Env}
    {lc : Option Nat} {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ Ec)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : Claim.CheckedLimAt calls bAddr t A lc)
    (hkey : Decl.KeyFree (keyOf t A))
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} Ec t lc env)
    (hstored : Decl.UsedRefsStored t env c)
    (hfresh : env.find? (keyOf t A) = none) :
    ∃ (cn ci₀ : ConstantInfo .anon) (d₀ : Ix.Kernel.Declaration .anon),
      cn.name = keyOf t A ∧ Reads t E₀ A ci₀ ∧ StoredAs cn ci₀ ∧ IsValueConst cn ∧
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d₀ ⟨cn :: env.consts⟩ ∧
      ∀ (E' : Ixon.Env) (lim' : Option Nat), recordOf E' A = some c →
        (∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b) →
        Decl.PrefixInv.{u} E' t lim' env → Decl.PrefixInv.{u} E' t lim' ⟨cn :: env.consts⟩ := by
  have hbound : Bounded calls := (hst.good env none).2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    checkedLimAt_value_step (order_role := []) ht hbound hS hrec₀ hinfo hlogic
      List.not_mem_nil hchk Ec hstored
  obtain ⟨hev, hreads, hreload⟩ := hall (.regular 0)
  have hfreshD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      env.find? ci₀.name = none := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hfresh
  have hkeyD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0)),
      Decl.KeyFree ci₀.name := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hkey
  obtain ⟨⟨d₀, hrun⟩, -, htrans⟩ :=
    Decl.walkedValue_step_lim_run hinv hev (hst.good env none) hfreshD hkeyD
  rw [LoadedReads.installs_defnDecl] at hrun
  have hname : (LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t A :=
    LoadedReads.defnConst_name _ _ _ _
  refine ⟨LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0),
    LoadedReads.defnConst d.kind ⟨keyOf t A, List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0),
    d₀, hname, hreads, storedAs_defnConst _ _ _ _ hannT hannV, isValueConst_defnConst _ _ _ _,
    hrun, ?_⟩
  intro E' lim' hrecE hblobE hinv'
  have h := htrans E' lim' (hreload E' hrecE hblobE) hinv'
  rw [LoadedReads.installs_defnDecl] at h
  exact h

/-- **The install of one checked member of a definition block**, at the store `Ec` and the
limit `lc` of its check (a validating role context or an assuming one). At a prefix with the
invariant there, the block's used references stored and the member's key fresh: one value
constant `cn` at the member's key that stores a reading of the member's address over the run's
records, the step of the declaration judgement that installs it, and the transport of the
prefix invariant past it at every store that holds the member's projection record, the block
record and the run's blobs, at every limit. -/
theorem memberInstall {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ Ec : Ixon.Env}
    {lc : Option Nat} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ Ec)
    (hrecB : Ix.Cert.recordAt E₀ B = some cb) (hmuts : cb.info = .muts ms)
    (hlogic : InLogic cb) {k : Nat} {d : Ixon.Definition} (hk : ms[k]? = some (.defn d))
    (hm : Claim.MemberCheckedLimAt calls bAddr t B ms k lc)
    (hkey : Decl.KeyFree (keyOf t (memberAddr B k (.defn d))))
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} Ec t lc env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (keyOf t (memberAddr B k (.defn d))) = none) :
    ∃ (cn ci₀ : ConstantInfo .anon) (d₀ : Ix.Kernel.Declaration .anon),
      cn.name = keyOf t (memberAddr B k (.defn d)) ∧
      Reads t E₀ (memberAddr B k (.defn d)) ci₀ ∧ StoredAs cn ci₀ ∧ IsValueConst cn ∧
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d₀ ⟨cn :: env.consts⟩ ∧
      ∀ (E' : Ixon.Env) (lim' : Option Nat),
        recordOf E' (memberAddr B k (.defn d)) = some (memberProjection B k (.defn d)) →
        recordOf E' B = some cb →
        (∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b) →
        Decl.PrefixInv.{u} E' t lim' env → Decl.PrefixInv.{u} E' t lim' ⟨cn :: env.consts⟩ := by
  have hbound : Bounded calls := (hst.good env none).2
  obtain ⟨ty₀, val₀, ty', val', hannT, hannV, hall⟩ :=
    memberCheckedLimAt_value_step (order_role := []) ht hbound hS hcov hrecB hmuts hk hlogic
      List.not_mem_nil hm Ec hstored
  obtain ⟨hev, hreads, hreload⟩ := hall (.regular 0)
  have hfreshD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀
      (.regular 0)), env.find? ci₀.name = none := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hfresh
  have hkeyD : ∀ ci₀ ∈ IxVM.Consistency.installs (LoadedReads.defnDecl d.kind
      ⟨Core.keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀
      (.regular 0)), Decl.KeyFree ci₀.name := by
    intro ci₀ hci
    rw [LoadedReads.installs_defnDecl] at hci
    rw [List.mem_singleton.mp hci, LoadedReads.defnConst_name]
    exact hkey
  obtain ⟨⟨d₀, hrun⟩, -, htrans⟩ :=
    Decl.walkedValue_step_lim_run hinv hev (hst.good env none) hfreshD hkeyD
  rw [LoadedReads.installs_defnDecl] at hrun
  have hname : (LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val'
      (.regular 0)).name = keyOf t (memberAddr B k (.defn d)) :=
    LoadedReads.defnConst_name _ _ _ _
  refine ⟨LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty'⟩ val' (.regular 0),
    LoadedReads.defnConst d.kind
      ⟨keyOf t (memberAddr B k (.defn d)), List.range d.lvls.toNat, ty₀⟩ val₀ (.regular 0),
    d₀, hname, hreads, storedAs_defnConst _ _ _ _ hannT hannV, isValueConst_defnConst _ _ _ _,
    hrun, ?_⟩
  intro E' lim' hprojE hblockE hblobE hinv'
  have h := htrans E' lim' (hreload E' hprojE hblockE hblobE) hinv'
  rw [LoadedReads.installs_defnDecl] at h
  exact h

/-! ## A value constant keeps the clause -/

/-- **A value constant at the key of a 32-byte address, installed along its declaration step,
keeps the clause at the same registry**, given the prefix invariant past it. The registry is
kept at the same registered families by IxC's declaration step (`EnvModelN.declRunJ`); the
store keys, the roots and the level clauses by a value constant at such a key. -/
theorem FoldClauseWith.consValue {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {Reg : NativeFam .anon → Prop}
    (h : FoldClauseWith.{u} L t E lim env Reg) {cn : ConstantInfo .anon}
    {d₀ : Ix.Kernel.Declaration .anon}
    (hfresh : env.find? cn.name = none) (hval : IsValueConst cn)
    (hnt : ∀ T : Ix.Kernel.Key .anon, cn.name ≠ Ix.Kernel.projTableName T)
    (hd₀ : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d₀ ⟨cn :: env.consts⟩)
    (hkeyx : ∃ x : _root_.Address, cn.name = keyOf t x ∧ x.hash.size = 32)
    (hinv' : Decl.PrefixInv.{u} E t lim ⟨cn :: env.consts⟩) :
    FoldClauseWith.{u} L t E lim ⟨cn :: env.consts⟩ Reg := by
  have hextE : Ix.Kernel.EnvExt env ⟨cn :: env.consts⟩ :=
    Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
  have hreg : FamRegistryWith.{u} L t E ⟨cn :: env.consts⟩ Reg :=
    h.registry.step hL (fun V _ hm => Ix.Kernel.Model.EnvModelN.declRunJ V hm hd₀) hextE
      (fun P cm ip cv caps hf hold _ _ _ => by
        rw [find_ind_cons_old hval.not_ind hf] at hold
        cases hold)
      (fun C cm cp cv nP nF hf hold _ _ _ => by
        have hnc : ∀ cv' nP' nF', cn ≠ .ctorInfo cv' nP' nF' := fun _ _ _ he => by
          rcases hval with ⟨_, _, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, h1⟩ <;> rw [h1] at he <;> cases he
        rw [find_ctor_cons_old hnc hf] at hold
        cases hold)
      (fun hp => recRhsPwNoModel_cons_noRec hextE hp fun _ _ _ _ he => by
        rcases hval with ⟨_, _, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, h1⟩ <;> rw [h1] at he <;> cases he)
      (fun hm => recHasModelNotNative_cons_noRecNoModel hextE hm
        (fun _ _ _ _ he => by
          rcases hval with ⟨_, _, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, h1⟩ <;> rw [h1] at he <;> cases he)
        (fun k he => let ⟨x, hx, _⟩ := hkeyx; keyOf_nonAux t x k .model (hx.symm.trans he)))
  exact FoldClauseWith.of_prefix hinv' hreg
    (keepsValuesKeyed_hashKeyed h.tableWf env _ d₀ h.hashKeyed hfresh hval hnt hd₀ hkeyx)
    (keepsValuesKeyed_auxRoot t env _ d₀ h.auxRoot hfresh hval hnt hd₀ hkeyx)
    (keepsValuesKeyed_lvClauses t env _ d₀ ⟨h.thmLevels, h.storeArR⟩ hfresh hval hnt hd₀
      hkeyx)

/-! ## The step of a standalone definition, theorem or opaque record -/

/-- **The step of a standalone definition, theorem or opaque record, stated once.** The run's
store `E₀` is a run store and holds the record `c` at `A`, in Lean's logic; the walk checked
`A` under the role context at the limit `lc`, validating or assuming; `Ec` is a store the
check is read at (`StepStore`); every store the clause is kept at holds the record and the
run's blobs; the keys of the record's constant addresses are free; no used reference is an
inert axiom's; and at every environment the fold hands the step the other used references are
stored. One constant is installed: the declaration of the record's canonical annotations, at
the record's key. -/
theorem valueUnitStep_defn {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {Stores : Ixon.Env → Prop} {lc : Option Nat}
    {bAddr A : _root_.Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ Ec)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : Claim.CheckedLimAt calls bAddr t A lc)
    (hStores : ∀ E, Stores E → recordOf E A = some c ∧
      ∀ x b, E₀.blobs.get? x = some b → E.blobs.get? x = some b)
    (hkeys : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) :
    ValueUnitStep.{u} L t envT E₀ Stores Ec lc A c := by
  intro env Reg hext hnd hC href hfresh
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inl ⟨d, hinfo⟩⟩
  have hfreshA : env.find? (keyOf t A) = none := hfresh A hown
  obtain ⟨cn, ci₀, d₀, hname, hreads, hsto, hval, hd₀, htrans⟩ :=
    valueInstall ht hS hst hc hinfo hlogic hchk (hkeys A hown) hC.prefixInv hstored hfreshA
  have hfreshC : env.find? cn.name = none := by
    rw [hname]
    exact hfreshA
  have hnt : ∀ T : Ix.Kernel.Key .anon, cn.name ≠ Ix.Kernel.projTableName T := by
    intro T
    rw [hname]
    exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t A)
  have hkeyx : ∃ x : _root_.Address, cn.name = keyOf t x ∧ x.hash.size = 32 :=
    ⟨A, hname, address_size_of_record hS hc⟩
  refine ⟨[cn], List.nodup_singleton _, ?_, ?_, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshC
  · intro E lim Reg' hE hC'
    obtain ⟨hrecE, hblobE⟩ := hStores E hE
    exact hC'.consValue hL hfreshC hval hnt hd₀ hkeyx
      (htrans E lim hrecE hblobE hC'.prefixInv)
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact ⟨A, hown, hname⟩
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hsto⟩
    · have h := hinfo.symm.trans hms
      cases h

/-- **`UnitStep` for a standalone definition, theorem or opaque record, keeping the fold's
clause**, at the limit of either role context. -/
theorem unitStep_value_foldExtra {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {d : Ixon.Definition}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .defn d) (hlogic : InLogic c)
    (hchk : Claim.CheckedLimAt calls bAddr t A lim)
    (hkeys : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c) :
    UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c := by
  have hheld : ∀ E', E' = E → recordOf E' A = some c ∧
      ∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b := by
    intro E' hE'
    rw [hE']
    exact ⟨hst.held hc, hst.runBlob⟩
  exact ValueUnitStep.unitStep (Stores := fun E' => E' = E) rfl
    (valueUnitStep_defn (Stores := fun E' => E' = E) hL ht hS hst hc hinfo hlogic hchk hheld
      hkeys hinert hcover)

/-! ## The step of a block of definitions -/

/-- **The members `0, …, m - 1` of a definition block installed**, in index order, at the
front of `env`: the installed constants `acc` have distinct fresh keys; at every store the
clause is kept at, every limit and every registry, the clause at `env` gives the clause at the
prefix; each of the members has a constant storing a reading of its address; and each installed
constant is at the key of one of them. -/
structure ValueMembersDone (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Stores : Ixon.Env → Prop)
    (env : Ix.Kernel.Env .anon) (B : _root_.Address) (ms : Array Ixon.MutConst) (m : Nat)
    (acc : List (ConstantInfo .anon)) : Prop where
  nodup : (acc.map (·.name)).Nodup
  fresh : ∀ ci ∈ acc, env.find? ci.name = none
  keep : ∀ (E : Ixon.Env) (lim : Option Nat) (Reg' : NativeFam .anon → Prop), Stores E →
    FoldClauseWith.{u} L t E lim env Reg' →
    FoldClauseWith.{u} L t E lim ⟨acc ++ env.consts⟩ Reg'
  done : ∀ i mi, i < m → ms[i]? = some mi → ∃ ci ∈ acc, ∃ ci₀,
    ci.name = keyOf t (memberAddr B i mi) ∧ Reads t E₀ (memberAddr B i mi) ci₀ ∧
      StoredAs ci ci₀
  named : ∀ ci ∈ acc, ∃ i mi, i < m ∧ ms[i]? = some mi ∧ ci.name = keyOf t (memberAddr B i mi)

/-- **The step of a block of definitions, stated once.** The run's store `E₀` is a run store
that holds every record the run hashed, and holds the block `cb` at `B`, in Lean's logic, every
member a definition, theorem or opaque constant; the walk checked every member under the role
context at the limit `lc`, validating or assuming; `Ec` is a store the checks are read at
(`StepStore`), one of the stores the clause is kept at; every such store holds the block
record, every member's projection record and the run's blobs; the keys of the record's
constant addresses are free; no reference the block uses is an inert axiom's; and at every
environment the fold hands the step the block's other used references are stored. The members
are installed in index order, each at the prefix that holds the members before it. -/
theorem valueUnitStep_defnBlock {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {Stores : Ixon.Env → Prop} {lc : Option Nat}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ Ec)
    (hEc : Stores Ec)
    (hc : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lc)
    (hStores : ∀ E, Stores E → recordOf E B = some cb ∧
      (∀ i mi, ms[i]? = some mi →
        recordOf E (memberAddr B i mi) = some (memberProjection B i mi)) ∧
      ∀ x b, E₀.blobs.get? x = some b → E.blobs.get? x = some b)
    (hkeys : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb) :
    ValueUnitStep.{u} L t envT E₀ Stores Ec lc B cb := by
  intro env Reg hext hnd hC href hfresh
  have hbound : Bounded calls := (hst.good env none).2
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hrecB : Ix.Cert.recordAt E₀ B = some cb := (hS.recordOf_eq_recordAt B).symm.trans hc
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  have hmem : ∀ i mi, ms[i]? = some mi → i < UInt64.size ∧
      Ix.Cert.recordAt E₀ (memberAddr B i mi) = some (memberProjection B i mi) :=
    fun i mi h => LoadedReads.memberCheckedLimAt_record hbound hS hcov
      (hchk i (Array.getElem?_eq_some_iff.mp h).1) h
  have hkeyM : ∀ i mi, ms[i]? = some mi → Decl.KeyFree (keyOf t (memberAddr B i mi)) :=
    fun i mi h => hkeys _ (Or.inr ⟨ms, i, mi, hmuts, h, Or.inl rfl⟩)
  have hfreshM : ∀ i mi, ms[i]? = some mi → env.find? (keyOf t (memberAddr B i mi)) = none :=
    fun i mi h => hfresh _ (Or.inr ⟨ms, i, mi, hmuts, h, Or.inl rfl⟩)
  have hdistinct : ∀ i j mi mj, ms[i]? = some mi → ms[j]? = some mj →
      keyOf t (memberAddr B i mi) = keyOf t (memberAddr B j mj) → i = j := by
    intro i j mi mj hi hj hk
    obtain ⟨di, rfl⟩ := hdefs i mi hi
    obtain ⟨dj, rfl⟩ := hdefs j mj hj
    obtain ⟨hi64, hri⟩ := hmem i _ hi
    obtain ⟨hj64, hrj⟩ := hmem j _ hj
    exact memberAddr_inj hi64 hj64 hri hrj (keyOf_inj hroles hk)
  have hfold : ∀ m, m ≤ ms.size →
      ∃ acc, ValueMembersDone.{u} L t E₀ Stores env B ms m acc := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨[], List.nodup_nil, (fun _ h => nomatch h), (fun _ _ _ _ h => h),
        (fun i mi hi _ => absurd hi (Nat.not_lt_zero _)), (fun _ h => nomatch h)⟩
    | succ m ih =>
      intro hm
      obtain ⟨acc, hacc⟩ := ih (by omega)
      have hlt : m < ms.size := by omega
      obtain ⟨mi, hmi⟩ : ∃ mi, ms[m]? = some mi := ⟨ms[m], Array.getElem?_eq_getElem hlt⟩
      obtain ⟨d, rfl⟩ := hdefs m mi hmi
      have hnotacc : ∀ ci ∈ acc, ci.name ≠ keyOf t (memberAddr B m (.defn d)) := by
        intro ci hci he
        obtain ⟨i, mj, hi, hmj, hn⟩ := hacc.named ci hci
        have hieq := hdistinct i m mj (.defn d) hmj hmi (hn.symm.trans he)
        omega
      have hfreshCur : (⟨acc ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
          (keyOf t (memberAddr B m (.defn d))) = none := by
        apply find_none_of_not_storedAt
        rintro ⟨ci, hci, hn⟩
        have hci' : ci ∈ acc ++ env.consts := hci
        rcases List.mem_append.mp hci' with hca | hce
        · exact hnotacc ci hca hn
        · have hs := find_isSome_of_storedAt (t := t) (env := env)
            (x := memberAddr B m (.defn d)) ⟨ci, hce, hn⟩
          rw [hfreshM m _ hmi] at hs
          simp at hs
      have hCacc : FoldClauseWith.{u} L t Ec lc ⟨acc ++ env.consts⟩ Reg :=
        hacc.keep Ec lc Reg hEc hC
      obtain ⟨cn, ci₀, d₀, hname, hreads, hsto, hval, hd₀, htrans⟩ :=
        memberInstall ht hS hcov hst hrecB hmuts hlogic hmi (hchk m hlt) (hkeyM m _ hmi)
          hCacc.prefixInv (usedRefsStored_append hstored acc) hfreshCur
      have hfreshC : (⟨acc ++ env.consts⟩ : Ix.Kernel.Env .anon).find? cn.name = none := by
        rw [hname]
        exact hfreshCur
      have hnt : ∀ T : Ix.Kernel.Key .anon, cn.name ≠ Ix.Kernel.projTableName T := by
        intro T
        rw [hname]
        exact Decl.ne_projTableName_of_isBaseKey
          (Decl.isBaseKey_keyOf t (memberAddr B m (.defn d)))
      have hkeyx : ∃ x : _root_.Address, cn.name = keyOf t x ∧ x.hash.size = 32 :=
        ⟨memberAddr B m (.defn d), hname,
          address_size_of_record hS (hS.recordOf_of_recordAt (hmem m _ hmi).2)⟩
      refine ⟨cn :: acc, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmemn => ?_, hacc.nodup⟩
        obtain ⟨ci, hci, he⟩ := List.mem_map.mp hmemn
        exact hnotacc ci hci (he.trans hname)
      · intro ci hci
        rcases List.mem_cons.mp hci with hcn | hci'
        · rw [hcn, hname]
          exact hfreshM m _ hmi
        · exact hacc.fresh ci hci'
      · intro E lim Reg' hE hC'
        obtain ⟨hblockE, hprojE, hblobE⟩ := hStores E hE
        have hC'' := hacc.keep E lim Reg' hE hC'
        exact hC''.consValue hL hfreshC hval hnt hd₀ hkeyx
          (htrans E lim (hprojE m _ hmi) hblockE hblobE hC''.prefixInv)
      · intro i mj hi hmj
        by_cases hi' : i < m
        · obtain ⟨ci, hci, ci₀', h1, h2, h3⟩ := hacc.done i mj hi' hmj
          exact ⟨ci, List.mem_cons_of_mem _ hci, ci₀', h1, h2, h3⟩
        · have hieq : i = m := by omega
          rw [hieq] at hmj
          rw [hmi] at hmj
          rw [hieq, ← Option.some.inj hmj]
          exact ⟨cn, List.mem_cons_self, ci₀, hname, hreads, hsto⟩
      · intro ci hci
        rcases List.mem_cons.mp hci with hcn | hci'
        · rw [hcn]
          exact ⟨m, _, Nat.lt_succ_self m, hmi, hname⟩
        · obtain ⟨i, mj, hi, hmj, hn⟩ := hacc.named ci hci'
          exact ⟨i, mj, Nat.lt_succ_of_lt hi, hmj, hn⟩
  obtain ⟨acc, hacc⟩ := hfold ms.size (Nat.le_refl _)
  refine ⟨acc, hacc.nodup, hacc.fresh, hacc.keep, ?_, ?_⟩
  · intro ci hci
    obtain ⟨i, mi, -, hmi, hn⟩ := hacc.named ci hci
    exact ⟨memberAddr B i mi, Or.inr ⟨ms, i, mi, hmuts, hmi, Or.inl rfl⟩, hn⟩
  · intro x hx
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, mi, hms', hmi, hx⟩
    · exact (standalone_not_block hs ⟨ms, hmuts⟩).elim
    · rw [hmuts] at hms'
      have hmm : ms = ms' := Ixon.ConstantInfo.muts.inj hms'
      subst hmm
      rcases hx with hx | ⟨ind, j, hind, -, -⟩
      · rw [hx]
        exact hacc.done i mi (Array.getElem?_eq_some_iff.mp hmi).1 hmi
      · obtain ⟨d, hd⟩ := hdefs i mi hmi
        rw [hd] at hind
        cases hind

/-- **`UnitStep` for a block of definitions, keeping the fold's clause**, at the limit of
either role context. -/
theorem unitStep_defnBlock_foldExtra {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hdefs : DefnBlock ms)
    (hchk : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim)
    (hkeys : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb) :
    UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim B cb := by
  have hbound : Bounded calls := (hst.good envT none).2
  have hheld : ∀ E', E' = E → recordOf E' B = some cb ∧
      (∀ i mi, ms[i]? = some mi →
        recordOf E' (memberAddr B i mi) = some (memberProjection B i mi)) ∧
      ∀ x b, E₀.blobs.get? x = some b → E'.blobs.get? x = some b := by
    intro E' hE'
    rw [hE']
    exact ⟨hst.held hc,
      fun i mi h => hst.held (hS.recordOf_of_recordAt
        (LoadedReads.memberCheckedLimAt_record hbound hS hcov
          (hchk i (Array.getElem?_eq_some_iff.mp h).1) h).2),
      hst.runBlob⟩
  exact ValueUnitStep.unitStep (Stores := fun E' => E' = E) rfl
    (valueUnitStep_defnBlock (Stores := fun E' => E' = E) hL ht hS hcov hst rfl hc hmuts
      hlogic hdefs hchk hheld hkeys hinert hcover)

end IxVM.Refinement.Typing
