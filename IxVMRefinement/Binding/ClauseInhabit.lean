import IxVMRefinement.Binding.ClauseFold
import IxVMRefinement.Binding.StoreCoverage
import IxVMRefinement.Binding.Inhabit
import IxVMRefinement.Assembly.FoldClauseSteps

/-! # Inhabitants of the binding fold's interfaces over the fold's clause

* `overUnitStep_recLate`: **the step of a standalone recursor record of a native family**. The
  parent is read at one store the run is good for; the registry, chosen before the store, holds
  its family, and the family is read off the parent's record at every store for `R`. The
  circuit's output is asked once, at the family read at that one store, with the recursor's
  reload at every store for `R`. Nothing is asked about the circuit's dispatch at another store.
* `roleFreeShapes_of_unit`, `roleFreeShapes_natPred`: the shapes premise of a group with no role
  unit is not asked at a group that holds one; at the default order, group 7 holds `Nat.pred`.
* `guardAt_of_noPropTable`, `raisedGuard_of_noPropTable`: the load contract's guard does not read
  the limit where no stored projection table is of a propositional structure, so the guard at
  the raised limits is the guard the clause holds at the group's validation limit.
* At the default table (`ctab`):
  * `bndOver_basis_default`: the invariant below group 6, at the store of the basis rows and the
    environment of the pins.
  * `admits_bool_observed`: the admission of group 6 (`Bool`) for the observed run record, from
    the store of the basis rows to the store with `Bool`'s committed rows. Its store clauses are
    proved; its two run clauses are the two observations.
  * `storeCovered_bool`: the store after group 6 is covered.
  * `shapes_bool`, `groupKept_bool`, `bndOver_bool`: at the environment IxC's native check of
    the `Bool` block installs, the stored shapes below 7, the group's roles kept, and the
    invariant below 7 from the clause below 6 at that environment and block wholeness (what the
    closure's unit step is to give): the raise past group 6 and its guard need nothing else.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Semantics (NativeFam DeclNativeRecLateRunJ)
open Ix.Kernel.Model (rulesJ)
open IxVM.Refinement.TableInhabit (basisEnv)
open IxVM.Refinement.StoreInhabit (basisStore)
open IxVM.Refinement.BoolInhabit (boolStore boolEnv)

/-! ## The step of a standalone recursor record -/

/-- **What the circuit's check of a recursor record gives at a registered family**, for the
binding fold: the late relation with the recursor `cn` in front, `cn` at the record's key and
stored as a reading of the record over the run's records, and its reload at every record store
for `R`. -/
def RecLateOutOver (t : Ix.Kernel.RoleTable) (R E₀ : Ixon.Env) (A : _root_.Address)
    (env : Ix.Kernel.Env .anon) (fam : NativeFam .anon) : Prop :=
  ∃ (cvR : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon))
    (cn : ConstantInfo .anon) (ci₀ : ConstantInfo .anon),
    DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules ⟨cn :: env.consts⟩ ∧
    cn.name = keyOf t A ∧ Reads t E₀ A ci₀ ∧ StoredAs cn ci₀ ∧
    ∀ E, RecordsFor R E → Decl.ReloadsAs E t ⟨cn :: env.consts⟩ cn

/-- At a record store for `R`, the interface gives the typing fold's. -/
theorem RecLateOutOver.recLateOut {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env}
    {A : _root_.Address} {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    (h : RecLateOutOver t R E₀ A env fam) (hE : RecordsFor R E) :
    RecLateOut t E₀ E A env fam := by
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ := h
  exact ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload E hE⟩

/-- **The step of a standalone recursor record of a native family, over the fold's clause**
(module docstring). `Ec` is a record store for `R` the parent is read at, at a carried limit
`lim₀` within `G`. -/
theorem overUnitStep_recLate {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim₀ : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (ht : t.check = .ok ()) (hinfo : c.info = .recr rc)
    (hsz : A.hash.size = 32) (hRc : RecordsFor R Ec) (hc₀ : Carried lim₀)
    (hl₀ : LimWithin G t lim₀) (hop : keyOf t A ∉ RoleOps.opNames)
    (hparent : ∀ env, StepAt.{u} t envT E₀ Ec lim₀ A c env →
      ∃ P ip, RecParent t Ec env P ip ∧ (recordOf R P).isSome = true)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ Ec lim₀ A c env → RecParent t Ec env P ip →
      FamReadAt L t Ec env P ip fam → RecLateOutOver t R E₀ A env fam) :
    OverUnitStep.{u} L t G R envT E₀ A c := by
  intro env Reg hext hnd hcl href hfresh
  have hC₀ := hcl Ec hRc lim₀ hc₀ hl₀
  have hstep : StepAt.{u} t envT E₀ Ec lim₀ A c env :=
    ⟨hext, hnd, hC₀.prefixInv, href, hfresh⟩
  obtain ⟨P, ip, hpar, hheld⟩ := hparent env hstep
  have hpar' := hpar
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar'
  -- The family, found once, at the store the parent was read at.
  obtain ⟨fam, hReg, hread₀⟩ := hC₀.registry.at_parent ht hfP hres hcm hcmi hnat
  have hnameP : fam.p.cvT.name = keyOf t P := hread₀.2.1
  obtain ⟨cmR, hcmR⟩ := Option.isSome_iff_exists.mp hheld
  have hcc : cmR = cm := Option.some.inj ((hRc.2.1 P cmR hcmR).symm.trans hcm)
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep hpar hread₀
  -- The clause with the recursor, at every store for `R` and every carried limit within `G`.
  have hall : ∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
      FoldClauseWith.{u} L t E lim ⟨cn :: env.consts⟩ Reg := by
    intro E hE lim hc hl
    have hC := hcl E hE lim hc hl
    have hcmE : Ix.Cert.recordAt E P = some cm := by
      rw [← hcc]
      exact hE.2.1 P cmR hcmR
    have hread : FamReadAt L t E env P ip fam := (hC.fams fam hReg).readAt ht hnameP hcmE hcmi
    have hcomp := late_companions_read ht hC.companions hread hcmE hcmi hrun
    exact hC.lateRec hL hReg hrun (hname.trans (LoadedReads.keyOf_eq t A).symm) hsz hcomp
      (hreload E hE)
  obtain ⟨hfreshN, -, -, -⟩ := late_head hrun
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  refine ⟨[cn], Reg, List.nodup_singleton _, ?_, hall, ?_, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshN
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact hop
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hstored⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

/-! ## The shapes premise is not asked at a group with a role unit -/

/-- **At a group that holds an operation or a standard axiom, the shapes premise of a group
with no role unit holds outright**: its own premise fails there. -/
theorem roleFreeShapes_of_unit (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) {g : Nat} {r : Ix.Kernel.Role} (hr : r ∈ roleGroup g)
    (hk : r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) : RoleFreeShapes.{u} L ρ t g :=
  fun hnu => absurd hk (hnu r hr)

set_option maxRecDepth 100000 in
private theorem natPred_group7 : Ix.Kernel.Role.natPred ∈ roleGroup 7 := by decide +kernel

/-- **At the group of `Nat.pred` (group 7) the shapes premise holds for every run and every
table.** -/
theorem roleFreeShapes_natPred (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (ρ : BRun)
    (t : Ix.Kernel.RoleTable) : RoleFreeShapes.{u} L ρ t 7 :=
  roleFreeShapes_of_unit L ρ t natPred_group7 (Or.inl (by decide))

/-! ## The guard where no propositional structure is stored -/

/-- **The load contract's guard does not read the limit where no stored projection table has a
structure sort that passes the zero test.** -/
theorem guardAt_of_noPropTable {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim lim' : Option Nat}
    {env : Ix.Kernel.Env .anon} (h : GuardAt E t lim env)
    (hno : ∀ (k : Ix.Kernel.Key .anon) (tbl : Ix.Kernel.ProjTable .anon),
      env.find? k = some (.projInfo tbl) →
      Ix.Kernel.Level.isEquiv tbl.structSort .zero ≠ some true) :
    GuardAt E t lim' env := by
  intro bp ip ptr hh hh' cs b i ev good hb hip j cvC nP nF tbl hc htbl
  exact ⟨(h bp ip ptr hh hh' cs b i ev good hb hip j cvC nP nF tbl hc htbl).1,
    fun hz => absurd hz (hno _ tbl htbl)⟩

/-- **The guard at the raised limits, where no propositional structure's table is stored**: it
is the guard the clause holds at the group's validation limit. -/
theorem raisedGuard_of_noPropTable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (h : BeforeRaise.{u} L t g R env)
    (hno : ∀ (k : Ix.Kernel.Key .anon) (tbl : Ix.Kernel.ProjTable .anon),
      env.find? k = some (.projInfo tbl) →
      Ix.Kernel.Level.isEquiv tbl.structSort .zero ≠ some true) :
    ∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin (· < g + 1) t lim →
      GuardAt E t lim env := by
  intro E hE lim _ _
  obtain ⟨Reg, hR⟩ := h.clause
  exact guardAt_of_noPropTable
    (lim := some (valLimit g)) (projGuard_of_loads
      (hR E hE (some (valLimit g)) (carried_valLimit g) (limWithin_below t g)).loads) hno

/-! ## The default table: the basis and the `Bool` group -/

/-- **The invariant below group 6 at the default table**, at the store of the basis rows and
the environment of the pins. -/
theorem bndOver_basis_default (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) :
    BndOver.{u} L ctab (· < 6) basisStore basisEnv :=
  bndOver_basis_at L RoleVal.committedDefaultRoleTable_check StoreInhabit.preludePinned_default
    ClosedFacts.defaultTable_allBound

/-- **The admission of the `Bool` group at the default table, for the observed run record**
whose loaded records are the store with `Bool`'s committed rows. The store clauses are those of
`admits_bool`; the two run clauses are the observations: the check of each new unit at the
group's validation limit, and the validation of each role of the group. -/
theorem admits_bool_observed {calls : List (Call F)} {bAddr : _root_.Address}
    (hchk : ∀ a c, New basisStore boolStore a → recordOf boolStore a = some c → UnitKind c →
      UnitCheckedAt calls bAddr ctab boolStore a (some (valLimit 6)))
    (hval : ∀ r ∈ roleGroup 6, RoleValidationIn calls bAddr ctab 6 r) :
    Admits (observedRun calls bAddr ctab boolStore (fun _ a => boolRank a)) ctab 6 basisStore
      boolStore where
  mono := admits_bool.mono
  monoBlobs := admits_bool.monoBlobs
  loaded := admits_bool.loaded
  loadedBlobs := admits_bool.loadedBlobs
  hashed := admits_bool.hashed
  usedClosed := admits_bool.usedClosed
  committed := admits_bool.committed
  zeroFree := admits_bool.zeroFree
  rankUsed := admits_bool.rankUsed
  rankOwner := admits_bool.rankOwner
  projMember := admits_bool.projMember
  standing := admits_bool.standing
  logic := admits_bool.logic
  checked := hchk
  validated := hval
  kept := admits_bool.kept
  opsOwn := admits_bool.opsOwn
  unitsLast := admits_bool.unitsLast

/-- The reading clause of the `Bool` group's admission: the run's records are the store's. -/
theorem admitsReads_bool : AdmitsReads boolRun ctab basisStore boolStore where
  blobs := fun _ _ h => h
  reads := fun _ _ _ _ _ _ _ h => h

/-- **The store after the `Bool` group's admission at the default table is covered.** -/
theorem storeCovered_bool : StoreCovered boolStore boolStore :=
  storeCovered_of_admits admits_bool admitsReads_bool

/-- **The stored shapes below group 7 at the environment with `Bool`** (decided for `Bool`; no
other shape's group is below 7). -/
theorem shapes_bool : Shapes (· < 6 + 1) boolEnv := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := groupOf_values
  have hbool := boolShape_of boolEnv_shapeB
  exact {
    bool := fun _ => hbool
    char := fun h => absurd (show Ix.SpecDigest.groupOf .char < 6 + 1 from h) (by omega)
    string := fun h => absurd (show Ix.SpecDigest.groupOf .string < 6 + 1 from h) (by omega)
    list := fun h => absurd (show Ix.SpecDigest.groupOf .list < 6 + 1 from h) (by omega)
    charOfNat := fun h =>
      absurd (show Ix.SpecDigest.groupOf .charOfNat < 6 + 1 from h) (by omega)
    stringOfList := fun h =>
      absurd (show Ix.SpecDigest.groupOf .stringOfList < 6 + 1 from h) (by omega)
    iff := fun h => absurd (show Ix.SpecDigest.groupOf .iff < 6 + 1 from h) (by omega)
    nonempty := fun h => absurd (show Ix.SpecDigest.groupOf .nonempty < 6 + 1 from h) (by omega) }

/-- **The roles of the `Bool` group are stored as their committed records declare them.** -/
theorem groupKept_bool : GroupKept ctab 6 boolStore boolEnv :=
  ⟨fun r hr hk _ a ha => BoolInhabit.tableShape_bool.{0}.kept 6 r a (Or.inr rfl) hr hk ha,
    fun r hr hp a ha =>
      BoolInhabit.tableShape_bool.{0}.preludeKept 6 r a (Or.inr rfl) hr hp ha⟩

private theorem ops_not_boolRoles :
    ∀ r ∈ RoleOps.opRoles, r ∉ BoolInhabit.boolRoles ++ TableInhabit.basisRoleOrder := by
  decide

/-- **The invariant below group 7 at the default table**, at the store with `Bool`'s committed
rows and the environment IxC's native check of the `Bool` block installs, from the clause below
group 6 at that environment and block wholeness there (what the closure's unit step gives).
The stored shapes, the group's roles, the raise past group 6 and the guard at the raised limit
are proved: the environment stores no projection table. -/
theorem bndOver_bool (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (hclause : FoldClauseOver.{u} L ctab (· < 6) boolStore boolEnv)
    (hwhole : ∀ E, RecordsFor boolStore E →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (boolEnv.find? (keyOf ctab a)).isSome = true → Ix.Cert.recordAt E a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb →
        cb.info = .muts ms → BlockStored ctab boolEnv B ms) :
    BndOver.{u} L ctab (· < 6 + 1) boolStore boolEnv := by
  have hall : AllBound ctab := ClosedFacts.defaultTable_allBound
  have htwf : ctab.wf = true := wf_of_check RoleVal.committedDefaultRoleTable_check
  have hnu : ∀ r ∈ roleGroup 6, ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) := by
    intro r hr hk
    have h := group6_noUnits r hr
    rcases hk with h1 | h1
    · exact h.1 h1
    · exact h.2 h1
  have hfab := fabKeys_of_groupKept htwf (Nat.le_refl 6) hnu groupKept_bool
  have hraise : RaiseAt ctab boolEnv 6 :=
    raiseAt_of_noOps (Nat.le_refl 6) (fun r hr hop => hnu r hr (Or.inl hop)) hfab
      (fun h => absurd h (by decide))
  have hset : (fun k => k < 6 ∨ k = 6) = (fun k : Nat => k < 6 + 1) :=
    funext fun k => propext (by omega)
  have hshape : TableShape.{u} ctab (· < 6 + 1) boolStore boolEnv := by
    have h := BoolInhabit.tableShape_bool.{u}
    rw [hset] at h
    exact h
  obtain ⟨hpin, hnone⟩ := opsPinned_of_names BoolInhabit.boolEnv_names ops_not_boolRoles
  have hfacts : BoundaryFacts ctab (· < 6 + 1) boolStore boolEnv :=
    { whole := hwhole
      opsPinned := hpin
      opsAdmitted := fun r hr hs => by
        rw [hnone r hr] at hs
        cases hs
      shapes := shapes_bool }
  exact bndOver_of_beforeRaise hall (by omega) ⟨hshape, hclause, hfacts, hraise⟩
    (fun E _ lim _ _ => guardAt_of_noTable boolEnv_noTable)

end IxVM.Refinement.Binding
