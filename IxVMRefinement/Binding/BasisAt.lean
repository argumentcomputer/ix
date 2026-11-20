import IxVMRefinement.Binding.BasisAtTransfer
import IxVMRefinement.Binding.StoreCongr
import IxVMRefinement.Binding.Inhabit

/-! # The binding fold's base case at every table that pins the prelude

`bnd_basis_at`: the boundary invariant below group 6, at the store of the 24 committed basis
rows and the environment of the pins, for every role table `t` that is well formed
(`RoleTable.check`), pins the prelude (`PreludePinned`) and binds every role (`AllBound`).
`bnd_basis` (`Inhabit.lean`) is this at the committed default table only.

The proof transfers the default table's facts. The environment of the pins stores only the
keys of the nineteen basis roles, all prelude roles (decided). A well-formed table binds each
role at one address and each address to one role, and a table that pins the prelude binds the
basis roles where the default table does. So the two tables' keys agree at every address whose
key the environment stores (`keysAgree_basis`), and differ only where it stores nothing.

* The prefix invariant: the declaration layer's, store, unresolved-key and η fields do not
  read the table; the load contract carries over by `scopedLoadFacts_table`; the companions by
  `coreCompanions_table` (a stored recursor's major head and rule constructors are basis keys,
  decided); `roleRes` is proved at `t` as at the default table, and no projection table is
  stored.
* The public shape: the store clauses do not read the table; the kept and prelude clauses are
  the pins; `ReadingOf.stored` reads the key of a basis role's record, the same under `t`.
* `basisBase_at`: the fold's basis hypothesis (`BasisBase`) for every run whose table is well
  formed and pins the prelude and whose store after the basis groups has the basis rows'
  entries, through `bnd_storeCongr`.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.TableInhabit (basisEnv basisRoleOrder)
open IxVM.Refinement.StoreInhabit (basisStore)

/-! ## The companions under another table -/

/-- **The role and record companions of a prefix under another role table**: the role fields
transfer along the roles in force; the recursor fields along the keys of a stored recursor's
major head and of its rules' constructors. -/
theorem coreCompanions_table {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {t₁ t₂ : Ix.Kernel.RoleTable} {lim : Option Nat}
    (h : Decl.CoreCompanions ⟨E, env, t₁, lim⟩)
    (hin : ∀ r, Core.Ctx.inForce ⟨E, env, t₂, lim⟩ r → Core.Ctx.inForce ⟨E, env, t₁, lim⟩ r)
    (hmaj : ∀ (k : Core.KKey) cv mI rP rls (p : _root_.Address) (us : List Core.KLevel),
      env.find? k = some (.recInfo cv mI rP rls) →
      (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (Core.keyOf t₂ p) us) →
      Core.keyOf t₁ p = Core.keyOf t₂ p)
    (hctor : ∀ (k : Core.KKey) cv mI rP rls (rl : Ix.Kernel.RecRule .anon) (x : _root_.Address),
      env.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls → rl.ctor = Core.keyOf t₁ x →
      Core.keyOf t₂ x = Core.keyOf t₁ x) :
    Decl.CoreCompanions ⟨E, env, t₂, lim⟩ where
  natLit := fun h1 h2 h3 => h.natLit (hin _ h1) (hin _ h2) (hin _ h3)
  strLit := fun h1 => h.strLit (hin _ h1)
  natOps := fun r hr hm => h.natOps r (hin r hr) hm
  natAdd := fun h1 => h.natAdd (hin _ h1)
  eqStored := fun h1 => h.eqStored (hin _ h1)
  primEqn := fun ⟨r, hge, hf⟩ => h.primEqn ⟨r, hge, hin r hf⟩
  quotBasis := fun h1 => h.quotBasis (hin _ h1)
  recMajorRecord := fun k cv mI rP rls p us hf hne hdom =>
    h.recMajorRecord k cv mI rP rls p us hf hne
      (hdom.trans (congrArg (fun k' => (some (Ix.Kernel.Expr.const k' us) : Option Core.KExpr))
        (hmaj k cv mI rP rls p us hf hdom).symm))
  recRulesNodupAndProj := fun k cv mI rP rls hf => by
    obtain ⟨hnd, hpr⟩ := h.recRulesNodupAndProj k cv mI rP rls hf
    refine ⟨hnd, fun p cm ip us hdom hrec hcm j rl hj => ?_⟩
    have r1 := hpr p cm ip us
      (hdom.trans (congrArg (fun k' => (some (Ix.Kernel.Expr.const k' us) : Option Core.KExpr))
        (hmaj k cv mI rP rls p us hf hdom).symm)) hrec hcm j rl hj
    exact r1.trans (hctor k cv mI rP rls rl _ hf (List.mem_of_getElem? hj) r1).symm
  recPlain := h.recPlain
  ruleCtorHead := h.ruleCtorHead

/-- A role in force under one table is in force under a table that binds every role. -/
theorem inForce_of_allBound {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {t₁ t₂ : Ix.Kernel.RoleTable} {lim : Option Nat} (hb : AllBound t₁) (r : Ix.Kernel.Role)
    (h : Core.Ctx.inForce ⟨E, env, t₂, lim⟩ r) : Core.Ctx.inForce ⟨E, env, t₁, lim⟩ r :=
  ⟨hb r, h.2⟩

/-! ## The keys of a table that pins the prelude -/

/-- Every basis role is a prelude role (decided). -/
theorem basisRoles_prelude : ∀ r ∈ basisRoleOrder, r ∈ preludeRoles := by decide

/-- No operation is a basis role (decided). -/
theorem ops_not_basisRoles : ∀ r ∈ RoleOps.opRoles, r ∉ basisRoleOrder := by decide

/-- The constructor of every rule of a stored recursor is a basis role's key (decided). -/
theorem basisEnv_ruleCtorKeys :
    basisEnv.consts.all (fun ci => match ci with
      | .recInfo _ _ _ rls => rls.all fun rl => StoreInhabit.isBasisKey rl.ctor
      | _ => true) = true := by
  decide +kernel

section
variable {t : Ix.Kernel.RoleTable}

theorem wf_of_check (ht : t.check = .ok ()) : t.wf = true := by
  unfold Ix.Kernel.RoleTable.wf
  rw [ht]
  rfl

/-- **A table that pins the prelude binds every basis role where the default table does.** -/
theorem addressOf_basis (hpre : PreludePinned t) {r : Ix.Kernel.Role}
    (hr : r ∈ basisRoleOrder) : t.addressOf? r = ctab.addressOf? r := by
  obtain ⟨b₀, t₀, hdef, hadm, hpin⟩ := hpre
  have ht₀ : t₀ = RoleVal.committedDefaultRoleTable :=
    RoleVal.admitBinding_committedDefault hdef hadm
  rw [hpin r (basisRoles_prelude r hr), ht₀]

/-- **A basis role's key names the same address under both tables.** -/
theorem keyOf_basis (ht : t.check = .ok ()) (hpre : PreludePinned t) {r : Ix.Kernel.Role}
    (hr : r ∈ basisRoleOrder) {x : _root_.Address} :
    Core.keyOf t x = .role r ↔ Core.keyOf ctab x = .role r := by
  constructor
  · intro h
    have ha := Core.addressOf_of_keyOf (wf_of_check ht) h
    rw [addressOf_basis hpre hr] at ha
    exact Core.keyOf_of_addressOf committedTable_wf ha
  · intro h
    have ha := Core.addressOf_of_keyOf committedTable_wf h
    rw [← addressOf_basis hpre hr] at ha
    exact Core.keyOf_of_addressOf (wf_of_check ht) ha

/-- **The keys of the default table and `t` agree wherever the environment of the pins stores
one of them.** -/
theorem keysAgree_basis (ht : t.check = .ok ()) (hpre : PreludePinned t) :
    KeysAgree basisEnv ctab t := by
  intro x ci h
  rcases h with h | h
  · obtain ⟨r, hr, hk⟩ := basisEnv_find_role h
    rw [hk]
    exact ((keyOf_basis ht hpre hr).mpr hk).symm
  · obtain ⟨r, hr, hk⟩ := basisEnv_find_role h
    rw [hk]
    exact (keyOf_basis ht hpre hr).mp hk

theorem keyOf_basis' (ht : t.check = .ok ()) (hpre : PreludePinned t) {r : Ix.Kernel.Role}
    (hr : r ∈ basisRoleOrder) {x : _root_.Address} :
    keyOf t x = .role r ↔ keyOf ctab x = .role r := by
  rw [← LoadedReads.keyOf_eq, ← LoadedReads.keyOf_eq]
  exact keyOf_basis ht hpre hr

theorem find_keyOf_basis (ht : t.check = .ok ()) (hpre : PreludePinned t) (x : _root_.Address) :
    basisEnv.find? (keyOf t x) = basisEnv.find? (keyOf ctab x) := by
  rw [← LoadedReads.keyOf_eq, ← LoadedReads.keyOf_eq]
  exact ((keysAgree_basis ht hpre).find x).symm

/-- The head of a stored recursor's major premise has one key under both tables. -/
theorem majorHead_keys (ht : t.check = .ok ()) (hpre : PreludePinned t) :
    ∀ (k : Core.KKey) cv mI rP rls (p : _root_.Address) (us : List Core.KLevel),
      basisEnv.find? k = some (.recInfo cv mI rP rls) →
      (Core.piDomAt mI cv.type).map (·.getAppFn) = some (.const (Core.keyOf t p) us) →
      Core.keyOf ctab p = Core.keyOf t p := by
  intro k cv mI rP rls p us hf hdom
  have h1 := List.all_eq_true.mp basisEnv_majorHeads _ (basisEnv_find_mem hf).1
  simp only [hdom] at h1
  obtain ⟨r, hr, hk⟩ := StoreInhabit.isBasisKey_role h1
  rw [hk]
  exact (keyOf_basis ht hpre hr).mp hk

/-- The constructor of a stored recursor's rule has one key under both tables. -/
theorem ruleCtor_keys (ht : t.check = .ok ()) (hpre : PreludePinned t) :
    ∀ (k : Core.KKey) cv mI rP rls (rl : Ix.Kernel.RecRule .anon) (x : _root_.Address),
      basisEnv.find? k = some (.recInfo cv mI rP rls) → rl ∈ rls →
      rl.ctor = Core.keyOf ctab x → Core.keyOf t x = Core.keyOf ctab x := by
  intro k cv mI rP rls rl x hf hrl hx
  have h1 := List.all_eq_true.mp basisEnv_ruleCtorKeys _ (basisEnv_find_mem hf).1
  have h2 : rls.all (fun rl => StoreInhabit.isBasisKey rl.ctor) = true := h1
  have h3 : StoreInhabit.isBasisKey rl.ctor = true := List.all_eq_true.mp h2 rl hrl
  rw [hx] at h3
  obtain ⟨r, hr, hk⟩ := StoreInhabit.isBasisKey_role h3
  rw [hk]
  exact (keyOf_basis ht hpre hr).mpr hk

/-! ## The prefix invariant at `t` -/

/-- The environment of the pins stores no projection table: its names are role keys. -/
theorem basisEnv_noProjTable (k : Ix.Kernel.Key .anon) (tbl : Ix.Kernel.ProjTable .anon) :
    basisEnv.find? k ≠ some (.projInfo tbl) := by
  intro h
  obtain ⟨r, -, hk⟩ := basisEnv_find_role h
  have hn := (basisEnv_find_mem h).2
  have hname : (Ix.Kernel.ConstantInfo.projInfo tbl).name =
      Ix.Kernel.Key.aux tbl.structName .projTable := rfl
  rw [hname, hk] at hn
  cases hn

/-- **A fabricated role in force is stored**, under `t`, at a limit within the six basis
groups. -/
theorem roleRes_basis_at (ht : t.check = .ok ()) {E : Ixon.Env} {lim : Option Nat}
    (hlim : LimWithin (· < 6) t lim) :
    RoleResAt (Core.Ctx.stored ⟨E, basisEnv, t, lim⟩) := by
  intro r a hf hfab ha
  have hg : Ix.SpecDigest.groupOf r < 6 := hlim r hf.1 hf.2
  obtain ⟨ci, hci, -⟩ := StoreInhabit.basisEnv_find (fabricated_basis r hfab hg)
  have hk : Core.keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf (wf_of_check ht) ha
  have hci' : basisEnv.find? (Core.keyOf t a) = some ci := by
    rw [hk]
    exact hci
  rw [Core.Ctx.stored_key_of_find (c := ⟨E, basisEnv, t, lim⟩) hci']
  exact Core.Resolved.ne

/-- **The prefix invariant of the environment of the pins under `t`**, for every store of the
basis records and every limit within the six basis groups. -/
theorem prefixInv_basis_at (ht : t.check = .ok ()) (hpre : PreludePinned t)
    (hall : AllBound t) {E : Ixon.Env} (hE : RecordsFor basisStore E) {lim : Option Nat}
    (hlim : LimWithin (· < 6) t lim) : Decl.PrefixInv.{u} E t lim basisEnv := by
  have hlim' : LimWithin (· < 6) ctab lim := fun r _ hl => hlim r (hall r) hl
  have h := basis_facts.{u}.inv E hE lim hlim'
  exact {
    decl := h.decl
    store := h.store
    unresolved := h.unresolved
    tableWf := wf_of_check ht
    companions := coreCompanions_table h.companions
      (inForce_of_allBound ClosedFacts.defaultTable_allBound)
      (majorHead_keys ht hpre) (ruleCtor_keys ht hpre)
    loads := scopedLoadFacts_table (keysAgree_basis ht hpre) h.loads (roleRes_basis_at ht hlim)
      (Core.projTablesFire_of_noTable fun k tbl => basisEnv_noProjTable _ tbl)
    etaStable := h.etaStable }

/-! ## The public shape at `t` -/

theorem store_stored_at (ht : t.check = .ok ()) (hpre : PreludePinned t) :
    ∀ a, (∃ ci₀, Reads t basisStore a ci₀) →
      ∃ ci, basisEnv.find? (keyOf t a) = some ci ∧
        (PinnedBasis ci ∨ ∃ ci₀, Reads t basisStore a ci₀ ∧ StoredAs ci ci₀) := by
  intro a hr
  obtain ⟨_, c, hc, hread⟩ := hr
  have hmem := StoreInhabit.store_record_inv hc
  have hF : (StoreInhabit.isMutsInfo c.info || StoreInhabit.isBasisKey (keyOf ctab a)) = true :=
    List.all_eq_true.mp StoreInhabit.keys_pinned (a, c) hmem
  have key : ∃ r ∈ basisRoleOrder, keyOf ctab a = .role r := by
    generalize c.info = info at hread hF
    cases info <;> first
      | exact False.elim hread
      | exact StoreInhabit.isBasisKey_role (k := keyOf ctab a) hF
  obtain ⟨r, hrole, hkey⟩ := key
  obtain ⟨ci, hfind, hpin⟩ := StoreInhabit.basisEnv_find hrole
  rw [(keyOf_basis' ht hpre hrole).mpr hkey]
  exact ⟨ci, hfind, Or.inl hpin⟩

/-- **The public shape of the basis at `t`.** -/
theorem tableShape_basis_at (ht : t.check = .ok ()) (hpre : PreludePinned t)
    (hall : AllBound t) : TableShape.{u} t (· < 6) basisStore basisEnv where
  needsClosed := fun g hg r hr => by
    have h1 : (groupNeeded g).all (fun r => decide (Ix.SpecDigest.groupOf r < 6)) = true :=
      List.all_eq_true.mp StoreInhabit.groups_closed g (List.mem_range.mpr hg)
    have h2 : decide (Ix.SpecDigest.groupOf r < 6) = true := List.all_eq_true.mp h1 r hr
    exact of_decide_eq_true h2
  bound := fun _ _ r _ => hall r
  prelude := hpre
  literals := fun _ r _ => hall r
  hashed := StoreInhabit.store_hashed
  usedClosed := StoreInhabit.store_usedClosed
  committed := StoreInhabit.store_committed
  zeroFree := StoreInhabit.store_zeroFree
  kept := fun _ _ _ hg hr _ _ => by
    obtain ⟨ci, hfind, hpin⟩ := StoreInhabit.basisEnv_find (StoreInhabit.groupRole_basis hg hr)
    exact ⟨ci, hfind, Or.inl hpin⟩
  reading := {
    nodup := TableInhabit.basisEnv_nodup
    provenance := fun ci hci => by
      rw [TableInhabit.basisEnv_claimed] at hci
      exact Or.inr (Or.inl (TableInhabit.basisEnv_pinned ci hci))
    stored := store_stored_at ht hpre }
  pins := TableInhabit.basisEnv_pins
  preludeKept := fun _ _ _ hg hr _ _ => by
    obtain ⟨ci, hfind, hpin⟩ := StoreInhabit.basisEnv_find (StoreInhabit.groupRole_basis hg hr)
    exact ⟨ci, hfind, Or.inl hpin⟩
  model := fun W _ => by
    rw [TableInhabit.basisEnv_claimed]
    exact TableInhabit.basisEnv_model W

/-! ## The internal part at `t` -/

theorem blockStored_basis_at (ht : t.check = .ok ()) (hpre : PreludePinned t)
    {B : _root_.Address} {ms : Array Ixon.MutConst} (h : BlockStored ctab basisEnv B ms) :
    BlockStored t basisEnv B ms := by
  intro i m hm
  obtain ⟨h1, h2⟩ := h i m hm
  refine ⟨?_, fun ind j hind hj => ?_⟩
  · rw [find_keyOf_basis ht hpre]
    exact h1
  · rw [find_keyOf_basis ht hpre]
    exact h2 ind j hind hj

/-- **The internal part of the invariant below group 6 at `t`.** -/
theorem bfacts_basis_at (ht : t.check = .ok ()) (hpre : PreludePinned t) (hall : AllBound t) :
    BFacts.{u} t (· < 6) basisStore basisEnv := by
  obtain ⟨hpin, hnone⟩ := opsPinned_of_names basisEnv_names ops_not_basisRoles
  exact {
    inv := fun E hE lim _ hlim => prefixInv_basis_at ht hpre hall hE hlim
    whole := fun E hE a B c cb ms hfa hra hown hne hrB hms =>
      blockStored_basis_at ht hpre (basis_facts.{0}.whole E hE a B c cb ms
        (by rw [← find_keyOf_basis ht hpre]; exact hfa) hra hown hne hrB hms)
    opsPinned := hpin
    opsAdmitted := fun r hr hs => by
      rw [hnone r hr] at hs
      cases hs
    shapes := shapes_below_six basisEnv }

end

/-! ## The base case -/

/-- **(T1a) The boundary invariant below group 6 at every well-formed table that pins the
prelude and binds every role**, the store of the basis rows and the environment of the pins. -/
theorem bnd_basis_at
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) (hpre : PreludePinned t)
    (hall : AllBound t) (hX : X t (· < 6) StoreInhabit.basisStore TableInhabit.basisEnv) :
    Bnd.{u} X t (· < 6) StoreInhabit.basisStore TableInhabit.basisEnv :=
  ⟨tableShape_basis_at ht hpre hall, bfacts_basis_at ht hpre hall, hX⟩

/-- **The fold's basis hypothesis** for every run whose table is well formed and pins the
prelude and whose store after the basis groups has the basis rows' entries, given that the
extra clause depends on that store only through its entries and holds at the basis. -/
theorem basisBase_at
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (hrun : ∀ t ρ Rs, Run t ρ Rs →
      t.check = .ok () ∧ PreludePinned t ∧
        (∀ a, (Rs 6).consts.get? a = basisStore.consts.get? a) ∧
        ∀ a, (Rs 6).blobs.get? a = basisStore.blobs.get? a)
    (hXc : ∀ t (R : Ixon.Env), (∀ a, basisStore.consts.get? a = R.consts.get? a) →
      (∀ a, basisStore.blobs.get? a = R.blobs.get? a) →
      X t (· < 6) basisStore basisEnv → X t (· < 6) R basisEnv)
    (hXb : ∀ t, t.check = .ok () → PreludePinned t → AllBound t →
      X t (· < 6) basisStore basisEnv) :
    BasisBase.{u} X Run := by
  intro t ρ Rs hr hall
  obtain ⟨ht, hpre, hc, hb⟩ := hrun t ρ Rs hr
  have hc' : ∀ a, basisStore.consts.get? a = (Rs 6).consts.get? a := fun a => (hc a).symm
  have hb' : ∀ a, basisStore.blobs.get? a = (Rs 6).blobs.get? a := fun a => (hb a).symm
  exact ⟨basisEnv, bnd_storeCongr hc' hb' (hXc t (Rs 6) hc' hb')
    (bnd_basis_at ht hpre hall (hXb t ht hpre hall))⟩

/-- `basisBase_at` with no extra clause. -/
theorem basisBase_at_true {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (hrun : ∀ t ρ Rs, Run t ρ Rs →
      t.check = .ok () ∧ PreludePinned t ∧
        (∀ a, (Rs 6).consts.get? a = basisStore.consts.get? a) ∧
        ∀ a, (Rs 6).blobs.get? a = basisStore.blobs.get? a) :
    BasisBase.{u} (fun _ _ _ _ => True) Run :=
  basisBase_at hrun (fun _ _ _ _ _ => trivial) (fun _ _ _ _ => trivial)

/-- **The run hypothesis of `basisBase_at` is satisfiable**: it holds of the runs at the
default table whose store after the basis groups is the basis store. -/
theorem basisBase_at_default :
    BasisBase.{u} (fun _ _ _ _ => True) (fun t _ Rs => t = ctab ∧ Rs 6 = basisStore) :=
  basisBase_at_true fun t _ Rs hr => by
    obtain ⟨ht, hR⟩ := hr
    subst ht
    rw [hR]
    exact ⟨RoleVal.committedDefaultRoleTable_check, StoreInhabit.preludePinned_default,
      fun _ => rfl, fun _ => rfl⟩

end IxVM.Refinement.Binding
