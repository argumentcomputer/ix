import IxVMRefinement.StatementRel.BoolRowStore
import IxVMRefinement.StatementRel.DefInhabit
import IxC.Kernel.Semantics.Inductives.DeclNative

/-! # An inhabitant of the table-validity shape with the `Bool` group

`tableShape_bool`: the default table is valid, in the public sense of `TableShape`, on the
basis and quotient groups and the `Bool` group (group 6), with the store of their 29
committed records and the environment that IxC's own executable check of the `Bool` block
installs at the basis environment.

* The block is read from its rows by the row reader (`boolBlock`: the type, the two
  constructors and the recursor, the recursor record folded into the block's declaration).
* The environment is IxC's: `nativeParts?` recognises the block, and the native check
  (`checkNative`, at fuel 16) passes at the basis environment and installs the four
  constants in front of the pins (`boolCheck`, evaluated). The kernel's step theorem gives
  the model (`boolEnv_ok`).
* Every record of the store with a reading reads as a constant the environment stores at
  its key (`bool_rowsOk`, evaluated): the pins for the basis rows, the installed constants
  for the `Bool` rows.

What this exercises that the earlier inhabitants do not: the `KeptIn` disjunct of the `kept`
and `preludeKept` fields, at roles whose constants are not pins (`Bool`, `Bool.false`,
`Bool.true`, `Bool.rec`), and a model step for an inductive block that is not a pin. Here
`kept`, `preludeKept` and `stored` hold through `KeptIn` and `StoredAs` at every role and
address of the seven groups; only `provenance` uses the pins, for the 19 pinned constants.
-/

universe u

namespace IxVM.Refinement.BoolInhabit

open Ix.Kernel
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.ClosedFacts
open IxVM.Refinement.TableInhabit
open IxVM.Refinement.StoreInhabit (isMutsInfo groups_closed preludePinned_default)
open IxVM.Refinement.RowReader
open IxVM.Refinement.RowsStore
open IxVM.Refinement.DefInhabit (basisEnv_ok)

/-! ## The run -/

/-- The value of a run, or `d` if it failed. -/
def okOr {ε : Type _} {α : Type _} (r : Except ε α) (d : α) : α :=
  match r with
  | .ok x => x
  | .error _ => d

theorem ok_okOr {ε : Type _} {α : Type _} {r : Except ε α} {d : α}
    (h : r.toBool = true) :
    r = .ok (okOr r d) := by
  cases r with
  | ok _ => rfl
  | error _ =>
    have h' : false = true := h
    cases h'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The block is not one of the kernel's pinned basis blocks (decided). -/
theorem boolBlock_notPin : (basisPinHit boolBlock).isNone = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- IxC's recogniser of directly installed blocks accepts the block (decided). -/
theorem boolParts_isSome : (nativeParts? 0 boolBlock).isSome = true := by decide +kernel

/-- **The block's parts for IxC's native check.** -/
def boolParts : NativeParts .anon := (nativeParts? 0 boolBlock).get boolParts_isSome

theorem boolParts_eq : nativeParts? 0 boolBlock = some boolParts :=
  (Option.some_get boolParts_isSome).symm

/-- **The environment**: what IxC's native check of the block installs at the basis
environment (its executable run at fuel 16). -/
def boolEnv : Env .anon :=
  okOr (checkNative (m := CheckM .anon) (fueledOps .verified 16) basisEnv boolParts) basisEnv

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **IxC's native check of the block passes at the basis environment** (its executable run
at fuel 16, evaluated). -/
theorem boolCheck_ok :
    (checkNative (m := CheckM .anon) (fueledOps .verified 16) basisEnv boolParts).toBool =
      true := by
  decide +kernel

theorem boolCheck :
    checkNative (m := CheckM .anon) (fueledOps .verified 16) basisEnv boolParts = .ok boolEnv :=
  ok_okOr boolCheck_ok

/-- **The kernel's run of the block's declaration**: not a pin, so the `.indDecl` dispatch,
which is the native route, whose run is the native check's. -/
theorem boolRun :
    Ix.Kernel.Semantics.DeclRun .verified 16
      (Ix.Kernel.Semantics.DeclIndRunDispatch .verified 16 basisEnv) basisEnv
      (.indDecl boolBlock 0) boolEnv := by
  have hpin : basisPinHit boolBlock = none := Option.isNone_iff_eq_none.mp boolBlock_notPin
  simp only [Ix.Kernel.Semantics.DeclRun, hpin, Ix.Kernel.Semantics.DeclIndRunDispatch,
    boolParts_eq]
  exact Ix.Kernel.Semantics.declNativeRun_of boolCheck

/-- **The environment carries the kernel's fold invariant**: the basis environment's, and one
step for the block. -/
theorem boolEnv_ok (W : Type u) [SetTheory W] :
    Ix.Kernel.Model.EnvModelOk W .verified boolEnv := by
  obtain ⟨⟨m⟩, hE⟩ := basisEnv_ok W
  exact Ix.Kernel.Model.declStep_preserves (F := 16) (d := .indDecl boolBlock 0) rfl m hE
    boolRun

/-! ## What the run installs -/

/-- The roles of the installed constants, front first. -/
def boolRoles : List Role := [.boolRec, .boolTrue, .boolFalse, .bool]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **What the run installs** (evaluated): four constants in front of the pins, keyed by the
four `Bool` roles, none of them a model-family constant. -/
theorem boolEnv_shape :
    (decide (boolEnv.consts.drop 4 = basisEnv.consts) &&
      decide ((boolEnv.consts.take 4).map (·.name) = boolRoles.map Key.role) &&
      boolEnv.consts.all (fun ci => !isModelAux ci)) = true := by
  decide +kernel

theorem boolEnv_drop : boolEnv.consts.drop 4 = basisEnv.consts := by
  have h := boolEnv_shape
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1

theorem boolEnv_take : (boolEnv.consts.take 4).map (·.name) = boolRoles.map Key.role := by
  have h := boolEnv_shape
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2

theorem boolEnv_noAux : boolEnv.consts.all (fun ci => !isModelAux ci) = true := by
  have h := boolEnv_shape
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem boolEnv_split : boolEnv.consts = boolEnv.consts.take 4 ++ basisEnv.consts := by
  rw [← boolEnv_drop, List.take_append_drop]

theorem boolEnv_names :
    boolEnv.consts.map (·.name) = (boolRoles ++ basisRoleOrder).map Key.role := by
  have hb : basisEnv.consts.map (·.name) = basisRoleOrder.map Key.role := rfl
  rw [boolEnv_split, List.map_append, boolEnv_take, hb, List.map_append]

theorem boolEnv_nodup : (boolEnv.consts.map (·.name)).Nodup :=
  roleNames_nodup (boolRoles ++ basisRoleOrder) boolEnv_names (by decide)

theorem boolEnv_filter : boolEnv.consts.filter (fun ci => !isModelAux ci) = boolEnv.consts :=
  List.filter_eq_self.mpr fun ci hci => List.all_eq_true.mp boolEnv_noAux ci hci

theorem env_eta (e : Env .anon) : (⟨e.consts⟩ : Env .anon) = e := rfl

theorem boolEnv_claimed : claimedEnv boolEnv = boolEnv :=
  (show claimedEnv boolEnv = ⟨boolEnv.consts.filter fun ci => !isModelAux ci⟩ from rfl).trans
    ((congrArg (Env.mk (md := .anon)) boolEnv_filter).trans (env_eta boolEnv))

theorem boolEnv_find_mem {ci : ConstantInfo .anon} (h : ci ∈ boolEnv.consts) :
    boolEnv.find? ci.name = some ci :=
  Ix.Cert.AcceptedKeys.find?_name_of_nodup (l := boolEnv.consts) boolEnv_nodup ci h

theorem boolEnv_pins : ∀ (kind : BasisKind),
    ∀ ci ∈ (kind.declsA : List (ConstantInfo .anon)), ci ∈ boolEnv.consts := by
  intro kind ci h
  rw [boolEnv_split]
  exact List.mem_append_right _ (basisEnv_pins kind ci h)

/-! ## The environment has a model -/

theorem boolEnv_model (W : Type u) [SetTheory W] :
    Nonempty (Ix.Kernel.Model W (claimedEnv boolEnv)) := by
  rw [boolEnv_claimed]
  exact model_of_envModelOk (boolEnv_ok W)

/-! ## The store's clauses -/

/-- The block of every row is a row (decided). -/
theorem bool_owners :
    boolRows.all (fun e => hasKeyIn boolRows (Ix.Cert.ownerOf e.1 e.2)) = true := by
  decide +kernel

/-- Every constant reference a row uses is a row (decided). -/
theorem bool_refs :
    boolRows.all (fun e =>
      (usedRefIdxs e.2).all fun i => (e.2.refs[i]?).all (hasKeyIn boolRows)) = true := by
  decide +kernel

/-- The zero address is not the address of a row (decided). -/
theorem bool_zero : hasKeyIn boolRows Ix.HostAdmission.Merkle.padding = false := by
  decide +kernel

/-- An axiom row sits at the address of a standard axiom's role. -/
def axiomOk (e : Row) : Bool :=
  match e.2.info with
  | .axio _ => axiomRoles.any fun r => decide (keyOf committedDefaultRoleTable e.1 = Key.role r)
  | _ => true

/-- The one axiom row, `Quot.sound`'s, sits at the address of a standard axiom's role
(decided). -/
theorem bool_axioms : boolRows.all axiomOk = true := by decide +kernel

theorem axiom_clause (a : _root_.Address) :
    ∀ c ax, recordOf boolStore a = some c → c.info = .axio ax →
      ∃ r ∈ axiomRoles, keyOf committedDefaultRoleTable a = .role r := by
  intro c ax hc hinfo
  have hmem := record_inv boolRows_committed hc
  have h1 : axiomOk (a, c) = true := List.all_eq_true.mp bool_axioms (a, c) hmem
  have h2 : (match c.info with
      | .axio _ => axiomRoles.any fun r =>
          decide (keyOf committedDefaultRoleTable a = Key.role r)
      | _ => true) = true := h1
  rw [hinfo] at h2
  have h3 : (axiomRoles.any fun r => decide (keyOf committedDefaultRoleTable a = Key.role r)) =
      true := h2
  obtain ⟨r, hr, hk⟩ := List.any_eq_true.mp h3
  exact ⟨r, hr, of_decide_eq_true hk⟩

/-! ## Every record reads as what the environment stores -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Every row that is not a block has a reading that the constant the environment holds at
its key stores** (decided: the reading is computed and `StoredAs` checked, row by row): the
pins for the 19 basis rows, the four installed constants for the `Bool` rows. -/
theorem bool_rowsOk :
    boolRowStore.rows.attach.all
      (fun x => isMutsInfo x.1.2.info || rowOk boolRowStore boolEnv x.1.1 x.1.2 x.2) = true := by
  decide +kernel

theorem bool_stored : ∀ a, (∃ ci₀, Reads committedDefaultRoleTable boolStore a ci₀) →
    ∃ ci, boolEnv.find? (keyOf committedDefaultRoleTable a) = some ci ∧
      (PinnedBasis ci ∨
        ∃ ci₀, Reads committedDefaultRoleTable boolStore a ci₀ ∧ StoredAs ci ci₀) := by
  intro a hr
  obtain ⟨ci, ci₀, hfind, hread, hst⟩ := reads_stored boolRowStore boolEnv bool_rowsOk a hr
  exact ⟨ci, hfind, Or.inr ⟨ci₀, hread, hst⟩⟩

/-- A role is bound at the address of a row that is not a block, and that address is keyed
by the role. -/
def roleRowOk (r : Role) : Bool :=
  match committedDefaultRoleTable.addressOf? r with
  | some a =>
    decide (keyOf committedDefaultRoleTable a = Key.role r) &&
      boolRows.any fun e => e.1 == a && !isMutsInfo e.2.info
  | none => false

/-- **Every role of the basis and quotient groups is bound at the address of a row that is not
a block, keyed by the role** (decided). -/
theorem basis_roles : (List.range 6).all (fun g => (roleGroup g).all roleRowOk) = true := by
  decide +kernel

/-- **Every role of the `Bool` group is bound at the address of a row that is not a block,
keyed by the role** (decided). -/
theorem bool_roles : (roleGroup 6).all roleRowOk = true := by
  decide +kernel

theorem roleRowOk_of {g : Nat} (hg : g < 6 ∨ g = 6) {r : Role} (hr : r ∈ roleGroup g) :
    roleRowOk r = true := by
  rcases hg with hg | hg
  · have h0 : (roleGroup g).all roleRowOk = true :=
      List.all_eq_true.mp basis_roles g (List.mem_range.mpr hg)
    exact List.all_eq_true.mp h0 r hr
  · subst hg
    exact List.all_eq_true.mp bool_roles r hr

/-- **At every role of the seven groups the environment keeps what the role's record
declares** (`KeptIn`): the record at the role's address reads, and the constant at the
role's key stores the reading. -/
theorem role_keptIn {g : Nat} (hg : g < 6 ∨ g = 6) {r : Role} (hr : r ∈ roleGroup g) :
    ∃ a ci, committedDefaultRoleTable.addressOf? r = some a ∧
      boolEnv.find? (Key.role r) = some ci ∧
      KeptIn committedDefaultRoleTable (recordOf boolStore) (fun x => boolStore.blobs.get? x)
        a ci := by
  have h1 : roleRowOk r = true := roleRowOk_of hg hr
  unfold roleRowOk at h1
  cases ha : committedDefaultRoleTable.addressOf? r with
  | none =>
    rw [ha] at h1
    have h' : false = true := h1
    cases h'
  | some a =>
    rw [ha] at h1
    have h2 : (decide (keyOf committedDefaultRoleTable a = Key.role r) &&
        boolRows.any fun e => e.1 == a && !isMutsInfo e.2.info) = true := h1
    simp only [Bool.and_eq_true] at h2
    obtain ⟨hk, hany⟩ := h2
    have hkey : keyOf committedDefaultRoleTable a = Key.role r := of_decide_eq_true hk
    obtain ⟨e, he, hea⟩ := List.any_eq_true.mp hany
    simp only [Bool.and_eq_true] at hea
    obtain ⟨hea1, hea2⟩ := hea
    have he1 : e.1 = a := beq_iff_eq.mp hea1
    have hmuts : isMutsInfo e.2.info = false := by
      cases hm : isMutsInfo e.2.info with
      | false => rfl
      | true =>
        rw [hm] at hea2
        cases hea2
    have hmem : (a, e.2) ∈ boolRowStore.rows := by
      rw [← he1]
      exact he
    have hF : (isMutsInfo e.2.info || rowOk boolRowStore boolEnv a e.2 hmem) = true :=
      List.all_eq_true.mp bool_rowsOk ⟨(a, e.2), hmem⟩ (List.mem_attach _ _)
    rw [hmuts, Bool.false_or] at hF
    obtain ⟨ci, ci₀, hfind, hread, hst⟩ := rowOk_spec boolRowStore boolEnv hF
    rw [hkey] at hfind
    refine ⟨a, ci, rfl, hfind, ?_⟩
    unfold KeptIn
    exact ⟨axiom_clause a, ci₀, hread, hst⟩

/-- The `Bool` roles are the roles of group 6 (decided). -/
theorem boolRoles_group : boolRoles.all (fun r => (roleGroup 6).contains r) = true := by
  decide +kernel

/-- The constants the run installs are kept at the `Bool` roles. -/
theorem installed_keptIn {ci : ConstantInfo .anon} (h : ci ∈ boolEnv.consts.take 4) :
    ∃ a, KeptIn committedDefaultRoleTable (recordOf boolStore) (fun x => boolStore.blobs.get? x)
      a ci := by
  have hn : ci.name ∈ boolRoles.map Key.role := by
    rw [← boolEnv_take]
    exact List.mem_map.mpr ⟨ci, h, rfl⟩
  obtain ⟨r, hr, hname⟩ := List.mem_map.mp hn
  have hg : r ∈ roleGroup 6 :=
    List.mem_of_elem_eq_true (List.all_eq_true.mp boolRoles_group r hr)
  obtain ⟨a, ci', -, hfind, hkept⟩ := role_keptIn (Or.inr rfl) hg
  have hci : ci ∈ boolEnv.consts := List.mem_of_mem_take h
  have hf : boolEnv.find? (Key.role r) = some ci := by
    rw [hname]
    exact boolEnv_find_mem hci
  have e : ci' = ci := Option.some.inj (hfind.symm.trans hf)
  rw [← e]
  exact ⟨a, hkept⟩

/-! ## The inhabitant -/

/-- **The default table is valid, in the public sense, on the basis and quotient groups and
the `Bool` group**, with the store of their 29 committed records and the environment IxC's
native check of the `Bool` block installs at the basis environment. -/
theorem tableShape_bool :
    TableShape.{u} committedDefaultRoleTable (fun g => g < 6 ∨ g = 6) boolStore boolEnv := {
  needsClosed := fun g hg r hr => by
    have hg' : g < 6 ∨ g = 6 := hg
    rcases hg' with hg' | hg'
    · have h1 : (groupNeeded g).all (fun r => decide (Ix.SpecDigest.groupOf r < 6)) = true :=
        List.all_eq_true.mp groups_closed g (List.mem_range.mpr hg')
      show Ix.SpecDigest.groupOf r < 6 ∨ Ix.SpecDigest.groupOf r = 6
      exact Or.inl (of_decide_eq_true (List.all_eq_true.mp h1 r hr))
    · have h6 : groupNeeded 6 = [] := by decide +kernel
      rw [hg', h6] at hr
      cases hr
  bound := fun _ _ r _ => defaultTable_allBound r
  prelude := preludePinned_default
  literals := committedDefaultRoleTable_literalSupportBound
  hashed := RowsStore.hashed boolRows_committed
  usedClosed := RowsStore.usedClosed boolRows_committed bool_projs_found bool_owners bool_refs
  committed := RowsStore.committed boolRows_committed
  zeroFree := RowsStore.zeroFree bool_zero
  kept := fun _ r a hg hr _ ha => by
    obtain ⟨a', ci, ha', hfind, hkept⟩ := role_keptIn hg hr
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    rw [← e]
    exact ⟨ci, hfind, Or.inr hkept⟩
  reading := {
    nodup := boolEnv_nodup
    provenance := fun ci hci => by
      rw [boolEnv_claimed] at hci
      rw [boolEnv_split] at hci
      rcases List.mem_append.mp hci with h | h
      · exact Or.inr (Or.inr (installed_keptIn h))
      · exact Or.inr (Or.inl (basisEnv_pinned ci h))
    stored := bool_stored }
  pins := boolEnv_pins
  preludeKept := fun _ r a hg hr _ ha => by
    obtain ⟨a', ci, ha', hfind, hkept⟩ := role_keptIn hg hr
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    rw [← e]
    exact ⟨ci, hfind, Or.inr hkept⟩
  model := fun W _ => boolEnv_model W }

end IxVM.Refinement.BoolInhabit
