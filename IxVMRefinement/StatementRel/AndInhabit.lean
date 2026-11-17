import IxVMRefinement.StatementRel.BoolInhabit

/-! # An inhabitant of the table-validity shape with the `Bool` and `And` groups

`tableShape_and`: the default table is valid, in the public sense of `TableShape`, on the
basis and quotient groups, the `Bool` group (11) and the `And` group (20), with the store of
all 33 committed prelude records and the environment that IxC's own executable check of the
`And` block installs at the environment of `BoolInhabit.tableShape_bool`.

* The `And` block is read from its rows by the row reader (`andBlock`: the type, the
  constructor and the recursor; two parameters).
* The environment is IxC's: the native check (`checkNative`, at fuel 16) passes at
  `boolEnv` and installs four constants in front of it: `And`, `And.intro`, `And.rec` and the
  structure's projection table (`andCheck`, evaluated). The kernel's step theorem gives the
  model (`andEnv_ok`).
* Every record of the store with a reading reads as a constant the environment stores at its
  key (`and_rowsOk`, evaluated).

What this exercises beyond `tableShape_bool`: a second non-pinned inductive group, on top of
the first; an inductive block with parameters; and the projection-table disjunct of
`ReadingOf.provenance`, which no earlier inhabitant reaches.
-/

universe u

namespace IxVM.Refinement.AndInhabit

open Ix.Kernel
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.ClosedFacts
open IxVM.Refinement.TableInhabit
open IxVM.Refinement.StoreInhabit (isMutsInfo groups_closed preludePinned_default)
open IxVM.Refinement.RowReader
open IxVM.Refinement.RowsStore
open IxVM.Refinement.BoolInhabit (okOr ok_okOr env_eta boolEnv boolEnv_ok boolEnv_split
  boolEnv_take boolRoles boolRoles_group axiomOk)

/-! ## The store: all 33 committed prelude records -/

/-- **The rows**: the 33 committed prelude records (the basis and quotient rows, then the
`And` block's four rows, then the `Bool` block's five). -/
def andRows : List Row := committedPreludeList

/-- The rows are at distinct addresses (decided). -/
theorem andEntries_distinct :
    (entriesOf andRows).Pairwise (fun a b => (a.1 == b.1) = false) := by
  decide +kernel

theorem andRows_committed : Committed andRows := ⟨andEntries_distinct, fun _ h => h⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- Every projection record of a block among the rows is one of the rows (by evaluation: the
row found is the projection record, term for term). -/
theorem and_projs_found :
    (expectedProjsOf andRows).map (fun p => (findProjOf andRows p).map (·.2)) =
      (expectedProjsOf andRows).map some :=
  rfl

/-- **The store.** -/
def andStore : Ixon.Env := rowsEnv andRows

/-- **The store, as a store of rows.** -/
def andRowStore : RowStore committedDefaultRoleTable :=
  rowStoreOf andRows andRows_committed and_projs_found

/-- What the row at position `i` declares, if it declares something. -/
def andReadingAt (i : Nat) : Option (ConstantInfo .anon) :=
  (andRowStore.rows.attach[i]?).bind fun x => (readRow andRowStore x.1.1 x.1.2 x.2).map (·.1)

/-- **The `And` block, as read from its rows**: the type, the constructor and the recursor
(rows 25 to 27; row 24 is the block record, which declares nothing). -/
def andBlock : List (ConstantInfo .anon) := [25, 26, 27].filterMap andReadingAt

/-! ## The run -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The block is not one of the kernel's pinned basis blocks (decided). -/
theorem andBlock_notPin : (basisPinHit andBlock).isNone = true := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- IxC's recogniser of directly installed blocks accepts the block, with its two parameters
(decided). -/
theorem andParts_isSome : (nativeParts? 2 andBlock).isSome = true := by decide +kernel

/-- **The block's parts for IxC's native check.** -/
def andParts : NativeParts .anon := (nativeParts? 2 andBlock).get andParts_isSome

theorem andParts_eq : nativeParts? 2 andBlock = some andParts :=
  (Option.some_get andParts_isSome).symm

/-- **The environment**: what IxC's native check of the `And` block installs at the
environment of the `Bool` inhabitant (its executable run at fuel 16). -/
def andEnv : Env .anon :=
  okOr (checkNative (m := CheckM .anon) (fueledOps .verified 16) boolEnv andParts) boolEnv

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **IxC's native check of the block passes at `boolEnv`** (its executable run at fuel 16,
evaluated). -/
theorem andCheck_ok :
    (checkNative (m := CheckM .anon) (fueledOps .verified 16) boolEnv andParts).toBool =
      true := by
  decide +kernel

theorem andCheck :
    checkNative (m := CheckM .anon) (fueledOps .verified 16) boolEnv andParts = .ok andEnv :=
  ok_okOr andCheck_ok

/-- **The kernel's run of the block's declaration**: not a pin, so the `.indDecl` dispatch,
which is the native route, whose run is the native check's. -/
theorem andRun :
    Ix.Kernel.Semantics.DeclRun .verified 16
      (Ix.Kernel.Semantics.DeclIndRunDispatch .verified 16 boolEnv) boolEnv
      (.indDecl andBlock 2) andEnv := by
  have hpin : basisPinHit andBlock = none := Option.isNone_iff_eq_none.mp andBlock_notPin
  simp only [Ix.Kernel.Semantics.DeclRun, hpin, Ix.Kernel.Semantics.DeclIndRunDispatch,
    andParts_eq]
  exact Ix.Kernel.Semantics.declNativeRun_of andCheck

/-- **The environment carries the kernel's fold invariant**: `boolEnv`'s, and one step for
the block. -/
theorem andEnv_ok (W : Type u) [SetTheory W] :
    Ix.Kernel.Model.EnvModelOk W .verified andEnv := by
  obtain ⟨⟨m⟩, hE⟩ := boolEnv_ok W
  exact Ix.Kernel.Model.declStep_preserves (F := 16) (d := .indDecl andBlock 2) rfl m hE
    andRun

/-! ## What the run installs -/

/-- The roles of the `And` group. -/
def andRoles : List Role := [.andRec, .andIntro, .and]

/-- A projection table. -/
def isProjInfo : ConstantInfo .anon → Bool
  | .projInfo _ => true
  | _ => false

theorem projInfo_of {ci : ConstantInfo .anon} (h : isProjInfo ci = true) :
    ∃ tbl, ci = .projInfo tbl := by
  cases ci with
  | projInfo tbl => exact ⟨tbl, rfl⟩
  | _ =>
    have h' : false = true := h
    cases h'

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **What the run installs** (evaluated): four constants in front of `boolEnv`, each a
projection table or keyed by a role of the `And` group; the names of the whole environment
are distinct; none of its constants is a model-family constant. -/
theorem andEnv_shape :
    (decide (andEnv.consts.drop 4 = boolEnv.consts) &&
      (andEnv.consts.take 4).all (fun ci =>
        isProjInfo ci || andRoles.any fun r => decide (ci.name = Key.role r)) &&
      decide ((andEnv.consts.map (·.name)).Nodup) &&
      andEnv.consts.all (fun ci => !isModelAux ci)) = true := by
  decide +kernel

theorem andEnv_drop : andEnv.consts.drop 4 = boolEnv.consts := by
  have h := andEnv_shape
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1

theorem andEnv_new : (andEnv.consts.take 4).all (fun ci =>
    isProjInfo ci || andRoles.any fun r => decide (ci.name = Key.role r)) = true := by
  have h := andEnv_shape
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem andEnv_nodup : (andEnv.consts.map (·.name)).Nodup := by
  have h := andEnv_shape
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.2

theorem andEnv_noAux : andEnv.consts.all (fun ci => !isModelAux ci) = true := by
  have h := andEnv_shape
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem andEnv_split : andEnv.consts = andEnv.consts.take 4 ++ boolEnv.consts := by
  rw [← andEnv_drop, List.take_append_drop]

theorem andEnv_filter : andEnv.consts.filter (fun ci => !isModelAux ci) = andEnv.consts :=
  List.filter_eq_self.mpr fun ci hci => List.all_eq_true.mp andEnv_noAux ci hci

theorem andEnv_claimed : claimedEnv andEnv = andEnv :=
  (show claimedEnv andEnv = ⟨andEnv.consts.filter fun ci => !isModelAux ci⟩ from rfl).trans
    ((congrArg (Env.mk (md := .anon)) andEnv_filter).trans (env_eta andEnv))

theorem andEnv_find_mem {ci : ConstantInfo .anon} (h : ci ∈ andEnv.consts) :
    andEnv.find? ci.name = some ci :=
  Ix.Cert.AcceptedKeys.find?_name_of_nodup (l := andEnv.consts) andEnv_nodup ci h

theorem andEnv_pins : ∀ (kind : BasisKind),
    ∀ ci ∈ (kind.declsA : List (ConstantInfo .anon)), ci ∈ andEnv.consts := by
  intro kind ci h
  rw [andEnv_split, boolEnv_split]
  exact List.mem_append_right _ (List.mem_append_right _ (basisEnv_pins kind ci h))

theorem andEnv_model (W : Type u) [SetTheory W] :
    Nonempty (Ix.Kernel.Model W (claimedEnv andEnv)) := by
  rw [andEnv_claimed]
  exact model_of_envModelOk (andEnv_ok W)

/-! ## The store's clauses -/

/-- The block of every row is a row (decided). -/
theorem and_owners :
    andRows.all (fun e => hasKeyIn andRows (Ix.Cert.ownerOf e.1 e.2)) = true := by
  decide +kernel

/-- Every constant reference a row uses is a row (decided). -/
theorem and_refs :
    andRows.all (fun e =>
      (usedRefIdxs e.2).all fun i => (e.2.refs[i]?).all (hasKeyIn andRows)) = true := by
  decide +kernel

/-- The zero address is not the address of a row (decided). -/
theorem and_zero : hasKeyIn andRows Ix.HostAdmission.Merkle.padding = false := by
  decide +kernel

/-- The one axiom row, `Quot.sound`'s, sits at the address of a standard axiom's role
(decided). -/
theorem and_axioms : andRows.all axiomOk = true := by decide +kernel

theorem axiom_clause (a : _root_.Address) :
    ∀ c ax, recordOf andStore a = some c → c.info = .axio ax →
      ∃ r ∈ axiomRoles, keyOf committedDefaultRoleTable a = .role r := by
  intro c ax hc hinfo
  have hmem := record_inv andRows_committed hc
  have h1 : axiomOk (a, c) = true := List.all_eq_true.mp and_axioms (a, c) hmem
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
pins for the 19 basis rows, the installed constants for the `And` and `Bool` rows. -/
theorem and_rowsOk :
    andRowStore.rows.attach.all
      (fun x => isMutsInfo x.1.2.info || rowOk andRowStore andEnv x.1.1 x.1.2 x.2) = true := by
  decide +kernel

theorem and_stored : ∀ a, (∃ ci₀, Reads committedDefaultRoleTable andStore a ci₀) →
    ∃ ci, andEnv.find? (keyOf committedDefaultRoleTable a) = some ci ∧
      (PinnedBasis ci ∨
        ∃ ci₀, Reads committedDefaultRoleTable andStore a ci₀ ∧ StoredAs ci ci₀) := by
  intro a hr
  obtain ⟨ci, ci₀, hfind, hread, hst⟩ := reads_stored andRowStore andEnv and_rowsOk a hr
  exact ⟨ci, hfind, Or.inr ⟨ci₀, hread, hst⟩⟩

/-- A role is bound at the address of a row that is not a block, and that address is keyed
by the role. -/
def roleRowOk (r : Role) : Bool :=
  match committedDefaultRoleTable.addressOf? r with
  | some a =>
    decide (keyOf committedDefaultRoleTable a = Key.role r) &&
      andRows.any fun e => e.1 == a && !isMutsInfo e.2.info
  | none => false

/-- The groups of the witness. -/
abbrev InGroups (g : Nat) : Prop := g < 6 ∨ g = 6 ∨ g = 15

/-- **Every role of the basis and quotient groups is bound at the address of a row that is not
a block, keyed by the role** (decided). -/
theorem basis_roles : (List.range 6).all (fun g => (roleGroup g).all roleRowOk) = true := by
  decide +kernel

/-- **The same for the `Bool` and `And` groups** (decided). -/
theorem boolAnd_roles :
    ((roleGroup 6).all roleRowOk && (roleGroup 15).all roleRowOk) = true := by
  decide +kernel

theorem roleRowOk_of {g : Nat} (hg : InGroups g) {r : Role} (hr : r ∈ roleGroup g) :
    roleRowOk r = true := by
  have hba := boolAnd_roles
  simp only [Bool.and_eq_true] at hba
  rcases hg with hg | hg | hg
  · have h0 : (roleGroup g).all roleRowOk = true :=
      List.all_eq_true.mp basis_roles g (List.mem_range.mpr hg)
    exact List.all_eq_true.mp h0 r hr
  · subst hg
    exact List.all_eq_true.mp hba.1 r hr
  · subst hg
    exact List.all_eq_true.mp hba.2 r hr

/-- **At every role of the eight groups the environment keeps what the role's record
declares** (`KeptIn`): the record at the role's address reads, and the constant at the
role's key stores the reading. -/
theorem role_keptIn {g : Nat} (hg : InGroups g) {r : Role} (hr : r ∈ roleGroup g) :
    ∃ a ci, committedDefaultRoleTable.addressOf? r = some a ∧
      andEnv.find? (Key.role r) = some ci ∧
      KeptIn committedDefaultRoleTable (recordOf andStore) (fun x => andStore.blobs.get? x)
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
        andRows.any fun e => e.1 == a && !isMutsInfo e.2.info) = true := h1
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
    have hmem : (a, e.2) ∈ andRowStore.rows := by
      rw [← he1]
      exact he
    have hF : (isMutsInfo e.2.info || rowOk andRowStore andEnv a e.2 hmem) = true :=
      List.all_eq_true.mp and_rowsOk ⟨(a, e.2), hmem⟩ (List.mem_attach _ _)
    rw [hmuts, Bool.false_or] at hF
    obtain ⟨ci, ci₀, hfind, hread, hst⟩ := rowOk_spec andRowStore andEnv hF
    rw [hkey] at hfind
    refine ⟨a, ci, rfl, hfind, ?_⟩
    unfold KeptIn
    exact ⟨axiom_clause a, ci₀, hread, hst⟩

/-- The `And` roles are the roles of group 15 (decided). -/
theorem andRoles_group : andRoles.all (fun r => (roleGroup 15).contains r) = true := by
  decide +kernel

/-- A constant of the environment keyed by a role of the eight groups is kept at that role. -/
theorem keptIn_of_role {ci : ConstantInfo .anon} (hci : ci ∈ andEnv.consts) {g : Nat}
    (hg : InGroups g) {r : Role} (hr : r ∈ roleGroup g) (hname : Key.role r = ci.name) :
    ∃ a, KeptIn committedDefaultRoleTable (recordOf andStore) (fun x => andStore.blobs.get? x)
      a ci := by
  obtain ⟨a, ci', -, hfind, hkept⟩ := role_keptIn hg hr
  have hf : andEnv.find? (Key.role r) = some ci := by
    rw [hname]
    exact andEnv_find_mem hci
  have e : ci' = ci := Option.some.inj (hfind.symm.trans hf)
  rw [← e]
  exact ⟨a, hkept⟩

/-- **Every constant of the environment is a projection table, a pin, or kept at a role of
the eight groups.** -/
theorem and_provenance : ∀ ci ∈ (claimedEnv andEnv).consts,
    (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
      ∃ a, KeptIn committedDefaultRoleTable (recordOf andStore)
        (fun x => andStore.blobs.get? x) a ci := by
  intro ci hci
  rw [andEnv_claimed] at hci
  have hmem := hci
  rw [andEnv_split, boolEnv_split] at hci
  rcases List.mem_append.mp hci with h | h
  · have h1 : (isProjInfo ci || andRoles.any fun r => decide (ci.name = Key.role r)) = true :=
      List.all_eq_true.mp andEnv_new ci h
    cases hp : isProjInfo ci with
    | true => exact Or.inl (projInfo_of hp)
    | false =>
      rw [hp, Bool.false_or] at h1
      obtain ⟨r, hr, hn⟩ := List.any_eq_true.mp h1
      have hg : r ∈ roleGroup 15 :=
        List.mem_of_elem_eq_true (List.all_eq_true.mp andRoles_group r hr)
      exact Or.inr (Or.inr (keptIn_of_role hmem (Or.inr (Or.inr rfl)) hg
        (of_decide_eq_true hn).symm))
  · rcases List.mem_append.mp h with h | h
    · have hn : ci.name ∈ boolRoles.map Key.role := by
        rw [← boolEnv_take]
        exact List.mem_map.mpr ⟨ci, h, rfl⟩
      obtain ⟨r, hr, hname⟩ := List.mem_map.mp hn
      have hg : r ∈ roleGroup 6 :=
        List.mem_of_elem_eq_true (List.all_eq_true.mp boolRoles_group r hr)
      exact Or.inr (Or.inr (keptIn_of_role hmem (Or.inr (Or.inl rfl)) hg hname))
    · exact Or.inr (Or.inl (basisEnv_pinned ci h))

/-! ## The inhabitant -/

/-- **The default table is valid, in the public sense, on the basis and quotient groups, the
`Bool` group and the `And` group**, with the store of all 33 committed prelude records and the
environment IxC's native checks of the `Bool` and `And` blocks install over the pins. -/
theorem tableShape_and :
    TableShape.{u} committedDefaultRoleTable (fun g => g < 6 ∨ g = 6 ∨ g = 15) andStore
      andEnv := {
  needsClosed := fun g hg r hr => by
    have hg' : InGroups g := hg
    show Ix.SpecDigest.groupOf r < 6 ∨ Ix.SpecDigest.groupOf r = 6 ∨
      Ix.SpecDigest.groupOf r = 15
    rcases hg' with hg' | hg' | hg'
    · have h1 : (groupNeeded g).all (fun r => decide (Ix.SpecDigest.groupOf r < 6)) = true :=
        List.all_eq_true.mp groups_closed g (List.mem_range.mpr hg')
      exact Or.inl (of_decide_eq_true (List.all_eq_true.mp h1 r hr))
    · have h6 : groupNeeded 6 = [] := by decide +kernel
      rw [hg', h6] at hr
      cases hr
    · have h15 : groupNeeded 15 = [] := by decide +kernel
      rw [hg', h15] at hr
      cases hr
  bound := fun _ _ r _ => defaultTable_allBound r
  prelude := preludePinned_default
  literals := committedDefaultRoleTable_literalSupportBound
  hashed := RowsStore.hashed andRows_committed
  usedClosed := RowsStore.usedClosed andRows_committed and_projs_found and_owners and_refs
  committed := RowsStore.committed andRows_committed
  zeroFree := RowsStore.zeroFree and_zero
  kept := fun _ r a hg hr _ ha => by
    obtain ⟨a', ci, ha', hfind, hkept⟩ := role_keptIn hg hr
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    rw [← e]
    exact ⟨ci, hfind, Or.inr hkept⟩
  reading := {
    nodup := andEnv_nodup
    provenance := and_provenance
    stored := and_stored }
  pins := andEnv_pins
  preludeKept := fun _ r a hg hr _ ha => by
    obtain ⟨a', ci, ha', hfind, hkept⟩ := role_keptIn hg hr
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    rw [← e]
    exact ⟨ci, hfind, Or.inr hkept⟩
  model := fun W _ => andEnv_model W }

end IxVM.Refinement.AndInhabit
