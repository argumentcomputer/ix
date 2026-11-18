import IxVMRefinement.Binding.Fold
import IxVMRefinement.Assembly.TypingBasisProj
import IxVMRefinement.StatementRel.BoolInhabit

/-! # Inhabitants of the binding fold's interfaces

* `bnd_basis`: **the boundary invariant below group 6 at the default table**, the store of the
  24 committed basis rows and the environment of the pins: `TableShape` from
  `StoreInhabit.tableShape_store`, the prefix invariant from `Typing.basis_facts`, and the
  rest (no operation stored, the shapes of groups not yet admitted) closed here. With no further hypothesis.
* `admits_bool`: **the admission of the `Bool` group (6) at the default table**, from the basis
  store to the store of the 29 committed rows (`BoolInhabit.boolStore`), for the run view
  `boolRun` whose loaded records are that store, whose rank puts the block before its
  projection records, and whose check and validation predicates are trivial. Every store clause
  of `Admits` is proved: no new record uses a reference outside the basis rows, every new
  projection record is at its block's member or constructor address, no new record is an axiom,
  quotient or operation record, and the group's roles have their records.
* `bool_step_instance`: **one step of `StepCore` taken at the `Bool` group**: from `bnd_basis`
  and `admits_bool` to the boundary invariant below 7 at the store of 29 rows and the
  environment IxC's native check of the block installs (`BoolInhabit.boolEnv`), with every
  field proved except two of the internal part at that environment, taken as hypotheses: the
  prefix invariant at the carried limits within groups 0–6 (`inv`), and blocks stored whole
  (`whole`). Their producer is the native-block step (an inductive block without recursor, then
  the late recursor) at a concrete environment; nothing in the tree proves them yet.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.TableInhabit (basisEnv)
open IxVM.Refinement.StoreInhabit (basisRows basisStore isMutsInfo)
open IxVM.Refinement.RowsStore (rowsEnv Committed hasKeyIn)
open IxVM.Refinement.RowReader (Row expectedProjsOf findProjOf inLogicMutB)
open IxVM.Refinement.BoolInhabit (boolRows boolStore boolEnv boolRowStore)

/-! ## Environments that store no operation -/

/-- A key that is no name of the environment's constants is not stored. -/
theorem find?_none_of_names {env : Ix.Kernel.Env .anon} {k : Ix.Kernel.Key .anon}
    (h : k ∉ env.consts.map (·.name)) : env.find? k = none := by
  unfold Ix.Kernel.Env.find?
  apply List.find?_eq_none.mpr
  intro ci hci heq
  exact h (List.mem_map.mpr ⟨ci, hci, beq_iff_eq.mp heq⟩)

/-- **An environment whose names are role keys of roles that are no operation stores no
operation.** -/
theorem opsPinned_of_names {env : Ix.Kernel.Env .anon} {rs : List Ix.Kernel.Role}
    (hn : env.consts.map (·.name) = rs.map Ix.Kernel.Key.role)
    (hops : ∀ r ∈ RoleOps.opRoles, r ∉ rs) :
    RoleOps.OpsPinned env ∧
      ∀ r ∈ RoleOps.opRoles, env.find? (Ix.Kernel.Key.role r) = none := by
  have hnone : ∀ r ∈ RoleOps.opRoles, env.find? (Ix.Kernel.Key.role r) = none := by
    intro r hr
    apply find?_none_of_names
    rw [hn]
    intro hm
    obtain ⟨r', hr', he⟩ := List.mem_map.mp hm
    have he' : r' = r := Ix.Kernel.Key.role.inj he
    rw [he'] at hr'
    exact hops r hr hr'
  refine ⟨RoleOps.OpsPinned.of_none fun n hn' => ?_, hnone⟩
  rw [RoleOps.opNames_eq_map] at hn'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn'
  exact hnone r hr

/-! ## The boundary invariant below group 6 -/

private theorem ops_not_basis :
    ∀ r ∈ RoleOps.opRoles, r ∉ TableInhabit.basisRoleOrder := by decide

theorem basisEnv_names :
    basisEnv.consts.map (·.name) = TableInhabit.basisRoleOrder.map Ix.Kernel.Key.role := rfl

set_option maxRecDepth 100000 in
/-- The groups of the roles whose shapes `Shapes` records (decided). -/
theorem groupOf_values :
    Ix.SpecDigest.groupOf .bool = 6 ∧ Ix.SpecDigest.groupOf .char = 41 ∧
      Ix.SpecDigest.groupOf .string = 42 ∧ Ix.SpecDigest.groupOf .list = 43 ∧
      Ix.SpecDigest.groupOf .charOfNat = 44 ∧ Ix.SpecDigest.groupOf .stringOfList = 45 ∧
      Ix.SpecDigest.groupOf .iff = 16 ∧ Ix.SpecDigest.groupOf .nonempty = 17 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **No group from 6 on has its shapes asked for below 6.** -/
theorem shapes_below_six (env : Ix.Kernel.Env .anon) : Shapes (· < 6) env := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := groupOf_values
  exact {
    bool := fun h => absurd (show Ix.SpecDigest.groupOf .bool < 6 from h) (by omega)
    char := fun h => absurd (show Ix.SpecDigest.groupOf .char < 6 from h) (by omega)
    string := fun h => absurd (show Ix.SpecDigest.groupOf .string < 6 from h) (by omega)
    list := fun h => absurd (show Ix.SpecDigest.groupOf .list < 6 from h) (by omega)
    charOfNat := fun h => absurd (show Ix.SpecDigest.groupOf .charOfNat < 6 from h) (by omega)
    stringOfList := fun h =>
      absurd (show Ix.SpecDigest.groupOf .stringOfList < 6 from h) (by omega)
    iff := fun h => absurd (show Ix.SpecDigest.groupOf .iff < 6 from h) (by omega)
    nonempty := fun h => absurd (show Ix.SpecDigest.groupOf .nonempty < 6 from h) (by omega) }

/-- **The boundary invariant below group 6, at the default table, the basis store and the
environment of the pins.** -/
theorem bnd_basis
    {X : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    (hX : X ctab (· < 6) basisStore basisEnv) :
    Bnd.{u} X ctab (· < 6) basisStore basisEnv := by
  obtain ⟨hpin, hnone⟩ := opsPinned_of_names basisEnv_names ops_not_basis
  exact {
    shape := StoreInhabit.tableShape_store
    facts := {
      inv := fun E hE lim _ hlim => basis_facts.inv E hE lim hlim
      whole := basis_facts.{0}.whole
      opsPinned := hpin
      opsAdmitted := fun r hr hs => by
        rw [hnone r hr] at hs
        cases hs
      shapes := shapes_below_six basisEnv }
    extra := hX }

/-- **The basis hypothesis of the fold holds of every run at the default table whose store after
the basis groups is the basis store** (an inhabitant of `BasisBase`). -/
theorem basisBase_default :
    BasisBase.{u} (fun _ _ _ _ => True) (fun t _ Rs => t = ctab ∧ Rs 6 = basisStore) := by
  rintro t ρ Rs ⟨rfl, hR⟩ -
  rw [hR]
  exact ⟨basisEnv, bnd_basis trivial⟩

/-! ## The admission of the `Bool` group -/

/-- The five rows of the `Bool` block: the block record, then the projection records of `Bool`,
`Bool.false`, `Bool.true` and `Bool.rec`. -/
def boolNew : List Row := RoleVal.committedPreludeList.drop 28

theorem basisStore_eq : basisStore = rowsEnv basisRows := rfl

theorem basis_committed : Committed basisRows :=
  ⟨StoreInhabit.basisEntries_distinct, StoreInhabit.basisRows_sub⟩

theorem boolRows_eq : boolRows = basisRows ++ boolNew := rfl

/-- The rank of a record kind in the `Bool` admission: the block, then the projection records,
then a standalone record (the recursor record, which names the projection records). -/
def kindRank : Ixon.ConstantInfo → Nat
  | .muts _ => 0
  | .recr _ => 2
  | .defn _ => 2
  | .axio _ => 2
  | .quot _ => 2
  | _ => 1

theorem kindRank_proj {c : Ixon.Constant} (h : IsProj c) : kindRank c.info = 1 := by
  rcases h with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ <;> rw [hp] <;> rfl

/-- What the check of a new row reads: no axiom, quotient or standalone definition record; a
recursor record that is safe; a block of members in Lean's logic; a projection record found
among the expected projection records of the rows' blocks. -/
def newRowOk (a : _root_.Address) : Ixon.ConstantInfo → Bool
  | .axio _ => false
  | .quot _ => false
  | .defn _ => false
  | .recr rc => decide (rc.isUnsafe = false)
  | .muts ms => ms.toList.all inLogicMutB
  | _ => (expectedProjsOf boolRows).any fun p => (findProjOf boolRows p).map (·.1) == some a

/-- A reference a new row uses: a basis row, or a new row of smaller kind rank. -/
def refOk (k : Nat) (x : _root_.Address) : Bool :=
  hasKeyIn basisRows x || boolNew.any fun e' => e'.1 == x && decide (kindRank e'.2.info < k)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **The new rows, decided**: each passes `newRowOk`; every reference it uses is a basis row or
a new row of smaller kind rank; neither it nor its block is a basis row; none is at the address
of an operation role. -/
theorem boolNew_ok :
    boolNew.all (fun e =>
      newRowOk e.1 e.2.info &&
      (usedRefIdxs e.2).all (fun i => (e.2.refs[i]?).all (refOk (kindRank e.2.info))) &&
      !hasKeyIn basisRows (Ix.Cert.ownerOf e.1 e.2) &&
      !hasKeyIn basisRows e.1 &&
      RoleOps.opRoles.all fun r => RoleVal.committedDefaultRoleTable.addressOf? r != some e.1) =
      true := by
  decide +kernel

theorem boolNew_row {e : Row} (h : e ∈ boolNew) :
    newRowOk e.1 e.2.info = true ∧
      (usedRefIdxs e.2).all (fun i => (e.2.refs[i]?).all (refOk (kindRank e.2.info))) = true ∧
      hasKeyIn basisRows (Ix.Cert.ownerOf e.1 e.2) = false ∧
      hasKeyIn basisRows e.1 = false ∧
      ∀ r ∈ RoleOps.opRoles, RoleVal.committedDefaultRoleTable.addressOf? r ≠ some e.1 := by
  have h1 : (newRowOk e.1 e.2.info &&
      (usedRefIdxs e.2).all (fun i => (e.2.refs[i]?).all (refOk (kindRank e.2.info))) &&
      !hasKeyIn basisRows (Ix.Cert.ownerOf e.1 e.2) &&
      !hasKeyIn basisRows e.1 &&
      RoleOps.opRoles.all fun r => RoleVal.committedDefaultRoleTable.addressOf? r != some e.1) =
      true := List.all_eq_true.mp boolNew_ok e h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩ := h1
  refine ⟨h2, h3, ?_, ?_, fun r hr => ?_⟩
  · revert h4
    cases hasKeyIn basisRows (Ix.Cert.ownerOf e.1 e.2) <;> decide
  · revert h5
    cases hasKeyIn basisRows e.1 <;> decide
  · exact bne_iff_ne.mp (List.all_eq_true.mp h6 r hr)

theorem recordOf_none_of_not_hasKey {rows : List Row} {a : _root_.Address}
    (h : hasKeyIn rows a = false) : recordOf (rowsEnv rows) a = none :=
  (congrArg (fun (o : Option Ixon.LazyConstant) =>
    o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption)
    (RowsStore.get?_of_not_hasKey h)).trans rfl

/-- **A record new in the `Bool` store is a row of the block.** -/
theorem new_bool {a : _root_.Address} (h : New basisStore boolStore a) :
    ∃ c, (a, c) ∈ boolNew ∧ recordOf boolStore a = some c := by
  obtain ⟨hs, hn⟩ := h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
  have hmem : (a, c) ∈ boolRows := RowsStore.record_inv BoolInhabit.boolRows_committed hc
  rw [boolRows_eq] at hmem
  rcases List.mem_append.mp hmem with hb | hnew
  · rw [basisStore_eq, RowsStore.record_of_mem basis_committed hb] at hn
    cases hn
  · exact ⟨c, hnew, hc⟩

/-- A new row is new in the `Bool` store. -/
theorem bool_new_of_row {e : Row} (he : e ∈ boolNew) :
    recordOf boolStore e.1 = some e.2 ∧ New basisStore boolStore e.1 := by
  have hrec : recordOf boolStore e.1 = some e.2 :=
    RowsStore.record_of_mem BoolInhabit.boolRows_committed (a := e.1) (c := e.2)
      (by rw [boolRows_eq]; exact List.mem_append_right _ he)
  refine ⟨hrec, ?_, ?_⟩
  · simp [hrec]
  · rw [basisStore_eq]
    exact recordOf_none_of_not_hasKey (boolNew_row he).2.2.2.1

/-- The projection records of member `i` of a block record. -/
theorem mem_projsOf {B : _root_.Address} {cb : Ixon.Constant} {i : Nat} {p : Ixon.Constant}
    (hi : i < (StoreInhabit.membersOf cb.info).size)
    (hp : p ∈ StoreInhabit.projsOf B i ((StoreInhabit.membersOf cb.info)[i]?)) :
    ∃ ms m, cb.info = .muts ms ∧ ms[i]? = some m ∧
      (p = memberProjection B i m ∨
        ∃ ind j, m = .indc ind ∧ j < ind.ctors.size ∧ p = constructorProjection B i j) := by
  cases hinfo : cb.info with
  | muts ms =>
    rw [hinfo] at hi hp
    have hi' : i < ms.size := hi
    have hm : ms[i]? = some ms[i] := Array.getElem?_eq_getElem hi'
    change p ∈ StoreInhabit.projsOf B i (ms[i]?) at hp
    rw [hm] at hp
    refine ⟨ms, ms[i], rfl, hm, ?_⟩
    rcases List.mem_cons.mp hp with h | h
    · exact Or.inl h
    · obtain ⟨j, hj, hpj⟩ := List.mem_map.mp h
      cases hmi : ms[i] with
      | indc ind =>
        rw [hmi] at hj
        exact Or.inr ⟨ind, j, rfl, List.mem_range.mp hj, hpj.symm⟩
      | defn d =>
        rw [hmi] at hj
        exact absurd (List.mem_range.mp hj) (Nat.not_lt_zero j)
      | recr rc =>
        rw [hmi] at hj
        exact absurd (List.mem_range.mp hj) (Nat.not_lt_zero j)
  | defn _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)
  | recr _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)
  | axio _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)
  | quot _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)
  | cPrj _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)
  | rPrj _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)
  | iPrj _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)
  | dPrj _ => rw [hinfo] at hi; exact absurd hi (Nat.not_lt_zero i)

/-- **A new projection record of the `Bool` store is at a member's or a constructor's address
of its block**, which the store holds. -/
theorem bool_projMember {a : _root_.Address} {c : Ixon.Constant}
    (hnew : New basisStore boolStore a) (hc : recordOf boolStore a = some c) (hp : IsProj c) :
    ∃ cb, recordOf boolStore (Ix.Cert.ownerOf a c) = some cb ∧
      ConstAddrOf (Ix.Cert.ownerOf a c) cb a := by
  obtain ⟨c₀, hmem, hc₀⟩ := new_bool hnew
  have hcc : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
  subst hcc
  have hok := (boolNew_row hmem).1
  have hany : (expectedProjsOf boolRows).any
      (fun p => (findProjOf boolRows p).map (·.1) == some a) = true := by
    rcases hp with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
    all_goals
      have h' : newRowOk a c₀.info = true := hok
      rw [hq] at h'
      exact h'
  obtain ⟨p, hpmem, hfound⟩ := List.any_eq_true.mp hany
  have hfound' : (findProjOf boolRows p).map (·.1) = some a := beq_iff_eq.mp hfound
  have hrow : (a, c₀) ∈ boolRowStore.rows := by
    show (a, c₀) ∈ boolRows
    rw [boolRows_eq]
    exact List.mem_append_right _ hmem
  obtain ⟨hcp, hap⟩ := RowReader.row_is_proj boolRowStore hrow hpmem hfound'
  obtain ⟨⟨B, cb⟩, hBrow, hp1⟩ := List.mem_flatMap.mp hpmem
  obtain ⟨i, hi, hp2⟩ := List.mem_flatMap.mp hp1
  have hi' : i < (StoreInhabit.membersOf cb.info).size := List.mem_range.mp hi
  have hp2' : p ∈ StoreInhabit.projsOf B i ((StoreInhabit.membersOf cb.info)[i]?) := hp2
  obtain ⟨ms, m, hms, hm, hpc⟩ := mem_projsOf hi' hp2'
  have hcb : recordOf boolStore B = some cb :=
    RowsStore.record_of_mem BoolInhabit.boolRows_committed hBrow
  rcases hpc with hpe | ⟨ind, j, hind, hj, hpe⟩
  · have howner : Ix.Cert.ownerOf a c₀ = B := by
      rw [hcp, hpe]
      exact ownerOf_memberProjection a B i m
    rw [howner]
    refine ⟨cb, hcb, Or.inr ⟨ms, i, m, hms, hm, Or.inl ?_⟩⟩
    exact hap.trans (congrArg (fun q => _root_.Address.blake3Pure (Ixon.serConstant q)) hpe)
  · have howner : Ix.Cert.ownerOf a c₀ = B := by
      rw [hcp, hpe]
      exact ownerOf_constructorProjection a B i j
    rw [howner]
    refine ⟨cb, hcb, Or.inr ⟨ms, i, m, hms, hm, Or.inr ⟨ind, j, hind, hj, ?_⟩⟩⟩
    exact hap.trans (congrArg (fun q => _root_.Address.blake3Pure (Ixon.serConstant q)) hpe)

/-- The rank of the `Bool` admission: the kind rank of the record at the address. -/
def boolRank (a : _root_.Address) : Nat :=
  match recordOf boolStore a with
  | some c => kindRank c.info
  | none => 3

theorem boolRank_of {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf boolStore a = some c) : boolRank a = kindRank c.info := by
  unfold boolRank
  simp [h]

/-- **The run view of the `Bool` admission**: the 29 rows are the records loaded; the check and
validation predicates are trivial (the admission's store clauses do not read them). -/
def boolRun : BRun where
  E₀ := boolStore
  rank := fun _ a => boolRank a
  checked := fun _ _ => True
  validated := fun _ _ => True

/-- The `Bool` group has no operation and no standard axiom (decided). -/
theorem group6_noUnits : ∀ r ∈ roleGroup 6, r ∉ RoleOps.opRoles ∧ r ∉ standardAxioms := by
  decide +kernel

/-- No role of the `Bool` group has equations, so none has evidence (decided). -/
theorem group6_noEquations : ∀ r ∈ roleGroup 6, RoleVal.roleHasEquations r = false := by
  decide +kernel

/-- **The admission of the `Bool` group at the default table**, from the basis store to the
store of the 29 rows. -/
theorem admits_bool : Admits boolRun ctab 6 basisStore boolStore where
  mono := by
    intro a lc h
    rw [basisStore_eq] at h
    obtain ⟨c, hmem, rfl⟩ := RowsStore.get?_inv basis_committed h
    have hmem' : (a, c) ∈ boolRows := by
      rw [boolRows_eq]
      exact List.mem_append_left _ hmem
    exact RowsStore.get?_of_mem BoolInhabit.boolRows_committed hmem'
  monoBlobs := by
    intro a b h
    have h' : basisStore.blobs.get? a = none := RowsStore.blobs_none (rows := basisRows) a
    rw [h'] at h
    cases h
  loaded := fun _ _ h => h
  loadedBlobs := fun _ _ h => h
  hashed := BoolInhabit.tableShape_bool.{0}.hashed
  usedClosed := BoolInhabit.tableShape_bool.{0}.usedClosed
  committed := BoolInhabit.tableShape_bool.{0}.committed
  zeroFree := BoolInhabit.tableShape_bool.{0}.zeroFree
  rankUsed := by
    intro a x hnew hused
    obtain ⟨c, hmem, hc⟩ := new_bool hnew
    obtain ⟨c', i, hc', hi, hx⟩ := hused
    have hcc : c = c' := Option.some.inj (hc.symm.trans hc')
    subst hcc
    have h1 := (boolNew_row hmem).2.1
    have h2 : (c.refs[i]?).all (refOk (kindRank c.info)) = true := List.all_eq_true.mp h1 i hi
    rw [hx] at h2
    have h3 : (hasKeyIn basisRows x || boolNew.any fun e' =>
        e'.1 == x && decide (kindRank e'.2.info < kindRank c.info)) = true := h2
    cases hb : hasKeyIn basisRows x with
    | true =>
      refine Or.inr ?_
      rw [basisStore_eq]
      exact RowsStore.isSome_of_hasKey basis_committed hb
    | false =>
      rw [hb, Bool.false_or] at h3
      obtain ⟨e', he', hxe⟩ := List.any_eq_true.mp h3
      have hxe' : (e'.1 == x && decide (kindRank e'.2.info < kindRank c.info)) = true := hxe
      rw [Bool.and_eq_true] at hxe'
      obtain ⟨hx1, hx2⟩ := hxe'
      have hex : e'.1 = x := beq_iff_eq.mp hx1
      have hlt : kindRank e'.2.info < kindRank c.info := of_decide_eq_true hx2
      obtain ⟨hrec, hnew'⟩ := bool_new_of_row he'
      rw [hex] at hrec hnew'
      refine Or.inl ⟨hnew', ?_⟩
      show boolRank x < boolRank a
      rw [boolRank_of hrec, boolRank_of hc]
      exact hlt
  rankOwner := by
    intro a c hnew hc hp
    obtain ⟨c₀, hmem, hc₀⟩ := new_bool hnew
    have hcc : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
    subst hcc
    obtain ⟨cb, hcb, hconst⟩ := bool_projMember hnew hc hp
    have hB : recordOf basisStore (Ix.Cert.ownerOf a c₀) = none := by
      rw [basisStore_eq]
      exact recordOf_none_of_not_hasKey (boolNew_row hmem).2.2.1
    have hmuts : ∃ ms, cb.info = .muts ms := by
      rcases hconst with ⟨hBa, hs⟩ | ⟨ms, _, _, hms, _, _⟩
      · rw [← hBa, hc] at hcb
        have e : c₀ = cb := Option.some.inj hcb
        rw [← e] at hs
        exact (standalone_not_proj hs hp).elim
      · exact ⟨ms, hms⟩
    obtain ⟨ms, hms⟩ := hmuts
    refine Or.inl ⟨⟨by simp [hcb], hB⟩, ?_⟩
    show boolRank (Ix.Cert.ownerOf a c₀) < boolRank a
    rw [boolRank_of hcb, boolRank_of hc, hms, kindRank_proj hp]
    exact Nat.zero_lt_one
  projMember := fun a c hnew hc hp => bool_projMember hnew hc hp
  standing := by
    intro a c hnew hc hax
    obtain ⟨c₀, hmem, hc₀⟩ := new_bool hnew
    have hcc : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
    subst hcc
    have hok : newRowOk a c₀.info = true := (boolNew_row hmem).1
    rcases hax with ⟨ax, hq⟩ | ⟨q, hq⟩ <;> (rw [hq] at hok; cases hok)
  logic := by
    intro a c hnew hc
    obtain ⟨c₀, hmem, hc₀⟩ := new_bool hnew
    have hcc : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
    subst hcc
    have hok : newRowOk a c₀.info = true := (boolNew_row hmem).1
    cases hinfo : c₀.info with
    | muts ms =>
      rw [hinfo] at hok
      exact RowReader.inLogic_muts hinfo hok
    | recr rc =>
      rw [hinfo] at hok
      have h' : decide (rc.isUnsafe = false) = true := hok
      exact RowReader.inLogic_recr hinfo (of_decide_eq_true h')
    | axio _ => rw [hinfo] at hok; cases hok
    | quot _ => rw [hinfo] at hok; cases hok
    | defn _ => rw [hinfo] at hok; cases hok
    | cPrj _ => unfold InLogic; rw [hinfo]; trivial
    | rPrj _ => unfold InLogic; rw [hinfo]; trivial
    | iPrj _ => unfold InLogic; rw [hinfo]; trivial
    | dPrj _ => unfold InLogic; rw [hinfo]; trivial
  checked := fun _ _ _ _ _ => trivial
  validated := fun _ _ => trivial
  kept := by
    intro r hr _ a ha
    obtain ⟨a', ci, ha', -, hkept⟩ := BoolInhabit.role_keptIn (Or.inr rfl) hr
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    subst e
    obtain ⟨-, ci₀, ⟨c, hc, -⟩, -⟩ := hkept
    simp [hc]
  opsOwn := by
    intro a r hnew ha hop
    obtain ⟨c, hmem, -⟩ := new_bool hnew
    exact absurd ha ((boolNew_row hmem).2.2.2.2 r hop)
  unitsLast := by
    rintro x a - - ⟨r, hr, -, hop⟩
    have h := group6_noUnits r hr
    rcases hop with h1 | h1
    · exact h.1 h1
    · exact h.2 h1
  evidenceRefs := by
    intro r hr arr thm x hm
    have h := RoleVal.evidence_roleHasEquations_of_wf Typing.committedTable_wf hm
    rw [group6_noEquations r hr] at h
    cases h

/-! ## The boundary invariant's other fields at the `Bool` environment -/

/-- The stored shapes `Bool`'s constants must have, decided. -/
def boolShapeB (env : Ix.Kernel.Env .anon) : Bool :=
  (match env.find? Ix.Kernel.boolName with
    | some ci => ci.toConstantVal.levelParams.isEmpty &&
        ci.toConstantVal.type == .sort (.succ .zero)
    | none => false) &&
  (match env.find? Ix.Kernel.boolTrueName with
    | some ci => ci.toConstantVal.levelParams.isEmpty &&
        ci.toConstantVal.type == .const Ix.Kernel.boolName []
    | none => false) &&
  (match env.find? Ix.Kernel.boolFalseName with
    | some ci => ci.toConstantVal.levelParams.isEmpty &&
        ci.toConstantVal.type == .const Ix.Kernel.boolName []
    | none => false)

theorem boolShape_of {env : Ix.Kernel.Env .anon} (h : boolShapeB env = true) :
    RoleOps.BoolPinned env ∧ RoleOps.BoolCtorsStored env ∧ RoleOps.BoolCtorsTyped env := by
  unfold boolShapeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hb, ht⟩, hf⟩ := h
  cases hB : env.find? Ix.Kernel.boolName with
  | none => rw [hB] at hb; cases hb
  | some ciB =>
    rw [hB] at hb
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hb
    cases hT : env.find? Ix.Kernel.boolTrueName with
    | none => rw [hT] at ht; cases ht
    | some ciT =>
      rw [hT] at ht
      simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at ht
      cases hF : env.find? Ix.Kernel.boolFalseName with
      | none => rw [hF] at hf; cases hf
      | some ciF =>
        rw [hF] at hf
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hf
        exact ⟨⟨ciB, hB, hb.1, hb.2⟩, ⟨⟨ciT, hT, ht.1⟩, ⟨ciF, hF, hf.1⟩⟩,
          ⟨⟨ciT, hT, ht.2⟩, ⟨ciF, hF, hf.2⟩⟩⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The `Bool` environment stores `Bool` and its constructors with the shapes the operations'
guards read (decided). -/
theorem boolEnv_shapeB : boolShapeB boolEnv = true := by
  decide +kernel

/-- The `Bool` environment stores no projection table: its names are role keys. -/
theorem boolEnv_noTable (k : Ix.Kernel.Key .anon) (tbl : Ix.Kernel.ProjTable .anon) :
    boolEnv.find? k ≠ some (.projInfo tbl) := by
  intro h
  have hmem := Ix.Kernel.Semantics.Env.find?_mem h
  have hn : (Ix.Kernel.ConstantInfo.projInfo tbl).name ∈ boolEnv.consts.map (·.name) :=
    List.mem_map.mpr ⟨_, hmem, rfl⟩
  rw [BoolInhabit.boolEnv_names] at hn
  obtain ⟨r, -, hr⟩ := List.mem_map.mp hn
  have hname : (Ix.Kernel.ConstantInfo.projInfo tbl).name =
      Ix.Kernel.Key.aux tbl.structName .projTable := rfl
  rw [hname] at hr
  cases hr

private theorem ops_not_bool :
    ∀ r ∈ RoleOps.opRoles, r ∉ BoolInhabit.boolRoles ++ TableInhabit.basisRoleOrder := by
  decide

/-- **The `Bool` environment's fields of the internal invariant below 7 other than the prefix
invariant and block wholeness**: no operation stored, and the
shapes (the `Bool` constants' shapes, decided; the others' groups are not yet admitted). -/
theorem bool_bfacts {R : Ixon.Env}
    (hinv : ∀ E, RecordsFor R E → ∀ lim, Carried lim →
      LimWithin (fun k => k < 6 ∨ k = 6) ctab lim → Decl.PrefixInv.{u} E ctab lim boolEnv)
    (hwhole : ∀ E, RecordsFor R E →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (boolEnv.find? (keyOf ctab a)).isSome = true → Ix.Cert.recordAt E a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb →
        cb.info = .muts ms → BlockStored ctab boolEnv B ms) :
    BFacts.{u} ctab (fun k => k < 6 ∨ k = 6) R boolEnv := by
  obtain ⟨hpin, hnone⟩ := opsPinned_of_names BoolInhabit.boolEnv_names ops_not_bool
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := groupOf_values
  have hbool := boolShape_of boolEnv_shapeB
  exact {
    inv := hinv
    whole := hwhole
    opsPinned := hpin
    opsAdmitted := fun r hr hs => by
      rw [hnone r hr] at hs
      cases hs
    shapes := {
      bool := fun _ => hbool
      char := fun h => absurd (show Ix.SpecDigest.groupOf .char < 6 ∨
        Ix.SpecDigest.groupOf .char = 6 from h) (by omega)
      string := fun h => absurd (show Ix.SpecDigest.groupOf .string < 6 ∨
        Ix.SpecDigest.groupOf .string = 6 from h) (by omega)
      list := fun h => absurd (show Ix.SpecDigest.groupOf .list < 6 ∨
        Ix.SpecDigest.groupOf .list = 6 from h) (by omega)
      charOfNat := fun h => absurd (show Ix.SpecDigest.groupOf .charOfNat < 6 ∨
        Ix.SpecDigest.groupOf .charOfNat = 6 from h) (by omega)
      stringOfList := fun h => absurd (show Ix.SpecDigest.groupOf .stringOfList < 6 ∨
        Ix.SpecDigest.groupOf .stringOfList = 6 from h) (by omega)
      iff := fun h => absurd (show Ix.SpecDigest.groupOf .iff < 6 ∨
        Ix.SpecDigest.groupOf .iff = 6 from h) (by omega)
      nonempty := fun h => absurd (show Ix.SpecDigest.groupOf .nonempty < 6 ∨
        Ix.SpecDigest.groupOf .nonempty = 6 from h) (by omega) } }

/-! ## One step of the fold at the `Bool` group -/

theorem groupNeeded_six : groupNeeded 6 = [] := by decide +kernel

/-- **One step of `StepCore` taken at the `Bool` group (6) of the default table**: from the
basis store and the environment of the pins to the store of 29 rows and the environment
IxC's native check of the `Bool` block installs. Every field is proved but two of the internal
invariant at the `Bool` environment, the prefix invariant at the carried limits within groups
0–6 and block wholeness, which are the hypotheses (producer: the native-block step). -/
theorem bool_step_instance
    (hinv : ∀ E, RecordsFor boolStore E → ∀ lim, Carried lim →
      LimWithin (fun k => k < 6 ∨ k = 6) ctab lim → Decl.PrefixInv.{u} E ctab lim boolEnv)
    (hwhole : ∀ E, RecordsFor boolStore E →
      ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
        (boolEnv.find? (keyOf ctab a)).isSome = true → Ix.Cert.recordAt E a = some c →
        Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb →
        cb.info = .muts ms → BlockStored ctab boolEnv B ms) :
    StepInstance.{u} (fun _ _ _ _ => True) boolRun ctab (· < 6) 6 basisStore boolStore
      basisEnv boolEnv where
  bound := fun r _ => ClosedFacts.defaultTable_allBound r
  needs := fun r hr => by
    rw [groupNeeded_six] at hr
    cases hr
  limWithin := limWithin_below ctab 6
  pre := bnd_basis trivial
  admits := admits_bool
  ext := fun ci h => by
    rw [BoolInhabit.boolEnv_split]
    exact List.mem_append_right _ h
  post := {
    shape := BoolInhabit.tableShape_bool
    facts := bool_bfacts hinv hwhole
    extra := trivial }

end IxVM.Refinement.Binding
