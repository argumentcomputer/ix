import IxVMRefinement.StatementRel.Inhabit
import IxVMRefinement.StatementRel.ClosedFacts

/-! # An inhabitant of the table-validity shape with a store

`tableShape_store`: the default table is valid, in the public sense of `TableShape`, on the
first six validation groups (`Nat`, `Eq`, `PUnit`, `Empty`, `False`, the quotient package),
with a store that holds the 24 committed prelude records of those blocks and the environment
of the kernel's pinned basis constants.

The store does not hold the nine committed records of `And` and `Bool`. Their projection
records read, so `ReadingOf.stored` would ask for constants at their keys, and the
environment has none before those groups are admitted; and a block cannot be kept without
its members' projection records (`UsedClosed`). A store on a set of groups holds exactly the
records whose constants the environment on those groups has.

Every clause over a record is exercised: `hashed`, `committed`, both halves of `usedClosed`,
and `stored`, `kept` and `preludeKept` at the nineteen role addresses, through the pin.
-/

universe u

namespace IxVM.Refinement.StoreInhabit

open Ix.Kernel
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.TableInhabit
open IxVM.Refinement.ClosedFacts
open IxVM.Refinement.Claim (mkLazy mkLazy_rawBytes)

/-! ## The committed rows, as a list -/

private theorem forall₂_imp' {α β : Type} {R S : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (H : ∀ a b, R a b → S a b) : List.Forall₂ S l₁ l₂ := by
  induction h with
  | nil => exact .nil
  | cons head _ ih => exact .cons (H _ _ head) ih

private theorem filterMap_of_forall₂ {α β γ : Type} {g : α → Option γ} {f : β → γ}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ (fun a b => g a = some (f b)) l₁ l₂) :
    l₁.filterMap g = l₂.map f := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [head, ih]

private theorem map_eq_pointwise {α β : Type} {f g : α → β} :
    ∀ {l : List α}, l.map f = l.map g → ∀ a ∈ l, f a = g a
  | [], _, _, ha => nomatch ha
  | x :: xs, h, a, ha => by
    rw [List.map_cons, List.map_cons] at h
    injection h with h1 h2
    rcases List.mem_cons.mp ha with hax | ha'
    · rw [hax]
      exact h1
    · exact map_eq_pointwise h2 a ha'

/-- The row parser of `committedRows`. -/
def parseRow (row : String × String) : Option (_root_.Address × ByteArray) :=
  (Ix.Kernel.Reader.addressOfHex row.1).bind fun a => (bytesOfHex row.2).map fun bytes => (a, bytes)

/-- **The rows of a committed file that decodes are its decoded records, in order, each with
its canonical bytes.** -/
theorem decoded_rows_eq (what : String) (raw : Array (String × String))
    {out : Array (_root_.Address × Ixon.Constant)}
    (h : Ix.Kernel.Reader.decodeCommitted what raw = .ok out) :
    raw.toList.filterMap parseRow = out.toList.map fun e => (e.1, Ixon.serConstant e.2) := by
  unfold Ix.Kernel.Reader.decodeCommitted at h
  rw [Array.mapM_eq_mapM_toList] at h
  simp only [Functor.map, Except.map] at h
  split at h
  · cases h
  · rename_i ys hr
    cases h
    apply filterMap_of_forall₂
    apply forall₂_imp' (Ix.CompileCert.Loop.mapM_forall₂ _ hr)
    intro row e step
    cases ha : Ix.Kernel.Reader.addressOfHex row.1 with
    | none => simp [ha] at step
    | some a =>
      cases hb : bytesOfHex row.2 with
      | none => simp [ha, hb] at step
      | some bytes =>
        simp only [ha, hb] at step
        obtain ⟨c, decoded, done⟩ := Ix.CompileCert.Loop.except_bind_ok.mp step
        cases done
        cases hd : Ixon.Canonical.deConstant Ix.Kernel.Reader.preludeMaxBytes
            Ix.Kernel.Reader.preludeMaxUnivNodes bytes with
        | error err => simp [hd, Except.mapError] at decoded
        | ok c' =>
          simp only [hd, Except.mapError, Except.ok.injEq] at decoded
          obtain ⟨-, -, encoded⟩ := Ixon.Verify.Canonical.deConstant_spec _ _ _ _ hd
          have e1 : bytes = Ixon.serConstant c := by
            rw [← decoded]
            exact encoded.symm
          exact (congrArg₂
            (fun (oa : Option _root_.Address) (ob : Option ByteArray) =>
              oa.bind fun a => ob.map fun bytes => (a, bytes)) ha hb).trans
            (congrArg (fun b => some (a, b)) e1)

/-- **The committed prelude rows are the 33 decoded committed records, in order, each with
its canonical bytes.** -/
theorem committedRows_eq :
    committedRows = committedPreludeList.map fun e => (e.1, Ixon.serConstant e.2) :=
  decoded_rows_eq "prelude" Ix.Kernel.Reader.RoleData.prelude preludeRecords_eq

/-! ## The store -/

/-- The committed records of the basis blocks and the quotient package: the first 24 of the
33 (the last nine are `And` and `Bool`). -/
def basisRows : List (_root_.Address × Ixon.Constant) := committedPreludeList.take 24

/-- The store's entries: each record under its address, with its canonical bytes. -/
def basisEntries : List (_root_.Address × Ixon.LazyConstant) :=
  basisRows.map fun e => (e.1, mkLazy (Ixon.serConstant e.2) e.2)

/-- **The store**: the 24 committed records of the basis blocks and the quotient package. -/
def basisStore : Ixon.Env := { consts := Std.HashMap.ofList basisEntries }

theorem basisRows_sub (e : _root_.Address × Ixon.Constant) (h : e ∈ basisRows) :
    e ∈ committedPreludeList :=
  List.mem_of_mem_take h

/-- The store's addresses are distinct (decided). -/
theorem basisEntries_distinct : basisEntries.Pairwise (fun a b => (a.1 == b.1) = false) := by
  decide +kernel

/-- No address of an `And` or `Bool` record is an address of the store (decided). -/
theorem rest_absent :
    (committedPreludeList.drop 24).all
      (fun e => (basisEntries.map Prod.fst).contains e.1 == false) = true := by
  decide +kernel

theorem store_get?_of_mem {a : _root_.Address} {c : Ixon.Constant} (h : (a, c) ∈ basisRows) :
    basisStore.consts.get? a = some (mkLazy (Ixon.serConstant c) c) := by
  have hmem : (a, mkLazy (Ixon.serConstant c) c) ∈ basisEntries :=
    List.mem_map.mpr ⟨(a, c), h, rfl⟩
  show (Std.HashMap.ofList basisEntries).get? a = some (mkLazy (Ixon.serConstant c) c)
  rw [Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.getElem?_ofList_of_mem (beq_self_eq_true a) basisEntries_distinct hmem

theorem store_get?_inv {a : _root_.Address} {lc : Ixon.LazyConstant}
    (h : basisStore.consts.get? a = some lc) :
    ∃ c, (a, c) ∈ basisRows ∧ lc = mkLazy (Ixon.serConstant c) c := by
  have h' : (Std.HashMap.ofList basisEntries)[a]? = some lc := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact h
  cases hc : (basisEntries.map Prod.fst).contains a with
  | false =>
    rw [Std.HashMap.getElem?_ofList_of_contains_eq_false hc] at h'
    cases h'
  | true =>
    have hmem : a ∈ basisEntries.map Prod.fst := List.mem_of_elem_eq_true hc
    obtain ⟨entry, hentry, hfst⟩ := List.mem_map.mp hmem
    obtain ⟨e, he, hee⟩ := List.mem_map.mp hentry
    have ha : e.1 = a := (congrArg Prod.fst hee).trans hfst
    have hmem' : (a, e.2) ∈ basisRows := by
      rw [← ha]
      exact he
    exact ⟨e.2, hmem', Option.some.inj (h.symm.trans (store_get?_of_mem hmem'))⟩

theorem store_record_of_mem {a : _root_.Address} {c : Ixon.Constant}
    (h : (a, c) ∈ basisRows) : recordOf basisStore a = some c := by
  have hdec : Ixon.deConstantExact (Ixon.serConstant c) = .ok c :=
    (committedPrelude_rows (a, c) (basisRows_sub (a, c) h)).2
  have h1 : recordOf basisStore a =
      (Ixon.deConstantExact (mkLazy (Ixon.serConstant c) c).rawBytes).toOption :=
    (congrArg (fun (o : Option Ixon.LazyConstant) =>
      o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) (store_get?_of_mem h)).trans
      rfl
  have h2 : Ixon.deConstantExact (mkLazy (Ixon.serConstant c) c).rawBytes = .ok c :=
    (congrArg Ixon.deConstantExact (mkLazy_rawBytes _ _)).trans hdec
  exact h1.trans ((congrArg Except.toOption h2).trans rfl)

theorem store_record_inv {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf basisStore a = some c) : (a, c) ∈ basisRows := by
  cases hg : basisStore.consts.get? a with
  | none =>
    have hn : recordOf basisStore a = none :=
      (congrArg (fun (o : Option Ixon.LazyConstant) =>
        o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) hg).trans rfl
    rw [hn] at h
    cases h
  | some lc =>
    obtain ⟨c', hmem, -⟩ := store_get?_inv hg
    have e : c' = c := Option.some.inj ((store_record_of_mem hmem).symm.trans h)
    rw [← e]
    exact hmem

/-! ## Decided facts about the 24 records -/

/-- `x` is an address of the store. -/
def hasKey (x : _root_.Address) : Bool := basisRows.any fun e => e.1 == x

theorem isSome_of_hasKey {x : _root_.Address} (h : hasKey x = true) :
    (recordOf basisStore x).isSome = true := by
  obtain ⟨e', he', hx⟩ := List.any_eq_true.mp h
  have e : e'.1 = x := beq_iff_eq.mp hx
  have hrec : recordOf basisStore x = some e'.2 := by
    rw [← e]
    exact store_record_of_mem (a := e'.1) (c := e'.2) he'
  exact (congrArg Option.isSome hrec).trans rfl

/-- The block of every record of the store is a record of the store (decided). -/
theorem owners_in : basisRows.all (fun e => hasKey (Ix.Cert.ownerOf e.1 e.2)) = true := by
  decide +kernel

/-- Every constant reference a record of the store uses is a record of the store (decided). -/
theorem refs_in :
    basisRows.all (fun e =>
      (usedRefIdxs e.2).all fun i => (e.2.refs[i]?).all hasKey) = true := by
  decide +kernel

/-- The members of a block record. -/
def membersOf : Ixon.ConstantInfo → Array Ixon.MutConst
  | .muts ms => ms
  | _ => #[]

/-- The number of constructors of an inductive member. -/
def ctorCount : Ixon.MutConst → Nat
  | .indc ind => ind.ctors.size
  | _ => 0

/-- The projection records of member `i` of the block at `B`: the member's, then one for each
constructor. -/
def projsOf (B : _root_.Address) (i : Nat) : Option Ixon.MutConst → List Ixon.Constant
  | some m =>
    memberProjection B i m :: (List.range (ctorCount m)).map fun j => constructorProjection B i j
  | none => []

/-- The projection records of every member and constructor of every block of the store. -/
def expectedProjs : List Ixon.Constant :=
  basisRows.flatMap fun e =>
    (List.range (membersOf e.2.info).size).flatMap fun i =>
      projsOf e.1 i ((membersOf e.2.info)[i]?)

/-- A cheap test that two records are the same projection. Only used to find a candidate;
the equality is then checked by evaluation. -/
def projTag : Ixon.ConstantInfo → Ixon.ConstantInfo → Bool
  | .dPrj x, .dPrj y => x.idx == y.idx && x.block == y.block
  | .iPrj x, .iPrj y => x.idx == y.idx && x.block == y.block
  | .rPrj x, .rPrj y => x.idx == y.idx && x.block == y.block
  | .cPrj x, .cPrj y => x.idx == y.idx && x.cidx == y.cidx && x.block == y.block
  | _, _ => false

/-- The record of the store that is the projection `p`, if any. -/
def findProj (p : Ixon.Constant) : Option (_root_.Address × Ixon.Constant) :=
  basisRows.find? fun e => projTag e.2.info p.info

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **Every projection record of a block of the store is a record of the store** (by
evaluation: the record found is the projection record, term for term). -/
theorem projs_found :
    expectedProjs.map (fun p => (findProj p).map (·.2)) = expectedProjs.map some :=
  rfl

theorem record_of_proj {p : Ixon.Constant} (h : p ∈ expectedProjs) :
    recordOf basisStore (Address.blake3Pure (Ixon.serConstant p)) = some p := by
  have hfound : (findProj p).map (·.2) = some p := map_eq_pointwise projs_found p h
  cases hf : findProj p with
  | none =>
    rw [hf] at hfound
    have e : (none : Option Ixon.Constant) = some p := hfound
    cases e
  | some e' =>
    rw [hf] at hfound
    have e : some e'.2 = some p := hfound
    have e2 : e'.2 = p := Option.some.inj e
    have he' : e' ∈ basisRows := List.mem_of_find?_eq_some hf
    have hh : Address.blake3Pure (Ixon.serConstant e'.2) = e'.1 :=
      committedRows_hashed (e'.1, Ixon.serConstant e'.2)
        (committedPrelude_rows e' (basisRows_sub e' he')).1
    rw [← e2, hh]
    exact store_record_of_mem (a := e'.1) (c := e'.2) he'

/-- A record of the store is a block. -/
def isMutsInfo : Ixon.ConstantInfo → Bool
  | .muts _ => true
  | _ => false

/-- The key of a pinned basis constant. -/
def isBasisKey : Key .anon → Bool
  | .role r => basisRoleOrder.contains r
  | _ => false

theorem isBasisKey_role {k : Key .anon} (h : isBasisKey k = true) :
    ∃ r ∈ basisRoleOrder, k = .role r := by
  cases k with
  | role r => exact ⟨r, List.mem_of_elem_eq_true h, rfl⟩
  | id _ =>
    have h' : false = true := h
    cases h'
  | aux _ _ =>
    have h' : false = true := h
    cases h'

/-- Every record of the store is a block or sits at an address the default table binds a
basis or quotient role to (decided). -/
theorem keys_pinned :
    basisRows.all (fun e =>
      isMutsInfo e.2.info || isBasisKey (keyOf committedDefaultRoleTable e.1)) = true := by
  decide +kernel

/-- The roles of the first six groups are the basis and quotient roles (decided). -/
theorem groups_basis :
    (List.range 6).all (fun g => (roleGroup g).all basisRoleOrder.contains) = true := by
  decide +kernel

/-- The first six groups need nothing outside themselves (decided). -/
theorem groups_closed :
    (List.range 6).all (fun g =>
      (groupNeeded g).all fun r => decide (Ix.SpecDigest.groupOf r < 6)) = true := by
  decide +kernel

/-! ## The clauses -/

/-- The environment stores the pin at the key of every basis and quotient role. -/
theorem basisEnv_find {r : Role} (hr : r ∈ basisRoleOrder) :
    ∃ ci, basisEnv.find? (Key.role r) = some ci ∧ PinnedBasis ci := by
  have hn : basisEnv.consts.map (·.name) = basisRoleOrder.map Key.role := rfl
  have hk : Key.role r ∈ basisEnv.consts.map (·.name) := by
    rw [hn]
    exact List.mem_map.mpr ⟨r, hr, rfl⟩
  obtain ⟨ci, hci, hname⟩ := List.mem_map.mp hk
  have hname' : ci.name = Key.role r := hname
  have hf := Ix.Cert.AcceptedKeys.find?_name_of_nodup (l := basisEnv.consts) basisEnv_nodup ci hci
  rw [hname'] at hf
  exact ⟨ci, hf, basisEnv_pinned ci hci⟩

theorem groupRole_basis {g : Nat} (hg : g < 6) {r : Role} (hr : r ∈ roleGroup g) :
    r ∈ basisRoleOrder := by
  have h1 : (roleGroup g).all basisRoleOrder.contains = true :=
    List.all_eq_true.mp groups_basis g (List.mem_range.mpr hg)
  have h2 : basisRoleOrder.contains r = true := List.all_eq_true.mp h1 r hr
  exact List.mem_of_elem_eq_true h2

theorem preludePinned_default : PreludePinned committedDefaultRoleTable := by
  obtain ⟨b₀, t₀, hdef, hadm⟩ := IxVM.Refinement.Assembly.defaultAdmits
  have ht₀ : t₀ = committedDefaultRoleTable := admitBinding_committedDefault hdef hadm
  unfold PreludePinned
  exact ⟨b₀, t₀, hdef, hadm, fun _ _ => by rw [ht₀]⟩

theorem store_hashed : EnvSelfHashed basisStore := by
  unfold EnvSelfHashed
  constructor
  · intro a _ h
    obtain ⟨c, hmem, hlc⟩ := store_get?_inv h
    rw [hlc, mkLazy_rawBytes]
    exact committedRows_hashed (a, Ixon.serConstant c)
      (committedPrelude_rows (a, c) (basisRows_sub (a, c) hmem)).1
  · intro a _ h
    have hn : basisStore.blobs.get? a = none := emptyMap_get? a
    rw [hn] at h
    cases h

/-- The zero address is not an address of the store (decided). -/
theorem zero_absent :
    (basisEntries.map Prod.fst).contains Ix.HostAdmission.Merkle.padding = false := by
  decide +kernel

theorem store_zeroFree :
    basisStore.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      basisStore.blobs.get? Ix.HostAdmission.Merkle.padding = none := by
  constructor
  · show (Std.HashMap.ofList basisEntries).get? Ix.HostAdmission.Merkle.padding = none
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_ofList_of_contains_eq_false zero_absent
  · exact emptyMap_get? Ix.HostAdmission.Merkle.padding

theorem store_committed : AgreesCommitted basisStore := by
  unfold AgreesCommitted
  intro p hp lc h
  rw [committedRows_eq] at hp
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp
  have hp1 : p.1 = e.1 := congrArg Prod.fst hpe.symm
  have hp2 : p.2 = Ixon.serConstant e.2 := congrArg Prod.snd hpe.symm
  have hsplit : e ∈ basisRows ∨ e ∈ committedPreludeList.drop 24 := by
    have hboth : e ∈ committedPreludeList.take 24 ++ committedPreludeList.drop 24 := by
      rw [List.take_append_drop]
      exact he
    exact List.mem_append.mp hboth
  rcases hsplit with hb | hd
  · rw [hp1, store_get?_of_mem (a := e.1) (c := e.2) hb] at h
    have e1 : mkLazy (Ixon.serConstant e.2) e.2 = lc := Option.some.inj h
    rw [hp2, ← e1, mkLazy_rawBytes]
  · have hF : ((basisEntries.map Prod.fst).contains e.1 == false) = true :=
      List.all_eq_true.mp rest_absent e hd
    have hc : (basisEntries.map Prod.fst).contains e.1 = false := beq_iff_eq.mp hF
    have hnone : basisStore.consts.get? e.1 = none := by
      show (Std.HashMap.ofList basisEntries).get? e.1 = none
      rw [Std.HashMap.get?_eq_getElem?]
      exact Std.HashMap.getElem?_ofList_of_contains_eq_false hc
    rw [hp1, hnone] at h
    cases h

theorem store_usedClosed : UsedClosed basisStore := by
  unfold UsedClosed
  constructor
  · intro a c hc
    have hmem := store_record_inv hc
    constructor
    · have h1 : hasKey (Ix.Cert.ownerOf a c) = true :=
        List.all_eq_true.mp owners_in (a, c) hmem
      exact isSome_of_hasKey h1
    · intro i hi x hx
      have h1 : (usedRefIdxs c).all (fun i => (c.refs[i]?).all hasKey) = true :=
        List.all_eq_true.mp refs_in (a, c) hmem
      have h2 : (c.refs[i]?).all hasKey = true := List.all_eq_true.mp h1 i hi
      rw [hx] at h2
      have h3 : hasKey x = true := h2
      exact isSome_of_hasKey h3
  · intro B c ms hc hinfo i m hmi
    have hmem := store_record_inv hc
    have hms : membersOf c.info = ms := (congrArg membersOf hinfo).trans rfl
    have hi : i < ms.size := by
      rcases Nat.lt_or_ge i ms.size with hl | hge
      · exact hl
      · rw [Array.getElem?_eq_none hge] at hmi
        cases hmi
    have hp : ∀ p ∈ projsOf B i (some m), p ∈ expectedProjs := by
      intro p hpm
      unfold expectedProjs
      refine List.mem_flatMap.mpr ⟨(B, c), hmem, ?_⟩
      refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr ?_, ?_⟩
      · show i < (membersOf c.info).size
        rw [hms]
        exact hi
      · show p ∈ projsOf B i ((membersOf c.info)[i]?)
        rw [hms, hmi]
        exact hpm
    constructor
    · exact record_of_proj (hp (memberProjection B i m) List.mem_cons_self)
    · intro ind hind j hj
      refine record_of_proj (hp (constructorProjection B i j) ?_)
      rw [hind]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

theorem store_stored : ∀ a, (∃ ci₀, Reads committedDefaultRoleTable basisStore a ci₀) →
    ∃ ci, basisEnv.find? (keyOf committedDefaultRoleTable a) = some ci ∧
      (PinnedBasis ci ∨
        ∃ ci₀, Reads committedDefaultRoleTable basisStore a ci₀ ∧ StoredAs ci ci₀) := by
  intro a hr
  obtain ⟨_, c, hc, hread⟩ := hr
  have hmem := store_record_inv hc
  have hF : (isMutsInfo c.info || isBasisKey (keyOf committedDefaultRoleTable a)) = true :=
    List.all_eq_true.mp keys_pinned (a, c) hmem
  have key : ∃ r ∈ basisRoleOrder, keyOf committedDefaultRoleTable a = .role r := by
    generalize c.info = info at hread hF
    cases info <;> first
      | exact False.elim hread
      | exact isBasisKey_role (k := keyOf committedDefaultRoleTable a) hF
  obtain ⟨r, hrole, hkey⟩ := key
  obtain ⟨ci, hfind, hpin⟩ := basisEnv_find hrole
  rw [hkey]
  exact ⟨ci, hfind, Or.inl hpin⟩

/-! ## The inhabitant -/

/-- **The default table is valid, in the public sense, on the basis and quotient groups**,
with the store of their 24 committed records and the environment of the kernel's pins. -/
theorem tableShape_store :
    TableShape.{u} committedDefaultRoleTable (fun g => g < 6) basisStore basisEnv := {
  needsClosed := fun g hg r hr => by
    have h1 : (groupNeeded g).all (fun r => decide (Ix.SpecDigest.groupOf r < 6)) = true :=
      List.all_eq_true.mp groups_closed g (List.mem_range.mpr hg)
    have h2 : decide (Ix.SpecDigest.groupOf r < 6) = true := List.all_eq_true.mp h1 r hr
    exact of_decide_eq_true h2
  bound := fun _ _ r _ => defaultTable_allBound r
  prelude := preludePinned_default
  literals := committedDefaultRoleTable_literalSupportBound
  hashed := store_hashed
  usedClosed := store_usedClosed
  committed := store_committed
  zeroFree := store_zeroFree
  kept := fun _ _ _ hg hr _ _ => by
    obtain ⟨ci, hfind, hpin⟩ := basisEnv_find (groupRole_basis hg hr)
    exact ⟨ci, hfind, Or.inl hpin⟩
  reading := {
    nodup := basisEnv_nodup
    provenance := fun ci hci => by
      rw [basisEnv_claimed] at hci
      exact Or.inr (Or.inl (basisEnv_pinned ci hci))
    stored := store_stored }
  pins := basisEnv_pins
  preludeKept := fun _ _ _ hg hr _ _ => by
    obtain ⟨ci, hfind, hpin⟩ := basisEnv_find (groupRole_basis hg hr)
    exact ⟨ci, hfind, Or.inl hpin⟩
  model := fun W _ => by
    rw [basisEnv_claimed]
    exact basisEnv_model W }

end IxVM.Refinement.StoreInhabit
