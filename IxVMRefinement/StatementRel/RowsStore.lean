import IxVMRefinement.StatementRel.RowReader

/-! # A store of committed prelude rows

`rowsEnv rows` is the store that holds the given committed prelude records, each under its
address with its canonical bytes. For rows at distinct addresses, each a row of the committed
prelude (`Committed`), this file proves the lookup lemmas, presents the store to the row reader
(`rowStoreOf`), and proves the clauses of `TableShape` that are about the store alone
(`EnvSelfHashed`, `AgreesCommitted`, `UsedClosed`, the zero address) from facts about the rows
that are decided by evaluation.

Hash maps do not evaluate in the kernel, so every lookup is reasoned through the list of
entries.
-/

namespace IxVM.Refinement.RowsStore

open Ix.Kernel
open IxVM.Consistency
open IxVM.Refinement.RoleVal
open IxVM.Refinement.ClosedFacts
open IxVM.Refinement.StoreInhabit (committedRows_eq)
open IxVM.Refinement.RowReader
open IxVM.Refinement.TableInhabit (emptyMap_get?)
open IxVM.Refinement.Claim (mkLazy mkLazy_rawBytes)

/-! ## The store -/

/-- The entries of the store: each row's record under its address, with its canonical bytes. -/
def entriesOf (rows : List Row) : List (_root_.Address × Ixon.LazyConstant) :=
  rows.map fun e => (e.1, mkLazy (Ixon.serConstant e.2) e.2)

/-- **The store of the rows.** -/
def rowsEnv (rows : List Row) : Ixon.Env := { consts := Std.HashMap.ofList (entriesOf rows) }

/-- **The rows are committed prelude records at distinct addresses.** -/
structure Committed (rows : List Row) : Prop where
  distinct : (entriesOf rows).Pairwise (fun a b => (a.1 == b.1) = false)
  sub : ∀ e ∈ rows, e ∈ committedPreludeList

/-- `x` is the address of a row. -/
def hasKeyIn (rows : List Row) (x : _root_.Address) : Bool := rows.any fun e => e.1 == x

/-- Two members of a list of pairs with distinct first components and the same first component
are equal. -/
theorem eq_of_pairwise_fst {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)}, l.Pairwise (fun a b => (a.1 == b.1) = false) →
      ∀ {x y : α × β}, x ∈ l → y ∈ l → x.1 = y.1 → x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | z :: zs, h, x, y, hx, hy, hxy => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with hxz | hx'
    · rcases List.mem_cons.mp hy with hyz | hy'
      · exact hxz.trans hyz.symm
      · have h1 : (z.1 == y.1) = false := h.1 y hy'
        rw [← hxz, hxy, beq_self_eq_true] at h1
        cases h1
    · rcases List.mem_cons.mp hy with hyz | hy'
      · have h1 : (z.1 == x.1) = false := h.1 x hx'
        rw [← hyz, ← hxy, beq_self_eq_true] at h1
        cases h1
      · exact eq_of_pairwise_fst h.2 hx' hy' hxy

/-- The committed prelude records are at distinct addresses (decided). -/
theorem committedPrelude_distinct :
    committedPreludeList.Pairwise (fun a b => (a.1 == b.1) = false) := by
  decide +kernel

variable {rows : List Row}

theorem get?_of_mem (h : Committed rows) {a : _root_.Address} {c : Ixon.Constant}
    (hm : (a, c) ∈ rows) :
    (rowsEnv rows).consts.get? a = some (mkLazy (Ixon.serConstant c) c) := by
  have hmem : (a, mkLazy (Ixon.serConstant c) c) ∈ entriesOf rows :=
    List.mem_map.mpr ⟨(a, c), hm, rfl⟩
  show (Std.HashMap.ofList (entriesOf rows)).get? a = some (mkLazy (Ixon.serConstant c) c)
  rw [Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.getElem?_ofList_of_mem (beq_self_eq_true a) h.distinct hmem

theorem get?_of_not_hasKey {a : _root_.Address} (hk : hasKeyIn rows a = false) :
    (rowsEnv rows).consts.get? a = none := by
  have hc : ((entriesOf rows).map Prod.fst).contains a = false := by
    cases hc' : ((entriesOf rows).map Prod.fst).contains a with
    | false => rfl
    | true =>
      have hmem : a ∈ (entriesOf rows).map Prod.fst := List.mem_of_elem_eq_true hc'
      obtain ⟨entry, hentry, hfst⟩ := List.mem_map.mp hmem
      obtain ⟨e, he, hee⟩ := List.mem_map.mp hentry
      have ha : e.1 = a := (congrArg Prod.fst hee).trans hfst
      have hk' : hasKeyIn rows a = true := List.any_eq_true.mpr ⟨e, he, beq_iff_eq.mpr ha⟩
      rw [hk] at hk'
      cases hk'
  show (Std.HashMap.ofList (entriesOf rows)).get? a = none
  rw [Std.HashMap.get?_eq_getElem?]
  exact Std.HashMap.getElem?_ofList_of_contains_eq_false hc

theorem get?_inv (h : Committed rows) {a : _root_.Address} {lc : Ixon.LazyConstant}
    (hg : (rowsEnv rows).consts.get? a = some lc) :
    ∃ c, (a, c) ∈ rows ∧ lc = mkLazy (Ixon.serConstant c) c := by
  cases hk : hasKeyIn rows a with
  | false =>
    rw [get?_of_not_hasKey hk] at hg
    cases hg
  | true =>
    obtain ⟨e, he, hea⟩ := List.any_eq_true.mp hk
    have ha : e.1 = a := beq_iff_eq.mp hea
    have hmem : (a, e.2) ∈ rows := by
      rw [← ha]
      exact he
    exact ⟨e.2, hmem, Option.some.inj (hg.symm.trans (get?_of_mem h hmem))⟩

theorem record_of_mem (h : Committed rows) {a : _root_.Address} {c : Ixon.Constant}
    (hm : (a, c) ∈ rows) : recordOf (rowsEnv rows) a = some c := by
  have hdec : Ixon.deConstantExact (Ixon.serConstant c) = .ok c :=
    (committedPrelude_rows (a, c) (h.sub (a, c) hm)).2
  have h1 : recordOf (rowsEnv rows) a =
      (Ixon.deConstantExact (mkLazy (Ixon.serConstant c) c).rawBytes).toOption :=
    (congrArg (fun (o : Option Ixon.LazyConstant) =>
      o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) (get?_of_mem h hm)).trans
      rfl
  have h2 : Ixon.deConstantExact (mkLazy (Ixon.serConstant c) c).rawBytes = .ok c :=
    (congrArg Ixon.deConstantExact (mkLazy_rawBytes _ _)).trans hdec
  exact h1.trans ((congrArg Except.toOption h2).trans rfl)

theorem record_inv (h : Committed rows) {a : _root_.Address} {c : Ixon.Constant}
    (hr : recordOf (rowsEnv rows) a = some c) : (a, c) ∈ rows := by
  cases hg : (rowsEnv rows).consts.get? a with
  | none =>
    have hn : recordOf (rowsEnv rows) a = none :=
      (congrArg (fun (o : Option Ixon.LazyConstant) =>
        o.bind fun lc => (Ixon.deConstantExact lc.rawBytes).toOption) hg).trans rfl
    rw [hn] at hr
    cases hr
  | some lc =>
    obtain ⟨c', hmem, -⟩ := get?_inv h hg
    have e : c' = c := Option.some.inj ((record_of_mem h hmem).symm.trans hr)
    rw [← e]
    exact hmem

theorem isSome_of_hasKey (h : Committed rows) {x : _root_.Address} (hk : hasKeyIn rows x = true) :
    (recordOf (rowsEnv rows) x).isSome = true := by
  obtain ⟨e', he', hx⟩ := List.any_eq_true.mp hk
  have e : e'.1 = x := beq_iff_eq.mp hx
  have hrec : recordOf (rowsEnv rows) x = some e'.2 := by
    rw [← e]
    exact record_of_mem h (a := e'.1) (c := e'.2) he'
  exact (congrArg Option.isSome hrec).trans rfl

/-- The store has no blobs. -/
theorem blobs_none (a : _root_.Address) : (rowsEnv rows).blobs.get? a = none :=
  emptyMap_get? a

/-! ## The store as a store of rows -/

/-- **The store, as a store of rows for the row reader**, given that every projection record
of a block among the rows is one of the rows (by evaluation: the row found is the projection
record, term for term). -/
def rowStoreOf (rows : List Row) (h : Committed rows)
    (hp : (expectedProjsOf rows).map (fun p => (findProjOf rows p).map (·.2)) =
      (expectedProjsOf rows).map some) :
    RowStore committedDefaultRoleTable where
  rows := rows
  store := recordOf (rowsEnv rows)
  blob := fun x => (rowsEnv rows).blobs.get? x
  checked := committedDefaultRoleTable_check
  holds := fun e he => record_of_mem h (a := e.1) (c := e.2) he
  only := fun _ _ hc => record_inv h hc
  hashed := fun e he =>
    committedRows_hashed (e.1, Ixon.serConstant e.2) (committedPrelude_rows e (h.sub e he)).1
  projs := map_eq_pointwise hp

/-! ## The clauses of `TableShape` about the store alone -/

theorem hashed (h : Committed rows) : EnvSelfHashed (rowsEnv rows) := by
  unfold EnvSelfHashed
  constructor
  · intro a _ hg
    obtain ⟨c, hmem, hlc⟩ := get?_inv h hg
    rw [hlc, mkLazy_rawBytes]
    exact committedRows_hashed (a, Ixon.serConstant c)
      (committedPrelude_rows (a, c) (h.sub _ hmem)).1
  · intro a _ hg
    rw [blobs_none a] at hg
    cases hg

theorem zeroFree (hz : hasKeyIn rows Ix.HostAdmission.Merkle.padding = false) :
    (rowsEnv rows).consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      (rowsEnv rows).blobs.get? Ix.HostAdmission.Merkle.padding = none :=
  ⟨get?_of_not_hasKey hz, blobs_none _⟩

theorem committed (h : Committed rows) : AgreesCommitted (rowsEnv rows) := by
  unfold AgreesCommitted
  intro p hp lc hl
  rw [committedRows_eq] at hp
  obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp
  obtain ⟨c, hmem, hlc⟩ := get?_inv h hl
  have hc : (p.1, c) ∈ committedPreludeList := h.sub _ hmem
  have hp1 : p.1 = e.1 := (congrArg Prod.fst hpe).symm
  have heq : (p.1, c) = e := eq_of_pairwise_fst committedPrelude_distinct hc he hp1
  have hp2 : p.2 = Ixon.serConstant e.2 := (congrArg Prod.snd hpe).symm
  rw [hlc, mkLazy_rawBytes, hp2, ← heq]

/-- Every projection record of a block among the rows is the record of the store at its
address. -/
theorem record_of_proj (h : Committed rows)
    (hp : (expectedProjsOf rows).map (fun p => (findProjOf rows p).map (·.2)) =
      (expectedProjsOf rows).map some)
    {p : Ixon.Constant} (hmem : p ∈ expectedProjsOf rows) :
    recordOf (rowsEnv rows) (Address.blake3Pure (Ixon.serConstant p)) = some p := by
  have hfound : (findProjOf rows p).map (·.2) = some p := map_eq_pointwise hp p hmem
  cases hf : findProjOf rows p with
  | none =>
    rw [hf] at hfound
    have e : (none : Option Ixon.Constant) = some p := hfound
    cases e
  | some e' =>
    obtain ⟨he', e2, e1⟩ := found_spec (rowStoreOf rows h hp) hmem hf
    rw [← e1]
    have hm : (e'.1, p) ∈ rows := by
      rw [← e2]
      exact he'
    exact record_of_mem h hm

theorem usedClosed (h : Committed rows)
    (hp : (expectedProjsOf rows).map (fun p => (findProjOf rows p).map (·.2)) =
      (expectedProjsOf rows).map some)
    (howners : rows.all (fun e => hasKeyIn rows (Ix.Cert.ownerOf e.1 e.2)) = true)
    (hrefs : rows.all (fun e =>
      (usedRefIdxs e.2).all fun i => (e.2.refs[i]?).all (hasKeyIn rows)) = true) :
    UsedClosed (rowsEnv rows) := by
  unfold UsedClosed
  constructor
  · intro a c hc
    have hmem := record_inv h hc
    constructor
    · exact isSome_of_hasKey h (List.all_eq_true.mp howners (a, c) hmem)
    · intro i hi x hx
      have h1 : (usedRefIdxs c).all (fun i => (c.refs[i]?).all (hasKeyIn rows)) = true :=
        List.all_eq_true.mp hrefs (a, c) hmem
      have h2 : (c.refs[i]?).all (hasKeyIn rows) = true := List.all_eq_true.mp h1 i hi
      rw [hx] at h2
      exact isSome_of_hasKey h h2
  · intro B c ms hc hinfo i m hmi
    have hmem := record_inv h hc
    constructor
    · exact record_of_proj h hp (mem_expected hmem hinfo hmi _ List.mem_cons_self)
    · intro ind hind j hj
      rw [hind] at hmi
      exact record_of_proj h hp (mem_expected hmem hinfo hmi _ (ctor_in_projs hj))

end IxVM.Refinement.RowsStore
