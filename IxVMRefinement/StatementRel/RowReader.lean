import IxVMRefinement.StatementRel.ExprReader
import IxVMRefinement.StatementRel.StoreInhabit
import Ix.IxVM.Consistency.StoredCheck

/-! # A proof-returning reader of the records of a store

For a store given by a list of rows (address, record) that are closed terms, `readRow`
computes what the record at a row declares under the role table (`Reads`) and returns it
with the proof. It covers inductive type and constructor projection records, standalone
recursor records, quotient records and axiom records; a block record has no reading.

`RowStore` is what the reader needs of the store: it holds exactly the rows, each under the
BLAKE3 hash of its canonical bytes, and every member and constructor projection record of
its blocks is one of the rows (found by a cheap search and checked term for term).

`reads_stored` packages a whole store: if every row that is not a block has a reading that
the constant the environment holds at its key stores (`rowOk`, evaluated), then every
address of the store with a reading has a reading the environment stores.
-/

namespace IxVM.Refinement.RowReader

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open IxVM.Refinement.StoreInhabit (membersOf ctorCount projsOf projTag isMutsInfo)
open IxVM.Refinement.ExprReader

/-- A row of a store: an address and the record at it. -/
abbrev Row := _root_.Address × Ixon.Constant

/-- The projection records of every member and constructor of every block among the rows. -/
def expectedProjsOf (rows : List Row) : List Ixon.Constant :=
  rows.flatMap fun e =>
    (List.range (membersOf e.2.info).size).flatMap fun i =>
      projsOf e.1 i ((membersOf e.2.info)[i]?)

/-- The row that is the projection `p`, by a cheap search. -/
def findProjOf (rows : List Row) (p : Ixon.Constant) : Option Row :=
  rows.find? fun e => projTag e.2.info p.info

/-- The row at the address `B`. -/
def blockOf (rows : List Row) (B : _root_.Address) : Option Row :=
  rows.find? fun e => e.1 == B

/-- **A store given by rows**: it holds exactly the rows, each under the BLAKE3 hash of its
canonical bytes, and the projection records of its blocks are among the rows. -/
structure RowStore (t : RoleTable) where
  rows : List Row
  store : Store
  blob : _root_.Address → Option ByteArray
  checked : t.check = .ok ()
  holds : ∀ e ∈ rows, store e.1 = some e.2
  only : ∀ a c, store a = some c → (a, c) ∈ rows
  hashed : ∀ e ∈ rows, Address.blake3Pure (Ixon.serConstant e.2) = e.1
  projs : ∀ p ∈ expectedProjsOf rows, (findProjOf rows p).map (·.2) = some p

variable {t : RoleTable}

theorem map_eq_pointwise {α β : Type} {f g : α → β} :
    ∀ {l : List α}, l.map f = l.map g → ∀ a ∈ l, f a = g a
  | [], _, _, ha => nomatch ha
  | x :: xs, h, a, ha => by
    rw [List.map_cons, List.map_cons] at h
    injection h with h1 h2
    rcases List.mem_cons.mp ha with hax | ha'
    · rw [hax]
      exact h1
    · exact map_eq_pointwise h2 a ha'

/-! ## Rows and projection records -/

theorem RowStore.snd_eq (S : RowStore t) {a : _root_.Address} {c c' : Ixon.Constant}
    (h : (a, c) ∈ S.rows) (h' : (a, c') ∈ S.rows) : c = c' :=
  Option.some.inj ((S.holds (a, c) h).symm.trans (S.holds (a, c') h'))

theorem blockOf_mem {rows : List Row} {B : _root_.Address} {eb : Row}
    (h : blockOf rows B = some eb) : (B, eb.2) ∈ rows := by
  have hmem : eb ∈ rows := List.mem_of_find?_eq_some h
  have hb : (eb.1 == B) = true := List.find?_some (p := fun e : Row => e.1 == B) h
  have he : eb.1 = B := beq_iff_eq.mp hb
  rw [← he]
  exact hmem

theorem mem_expected {rows : List Row} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {m : Ixon.MutConst} (hB : (B, cb) ∈ rows)
    (hms : cb.info = .muts ms) (hm : ms[i]? = some m) :
    ∀ p ∈ projsOf B i (some m), p ∈ expectedProjsOf rows := by
  have hms' : membersOf cb.info = ms := (congrArg membersOf hms).trans rfl
  have hi : i < ms.size := by
    rcases Nat.lt_or_ge i ms.size with hl | hge
    · exact hl
    · rw [Array.getElem?_eq_none hge] at hm
      cases hm
  intro p hpm
  unfold expectedProjsOf
  refine List.mem_flatMap.mpr ⟨(B, cb), hB, ?_⟩
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr ?_, ?_⟩
  · show i < (membersOf cb.info).size
    rw [hms']
    exact hi
  · show p ∈ projsOf B i ((membersOf cb.info)[i]?)
    rw [hms', hm]
    exact hpm

theorem ctor_in_projs {B : _root_.Address} {i j : Nat} {ind : Ixon.Inductive}
    (hj : j < ind.ctors.size) :
    constructorProjection B i j ∈ projsOf B i (some (.indc ind)) :=
  List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

/-- The row found for an expected projection record is that record, at its address. -/
theorem found_spec (S : RowStore t) {p : Ixon.Constant} {e' : Row}
    (hp : p ∈ expectedProjsOf S.rows) (hf : findProjOf S.rows p = some e') :
    e' ∈ S.rows ∧ e'.2 = p ∧ e'.1 = Address.blake3Pure (Ixon.serConstant p) := by
  have h1 := S.projs p hp
  rw [hf] at h1
  have h2 : some e'.2 = some p := h1
  have h3 : e'.2 = p := Option.some.inj h2
  have hmem : e' ∈ S.rows := List.mem_of_find?_eq_some hf
  refine ⟨hmem, h3, ?_⟩
  rw [← h3]
  exact (S.hashed e' hmem).symm

/-- A row at the address of the row found for an expected projection record is that
projection record. -/
theorem row_is_proj (S : RowStore t) {a : _root_.Address} {c p : Ixon.Constant}
    (hrow : (a, c) ∈ S.rows) (hp : p ∈ expectedProjsOf S.rows)
    (hfound : (findProjOf S.rows p).map (·.1) = some a) :
    c = p ∧ a = Address.blake3Pure (Ixon.serConstant p) := by
  cases hf : findProjOf S.rows p with
  | none =>
    rw [hf] at hfound
    have h' : (none : Option _root_.Address) = some a := hfound
    cases h'
  | some e' =>
    rw [hf] at hfound
    have h1 : some e'.1 = some a := hfound
    have ha : e'.1 = a := Option.some.inj h1
    obtain ⟨hmem, h3, h4⟩ := found_spec S hp hf
    have hmem' : (a, e'.2) ∈ S.rows := by
      rw [← ha]
      exact hmem
    refine ⟨(S.snd_eq hrow hmem').trans h3, ?_⟩
    rw [← ha]
    exact h4

/-! ## Safety -/

/-- `InLogicMut`, decided. -/
def inLogicMutB : Ixon.MutConst → Bool
  | .defn d => decide (Ix.Kernel.Reader.safetyDecline d = none)
  | .indc i => decide (i.isUnsafe = false ∧ ∀ ctor ∈ i.ctors.toList, ctor.isUnsafe = false)
  | .recr r => decide (r.isUnsafe = false)

theorem inLogicMut_of_B {m : Ixon.MutConst} (h : inLogicMutB m = true) : InLogicMut m := by
  cases m with
  | defn d => exact of_decide_eq_true (p := Ix.Kernel.Reader.safetyDecline d = none) h
  | indc i =>
    exact of_decide_eq_true
      (p := i.isUnsafe = false ∧ ∀ ctor ∈ i.ctors.toList, ctor.isUnsafe = false) h
  | recr r => exact of_decide_eq_true (p := r.isUnsafe = false) h

theorem inLogic_muts {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hms : cb.info = .muts ms)
    (h : ms.toList.all inLogicMutB = true) : InLogic cb := by
  unfold InLogic
  rw [hms]
  exact fun m hm => inLogicMut_of_B (List.all_eq_true.mp h m hm)

theorem inLogic_recr {c : Ixon.Constant} {rc : Ixon.Recursor} (hinfo : c.info = .recr rc)
    (h : rc.isUnsafe = false) : InLogic c := by
  unfold InLogic
  rw [hinfo]
  exact h

theorem inLogic_axio {c : Ixon.Constant} {ax : Ixon.Axiom} (hinfo : c.info = .axio ax)
    (h : ax.isUnsafe = false) : InLogic c := by
  unfold InLogic
  rw [hinfo]
  exact h

/-! ## `recur` in a standalone record and in a block -/

/-- The key `recur k` reads as in a standalone record at `a`. -/
def soloKey (t : RoleTable) (a : _root_.Address) : Nat → Option (Key .anon) :=
  fun k => if k == 0 then some (keyOf t a) else none

theorem soloKey_ok (t : RoleTable) (a : _root_.Address) :
    ∀ (k : Nat) (kk : Key .anon), soloKey t a k = some kk →
      soloSelf t a k = some (Except.ok kk) := by
  intro k kk h
  unfold soloKey at h
  unfold soloSelf
  by_cases hk : (k == 0) = true
  · rw [ite_eq_left hk] at h
    rw [ite_eq_left hk]
    exact congrArg (fun x => some (Except.ok x)) (Option.some.inj h)
  · rw [ite_eq_right hk] at h
    cases h

/-- The key `recur k` reads as in the block at `B` with members `ms`: the key of the row
found for member `k`'s projection record. -/
def blockKey (rows : List Row) (t : RoleTable) (B : _root_.Address) (ms : Array Ixon.MutConst) :
    Nat → Option (Key .anon) :=
  fun k => (ms[k]?).bind fun m =>
    (findProjOf rows (memberProjection B k m)).map fun e' => keyOf t e'.1

theorem blockKey_ok (S : RowStore t) {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hB : (B, cb) ∈ S.rows) (hms : cb.info = .muts ms) :
    ∀ (k : Nat) (kk : Key .anon), blockKey S.rows t B ms k = some kk →
      blockSelf t B ms k = some (Except.ok kk) := by
  intro k kk h
  unfold blockKey at h
  unfold blockSelf
  cases hm : ms[k]? with
  | none =>
    rw [hm] at h
    have h' : (none : Option (Key .anon)) = some kk := h
    cases h'
  | some m =>
    rw [hm] at h
    have h1 : (findProjOf S.rows (memberProjection B k m)).map (fun e' => keyOf t e'.1) =
        some kk := h
    cases hf : findProjOf S.rows (memberProjection B k m) with
    | none =>
      rw [hf] at h1
      have h' : (none : Option (Key .anon)) = some kk := h1
      cases h'
    | some e' =>
      rw [hf] at h1
      have h2 : some (keyOf t e'.1) = some kk := h1
      have hk : keyOf t e'.1 = kk := Option.some.inj h2
      obtain ⟨-, -, h4⟩ :=
        found_spec S (mem_expected hB hms hm _ List.mem_cons_self) hf
      rw [h4] at hk
      exact congrArg (fun x => some (Except.ok x)) hk

/-! ## Readings -/

/-- A reading of the record at `a`: a constant with the proof that the record declares it. -/
abbrev Reading (S : RowStore t) (a : _root_.Address) :=
  { ci₀ : ConstantInfo .anon // ReadsIn t S.store S.blob a ci₀ }

theorem readsIn_intro (S : RowStore t) {a : _root_.Address} {c : Ixon.Constant}
    {ci₀ : ConstantInfo .anon} {info : Ixon.ConstantInfo} (hrow : (a, c) ∈ S.rows)
    (hinfo : c.info = info) (h : ReadsRecord t S.store S.blob a c ci₀ info) :
    ReadsIn t S.store S.blob a ci₀ :=
  Exists.intro c (And.intro (S.holds (a, c) hrow) (by rw [hinfo]; exact h))

theorem memberAt_of (S : RowStore t) {a : _root_.Address} {c : Ixon.Constant}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    {m : Ixon.MutConst} (hrow : (a, c) ∈ S.rows) (hB : (B, cb) ∈ S.rows)
    (hms : cb.info = .muts ms) (hm : ms[i]? = some m)
    (hfound : (findProjOf S.rows (memberProjection B i m)).map (·.1) = some a)
    (hlogic : ms.toList.all inLogicMutB = true) : MemberAt S.store a c B cb ms i m := by
  obtain ⟨hc, ha⟩ :=
    row_is_proj S hrow (mem_expected hB hms hm _ List.mem_cons_self) hfound
  unfold MemberAt
  exact ⟨S.holds (B, cb) hB, hms, hm, hc, ha, inLogic_muts hms hlogic⟩

/-- **An inductive type's projection row, with its block.** -/
structure IndRow (S : RowStore t) (a : _root_.Address) where
  c : Ixon.Constant
  p : Ixon.InductiveProj
  cb : Ixon.Constant
  ms : Array Ixon.MutConst
  ind : Ixon.Inductive
  hrow : (a, c) ∈ S.rows
  hinfo : c.info = .iPrj p
  hB : (p.block, cb) ∈ S.rows
  hms : cb.info = .muts ms
  hmember : MemberAt S.store a c p.block cb ms p.idx.toNat (.indc ind)

/-- The row at `a` as an inductive type's projection row, if it is one. -/
def indRow? (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Option (IndRow S a) :=
  match hinfo : c.info with
  | .iPrj p =>
    match hb : blockOf S.rows p.block with
    | some eb =>
      match hms : eb.2.info with
      | .muts ms =>
        match hm : ms[p.idx.toNat]? with
        | some (.indc ind) =>
          if hf : (findProjOf S.rows (memberProjection p.block p.idx.toNat (.indc ind))).map
              (·.1) = some a then
            if hl : ms.toList.all inLogicMutB = true then
              some { c := c, p := p, cb := eb.2, ms := ms, ind := ind, hrow := hrow,
                     hinfo := hinfo, hB := blockOf_mem hb, hms := hms,
                     hmember := memberAt_of S hrow (blockOf_mem hb) hms hm hf hl }
            else none
          else none
        | _ => none
      | _ => none
    | none => none
  | _ => none

theorem indKeyAt_of (S : RowStore t) {a : _root_.Address} (r : IndRow S a) {k : Key .anon}
    (hk : k = keyOf t a) : IndKeyAt t S.store k r.p.block r.p.idx.toNat r.ind := by
  unfold IndKeyAt
  exact ⟨a, r.c, r.p, r.cb, r.ms, hk, S.holds (a, r.c) r.hrow, r.hinfo, rfl, rfl, r.hmember⟩

/-- The oracle for the expressions of a member of the block at `B`. -/
def blockOracle (S : RowStore t) {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hB : (B, cb) ∈ S.rows) (hms : cb.info = .muts ms) :
    Oracle (⟨readCtx t S.blob, cb, cb.univs.map (convUniv id), blockSelf t B ms⟩ : ECx .anon) :=
  oracleOf S.checked S.blob cb id (blockSelf t B ms) (blockKey S.rows t B ms)
    (blockKey_ok S hB hms)

/-- The oracle for the expressions of a standalone record at `a`, with `recur 0` the record
itself. -/
def soloOracle (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (param : Nat → LevelParam) :
    Oracle (⟨readCtx t S.blob, c, c.univs.map (convUniv param), soloSelf t a⟩ : ECx .anon) :=
  oracleOf S.checked S.blob c param (soloSelf t a) (soloKey t a) (soloKey_ok t a)

/-- The oracle for the expressions of a record with no `recur`. -/
def plainOracle (S : RowStore t) (c : Ixon.Constant) :
    Oracle (⟨readCtx t S.blob, c, c.univs.map (convUniv id), fun _ => none⟩ : ECx .anon) :=
  oracleOf S.checked S.blob c id (fun _ => none) (fun _ => none)
    (fun _ _ h => by
      have h' : (none : Option (Key .anon)) = some _ := h
      cases h')

theorem reads_ind (S : RowStore t) {a : _root_.Address} (r : IndRow S a) {ty : CExpr .anon}
    (hty : (MemberReader.mk' (readCtx t S.blob) r.cb id (blockSelf t r.p.block r.ms)).read
      r.ind.typ = .ok ty) :
    ReadsIn t S.store S.blob a
      (.indInfo ⟨keyOf t a, List.range r.ind.lvls.toNat, ty⟩ ({} : IndCaps .anon)) :=
  readsIn_intro S r.hrow r.hinfo
    (Exists.intro r.cb (Exists.intro r.ms (Exists.intro r.ind (And.intro r.hmember
      (Exists.intro ty (Exists.intro ({} : IndCaps .anon) (And.intro hty rfl)))))))

/-- **What an inductive type's projection row declares.** -/
def readInd (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Option (Reading S a) :=
  match indRow? S a c hrow with
  | none => none
  | some r =>
    match sharesCheck (blockOracle S r.hB r.hms) r.cb.sharing.toList with
    | none => none
    | some sh =>
      match readCheck (blockOracle S r.hB r.hms) sh r.ind.typ with
      | none => none
      | some ty => some ⟨_, reads_ind S r ty.2⟩

theorem reads_ctor (S : RowStore t) {a : _root_.Address} {c : Ixon.Constant}
    {p : Ixon.ConstructorProj} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} {ct : Ixon.Constructor} {ty : CExpr .anon}
    (hrow : (a, c) ∈ S.rows) (hinfo : c.info = .cPrj p) (hB : (p.block, cb) ∈ S.rows)
    (hms : cb.info = .muts ms) (hm : ms[p.idx.toNat]? = some (.indc ind))
    (hct : ind.ctors[p.cidx.toNat]? = some ct) (hcx : ct.cidx.toNat = p.cidx.toNat)
    (hfound : (findProjOf S.rows
      (constructorProjection p.block p.idx.toNat p.cidx.toNat)).map (·.1) = some a)
    (hlogic : ms.toList.all inLogicMutB = true)
    (hty : (MemberReader.mk' (readCtx t S.blob) cb id (blockSelf t p.block ms)).read ct.typ =
      .ok ty) :
    ReadsIn t S.store S.blob a
      (.ctorInfo ⟨keyOf t a, List.range ct.lvls.toNat, ty⟩ ct.params.toNat ct.fields.toNat) := by
  have hj : p.cidx.toNat < ind.ctors.size := by
    rcases Nat.lt_or_ge p.cidx.toNat ind.ctors.size with hl | hge
    · exact hl
    · rw [Array.getElem?_eq_none hge] at hct
      cases hct
  obtain ⟨hc, ha⟩ :=
    row_is_proj S hrow (mem_expected hB hms hm _ (ctor_in_projs hj)) hfound
  exact readsIn_intro S hrow hinfo
    (Exists.intro cb (Exists.intro ms (Exists.intro ind (Exists.intro ct
      (And.intro (S.holds (p.block, cb) hB) (And.intro hms (And.intro hm (And.intro hct
        (And.intro hcx (And.intro hc (And.intro ha (And.intro (inLogic_muts hms hlogic)
          (Exists.intro ty (And.intro hty rfl))))))))))))))

/-- **What a constructor's projection row declares.** -/
def readCtor (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Option (Reading S a) :=
  match hinfo : c.info with
  | .cPrj p =>
    match hb : blockOf S.rows p.block with
    | some eb =>
      match hms : eb.2.info with
      | .muts ms =>
        match hm : ms[p.idx.toNat]? with
        | some (.indc ind) =>
          match hct : ind.ctors[p.cidx.toNat]? with
          | some ct =>
            if hcx : ct.cidx.toNat = p.cidx.toNat then
              if hf : (findProjOf S.rows
                  (constructorProjection p.block p.idx.toNat p.cidx.toNat)).map (·.1) =
                    some a then
                if hl : ms.toList.all inLogicMutB = true then
                  match sharesCheck (blockOracle S (blockOf_mem hb) hms) eb.2.sharing.toList with
                  | none => none
                  | some sh =>
                    match readCheck (blockOracle S (blockOf_mem hb) hms) sh ct.typ with
                    | none => none
                    | some ty =>
                      some ⟨_, reads_ctor S hrow hinfo (blockOf_mem hb) hms hm hct hcx hf hl
                        ty.2⟩
                else none
              else none
            else none
          | none => none
        | _ => none
      | _ => none
    | none => none
  | _ => none

/-- **What an axiom record declares.** -/
def readAxio (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Option (Reading S a) :=
  match hinfo : c.info with
  | .axio ax =>
    if hu : ax.isUnsafe = false then
      if hk : inertKey (keyOf t a) = false then
        match sharesCheck (plainOracle S c) c.sharing.toList with
        | none => none
        | some sh =>
          match readCheck (plainOracle S c) sh ax.typ with
          | none => none
          | some ty =>
            some ⟨.axiomInfo ⟨keyOf t a, List.range ax.lvls.toNat, ty.1⟩,
              readsIn_intro S hrow hinfo (And.intro (inLogic_axio hinfo hu)
                (And.intro hk (Exists.intro ty.1 (And.intro ty.2 rfl))))⟩
      else none
    else none
  | _ => none

/-- **What a quotient record declares**: the kernel's pinned quotient constant of its kind,
when the record's reading matches that pin. -/
def readQuot (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Option (Reading S a) :=
  match hinfo : c.info with
  | .quot q =>
    match sharesCheck (plainOracle S c) c.sharing.toList with
    | none => none
    | some sh =>
      match readCheck (plainOracle S c) sh q.typ with
      | none => none
      | some ty =>
        if hq : Ix.Kernel.quotPinHit (quotSlot q.kind)
            (⟨keyOf t a, List.range q.lvls.toNat, ty.1⟩ : ConstantVal .anon) = true then
          match hs : (BasisKind.quotK.declsA : List (ConstantInfo .anon))[
              (quotSlot q.kind).slot]? with
          | some ci₀ =>
            some ⟨ci₀, readsIn_intro S hrow hinfo
              (Exists.intro ty.1 (And.intro ty.2 (And.intro hq hs)))⟩
          | none => none
        else none
  | _ => none

/-! ### Recursors -/

/-- The inductive type's projection row whose key is `k`. -/
def findIndByKey (S : RowStore t) (k : Key .anon) :
    Option (Σ a : _root_.Address, { _r : IndRow S a // k = keyOf t a }) :=
  S.rows.attach.findSome? fun x =>
    if hk : k = keyOf t x.1.1 then
      match indRow? S x.1.1 x.1.2 x.2 with
      | some r => some ⟨x.1.1, r, hk⟩
      | none => none
    else none

theorem rule_reads (S : RowStore t) {aM : _root_.Address} (rM : IndRow S aM)
    {mr : MemberReader .anon} {ru : Ixon.RecursorRule × Nat} {e' : Row} {rhs : CExpr .anon}
    (hj : ru.2 < rM.ind.ctors.size)
    (hf : findProjOf S.rows (constructorProjection rM.p.block rM.p.idx.toNat ru.2) = some e')
    (hrhs : mr.read ru.1.rhs = .ok rhs) :
    RuleReads t mr rM.p.block rM.p.idx.toNat ru
      (RecRule.mk (keyOf t e'.1) ru.1.fields.toNat 0 .inert rhs false false false) := by
  have hm : rM.ms[rM.p.idx.toNat]? = some (.indc rM.ind) := rM.hmember.2.2.1
  obtain ⟨-, -, h4⟩ :=
    found_spec S (mem_expected rM.hB rM.hms hm _ (ctor_in_projs hj)) hf
  unfold RuleReads
  exact ⟨rhs, hrhs,
    congrArg (fun x => RecRule.mk (keyOf t x) ru.1.fields.toNat 0 .inert rhs false false false) h4⟩

/-- The rules of a recursor, one for each constructor in order, with the proof. -/
def readRules (S : RowStore t) {cx : Ctx .anon} {src : Ixon.Constant}
    {param : Nat → LevelParam} {self : Nat → Option (ReadM (CName .anon))}
    (o : Oracle (⟨cx, src, src.univs.map (convUniv param), self⟩ : ECx .anon))
    (sh : { ws : Array (CExpr .anon) //
      ShareOk ⟨cx, src, src.univs.map (convUniv param), self⟩ src.sharing.toList ws })
    {aM : _root_.Address} (rM : IndRow S aM) :
    (rs : List (Ixon.RecursorRule × Nat)) →
      Option { rules : List (RecRule .anon) //
        List.Forall₂ (RuleReads t (MemberReader.mk' cx src param self) rM.p.block
          rM.p.idx.toNat) rs rules }
  | [] => some ⟨[], .nil⟩
  | ru :: rs =>
    if hj : ru.2 < rM.ind.ctors.size then
      match hf : findProjOf S.rows
          (constructorProjection rM.p.block rM.p.idx.toNat ru.2) with
      | none => none
      | some _ =>
        match readCheck o sh ru.1.rhs, readRules S o sh rM rs with
        | some rhs, some rest => some ⟨_ :: rest.1, .cons (rule_reads S rM hj hf rhs.2) rest.2⟩
        | _, _ => none
    else none

theorem reads_rec (S : RowStore t) {a : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} {tyP ty : CExpr .anon} {kF kM : Key .anon} {B Bm : _root_.Address}
    {i im : Nat} {ind indM : Ixon.Inductive} {rules : List (RecRule .anon)}
    (hrow : (a, c) ∈ S.rows) (hinfo : c.info = .recr rc) (hu : rc.isUnsafe = false)
    (htyP : (exprReader t S.blob c id (soloSelf t a)).read rc.typ = .ok tyP)
    (hF : familyKey rc tyP = some kF) (hIndF : IndKeyAt t S.store kF B i ind)
    (hM : majorKey rc tyP = some kM) (hIndM : IndKeyAt t S.store kM Bm im indM)
    (hty : (exprReader t S.blob c
      (recParam (recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
        (List.range ind.lvls.toNat))) (soloSelf t a)).read rc.typ = .ok ty)
    (hsz : rc.rules.size = indM.ctors.size)
    (hrules : List.Forall₂ (RuleReads t (exprReader t S.blob c
      (recParam (recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
        (List.range ind.lvls.toNat))) (soloSelf t a)) Bm im) rc.rules.toList.zipIdx rules) :
    ReadsIn t S.store S.blob a
      (.recInfo ⟨keyOf t a, recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
          (List.range ind.lvls.toNat), ty⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules) := by
  have hrec : RecReads t S.store S.blob c (soloSelf t a) (keyOf t a) rc
      (.recInfo ⟨keyOf t a, recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
          (List.range ind.lvls.toNat), ty⟩
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat)
        (rc.params.toNat + rc.motives.toNat + rc.minors.toNat) rules) := by
    unfold RecReads
    exact ⟨tyP, ty, kF, kM, B, Bm, i, im, ind, indM, _, rules, htyP, hF, hIndF, hM, hIndM, rfl,
      hty, hsz, hrules, rfl⟩
  exact readsIn_intro S hrow hinfo (And.intro (inLogic_recr hinfo hu) hrec)

/-- **What a standalone recursor record declares.** -/
def readRec (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Option (Reading S a) :=
  match hinfo : c.info with
  | .recr rc =>
    if hu : rc.isUnsafe = false then
      match sharesCheck (soloOracle S a c id) c.sharing.toList with
      | none => none
      | some shI =>
        match readCheck (soloOracle S a c id) shI rc.typ with
        | none => none
        | some tyP =>
          match hF : familyKey rc tyP.1 with
          | none => none
          | some kF =>
            match findIndByKey S kF with
            | none => none
            | some ⟨_, rF, hkF⟩ =>
              match hM : majorKey rc tyP.1 with
              | none => none
              | some kM =>
                match findIndByKey S kM with
                | none => none
                | some ⟨_, rM, hkM⟩ =>
                  match sharesCheck (soloOracle S a c
                      (recParam (recLps (decide (rc.lvls.toNat = rF.ind.lvls.toNat + 1))
                        (List.range rF.ind.lvls.toNat)))) c.sharing.toList with
                  | none => none
                  | some shP =>
                    match readCheck (soloOracle S a c
                        (recParam (recLps (decide (rc.lvls.toNat = rF.ind.lvls.toNat + 1))
                          (List.range rF.ind.lvls.toNat)))) shP rc.typ with
                    | none => none
                    | some ty =>
                      if hsz : rc.rules.size = rM.ind.ctors.size then
                        match readRules S (soloOracle S a c
                            (recParam (recLps (decide (rc.lvls.toNat = rF.ind.lvls.toNat + 1))
                              (List.range rF.ind.lvls.toNat)))) shP rM rc.rules.toList.zipIdx with
                        | none => none
                        | some rules =>
                          some ⟨_, reads_rec S hrow hinfo hu tyP.2 hF (indKeyAt_of S rF hkF) hM
                            (indKeyAt_of S rM hkM) ty.2 hsz rules.2⟩
                      else none
    else none
  | _ => none

/-! ## A row, and a whole store -/

/-- **What the record at a row declares**, by its kind, with the proof. -/
def readRow (S : RowStore t) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Option (Reading S a) :=
  match readInd S a c hrow with
  | some r => some r
  | none =>
    match readCtor S a c hrow with
    | some r => some r
    | none =>
      match readRec S a c hrow with
      | some r => some r
      | none =>
        match readQuot S a c hrow with
        | some r => some r
        | none => readAxio S a c hrow

/-- The row has a reading that the constant the environment holds at its key stores. -/
def rowOk (S : RowStore t) (env : Env .anon) (a : _root_.Address) (c : Ixon.Constant)
    (hrow : (a, c) ∈ S.rows) : Bool :=
  match readRow S a c hrow with
  | none => false
  | some r =>
    match env.find? (keyOf t a) with
    | none => false
    | some ci => (storedAsCheck 256 ci r.1).isSome

theorem rowOk_spec (S : RowStore t) (env : Env .anon) {a : _root_.Address}
    {c : Ixon.Constant} {hrow : (a, c) ∈ S.rows} (h : rowOk S env a c hrow = true) :
    ∃ ci ci₀, env.find? (keyOf t a) = some ci ∧ ReadsIn t S.store S.blob a ci₀ ∧
      StoredAs ci ci₀ := by
  unfold rowOk at h
  cases hr : readRow S a c hrow with
  | none =>
    rw [hr] at h
    have h' : false = true := h
    cases h'
  | some r =>
    cases hp : env.find? (keyOf t a) with
    | none =>
      rw [hr, hp] at h
      have h' : false = true := h
      cases h'
    | some ci =>
      rw [hr, hp] at h
      have h1 : (storedAsCheck 256 ci r.1).isSome = true := h
      exact ⟨ci, r.1, rfl, r.2, storedAs_of_check h1⟩

/-- A row that passes `rowOk` reads as the constant `readRow` computes, and the constant the
environment holds at its key stores that constant. -/
theorem rowOk_reading (S : RowStore t) (env : Env .anon) {a : _root_.Address}
    {c : Ixon.Constant} {hrow : (a, c) ∈ S.rows} (h : rowOk S env a c hrow = true) :
    ∃ r : Reading S a, readRow S a c hrow = some r ∧
      ∃ ci, env.find? (keyOf t a) = some ci ∧ StoredAs ci r.1 := by
  unfold rowOk at h
  cases hr : readRow S a c hrow with
  | none =>
    rw [hr] at h
    have h' : false = true := h
    cases h'
  | some r =>
    cases hp : env.find? (keyOf t a) with
    | none =>
      rw [hr, hp] at h
      have h' : false = true := h
      cases h'
    | some ci =>
      rw [hr, hp] at h
      have h1 : (storedAsCheck 256 ci r.1).isSome = true := h
      exact ⟨r, rfl, ci, rfl, storedAs_of_check h1⟩

/-- **Every address of the store with a reading has a reading the environment stores**, if
every row that is not a block passes `rowOk`. -/
theorem reads_stored (S : RowStore t) (env : Env .anon)
    (hall : S.rows.attach.all
      (fun x => isMutsInfo x.1.2.info || rowOk S env x.1.1 x.1.2 x.2) = true) :
    ∀ a, (∃ ci₀, ReadsIn t S.store S.blob a ci₀) →
      ∃ ci ci₀, env.find? (keyOf t a) = some ci ∧ ReadsIn t S.store S.blob a ci₀ ∧
        StoredAs ci ci₀ := by
  intro a hr
  obtain ⟨_, c, hc, hread⟩ := hr
  have hmem : (a, c) ∈ S.rows := S.only a c hc
  have hF : (isMutsInfo c.info || rowOk S env a c hmem) = true :=
    List.all_eq_true.mp hall ⟨(a, c), hmem⟩ (List.mem_attach _ _)
  have hok : rowOk S env a c hmem = true := by
    generalize c.info = info at hread hF
    cases info <;> first
      | exact False.elim hread
      | exact hF
  exact rowOk_spec S env hok

end IxVM.Refinement.RowReader
