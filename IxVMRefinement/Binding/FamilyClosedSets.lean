import IxVMRefinement.Binding.FamilyCallPremises
import IxVMRefinement.Binding.ReadsLiteralFree
import IxVMRefinement.TwinFamily.ProducerRow
import IxVMRefinement.FamilyGraph.ProducersStoredFam

/-! # Two closure facts: the basis rows' level parameters, and a closed set below a family record

* **`unitLevelsAt_basis`**: `FamilyCallPremises.UnitLevelsAt` at every row of the basis store, the
  hypothesis `hbasis` of `FamilyCallPremises.unitLevelsAt_of_storedBelow`,
  `levelsDefinedAt_of_held` and `loadedLevelsDefined_of_held`, with no hypothesis beyond
  `BasisRowsLoaded`. The reader takes every level of a reading from the record's universe table
  (`read_levelsDefined`), and the universe table of each of the 24 rows stays within the level
  count of each of its constants (`basisRows_levelsBelow`, decided over the rows).
* **`graphStoreClosed_of_coveredStore`**: `TwinFamily.GraphStoreClosed` from the one premise
  `CoveredStoreApart`. The set is the addresses held by `belowStore`: the records the walk reached
  at rank at most the block's, with their blocks' projection records (`WalkBelow`), together with
  a store `Rc` for the covered references. That store is closed under what its records use
  (`belowStore_usedClosed`, from `TopGraph.closed`, `owner`, `members`), so its addresses are
  closed under what the run's store answers (`closedOn_of_usedClosed_sub`); it holds the block;
  and a recursor projection record of the family record is not of the walk below the block's rank
  (`not_walkBelow_member`, from `FamilyGraph.famAfter`).

* **`coveredStoreApart_of_witness`**, **`graphStoreClosed_of_witnessApart`**: `CoveredStoreApart`,
  and so `TwinFamily.GraphStoreClosed`, from `WitnessStoreApart`. The store for the covered
  references is the step's records at the addresses the witness's store or the basis store holds
  (`heldStore`, `heldStore_usedClosed`); a covered address is one of those (`covered_held`); and
  no basis row is a recursor projection record of a family record (`basisRows_noRecBlock`,
  decided over the rows).

Remaining hypothesis: `CoveredStoreApart`, a used-closed store of records of the step's store
that holds the covered references of the walk below the block and no recursor projection record
of the block's family record; or, stronger, `WitnessStoreApart`, that the witness's store holds
no recursor projection record of a family record of the graph. -/

namespace IxVM.Refinement.Binding.FamilyClosedSets

open Ix.Kernel Ix.Kernel.Reader
open IxVM.Consistency
open IxVM.Refinement.StoreInhabit (basisStore basisRows)
open IxVM.Refinement.Binding.FamilyCallPremises (UnitLevelsAt)
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (throw_ok)

/-! ## Universe tables within a level count -/

/-- **Every variable of the universe is below `n`.** -/
def univBelow (n : Nat) : Ixon.Univ → Bool
  | .zero => true
  | .succ u => univBelow n u
  | .max a b => univBelow n a && univBelow n b
  | .imax a b => univBelow n a && univBelow n b
  | .var i => decide (i.toNat < n)

/-- **Every variable of the record's universe table is below `n`.** -/
def univsBelow (n : Nat) (c : Ixon.Constant) : Bool :=
  c.univs.toList.all (univBelow n)

/-- **The universe table of the record stays within the level count of each constant whose
reading `UnitLevelsAt` speaks of**: a standalone definition's, and of a block every definition
member's and every inductive member's. -/
def recordLevelsBelow (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d => univsBelow d.lvls.toNat c
  | .muts ms => ms.toList.all fun
    | .defn d => univsBelow d.lvls.toNat c
    | .indc ind => univsBelow ind.lvls.toNat c
    | .recr _ => true
  | _ => true

theorem convUniv_below {n : Nat} :
    ∀ (u : Ixon.Univ), univBelow n u = true →
      (convUniv id u).allParamsDefined (List.range n) = true
  | .zero, _ => rfl
  | .succ u, h => by
    simp only [univBelow] at h
    simpa only [convUniv, Level.allParamsDefined] using convUniv_below u h
  | .max a b, h => by
    simp only [univBelow, Bool.and_eq_true] at h
    simp only [convUniv, Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_below a h.1, convUniv_below b h.2⟩
  | .imax a b, h => by
    simp only [univBelow, Bool.and_eq_true] at h
    simp only [convUniv, Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨convUniv_below a h.1, convUniv_below b h.2⟩
  | .var i, h => by
    simp only [univBelow, decide_eq_true_eq] at h
    simpa [convUniv, Level.allParamsDefined] using h

section Conv

variable {e : ECx .anon} {ps : List LevelParam}

private theorem level_defined (hu : ∀ l ∈ e.univs.toList, l.allParamsDefined ps = true)
    {i : UInt64} {l : CLevel} (h : e.level i = .ok l) : l.allParamsDefined ps = true := by
  unfold ECx.level at h
  cases hi : e.univs[i.toNat]? with
  | none =>
    simp only [hi] at h
    exact (throw_ok h).elim
  | some l' =>
    simp only [hi] at h
    cases h
    exact hu _ (Array.mem_def.mp (Array.mem_of_getElem? hi))

private theorem levels_defined (hu : ∀ l ∈ e.univs.toList, l.allParamsDefined ps = true) :
    ∀ (us : List UInt64) (ls : List CLevel), us.mapM e.level = .ok ls →
      ls.all (Level.allParamsDefined ps) = true
  | [], ls, h => by
    cases h
    rfl
  | u :: us, ls, h => by
    rw [List.mapM_cons] at h
    obtain ⟨l, hl, h⟩ := except_bind_ok.mp h
    obtain ⟨ls', hls', h⟩ := except_bind_ok.mp h
    cases h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨level_defined hu hl, levels_defined hu us ls' hls'⟩

/-- **A conversion against a universe table within `ps`, and sharing entries within `ps`, is
within `ps`.** -/
theorem convExpr_levelsDefined (hu : ∀ l ∈ e.univs.toList, l.allParamsDefined ps = true)
    {tbl : Array (ReadM (CExpr .anon))}
    (htbl : ∀ (i : Nat) (v : CExpr .anon), tbl[i]? = some (Except.ok v) →
      v.allLevelParamsDefined ps = true) :
    ∀ (x : Ixon.Expr) (v : CExpr .anon), convExpr e tbl x = .ok v →
      v.allLevelParamsDefined ps = true := by
  intro x
  induction x with
  | sort i =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨l, hl, h⟩ := except_bind_ok.mp h
    cases h
    exact level_defined hu hl
  | var i =>
    intro v h
    simp only [convExpr] at h
    cases h
    rw [Expr.mkBvar_eq]
    rfl
  | ref i us =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨ls, hls, h⟩ := except_bind_ok.mp h
    cases h
    exact levels_defined hu _ _ hls
  | recur i us =>
    intro v h
    cases hs : e.self i.toNat with
    | none =>
      simp only [convExpr, hs] at h
      exact (throw_ok h).elim
    | some m =>
      simp only [convExpr, hs] at h
      obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
      obtain ⟨ls, hls, h⟩ := except_bind_ok.mp h
      cases h
      exact levels_defined hu _ _ hls
  | prj i field val ih =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨k, hk, h⟩ := except_bind_ok.mp h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    cases h
    exact ih x hx
  | str i =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok.mp h
    cases hs : String.fromUTF8? b with
    | none =>
      simp only [hs] at h
      exact (throw_ok h).elim
    | some s =>
      simp only [hs] at h
      cases h
      rfl
  | nat i =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨n, hn, h⟩ := except_bind_ok.mp h
    cases h
    rfl
  | app f a ihf iha =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    cases h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨ihf x hx, iha y hy⟩
  | lam ty b iht ihb =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    cases h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht x hx, ihb y hy⟩, rfl⟩
  | all ty b iht ihb =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    cases h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht x hx, ihb y hy⟩, rfl⟩
  | letE nonDep mode ty val b iht ihv ihb =>
    intro v h
    simp only [convExpr] at h
    obtain ⟨x, hx, h⟩ := except_bind_ok.mp h
    obtain ⟨y, hy, h⟩ := except_bind_ok.mp h
    obtain ⟨z, hz, h⟩ := except_bind_ok.mp h
    cases h
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true]
    exact ⟨⟨iht x hx, ihv y hy⟩, ihb z hz⟩
  | share i =>
    intro v h
    cases ht : tbl[i.toNat]? with
    | none =>
      simp only [convExpr, ht] at h
      exact (throw_ok h).elim
    | some r =>
      simp only [convExpr, ht] at h
      subst h
      exact htbl _ _ ht

/-- The sharing table against a universe table within `ps`, entry by entry. -/
theorem buildShareTblGo_levelsDefined
    (hu : ∀ l ∈ e.univs.toList, l.allParamsDefined ps = true) :
    ∀ (es : List Ixon.Expr) (acc : Array (ReadM (CExpr .anon))),
      (∀ (i : Nat) (v : CExpr .anon), acc[i]? = some (Except.ok v) →
        v.allLevelParamsDefined ps = true) →
      ∀ (i : Nat) (v : CExpr .anon), (L1.buildShareTblGo e acc es)[i]? = some (Except.ok v) →
        v.allLevelParamsDefined ps = true := by
  intro es
  induction es with
  | nil =>
    intro acc hacc
    exact hacc
  | cons x es ih =>
    intro acc hacc
    simp only [L1.buildShareTblGo]
    apply ih
    intro i v hi
    rw [Array.getElem?_push] at hi
    by_cases hsize : i = acc.size
    · rw [ite_eq_left hsize] at hi
      exact convExpr_levelsDefined hu hacc x v (Option.some.inj hi)
    · rw [ite_eq_right hsize] at hi
      exact hacc i v hi

end Conv

/-- **A reading against a universe table within `n` level parameters mentions only those.** -/
theorem read_levelsDefined {cx : Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (ReadM (CName .anon))} {n : Nat} (hu : univsBelow n src = true)
    {x : Ixon.Expr} {v : CExpr .anon} (h : (MemberReader.mk' cx src id self).read x = .ok v) :
    v.allLevelParamsDefined (List.range n) = true := by
  obtain ⟨hecx, htbl⟩ := L1.memberReader_mk'_eq cx src id self
  unfold MemberReader.read at h
  rw [hecx, htbl] at h
  have hu' : ∀ l ∈ (⟨cx, src, src.univs.map (convUniv id), self⟩ : ECx .anon).univs.toList,
      l.allParamsDefined (List.range n) = true := by
    intro l hl
    simp only [Array.toList_map, List.mem_map] at hl
    obtain ⟨u, hu₁, rfl⟩ := hl
    exact convUniv_below u (List.all_eq_true.mp hu u hu₁)
  exact convExpr_levelsDefined hu'
    (buildShareTblGo_levelsDefined hu' src.sharing.toList #[] (fun i v hi => by simp at hi)) x v h

/-! ## The basis rows -/

set_option maxRecDepth 100000 in
/-- **The universe table of each of the 24 committed basis rows stays within the level counts of
its constants** (decided over the rows). -/
theorem basisRows_levelsBelow : basisRows.all (fun e => recordLevelsBelow e.2) = true := by
  decide +kernel

/-- A record of the run's store at an address the basis store holds is the basis store's. -/
theorem basis_record {E₀ : Ixon.Env} (hb : BasisRowsLoaded E₀) {A : _root_.Address}
    (hA : (basisStore.consts.get? A).isSome = true) {c : Ixon.Constant}
    (hc : recordOf E₀ A = some c) : recordOf basisStore A = some c := by
  obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hA
  unfold recordOf at hc ⊢
  rw [hb A lc hlc] at hc
  rw [hlc]
  exact hc

/-- **The readings of every basis row mention only their constants' level parameters**
(`FamilyCallPremises.UnitLevelsAt` at every address the basis store holds, for a store holding the
basis rows): the hypothesis `hbasis` of `FamilyCallPremises.unitLevelsAt_of_storedBelow`,
`levelsDefinedAt_of_held` and `loadedLevelsDefined_of_held`. The reader takes every level of a
reading from the record's universe table, and each basis row's table stays within the level count
of each of its constants (`basisRows_levelsBelow`); the role table and the blobs play no part. -/
theorem unitLevelsAt_basis {t : RoleTable} {E₀ : Ixon.Env} (hb : BasisRowsLoaded E₀) :
    ∀ A, (basisStore.consts.get? A).isSome = true → UnitLevelsAt t E₀ A := by
  intro A hA
  have hrow : ∀ c, recordOf E₀ A = some c → recordLevelsBelow c = true := fun c hc =>
    List.all_eq_true.mp basisRows_levelsBelow (A, c)
      (StoreInhabit.store_record_inv (basis_record hb hA hc))
  refine ⟨?_, ?_, ?_⟩
  · intro c d v hrec hinfo _ hread
    have h := hrow c hrec
    simp only [recordLevelsBelow, hinfo] at h
    exact read_levelsDefined h hread
  · intro cb ms k d v hrec hms hm _ hread
    have h := hrow cb hrec
    simp only [recordLevelsBelow, hms] at h
    have h' := List.all_eq_true.mp h _ (Array.mem_def.mp (Array.mem_of_getElem? hm))
    exact read_levelsDefined h' hread
  · intro cb ms k ind v hrec hms hm hread
    have h := hrow cb hrec
    simp only [recordLevelsBelow, hms] at h
    have h' := List.all_eq_true.mp h _ (Array.mem_def.mp (Array.mem_of_getElem? hm))
    exact read_levelsDefined h' hread

end IxVM.Refinement.Binding.FamilyClosedSets

/-! ## Closed sets from a used-closed sub-store of a store over the run's -/

namespace IxVM.Refinement.Binding.FamilyClosedSets

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding.FamilyFlat (FlatView Held)
open IxVM.Refinement.Binding.FamilyRecon (ReconView)

set_option linter.unusedVariables false

/-- **A set closed under what a larger store answers is closed under what the run's store
answers** (reconstruction view): the larger store answers whatever the run's does
(`FamilyRecon.reconOfStore_le`), and both name addresses by keys alike. -/
theorem reconClosedOn_of_le {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {S : _root_.Address → Prop}
    (hle : ∀ y c, recordOf E₀ y = some c → recordOf E y = some c)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → E.blobs.get? y = some b)
    (h : (ReconView.ofStore t E).ClosedOn S) : (ReconView.ofStore t E₀).ClosedOn S where
  indBlk a i ha hi :=
    h.indBlk a i ha ((FamilyRecon.reconOfStore_le hle hblob).ind a _ trivial hi)
  indTy a i ha hi :=
    h.indTy a i ha ((FamilyRecon.reconOfStore_le hle hblob).ind a _ trivial hi)
  ctorTy b i c ty np hb hc :=
    h.ctorTy b i c ty np hb ((FamilyRecon.reconOfStore_le hle hblob).ctor b i c _ trivial hc)
  unfold k us v hk hu :=
    h.unfold k us v hk
      ((FamilyRecon.reconOfStore_le hle hblob).unfold k us _ (fun _ _ => trivial) hu)

/-- **A set closed under what a larger store answers is closed under what the run's store
answers** (flattening view, `FamilyFlat.ofStore_le`). -/
theorem flatClosedOn_of_le {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {S : _root_.Address → Prop}
    (hle : ∀ y c, recordOf E₀ y = some c → recordOf E y = some c)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → E.blobs.get? y = some b)
    (h : (FlatView.ofStore t E).ClosedOn S) : (FlatView.ofStore t E₀).ClosedOn S where
  ciBlk a i ha hi := h.ciBlk a i ha ((FamilyFlat.ofStore_le hle hblob).ci a _ hi)
  members b ms hb hm := h.members b ms hb ((FamilyFlat.ofStore_le hle hblob).members b _ hm)
  ctorType b i c ty hb hc :=
    h.ctorType b i c ty hb ((FamilyFlat.ofStore_le hle hblob).ctorType b i c _ hc)

/-- **The addresses a used-closed sub-store of a store over the run's holds are closed under what
the run's store answers**, in both views (`FamilyRecon.reconOfStore_closedOn_sub`,
`FamilyFlat.ofStore_closedOn_sub` at the larger store, then `reconClosedOn_of_le`,
`flatClosedOn_of_le`). -/
theorem closedOn_of_usedClosed_sub {t : Ix.Kernel.RoleTable} {E₀ E R' : Ixon.Env}
    (checked : t.check = .ok ())
    (hle : ∀ y c, recordOf E₀ y = some c → recordOf E y = some c)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → E.blobs.get? y = some b)
    (hsub : ∀ y c, recordOf R' y = some c → recordOf E y = some c) (hcl : UsedClosed R') :
    (ReconView.ofStore t E₀).ClosedOn (Held R') ∧ (FlatView.ofStore t E₀).ClosedOn (Held R') := by
  have hwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [checked]
    rfl
  exact ⟨reconClosedOn_of_le hle hblob
      (FamilyRecon.reconOfStore_closedOn_sub checked hwf hsub hcl),
    flatClosedOn_of_le hle hblob (FamilyFlat.ofStore_closedOn_sub checked hwf hsub hcl)⟩

/-! ## The walk below a rank -/

/-- **An address the walk reached at rank at most `n`, or a constant address of a record it
reached there** (a member's or a constructor's projection record of a block). -/
def WalkBelow (E₀ : Ixon.Env) (Top : _root_.Address → Prop) (rank : _root_.Address → Nat)
    (n : Nat) (x : _root_.Address) : Prop :=
  ∃ a, Top a ∧ rank a ≤ n ∧ (x = a ∨ ∃ c, recordOf E₀ a = some c ∧ ConstAddrOf a c x)

/-- **The records of `E` the walk reached below a rank, with those of a store `Rc`**: at the
addresses of `WalkBelow` and at the addresses `Rc` holds. -/
noncomputable def belowStore (E₀ E Rc : Ixon.Env) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat) (n : Nat) : Ixon.Env :=
  recordsAt E fun x => WalkBelow E₀ Top rank n x ∨ Held Rc x

theorem belowStore_recordOf {E₀ E Rc : Ixon.Env} {Top : _root_.Address → Prop}
    {rank : _root_.Address → Nat} {n : Nat} {a : _root_.Address} {c : Ixon.Constant} :
    recordOf (belowStore E₀ E Rc Top rank n) a = some c ↔
      (WalkBelow E₀ Top rank n a ∨ Held Rc a) ∧ recordOf E a = some c :=
  recordOf_restrict (fun _ => recordsAt_consts) c

private theorem ownerOf_of_not_proj {a : _root_.Address} {c : Ixon.Constant} (h : ¬ IsProj c) :
    Ix.Cert.ownerOf a c = a := by
  unfold Ix.Cert.ownerOf
  cases hi : c.info with
  | dPrj p => exact absurd (Or.inl ⟨p, hi⟩) h
  | iPrj p => exact absurd (Or.inr (Or.inl ⟨p, hi⟩)) h
  | cPrj p => exact absurd (Or.inr (Or.inr (Or.inl ⟨p, hi⟩))) h
  | rPrj p => exact absurd (Or.inr (Or.inr (Or.inr ⟨p, hi⟩))) h
  | defn _ => rfl
  | recr _ => rfl
  | axio _ => rfl
  | quot _ => rfl
  | muts _ => rfl

private theorem memberProjection_refs (B : _root_.Address) (i : Nat) (m : Ixon.MutConst) :
    (memberProjection B i m).refs = #[] := rfl

private theorem memberProjection_not_muts (B : _root_.Address) (i : Nat) (m : Ixon.MutConst)
    (ms : Array Ixon.MutConst) : (memberProjection B i m).info ≠ .muts ms := by
  cases m <;> (intro h; cases h)

section Walk

variable {t : Ix.Kernel.RoleTable} {E₀ E Rc : Ixon.Env} {seeds : List _root_.Address}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {n : Nat}

/-- An address of `WalkBelow` is one the walk reached at rank at most `n`, or holds a member's or
a constructor's projection record of a block the walk reached there. -/
theorem walkBelow_cases (hG : TopGraph t E₀ seeds Top rank) {x : _root_.Address}
    (hx : WalkBelow E₀ Top rank n x) :
    (Top x ∧ rank x ≤ n) ∨
      ∃ a P, Top a ∧ rank a ≤ n ∧ recordOf E₀ x = some P ∧
        ((∃ i m, P = memberProjection a i m) ∨ ∃ i j, P = constructorProjection a i j) := by
  obtain ⟨a, hTa, hle, rfl | ⟨c, hc, hcx⟩⟩ := hx
  · exact Or.inl ⟨hTa, hle⟩
  · rcases hcx with ⟨rfl, -⟩ | ⟨ms, i, m, hms, hm, rfl | ⟨ind, j, hind, hj, rfl⟩⟩
    · exact Or.inl ⟨hTa, hle⟩
    · exact Or.inr ⟨a, _, hTa, hle, (hG.members a c ms hTa hc hms i m hm).1, Or.inl ⟨i, m, rfl⟩⟩
    · exact Or.inr ⟨a, _, hTa, hle, (hG.members a c ms hTa hc hms i m hm).2 ind j hind hj,
        Or.inr ⟨i, j, rfl⟩⟩

/-- **The store below a rank is closed under what its records use**, when `Rc` is, its records
are records of `E`, and it holds every covered reference of a record the walk reached at rank at
most `n`: a reference such a record uses is reached at a smaller rank or covered
(`TopGraph.closed`), a projection record's block is reached at a smaller rank (`TopGraph.owner`),
and a reached block's projection records are its constant addresses (`TopGraph.members`). -/
theorem belowStore_usedClosed (hG : TopGraph t E₀ seeds Top rank)
    (hle : ∀ y c, recordOf E₀ y = some c → recordOf E y = some c)
    (hsub : ∀ y c, recordOf Rc y = some c → recordOf E y = some c) (hcl : UsedClosed Rc)
    (hcov : ∀ a x, Top a → rank a ≤ n → UsedRef E₀ a x → Covered t x → Held Rc x) :
    UsedClosed (belowStore E₀ E Rc Top rank n) := by
  have hheld : ∀ {y : _root_.Address} {c : Ixon.Constant}, recordOf Rc y = some c →
      recordOf (belowStore E₀ E Rc Top rank n) y = some c := fun {y c} h =>
    belowStore_recordOf.mpr ⟨Or.inr (by unfold Held; rw [h]; rfl), hsub y c h⟩
  have htop : ∀ {y : _root_.Address}, Top y → rank y ≤ n →
      (recordOf (belowStore E₀ E Rc Top rank n) y).isSome = true := by
    intro y hTy hy
    obtain ⟨c, hc⟩ := hG.record y hTy
    rw [belowStore_recordOf.mpr ⟨Or.inl ⟨y, hTy, hy, Or.inl rfl⟩, hle y c hc⟩]
    rfl
  constructor
  · intro a c hrec
    obtain ⟨hQ, hEc⟩ := belowStore_recordOf.mp hrec
    rcases hQ with hW | hR
    · rcases walkBelow_cases hG hW with ⟨hTa, hna⟩ | ⟨a', P, hTa', hna', hP, hshape⟩
      · obtain ⟨c₀, hc₀⟩ := hG.record a hTa
        have e : c₀ = c := Option.some.inj ((hle a c₀ hc₀).symm.trans hEc)
        subst e
        refine ⟨?_, ?_⟩
        · by_cases hp : IsProj c₀
          · obtain ⟨hTo, hro⟩ := hG.owner a c₀ hTa hc₀ hp
            exact htop hTo (by omega)
          · rw [ownerOf_of_not_proj hp, hrec]
            rfl
        · intro i hi x hx
          rcases hG.closed a x hTa ⟨c₀, i, hc₀, hi, hx⟩ with ⟨hTx, hrx⟩ | hcx
          · exact htop hTx (by omega)
          · obtain ⟨cx, hcx'⟩ := Option.isSome_iff_exists.mp
              (hcov a x hTa hna ⟨c₀, i, hc₀, hi, hx⟩ hcx)
            rw [hheld hcx']
            rfl
      · have e : P = c := Option.some.inj ((hle a P hP).symm.trans hEc)
        subst e
        refine ⟨?_, ?_⟩
        · rcases hshape with ⟨i, m, rfl⟩ | ⟨i, j, rfl⟩
          · rw [ownerOf_memberProjection]
            exact htop hTa' hna'
          · rw [ownerOf_constructorProjection]
            exact htop hTa' hna'
        · intro i hi x hx
          rcases hshape with ⟨i', m, rfl⟩ | ⟨i', j, rfl⟩
          · rw [memberProjection_refs] at hx
            simp at hx
          · simp [constructorProjection] at hx
    · obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hR
      have e : c' = c := Option.some.inj ((hsub a c' hc').symm.trans hEc)
      subst e
      obtain ⟨ho, hrefs⟩ := hcl.1 a c' hc'
      refine ⟨?_, ?_⟩
      · obtain ⟨co, hco⟩ := Option.isSome_iff_exists.mp ho
        rw [hheld hco]
        rfl
      · intro i hi x hx
        obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp (hrefs i hi x hx)
        rw [hheld hcx]
        rfl
  · intro B' c ms hrec hms i m hm
    obtain ⟨hQ, hEc⟩ := belowStore_recordOf.mp hrec
    rcases hQ with hW | hR
    · rcases walkBelow_cases hG hW with ⟨hTa, hna⟩ | ⟨a', P, hTa', hna', hP, hshape⟩
      · obtain ⟨c₀, hc₀⟩ := hG.record B' hTa
        have e : c₀ = c := Option.some.inj ((hle B' c₀ hc₀).symm.trans hEc)
        subst e
        obtain ⟨h1, h2⟩ := hG.members B' c₀ ms hTa hc₀ hms i m hm
        refine ⟨belowStore_recordOf.mpr ⟨Or.inl ⟨B', hTa, hna, Or.inr ⟨c₀, hc₀,
          Or.inr ⟨ms, i, m, hms, hm, Or.inl rfl⟩⟩⟩, hle _ _ h1⟩, ?_⟩
        intro ind hind j hj
        exact belowStore_recordOf.mpr ⟨Or.inl ⟨B', hTa, hna, Or.inr ⟨c₀, hc₀,
          Or.inr ⟨ms, i, m, hms, hm, Or.inr ⟨ind, j, hind, hj, rfl⟩⟩⟩⟩, hle _ _ (h2 ind j hind hj)⟩
      · have e : P = c := Option.some.inj ((hle B' P hP).symm.trans hEc)
        subst e
        rcases hshape with ⟨i', m', rfl⟩ | ⟨i', j, rfl⟩
        · exact absurd hms (memberProjection_not_muts _ _ _ _)
        · cases hms
    · obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hR
      have e : c' = c := Option.some.inj ((hsub B' c' hc').symm.trans hEc)
      subst e
      obtain ⟨h1, h2⟩ := hcl.2 B' c' ms hc' hms i m hm
      exact ⟨hheld h1, fun ind hind j hj => hheld (h2 ind hind j hj)⟩

/-- **A member's projection record of a block the walk reached, if at all, above rank `n` is no
address of `WalkBelow`**: reached itself, it comes after its block (`TopGraph.owner`); a constant
address of a reached record, it holds that record's projection, so the record is its block. -/
theorem not_walkBelow_member (hG : TopGraph t E₀ seeds Top rank) {rb y : _root_.Address}
    {j : Nat} {m : Ixon.MutConst} (hy : recordOf E₀ y = some (memberProjection rb j m))
    (hafter : Top rb → n < rank rb) : ¬ WalkBelow E₀ Top rank n y := by
  intro hW
  rcases walkBelow_cases hG hW with ⟨hTy, hny⟩ | ⟨a, P, hTa, hna, hP, hshape⟩
  · obtain ⟨hTo, hro⟩ := hG.owner y _ hTy hy (memberProjection_isProj rb j m)
    rw [ownerOf_memberProjection] at hTo hro
    have := hafter hTo
    omega
  · have e : memberProjection rb j m = P := Option.some.inj (hy.symm.trans hP)
    have hown : rb = a := by
      have h1 := congrArg (Ix.Cert.ownerOf y) e
      rw [ownerOf_memberProjection] at h1
      rcases hshape with ⟨i, m', rfl⟩ | ⟨i, j', rfl⟩
      · rw [ownerOf_memberProjection] at h1
        exact h1
      · rw [ownerOf_constructorProjection] at h1
        exact h1
    subst hown
    have := hafter hTa
    omega

end Walk

/-! ## `GraphStoreClosed` -/

universe u

/-- **A store for the covered references of a block's walk, apart from its family record**: at a
typing walk with its family graph and a step context, for a block `B` with the family record
`rb`, a store `Rc` whose records are records of the step's store `E`, closed under what its
records use, holding every covered reference of a record the walk reached at rank at most `B`'s,
and holding no recursor projection record of `rb`. -/
def CoveredStoreApart : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (B rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst),
        fam B = some rb → FamRecRecord E₀ rb crb rs →
        ∃ Rc : Ixon.Env,
          (∀ y c, recordOf Rc y = some c → recordOf E y = some c) ∧ UsedClosed Rc ∧
          (∀ a x, Top a → rank a ≤ rank B → UsedRef E₀ a x → Covered t x → Held Rc x) ∧
          (∀ j rc, rs[j]? = some (.recr rc) → ¬ Held Rc (memberAddr rb j (.recr rc)))

/-- **`TwinFamily.GraphStoreClosed` from `CoveredStoreApart`**: the set is the addresses held by
the store of the walk below `B`'s rank with `Rc` (`belowStore`), a used-closed sub-store of the
step's store (`belowStore_usedClosed`), so closed under what the run's store answers
(`closedOn_of_usedClosed_sub`). It holds `B`, which the walk reached (`FamilyGraph.famBlock`). A
recursor projection record of `rb` is none of `Rc`'s, and none of the walk below `B`'s rank
(`not_walkBelow_member`): the family record, where the walk reached it, comes after its block
(`FamilyGraph.famAfter`). -/
theorem graphStoreClosed_of_coveredStore (hCov : CoveredStoreApart.{u}) :
    TwinFamily.GraphStoreClosed.{u} := by
  intro calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx B rb crb rs
    hfam hrb
  obtain ⟨Rc, hsub, hcl, hcov, hapart⟩ :=
    hCov calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx B rb crb rs
      hfam hrb
  obtain ⟨bAddrW, hWc, hG⟩ := hWalk
  have ht : t.check = .ok () := hWc.check_ok
  have hle : ∀ y c, recordOf E₀ y = some c → recordOf E y = some c := fun y c h =>
    (recordOf_eq_recordAt_of_decoded hctx.recordsFor.1 y).trans (hctx.runRecord y c h)
  have hTB : Top B := hFR.graph.famBlock B rb hfam
  obtain ⟨cb, hcb⟩ := hG.record B hTB
  have hclS := belowStore_usedClosed (n := rank B) hG hle hsub hcl hcov
  have hsubS : ∀ y c, recordOf (belowStore E₀ E Rc Top rank (rank B)) y = some c →
      recordOf E y = some c := fun y c h => (belowStore_recordOf.mp h).2
  obtain ⟨hrec, hflat⟩ := closedOn_of_usedClosed_sub ht hle hctx.runBlob hsubS hclS
  refine ⟨Held (belowStore E₀ E Rc Top rank (rank B)), hrec, hflat, ?_, ?_⟩
  · show (recordOf (belowStore E₀ E Rc Top rank (rank B)) B).isSome = true
    rw [belowStore_recordOf.mpr ⟨Or.inl ⟨B, hTB, Nat.le_refl _, Or.inl rfl⟩, hle B cb hcb⟩]
    rfl
  · intro j rc hj hS
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hS
    rcases (belowStore_recordOf.mp hc).1 with hW | hR
    · exact not_walkBelow_member hG (hrb.members j _ hj)
        (fun hT => hFR.graph.famAfter B rb hfam (Or.inl hT)) hW
    · exact hapart j rc hj hR

end IxVM.Refinement.Binding.FamilyClosedSets

/-! ## The premise from the witness's store and the basis rows -/

namespace IxVM.Refinement.Binding.FamilyClosedSets

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding.FamilyFlat (Held)
open IxVM.Refinement.StoreInhabit (basisStore basisRows)

set_option linter.unusedVariables false

universe u

/-- **A non-empty block of recursors.** -/
def recBlock (c : Ixon.Constant) : Bool :=
  match c.info with
  | .muts ms => !ms.toList.isEmpty && ms.toList.all fun
    | .recr _ => true
    | _ => false
  | _ => false

set_option maxRecDepth 100000 in
/-- **No basis row is a non-empty block of recursors** (decided over the 24 rows). -/
theorem basisRows_noRecBlock : basisRows.all (fun e => !recBlock e.2) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The names of the pinned basis constants are keys of basis roles. -/
private theorem pinned_names_basis (kind : Ix.Kernel.BasisKind) :
    ∀ n ∈ (kind.declsA (md := .anon)).map (·.name),
      n ∈ TableInhabit.basisRoleOrder.map Ix.Kernel.Key.role := by
  cases kind <;> decide +kernel

/-- **The records of `E` at the addresses two stores hold.** -/
noncomputable def heldStore (E R₁ R₂ : Ixon.Env) : Ixon.Env :=
  recordsAt E fun x => Held R₁ x ∨ Held R₂ x

theorem heldStore_recordOf {E R₁ R₂ : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant} :
    recordOf (heldStore E R₁ R₂) a = some c ↔ (Held R₁ a ∨ Held R₂ a) ∧ recordOf E a = some c :=
  recordOf_restrict (fun _ => recordsAt_consts) c

/-- **The records at the addresses two used-closed sub-stores of `E` hold are closed under what
they use.** -/
theorem heldStore_usedClosed {E R₁ R₂ : Ixon.Env}
    (h₁ : ∀ y c, recordOf R₁ y = some c → recordOf E y = some c)
    (h₂ : ∀ y c, recordOf R₂ y = some c → recordOf E y = some c)
    (cl₁ : UsedClosed R₁) (cl₂ : UsedClosed R₂) : UsedClosed (heldStore E R₁ R₂) := by
  have in₁ : ∀ {y : _root_.Address} {c : Ixon.Constant}, recordOf R₁ y = some c →
      recordOf (heldStore E R₁ R₂) y = some c := fun {y c} h =>
    heldStore_recordOf.mpr ⟨Or.inl (by unfold Held; rw [h]; rfl), h₁ y c h⟩
  have in₂ : ∀ {y : _root_.Address} {c : Ixon.Constant}, recordOf R₂ y = some c →
      recordOf (heldStore E R₁ R₂) y = some c := fun {y c} h =>
    heldStore_recordOf.mpr ⟨Or.inr (by unfold Held; rw [h]; rfl), h₂ y c h⟩
  constructor
  · intro a c hrec
    obtain ⟨hQ, hEc⟩ := heldStore_recordOf.mp hrec
    rcases hQ with hR | hR
    · obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hR
      have e : c' = c := Option.some.inj ((h₁ a c' hc').symm.trans hEc)
      subst e
      obtain ⟨ho, hrefs⟩ := cl₁.1 a c' hc'
      refine ⟨?_, ?_⟩
      · obtain ⟨co, hco⟩ := Option.isSome_iff_exists.mp ho
        rw [in₁ hco]
        rfl
      · intro i hi x hx
        obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp (hrefs i hi x hx)
        rw [in₁ hcx]
        rfl
    · obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hR
      have e : c' = c := Option.some.inj ((h₂ a c' hc').symm.trans hEc)
      subst e
      obtain ⟨ho, hrefs⟩ := cl₂.1 a c' hc'
      refine ⟨?_, ?_⟩
      · obtain ⟨co, hco⟩ := Option.isSome_iff_exists.mp ho
        rw [in₂ hco]
        rfl
      · intro i hi x hx
        obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp (hrefs i hi x hx)
        rw [in₂ hcx]
        rfl
  · intro B' c ms hrec hms i m hm
    obtain ⟨hQ, hEc⟩ := heldStore_recordOf.mp hrec
    rcases hQ with hR | hR
    · obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hR
      have e : c' = c := Option.some.inj ((h₁ B' c' hc').symm.trans hEc)
      subst e
      obtain ⟨g1, g2⟩ := cl₁.2 B' c' ms hc' hms i m hm
      exact ⟨in₁ g1, fun ind hind j hj => in₁ (g2 ind hind j hj)⟩
    · obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hR
      have e : c' = c := Option.some.inj ((h₂ B' c' hc').symm.trans hEc)
      subst e
      obtain ⟨g1, g2⟩ := cl₂.2 B' c' ms hc' hms i m hm
      exact ⟨in₂ g1, fun ind hind j hj => in₂ (g2 ind hind j hj)⟩

/-- **A covered address is held by the witness's store or is a basis row**: the witness's
environment keeps a covered role's constant (`TableShape.kept`) as a reading of the record of the
witness's store at the role's address, or as a pinned basis constant, whose name is a basis
role's key (`pinned_names_basis`), bound to a basis row (`addressOf_basis`, `basisRoles_rows`). -/
theorem covered_held {t : Ix.Kernel.RoleTable} {R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    (hshape : TableShape.{u} t (fun _ => True) R envT) {x : _root_.Address}
    (h : Covered t x) : Held R x ∨ Held basisStore x := by
  obtain ⟨r, ha, hw⟩ := h
  obtain ⟨ci, hfind, hk⟩ := hshape.kept (Ix.SpecDigest.groupOf r) r x trivial
    (role_mem_roleGroup r) (Or.inl (Or.inl hw)) ha
  rcases hk with ⟨kind, hci⟩ | ⟨-, ci₀, ⟨c, hc, -⟩, -⟩
  · right
    have hname : ci.name = .role r := Ix.Kernel.Semantics.Env.find?_name hfind
    obtain ⟨r', hr', he⟩ := List.mem_map.mp
      (pinned_names_basis kind ci.name (List.mem_map.mpr ⟨ci, hci, rfl⟩))
    have e : r' = r := Ix.Kernel.Key.role.inj (he.trans hname)
    subst e
    have hrows := List.all_eq_true.mp basisRoles_rows r' hr'
    simp only [← Binding.addressOf_basis hshape.prelude hr', ha] at hrows
    exact StoreInhabit.isSome_of_hasKey hrows
  · left
    show (recordOf R x).isSome = true
    rw [hc]
    rfl

/-- **The witness's store holds no recursor projection record of a family record of the graph**:
at a typing walk with its family graph and a step context, for a block `B` with the family record
`rb`. (The family graph gives only that the witness's environment stores no constant at those
addresses, `FamilyGraph.famFresh`.) -/
def WitnessStoreApart : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (R : Ixon.Env) (envT : Ix.Kernel.Env .anon) (E : Ixon.Env)
      (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      StepCtx.{u} calls t R envT E₀ E →
      ∀ (B rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst),
        fam B = some rb → FamRecRecord E₀ rb crb rs →
        ∀ j rc, rs[j]? = some (.recr rc) → ¬ Held R (memberAddr rb j (.recr rc))

/-- **`CoveredStoreApart` from `WitnessStoreApart`**: the store is the step's records at the
addresses the witness's store or the basis store holds (`heldStore`), closed under what its
records use since both are (`TableShape.usedClosed`, `StoreInhabit.store_usedClosed`); it holds
every covered address (`covered_held`); and no basis row is a recursor projection record of the
family record, whose block the basis store would hold, a non-empty block of recursors
(`basisRows_noRecBlock`). -/
theorem coveredStoreApart_of_witness (hW : WitnessStoreApart.{u}) : CoveredStoreApart.{u} := by
  intro calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx B rb crb rs
    hfam hrb
  have hapart := hW calls t seeds E₀ lim Top rank hWalk R envT E fam twin adv Inner hFR hctx B rb
    crb rs hfam hrb
  have hdec := hctx.recordsFor.1
  have hle : ∀ y c, recordOf E₀ y = some c → recordOf E y = some c := fun y c h =>
    (recordOf_eq_recordAt_of_decoded hdec y).trans (hctx.runRecord y c h)
  have hRE : ∀ y c, recordOf R y = some c → recordOf E y = some c := fun y c h =>
    (recordOf_eq_recordAt_of_decoded hdec y).trans (hctx.recordsFor.2.1 y c h)
  have hBE : ∀ y c, recordOf basisStore y = some c → recordOf E y = some c := fun y c h =>
    (recordOf_eq_recordAt_of_decoded hdec y).trans
      ((recordsFor_basisStore hctx.recordsFor).2.1 y c h)
  refine ⟨heldStore E R basisStore, fun y c h => (heldStore_recordOf.mp h).2,
    heldStore_usedClosed hRE hBE hctx.shape.usedClosed StoreInhabit.store_usedClosed, ?_, ?_⟩
  · intro a x _ _ _ hcov
    show (recordOf (heldStore E R basisStore) x).isSome = true
    rcases covered_held hctx.shape hcov with hx | hx
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      rw [heldStore_recordOf.mpr ⟨Or.inl hx, hRE x c hc⟩]
      rfl
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      rw [heldStore_recordOf.mpr ⟨Or.inr hx, hBE x c hc⟩]
      rfl
  · intro j rc hj hS
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hS
    rcases (heldStore_recordOf.mp hc).1 with hR | hBs
    · exact hapart j rc hj hR
    · obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp hBs
      have e : cx = memberProjection rb j (.recr rc) := Option.some.inj
        ((hBE _ cx hcx).symm.trans (hle _ _ (hrb.members j _ hj)))
      have hown := (StoreInhabit.store_usedClosed.1 _ cx hcx).1
      rw [e, ownerOf_memberProjection] at hown
      obtain ⟨cb, hcb⟩ := Option.isSome_iff_exists.mp hown
      have e2 : cb = crb := Option.some.inj ((hBE rb cb hcb).symm.trans (hle rb crb hrb.record))
      subst e2
      have hno := List.all_eq_true.mp basisRows_noRecBlock (rb, cb)
        (StoreInhabit.store_record_inv hcb)
      have hyes : recBlock cb = true := by
        unfold recBlock
        rw [hrb.muts]
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          List.all_eq_true]
        refine ⟨?_, fun m hm => ?_⟩
        · intro hnil
          have hjl : rs.toList[j]? = some (Ixon.MutConst.recr rc) := by
            rw [Array.getElem?_toList]
            exact hj
          rw [hnil] at hjl
          cases hjl
        · obtain ⟨r, rfl⟩ := hrb.recrs m hm
          rfl
      rw [hyes] at hno
      cases hno

/-- **`TwinFamily.GraphStoreClosed` from `WitnessStoreApart`**
(`graphStoreClosed_of_coveredStore`, `coveredStoreApart_of_witness`). -/
theorem graphStoreClosed_of_witnessApart (hW : WitnessStoreApart.{u}) :
    TwinFamily.GraphStoreClosed.{u} :=
  graphStoreClosed_of_coveredStore (coveredStoreApart_of_witness hW)

end IxVM.Refinement.Binding.FamilyClosedSets
