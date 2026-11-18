import IxVMRefinement.FamilyGraph.Graph
import Ix.CompileCert.MutualProjections
import IxC.Ixon.Verify.Framing

/-! # Deciding the family graph over a store and finite data

`GraphData` lists, for one run over a store: the checked records in the order of their ranks,
which of them the walk reached and which a family check checked, the family record of each
modeled block, the twins, the advice records, and constant addresses the witness's environment
does not store. `Checks d t E₀` is a conjunction of bounded statements about the store and the
role table, each decidable by evaluation (`recordOf`, the used references, the constant
addresses of a block, the exact bytes of a projection record). `familyGraph_of_checks` proves
`FamilyGraph` from it, at the predicates the data defines.

Records are compared through their stored bytes: a store holds the member projection of a block
where it holds, at the member's address, exactly the serialization of that projection
(`HoldsBytes`, `recordOf_of_holdsBytes`). -/

namespace IxVM.Refinement.Typing.GraphCheck

open IxVM.Consistency
open IxVM.Refinement.Typing

set_option linter.unusedVariables false

abbrev Addr := _root_.Address

/-- **The finite data of a run's family graph.** -/
structure GraphData where
  /-- The checked records, earliest first: a record's rank is its position. -/
  order : List Addr
  /-- The records the walk reached. -/
  tops : List Addr
  /-- The records checked inside a family check. -/
  inner : List Addr
  /-- A modeled block and the family record it installs. -/
  fam : List (Addr × Addr)
  /-- A second family record and its block. -/
  twin : List (Addr × Addr)
  /-- A block and an advice record of its family check. -/
  adv : List (Addr × Addr)
  /-- Constant addresses the witness's environment does not store. -/
  fresh : List Addr

/-- The position of an address in a list (the list's length where it is absent). -/
def rankIn : List Addr → Addr → Nat
  | [], _ => 0
  | b :: rest, a => if b = a then 0 else rankIn rest a + 1

/-- The first value at a key. -/
def assoc : List (Addr × Addr) → Addr → Option Addr
  | [], _ => none
  | p :: rest, a => if p.1 = a then some p.2 else assoc rest a

theorem assoc_mem : ∀ {l : List (Addr × Addr)} {a b : Addr}, assoc l a = some b → (a, b) ∈ l
  | [], _, _, h => nomatch h
  | p :: rest, a, b, h => by
    unfold assoc at h
    split at h
    · next hk =>
      have hb : p.2 = b := Option.some.inj h
      have hp : p = (a, b) := Prod.ext hk hb
      rw [hp]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (assoc_mem h)

/-- The predicates of the graph, from the data. -/
def GraphData.Top (d : GraphData) (a : Addr) : Prop := a ∈ d.tops
def GraphData.Inner (d : GraphData) (a : Addr) : Prop := a ∈ d.inner
def GraphData.rank (d : GraphData) (a : Addr) : Nat := rankIn d.order a
def GraphData.famOf (d : GraphData) (B : Addr) : Option Addr := assoc d.fam B
def GraphData.twinOf (d : GraphData) (rb : Addr) : Option Addr := assoc d.twin rb
def GraphData.advOf (d : GraphData) (B a : Addr) : Prop := (B, a) ∈ d.adv

/-! ## Records in Lean's logic, decided -/

instance decInLogicMut : (m : Ixon.MutConst) → Decidable (InLogicMut m)
  | .defn d => inferInstanceAs (Decidable (Ix.Kernel.Reader.safetyDecline d = none))
  | .indc i => inferInstanceAs
      (Decidable (i.isUnsafe = false ∧ ∀ ctor ∈ i.ctors.toList, ctor.isUnsafe = false))
  | .recr r => inferInstanceAs (Decidable (r.isUnsafe = false))

instance decInLogic (c : Ixon.Constant) : Decidable (InLogic c) :=
  match h : c.info with
  | .defn d => decidable_of_iff (Ix.Kernel.Reader.safetyDecline d = none)
      (by simp only [InLogic, h])
  | .recr r => decidable_of_iff (r.isUnsafe = false) (by simp only [InLogic, h])
  | .axio a => decidable_of_iff (a.isUnsafe = false) (by simp only [InLogic, h])
  | .muts ms => decidable_of_iff (∀ m ∈ ms.toList, InLogicMut m) (by simp only [InLogic, h])
  | .quot _ => isTrue (by simp only [InLogic, h])
  | .cPrj _ => isTrue (by simp only [InLogic, h])
  | .rPrj _ => isTrue (by simp only [InLogic, h])
  | .iPrj _ => isTrue (by simp only [InLogic, h])
  | .dPrj _ => isTrue (by simp only [InLogic, h])

/-! ## The constant addresses of a record, bounded -/

theorem lt_size_of_getElem? {α : Type} {xs : Array α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : i < xs.size := by
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp h
  exact hi

/-- `x` is the address of a constructor of the member `m` at position `i` of the block `A`. -/
def CtorAddrP (A : Addr) (i : Nat) (x : Addr) : Ixon.MutConst → Prop
  | .indc ind => ∃ j ∈ List.range ind.ctors.size, x = ctorAddr A i j
  | .defn _ => False
  | .recr _ => False

instance decCtorAddrP (A : Addr) (i : Nat) (x : Addr) :
    (m : Ixon.MutConst) → Decidable (CtorAddrP A i x m)
  | .indc ind => inferInstanceAs (Decidable (∃ j ∈ List.range ind.ctors.size, x = ctorAddr A i j))
  | .defn _ => isFalse (fun h => h)
  | .recr _ => isFalse (fun h => h)

/-- `x` is a constant address of a record with the payload `info` at `A`. -/
def ConstAddrInfoP (A x : Addr) : Ixon.ConstantInfo → Prop
  | .muts ms => ∃ i ∈ List.range ms.size, ∃ m ∈ ms[i]?,
      (x = memberAddr A i m ∨ CtorAddrP A i x m)
  | .defn _ => x = A
  | .recr _ => x = A
  | .axio _ => x = A
  | .quot _ => x = A
  | .cPrj _ => False
  | .rPrj _ => False
  | .iPrj _ => False
  | .dPrj _ => False

instance decConstAddrInfoP (A x : Addr) :
    (info : Ixon.ConstantInfo) → Decidable (ConstAddrInfoP A x info)
  | .muts ms => inferInstanceAs (Decidable (∃ i ∈ List.range ms.size, ∃ m ∈ ms[i]?,
      (x = memberAddr A i m ∨ CtorAddrP A i x m)))
  | .defn _ => inferInstanceAs (Decidable (x = A))
  | .recr _ => inferInstanceAs (Decidable (x = A))
  | .axio _ => inferInstanceAs (Decidable (x = A))
  | .quot _ => inferInstanceAs (Decidable (x = A))
  | .cPrj _ => isFalse (fun h => h)
  | .rPrj _ => isFalse (fun h => h)
  | .iPrj _ => isFalse (fun h => h)
  | .dPrj _ => isFalse (fun h => h)

/-- `x` is a constant address of the record `c` at `A`, bounded. -/
abbrev ConstAddrP (A : Addr) (c : Ixon.Constant) (x : Addr) : Prop := ConstAddrInfoP A x c.info

theorem constAddr_of_P {A x : Addr} {c : Ixon.Constant} (h : ConstAddrP A c x) :
    ConstAddrOf A c x := by
  have h' : ConstAddrInfoP A x c.info := h
  cases hi : c.info
  case muts ms =>
    rw [hi] at h'
    obtain ⟨i, -, m, hm, hx⟩ := h'
    refine Or.inr ⟨ms, i, m, hi, Option.mem_def.mp hm, ?_⟩
    rcases hx with hx | hx
    · exact Or.inl hx
    · cases m with
      | indc ind =>
        obtain ⟨j, hj, hxj⟩ := hx
        exact Or.inr ⟨ind, j, rfl, List.mem_range.mp hj, hxj⟩
      | defn _ => exact False.elim hx
      | recr _ => exact False.elim hx
  case defn dd =>
    rw [hi] at h'
    exact Or.inl ⟨h', Or.inl ⟨dd, hi⟩⟩
  case recr r =>
    rw [hi] at h'
    exact Or.inl ⟨h', Or.inr (Or.inl ⟨r, hi⟩)⟩
  case axio a =>
    rw [hi] at h'
    exact Or.inl ⟨h', Or.inr (Or.inr (Or.inl ⟨a, hi⟩))⟩
  case quot q =>
    rw [hi] at h'
    exact Or.inl ⟨h', Or.inr (Or.inr (Or.inr ⟨q, hi⟩))⟩
  all_goals (rw [hi] at h'; exact False.elim h')

theorem constAddrP_of {A x : Addr} {c : Ixon.Constant} (h : ConstAddrOf A c x) :
    ConstAddrP A c x := by
  show ConstAddrInfoP A x c.info
  rcases h with ⟨hx, hs⟩ | ⟨ms, i, m, hms, hm, hx⟩
  · rcases hs with ⟨dd, hd⟩ | ⟨r, hr⟩ | ⟨a, ha⟩ | ⟨q, hq⟩
    · rw [hd]
      exact hx
    · rw [hr]
      exact hx
    · rw [ha]
      exact hx
    · rw [hq]
      exact hx
  · rw [hms]
    refine ⟨i, List.mem_range.mpr (lt_size_of_getElem? hm), m, Option.mem_def.mpr hm, ?_⟩
    rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
    · exact Or.inl hx
    · rw [hind]
      exact Or.inr ⟨j, List.mem_range.mpr hj, hx⟩

/-! ## Projection records through their stored bytes -/

/-- **The store holds, at `x`, exactly the serialization of the record `P`.** -/
abbrev HoldsBytes (E₀ : Ixon.Env) (x : Addr) (P : Ixon.Constant) : Prop :=
  ∃ lc ∈ E₀.consts.get? x, lc.rawBytes = Ixon.serConstant P

theorem recordOf_of_holdsBytes {E₀ : Ixon.Env} {x : Addr} {P : Ixon.Constant}
    (h : HoldsBytes E₀ x P) (hwf : P.wireWF) : recordOf E₀ x = some P := by
  obtain ⟨lc, hlc, hb⟩ := h
  have hget : E₀.consts.get? x = some lc := Option.mem_def.mp hlc
  have h1 : recordOf E₀ x = (Ixon.deConstantExact lc.rawBytes).toOption := by
    unfold recordOf
    simp only [hget, Option.bind_some]
  have h2 : (Ixon.deConstantExact lc.rawBytes).toOption = some P := by
    rw [hb, Ixon.Verify.deConstantExact_serConstant P hwf]
    rfl
  exact h1.trans h2

theorem memberProjection_wireWF (B : Addr) (hB : B.hash.size = 32) (i : Nat)
    (m : Ixon.MutConst) : (memberProjection B i m).wireWF := by
  cases m <;> exact Ix.CompileCert.MutualProjections.empty_tables_wire _ hB

theorem constructorProjection_wireWF (B : Addr) (hB : B.hash.size = 32) (i j : Nat) :
    (constructorProjection B i j).wireWF :=
  Ix.CompileCert.MutualProjections.empty_tables_wire _ hB

/-! ## A block of recursors with its member projections -/

/-- A recursor member. -/
def RecrP : Ixon.MutConst → Prop
  | .recr _ => True
  | .defn _ => False
  | .indc _ => False

instance decRecrP : (m : Ixon.MutConst) → Decidable (RecrP m)
  | .recr _ => isTrue trivial
  | .defn _ => isFalse (fun h => h)
  | .indc _ => isFalse (fun h => h)

/-- The payload of a block of at least one recursor whose member projections the store holds. -/
def RecMembersP (E₀ : Ixon.Env) (rb : Addr) : Ixon.ConstantInfo → Prop
  | .muts rs => rs.size ≠ 0 ∧ (∀ m ∈ rs.toList, RecrP m) ∧
      ∀ i ∈ List.range rs.size, ∀ m ∈ rs[i]?,
        HoldsBytes E₀ (memberAddr rb i m) (memberProjection rb i m)
  | .defn _ => False
  | .recr _ => False
  | .axio _ => False
  | .quot _ => False
  | .cPrj _ => False
  | .rPrj _ => False
  | .iPrj _ => False
  | .dPrj _ => False

instance decRecMembersP (E₀ : Ixon.Env) (rb : Addr) :
    (info : Ixon.ConstantInfo) → Decidable (RecMembersP E₀ rb info)
  | .muts rs => inferInstanceAs (Decidable (rs.size ≠ 0 ∧ (∀ m ∈ rs.toList, RecrP m) ∧
      ∀ i ∈ List.range rs.size, ∀ m ∈ rs[i]?,
        HoldsBytes E₀ (memberAddr rb i m) (memberProjection rb i m)))
  | .defn _ => isFalse (fun h => h)
  | .recr _ => isFalse (fun h => h)
  | .axio _ => isFalse (fun h => h)
  | .quot _ => isFalse (fun h => h)
  | .cPrj _ => isFalse (fun h => h)
  | .rPrj _ => isFalse (fun h => h)
  | .iPrj _ => isFalse (fun h => h)
  | .dPrj _ => isFalse (fun h => h)

/-- **A block of at least one recursor at `rb`, in Lean's logic, with its member projections**,
bounded. -/
abbrev RecBlockP (E₀ : Ixon.Env) (rb : Addr) : Prop :=
  rb.hash.size = 32 ∧ ∃ crb ∈ recordOf E₀ rb, InLogic crb ∧ RecMembersP E₀ rb crb.info

theorem famRecRecord_of_P {E₀ : Ixon.Env} {rb : Addr} (h : RecBlockP E₀ rb) :
    ∃ crb rs, FamRecRecord E₀ rb crb rs ∧ rs.size ≠ 0 := by
  obtain ⟨hsz, crb, hcrb, hlog, hmem⟩ := h
  cases hi : crb.info
  case muts rs =>
    rw [hi] at hmem
    obtain ⟨hne, hrec, hproj⟩ := hmem
    refine ⟨crb, rs, ⟨Option.mem_def.mp hcrb, hi, ?_, hlog, ?_⟩, hne⟩
    · intro m hm
      have hr := hrec m hm
      cases m with
      | recr r => exact ⟨r, rfl⟩
      | defn _ => exact False.elim hr
      | indc _ => exact False.elim hr
    · intro i m him
      exact recordOf_of_holdsBytes
        (hproj i (List.mem_range.mpr (lt_size_of_getElem? him)) m (Option.mem_def.mpr him))
        (memberProjection_wireWF rb hsz i m)
  all_goals (rw [hi] at hmem; exact False.elim hmem)

/-! ## The blocks checked inside a family check -/

/-- The store holds the constructor projections of the member `m` at position `i` of `B`. -/
def CtorsHeldP (E₀ : Ixon.Env) (B : Addr) (i : Nat) : Ixon.MutConst → Prop
  | .indc ind => ∀ j ∈ List.range ind.ctors.size,
      HoldsBytes E₀ (ctorAddr B i j) (constructorProjection B i j)
  | .defn _ => True
  | .recr _ => True

instance decCtorsHeldP (E₀ : Ixon.Env) (B : Addr) (i : Nat) :
    (m : Ixon.MutConst) → Decidable (CtorsHeldP E₀ B i m)
  | .indc ind => inferInstanceAs (Decidable (∀ j ∈ List.range ind.ctors.size,
      HoldsBytes E₀ (ctorAddr B i j) (constructorProjection B i j)))
  | .defn _ => isTrue trivial
  | .recr _ => isTrue trivial

/-- For a block payload, the store holds the member and constructor projections. -/
def MembersHeldP (E₀ : Ixon.Env) (B : Addr) : Ixon.ConstantInfo → Prop
  | .muts ms => B.hash.size = 32 ∧ ∀ i ∈ List.range ms.size, ∀ m ∈ ms[i]?,
      HoldsBytes E₀ (memberAddr B i m) (memberProjection B i m) ∧ CtorsHeldP E₀ B i m
  | .defn _ => True
  | .recr _ => True
  | .axio _ => True
  | .quot _ => True
  | .cPrj _ => True
  | .rPrj _ => True
  | .iPrj _ => True
  | .dPrj _ => True

instance decMembersHeldP (E₀ : Ixon.Env) (B : Addr) :
    (info : Ixon.ConstantInfo) → Decidable (MembersHeldP E₀ B info)
  | .muts ms => inferInstanceAs (Decidable (B.hash.size = 32 ∧
      ∀ i ∈ List.range ms.size, ∀ m ∈ ms[i]?,
        HoldsBytes E₀ (memberAddr B i m) (memberProjection B i m) ∧ CtorsHeldP E₀ B i m))
  | .defn _ => isTrue trivial
  | .recr _ => isTrue trivial
  | .axio _ => isTrue trivial
  | .quot _ => isTrue trivial
  | .cPrj _ => isTrue trivial
  | .rPrj _ => isTrue trivial
  | .iPrj _ => isTrue trivial
  | .dPrj _ => isTrue trivial

/-- No axiom and no quotient payload. -/
def NotAxQuotP : Ixon.ConstantInfo → Prop
  | .axio _ => False
  | .quot _ => False
  | .muts _ => True
  | .defn _ => True
  | .recr _ => True
  | .cPrj _ => True
  | .rPrj _ => True
  | .iPrj _ => True
  | .dPrj _ => True

instance decNotAxQuotP : (info : Ixon.ConstantInfo) → Decidable (NotAxQuotP info)
  | .axio _ => isFalse (fun h => h)
  | .quot _ => isFalse (fun h => h)
  | .muts _ => isTrue trivial
  | .defn _ => isTrue trivial
  | .recr _ => isTrue trivial
  | .cPrj _ => isTrue trivial
  | .rPrj _ => isTrue trivial
  | .iPrj _ => isTrue trivial
  | .dPrj _ => isTrue trivial

/-- No block payload. -/
def NotMutsP : Ixon.ConstantInfo → Prop
  | .muts _ => False
  | .axio _ => True
  | .quot _ => True
  | .defn _ => True
  | .recr _ => True
  | .cPrj _ => True
  | .rPrj _ => True
  | .iPrj _ => True
  | .dPrj _ => True

instance decNotMutsP : (info : Ixon.ConstantInfo) → Decidable (NotMutsP info)
  | .muts _ => isFalse (fun h => h)
  | .axio _ => isTrue trivial
  | .quot _ => isTrue trivial
  | .defn _ => isTrue trivial
  | .recr _ => isTrue trivial
  | .cPrj _ => isTrue trivial
  | .rPrj _ => isTrue trivial
  | .iPrj _ => isTrue trivial
  | .dPrj _ => isTrue trivial

/-- The store holds a record at `x` that is no block: what a needed reference is, at least. -/
abbrev NeedP (E₀ : Ixon.Env) (x : Addr) : Prop := ∃ c ∈ recordOf E₀ x, NotMutsP c.info

theorem needP_of_needOk {E₀ : Ixon.Env} {x : Addr} (h : NeedOk E₀ x) : NeedP E₀ x := by
  obtain ⟨c, hc, hnb, -, -⟩ := h
  refine ⟨c, Option.mem_def.mpr hc, ?_⟩
  cases hi : c.info
  case muts ms => exact absurd ⟨ms, hi⟩ hnb
  all_goals exact trivial

/-! ## Covered references and ownership below a rank, bounded -/

/-- `x` is bound to a role whose record a validation walks, bounded over the table. -/
abbrev CoveredP (t : Ix.Kernel.RoleTable) (x : Addr) : Prop :=
  ∃ p ∈ t.bound.toList, walkedRole p.1 = true ∧ t.addressOf? p.1 = some x

theorem covered_of_P {t : Ix.Kernel.RoleTable} {x : Addr} (h : CoveredP t x) : Covered t x := by
  obtain ⟨p, -, hw, ha⟩ := h
  exact ⟨p.1, ha, hw⟩

/-- `x` is owned by a checked, unclaimed record of rank below `n`, bounded over the data. -/
abbrev OwnedBelowP (d : GraphData) (E₀ : Ixon.Env) (n : Nat) (x : Addr) : Prop :=
  ∃ D ∈ d.order, (D ∈ d.tops ∨ D ∈ d.inner) ∧ (∀ q ∈ d.fam, q.2 ≠ D) ∧
    rankIn d.order D < n ∧
    ∃ c ∈ recordOf E₀ D, (ConstAddrP D c x ∨
      ∃ rb ∈ assoc d.fam D, ∃ crb ∈ recordOf E₀ rb, ConstAddrP rb crb x)

theorem unclaimed_of_P {d : GraphData} {D : Addr} (h : ∀ q ∈ d.fam, q.2 ≠ D) :
    Unclaimed d.famOf D :=
  fun B hB => h (B, D) (assoc_mem hB) rfl

theorem ownedBelow_of_P {d : GraphData} {E₀ : Ixon.Env} {n : Nat} {x : Addr}
    (h : OwnedBelowP d E₀ n x) : OwnedBelow E₀ d.Top d.Inner d.rank d.famOf n x := by
  obtain ⟨D, -, hW, hU, hrk, c, hc, hown⟩ := h
  refine ⟨D, hW, unclaimed_of_P hU, hrk, c, Option.mem_def.mp hc, ?_⟩
  rcases hown with h | ⟨rb, hrb, crb, hcrb, hx⟩
  · exact Or.inl (constAddr_of_P h)
  · exact Or.inr ⟨rb, crb, Option.mem_def.mp hrb, Option.mem_def.mp hcrb, constAddr_of_P hx⟩

/-! ## The checks -/

section Checks

variable (d : GraphData) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)

/-- A block with a family record is top-walked. -/
abbrev FamBlockP : Prop := ∀ p ∈ d.fam, p.1 ∈ d.tops

/-- A block with a family record is unclaimed, in Lean's logic, with a fresh constant
address. -/
abbrev FamUnitP : Prop :=
  ∀ p ∈ d.fam, (∀ q ∈ d.fam, q.2 ≠ p.1) ∧
    ∃ cb ∈ recordOf E₀ p.1, InLogic cb ∧ ∃ x ∈ d.fresh, ConstAddrP p.1 cb x

/-- A family record is a block of at least one recursor. -/
abbrev FamRecordP : Prop := ∀ p ∈ d.fam, RecBlockP E₀ p.2

/-- A checked family record comes after its block. -/
abbrev FamAfterP : Prop :=
  ∀ p ∈ d.fam, (p.2 ∈ d.tops ∨ p.2 ∈ d.inner) → rankIn d.order p.1 < rankIn d.order p.2

/-- One block claims a family record. -/
abbrev FamInjP : Prop := ∀ p ∈ d.fam, ∀ q ∈ d.fam, p.2 = q.2 → p.1 = q.1

/-- What a family record uses is covered, the block's, its own, or owned below the block. -/
abbrev FamClosedP : Prop :=
  ∀ p ∈ d.fam, ∀ c ∈ recordOf E₀ p.2, ∀ i ∈ usedRefIdxs c, ∀ x ∈ c.refs[i]?, NeedP E₀ x →
    CoveredP t x ∨ (∃ cb ∈ recordOf E₀ p.1, ConstAddrP p.1 cb x) ∨ ConstAddrP p.2 c x ∨
      OwnedBelowP d E₀ (rankIn d.order p.1) x

/-- An advice record is checked, unclaimed, below its block, in Lean's logic. -/
abbrev AdvEarlierP : Prop :=
  ∀ p ∈ d.adv, (p.2 ∈ d.tops ∨ p.2 ∈ d.inner) ∧ (∀ q ∈ d.fam, q.2 ≠ p.2) ∧
    rankIn d.order p.2 < rankIn d.order p.1 ∧ ∀ ca ∈ recordOf E₀ p.2, InLogic ca

/-- A record checked inside a family check is in the store. -/
abbrev InnerRecordP : Prop := ∀ a ∈ d.inner, ∃ c ∈ recordOf E₀ a, True

/-- The projections of a block checked inside a family check are in the store. -/
abbrev InnerMembersP : Prop := ∀ a ∈ d.inner, ∀ c ∈ recordOf E₀ a, MembersHeldP E₀ a c.info

/-- A record checked inside a family check is no axiom and no quotient record. -/
abbrev InnerKindP : Prop := ∀ a ∈ d.inner, ∀ c ∈ recordOf E₀ a, NotAxQuotP c.info

/-- What a record checked inside a family check uses is covered, its own, or owned below. -/
abbrev InnerClosedP : Prop :=
  ∀ a ∈ d.inner, ∀ c ∈ recordOf E₀ a, ∀ i ∈ usedRefIdxs c, ∀ x ∈ c.refs[i]?, NeedP E₀ x →
    CoveredP t x ∨ ConstAddrP a c x ∨ OwnedBelowP d E₀ (rankIn d.order a) x

/-- A twin is a second family record of a block with one, after the block. -/
abbrev TwinBlockP : Prop :=
  ∀ p ∈ d.twin, ∃ rb ∈ assoc d.fam p.2, p.1 ≠ rb ∧ rankIn d.order p.2 < rankIn d.order p.1

/-- A twin is checked, unclaimed and without a family record of its own. -/
abbrev TwinWalkedP : Prop :=
  ∀ p ∈ d.twin, (p.1 ∈ d.tops ∨ p.1 ∈ d.inner) ∧ (∀ q ∈ d.fam, q.2 ≠ p.1) ∧
    assoc d.fam p.1 = none

/-- A twin is a block of at least one recursor. -/
abbrev TwinRecordP : Prop := ∀ p ∈ d.twin, RecBlockP E₀ p.1

/-- **The checks of the family graph over a store**: bounded, decided by evaluation. -/
abbrev Checks : Prop :=
  FamBlockP d ∧ FamUnitP d E₀ ∧ FamRecordP d E₀ ∧ FamAfterP d ∧ FamInjP d ∧ FamClosedP d t E₀ ∧
    AdvEarlierP d E₀ ∧ InnerRecordP d E₀ ∧ InnerMembersP d E₀ ∧ InnerKindP d E₀ ∧
    InnerClosedP d t E₀ ∧ TwinBlockP d ∧ TwinWalkedP d ∧ TwinRecordP d E₀

end Checks

/-- **The family graph from the checks**, at the predicates the data defines, for a witness's
environment that stores none of the listed fresh addresses and no constant address of a family
record. -/
theorem familyGraph_of_checks {d : GraphData} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    (h : Checks d t E₀) {envT : Ix.Kernel.Env .anon}
    (hfresh : ∀ x ∈ d.fresh, ¬ StoredAt t envT x)
    (hff : ∀ p ∈ d.fam, ∀ crb x, recordOf E₀ p.2 = some crb → ConstAddrOf p.2 crb x →
      ¬ StoredAt t envT x) :
    FamilyGraph t envT E₀ d.Top d.rank d.famOf d.twinOf d.advOf d.Inner := by
  obtain ⟨kBlock, kUnit, kRecord, kAfter, kInj, kClosed, kAdv, kIRec, kIMem, kIKind, kIClosed,
    kTBlock, kTWalked, kTRecord⟩ := h
  refine
    { famBlock := fun B rb hB => kBlock (B, rb) (assoc_mem hB)
      famUnit := ?_
      famRecord := fun B rb hB => famRecRecord_of_P (kRecord (B, rb) (assoc_mem hB))
      famAfter := fun B rb hB hW => kAfter (B, rb) (assoc_mem hB) hW
      famInj := fun B B' rb hB hB' => kInj (B, rb) (assoc_mem hB) (B', rb) (assoc_mem hB') rfl
      famFresh := fun B rb crb x hB hcrb hx => hff (B, rb) (assoc_mem hB) crb x hcrb hx
      famClosed := ?_
      advEarlier := ?_
      innerRecord := ?_
      innerMembers := ?_
      innerKind := ?_
      innerClosed := ?_
      twinBlock := ?_
      twinWalked := ?_
      twinRecord := fun rb' B hT => famRecRecord_of_P (kTRecord (rb', B) (assoc_mem hT)) }
  · intro B rb hB
    obtain ⟨hU, cb, hcb, hlog, x, hx, hxc⟩ := kUnit (B, rb) (assoc_mem hB)
    exact ⟨unclaimed_of_P hU, cb, Option.mem_def.mp hcb, hlog, x, constAddr_of_P hxc,
      hfresh x hx⟩
  · intro B rb x hB hu hok
    obtain ⟨c, i, hc, hi, hx⟩ := hu
    rcases kClosed (B, rb) (assoc_mem hB) c (Option.mem_def.mpr hc) i hi x (Option.mem_def.mpr hx)
      (needP_of_needOk hok) with h | ⟨cb, hcb, h⟩ | h | h
    · exact Or.inr (Or.inl (covered_of_P h))
    · exact Or.inr (Or.inr (Or.inl ⟨cb, Option.mem_def.mp hcb, constAddr_of_P h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, constAddr_of_P h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (ownedBelow_of_P h))))
  · intro B a ha
    obtain ⟨hW, hU, hrk, hlog⟩ := kAdv (B, a) ha
    exact ⟨hW, unclaimed_of_P hU, hrk, fun ca hca => hlog ca (Option.mem_def.mpr hca)⟩
  · intro a ha
    obtain ⟨c, hc, -⟩ := kIRec a ha
    exact ⟨c, Option.mem_def.mp hc⟩
  · intro B c ms hI hc hms i m him
    have hm := kIMem B hI c (Option.mem_def.mpr hc)
    rw [hms] at hm
    obtain ⟨hsz, hall⟩ := hm
    obtain ⟨hmem, hct⟩ :=
      hall i (List.mem_range.mpr (lt_size_of_getElem? him)) m (Option.mem_def.mpr him)
    refine ⟨recordOf_of_holdsBytes hmem (memberProjection_wireWF B hsz i m), ?_⟩
    intro ind j hind hj
    rw [hind] at hct
    exact recordOf_of_holdsBytes (hct j (List.mem_range.mpr hj))
      (constructorProjection_wireWF B hsz i j)
  · intro a c hI hc
    have hk := kIKind a hI c (Option.mem_def.mpr hc)
    refine ⟨fun ax hax => ?_, fun q hq => ?_⟩
    · rw [hax] at hk
      exact hk
    · rw [hq] at hk
      exact hk
  · intro a x hI hu hok
    obtain ⟨c, i, hc, hi, hx⟩ := hu
    rcases kIClosed a hI c (Option.mem_def.mpr hc) i hi x (Option.mem_def.mpr hx)
      (needP_of_needOk hok) with h | h | h
    · exact Or.inr (Or.inl (covered_of_P h))
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, constAddr_of_P h⟩))
    · exact Or.inr (Or.inr (Or.inr (ownedBelow_of_P h)))
  · intro rb' B hT
    obtain ⟨rb, hrb, hne, hrk⟩ := kTBlock (rb', B) (assoc_mem hT)
    exact ⟨rb, Option.mem_def.mp hrb, hne, hrk⟩
  · intro rb' B hT
    obtain ⟨hW, hU, hnone⟩ := kTWalked (rb', B) (assoc_mem hT)
    exact ⟨hW, unclaimed_of_P hU, hnone⟩

end IxVM.Refinement.Typing.GraphCheck
