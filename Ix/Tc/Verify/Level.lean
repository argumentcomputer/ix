import Ix.Tc.Level
import Batteries.Data.RBMap.Lemmas
import Lean4Lean.Theory.VLevel

/-!
# Level slice: `KUniv` soundness against `Lean4Lean.Theory.VLevel`

M1 of plans/tc-verify-roadmap.md. This file is also the A3 interop spike.
A3 outcome (2026-07-21): proof files are **classic** (no `module` header) —
a `module` file cannot import the classic-import lean4lean dep at all
(`cannot import non-`module` … from `module``), while classic files import
module-system `Ix.Tc` fine and see its `@[expose]` bodies. The sanity
`rfl`-lemmas below certify the cross-boundary unfolding.

`KUniv` and `VLevel` align constructor-for-constructor (both carry
positional params), so the translation `toVLevel` is a total structural
function — no `ofLevel`-style partiality as with `Lean.Level`'s named
params. The semantic target is `VLevel.eval : List Nat → VLevel → Nat`;
the headline theorems state that the kernel's `univEq`/`univGeq` decide
`≈`/`≤` on translations, conditional only on addr-faithfulness of the
compared pair (the `CollisionFree` pilot: `==` on `KUniv` is Blake3
address equality, sound only up to hash collisions).

Sorry frontier (tracked in the roadmap ledger): `univEq_sound`,
`univGeq_sound` — to be discharged via the canonical-form denotation
layer (normalizeAux/subsumption eval lemmas), which lands next.
-/

namespace Ix.Tc

open Lean4Lean (VLevel)

variable {m : Mode}

namespace KUniv

/-- Translate a kernel level to the lean4lean theory's `VLevel`.
    Structure-preserving; addresses and display names are dropped
    (`VLevel` is the fully anonymous mathematical object). -/
def toVLevel : KUniv m → VLevel
  | .zero _ => .zero
  | .succ u _ => .succ u.toVLevel
  | .max a b _ => .max a.toVLevel b.toVLevel
  | .imax a b _ => .imax a.toVLevel b.toVLevel
  | .param idx _ _ => .param idx.toNat

/-- Anon erasure: drop metadata fields, keep every stored address verbatim
    (addresses are metadata-blind by the hash contract, so the erased term
    is the anon twin with the *same* Merkle addresses). -/
def eraseMeta : KUniv m → KUniv .anon
  | .zero a => .zero a
  | .succ u a => .succ u.eraseMeta a
  | .max x y a => .max x.eraseMeta y.eraseMeta a
  | .imax x y a => .imax x.eraseMeta y.eraseMeta a
  | .param idx _ a => .param idx () a

@[simp] theorem addr_eraseMeta (u : KUniv m) : u.eraseMeta.addr = u.addr := by
  cases u <;> rfl

/-- `toVLevel` is metadata-blind: translating the anon twin gives the same
    `VLevel`. This is the mode-invariance half of the erasure discipline. -/
@[simp] theorem toVLevel_eraseMeta (u : KUniv m) :
    u.eraseMeta.toVLevel = u.toVLevel := by
  induction u with
  | zero => rfl
  | succ _ _ ih => simp [eraseMeta, toVLevel, ih]
  | max _ _ _ iha ihb => simp [eraseMeta, toVLevel, iha, ihb]
  | imax _ _ _ iha ihb => simp [eraseMeta, toVLevel, iha, ihb]
  | param => rfl

/-! Interop sanity checks: these unfold `@[expose]` bodies from
`Ix.Tc.Level` (smart constructors through `Id.run`) against `VLevel`
constructors from the classic-import dep — the A3 spike proper. -/

theorem toVLevel_mkZero : (mkZero (m := m)).toVLevel = .zero := rfl

theorem toVLevel_mkSucc (u : KUniv m) :
    (mkSucc u).toVLevel = .succ u.toVLevel := rfl

theorem toVLevel_mkParam (idx : UInt64) (n : m.F Name) :
    (mkParam idx n).toVLevel = .param idx.toNat := rfl

theorem toVLevel_mkMaxRaw (a b : KUniv m) :
    (mkMaxRaw a b).toVLevel = .max a.toVLevel b.toVLevel := rfl

end KUniv

/-- `==` on `KUniv` is Blake3 address equality — the definitional bridge
    proofs use to expose the fast paths. -/
theorem KUniv.beq_def (u v : KUniv m) : (u == v) = (u.addr == v.addr) := rfl

/-- Addr-faithfulness of a compared pair — the `CollisionFree` pilot, in
    its smallest habitat. `==` on `KUniv` is address equality; concluding
    anything semantic from it is sound only if these two terms don't
    collide. Stated (a) with `==` on addresses — precisely the boolean the
    kernel tests, no `LawfulBEq ByteArray` needed — and (b) up to anon
    erasure, because names are never hashed (equal addresses can never
    promise equal names). The general intern-table `Set.InjOn` form
    arrives in M2. -/
def KUniv.AddrFaithful (u v : KUniv m) : Prop :=
  (u.addr == v.addr) = true → u.eraseMeta = v.eraseMeta

/-- Addr-faithfulness gives semantic agreement: erased twins translate
    identically, and `toVLevel` is erasure-blind. -/
theorem KUniv.AddrFaithful.toVLevel_eq {u v : KUniv m}
    (h : u.AddrFaithful v) (haddr : (u.addr == v.addr) = true) :
    u.toVLevel = v.toVLevel := by
  have := congrArg KUniv.toVLevel (h haddr)
  simpa using this

/-- A level the kernel sees as syntactically zero translates to `.zero`. -/
theorem KUniv.toVLevel_of_isZero {v : KUniv m} (h : v.isZero = true) :
    v.toVLevel = .zero := by
  cases v <;> simp_all [isZero, toVLevel]

/-! ### Denotation of the canonical form

Port of the upstream denotation layer (lean4lean `Verify/Level.lean`,
`evalParam`/`Node.eval`/`evalPath`/`NormLevel.eval`), leaner here because
params are positional (no `ls : List Name` plumbing — `evalParam` *is*
`VLevel.eval`'s param case) but with a genuinely new obligation class: Ix
stores offsets/constants as `UInt64`, so the normalization bookkeeping's
`+ 1`s carry no-wrap side conditions, threaded as size bounds
(`k.toNat + l.size < UInt64.size`). An in-memory `KUniv` can never
violate them; a 2⁶⁴-succ tower genuinely would wrap and mis-normalize —
the hypotheses are load-bearing, not pedantry. -/

namespace Level

variable (ρ : List Nat)

/-- Positional-param value under an assignment — exactly `VLevel.eval`'s
    `.param` case. -/
def evalParam (idx : UInt64) : Nat := ρ.getD idx.toNat 0

/-- `ρ(v.idx) + v.offset` — one variable contribution. -/
def VarNode.eval (v : VarNode) : Nat := evalParam ρ v.idx + v.offset.toNat

/-- Max of the constant and all variable contributions. -/
def NormNode.eval (n : NormNode) : Nat :=
  n.vars.foldl (fun acc v => max acc (v.eval ρ)) n.constant.toNat

/-- Every param on the imax-conditioning chain is nonzero. -/
def allNZ (path : Path) : Bool := path.all fun idx => 0 < evalParam ρ idx

/-- A path-conditioned value: `n` when the chain is active, else `0`. -/
def evalPath (path : Path) (n : Nat) : Nat := if allNZ ρ path then n else 0

/-- Denotation of a canonical form: max over entries of the
    path-conditioned node values. -/
def NormLevel.eval (l : NormLevel) : Nat :=
  l.foldl (fun acc p n => max acc (evalPath ρ p (n.eval ρ))) 0

/-- The upstream `EvalPaths` invariant: `path` was built by ordered
    inserts whose conditioned param values are already ≤ `n` (this is
    what justifies `addConst`'s `k = 1` skip on nonempty paths). -/
inductive EvalPaths : Path → Nat → Prop
  | nil : EvalPaths [] n
  | insert : orderedInsert a path = some path' →
    evalPath ρ path (evalParam ρ a) ≤ n → EvalPaths path n →
    EvalPaths path' n

/-! #### Foundational lemmas (grind bottom-up; the statements are the
design — see the sorry-frontier ledger in plans/tc-verify-roadmap.md) -/

section TransCmp

variable {α : Type _} [Ord α]

private theorem eq_of_swap_eq {o : Ordering} (h : o.swap = .eq) : o = .eq := by
  cases o <;> first | rfl | exact absurd h (by decide)

/-- `.eq` composes under `TransCmp` (not packaged in core/Batteries). -/
private theorem cmp_eq_trans [Std.TransCmp (compare : α → α → Ordering)]
    {a b c : α} (hab : compare a b = .eq) (hbc : compare b c = .eq) :
    compare a c = .eq := by
  have h1 : (compare a c).isLE = true :=
    Std.TransCmp.isLE_trans (by rw [hab]; rfl) (by rw [hbc]; rfl)
  have hba : compare b a = .eq :=
    eq_of_swap_eq ((Std.OrientedCmp.eq_swap
      (cmp := (compare : α → α → Ordering))).symm.trans hab)
  have hcb : compare c b = .eq :=
    eq_of_swap_eq ((Std.OrientedCmp.eq_swap
      (cmp := (compare : α → α → Ordering))).symm.trans hbc)
  have h2 : (compare c a).isLE = true :=
    Std.TransCmp.isLE_trans (by rw [hcb]; rfl) (by rw [hba]; rfl)
  have h3 : compare a c = (compare c a).swap :=
    Std.OrientedCmp.eq_swap (cmp := (compare : α → α → Ordering))
  cases hac : compare a c
  · rw [hac] at h3
    cases hca : compare c a <;> rw [hca] at h3 h2
    · exact absurd h3 (by decide)
    · exact absurd h3 (by decide)
    · exact absurd h2 (by decide)
  · rfl
  · rw [hac] at h1; exact absurd h1 (by decide)

private theorem compareList_eq_swap [Std.TransCmp (compare : α → α → Ordering)] :
    ∀ p q : List α, compareList p q = (compareList q p).swap
  | [], [] => rfl
  | _ :: _, [] => rfl
  | [], _ :: _ => rfl
  | a :: as, b :: bs => by
    simp only [compareList]
    have hswap := Std.OrientedCmp.eq_swap (cmp := (compare : α → α → Ordering))
      (a := a) (b := b)
    cases hba : compare b a <;> rw [hba] at hswap <;>
      simp only [Ordering.swap] at hswap <;> rw [hswap] <;>
      simp [Ordering.swap, compareList_eq_swap as bs]

private theorem compareList_isLE_trans
    [Std.TransCmp (compare : α → α → Ordering)] :
    ∀ p q r : List α, (compareList p q).isLE → (compareList q r).isLE →
      (compareList p r).isLE
  | [], [], r, _, _ => by cases r <;> simp [compareList, Ordering.isLE]
  | [], _ :: _, r, _, _ => by cases r <;> simp [compareList, Ordering.isLE]
  | _ :: _, [], _, h, _ => by simp [compareList, Ordering.isLE] at h
  | _ :: _, _ :: _, [], _, h => by simp [compareList, Ordering.isLE] at h
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    simp only [compareList] at h1 h2 ⊢
    cases hab : compare a b <;> rw [hab] at h1
    · cases hbc : compare b c <;> rw [hbc] at h2
      · have : compare a c = .lt := Std.TransCmp.lt_of_lt_of_le hab (by simp [hbc])
        simp [this, Ordering.isLE]
      · have : compare a c = .lt := Std.TransCmp.lt_of_lt_of_le hab (by simp [hbc])
        simp [this, Ordering.isLE]
      · simp [Ordering.isLE] at h2
    · cases hbc : compare b c <;> rw [hbc] at h2
      · have : compare a c = .lt :=
          Std.TransCmp.lt_of_le_of_lt (by simp [hab]) hbc
        simp [this, Ordering.isLE]
      · have : compare a c = .eq := cmp_eq_trans hab hbc
        rw [this]
        exact compareList_isLE_trans as bs cs h1 h2
      · simp [Ordering.isLE] at h2
    · simp [Ordering.isLE] at h1

end TransCmp

/-- Ix's lexicographic list compare (Ix/Common.lean `compareList`) is a
    lawful comparator — prerequisite for every Batteries `RBMap` bridge
    lemma (`find?_insert*`, `mem_toList_unique`, …). -/
instance : Std.TransCmp (compare : Path → Path → Ordering) where
  eq_swap := compareList_eq_swap _ _
  isLE_trans := compareList_isLE_trans _ _ _

private theorem compareList_refl {α : Type _} [Ord α]
    [Std.ReflCmp (compare : α → α → Ordering)] :
    ∀ p : List α, compareList p p = .eq
  | [] => rfl
  | _ :: as => by
    simp only [compareList, Std.ReflCmp.compare_self]
    exact compareList_refl as

private theorem compareList_eq {α : Type _} [Ord α]
    [Std.LawfulEqCmp (compare : α → α → Ordering)] :
    ∀ {p q : List α}, compareList p q = .eq → p = q
  | [], [], _ => rfl
  | _ :: _, [], h => by simp [compareList] at h
  | [], _ :: _, h => by simp [compareList] at h
  | a :: as, b :: bs, h => by
    simp only [compareList] at h
    cases hab : compare a b <;> rw [hab] at h
    · simp at h
    · rw [Std.LawfulEqCmp.eq_of_compare hab, compareList_eq h]
    · simp at h

instance : Std.ReflCmp (compare : Path → Path → Ordering) where
  compare_self := compareList_refl _

instance : Std.LawfulEqCmp (compare : Path → Path → Ordering) where
  eq_of_compare := compareList_eq

private theorem foldl_max_le {α : Type _} {l : List α} {f : α → Nat}
    {init x : Nat} :
    l.foldl (fun acc v => max acc (f v)) init ≤ x ↔
      init ≤ x ∧ ∀ v ∈ l, f v ≤ x := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Nat.max_le]
    simp [List.forall_mem_cons, and_assoc]

theorem NormNode.eval_le {ρ : List Nat} {n : NormNode} {x : Nat} :
    n.eval ρ ≤ x ↔ n.constant.toNat ≤ x ∧ ∀ v ∈ n.vars, v.eval ρ ≤ x := by
  rw [NormNode.eval, ← Array.foldl_toList, foldl_max_le]
  simp

theorem allNZ_cons {ρ : List Nat} {a : UInt64} {path : Path} :
    allNZ ρ (a :: path) = true ↔
      0 < evalParam ρ a ∧ allNZ ρ path = true := by
  simp [allNZ]

theorem evalPath_le {ρ : List Nat} {path : Path} {n x : Nat} :
    evalPath ρ path n ≤ x ↔ (allNZ ρ path = true → n ≤ x) := by
  simp only [evalPath]; split <;> simp [*]

theorem evalPath_max {ρ : List Nat} {path : Path} {a b : Nat} :
    evalPath ρ path (max a b)
      = max (evalPath ρ path a) (evalPath ρ path b) := by
  simp only [evalPath]; split <;> simp

/-- `≤`-characterization of the map denotation via `find?` — the RBMap
    bridge (`foldl_eq_foldl_toList` + `find?`↔`toList` membership). -/
theorem NormLevel.eval_le {ρ : List Nat} {l : NormLevel} {x : Nat} :
    l.eval ρ ≤ x ↔
      ∀ p n, l.find? p = some n → evalPath ρ p (n.eval ρ) ≤ x := by
  rw [NormLevel.eval, Batteries.RBMap.foldl_eq_foldl_toList, foldl_max_le]
  simp only [Nat.zero_le, true_and]
  constructor
  · intro H p n hf
    obtain ⟨y, hy, hcmp⟩ := Batteries.RBMap.find?_some_mem_toList hf
    cases Std.LawfulEqCmp.eq_of_compare hcmp
    exact H (p, n) hy
  · intro H pn hpn
    exact H pn.1 pn.2
      (Batteries.RBMap.find?_some.mpr ⟨pn.1, hpn, Std.ReflCmp.compare_self⟩)

theorem NormLevel.le_eval {ρ : List Nat} {l : NormLevel} {p : Path}
    {n : NormNode} (h : l.find? p = some n) :
    evalPath ρ p (n.eval ρ) ≤ l.eval ρ :=
  NormLevel.eval_le.mp (Nat.le_refl _) p n h

theorem mem_orderedInsert {a x : UInt64} :
    ∀ {p q : Path}, orderedInsert a p = some q → (x ∈ q ↔ x = a ∨ x ∈ p)
  | [], _, h => by cases h; simp
  | b :: bs, q, h => by
    rw [orderedInsert] at h
    split at h
    · cases h; simp [List.mem_cons]
    · split at h
      · simp at h
      · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [List.mem_cons, mem_orderedInsert hq']
        grind

/-- `isSubset` is sound for membership (this direction needs no
    sortedness). -/
theorem isSubset_mem :
    ∀ {p q : Path}, isSubset p q = true → ∀ x ∈ p, x ∈ q
  | [], _, _, x, hx => absurd hx (List.not_mem_nil)
  | _ :: _, [], h, _, _ => by simp [isSubset] at h
  | a :: as, b :: bs, h, x, hx => by
    rw [isSubset] at h
    by_cases hlt : b < a
    · rw [if_pos hlt] at h
      exact List.mem_cons_of_mem b (isSubset_mem h x hx)
    · rw [if_neg hlt] at h
      by_cases heq : (b == a) = true
      · rw [if_pos heq] at h
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact List.mem_cons.mpr (.inl (eq_of_beq heq).symm)
        · exact List.mem_cons_of_mem b (isSubset_mem h x hx')
      · rw [if_neg heq] at h
        simp at h
  termination_by p q => q.length + p.length

theorem allNZ_of_isSubset {ρ : List Nat} {p q : Path}
    (h : isSubset p q = true) (hq : allNZ ρ q = true) :
    allNZ ρ p = true := by
  rw [allNZ, List.all_eq_true] at hq ⊢
  exact fun x hx => hq x (isSubset_mem h x hx)

/-! #### Insert-eval lemmas -/

private theorem toNat_max (a b : UInt64) :
    (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = max a.toNat b.toNat
  rw [Nat.max_def]
  split <;> split <;>
    first
      | rfl
      | (rename_i h1 h2
         exact absurd (UInt64.le_iff_toNat_le.mp h1) h2)
      | (rename_i h1 h2
         exact absurd h2 fun hh => h1 (UInt64.le_iff_toNat_le.mpr hh))

private theorem forall_mem_set {α : Type _} {l : List α} {i : Nat}
    (hi : i < l.length) {b : α} {P : α → Prop} :
    (∀ a ∈ l.set i b, P a) ↔
      P b ∧ ∀ j (hj : j < l.length), j ≠ i → P l[j] := by
  constructor
  · intro H
    refine ⟨H b (List.mem_set hi b), fun j hj hne => ?_⟩
    have hj' : j < (l.set i b).length := by simpa using hj
    have := H _ (List.getElem_mem hj')
    rwa [List.getElem_set, if_neg fun h => hne h.symm] at this
  · rintro ⟨hb, hrest⟩ a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    rw [List.getElem_set]
    split
    · exact hb
    · rename_i hne
      exact hrest j (by simpa using hj) fun h => hne h.symm

theorem NormNode.addVar_eval {ρ : List Nat} {n : NormNode} {idx k : UInt64} :
    (n.addVar idx k).eval ρ = max (n.eval ρ) (evalParam ρ idx + k.toNat) := by
  have ext : ∀ x, ((n.addVar idx k).eval ρ ≤ x ↔
      max (n.eval ρ) (evalParam ρ idx + k.toNat) ≤ x) := by
    intro x
    rw [Nat.max_le, NormNode.eval_le, NormNode.eval_le]
    simp only [NormNode.addVar]
    split
    · rename_i p hfind
      obtain ⟨hp, hple, hmin⟩ :=
        Array.findIdx?_eq_some_iff_getElem.mp hfind
      have hbang : n.vars[p]! = n.vars[p] := getElem!_pos ..
      rw [hbang]
      split
      · rename_i hidx
        have hidx' : n.vars[p].idx = idx := eq_of_beq hidx
        have hp' : p < n.vars.toList.length := by simpa using hp
        have hEe : ∀ y : Nat,
            VarNode.eval ρ { n.vars[p] with offset := max n.vars[p].offset k } ≤ y
              ↔ n.vars[p].eval ρ ≤ y ∧ evalParam ρ idx + k.toNat ≤ y := by
          intro y
          show evalParam ρ (n.vars[p]).idx + (max (n.vars[p]).offset k).toNat ≤ y
              ↔ evalParam ρ (n.vars[p]).idx + (n.vars[p]).offset.toNat ≤ y
                ∧ evalParam ρ idx + k.toNat ≤ y
          rw [hidx', toNat_max, ← Nat.add_max_add_left, Nat.max_le]
        have hsplit : (∀ v' ∈ n.vars.toList, VarNode.eval ρ v' ≤ x) ↔
            n.vars[p].eval ρ ≤ x ∧
              ∀ j (hj : j < n.vars.toList.length), j ≠ p →
                VarNode.eval ρ n.vars.toList[j] ≤ x := by
          constructor
          · intro H
            exact ⟨Array.getElem_toList hp ▸ H _ (List.getElem_mem hp'),
              fun j hj _ => H _ (List.getElem_mem hj)⟩
          · rintro ⟨hpe, hrest⟩ v' hv'
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv'
            by_cases hje : j = p
            · subst hje
              exact (Array.getElem_toList (by simpa using hj)).symm ▸ hpe
            · exact hrest j hj hje
        simp only [← Array.mem_toList_iff, Array.set!_eq_setIfInBounds,
          Array.toList_setIfInBounds]
        rw [forall_mem_set hp', hEe, hsplit]
        constructor
        · rintro ⟨hc, ⟨hpe, hnew⟩, hrest⟩
          exact ⟨⟨hc, hpe, hrest⟩, hnew⟩
        · rintro ⟨⟨hc, hpe, hrest⟩, hnew⟩
          exact ⟨hc, ⟨hpe, hnew⟩, hrest⟩
      · rename_i hidx
        have hple' : p ≤ n.vars.toList.length := by simpa using Nat.le_of_lt hp
        have hins : (n.vars.insertIdx! p ⟨idx, k⟩).toList
            = n.vars.toList.insertIdx p ⟨idx, k⟩ := by
          unfold Array.insertIdx!
          split
          all_goals first
            | exact Array.toList_insertIdx _
            | (exfalso; omega)
        simp only [← Array.mem_toList_iff, hins]
        constructor
        · rintro ⟨hc, H⟩
          have hnew := H _ ((List.mem_insertIdx hple').mpr (.inl rfl))
          refine ⟨⟨hc, fun v hv => H _ ((List.mem_insertIdx hple').mpr (.inr ?_))⟩,
            by simpa [VarNode.eval] using hnew⟩
          simpa using hv
        · rintro ⟨⟨hc, hold⟩, hnew⟩
          refine ⟨hc, fun v hv => ?_⟩
          rcases (List.mem_insertIdx hple').mp hv with rfl | hv'
          · simpa [VarNode.eval] using hnew
          · exact hold _ (by simpa using hv')
    · rename_i hfind
      simp only [← Array.mem_toList_iff, Array.toList_push,
        List.forall_mem_append, List.forall_mem_singleton]
      constructor
      · rintro ⟨hc, hold, hnew⟩
        exact ⟨⟨hc, hold⟩, by simpa [VarNode.eval] using hnew⟩
      · rintro ⟨⟨hc, hold⟩, hnew⟩
        exact ⟨hc, hold, by simpa [VarNode.eval] using hnew⟩
  exact Nat.le_antisymm ((ext _).mpr (Nat.le_refl _)) ((ext _).mp (Nat.le_refl _))

theorem NormLevel.addVar_eval {ρ : List Nat} {l : NormLevel}
    {idx k : UInt64} {path : Path} :
    (l.addVar idx k path).eval ρ
      = max (l.eval ρ) (evalPath ρ path (evalParam ρ idx + k.toNat)) := by
  sorry

/-- `addConst` skips `k = 0` (neutral) and `k = 1` on nonempty paths —
    sound because an active nonempty path already contributes ≥ 1 (the
    `EvalPaths` invariant). -/
theorem NormLevel.addConst_eval {ρ : List Nat} {l : NormLevel} {k : UInt64}
    {path : Path} (hp : EvalPaths ρ path (l.eval ρ)) :
    (l.addConst k path).eval ρ
      = max (l.eval ρ) (evalPath ρ path k.toNat) := by
  sorry

/-! #### The keystone: normalization preserves the denotation -/

mutual

theorem normalizeAux_eval {ρ : List Nat} {l : KUniv m} {path : Path}
    {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + l.size < UInt64.size)
    (hc : (acc.find? path).isSome)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeAux l path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path ((KUniv.toVLevel l).eval ρ + k.toNat)) := by
  sorry

theorem normalizeImaxMax_eval {ρ : List Nat} {u v w : KUniv m} {path : Path}
    {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + (u.size + v.size + w.size) < UInt64.size)
    (hc : (acc.find? path).isSome)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeImaxMax u v w path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            ((VLevel.imax u.toVLevel (VLevel.max v.toVLevel w.toVLevel)).eval ρ
              + k.toNat)) := by
  sorry

theorem normalizeImaxImax_eval {ρ : List Nat} {u v w : KUniv m} {path : Path}
    {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + (u.size + v.size + w.size) < UInt64.size)
    (hc : (acc.find? path).isSome)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeImaxImax u v w path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            ((VLevel.imax u.toVLevel (VLevel.imax v.toVLevel w.toVLevel)).eval ρ
              + k.toNat)) := by
  sorry

theorem normalizeImaxDispatch_eval {ρ : List Nat} {a b : KUniv m}
    {path : Path} {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + (a.size + b.size) < UInt64.size)
    (hc : (acc.find? path).isSome)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeImaxDispatch a b path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            ((VLevel.imax a.toVLevel b.toVLevel).eval ρ + k.toNat)) := by
  sorry

end

/-- **Fresh** (upstream's live sorry, lean4lean `Verify/Level.lean:545`):
    the subsumption pass drops only dominated contributions. -/
theorem subsumption_eval {ρ : List Nat} {l : NormLevel} :
    NormLevel.eval ρ (subsumption l) = NormLevel.eval ρ l := by
  sorry

theorem seed_eval {ρ : List Nat} :
    NormLevel.eval ρ ((∅ : NormLevel).insert [] {}) = 0 := by
  refine Nat.le_antisymm (NormLevel.eval_le.mpr fun p n hf => ?_) (Nat.zero_le _)
  rw [Batteries.RBMap.find?_insert] at hf
  split at hf
  · rename_i hcmp
    cases Std.LawfulEqCmp.eq_of_compare hcmp
    cases hf
    simp [evalPath, allNZ, NormNode.eval]
  · obtain ⟨y, hy, -⟩ := Batteries.RBMap.find?_some_mem_toList hf
    simp at hy

/-- Normalization computes the `VLevel` denotation. -/
theorem normalizeLevel_eval {ρ : List Nat} {u : KUniv m}
    (hu : u.size < UInt64.size) :
    NormLevel.eval ρ (normalizeLevel u) = (KUniv.toVLevel u).eval ρ := by
  have hseed : (((∅ : NormLevel).insert [] {}).find? ([] : Path)).isSome := by
    rw [Batteries.RBMap.find?_insert_of_eq _ (by rfl)]; rfl
  rw [normalizeLevel, subsumption_eval,
    normalizeAux_eval (by simpa using hu) hseed (seed_eval ▸ .nil), seed_eval]
  simp [evalPath, allNZ]

/-! #### Canonical-form comparison soundness -/

/-- `normLevelEq` on canonical forms implies equal denotations. -/
theorem normLevelEq_eval {ρ : List Nat} {l₁ l₂ : NormLevel}
    (h : normLevelEq l₁ l₂ = true) :
    NormLevel.eval ρ l₁ = NormLevel.eval ρ l₂ := by
  sorry

/-- The coverage argument (level.rs:634-643, no upstream counterpart):
    `normLevelLe` on canonical forms implies `≤` on denotations. -/
theorem normLevelLe_eval {ρ : List Nat} {l₁ l₂ : NormLevel}
    (h : normLevelLe l₁ l₂ = true) :
    NormLevel.eval ρ l₁ ≤ NormLevel.eval ρ l₂ := by
  sorry

end Level

/-! ### The canonical-form frontier, assembled -/

/-- Canonical-form equality is semantically sound. -/
theorem normLevelEq_sound {u v : KUniv m}
    (hu : u.size < UInt64.size) (hv : v.size < UInt64.size)
    (h : Level.normLevelEq (Level.normalizeLevel u) (Level.normalizeLevel v)
       = true) :
    u.toVLevel ≈ v.toVLevel := by
  refine VLevel.equiv_def.mpr fun ρ => ?_
  rw [← Level.normalizeLevel_eval (ρ := ρ) hu,
    ← Level.normalizeLevel_eval (ρ := ρ) hv]
  exact Level.normLevelEq_eval h

/-- Canonical-form `≤` is semantically sound (the `normLevelLe` theorem —
    new mathematics; the independent coverage search is deliberately more
    complete than upstream's single-witness `le`). -/
theorem normLevelLe_sound {u v : KUniv m}
    (hu : u.size < UInt64.size) (hv : v.size < UInt64.size)
    (h : Level.normLevelLe (Level.normalizeLevel u) (Level.normalizeLevel v)
       = true) :
    u.toVLevel ≤ v.toVLevel := by
  intro ρ
  rw [← Level.normalizeLevel_eval (ρ := ρ) hu,
    ← Level.normalizeLevel_eval (ρ := ρ) hv]
  exact Level.normLevelLe_eval h

/-- **Soundness of `univEq`** (headline, Level slice): if the kernel's
    universe-equality decision procedure accepts, the translations are
    semantically equal under every parameter assignment. Conditional on
    addr-faithfulness of the compared pair (the `u == v` fast path at
    Ix/Tc/Level.lean:426 — discharged through the `CollisionFree` pilot)
    and the UInt64 no-wrap size bounds. -/
theorem univEq_sound {u v : KUniv m} (hinj : u.AddrFaithful v)
    (hu : u.size < UInt64.size) (hv : v.size < UInt64.size)
    (h : univEq u v = true) : u.toVLevel ≈ v.toVLevel := by
  rw [univEq, Bool.or_eq_true, KUniv.beq_def] at h
  rcases h with haddr | hnorm
  · rw [hinj.toVLevel_eq haddr]
    exact VLevel.equiv_def'.mpr rfl
  · exact normLevelEq_sound hu hv hnorm

/-- **Soundness of `univGeq`** (headline, Level slice): if the kernel
    accepts `u ≥ v`, then `⟦v⟧ρ ≤ ⟦u⟧ρ` for every assignment. All three
    disjuncts of Ix/Tc/Level.lean:430 discharged: the addr fast path via
    addr-faithfulness, `v.isZero` via `VLevel.zero_le`, and the canonical
    order via `normLevelLe_sound`. -/
theorem univGeq_sound {u v : KUniv m} (hinj : u.AddrFaithful v)
    (hu : u.size < UInt64.size) (hv : v.size < UInt64.size)
    (h : univGeq u v = true) : v.toVLevel ≤ u.toVLevel := by
  rw [univGeq, Bool.or_eq_true, Bool.or_eq_true, KUniv.beq_def] at h
  rcases h with (haddr | hzero) | hle
  · rw [hinj.toVLevel_eq haddr]; exact VLevel.le_refl _
  · rw [KUniv.toVLevel_of_isZero hzero]; exact VLevel.zero_le
  · exact normLevelLe_sound hv hu hle

end Ix.Tc
