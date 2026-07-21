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

Status: the slice is **sorry-free** — the full chain `univEq_sound` /
`univGeq_sound` ← `normalizeLevel_eval` ← the 4-way `normalizeAux_eval`
keystone + `subsumption_eval` (upstream's `Verify/Level.lean:545` is
still a live sorry there; proven here via the pure per-key model and a
lex (path length, constant-after-var) strong induction) is closed,
conditional only on addr-faithfulness and the UInt64 no-wrap bounds.
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

/-! #### Foundational lemmas (grind bottom-up) -/

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

theorem orderedInsert_none {a : UInt64} :
    ∀ {p : Path}, orderedInsert a p = none → a ∈ p
  | [], h => by simp [orderedInsert] at h
  | b :: bs, h => by
    rw [orderedInsert] at h
    split at h
    · simp at h
    · split at h
      · rename_i heq
        exact List.mem_cons.mpr (.inl (eq_of_beq heq))
      · exact List.mem_cons.mpr
          (.inr (orderedInsert_none (Option.map_eq_none_iff.mp h)))

theorem allNZ_orderedInsert {ρ : List Nat} {a : UInt64} {p q : Path}
    (h : orderedInsert a p = some q) :
    allNZ ρ q = true ↔ 0 < evalParam ρ a ∧ allNZ ρ p = true := by
  simp only [allNZ, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro H
    exact ⟨H a ((mem_orderedInsert h).mpr (.inl rfl)),
      fun x hx => H x ((mem_orderedInsert h).mpr (.inr hx))⟩
  · rintro ⟨ha, Hp⟩ x hx
    rcases (mem_orderedInsert h).mp hx with rfl | hx'
    · exact ha
    · exact Hp x hx'

theorem evalPath_mono {ρ : List Nat} {path : Path} {a b : Nat} (h : a ≤ b) :
    evalPath ρ path a ≤ evalPath ρ path b := by
  simp only [evalPath]
  split <;> simp [h]

/-- Growing the path by an ordered insert conditions the value on the new
    param too. -/
theorem evalPath_orderedInsert {ρ : List Nat} {a : UInt64} {p q : Path}
    (h : orderedInsert a p = some q) {n : Nat} :
    evalPath ρ q n = if 0 < evalParam ρ a then evalPath ρ p n else 0 := by
  simp only [evalPath]
  by_cases ha : 0 < evalParam ρ a
  · rw [if_pos ha]
    by_cases hp : allNZ ρ p = true
    · rw [if_pos ((allNZ_orderedInsert h).mpr ⟨ha, hp⟩), if_pos hp]
    · rw [if_neg fun hq => hp ((allNZ_orderedInsert h).mp hq).2, if_neg hp]
  · rw [if_neg ha, if_neg fun hq => ha ((allNZ_orderedInsert h).mp hq).1]

theorem EvalPaths.mono {ρ : List Nat} {path : Path} {n n' : Nat}
    (hle : n ≤ n') : EvalPaths ρ path n → EvalPaths ρ path n'
  | .nil => .nil
  | .insert h₁ h₂ h₃ => .insert h₁ (Nat.le_trans h₂ hle) (h₃.mono hle)

theorem EvalPaths.le_max {ρ : List Nat} {path : Path} {n m : Nat}
    (h : EvalPaths ρ path n) : EvalPaths ρ path (max n m) :=
  h.mono (Nat.le_max_left ..)

/-- Every param on an `EvalPaths`-built active chain is already accounted
    for in `n` — the invariant's payoff (justifies the `addConst` skip and
    the redundant-param fast path). -/
theorem EvalPaths.mem_le {ρ : List Nat} {x : UInt64} :
    ∀ {path : Path} {n : Nat}, EvalPaths ρ path n → x ∈ path →
      allNZ ρ path = true → evalParam ρ x ≤ n
  | _, _, .nil, hx, _ => absurd hx (List.not_mem_nil)
  | _, _, .insert (a := a) (path := pre) h₁ h₂ h₃, hx, hnz => by
    have hnzpre : allNZ ρ pre = true := by
      simp only [allNZ, List.all_eq_true] at hnz ⊢
      exact fun y hy => hnz y ((mem_orderedInsert h₁).mpr (.inr hy))
    rcases (mem_orderedInsert h₁).mp hx with rfl | hx'
    · have heq : evalPath ρ pre (evalParam ρ x) = evalParam ρ x := by
        simp [evalPath, hnzpre]
      exact heq ▸ h₂
    · exact h₃.mem_le hx' hnzpre

/-- An active nonempty chain contributes at least 1 (justifies `addConst`
    skipping `k = 1` on nonempty paths). -/
theorem EvalPaths.one_le {ρ : List Nat} {path : Path} {n : Nat}
    (h : EvalPaths ρ path n) (hne : path ≠ []) (hnz : allNZ ρ path = true) :
    1 ≤ n := by
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha : a ∈ a :: rest := List.mem_cons_self ..
  have h1 : 0 < evalParam ρ a := by
    simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnz
    exact hnz a ha
  exact Nat.le_trans h1 (h.mem_le ha hnz)

/-- `imax` distributes over `max` in the second argument — the semantic
    content of the `normalizeImaxMax` rewrite. -/
private theorem imax_max (a b c : Nat) :
    Nat.imax a (max b c) = max (Nat.imax a b) (Nat.imax a c) := by
  by_cases hb : b = 0 <;> by_cases hc : c = 0 <;>
    simp [Nat.imax, hb, hc, Nat.max_eq_max, Nat.max_eq_zero_iff] <;> omega

/-- `imax(a, imax(b, c)) = max(imax(a, c), imax(b, c))` — the semantic
    content of the `normalizeImaxImax` rewrite. -/
private theorem imax_imax (a b c : Nat) :
    Nat.imax a (Nat.imax b c) = max (Nat.imax a c) (Nat.imax b c) := by
  by_cases hc : c = 0 <;> by_cases hb : b = 0 <;>
    simp [Nat.imax, hb, hc, Nat.max_eq_max, Nat.max_eq_zero_iff] <;> omega

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

/-- The `findD` default is harmless: the path-conditioned value of the
    node stored at `path` (or the empty node) never exceeds the map
    denotation. -/
private theorem findD_evalPath_le {ρ : List Nat} {l : NormLevel} {path : Path} :
    evalPath ρ path ((l.findD path {}).eval ρ) ≤ l.eval ρ := by
  rw [Batteries.RBMap.findD]
  cases hf : l.find? path with
  | some n => simpa using NormLevel.le_eval hf
  | none =>
    simp only [Option.getD_none]
    refine evalPath_le.mpr fun _ => NormNode.eval_le.mpr ⟨by simp, ?_⟩
    intro v hv
    simp at hv

/-- Upsert-eval: inserting at `path` a node whose value maxes the old
    (`findD`) node's value with a fresh contribution `c` grows the map
    denotation by exactly `evalPath path c`. Common core of
    `NormLevel.addVar_eval` and `NormLevel.addConst_eval`. -/
private theorem insert_findD_eval {ρ : List Nat} {l : NormLevel} {path : Path}
    {v' : NormNode} {c : Nat}
    (hv : v'.eval ρ = max ((l.findD path {}).eval ρ) c) :
    NormLevel.eval ρ (l.insert path v')
      = max (l.eval ρ) (evalPath ρ path c) := by
  have hfind : ∀ p, (l.insert path v').find? p
      = if compare p path = .eq then some v' else l.find? p := fun p => by
    rw [Batteries.RBMap.find?_insert]
  have ext : ∀ x, (NormLevel.eval ρ (l.insert path v') ≤ x ↔
      max (l.eval ρ) (evalPath ρ path c) ≤ x) := by
    intro x
    rw [Nat.max_le, NormLevel.eval_le, NormLevel.eval_le]
    constructor
    · intro H
      have hpath : evalPath ρ path (v'.eval ρ) ≤ x :=
        H path _ (by rw [hfind, if_pos Std.ReflCmp.compare_self])
      rw [hv, evalPath_max, Nat.max_le] at hpath
      refine ⟨fun p n hf => ?_, hpath.2⟩
      by_cases hcmp : compare p path = .eq
      · cases Std.LawfulEqCmp.eq_of_compare hcmp
        have hD : l.findD path {} = n := by
          rw [Batteries.RBMap.findD, hf, Option.getD_some]
        rw [← hD]
        exact hpath.1
      · exact H p n (by rw [hfind, if_neg hcmp]; exact hf)
    · rintro ⟨hl, hnew⟩ p n hf
      rw [hfind] at hf
      split at hf
      · rename_i hcmp
        cases Std.LawfulEqCmp.eq_of_compare hcmp
        cases hf
        rw [hv, evalPath_max, Nat.max_le]
        exact ⟨Nat.le_trans findD_evalPath_le (NormLevel.eval_le.mpr hl), hnew⟩
      · exact hl p n hf
  exact Nat.le_antisymm ((ext _).mpr (Nat.le_refl _)) ((ext _).mp (Nat.le_refl _))

/-- Bumping the constant to `max constant k` maxes the node value with
    `k` (the vars are untouched). -/
private theorem NormNode.setConst_eval {ρ : List Nat} {n : NormNode}
    {k : UInt64} :
    NormNode.eval ρ { n with constant := max n.constant k }
      = max (n.eval ρ) k.toNat := by
  have ext : ∀ x, (NormNode.eval ρ { n with constant := max n.constant k } ≤ x
      ↔ max (n.eval ρ) k.toNat ≤ x) := by
    intro x
    rw [Nat.max_le, NormNode.eval_le, NormNode.eval_le]
    show (max n.constant k).toNat ≤ x ∧ (∀ v ∈ n.vars, VarNode.eval ρ v ≤ x)
      ↔ _
    rw [toNat_max, Nat.max_le]
    constructor
    · rintro ⟨⟨hc, hk⟩, hvars⟩
      exact ⟨⟨hc, hvars⟩, hk⟩
    · rintro ⟨⟨hc, hvars⟩, hk⟩
      exact ⟨⟨hc, hk⟩, hvars⟩
  exact Nat.le_antisymm ((ext _).mpr (Nat.le_refl _)) ((ext _).mp (Nat.le_refl _))

theorem NormLevel.addVar_eval {ρ : List Nat} {l : NormLevel}
    {idx k : UInt64} {path : Path} :
    (l.addVar idx k path).eval ρ
      = max (l.eval ρ) (evalPath ρ path (evalParam ρ idx + k.toNat)) := by
  rw [NormLevel.addVar]
  exact insert_findD_eval NormNode.addVar_eval

/-- `addConst` skips `k = 0` (neutral) and `k = 1` on nonempty paths —
    sound because an active nonempty path already contributes ≥ 1 (the
    `EvalPaths` invariant). -/
theorem NormLevel.addConst_eval {ρ : List Nat} {l : NormLevel} {k : UInt64}
    {path : Path} (hp : EvalPaths ρ path (l.eval ρ)) :
    (l.addConst k path).eval ρ
      = max (l.eval ρ) (evalPath ρ path k.toNat) := by
  rw [NormLevel.addConst]
  split
  · rename_i hskip
    rw [Bool.or_eq_true, Bool.and_eq_true] at hskip
    rcases hskip with h0 | ⟨h1, hne⟩
    · have h0' : k.toNat = 0 := by rw [eq_of_beq h0]; decide
      rw [h0']
      refine (Nat.max_eq_left ?_).symm
      exact evalPath_le.mpr fun _ => Nat.zero_le _
    · have h1' : k.toNat = 1 := by rw [eq_of_beq h1]; decide
      have hne' : path ≠ [] := by
        cases path
        · simp at hne
        · simp
      rw [h1']
      refine (Nat.max_eq_left ?_).symm
      exact evalPath_le.mpr fun hnz => hp.one_le hne' hnz
  · exact insert_findD_eval NormNode.setConst_eval

/-! #### The keystone: normalization preserves the denotation -/

/-- `succ` ticks the accumulator without wrapping — this is exactly where
    the `UInt64.size` side conditions earn their keep. -/
private theorem toNat_add_one {k : UInt64} (h : k.toNat + 1 < UInt64.size) :
    (k + 1).toNat = k.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from by decide]
  exact Nat.mod_eq_of_lt h

/-- Extensionality along `≤` (upstream's `ext_le`): the uniform closer for
    max-tree equations — shatter both sides with `Nat.max_le`, hand the
    linear atoms to `omega`. -/
private theorem ext_le {n m : Nat} (H : ∀ x, n ≤ x ↔ m ≤ x) : n = m :=
  Nat.le_antisymm ((H _).mpr (Nat.le_refl _)) ((H _).mp (Nat.le_refl _))

mutual

private theorem normalizeAux_eval' {ρ : List Nat} :
    ∀ (l : KUniv m) (path : Path) (k : UInt64) (acc : NormLevel),
      k.toNat + l.size < UInt64.size →
      EvalPaths ρ path (NormLevel.eval ρ acc) →
      NormLevel.eval ρ (normalizeAux l path k acc)
        = max (NormLevel.eval ρ acc)
            (evalPath ρ path ((KUniv.toVLevel l).eval ρ + k.toNat))
  | .zero ad, path, k, acc, hk, hp => by
    simp only [normalizeAux]
    rw [NormLevel.addConst_eval hp]
    simp [KUniv.toVLevel, VLevel.eval]
  | .succ inner ad, path, k, acc, hk, hp => by
    have hk1 : (k + 1).toNat = k.toNat + 1 :=
      toNat_add_one (by simp [KUniv.size] at hk; omega)
    simp only [normalizeAux]
    rw [normalizeAux_eval' inner path (k + 1) acc
        (by rw [hk1]; simp [KUniv.size] at hk; omega) hp,
      hk1,
      show (KUniv.toVLevel (.succ inner ad)).eval ρ
          = (KUniv.toVLevel inner).eval ρ + 1 from rfl,
      show (KUniv.toVLevel inner).eval ρ + (k.toNat + 1)
          = (KUniv.toVLevel inner).eval ρ + 1 + k.toNat from by omega]
  | .max a b ad, path, k, acc, hk, hp => by
    have hka : k.toNat + a.size < UInt64.size := by
      simp [KUniv.size] at hk; omega
    have hkb : k.toNat + b.size < UInt64.size := by
      simp [KUniv.size] at hk; omega
    have ihA := normalizeAux_eval' a path k acc hka hp
    have hmono : NormLevel.eval ρ acc
        ≤ NormLevel.eval ρ (normalizeAux a path k acc) := by
      rw [ihA]; exact Nat.le_max_left ..
    have ihB := normalizeAux_eval' b path k (normalizeAux a path k acc) hkb
      (hp.mono hmono)
    simp only [normalizeAux]
    rw [ihB, ihA,
      show (KUniv.toVLevel (.max a b ad)).eval ρ
          = max ((KUniv.toVLevel a).eval ρ) ((KUniv.toVLevel b).eval ρ)
        from rfl,
      ← Nat.add_max_add_right, evalPath_max]
    refine ext_le fun x => ?_
    simp only [Nat.max_le]
    omega
  | .imax u (.zero b_ad) ad, path, k, acc, hk, hp => by
    simp only [normalizeAux]
    rw [NormLevel.addConst_eval hp]
    simp [KUniv.toVLevel, VLevel.eval, Nat.imax]
  | .imax u (.succ v b_ad) ad, path, k, acc, hk, hp => by
    have hk1 : (k + 1).toNat = k.toNat + 1 :=
      toNat_add_one (by simp [KUniv.size] at hk; omega)
    have hku : k.toNat + u.size < UInt64.size := by
      simp [KUniv.size] at hk; omega
    have hkv : (k + 1).toNat + v.size < UInt64.size := by
      rw [hk1]; simp [KUniv.size] at hk; omega
    have ihU := normalizeAux_eval' u path k acc hku hp
    have hmono : NormLevel.eval ρ acc
        ≤ NormLevel.eval ρ (normalizeAux u path k acc) := by
      rw [ihU]; exact Nat.le_max_left ..
    have ihV := normalizeAux_eval' v path (k + 1) (normalizeAux u path k acc)
      hkv (hp.mono hmono)
    simp only [normalizeAux]
    rw [ihV, ihU, hk1,
      show (KUniv.toVLevel (.imax u (.succ v b_ad) ad)).eval ρ
          = Nat.imax ((KUniv.toVLevel u).eval ρ)
              ((KUniv.toVLevel v).eval ρ + 1) from rfl,
      show Nat.imax ((KUniv.toVLevel u).eval ρ)
            ((KUniv.toVLevel v).eval ρ + 1)
          = max ((KUniv.toVLevel u).eval ρ)
              ((KUniv.toVLevel v).eval ρ + 1) from by
        simp [Nat.imax, Nat.max_eq_max],
      show (KUniv.toVLevel v).eval ρ + (k.toNat + 1)
          = (KUniv.toVLevel v).eval ρ + 1 + k.toNat from by omega,
      ← Nat.add_max_add_right, evalPath_max]
    refine ext_le fun x => ?_
    simp only [Nat.max_le]
    omega
  | .imax u (.max v w b_ad) ad, path, k, acc, hk, hp => by
    simp only [normalizeAux]
    exact normalizeImaxMax_eval (by simp [KUniv.size] at hk; omega) hp
  | .imax u (.imax v w b_ad) ad, path, k, acc, hk, hp => by
    simp only [normalizeAux]
    exact normalizeImaxImax_eval (by simp [KUniv.size] at hk; omega) hp
  | .imax u (.param idx nm b_ad) ad, path, k, acc, hk, hp => by
    cases h₁ : orderedInsert idx path with
    | some newPath =>
      simp only [normalizeAux, h₁]
      exact normalize_param_some_eval h₁
        (by simp [KUniv.size] at hk; omega) hp
    | none =>
      simp only [normalizeAux, h₁]
      exact normalize_param_none_eval h₁
        (by simp [KUniv.size] at hk; omega) hp
  | .param idx nm ad, path, k, acc, hk, hp => by
    have hev : (KUniv.toVLevel (.param idx nm ad)).eval ρ
        = evalParam ρ idx := rfl
    rw [hev]
    cases h₁ : orderedInsert idx path with
    | some newPath =>
      simp only [normalizeAux, h₁]
      rw [NormLevel.addVar_eval, NormLevel.addConst_eval hp,
        evalPath_orderedInsert h₁]
      by_cases hz : 0 < evalParam ρ idx
      · rw [if_pos hz]
        by_cases hnz : allNZ ρ path = true
        · simp only [evalPath, if_pos hnz]
          refine ext_le fun x => ?_
          simp only [Nat.max_le]
          omega
        · simp only [evalPath, if_neg hnz]
          refine ext_le fun x => ?_
          simp only [Nat.max_le]
          omega
      · rw [if_neg hz, Nat.eq_zero_of_not_pos hz]
        by_cases hnz : allNZ ρ path = true
        · simp only [evalPath, if_pos hnz, Nat.zero_add]
          refine ext_le fun x => ?_
          simp only [Nat.max_le]
          omega
        · simp only [evalPath, if_neg hnz]
          refine ext_le fun x => ?_
          simp only [Nat.max_le]
          omega
    | none =>
      have hmem : idx ∈ path := orderedInsert_none h₁
      simp only [normalizeAux, h₁]
      split
      · rw [NormLevel.addVar_eval]
      · rename_i hk0
        have hkz : k = 0 := by simpa using hk0
        subst hkz
        rw [show (0 : UInt64).toNat = 0 from by decide, Nat.add_zero]
        by_cases hnz : allNZ ρ path = true
        · have hle : evalParam ρ idx ≤ NormLevel.eval ρ acc :=
            hp.mem_le hmem hnz
          simp only [evalPath, if_pos hnz]
          refine ext_le fun x => ?_
          simp only [Nat.max_le]
          omega
        · simp only [evalPath, if_neg hnz]
          refine ext_le fun x => ?_
          simp only [Nat.max_le]
          omega
termination_by l _ _ _ _ _ => 3 * l.size
decreasing_by
  all_goals try simp [KUniv.size]
  all_goals omega

theorem normalizeImaxMax_eval {ρ : List Nat} {u v w : KUniv m} {path : Path}
    {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + (u.size + v.size + w.size) < UInt64.size)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeImaxMax u v w path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            ((VLevel.imax u.toVLevel (VLevel.max v.toVLevel w.toVLevel)).eval ρ
              + k.toNat)) := by
  have hkuv : k.toNat + (u.size + v.size) < UInt64.size := by omega
  have hkuw : k.toNat + (u.size + w.size) < UInt64.size := by omega
  have ihV := normalizeImaxDispatch_eval' u v path k acc hkuv hp
  have hmono : NormLevel.eval ρ acc
      ≤ NormLevel.eval ρ (normalizeImaxDispatch u v path k acc) := by
    rw [ihV]; exact Nat.le_max_left ..
  have ihW := normalizeImaxDispatch_eval' u w path k
    (normalizeImaxDispatch u v path k acc) hkuw (hp.mono hmono)
  simp only [normalizeImaxMax]
  rw [ihW, ihV,
    show (VLevel.imax u.toVLevel (VLevel.max v.toVLevel w.toVLevel)).eval ρ
        = Nat.imax ((KUniv.toVLevel u).eval ρ)
            (max ((KUniv.toVLevel v).eval ρ) ((KUniv.toVLevel w).eval ρ))
      from rfl,
    imax_max, ← Nat.add_max_add_right, evalPath_max,
    show (VLevel.imax u.toVLevel v.toVLevel).eval ρ
        = Nat.imax ((KUniv.toVLevel u).eval ρ) ((KUniv.toVLevel v).eval ρ)
      from rfl,
    show (VLevel.imax u.toVLevel w.toVLevel).eval ρ
        = Nat.imax ((KUniv.toVLevel u).eval ρ) ((KUniv.toVLevel w).eval ρ)
      from rfl]
  refine ext_le fun x => ?_
  simp only [Nat.max_le]
  omega
termination_by 3 * (u.size + v.size + w.size) + 1
decreasing_by
  all_goals have hv := KUniv.size_pos v
  all_goals have hw := KUniv.size_pos w
  all_goals omega

theorem normalizeImaxImax_eval {ρ : List Nat} {u v w : KUniv m} {path : Path}
    {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + (u.size + v.size + w.size) < UInt64.size)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeImaxImax u v w path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            ((VLevel.imax u.toVLevel (VLevel.imax v.toVLevel w.toVLevel)).eval ρ
              + k.toNat)) := by
  have hkuw : k.toNat + (u.size + w.size) < UInt64.size := by omega
  have hkvw : k.toNat + (v.size + w.size) < UInt64.size := by omega
  have ihUW := normalizeImaxDispatch_eval' u w path k acc hkuw hp
  have hmono : NormLevel.eval ρ acc
      ≤ NormLevel.eval ρ (normalizeImaxDispatch u w path k acc) := by
    rw [ihUW]; exact Nat.le_max_left ..
  have ihVW := normalizeImaxDispatch_eval' v w path k
    (normalizeImaxDispatch u w path k acc) hkvw (hp.mono hmono)
  simp only [normalizeImaxImax]
  rw [ihVW, ihUW,
    show (VLevel.imax u.toVLevel (VLevel.imax v.toVLevel w.toVLevel)).eval ρ
        = Nat.imax ((KUniv.toVLevel u).eval ρ)
            (Nat.imax ((KUniv.toVLevel v).eval ρ) ((KUniv.toVLevel w).eval ρ))
      from rfl,
    imax_imax, ← Nat.add_max_add_right, evalPath_max,
    show (VLevel.imax u.toVLevel w.toVLevel).eval ρ
        = Nat.imax ((KUniv.toVLevel u).eval ρ) ((KUniv.toVLevel w).eval ρ)
      from rfl,
    show (VLevel.imax v.toVLevel w.toVLevel).eval ρ
        = Nat.imax ((KUniv.toVLevel v).eval ρ) ((KUniv.toVLevel w).eval ρ)
      from rfl]
  refine ext_le fun x => ?_
  simp only [Nat.max_le]
  omega
termination_by 3 * (u.size + v.size + w.size) + 1
decreasing_by
  all_goals have hu := KUniv.size_pos u
  all_goals have hv := KUniv.size_pos v
  all_goals omega

private theorem normalizeImaxDispatch_eval' {ρ : List Nat} :
    ∀ (a b : KUniv m) (path : Path) (k : UInt64) (acc : NormLevel),
      k.toNat + (a.size + b.size) < UInt64.size →
      EvalPaths ρ path (NormLevel.eval ρ acc) →
      NormLevel.eval ρ (normalizeImaxDispatch a b path k acc)
        = max (NormLevel.eval ρ acc)
            (evalPath ρ path
              ((VLevel.imax a.toVLevel b.toVLevel).eval ρ + k.toNat))
  | a, .zero b_ad, path, k, acc, hk, hp => by
    simp only [normalizeImaxDispatch]
    rw [NormLevel.addConst_eval hp]
    simp [KUniv.toVLevel, VLevel.eval, Nat.imax]
  | a, .succ v b_ad, path, k, acc, hk, hp => by
    have hsza := KUniv.size_pos a
    have hk1 : (k + 1).toNat = k.toNat + 1 :=
      toNat_add_one (by simp [KUniv.size] at hk; omega)
    have hka : k.toNat + a.size < UInt64.size := by
      simp [KUniv.size] at hk; omega
    have hkv : (k + 1).toNat + v.size < UInt64.size := by
      rw [hk1]; simp [KUniv.size] at hk; omega
    have ihA := normalizeAux_eval' a path k acc hka hp
    have hmono : NormLevel.eval ρ acc
        ≤ NormLevel.eval ρ (normalizeAux a path k acc) := by
      rw [ihA]; exact Nat.le_max_left ..
    have ihV := normalizeAux_eval' v path (k + 1) (normalizeAux a path k acc)
      hkv (hp.mono hmono)
    simp only [normalizeImaxDispatch]
    rw [ihV, ihA, hk1,
      show (VLevel.imax a.toVLevel (KUniv.toVLevel (.succ v b_ad))).eval ρ
          = Nat.imax ((KUniv.toVLevel a).eval ρ)
              ((KUniv.toVLevel v).eval ρ + 1) from rfl,
      show Nat.imax ((KUniv.toVLevel a).eval ρ)
            ((KUniv.toVLevel v).eval ρ + 1)
          = max ((KUniv.toVLevel a).eval ρ)
              ((KUniv.toVLevel v).eval ρ + 1) from by
        simp [Nat.imax, Nat.max_eq_max],
      show (KUniv.toVLevel v).eval ρ + (k.toNat + 1)
          = (KUniv.toVLevel v).eval ρ + 1 + k.toNat from by omega,
      ← Nat.add_max_add_right, evalPath_max]
    refine ext_le fun x => ?_
    simp only [Nat.max_le]
    omega
  | a, .max v w b_ad, path, k, acc, hk, hp => by
    simp only [normalizeImaxDispatch]
    exact normalizeImaxMax_eval (by simp [KUniv.size] at hk; omega) hp
  | a, .imax v w b_ad, path, k, acc, hk, hp => by
    simp only [normalizeImaxDispatch]
    exact normalizeImaxImax_eval (by simp [KUniv.size] at hk; omega) hp
  | a, .param idx nm b_ad, path, k, acc, hk, hp => by
    cases h₁ : orderedInsert idx path with
    | some newPath =>
      simp only [normalizeImaxDispatch, h₁]
      exact normalize_param_some_eval h₁
        (by simp [KUniv.size] at hk; omega) hp
    | none =>
      simp only [normalizeImaxDispatch, h₁]
      exact normalize_param_none_eval h₁
        (by simp [KUniv.size] at hk; omega) hp
termination_by a b _ _ _ _ _ => 3 * (a.size + b.size) + 2
decreasing_by
  all_goals try simp [KUniv.size]
  all_goals omega

/-- Shared `imax·param` continuation, `orderedInsert` hit: record the
    conditioned constant, seed the grown path with the param node, and
    normalize the conditioned side into the grown accumulator. Common to
    `normalizeAux` (`.imax u (.param idx)`) and `normalizeImaxDispatch`. -/
private theorem normalize_param_some_eval {ρ : List Nat} {u : KUniv m}
    {idx : UInt64} {path newPath : Path} {k : UInt64} {acc : NormLevel}
    (h₁ : orderedInsert idx path = some newPath)
    (hk : k.toNat + u.size + 1 < UInt64.size)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeAux u newPath k
        ((acc.addConst k path).addVar idx k newPath))
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            (Nat.imax ((KUniv.toVLevel u).eval ρ) (evalParam ρ idx)
              + k.toNat)) := by
  have hconst : NormLevel.eval ρ (acc.addConst k path)
      = max (NormLevel.eval ρ acc) (evalPath ρ path k.toNat) :=
    NormLevel.addConst_eval hp
  have hvar : NormLevel.eval ρ ((acc.addConst k path).addVar idx k newPath)
      = max (NormLevel.eval ρ (acc.addConst k path))
          (evalPath ρ newPath (evalParam ρ idx + k.toNat)) :=
    NormLevel.addVar_eval
  have hp₂ : EvalPaths ρ newPath
      (NormLevel.eval ρ ((acc.addConst k path).addVar idx k newPath)) := by
    refine .insert h₁ ?_ (hp.mono ?_)
    · rw [hvar]
      refine Nat.le_trans ?_ (Nat.le_max_right ..)
      rw [evalPath_orderedInsert h₁]
      by_cases hz : 0 < evalParam ρ idx
      · rw [if_pos hz]
        exact evalPath_mono (Nat.le_add_right ..)
      · rw [if_neg hz, Nat.eq_zero_of_not_pos hz]
        exact evalPath_le.mpr fun _ => Nat.le_refl _
    · rw [hvar, hconst]
      exact Nat.le_trans (Nat.le_max_left ..) (Nat.le_max_left ..)
  rw [normalizeAux_eval' u newPath k
      ((acc.addConst k path).addVar idx k newPath) (by omega) hp₂,
    hvar, hconst, evalPath_orderedInsert h₁, evalPath_orderedInsert h₁]
  by_cases hnz : allNZ ρ path = true <;> by_cases hz : 0 < evalParam ρ idx
  · rw [if_pos hz, if_pos hz]
    simp only [evalPath, if_pos hnz, Nat.imax,
      if_neg (Nat.pos_iff_ne_zero.mp hz), Nat.max_eq_max,
      ← Nat.add_max_add_right]
    refine ext_le fun x => ?_
    simp only [Nat.max_le]
    omega
  · rw [if_neg hz, if_neg hz, Nat.eq_zero_of_not_pos hz]
    simp only [evalPath, if_pos hnz, Nat.imax, reduceIte, Nat.zero_add]
    refine ext_le fun x => ?_
    simp only [Nat.max_le]
    omega
  · rw [if_pos hz, if_pos hz]
    simp only [evalPath, if_neg hnz]
    refine ext_le fun x => ?_
    simp only [Nat.max_le]
    omega
  · rw [if_neg hz, if_neg hz]
    simp only [evalPath, if_neg hnz]
    refine ext_le fun x => ?_
    simp only [Nat.max_le]
    omega
termination_by 3 * u.size + 1
decreasing_by all_goals omega

/-- Shared `imax·param` continuation, param already on the path: the chain
    pins it positive, so its contribution is either already dominated
    (`k = 0`, via `EvalPaths.mem_le`) or re-recorded at the same path. -/
private theorem normalize_param_none_eval {ρ : List Nat} {u : KUniv m}
    {idx : UInt64} {path : Path} {k : UInt64} {acc : NormLevel}
    (h₁ : orderedInsert idx path = none)
    (hk : k.toNat + u.size + 1 < UInt64.size)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeAux u path k
        (if k != 0 then acc.addVar idx k path else acc))
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            (Nat.imax ((KUniv.toVLevel u).eval ρ) (evalParam ρ idx)
              + k.toNat)) := by
  have hmem : idx ∈ path := orderedInsert_none h₁
  split
  · have hvar : NormLevel.eval ρ (acc.addVar idx k path)
        = max (NormLevel.eval ρ acc)
            (evalPath ρ path (evalParam ρ idx + k.toNat)) :=
      NormLevel.addVar_eval
    have hmono : NormLevel.eval ρ acc
        ≤ NormLevel.eval ρ (acc.addVar idx k path) := by
      rw [hvar]; exact Nat.le_max_left ..
    rw [normalizeAux_eval' u path k (acc.addVar idx k path) (by omega)
        (hp.mono hmono),
      hvar]
    by_cases hnz : allNZ ρ path = true
    · have hz : 0 < evalParam ρ idx := by
        simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnz
        exact hnz idx hmem
      simp only [evalPath, if_pos hnz, Nat.imax,
        if_neg (Nat.pos_iff_ne_zero.mp hz), Nat.max_eq_max,
        ← Nat.add_max_add_right]
      refine ext_le fun x => ?_
      simp only [Nat.max_le]
      omega
    · simp only [evalPath, if_neg hnz]
      refine ext_le fun x => ?_
      simp only [Nat.max_le]
      omega
  · rename_i hk0
    have hkz : k = 0 := by simpa using hk0
    subst hkz
    rw [normalizeAux_eval' u path 0 acc (by omega) hp]
    simp only [show (0 : UInt64).toNat = 0 from by decide, Nat.add_zero]
    by_cases hnz : allNZ ρ path = true
    · have hz : 0 < evalParam ρ idx := by
        simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnz
        exact hnz idx hmem
      have hle : evalParam ρ idx ≤ NormLevel.eval ρ acc :=
        hp.mem_le hmem hnz
      simp only [evalPath, if_pos hnz, Nat.imax,
        if_neg (Nat.pos_iff_ne_zero.mp hz), Nat.max_eq_max]
      refine ext_le fun x => ?_
      simp only [Nat.max_le]
      omega
    · simp only [evalPath, if_neg hnz]
termination_by 3 * u.size + 1
decreasing_by all_goals omega

end

/-- The keystone, public shape: normalization folds a level into the
    accumulator, growing the denotation by exactly the path-conditioned
    translated value (plus the pending succ offset). -/
theorem normalizeAux_eval {ρ : List Nat} {l : KUniv m} {path : Path}
    {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + l.size < UInt64.size)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeAux l path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path ((KUniv.toVLevel l).eval ρ + k.toNat)) :=
  normalizeAux_eval' l path k acc hk hp

theorem normalizeImaxDispatch_eval {ρ : List Nat} {a b : KUniv m}
    {path : Path} {k : UInt64} {acc : NormLevel}
    (hk : k.toNat + (a.size + b.size) < UInt64.size)
    (hp : EvalPaths ρ path (NormLevel.eval ρ acc)) :
    NormLevel.eval ρ (normalizeImaxDispatch a b path k acc)
      = max (NormLevel.eval ρ acc)
          (evalPath ρ path
            ((VLevel.imax a.toVLevel b.toVLevel).eval ρ + k.toNat)) :=
  normalizeImaxDispatch_eval' a b path k acc hk hp

/-! #### Subsumption: the pure model -/

/-- One inner-loop step of `subsumption`, as a pure function (same
    conditions and mutations as the loop body, `let`s and all — the
    commute proof below reduces both against each other). -/
def subsumeStep (p1 : Path) (n1 : NormNode) (p2 : Path) (n2 : NormNode) :
    NormNode :=
  if isSubset p2 p1 then
    let same := p1.length == p2.length
    let n1' := if n1.constant != 0 then
        (let maxVarOffset := n1.vars.foldl (fun acc v => max acc v.offset) 0
         let keepConst := (same || n1.constant > n2.constant)
           && (n2.vars.isEmpty || n1.constant > maxVarOffset + 1)
         if !keepConst then { n1 with constant := 0 } else n1)
      else n1
    if !same && !n2.vars.isEmpty then
      { n1' with vars := subsumeVars n1'.vars n2.vars }
    else n1'
  else n1

/-- The processed node for one snapshot entry. -/
def processEntry (snapshot : List (Path × NormNode)) (p1 : Path)
    (n1₀ : NormNode) : NormNode :=
  snapshot.foldl (fun n1 pn => subsumeStep p1 n1 pn.1 pn.2) n1₀

/-- Pure model of the whole pass: every entry is processed against the
    immutable snapshot and written back at its own key. -/
def subsumptionModel (acc : NormLevel) : NormLevel :=
  acc.toList.foldl
    (fun result pn => result.insert pn.1 (processEntry acc.toList pn.1 pn.2))
    acc

/-- `forIn` in `Id` with an all-`yield` body is a fold. -/
private theorem forIn_id_eq_foldl {α β : Type _} :
    ∀ (l : List α) (init : β) (f : α → β → Id (ForInStep β)) (g : β → α → β),
      (∀ a ∈ l, ∀ b, f a b = ForInStep.yield (g b a)) →
      forIn (m := Id) l init f = l.foldl g init
  | [], _, _, _, _ => rfl
  | a :: as, init, f, g, h => by
    rw [List.forIn_cons, h a (List.mem_cons_self ..) init, List.foldl_cons]
    show forIn (m := Id) as (g init a) f = as.foldl g (g init a)
    exact forIn_id_eq_foldl as _ f g
      fun a' ha' => h a' (List.mem_cons_of_mem _ ha')

/-- The imperative pass equals the pure model. -/
theorem subsumption_eq_model (acc : NormLevel) :
    subsumption acc = subsumptionModel acc := by
  unfold subsumption subsumptionModel
  refine forIn_id_eq_foldl _ _ _ _ ?_
  rintro ⟨p1, n1₀⟩ hmem result
  refine congrArg (fun x => ForInStep.yield (result.insert p1 x)) ?_
  rw [processEntry]
  refine forIn_id_eq_foldl _ _ _ _ ?_
  rintro ⟨p2, n2⟩ hmem2 n1
  simp only [letFun, subsumeStep]
  split
  · split
    · split
      · split
        · rename_i h4
          try rw [if_pos h4]
          rfl
        · rename_i h4
          try rw [if_neg h4]
          rfl
      · split
        · rename_i h4
          try rw [if_pos h4]
          rfl
        · rename_i h4
          try rw [if_neg h4]
          rfl
    · split
      · rename_i h4
        try rw [if_pos h4]
        rfl
      · rename_i h4
        try rw [if_neg h4]
        rfl
  · rfl

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
/-! #### Canonical-form comparison soundness -/

/-- The derived `BEq VarNode` is field-wise on two lawful `UInt64`s. -/
instance : LawfulBEq VarNode where
  eq_of_beq {a b} h := by
    obtain ⟨ai, ao⟩ := a
    obtain ⟨bi, bo⟩ := b
    have h' : (ai == bi && ao == bo) = true := h
    rw [Bool.and_eq_true] at h'
    rw [eq_of_beq h'.1, eq_of_beq h'.2]
  rfl {a} := by
    obtain ⟨ai, ao⟩ := a
    show (ai == ai && ao == ao) = true
    simp

/-- The pair-key comparator `RBMap.toList_sorted` sorts by is lawful —
    inherited pointwise from the `Path` comparator. -/
private instance : Std.TransCmp
    (fun (a b : Path × NormNode) => compare a.1 b.1) where
  eq_swap :=
    Std.OrientedCmp.eq_swap (cmp := (compare : Path → Path → Ordering))
  isLE_trans :=
    Std.TransCmp.isLE_trans (cmp := (compare : Path → Path → Ordering))

/-- `normLevelEq` on canonical forms implies equal denotations. The
    entry-wise check gives `⟦l₁⟧ ≤ ⟦l₂⟧` directly; the size check upgrades
    the key-set inclusion to equality (pigeonhole over nodup sorted keys),
    giving the reverse. -/
theorem normLevelEq_eval {ρ : List Nat} {l₁ l₂ : NormLevel}
    (h : normLevelEq l₁ l₂ = true) :
    NormLevel.eval ρ l₁ = NormLevel.eval ρ l₂ := by
  rw [normLevelEq, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hsize, hall⟩ := h
  have hcorr : ∀ p n₁, (p, n₁) ∈ l₁.toList →
      ∃ n₂, l₂.find? p = some n₂ ∧
        NormNode.eval ρ n₂ = NormNode.eval ρ n₁ := by
    intro p n₁ hmem
    have h1 := hall (p, n₁) hmem
    simp only at h1
    split at h1
    · rename_i n₂ hf
      rw [Bool.and_eq_true] at h1
      refine ⟨n₂, hf, ?_⟩
      rw [NormNode.eval, NormNode.eval, eq_of_beq h1.1, eq_of_beq h1.2]
    · simp at h1
  have h12 : NormLevel.eval ρ l₁ ≤ NormLevel.eval ρ l₂ := by
    rw [NormLevel.eval_le]
    intro p n₁ hf
    obtain ⟨y, hymem, hycmp⟩ := Batteries.RBMap.find?_some_mem_toList hf
    cases Std.LawfulEqCmp.eq_of_compare hycmp
    obtain ⟨n₂, hf₂, heval⟩ := hcorr p n₁ hymem
    rw [← heval]
    exact NormLevel.le_eval hf₂
  have hnodup : (l₁.toList.map Prod.fst).Nodup := by
    refine List.Pairwise.map _ ?_ Batteries.RBMap.toList_sorted
    intro a b hlt heq
    have hc := Batteries.RBNode.cmpLT_iff.mp hlt
    rw [heq] at hc
    have hself : compare b.1 b.1 = .eq := Std.ReflCmp.compare_self
    rw [hself] at hc
    exact absurd hc (by decide)
  have hsub : ∀ p ∈ l₁.toList.map Prod.fst, p ∈ l₂.toList.map Prod.fst := by
    intro p hp
    obtain ⟨x₁, hmem₁, rfl⟩ := List.mem_map.mp hp
    obtain ⟨n₂, hf₂, -⟩ := hcorr x₁.1 x₁.2 hmem₁
    obtain ⟨y, hymem, hycmp⟩ := Batteries.RBMap.find?_some_mem_toList hf₂
    cases Std.LawfulEqCmp.eq_of_compare hycmp
    exact List.mem_map.mpr ⟨(x₁.1, n₂), hymem, rfl⟩
  have hlen : (l₂.toList.map Prod.fst).length
      ≤ (l₁.toList.map Prod.fst).length := by
    have hs := eq_of_beq hsize
    rw [Batteries.RBMap.size_eq, Batteries.RBMap.size_eq] at hs
    simp only [List.length_map]
    omega
  have hperm : List.Perm (l₁.toList.map Prod.fst)
      (l₂.toList.map Prod.fst) :=
    (List.subperm_of_subset hnodup hsub).perm_of_length_le hlen
  have h21 : NormLevel.eval ρ l₂ ≤ NormLevel.eval ρ l₁ := by
    rw [NormLevel.eval_le]
    intro p n₂ hf
    obtain ⟨y, hymem, hycmp⟩ := Batteries.RBMap.find?_some_mem_toList hf
    cases Std.LawfulEqCmp.eq_of_compare hycmp
    have hpk : p ∈ l₁.toList.map Prod.fst :=
      hperm.mem_iff.mpr (List.mem_map.mpr ⟨(p, n₂), hymem, rfl⟩)
    obtain ⟨x₁, hmem₁, hpp'⟩ := List.mem_map.mp hpk
    obtain ⟨n₂', hf₂, heval⟩ := hcorr x₁.1 x₁.2 hmem₁
    rw [hpp'] at hf₂
    have hn : n₂' = n₂ := Option.some.inj (hf₂.symm.trans hf)
    subst hn
    rw [heval]
    refine NormLevel.le_eval
      (Batteries.RBMap.find?_some.mpr ⟨x₁.1, hmem₁, ?_⟩)
    rw [hpp']
    exact Std.ReflCmp.compare_self
  exact Nat.le_antisymm h12 h21

/-- Canonical-form var-placement invariant: every variable contribution
    sits on its own entry's conditioning path. `normalizeLevel` output
    satisfies it — vars are only ever added at the path that just absorbed
    their index (`addVar` call sites), and `subsumeVars` only filters.
    The `+ 1` branch of `coversConst` is sound *only* under it (an active
    path pins `evalParam v.idx ≥ 1`); for raw maps `normLevelLe` is not
    `eval`-sound — `l₂ = {[] ↦ ⟨0, #[⟨5, 3⟩]⟩}` "covers"
    `l₁ = {[] ↦ ⟨4, #[]⟩}` yet `⟦l₁⟧ = 4 > 3 = ⟦l₂⟧` at `ρ 5 = 0`. -/
def VarsOnPath (l : NormLevel) : Prop :=
  ∀ p n, l.find? p = some n → ∀ v ∈ n.vars, v.idx ∈ p

/-- The covering entry's bound, shared by all coverage branches: an
    active `p₂ ⊆ p₁` entry contributes its full node value to `⟦l₂⟧`. -/
private theorem covering_entry_le {ρ : List Nat} {l₂ : NormLevel}
    {p₂ : Path} {n₂ : NormNode} (hmem : (p₂, n₂) ∈ l₂.toList)
    (hnz₂ : allNZ ρ p₂ = true) :
    NormNode.eval ρ n₂ ≤ NormLevel.eval ρ l₂ := by
  have hfind : l₂.find? p₂ = some n₂ :=
    Batteries.RBMap.find?_some.mpr ⟨p₂, hmem, Std.ReflCmp.compare_self⟩
  simpa [evalPath, hnz₂] using NormLevel.le_eval (ρ := ρ) hfind

/-- The coverage argument (level.rs:634-643, no upstream counterpart):
    `normLevelLe` on canonical forms implies `≤` on denotations —
    conditional on the `VarsOnPath` invariant of the right-hand form. -/
theorem normLevelLe_eval {ρ : List Nat} {l₁ l₂ : NormLevel}
    (hwf : VarsOnPath l₂) (h : normLevelLe l₁ l₂ = true) :
    NormLevel.eval ρ l₁ ≤ NormLevel.eval ρ l₂ := by
  rw [normLevelLe, List.all_eq_true] at h
  rw [NormLevel.eval_le]
  intro p₁ n₁ hf
  obtain ⟨y, hymem, hycmp⟩ := Batteries.RBMap.find?_some_mem_toList hf
  cases Std.LawfulEqCmp.eq_of_compare hycmp
  have h1 := h (p₁, n₁) hymem
  simp only at h1
  rw [evalPath_le]
  intro hnz
  rw [NormNode.eval_le]
  split at h1
  · -- syntactically-zero entry contributes nothing
    rename_i htriv
    rw [Bool.and_eq_true] at htriv
    refine ⟨?_, ?_⟩
    · rw [eq_of_beq htriv.1, show (0 : UInt64).toNat = 0 from by decide]
      exact Nat.zero_le _
    · intro v hv
      rw [Array.isEmpty_iff.mp htriv.2] at hv
      simp at hv
  · rw [Bool.and_eq_true, Bool.or_eq_true] at h1
    obtain ⟨hconst, hvars⟩ := h1
    constructor
    · -- the constant is covered
      rcases hconst with hc0 | hcov
      · rw [eq_of_beq hc0, show (0 : UInt64).toNat = 0 from by decide]
        exact Nat.zero_le _
      · rw [coversConst, List.any_eq_true] at hcov
        obtain ⟨⟨p₂, n₂⟩, hmem₂, hcheck⟩ := hcov
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hcheck
        obtain ⟨hsub, hdom⟩ := hcheck
        have hnz₂ := allNZ_of_isSubset hsub hnz
        refine Nat.le_trans ?_ (covering_entry_le hmem₂ hnz₂)
        rcases hdom with hcc | hvv
        · -- dominated by the covering constant
          refine Nat.le_trans
            (UInt64.le_iff_toNat_le.mp (of_decide_eq_true hcc)) ?_
          exact ((NormNode.eval_le (ρ := ρ)).mp (Nat.le_refl _)).1
        · -- dominated by a covering var: its index is pinned active
          rw [Array.any_eq_true] at hvv
          obtain ⟨i, hi, hvle⟩ := hvv
          have hvmem : n₂.vars[i] ∈ n₂.vars := Array.getElem_mem hi
          have hidx : n₂.vars[i].idx ∈ p₂ := by
            have hfind₂ : l₂.find? p₂ = some n₂ :=
              Batteries.RBMap.find?_some.mpr
                ⟨p₂, hmem₂, Std.ReflCmp.compare_self⟩
            exact hwf p₂ n₂ hfind₂ _ hvmem
          have h1ev : 1 ≤ evalParam ρ n₂.vars[i].idx := by
            rw [allNZ, List.all_eq_true] at hnz₂
            simpa using hnz₂ _ hidx
          have hoff : n₁.constant.toNat ≤ n₂.vars[i].offset.toNat + 1 := by
            refine Nat.le_trans
              (UInt64.le_iff_toNat_le.mp (of_decide_eq_true hvle)) ?_
            rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from by decide]
            exact Nat.mod_le ..
          have hvev : n₂.vars[i].eval ρ ≤ NormNode.eval ρ n₂ :=
            ((NormNode.eval_le (ρ := ρ)).mp (Nat.le_refl _)).2 _ hvmem
          refine Nat.le_trans ?_ hvev
          rw [VarNode.eval]
          omega
    · -- every var is covered by a var of no smaller offset, same index
      intro v₁ hv₁
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hv₁
      have hcv := Array.all_eq_true.mp hvars i hi
      rw [coversVar, List.any_eq_true] at hcv
      obtain ⟨⟨p₂, n₂⟩, hmem₂, hcheck⟩ := hcv
      simp only [Bool.and_eq_true] at hcheck
      obtain ⟨hsub, hvv⟩ := hcheck
      have hnz₂ := allNZ_of_isSubset hsub hnz
      refine Nat.le_trans ?_ (covering_entry_le hmem₂ hnz₂)
      rw [Array.any_eq_true] at hvv
      obtain ⟨j, hj, hj2⟩ := hvv
      simp only [Bool.and_eq_true] at hj2
      obtain ⟨hidxeq, hoffge⟩ := hj2
      have hvmem : n₂.vars[j] ∈ n₂.vars := Array.getElem_mem hj
      have hvev : n₂.vars[j].eval ρ ≤ NormNode.eval ρ n₂ :=
        ((NormNode.eval_le (ρ := ρ)).mp (Nat.le_refl _)).2 _ hvmem
      refine Nat.le_trans ?_ hvev
      rw [VarNode.eval, VarNode.eval, eq_of_beq hidxeq]
      have := UInt64.le_iff_toNat_le.mp (of_decide_eq_true hoffge)
      omega

/-- `NormNode.addVar` only adds the given index: every var of the result
    carries the fresh `idx` or an index already present in the node. -/
private theorem NormNode.addVar_idx_mem {n : NormNode} {idx k : UInt64} :
    ∀ v ∈ (n.addVar idx k).vars,
      v.idx = idx ∨ ∃ v' ∈ n.vars, v.idx = v'.idx := by
  intro v hv
  simp only [NormNode.addVar] at hv
  split at hv
  · rename_i p hfind
    obtain ⟨hp, hple, hmin⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfind
    have hbang : n.vars[p]! = n.vars[p] := getElem!_pos ..
    rw [hbang] at hv
    have hp' : p < n.vars.toList.length := by simpa using hp
    split at hv
    · -- set!: the updated slot keeps `vars[p].idx`
      simp only [← Array.mem_toList_iff, Array.set!_eq_setIfInBounds,
        Array.toList_setIfInBounds] at hv
      obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hv
      rw [List.getElem_set] at hje
      split at hje
      · rw [← hje]
        exact .inr ⟨n.vars[p], Array.getElem_mem hp, rfl⟩
      · rw [← hje]
        refine .inr ⟨_, ?_, rfl⟩
        rw [← Array.mem_toList_iff]
        exact List.getElem_mem _
    · -- insertIdx!: the fresh `⟨idx, k⟩` plus the old vars
      have hple' : p ≤ n.vars.toList.length := by simpa using Nat.le_of_lt hp
      have hins : (n.vars.insertIdx! p ⟨idx, k⟩).toList
          = n.vars.toList.insertIdx p ⟨idx, k⟩ := by
        unfold Array.insertIdx!
        split
        all_goals first
          | exact Array.toList_insertIdx _
          | (exfalso; omega)
      simp only [← Array.mem_toList_iff, hins] at hv
      rcases (List.mem_insertIdx hple').mp hv with rfl | hv'
      · exact .inl rfl
      · exact .inr ⟨v, by simpa using hv', rfl⟩
  · -- push
    simp only [← Array.mem_toList_iff, Array.toList_push] at hv
    rcases List.mem_append.mp hv with hv' | hv'
    · exact .inr ⟨v, by simpa using hv', rfl⟩
    · rw [List.mem_singleton] at hv'
      subst hv'
      exact .inl rfl

/-- `addVar` at a path that contains the index preserves the invariant. -/
theorem VarsOnPath.addVar {l : NormLevel} {idx k : UInt64} {path : Path}
    (hl : VarsOnPath l) (hidx : idx ∈ path) :
    VarsOnPath (l.addVar idx k path) := by
  intro p n hf v hv
  rw [NormLevel.addVar, Batteries.RBMap.find?_insert] at hf
  split at hf
  · rename_i hcmp
    cases Std.LawfulEqCmp.eq_of_compare hcmp
    cases hf
    rcases NormNode.addVar_idx_mem v hv with rfl | ⟨v', hv', heq⟩
    · exact hidx
    · rw [heq]
      rw [Batteries.RBMap.findD] at hv'
      cases hff : l.find? path with
      | some n₀ =>
        rw [hff, Option.getD_some] at hv'
        exact hl path n₀ hff v' hv'
      | none =>
        rw [hff, Option.getD_none] at hv'
        simp at hv'
  · exact hl p n hf v hv

/-- `addConst` never touches vars, so it preserves the invariant. -/
theorem VarsOnPath.addConst {l : NormLevel} {k : UInt64} {path : Path}
    (hl : VarsOnPath l) : VarsOnPath (l.addConst k path) := by
  intro p n hf v hv
  simp only [NormLevel.addConst] at hf
  split at hf
  · exact hl p n hf v hv
  · rw [Batteries.RBMap.find?_insert] at hf
    split at hf
    · rename_i hcmp
      cases Std.LawfulEqCmp.eq_of_compare hcmp
      cases hf
      rw [Batteries.RBMap.findD] at hv
      cases hff : l.find? path with
      | some n₀ =>
        rw [hff, Option.getD_some] at hv
        exact hl path n₀ hff v hv
      | none =>
        rw [hff, Option.getD_none] at hv
        simp at hv
    · exact hl p n hf v hv

mutual

private theorem varsOnPath_normalizeAux :
    ∀ (l : KUniv m) (path : Path) (k : UInt64) (acc : NormLevel),
      VarsOnPath acc → VarsOnPath (normalizeAux l path k acc)
  | .zero ad, path, k, acc, hacc => by
    simp only [normalizeAux]
    exact hacc.addConst
  | .succ inner ad, path, k, acc, hacc => by
    simp only [normalizeAux]
    exact varsOnPath_normalizeAux inner path (k + 1) acc hacc
  | .max a b ad, path, k, acc, hacc => by
    simp only [normalizeAux]
    exact varsOnPath_normalizeAux b path k _
      (varsOnPath_normalizeAux a path k acc hacc)
  | .imax u (.zero b_ad) ad, path, k, acc, hacc => by
    simp only [normalizeAux]
    exact hacc.addConst
  | .imax u (.succ v b_ad) ad, path, k, acc, hacc => by
    simp only [normalizeAux]
    exact varsOnPath_normalizeAux v path (k + 1) _
      (varsOnPath_normalizeAux u path k acc hacc)
  | .imax u (.max v w b_ad) ad, path, k, acc, hacc => by
    simp only [normalizeAux]
    exact varsOnPath_normalizeImaxMax u v w path k acc hacc
  | .imax u (.imax v w b_ad) ad, path, k, acc, hacc => by
    simp only [normalizeAux]
    exact varsOnPath_normalizeImaxImax u v w path k acc hacc
  | .imax u (.param idx nm b_ad) ad, path, k, acc, hacc => by
    cases h₁ : orderedInsert idx path with
    | some newPath =>
      simp only [normalizeAux, h₁]
      exact varsOnPath_normalizeAux u newPath k _
        ((hacc.addConst).addVar ((mem_orderedInsert h₁).mpr (.inl rfl)))
    | none =>
      simp only [normalizeAux, h₁]
      refine varsOnPath_normalizeAux u path k _ ?_
      split
      · exact hacc.addVar (orderedInsert_none h₁)
      · exact hacc
  | .param idx nm ad, path, k, acc, hacc => by
    cases h₁ : orderedInsert idx path with
    | some newPath =>
      simp only [normalizeAux, h₁]
      exact (hacc.addConst).addVar ((mem_orderedInsert h₁).mpr (.inl rfl))
    | none =>
      simp only [normalizeAux, h₁]
      split
      · exact hacc.addVar (orderedInsert_none h₁)
      · exact hacc
termination_by l _ _ _ _ => 3 * l.size
decreasing_by
  all_goals try simp [KUniv.size]
  all_goals omega

private theorem varsOnPath_normalizeImaxMax :
    ∀ (u v w : KUniv m) (path : Path) (k : UInt64) (acc : NormLevel),
      VarsOnPath acc → VarsOnPath (normalizeImaxMax u v w path k acc)
  | u, v, w, path, k, acc, hacc => by
    simp only [normalizeImaxMax]
    exact varsOnPath_normalizeImaxDispatch u w path k _
      (varsOnPath_normalizeImaxDispatch u v path k acc hacc)
termination_by u v w _ _ _ _ => 3 * (u.size + v.size + w.size) + 1
decreasing_by
  all_goals have hv := KUniv.size_pos v
  all_goals have hw := KUniv.size_pos w
  all_goals omega

private theorem varsOnPath_normalizeImaxImax :
    ∀ (u v w : KUniv m) (path : Path) (k : UInt64) (acc : NormLevel),
      VarsOnPath acc → VarsOnPath (normalizeImaxImax u v w path k acc)
  | u, v, w, path, k, acc, hacc => by
    simp only [normalizeImaxImax]
    exact varsOnPath_normalizeImaxDispatch v w path k _
      (varsOnPath_normalizeImaxDispatch u w path k acc hacc)
termination_by u v w _ _ _ _ => 3 * (u.size + v.size + w.size) + 1
decreasing_by
  all_goals have hu := KUniv.size_pos u
  all_goals have hv := KUniv.size_pos v
  all_goals omega

private theorem varsOnPath_normalizeImaxDispatch :
    ∀ (a b : KUniv m) (path : Path) (k : UInt64) (acc : NormLevel),
      VarsOnPath acc → VarsOnPath (normalizeImaxDispatch a b path k acc)
  | a, .zero b_ad, path, k, acc, hacc => by
    simp only [normalizeImaxDispatch]
    exact hacc.addConst
  | a, .succ v b_ad, path, k, acc, hacc => by
    simp only [normalizeImaxDispatch]
    exact varsOnPath_normalizeAux v path (k + 1) _
      (varsOnPath_normalizeAux a path k acc hacc)
  | a, .max v w b_ad, path, k, acc, hacc => by
    simp only [normalizeImaxDispatch]
    exact varsOnPath_normalizeImaxMax a v w path k acc hacc
  | a, .imax v w b_ad, path, k, acc, hacc => by
    simp only [normalizeImaxDispatch]
    exact varsOnPath_normalizeImaxImax a v w path k acc hacc
  | a, .param idx nm b_ad, path, k, acc, hacc => by
    cases h₁ : orderedInsert idx path with
    | some newPath =>
      simp only [normalizeImaxDispatch, h₁]
      exact varsOnPath_normalizeAux a newPath k _
        ((hacc.addConst).addVar ((mem_orderedInsert h₁).mpr (.inl rfl)))
    | none =>
      simp only [normalizeImaxDispatch, h₁]
      refine varsOnPath_normalizeAux a path k _ ?_
      split
      · exact hacc.addVar (orderedInsert_none h₁)
      · exact hacc
termination_by a b _ _ _ _ => 3 * (a.size + b.size) + 2
decreasing_by
  all_goals try simp [KUniv.size]
  all_goals omega

end

private theorem varsOnPath_seed :
    VarsOnPath ((∅ : NormLevel).insert [] ({} : NormNode)) := by
  intro p n hf v hv
  rw [Batteries.RBMap.find?_insert] at hf
  split at hf
  · cases hf
    simp at hv
  · obtain ⟨y, hy, -⟩ := Batteries.RBMap.find?_some_mem_toList hf
    simp at hy

/-- `subsumeVars` only filters: every survivor comes from the first
    input. -/
private theorem mem_subsumeVars_go {xs ys : Array VarNode} :
    ∀ (xi yi : Nat) (result : Array VarNode) (v : VarNode),
      v ∈ subsumeVars.go xs ys xi yi result → v ∈ result ∨ v ∈ xs
  | xi, yi, result, v, hv => by
    rw [subsumeVars.go] at hv
    simp only [] at hv
    split at hv
    · rename_i hx
      split at hv
      · rcases Array.mem_append.mp hv with h | h
        · exact .inl h
        · rw [Array.mem_extract_iff_getElem] at h
          obtain ⟨kk, hkk, hke⟩ := h
          rw [← hke]
          exact .inr (Array.getElem_mem (by omega))
      · have hxi : xs[xi]! = xs[xi] := getElem!_pos ..
        split at hv
        · rcases mem_subsumeVars_go (xi + 1) yi _ v hv with h | h
          · rcases Array.mem_push.mp h with h' | rfl
            · exact .inl h'
            · rw [hxi]
              exact .inr (Array.getElem_mem hx)
          · exact .inr h
        · split at hv
          · rcases mem_subsumeVars_go (xi + 1) (yi + 1) _ v hv with h | h
            · split at h
              · rcases Array.mem_push.mp h with h' | rfl
                · exact .inl h'
                · rw [hxi]
                  exact .inr (Array.getElem_mem hx)
              · exact .inl h
            · exact .inr h
          · rcases mem_subsumeVars_go xi (yi + 1) result v hv with h | h
            · exact .inl h
            · exact .inr h
    · exact .inl hv
termination_by xi yi _ _ _ => (xs.size - xi) + (ys.size - yi)
decreasing_by all_goals omega

private theorem mem_subsumeVars {xs ys : Array VarNode} {v : VarNode}
    (hv : v ∈ subsumeVars xs ys) : v ∈ xs := by
  rw [subsumeVars] at hv
  rcases mem_subsumeVars_go 0 0 #[] v hv with h | h
  · simp at h
  · exact h

/-- Invariant rule for `Id`-monad `forIn` over a list (no early-exit
    assumption needed: the step hypothesis covers both `ForInStep`
    outcomes). Lets the `subsumption` loop proofs work directly on the
    do-elaborated body — no `foldl` normal form required. -/
private theorem forIn_id_invariant {α β : Type _} {P : β → Prop} :
    ∀ (l : List α) (init : β) (f : α → β → Id (ForInStep β)),
      P init →
      (∀ a ∈ l, ∀ b, P b →
        P (match f a b with | .yield b' => b' | .done b' => b')) →
      P (forIn (m := Id) l init f)
  | [], init, f, hinit, _ => by
    simpa using hinit
  | a :: as, init, f, hinit, hstep => by
    rw [List.forIn_cons]
    have h0 := hstep a (List.mem_cons_self ..) init hinit
    cases hfa : f a init with
    | done b =>
      rw [hfa] at h0
      show P (match ForInStep.done b with
        | .done b => (pure b : Id β)
        | .yield b => forIn as b f)
      exact h0
    | yield b =>
      rw [hfa] at h0
      show P (match ForInStep.yield b with
        | .done b => (pure b : Id β)
        | .yield b => forIn as b f)
      exact forIn_id_invariant as b f h0
        fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha')

/-- Push the loop-step selector through an `if` (the do-elaborated body
    is an `if`-tree of yields). -/
private theorem match_id_ite {β : Type _} {c : Prop} [Decidable c]
    {t e : Id (ForInStep β)} :
    (match (if c then t else e) with | .yield b' => b' | .done b' => b')
      = if c then (match t with | .yield b' => b' | .done b' => b')
        else (match e with | .yield b' => b' | .done b' => b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- Strip a unit-valued `Id` bind (the do-elaborator's join-point
    plumbing) under the selector — definitional by `PUnit` eta. -/
private theorem match_id_bind_unit {β : Type _} {x : Id PUnit}
    {f : PUnit → Id (ForInStep β)} :
    (match (x >>= f : Id (ForInStep β)) with
      | .yield b' => b' | .done b' => b')
      = (match f PUnit.unit with | .yield b' => b' | .done b' => b') := rfl

/-- Collapse the loop-step selector on an `Id` leaf (`pure`-yield). -/
private theorem match_id_yield₁ {β : Type _} {b : β} :
    (match (pure (ForInStep.yield b) : Id (ForInStep β)) with
      | .yield b' => b' | .done b' => b') = b := rfl

/-- Same, for the `do`-sequenced leaf the elaborator emits. -/
private theorem match_id_yield₂ {β : Type _} {b : β} :
    (match (do pure PUnit.unit; pure (ForInStep.yield b) : Id (ForInStep β))
        with
      | .yield b' => b' | .done b' => b') = b := rfl

/-- Replacing (or creating) the entry at `p1` with a node whose vars are
    drawn from a node already known to sit on `p1` preserves the
    invariant. -/
private theorem VarsOnPath.insert_of_subset {res : NormLevel} {p1 : Path}
    {n0 nf : NormNode} (hres : VarsOnPath res)
    (hsub : ∀ v ∈ nf.vars, v ∈ n0.vars)
    (h0 : ∀ v ∈ n0.vars, v.idx ∈ p1) :
    VarsOnPath (res.insert p1 nf) := by
  intro p n hf v hv
  rw [Batteries.RBMap.find?_insert] at hf
  split at hf
  · rename_i hcmp
    cases Std.LawfulEqCmp.eq_of_compare hcmp
    cases hf
    exact h0 v (hsub v hv)
  · exact hres p n hf v hv

/-- The subsumption pass preserves the invariant: entries only ever get
    their constant zeroed or their vars filtered (`subsumeVars` ⊆), always
    re-inserted at their own key. -/
theorem varsOnPath_subsumption {l : NormLevel} (hl : VarsOnPath l) :
    VarsOnPath (subsumption l) := by
  unfold subsumption
  refine forIn_id_invariant _ _ _ hl ?_
  rintro ⟨p1, n1₀⟩ hmem result hres
  refine VarsOnPath.insert_of_subset (n0 := n1₀) hres ?_ ?_
  · -- the processed node's vars come from the snapshot node
    refine forIn_id_invariant
      (P := fun (n1f : NormNode) => ∀ v ∈ n1f.vars, v ∈ n1₀.vars) _ _ _ ?_ ?_
    · exact fun v hv => hv
    rintro ⟨p2, n2⟩ hmem2 n1cur hcur v hv
    simp only [match_id_ite, match_id_bind_unit] at hv
    split at hv
    · split at hv
      · split at hv
        · split at hv
          · exact hcur v (mem_subsumeVars hv)
          · exact hcur v hv
        · split at hv
          · exact hcur v (mem_subsumeVars hv)
          · exact hcur v hv
      · split at hv
        · exact hcur v (mem_subsumeVars hv)
        · exact hcur v hv
    · exact hcur v hv
  · intro v hv
    have hf1 : l.find? p1 = some n1₀ :=
      Batteries.RBMap.find?_some.mpr ⟨p1, hmem, Std.ReflCmp.compare_self⟩
    exact hl p1 n1₀ hf1 v hv

/-! #### Subsumption: the `≤` half and the per-key characterization -/

/-- `isSubset` only accepts shorter-or-equal paths (each step consumes at
    least one element of the superset). -/
private theorem isSubset_length :
    ∀ {p q : Path}, isSubset p q = true → p.length ≤ q.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], h => by simp [isSubset] at h
  | a :: as, b :: bs, h => by
    rw [isSubset] at h
    split at h
    · exact Nat.le_succ_of_le (isSubset_length h)
    · split at h
      · simpa using Nat.succ_le_succ (isSubset_length h)
      · simp at h
  termination_by p q => q.length + p.length

/-- Zeroing the constant shrinks the node value. -/
private theorem constant_zero_eval_le {ρ : List Nat} {n : NormNode} :
    NormNode.eval ρ { n with constant := 0 } ≤ NormNode.eval ρ n :=
  NormNode.eval_le.mpr ⟨by simp,
    fun v hv => ((NormNode.eval_le (ρ := ρ)).mp (Nat.le_refl _)).2 v hv⟩

/-- Filtering the vars shrinks the node value. -/
private theorem subsume_vars_eval_le {ρ : List Nat} {n : NormNode}
    {ys : Array VarNode} :
    NormNode.eval ρ { n with vars := subsumeVars n.vars ys }
      ≤ NormNode.eval ρ n :=
  NormNode.eval_le.mpr ⟨((NormNode.eval_le (ρ := ρ) (n := n)).mp (Nat.le_refl _)).1,
    fun v hv => ((NormNode.eval_le (ρ := ρ) (n := n)).mp (Nat.le_refl _)).2 v
      (mem_subsumeVars hv)⟩

/-- One subsumption step never grows the node value. -/
private theorem subsumeStep_eval_le {ρ : List Nat} {p1 p2 : Path}
    {n1 n2 : NormNode} :
    NormNode.eval ρ (subsumeStep p1 n1 p2 n2) ≤ NormNode.eval ρ n1 := by
  simp only [subsumeStep]
  split
  · split
    · refine Nat.le_trans subsume_vars_eval_le ?_
      split
      · split
        · exact constant_zero_eval_le
        · exact Nat.le_refl _
      · exact Nat.le_refl _
    · split
      · split
        · exact constant_zero_eval_le
        · exact Nat.le_refl _
      · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- Processing an entry never grows its value. -/
private theorem processEntry_eval_le {ρ : List Nat} {p1 : Path} :
    ∀ (snapshot : List (Path × NormNode)) (n1 : NormNode),
      NormNode.eval ρ (processEntry snapshot p1 n1) ≤ NormNode.eval ρ n1
  | [], _ => Nat.le_refl _
  | pn :: rest, n1 => by
    rw [processEntry, List.foldl_cons]
    exact Nat.le_trans (processEntry_eval_le rest _) subsumeStep_eval_le

/-- Keys of an `RBMap`'s `toList` are nodup (strict sortedness). -/
private theorem toList_keys_nodup (l : NormLevel) :
    (l.toList.map Prod.fst).Nodup := by
  refine List.Pairwise.map _ ?_ Batteries.RBMap.toList_sorted
  intro a b hlt heq
  have hc := Batteries.RBNode.cmpLT_iff.mp hlt
  rw [heq] at hc
  have hself : compare b.1 b.1 = .eq := Std.ReflCmp.compare_self
  rw [hself] at hc
  exact absurd hc (by decide)

/-- A fold of key-wise inserts leaves foreign keys untouched. -/
private theorem foldl_insert_find?_of_not_mem
    (f : Path → NormNode → NormNode) :
    ∀ (todo : List (Path × NormNode)) (res : NormLevel) (p : Path),
      (∀ pn ∈ todo, p ≠ pn.1) →
      (todo.foldl (fun r pn => r.insert pn.1 (f pn.1 pn.2)) res).find? p
        = res.find? p
  | [], _, _, _ => rfl
  | pn :: rest, res, p, h => by
    rw [List.foldl_cons, foldl_insert_find?_of_not_mem f rest _ p
      fun q hq => h q (List.mem_cons_of_mem _ hq)]
    refine Batteries.RBMap.find?_insert_of_ne _ fun hcmp => ?_
    exact h pn (List.mem_cons_self ..) (Std.LawfulEqCmp.eq_of_compare hcmp)

/-- With nodup keys, the fold writes each entry exactly once. -/
private theorem foldl_insert_find?_self
    (f : Path → NormNode → NormNode) :
    ∀ (todo : List (Path × NormNode)) (res : NormLevel) (p : Path)
      (n : NormNode), (p, n) ∈ todo → (todo.map Prod.fst).Nodup →
      (todo.foldl (fun r pn => r.insert pn.1 (f pn.1 pn.2)) res).find? p
        = some (f p n)
  | [], _, _, _, h, _ => absurd h (List.not_mem_nil)
  | pn :: rest, res, p, n, hmem, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [foldl_insert_find?_of_not_mem f rest _ p fun q hq heq => hnd.1
        (heq ▸ List.mem_map.mpr ⟨q, hq, rfl⟩)]
      exact Batteries.RBMap.find?_insert_of_eq _ Std.ReflCmp.compare_self
    · exact foldl_insert_find?_self f rest _ p n hmem' hnd.2

/-- Forward characterization: every entry of the model comes from an
    original entry at the same key, processed against the snapshot. -/
private theorem subsumptionModel_find?_some {l : NormLevel} {p : Path}
    {n : NormNode} (hf : (subsumptionModel l).find? p = some n) :
    ∃ n₀, l.find? p = some n₀ ∧ n = processEntry l.toList p n₀ := by
  cases hf₀ : l.find? p with
  | some n₀ =>
    obtain ⟨y, hy, hycmp⟩ := Batteries.RBMap.find?_some_mem_toList hf₀
    cases Std.LawfulEqCmp.eq_of_compare hycmp
    refine ⟨n₀, rfl, ?_⟩
    rw [subsumptionModel,
      foldl_insert_find?_self _ l.toList l p n₀ hy (toList_keys_nodup l)]
      at hf
    exact (Option.some.inj hf).symm
  | none =>
    rw [subsumptionModel, foldl_insert_find?_of_not_mem _ l.toList l p
      (fun pn hpn heq => by
        rw [heq, Batteries.RBMap.find?_some.mpr
          ⟨pn.1, hpn, Std.ReflCmp.compare_self⟩] at hf₀
        simp at hf₀),
      hf₀] at hf
    simp at hf

/-- Backward access: the model's entry at an original key. -/
private theorem subsumptionModel_find?_of_mem {l : NormLevel} {p : Path}
    {n₀ : NormNode} (hmem : (p, n₀) ∈ l.toList) :
    (subsumptionModel l).find? p = some (processEntry l.toList p n₀) := by
  rw [subsumptionModel]
  exact foldl_insert_find?_self _ l.toList l p n₀ hmem (toList_keys_nodup l)

/-- The easy half: subsumption never grows the denotation. -/
private theorem subsumptionModel_eval_le {ρ : List Nat} {l : NormLevel} :
    NormLevel.eval ρ (subsumptionModel l) ≤ NormLevel.eval ρ l := by
  rw [NormLevel.eval_le]
  intro p n hf
  obtain ⟨n₀, hf₀, rfl⟩ := subsumptionModel_find?_some hf
  exact Nat.le_trans (evalPath_mono (processEntry_eval_le _ _))
    (NormLevel.le_eval hf₀)

/-! #### Subsumption: the `≥` half — drop characterizations -/

/-- `go` only ever grows the accumulator. -/
private theorem subsumeVars_go_mono {xs ys : Array VarNode} :
    ∀ (xi yi : Nat) (result : Array VarNode) (v : VarNode),
      v ∈ result → v ∈ subsumeVars.go xs ys xi yi result
  | xi, yi, result, v, hv => by
    rw [subsumeVars.go]
    simp only []
    split
    · split
      · exact Array.mem_append.mpr (.inl hv)
      · split
        · exact subsumeVars_go_mono (xi + 1) yi _ v
            (Array.mem_push.mpr (.inl hv))
        · split
          · refine subsumeVars_go_mono (xi + 1) (yi + 1) _ v ?_
            split
            · exact Array.mem_push.mpr (.inl hv)
            · exact hv
          · exact subsumeVars_go_mono xi (yi + 1) result v hv
    · exact hv
  termination_by xi yi _ _ _ => (xs.size - xi) + (ys.size - yi)
  decreasing_by all_goals omega

/-- Every pending element the walk drops has a dominator in `ys`: drops
    happen only on an index match against a no-smaller offset. -/
private theorem subsumeVars_go_drop {xs ys : Array VarNode} :
    ∀ (xi yi : Nat) (result : Array VarNode) (v : VarNode),
      (∃ j, xi ≤ j ∧ ∃ (hj : j < xs.size), xs[j] = v) →
      v ∉ subsumeVars.go xs ys xi yi result →
      ∃ y ∈ ys, v.idx = y.idx ∧ v.offset ≤ y.offset
  | xi, yi, result, v, ⟨j, hxj, hj, hje⟩, hd => by
    rw [subsumeVars.go] at hd
    simp only [] at hd
    split at hd
    · rename_i hx
      split at hd
      · exfalso
        refine hd (Array.mem_append.mpr (.inr
          (Array.mem_extract_iff_getElem.mpr ⟨j - xi, by omega, ?_⟩)))
        have heq : xi + (j - xi) = j := by omega
        simp only [heq]
        exact hje
      · rename_i hy
        have hxi : xs[xi]! = xs[xi] := getElem!_pos ..
        have hyi : ys[yi]! = ys[yi] := getElem!_pos _ _ (by omega)
        split at hd
        · rcases Nat.lt_or_ge xi j with hj' | hj'
          · exact subsumeVars_go_drop (xi + 1) yi _ v ⟨j, hj', hj, hje⟩ hd
          · exfalso
            have hji : j = xi := by omega
            subst hji
            exact hd (subsumeVars_go_mono _ _ _ _
              (Array.mem_push.mpr (.inr (by rw [hxi, hje]))))
        · split at hd
          · rename_i hidx
            rcases Nat.lt_or_ge xi j with hj' | hj'
            · exact subsumeVars_go_drop (xi + 1) (yi + 1) _ v
                ⟨j, hj', hj, hje⟩ hd
            · have hji : j = xi := by omega
              subst hji
              by_cases hoff : xs[j]!.offset > ys[yi]!.offset
              · exfalso
                rw [if_pos hoff] at hd
                exact hd (subsumeVars_go_mono _ _ _ _
                  (Array.mem_push.mpr (.inr (by rw [hxi, hje]))))
              · have hn : ¬(ys[yi]!.offset.toNat < xs[j]!.offset.toNat) :=
                  fun h => hoff (UInt64.lt_iff_toNat_lt.mpr h)
                have h2 : xs[j]!.offset.toNat ≤ ys[yi]!.offset.toNat := by
                  omega
                refine ⟨ys[yi], Array.getElem_mem (by omega), ?_, ?_⟩
                · rw [← hje, ← hxi, ← hyi]
                  exact eq_of_beq hidx
                · rw [← hje, ← hxi, ← hyi]
                  exact UInt64.le_iff_toNat_le.mpr h2
          · exact subsumeVars_go_drop xi (yi + 1) result v
              ⟨j, hxj, hj, hje⟩ hd
    · rename_i hx
      exact absurd hj (by omega)
  termination_by xi yi _ _ _ => (xs.size - xi) + (ys.size - yi)
  decreasing_by all_goals omega

/-- A dropped var has a dominator: same index, no smaller offset. -/
private theorem subsumeVars_drop {xs ys : Array VarNode} {v : VarNode}
    (hv : v ∈ xs) (hd : v ∉ subsumeVars xs ys) :
    ∃ y ∈ ys, v.idx = y.idx ∧ v.offset ≤ y.offset := by
  rw [subsumeVars] at hd
  obtain ⟨j, hj, hje⟩ := Array.mem_iff_getElem.mp hv
  exact subsumeVars_go_drop 0 0 #[] v ⟨j, Nat.zero_le _, hj, hje⟩ hd

/-- Step-level vars: kept verbatim, or filtered under the guards. -/
private theorem subsumeStep_vars_cases (p1 p2 : Path) (n1 n2 : NormNode) :
    (subsumeStep p1 n1 p2 n2).vars = n1.vars ∨
    (isSubset p2 p1 = true ∧ (p1.length == p2.length) = false ∧
      n2.vars.isEmpty = false ∧
      (subsumeStep p1 n1 p2 n2).vars = subsumeVars n1.vars n2.vars) := by
  simp only [subsumeStep]
  split
  · rename_i h1
    split
    · rename_i h4
      rw [Bool.and_eq_true] at h4
      obtain ⟨hs, he⟩ := h4
      refine .inr ⟨h1, ?_, ?_, ?_⟩
      · rwa [Bool.not_eq_true'] at hs
      · rwa [Bool.not_eq_true'] at he
      · split
        · split
          · rfl
          · rfl
        · rfl
    · left
      split
      · split
        · rfl
        · rfl
      · rfl
  · left
    rfl

/-- Step-level constant: kept verbatim, or zeroed with the recorded
    failure of `keepConst` (raw boolean payload). -/
private theorem subsumeStep_const_cases (p1 p2 : Path) (n1 n2 : NormNode) :
    (subsumeStep p1 n1 p2 n2).constant = n1.constant ∨
    (isSubset p2 p1 = true ∧
      ((p1.length == p2.length || decide (n1.constant > n2.constant))
        && (n2.vars.isEmpty
            || decide (n1.constant
                > n1.vars.foldl (fun acc v => max acc v.offset) 0 + 1)))
        = false) := by
  simp only [subsumeStep]
  split
  · rename_i h1
    split
    · split
      · split
        · rename_i h3
          refine .inr ⟨h1, ?_⟩
          rwa [Bool.not_eq_true'] at h3
        · left; rfl
      · left; rfl
    · split
      · split
        · rename_i h3
          refine .inr ⟨h1, ?_⟩
          rwa [Bool.not_eq_true'] at h3
        · left; rfl
      · left; rfl
  · left; rfl

private theorem processEntry_cons (p1 : Path) (pn : Path × NormNode)
    (rest : List (Path × NormNode)) (n1 : NormNode) :
    processEntry (pn :: rest) p1 n1
      = processEntry rest p1 (subsumeStep p1 n1 pn.1 pn.2) := by
  rw [processEntry, processEntry, List.foldl_cons]

/-- Processing only ever filters the var array. -/
private theorem processEntry_vars_subset {p1 : Path} :
    ∀ (snapshot : List (Path × NormNode)) (n1 : NormNode) (v : VarNode),
      v ∈ (processEntry snapshot p1 n1).vars → v ∈ n1.vars
  | [], _, _, hv => hv
  | pn :: rest, n1, v, hv => by
    rw [processEntry_cons] at hv
    have hrec := processEntry_vars_subset rest _ v hv
    rcases subsumeStep_vars_cases p1 pn.1 n1 pn.2 with hkeep | ⟨_, _, _, hfil⟩
    · exact hkeep ▸ hrec
    · exact mem_subsumeVars (hfil ▸ hrec)

/-- Fold-level vars: a var of the input either survives processing or is
    dominated by a var of some subset-path, strictly-shorter entry. -/
private theorem processEntry_var_cases {p1 : Path} :
    ∀ (snapshot : List (Path × NormNode)) (n1 : NormNode) (v : VarNode),
      v ∈ n1.vars →
      v ∈ (processEntry snapshot p1 n1).vars ∨
      ∃ pn ∈ snapshot, isSubset pn.1 p1 = true ∧
        (p1.length == pn.1.length) = false ∧
        ∃ y ∈ pn.2.vars, v.idx = y.idx ∧ v.offset ≤ y.offset
  | [], _, _, hv => .inl hv
  | pn :: rest, n1, v, hv => by
    rw [processEntry_cons]
    rcases subsumeStep_vars_cases p1 pn.1 n1 pn.2 with hkeep | ⟨h1, hs, _, hfil⟩
    · rcases processEntry_var_cases rest _ v (hkeep.symm ▸ hv)
        with h | ⟨qn, hqn, h⟩
      · exact .inl h
      · exact .inr ⟨qn, List.mem_cons_of_mem _ hqn, h⟩
    · by_cases hsv : v ∈ subsumeVars n1.vars pn.2.vars
      · rcases processEntry_var_cases rest _ v (hfil.symm ▸ hsv)
          with h | ⟨qn, hqn, h⟩
        · exact .inl h
        · exact .inr ⟨qn, List.mem_cons_of_mem _ hqn, h⟩
      · obtain ⟨y, hy, hidx, hoff⟩ := subsumeVars_drop hv hsv
        exact .inr ⟨pn, List.mem_cons_self .., h1, hs, y, hy, hidx, hoff⟩

/-- Fold-level constant: kept verbatim, or zeroed at some subset-path
    entry with the guard recorded against a node `m` that still carries
    the original constant and a sub-array of the original vars. -/
private theorem processEntry_const_cases {p1 : Path} :
    ∀ (snapshot : List (Path × NormNode)) (n1 : NormNode),
      (processEntry snapshot p1 n1).constant = n1.constant ∨
      ∃ pn ∈ snapshot, isSubset pn.1 p1 = true ∧
        ∃ (m : NormNode), m.constant = n1.constant ∧
          (∀ v ∈ m.vars, v ∈ n1.vars) ∧
          ((p1.length == pn.1.length || decide (m.constant > pn.2.constant))
            && (pn.2.vars.isEmpty
                || decide (m.constant
                    > m.vars.foldl (fun acc v => max acc v.offset) 0 + 1)))
            = false
  | [], _ => .inl rfl
  | pn :: rest, n1 => by
    rw [processEntry_cons]
    rcases subsumeStep_const_cases p1 pn.1 n1 pn.2 with hkeep | ⟨h1, hexp⟩
    · rcases processEntry_const_cases rest (subsumeStep p1 n1 pn.1 pn.2)
        with h | ⟨qn, hqn, hsub, m, hmc, hmv, hexp⟩
      · left
        rw [h, hkeep]
      · refine .inr ⟨qn, List.mem_cons_of_mem _ hqn, hsub, m, ?_, ?_, hexp⟩
        · rw [hmc, hkeep]
        · intro v hv
          have hmem := hmv v hv
          rcases subsumeStep_vars_cases p1 pn.1 n1 pn.2
            with hk | ⟨_, _, _, hf⟩
          · exact hk ▸ hmem
          · exact mem_subsumeVars (hf ▸ hmem)
    · exact .inr ⟨pn, List.mem_cons_self .., h1, n1, rfl, fun _ h => h, hexp⟩

/-- Max-fold over offsets is the init or attained by a member. -/
private theorem foldl_max_cases :
    ∀ (l : List VarNode) (init : UInt64),
      l.foldl (fun acc (v : VarNode) => max acc v.offset) init = init ∨
      ∃ v ∈ l, l.foldl (fun acc (v : VarNode) => max acc v.offset) init = v.offset
  | [], _ => .inl rfl
  | a :: l, init => by
    rw [List.foldl_cons]
    rcases foldl_max_cases l (max init a.offset) with h | ⟨v, hv, h⟩
    · rw [h]
      by_cases hle : init ≤ a.offset
      · refine .inr ⟨a, List.mem_cons_self .., ?_⟩
        show (if init ≤ a.offset then a.offset else init) = a.offset
        rw [if_pos hle]
      · left
        show (if init ≤ a.offset then a.offset else init) = init
        rw [if_neg hle]
    · exact .inr ⟨v, List.mem_cons_of_mem _ hv, h⟩

/-- The hard half: every original contribution is still dominated in the
    model — strong induction on the lex order (path length,
    constant-after-var). A dropped var's dominator sits at a strictly
    shorter path; a zeroed constant's dominator is a constant at a
    strictly shorter path or one of the same entry's own (active) vars. -/
private theorem le_subsumptionModel_eval {ρ : List Nat} {l : NormLevel}
    (hwf : ∀ p n, l.find? p = some n → ∀ v ∈ n.vars, v.idx ∈ p) :
    NormLevel.eval ρ l ≤ NormLevel.eval ρ (subsumptionModel l) := by
  have V : ∀ len, ∀ p1 n1₀, l.find? p1 = some n1₀ → p1.length < len →
      allNZ ρ p1 = true → ∀ v ∈ n1₀.vars,
      evalParam ρ v.idx + v.offset.toNat
        ≤ NormLevel.eval ρ (subsumptionModel l) := by
    intro len
    induction len with
    | zero =>
      intro p1 n1₀ _ h
      exact absurd h (by omega)
    | succ len ih =>
      intro p1 n1₀ hf hlen hnz v hv
      rcases processEntry_var_cases l.toList n1₀ v hv
        with hsurv | ⟨pn, hpn, hsub, hsame, y, hy, hidx, hoff⟩
      · obtain ⟨yy, hyy, hyycmp⟩ := Batteries.RBMap.find?_some_mem_toList hf
        cases Std.LawfulEqCmp.eq_of_compare hyycmp
        have hfm := subsumptionModel_find?_of_mem hyy
        refine Nat.le_trans
          (((NormNode.eval_le (ρ := ρ)).mp (Nat.le_refl _)).2 v hsurv) ?_
        simpa [evalPath, hnz] using NormLevel.le_eval (ρ := ρ) hfm
      · have hf₂ : l.find? pn.1 = some pn.2 :=
          Batteries.RBMap.find?_some.mpr
            ⟨pn.1, hpn, Std.ReflCmp.compare_self⟩
        have hnz₂ : allNZ ρ pn.1 = true := allNZ_of_isSubset hsub hnz
        have hlt : pn.1.length < p1.length := by
          have h1 := isSubset_length hsub
          have h2 : p1.length ≠ pn.1.length := by
            intro h
            rw [h] at hsame
            simp at hsame
          omega
        refine Nat.le_trans ?_ (ih pn.1 pn.2 hf₂ (by omega) hnz₂ y hy)
        rw [hidx]
        have := UInt64.le_iff_toNat_le.mp hoff
        omega
  have CC : ∀ len, ∀ p1 n1₀, l.find? p1 = some n1₀ → p1.length < len →
      allNZ ρ p1 = true →
      n1₀.constant.toNat ≤ NormLevel.eval ρ (subsumptionModel l) := by
    intro len
    induction len with
    | zero =>
      intro p1 n1₀ _ h
      exact absurd h (by omega)
    | succ len ih =>
      intro p1 n1₀ hf hlen hnz
      rcases processEntry_const_cases l.toList n1₀
        with hkeep | ⟨pn, hpn, hsub, m, hmc, hmv, hexp⟩
      · obtain ⟨yy, hyy, hyycmp⟩ := Batteries.RBMap.find?_some_mem_toList hf
        cases Std.LawfulEqCmp.eq_of_compare hyycmp
        have hfm := subsumptionModel_find?_of_mem hyy
        have hb : NormNode.eval ρ (processEntry l.toList p1 n1₀)
            ≤ NormLevel.eval ρ (subsumptionModel l) := by
          simpa [evalPath, hnz] using NormLevel.le_eval (ρ := ρ) hfm
        refine Nat.le_trans ?_ hb
        rw [← hkeep]
        exact ((NormNode.eval_le (ρ := ρ)).mp (Nat.le_refl _)).1
      · have hf₂ : l.find? pn.1 = some pn.2 :=
          Batteries.RBMap.find?_some.mpr
            ⟨pn.1, hpn, Std.ReflCmp.compare_self⟩
        have hnz₂ : allNZ ρ pn.1 = true := allNZ_of_isSubset hsub hnz
        rw [Bool.and_eq_false_iff] at hexp
        rcases hexp with hA | hB
        · rw [Bool.or_eq_false_iff] at hA
          obtain ⟨hsame, hcle⟩ := hA
          have hlt : pn.1.length < p1.length := by
            have h1 := isSubset_length hsub
            have h2 : p1.length ≠ pn.1.length := by
              intro h
              rw [h] at hsame
              simp at hsame
            omega
          have hncle := of_decide_eq_false hcle
          have hn : ¬(pn.2.constant.toNat < m.constant.toNat) :=
            fun h => hncle (UInt64.lt_iff_toNat_lt.mpr h)
          refine Nat.le_trans ?_ (ih pn.1 pn.2 hf₂ (by omega) hnz₂)
          rw [← hmc]
          omega
        · rw [Bool.or_eq_false_iff] at hB
          obtain ⟨hne, hmax⟩ := hB
          have hncle := of_decide_eq_false hmax
          have hn : ¬((m.vars.foldl (fun acc (v : VarNode) => max acc v.offset) 0
              + 1).toNat < m.constant.toNat) :=
            fun h => hncle (UInt64.lt_iff_toNat_lt.mpr h)
          have hub : (m.vars.foldl (fun acc (v : VarNode) => max acc v.offset) 0
              + 1).toNat
              ≤ (m.vars.foldl (fun acc (v : VarNode) => max acc v.offset) 0).toNat
                + 1 := by
            rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from by decide]
            exact Nat.mod_le ..
          have hmle : n1₀.constant.toNat
              ≤ (m.vars.foldl (fun acc (v : VarNode) => max acc v.offset) 0).toNat
                + 1 := by
            rw [← hmc]
            omega
          rcases foldl_max_cases m.vars.toList 0 with hz | ⟨w, hw, hweq⟩
          · -- own vars can only bound by 1: use a var of the covering entry
            rw [Array.foldl_toList] at hz
            rw [hz, show (0 : UInt64).toNat = 0 from by decide] at hmle
            have hsz : 0 < pn.2.vars.size := by
              rcases Nat.eq_zero_or_pos pn.2.vars.size with h | h
              · exfalso
                have : pn.2.vars.isEmpty = true := by
                  simp [Array.isEmpty, h]
                rw [this] at hne
                simp at hne
              · exact h
            have hymem : pn.2.vars[0] ∈ pn.2.vars := Array.getElem_mem hsz
            have hyidx : pn.2.vars[0].idx ∈ pn.1 := hwf pn.1 pn.2 hf₂ _ hymem
            have h1e : 1 ≤ evalParam ρ pn.2.vars[0].idx := by
              simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnz₂
              exact hnz₂ _ hyidx
            have hV := V (pn.1.length + 1) pn.1 pn.2 hf₂
              (Nat.lt_succ_self _) hnz₂ _ hymem
            omega
          · -- attained: the same entry's own var dominates, via V at p1
            rw [Array.foldl_toList] at hweq
            rw [hweq] at hmle
            have hw' : w ∈ n1₀.vars := hmv w (Array.mem_toList_iff.mp hw)
            have hwidx : w.idx ∈ p1 := hwf p1 n1₀ hf w hw'
            have h1e : 1 ≤ evalParam ρ w.idx := by
              simp only [allNZ, List.all_eq_true, decide_eq_true_eq] at hnz
              exact hnz _ hwidx
            have hV := V (p1.length + 1) p1 n1₀ hf
              (Nat.lt_succ_self _) hnz w hw'
            omega
  rw [NormLevel.eval_le]
  intro p1 n1₀ hf
  rw [evalPath_le]
  intro hnz
  rw [NormNode.eval_le]
  exact ⟨CC (p1.length + 1) p1 n1₀ hf (Nat.lt_succ_self _) hnz,
    fun v hv => V (p1.length + 1) p1 n1₀ hf (Nat.lt_succ_self _) hnz v hv⟩

/-- **Fresh** (upstream's live sorry, lean4lean `Verify/Level.lean:545`):
    the subsumption pass drops only dominated contributions. Needs the
    var-placement invariant (stated raw; defeq to `VarsOnPath l`): the
    `maxVarOffset + 1` zeroing branch is justified by a var of the *same*
    entry whose active index contributes ≥ 1 — for raw maps it is
    unsound: in `l = {[] ↦ ⟨0, #[⟨7, 0⟩]⟩, [5] ↦ ⟨1, #[]⟩}` the
    `[5]`-entry's constant is zeroed (own vars empty ⇒ `maxVarOffset = 0`,
    `1 ≤ 1`, the `[]`-entry's vars nonempty), yet at `ρ 5 = 1, ρ 7 = 0`
    the original evals to `1`, the subsumed to `0`. -/
theorem subsumption_eval {ρ : List Nat} {l : NormLevel}
    (hwf : ∀ p n, l.find? p = some n → ∀ v ∈ n.vars, v.idx ∈ p) :
    NormLevel.eval ρ (subsumption l) = NormLevel.eval ρ l := by
  rw [subsumption_eq_model]
  refine Nat.le_antisymm subsumptionModel_eval_le ?_
  exact le_subsumptionModel_eval hwf

/-- `normalizeLevel` establishes `VarsOnPath`: every `addVar` call site
    adds the index to the path first (`orderedInsert` hit) or already has
    it there (`orderedInsert` miss), and the subsumption pass only
    filters. -/
theorem varsOnPath_normalizeLevel {u : KUniv m} :
    VarsOnPath (normalizeLevel u) := by
  rw [normalizeLevel]
  exact varsOnPath_subsumption
    (varsOnPath_normalizeAux u [] 0 _ varsOnPath_seed)


/-- Normalization computes the `VLevel` denotation (placed after the
    `VarsOnPath` development: `subsumption_eval` consumes the invariant). -/
theorem normalizeLevel_eval {ρ : List Nat} {u : KUniv m}
    (hu : u.size < UInt64.size) :
    NormLevel.eval ρ (normalizeLevel u) = (KUniv.toVLevel u).eval ρ := by
  rw [normalizeLevel,
    subsumption_eval (varsOnPath_normalizeAux u [] 0 _ varsOnPath_seed),
    normalizeAux_eval (by simpa using hu) EvalPaths.nil, seed_eval]
  simp [evalPath, allNZ]
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
  exact Level.normLevelLe_eval Level.varsOnPath_normalizeLevel h

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
