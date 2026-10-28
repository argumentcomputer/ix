import Ix.CompileCert.Canon.Ref
import Ix.Mutual

/-! # The ordered mutual context

`Ix.MutConst.ctx` assigns each member its list index and each constructor
a slot after all members and the constructors of earlier members. The
fold characterization identifies every lookup when names are distinct.
-/

namespace Ix.CompileCert.Canon

open Ix (Name MutConst MutCtx ConstructorVal)

/-! ## The definition as a fold -/

/-- Insert one member and its constructors, then advance the constructor base. -/
def ctxStep (s : MutCtx × Nat) (p : MutConst × Nat) : MutCtx × Nat :=
  (p.1.ctors.zipIdx.foldl (fun mc q => mc.insert q.1.cnst.name (s.2 + q.2))
    (s.1.insert p.1.name p.2), s.2 + p.1.ctors.size)

theorem ctx_eq (members : List MutConst) :
    MutConst.ctx members = (members.zipIdx.foldl ctxStep (default, members.length)).1 := by
  simp only [MutConst.ctx]
  delta ctxStep
  simp

/-- Insert a name-index pair. -/
def insP (mc : MutCtx) (p : Name × Nat) : MutCtx := mc.insert p.1 p.2

/-- The pairs inserted for a member at index `j`, with constructor base `i`. -/
def pairsOf (j i : Nat) (member : MutConst) : List (Name × Nat) :=
  (member.name, j) :: (member.ctors.toList.zipIdx.map fun q => (q.1.cnst.name, i + q.2))

/-- The complete sequence of insertions. -/
def ctxPairs : List MutConst → Nat → Nat → List (Name × Nat)
  | [], _, _ => []
  | member :: rest, n, i => pairsOf n i member ++ ctxPairs rest (n + 1) (i + member.ctors.size)

/-- The total number of constructor slots. -/
def ctorCount : List MutConst → Nat
  | [] => 0
  | member :: rest => member.ctors.size + ctorCount rest

theorem ctor_fold (i : Nat) (m : MutConst) (mc : MutCtx) :
    m.ctors.zipIdx.foldl (fun mc q => mc.insert q.1.cnst.name (i + q.2)) mc =
      (m.ctors.toList.zipIdx.map fun q => (q.1.cnst.name, i + q.2)).foldl insP mc := by
  rw [← Array.foldl_toList, Array.toList_zipIdx, List.foldl_map]
  rfl

theorem members_fold : ∀ (members : List MutConst) (n i : Nat) (mc : MutCtx),
    (members.zipIdx n).foldl ctxStep (mc, i) =
      ((ctxPairs members n i).foldl insP mc, i + ctorCount members) := by
  intro members
  induction members with
  | nil => intro n i mc; simp [ctxPairs, ctorCount]
  | cons member rest ih =>
    intro n i mc
    simp only [List.zipIdx_cons, List.foldl_cons, ctxStep]
    rw [ih, ctor_fold]
    simp only [ctxPairs, pairsOf, ctorCount, List.foldl_append, List.foldl_cons, insP, Prod.mk.injEq,
      true_and]
    omega

theorem ctx_fold (members : List MutConst) :
    MutConst.ctx members = (ctxPairs members 0 members.length).foldl insP default := by
  rw [ctx_eq, members_fold]

/-! ## Lookups in a fold of distinct-key insertions

`MutCtx` is a tree map under `nameCompareExact`, a lawful order whose `eq`
is equality (`Ref.lean`): a lookup after an insertion answers the inserted
value for the inserted name only. -/

theorem treeMap_insert_self (m0 : MutCtx) (k : Name) (v : Nat) : (m0.insert k v)[k]? = some v := by
  rw [Std.TreeMap.getElem?_insert]; simp

theorem treeMap_insert_ne (m0 : MutCtx) {k x : Name} (v : Nat) (h : k ≠ x) :
    (m0.insert k v)[x]? = m0[x]? := by
  rw [Std.TreeMap.getElem?_insert]; simp [h]

theorem foldl_insP_getElem? :
    ∀ (L : List (Name × Nat)) (m0 : MutCtx),
      (L.map (·.1)).Pairwise (· ≠ ·) → ∀ (x : Name) (v : Nat),
      (L.foldl insP m0)[x]? = some v ↔
        (∃ p ∈ L, p.1 = x ∧ p.2 = v) ∨ ((∀ p ∈ L, p.1 ≠ x) ∧ m0[x]? = some v) := by
  intro L
  induction L with
  | nil =>
    intro m0 _ x v
    simp only [List.foldl_nil]
    constructor
    · intro h; exact .inr ⟨fun p hp => absurd hp List.not_mem_nil, h⟩
    · rintro (⟨p, hp, -⟩ | ⟨-, h⟩)
      · exact absurd hp List.not_mem_nil
      · exact h
  | cons p L ih =>
    intro m0 hd x v
    simp only [List.map_cons, List.pairwise_cons] at hd
    simp only [List.foldl_cons]
    rw [ih _ hd.2 x v]
    simp only [insP]
    by_cases hp : p.1 = x
    · subst hp
      rw [treeMap_insert_self]
      have hL : ∀ q ∈ L, q.1 ≠ p.1 := fun q hq e => hd.1 q.1 (List.mem_map_of_mem hq) e.symm
      constructor
      · rintro (⟨q, hq, hqx, -⟩ | ⟨-, h⟩)
        · exact absurd hqx (hL q hq)
        · cases h; exact .inl ⟨p, by simp, rfl, rfl⟩
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, -⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact .inr ⟨hL, rfl⟩
          · exact absurd hqx (hL q hq)
        · exact absurd rfl (h p (by simp))
    · rw [treeMap_insert_ne _ _ hp]
      constructor
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · exact .inl ⟨q, List.mem_cons_of_mem _ hq, hqx, rfl⟩
        · refine .inr ⟨fun q hq => ?_, h'⟩
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact h q hq
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact absurd hqx hp
          · exact .inl ⟨q, hq, hqx, rfl⟩
        · exact .inr ⟨fun q hq => h q (List.mem_cons_of_mem _ hq), h'⟩

/-! ## The pairs -/

/-- The names a member contributes: its own, then its constructors'. -/
def keysOf (m : MutConst) : List Name := m.name :: m.ctors.toList.map (·.cnst.name)

/-- The member and constructor names are pairwise distinct (Lean's names are
unique). -/
def KeysDistinct (ms : List MutConst) : Prop := (ms.flatMap keysOf).Nodup

theorem KeysDistinct.perm {ms ms' : List MutConst} (h : ms.Perm ms') (hk : KeysDistinct ms) :
    KeysDistinct ms' :=
  (List.Perm.flatMap_right keysOf h).nodup_iff.1 hk

theorem map_zipIdx_fst {β γ : Type} (f : β → γ) :
    ∀ (l : List β) (n : Nat), (l.zipIdx n).map (fun q => f q.1) = l.map f
  | [], _ => rfl
  | b :: l, n => by simp only [List.zipIdx_cons, List.map_cons]; rw [map_zipIdx_fst f l (n + 1)]

theorem keys_pairsOf (j i : Nat) (m : MutConst) :
    (pairsOf j i m).map (·.1) = keysOf m := by
  simp only [pairsOf, List.map_cons, List.map_map, keysOf]
  congr 1
  exact map_zipIdx_fst (fun c : ConstructorVal => c.cnst.name) _ 0

/-- The constructor offset of member `j`, after earlier members' constructors. -/
def offs (members : List MutConst) (j : Nat) : Nat := ctorCount (members.take j)

theorem offs_zero (members : List MutConst) : offs members 0 = 0 := by simp [offs, ctorCount]

theorem offs_cons_succ (m : MutConst) (rest : List MutConst) (j : Nat) :
    offs (m :: rest) (j + 1) = m.ctors.size + offs rest j := by simp [offs, ctorCount]

theorem keys_ctxPairs : ∀ (members : List MutConst) (n i : Nat),
    (ctxPairs members n i).map (·.1) = members.flatMap keysOf
  | [], _, _ => rfl
  | m :: rest, n, i => by
    simp only [ctxPairs, List.map_append, keys_pairsOf, keys_ctxPairs rest, List.flatMap_cons]

theorem mem_pairsOf {p : Name × Nat} {j i : Nat} {m : MutConst} :
    p ∈ pairsOf j i m ↔ p = (m.name, j) ∨
      ∃ (k : Nat) (c : ConstructorVal), m.ctors[k]? = some c ∧ p = (c.cnst.name, i + k) := by
  simp only [pairsOf, List.mem_cons, List.mem_map]
  refine or_congr_right ?_
  constructor
  · rintro ⟨⟨c, k⟩, hq, rfl⟩
    have := List.mem_zipIdx_iff_getElem?.1 hq
    simp only [Array.getElem?_toList] at this
    exact ⟨k, c, this, rfl⟩
  · rintro ⟨k, c, hc, rfl⟩
    exact ⟨(c, k), List.mem_zipIdx_iff_getElem?.2 (by simpa [Array.getElem?_toList] using hc), rfl⟩

theorem mem_ctxPairs : ∀ (members : List MutConst) (n i : Nat) (p : Name × Nat),
    p ∈ ctxPairs members n i ↔ ∃ (j : Nat) (m : MutConst), members[j]? = some m ∧
      (p = (m.name, n + j) ∨ ∃ (k : Nat) (c : ConstructorVal), m.ctors[k]? = some c ∧
        p = (c.cnst.name, i + offs members j + k))
  | [], n, i, p => by
    simp only [ctxPairs, List.not_mem_nil, false_iff]
    rintro ⟨j, m, h, -⟩
    rw [List.getElem?_nil] at h; cases h
  | m :: rest, n, i, p => by
    simp only [ctxPairs, List.mem_append, mem_pairsOf, mem_ctxPairs rest (n + 1) (i + m.ctors.size) p]
    constructor
    · rintro (h | ⟨j, member, hm, h⟩)
      · refine ⟨0, m, rfl, ?_⟩
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (by rw [h, Nat.add_zero])
        · exact .inr ⟨k, c, hc, by rw [h, offs_zero, Nat.add_zero]⟩
      · refine ⟨j + 1, member, by rw [List.getElem?_cons_succ]; exact hm, ?_⟩
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (by rw [h]; congr 1; omega)
        · exact .inr ⟨k, c, hc, by rw [h, offs_cons_succ]; congr 1; omega⟩
    · rintro ⟨j, member, hm, h⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (.inl (by rw [h, Nat.add_zero]))
        · exact .inl (.inr ⟨k, c, hc, by rw [h, offs_zero, Nat.add_zero]⟩)
      | succ j =>
        simp only [List.getElem?_cons_succ] at hm
        refine .inr ⟨j, member, hm, ?_⟩
        rcases h with h | ⟨k, c, hc, h⟩
        · exact .inl (by rw [h]; congr 1; omega)
        · exact .inr ⟨k, c, hc, by rw [h, offs_cons_succ]; congr 1; omega⟩

/-! ## Values of the context -/

theorem default_getElem? (x : Name) : (default : MutCtx)[x]? = none := by
  show (∅ : MutCtx)[x]? = none
  exact Std.TreeMap.getElem?_emptyc

/-- Distinct keys, as a pairwise statement. -/
theorem KeysDistinct.ne {ms : List MutConst} (hk : KeysDistinct ms) :
    (ms.flatMap keysOf).Pairwise (· ≠ ·) := hk

section
variable {cls : List MutConst} (hk : KeysDistinct cls)
include hk

theorem ctx_lookup (x : Name) (v : Nat) :
    (MutConst.ctx cls)[x]? = some v ↔ ∃ p ∈ ctxPairs cls 0 cls.length, p.1 = x ∧ p.2 = v := by
  rw [ctx_fold, foldl_insP_getElem? _ _ (by rw [keys_ctxPairs]; exact hk.ne), default_getElem?]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact h
    · cases h
  · exact .inl

theorem ctx_member {j : Nat} {m : MutConst} (hm : cls[j]? = some m) :
    (MutConst.ctx cls)[m.name]? = some j :=
  (ctx_lookup hk _ _).2 ⟨(m.name, j), (mem_ctxPairs cls 0 _ _).2 ⟨j, m, hm, .inl (by simp)⟩,
    rfl, rfl⟩

theorem ctx_ctor {j : Nat} {m : MutConst} (hm : cls[j]? = some m)
    {k : Nat} {c : ConstructorVal} (hc : m.ctors[k]? = some c) :
    (MutConst.ctx cls)[c.cnst.name]? = some (cls.length + offs cls j + k) :=
  (ctx_lookup hk _ _).2 ⟨(c.cnst.name, cls.length + offs cls j + k),
    (mem_ctxPairs cls 0 _ _).2 ⟨j, m, hm, .inr ⟨k, c, hc, rfl⟩⟩, rfl, rfl⟩

theorem ctx_val {x : Name} {v : Nat} (h : (MutConst.ctx cls)[x]? = some v) :
    ∃ (j : Nat) (m : MutConst), cls[j]? = some m ∧
      ((m.name = x ∧ v = j) ∨ ∃ (k : Nat) (c : ConstructorVal), m.ctors[k]? = some c ∧
        c.cnst.name = x ∧ v = cls.length + offs cls j + k) := by
  obtain ⟨p, hp, hpx, rfl⟩ := (ctx_lookup hk x v).1 h
  obtain ⟨j, m, hm, hp'⟩ := (mem_ctxPairs cls 0 _ p).1 hp
  refine ⟨j, m, hm, ?_⟩
  rcases hp' with rfl | ⟨k, c, hc, rfl⟩
  · exact .inl ⟨hpx, by simp⟩
  · exact .inr ⟨k, c, hc, hpx, rfl⟩

end

/-- The names in the context are the member and constructor names. -/
theorem ctx_dom (cls : List MutConst) (x : Name) :
    ((MutConst.ctx cls)[x]?).isSome = true ↔ x ∈ cls.flatMap keysOf := by
  have key : ∀ (L : List (Name × Nat)) (m0 : MutCtx),
      ((L.foldl insP m0)[x]?).isSome = true ↔ (x ∈ L.map (·.1) ∨ (m0[x]?).isSome = true) := by
    intro L
    induction L with
    | nil => intro m0; simp
    | cons p L ih =>
      intro m0
      simp only [List.foldl_cons, List.map_cons, List.mem_cons]
      rw [ih]
      simp only [insP]
      by_cases hp : p.1 = x
      · subst hp; simp
      · rw [treeMap_insert_ne _ _ hp]
        constructor
        · rintro (h | h)
          · exact .inl (.inr h)
          · exact .inr h
        · rintro ((h | h) | h)
          · exact absurd h.symm hp
          · exact .inl h
          · exact .inr h
  rw [ctx_fold, key, keys_ctxPairs, default_getElem?]
  simp
/-! ## Constructor slots are disjoint across members -/

theorem offs_succ : ∀ (cls : List MutConst) (j : Nat) (C : MutConst), cls[j]? = some C →
    offs cls (j + 1) = offs cls j + C.ctors.size
  | [], _, _, h => by cases h
  | D :: rest, 0, C, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
    simp [offs, ctorCount]
  | D :: rest, j + 1, C, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [offs_cons_succ, offs_cons_succ, offs_succ rest j C h]; omega

theorem offs_mono (cls : List MutConst) : ∀ {j₁ j₂ : Nat}, j₁ ≤ j₂ → offs cls j₁ ≤ offs cls j₂ := by
  intro j₁ j₂ h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i j _
    have : offs cls j ≤ offs cls (j + 1) := by
      unfold offs
      rcases Nat.lt_or_ge j cls.length with hj | hj
      · rw [List.take_add_one, List.getElem?_eq_getElem hj]
        have : ∀ (a b : List MutConst), ctorCount (a ++ b) = ctorCount a + ctorCount b := by
          intro a b; induction a with
          | nil => simp [ctorCount]
          | cons x a ih' => simp only [List.cons_append, ctorCount, ih']; omega
        simp only [Option.toList_some, this]; omega
      · rw [List.take_of_length_le hj, List.take_of_length_le (by omega)]; exact Nat.le_refl _
    exact Nat.le_trans ih this

theorem slot_disjoint {cls : List MutConst} {j₁ j₂ : Nat} {C₁ C₂ : MutConst}
    (h₁ : cls[j₁]? = some C₁) (h₂ : cls[j₂]? = some C₂) {k₁ k₂ : Nat} (hk₁ : k₁ < C₁.ctors.size)
    (hk₂ : k₂ < C₂.ctors.size) (h : offs cls j₁ + k₁ = offs cls j₂ + k₂) : j₁ = j₂ ∧ k₁ = k₂ := by
  rcases Nat.lt_trichotomy j₁ j₂ with hl | rfl | hl
  · have := offs_mono cls (Nat.succ_le_of_lt hl); rw [offs_succ cls j₁ C₁ h₁] at this; omega
  · exact ⟨rfl, by omega⟩
  · have := offs_mono cls (Nat.succ_le_of_lt hl); rw [offs_succ cls j₂ C₂ h₂] at this; omega

end Ix.CompileCert.Canon
