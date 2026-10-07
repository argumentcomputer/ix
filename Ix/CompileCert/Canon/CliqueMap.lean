import Ix.CompileCert.Canon.SccNames
import Ix.Compile.Canon.NameMap

/-!
# M7 L1, the clique name map is well defined

`Ix.Compile.Canon.cliqueNameMap classes` sends each name of each class to the class's position.
`cliqueNameMap_spec`: when the names are pairwise distinct under `==`, a name is mapped to
`.clique k` exactly when it is (`==`) a name of the `k`-th class, and to nothing else.

(`blockNameMap` builds the names `T.rec`, `all₀.rec_j`, … with `Ix.Name.mkStr`, which carries the
two `native_decide` auxiliaries of the report's §3; statements about it wait on that decision.)
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name)

/-- Inserting pairs with pairwise distinct keys: a key is found at its pair's value. -/
theorem foldl_insert_getElem?' {β : Type} :
    ∀ (L : List (Name × β)) (m0 : Std.HashMap Name β),
      (L.map (·.1)).Pairwise (fun a b => (a == b) = false) → ∀ (x : Name) (i : β),
      (L.foldl (fun m p => m.insert p.1 p.2) m0)[x]? = some i ↔
        (∃ p ∈ L, (p.1 == x) = true ∧ p.2 = i) ∨ ((∀ p ∈ L, (p.1 == x) = false) ∧ m0[x]? = some i) := by
  intro L
  induction L with
  | nil =>
    intro m0 _ x i
    simp only [List.foldl_nil]
    constructor
    · intro h; exact .inr ⟨fun p hp => absurd hp List.not_mem_nil, h⟩
    · rintro (⟨p, hp, -⟩ | ⟨-, h⟩)
      · exact absurd hp List.not_mem_nil
      · exact h
  | cons p L ih =>
    intro m0 hd x i
    simp only [List.map_cons, List.pairwise_cons] at hd
    simp only [List.foldl_cons]
    rw [ih _ hd.2 x i, Std.HashMap.getElem?_insert]
    by_cases hp : (p.1 == x) = true
    · simp only [hp, ↓reduceIte, Option.some.injEq]
      constructor
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨-, h⟩)
        · exfalso
          have := hd.1 q.1 (List.mem_map_of_mem hq)
          rw [BEq.trans hp (BEq.symm hqx)] at this; cases this
        · exact .inl ⟨p, List.mem_cons_self .., hp, h⟩
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, -⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · have hall : ∀ q' ∈ L, (q'.1 == x) = false := fun q' hq' => by
              have := hd.1 q'.1 (List.mem_map_of_mem hq')
              cases hb : (q'.1 == x)
              · rfl
              · rw [BEq.trans hp (BEq.symm hb)] at this; cases this
            exact .inr ⟨hall, rfl⟩
          · exact .inl ⟨q, hq, hqx, rfl⟩
        · have := h p (List.mem_cons_self ..); rw [hp] at this; cases this
    · have hp' : (p.1 == x) = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · exact .inl ⟨q, List.mem_cons_of_mem _ hq, hqx, rfl⟩
        · refine .inr ⟨fun q hq => ?_, h'⟩
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp'
          · exact h q hq
      · rintro (⟨q, hq, hqx, rfl⟩ | ⟨h, h'⟩)
        · rcases List.mem_cons.1 hq with rfl | hq
          · rw [hp'] at hqx; cases hqx
          · exact .inl ⟨q, hq, hqx, rfl⟩
        · exact .inr ⟨fun q hq => h q (List.mem_cons_of_mem _ hq), h'⟩

/-- The pairs `cliqueNameMap` inserts, classes from position `k`. -/
def cliquePairs : List (Array Name) → Nat → List (Name × CanonPos)
  | [], _ => []
  | cls :: rest, k => cls.toList.map (fun n => (n, CanonPos.clique k)) ++ cliquePairs rest (k + 1)

theorem cliqueNameMap_eq (classes : Array (Array Name)) :
    cliqueNameMap classes = (cliquePairs classes.toList 0).foldl (fun m p => m.insert p.1 p.2) {} := by
  unfold cliqueNameMap
  rw [← Array.foldl_toList, Array.toList_zipIdx]
  generalize (∅ : Std.HashMap Name CanonPos) = m0
  suffices h : ∀ (L : List (Array Name)) (k : Nat) (m : Std.HashMap Name CanonPos),
      (L.zipIdx k).foldl (fun m q => q.1.foldl (fun m n => m.insert n (CanonPos.clique q.2)) m) m =
        (cliquePairs L k).foldl (fun m p => m.insert p.1 p.2) m from h _ 0 m0
  intro L
  induction L with
  | nil => intro k m; rfl
  | cons cls rest ih =>
    intro k m
    simp only [List.zipIdx_cons, List.foldl_cons, cliquePairs, List.foldl_append]
    rw [ih (k + 1)]
    congr 1
    rw [← Array.foldl_toList, List.foldl_map]

theorem cliquePairs_keys : ∀ (L : List (Array Name)) (k : Nat),
    (cliquePairs L k).map (·.1) = L.flatMap Array.toList
  | [], _ => rfl
  | cls :: rest, k => by
    simp only [cliquePairs, List.map_append, List.map_map, List.flatMap_cons, cliquePairs_keys rest]
    congr 1
    exact List.map_id' _

theorem mem_cliquePairs : ∀ (L : List (Array Name)) (k : Nat) (q : Name × CanonPos),
    q ∈ cliquePairs L k ↔ ∃ (j : Nat) (cls : Array Name), L[j]? = some cls ∧
      ∃ n ∈ cls, q = (n, CanonPos.clique (k + j))
  | [], _, q => by
    simp only [cliquePairs, List.not_mem_nil, List.getElem?_nil, reduceCtorEq, false_and,
      exists_false]
  | cls :: rest, k, q => by
    simp only [cliquePairs, List.mem_append, List.mem_map, mem_cliquePairs rest]
    constructor
    · rintro (⟨n, hn, rfl⟩ | ⟨j, c, hc, n, hn, rfl⟩)
      · exact ⟨0, cls, rfl, n, Array.mem_toList_iff.1 hn, by rw [Nat.add_zero]⟩
      · exact ⟨j + 1, c, by simpa using hc, n, hn, by rw [Nat.add_assoc, Nat.add_comm 1 j]⟩
    · rintro ⟨j, c, hc, n, hn, rfl⟩
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc; subst hc
        exact .inl ⟨n, Array.mem_toList_iff.2 hn, by rw [Nat.add_zero]⟩
      | succ j =>
        simp only [List.getElem?_cons_succ] at hc
        exact .inr ⟨j, c, hc, n, hn, by rw [Nat.add_assoc, Nat.add_comm 1 j]⟩

/-- **The clique name map is well defined**: with the names of the classes pairwise distinct
under `==`, a name is mapped exactly when it is a name of some class, and then to that class's
position. -/
theorem cliqueNameMap_spec {classes : Array (Array Name)}
    (hd : (classes.toList.flatMap Array.toList).Pairwise (fun a b => (a == b) = false))
    (x : Name) (p : CanonPos) :
    (cliqueNameMap classes)[x]? = some p ↔
      ∃ (k : Nat) (cls : Array Name), classes[k]? = some cls ∧ (∃ n ∈ cls, (n == x) = true) ∧
        p = .clique k := by
  rw [cliqueNameMap_eq, foldl_insert_getElem?' _ _ (by rw [cliquePairs_keys]; exact hd)]
  constructor
  · rintro (⟨q, hq, hqx, rfl⟩ | ⟨-, h⟩)
    · obtain ⟨j, cls, hc, n, hn, rfl⟩ := (mem_cliquePairs _ 0 q).1 hq
      refine ⟨j, cls, by rw [← Array.getElem?_toList]; exact hc, ⟨n, hn, hqx⟩, by rw [Nat.zero_add]⟩
    · simp only [Std.HashMap.getElem?_empty, reduceCtorEq] at h
  · rintro ⟨k, cls, hc, ⟨n, hn, hnx⟩, rfl⟩
    refine .inl ⟨(n, .clique k), (mem_cliquePairs _ 0 _).2 ⟨k, cls, ?_, n, hn, by rw [Nat.zero_add]⟩,
      hnx, rfl⟩
    rw [Array.getElem?_toList]; exact hc

end Ix.CompileCert.Canon
