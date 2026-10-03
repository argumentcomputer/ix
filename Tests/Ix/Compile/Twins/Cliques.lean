/-
  Clique twin families: definition and theorem cliques, each in two or
  three presentations (function order permuted; a regrouping where the
  language allows one; a renaming in one family). The data the cliques
  range over live in `Common`, outside the presentations, so that only the
  clique's own presentation varies (design document §5.6: the earlier
  inductive-predicate measurement permuted the inductives too).

  Family index (design document §5; the twins gate `Tests.Ix.Compile.Twins`
  lists the presentations and their name maps):

  - `SA`   structural, two functions on one type former (Nat); P2 renames,
           P3 regroups with `where`
  - `S3`   structural, three functions on one type former
  - `SM`   structural over a mutual inductive, one function per type former
  - `SX`   structural over a mutual inductive, two functions on one type
           former and one on the other
  - `WD`   well-founded, two functions, default `decreasing_by`
  - `W3`   well-founded, three functions, default `decreasing_by`
           (a lexicographic measure)
  - `WG`   well-founded, two functions whose measure GuessLex must pick
           among two non-uniform combinations (the GUESSLEX probe)
  - `WT`   well-founded, explicit `termination_by`
  - `WB`   well-founded, explicit `termination_by` and `decreasing_by`
  - `PF`   `partial_fixpoint`, three functions
  - `TS`   theorems meant as structural, two on one type former; Lean
           elaborates them by well-founded recursion (`odT (n+1)` calls
           `evT (n+1)`), with GuessLex function-index measures
  - `TM`   theorems by mutual structural recursion over a mutual inductive
  - `TW`   theorems by mutual well-founded recursion
  - `IP`   theorems by structural recursion over a mutual inductive
           predicate (the "below" matchers)
  - `TP`   theorems by mutual structural recursion, two on one type former
  - `SP`   structural, fixed parameters in another order per function
  - `WP`   well-founded, fixed parameters in another order per function
  - `PT`   `partial def` clique (kernel-level SCC; control)
  - `WA`   well-founded, three functions, one making two calls with a
           goal-specific `decreasing_by` (the TACTIC-ASYM probe)
  - `TN`   theorems by mutual structural recursion with identical
           statements (the NOSPEC probe)
  - `RF`   structural over a reflexive inductive (a field `Nat → Rt`): paths
           into `below` through an application (A5f)
  - `NS`   structural over a nested inductive (`Rose`, `List Rose`), two
           functions on `Rose` and one on the nested `List Rose` (A5f)
  - `LI`   `inductive_fixpoint`, three predicates (the lattice route) (A5f)
  - `LC`   `coinductive_fixpoint`, two predicates (A5f)
  - `PU`   `partial_fixpoint` with user-written monotonicity proofs: one
           tactic block that unfolds the order, one explicit lemma chain (A5f)
  - `RA`   structural, two candidate recursive arguments per function and
           no `termination_by structural` (the RECARG probe) (A5f)
  - `WH`   well-founded, fixed proofs in another order per function and a
           `decreasing_by` that picks a hypothesis by context order (the
           TACTIC-ASYM probe within one goal) (A5f)
  - `TR`   theorems by mutual structural recursion, identical statements,
           different recursion (Q6's recovered specification) (A5f)
  - `TQ`   theorems by mutual well-founded recursion, identical statements,
           different recursion (Q6's recovered specification) (A5f)
  - `WU`   well-founded, a user value of exactly the clique's packing type
           (the position restriction's negative control) (A5f)
-/

namespace Tests.Ix.Compile.Twins.Cliques

namespace Common

mutual
inductive Tr where
  | leaf : Nat → Tr
  | node : Fo → Tr
inductive Fo where
  | nil : Fo
  | cons : Tr → Fo → Fo
end

mutual
inductive EvP : Nat → Prop where
  | z : EvP 0
  | s : OdP n → EvP (n + 1)
inductive OdP : Nat → Prop where
  | s : EvP n → OdP (n + 1)
end

def ev : Nat → Bool
  | 0 => true
  | n + 1 => !ev n

/-- A reflexive inductive (family `RF`). -/
inductive Rt where
  | leaf : Nat → Rt
  | node : (Nat → Rt) → Rt

/-- A nested inductive (family `NS`). -/
inductive Rose where
  | node : Nat → List Rose → Rose

/-- A user function on the packing type of a two-function well-founded
clique over `Nat` (family `WU`). -/
def pv : PSum Nat Nat → Nat
  | .inl a => a
  | .inr b => b + 1

end Common

open Common

/-! ## SA: structural, two functions on one type former -/
namespace SA
namespace P0
mutual
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
end
theorem ev4 : ev 4 = true := rfl
end P0
namespace P1
mutual
def od : Nat → Bool
  | 0 => false
  | n + 1 => ev n
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
end
theorem ev4 : ev 4 = true := rfl
end P1
-- renaming of members and binders
namespace P2
mutual
def isE : Nat → Bool
  | 0 => true
  | k + 1 => isO k
def isO : Nat → Bool
  | 0 => false
  | k + 1 => isE k
end
theorem ev4 : isE 4 = true := rfl
end P2
-- regrouping: `od` as a `where` function of `ev`
namespace P3
def ev : Nat → Bool
  | 0 => true
  | n + 1 => od n
where
  od : Nat → Bool
    | 0 => false
    | n + 1 => ev n
theorem ev4 : ev 4 = true := rfl
end P3
end SA

/-! ## S3: structural, three functions on one type former -/
namespace S3
namespace P0
mutual
def m0 : Nat → Nat
  | 0 => 0
  | n + 1 => m1 n + 1
def m1 : Nat → Nat
  | 0 => 10
  | n + 1 => m2 n + 2
def m2 : Nat → Nat
  | 0 => 20
  | n + 1 => m0 n + 3
end
end P0
namespace P1
mutual
def m2 : Nat → Nat
  | 0 => 20
  | n + 1 => m0 n + 3
def m0 : Nat → Nat
  | 0 => 0
  | n + 1 => m1 n + 1
def m1 : Nat → Nat
  | 0 => 10
  | n + 1 => m2 n + 2
end
end P1
namespace P2
mutual
def m1 : Nat → Nat
  | 0 => 10
  | n + 1 => m2 n + 2
def m0 : Nat → Nat
  | 0 => 0
  | n + 1 => m1 n + 1
def m2 : Nat → Nat
  | 0 => 20
  | n + 1 => m0 n + 3
end
end P2
end S3

/-! ## SM: structural over a mutual inductive, one function per type former -/
namespace SM
namespace P0
mutual
def szTr : Tr → Nat
  | .leaf n => n + 1
  | .node f => szFo f + 1
def szFo : Fo → Nat
  | .nil => 0
  | .cons t f => szTr t + szFo f
end
theorem sz : szTr (.node (.cons (.leaf 2) .nil)) = 4 := rfl
end P0
namespace P1
mutual
def szFo : Fo → Nat
  | .nil => 0
  | .cons t f => szTr t + szFo f
def szTr : Tr → Nat
  | .leaf n => n + 1
  | .node f => szFo f + 1
end
theorem sz : szTr (.node (.cons (.leaf 2) .nil)) = 4 := rfl
end P1
end SM

/-! ## SX: structural over a mutual inductive, two functions on `Fo` -/
namespace SX
namespace P0
mutual
def cTr : Tr → Nat
  | .leaf _ => 1
  | .node f => cFo f + lFo f
def cFo : Fo → Nat
  | .nil => 0
  | .cons t f => cTr t + cFo f
def lFo : Fo → Nat
  | .nil => 7
  | .cons t f => lFo f + cTr t + 1
end
end P0
namespace P1
mutual
def lFo : Fo → Nat
  | .nil => 7
  | .cons t f => lFo f + cTr t + 1
def cTr : Tr → Nat
  | .leaf _ => 1
  | .node f => cFo f + lFo f
def cFo : Fo → Nat
  | .nil => 0
  | .cons t f => cTr t + cFo f
end
end P1
namespace P2
mutual
def cFo : Fo → Nat
  | .nil => 0
  | .cons t f => cTr t + cFo f
def lFo : Fo → Nat
  | .nil => 7
  | .cons t f => lFo f + cTr t + 1
def cTr : Tr → Nat
  | .leaf _ => 1
  | .node f => cFo f + lFo f
end
end P2
end SX

/-! ## WD: well-founded, two functions, default `decreasing_by` -/
namespace WD
namespace P0
mutual
def wa (n : Nat) : Nat := if h : n ≤ 1 then n else wb (n - 2) + 1
def wb (n : Nat) : Nat := if h : n = 0 then 0 else wa (n - 1) + 2
end
end P0
namespace P1
mutual
def wb (n : Nat) : Nat := if h : n = 0 then 0 else wa (n - 1) + 2
def wa (n : Nat) : Nat := if h : n ≤ 1 then n else wb (n - 2) + 1
end
end P1
-- regrouping: `wb` as a `where` function of `wa`
namespace P2
def wa (n : Nat) : Nat := if h : n ≤ 1 then n else wb (n - 2) + 1
where
  wb (n : Nat) : Nat := if h : n = 0 then 0 else wa (n - 1) + 2
end P2
end WD

/-! ## W3: well-founded, three functions, lexicographic measure -/
namespace W3
namespace P0
mutual
def ga (m n : Nat) : Nat := if h : m = 0 then n else gb (m - 1) (n + 1)
def gb (m n : Nat) : Nat := if h : n = 0 then m else gc m (n - 1)
def gc (m n : Nat) : Nat := if h : m = 0 then 0 else ga (m - 1) n
end
end P0
namespace P1
mutual
def gc (m n : Nat) : Nat := if h : m = 0 then 0 else ga (m - 1) n
def ga (m n : Nat) : Nat := if h : m = 0 then n else gb (m - 1) (n + 1)
def gb (m n : Nat) : Nat := if h : n = 0 then m else gc m (n - 1)
end
end P1
namespace P2
mutual
def gb (m n : Nat) : Nat := if h : n = 0 then m else gc m (n - 1)
def ga (m n : Nat) : Nat := if h : m = 0 then n else gb (m - 1) (n + 1)
def gc (m n : Nat) : Nat := if h : m = 0 then 0 else ga (m - 1) n
end
end P2
end W3

/-! ## WG: the GuessLex probe. Neither argument position alone works for
both functions; `(ga.x, gb.y)` and `(ga.y, gb.x)` both do. -/
namespace WG
namespace P0
mutual
def ga (x y : Nat) : Nat := if h : x = 0 ∨ y = 0 then 0 else gb (y - 1) (x - 1)
def gb (x y : Nat) : Nat := if h : x = 0 ∨ y = 0 then 1 else ga (y - 1) (x - 1)
end
end P0
namespace P1
mutual
def gb (x y : Nat) : Nat := if h : x = 0 ∨ y = 0 then 1 else ga (y - 1) (x - 1)
def ga (x y : Nat) : Nat := if h : x = 0 ∨ y = 0 then 0 else gb (y - 1) (x - 1)
end
end P1
end WG

/-! ## WT: well-founded, explicit `termination_by` -/
namespace WT
namespace P0
mutual
def ta (n : Nat) : Nat := if h : n ≤ 1 then n else tb (n - 2) + 1
termination_by n
def tb (n : Nat) : Nat := if h : n = 0 then 0 else ta (n - 1) + 2
termination_by n
end
end P0
namespace P1
mutual
def tb (n : Nat) : Nat := if h : n = 0 then 0 else ta (n - 1) + 2
termination_by n
def ta (n : Nat) : Nat := if h : n ≤ 1 then n else tb (n - 2) + 1
termination_by n
end
end P1
end WT

/-! ## WB: well-founded, `termination_by` and `decreasing_by` -/
namespace WB
namespace P0
mutual
def ba (n : Nat) : Nat := if h : n ≤ 1 then n else bb (n - 2) + 1
termination_by n
decreasing_by omega
def bb (n : Nat) : Nat := if h : n = 0 then 0 else ba (n - 1) + 2
termination_by n
decreasing_by omega
end
end P0
namespace P1
mutual
def bb (n : Nat) : Nat := if h : n = 0 then 0 else ba (n - 1) + 2
termination_by n
decreasing_by omega
def ba (n : Nat) : Nat := if h : n ≤ 1 then n else bb (n - 2) + 1
termination_by n
decreasing_by omega
end
end P1
end WB

/-! ## PF: `partial_fixpoint`, three functions -/
namespace PF
namespace P0
mutual
def pa (n : Nat) : Option Nat := if n = 0 then some 0 else pb (n - 1)
partial_fixpoint
def pb (n : Nat) : Option Nat := if n = 0 then some 1 else do
  let r ← pc (n - 1)
  pure (r + 1)
partial_fixpoint
def pc (n : Nat) : Option Nat := if n > 100 then none else pa (n + 2)
partial_fixpoint
end
end P0
namespace P1
mutual
def pc (n : Nat) : Option Nat := if n > 100 then none else pa (n + 2)
partial_fixpoint
def pa (n : Nat) : Option Nat := if n = 0 then some 0 else pb (n - 1)
partial_fixpoint
def pb (n : Nat) : Option Nat := if n = 0 then some 1 else do
  let r ← pc (n - 1)
  pure (r + 1)
partial_fixpoint
end
end P1
namespace P2
mutual
def pb (n : Nat) : Option Nat := if n = 0 then some 1 else do
  let r ← pc (n - 1)
  pure (r + 1)
partial_fixpoint
def pa (n : Nat) : Option Nat := if n = 0 then some 0 else pb (n - 1)
partial_fixpoint
def pc (n : Nat) : Option Nat := if n > 100 then none else pa (n + 2)
partial_fixpoint
end
end P2
end PF

/-! ## TS: theorems by mutual structural recursion, two on one type former -/
namespace TS
namespace P0
mutual
theorem evT : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := odT n
    simp only [Nat.mul_succ, ev] at *
    simpa using this
theorem odT : ∀ n, ev (2 * n + 1) = false
  | 0 => rfl
  | n + 1 => by
    have := evT (n + 1)
    simp only [ev] at *
    simpa using this
end
end P0
namespace P1
mutual
theorem odT : ∀ n, ev (2 * n + 1) = false
  | 0 => rfl
  | n + 1 => by
    have := evT (n + 1)
    simp only [ev] at *
    simpa using this
theorem evT : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := odT n
    simp only [Nat.mul_succ, ev] at *
    simpa using this
end
end P1
end TS

/-! ## TM: theorems by mutual structural recursion over a mutual inductive -/
namespace TM
mutual
def cTr : Tr → Nat
  | .leaf _ => 1
  | .node f => cFo f + 1
def cFo : Fo → Nat
  | .nil => 1
  | .cons t f => cTr t + cFo f
end
namespace P0
mutual
theorem pTr : ∀ t, 0 < cTr t
  | .leaf _ => Nat.one_pos
  | .node f => Nat.lt_of_lt_of_le (pFo f) (Nat.le_succ _)
theorem pFo : ∀ f, 0 < cFo f
  | .nil => Nat.one_pos
  | .cons t _ => Nat.lt_of_lt_of_le (pTr t) (Nat.le_add_right _ _)
end
end P0
namespace P1
mutual
theorem pFo : ∀ f, 0 < cFo f
  | .nil => Nat.one_pos
  | .cons t _ => Nat.lt_of_lt_of_le (pTr t) (Nat.le_add_right _ _)
theorem pTr : ∀ t, 0 < cTr t
  | .leaf _ => Nat.one_pos
  | .node f => Nat.lt_of_lt_of_le (pFo f) (Nat.le_succ _)
end
end P1
end TM

/-! ## TW: theorems by mutual well-founded recursion -/
namespace TW
namespace P0
mutual
theorem wa (n : Nat) : n % 2 = 0 → ev n = true := fun h =>
  if h0 : n = 0 then by subst h0; rfl
  else by
    have := wb (n - 1) (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [ev, Nat.add_sub_cancel] at *
    simp [this]
termination_by n
theorem wb (n : Nat) : n % 2 = 1 → ev n = false := fun h =>
  if h0 : n = 0 then by omega
  else by
    have := wa (n - 1) (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [ev, Nat.add_sub_cancel] at *
    simp [this]
termination_by n
end
end P0
namespace P1
mutual
theorem wb (n : Nat) : n % 2 = 1 → ev n = false := fun h =>
  if h0 : n = 0 then by omega
  else by
    have := wa (n - 1) (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [ev, Nat.add_sub_cancel] at *
    simp [this]
termination_by n
theorem wa (n : Nat) : n % 2 = 0 → ev n = true := fun h =>
  if h0 : n = 0 then by subst h0; rfl
  else by
    have := wb (n - 1) (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [ev, Nat.add_sub_cancel] at *
    simp [this]
termination_by n
end
end P1
end TW

/-! ## IP: structural recursion over a mutual inductive predicate -/
namespace IP
namespace P0
mutual
theorem evM : EvP n → n % 2 = 0
  | .z => rfl
  | .s h => by have := odM h; omega
theorem odM : OdP n → n % 2 = 1
  | .s h => by have := evM h; omega
end
end P0
namespace P1
mutual
theorem odM : OdP n → n % 2 = 1
  | .s h => by have := evM h; omega
theorem evM : EvP n → n % 2 = 0
  | .z => rfl
  | .s h => by have := odM h; omega
end
end P1
end IP

/-! ## TP: theorems by mutual structural recursion, two on one type former
(each calls the other at the structurally smaller argument) -/
namespace TP
namespace P0
mutual
theorem sa : ∀ n, ev (n + n) = true
  | 0 => rfl
  | n + 1 => by
    have h := sb n
    rw [show n + 1 + (n + 1) = n + n + 1 + 1 by omega, ev.eq_2, h]; rfl
theorem sb : ∀ n, ev (n + n + 1) = false
  | 0 => rfl
  | n + 1 => by
    have h := sa n
    rw [show n + 1 + (n + 1) + 1 = n + n + 1 + 1 + 1 by omega, ev.eq_2, ev.eq_2, ev.eq_2, h]
    rfl
end
end P0
namespace P1
mutual
theorem sb : ∀ n, ev (n + n + 1) = false
  | 0 => rfl
  | n + 1 => by
    have h := sa n
    rw [show n + 1 + (n + 1) + 1 = n + n + 1 + 1 + 1 by omega, ev.eq_2, ev.eq_2, ev.eq_2, h]
    rfl
theorem sa : ∀ n, ev (n + n) = true
  | 0 => rfl
  | n + 1 => by
    have h := sb n
    rw [show n + 1 + (n + 1) = n + n + 1 + 1 by omega, ev.eq_2, h]; rfl
end
end P1
end TP

/-! ## SP: structural, fixed parameters in a different order per function -/
namespace SP
namespace P0
mutual
def fa (k : Nat) (b : Bool) : Nat → Nat
  | 0 => k
  | n + 1 => fb b k n + 1
def fb (b : Bool) (k : Nat) : Nat → Nat
  | 0 => if b then 1 else 0
  | n + 1 => fa k b n + 2
end
end P0
namespace P1
mutual
def fb (b : Bool) (k : Nat) : Nat → Nat
  | 0 => if b then 1 else 0
  | n + 1 => fa k b n + 2
def fa (k : Nat) (b : Bool) : Nat → Nat
  | 0 => k
  | n + 1 => fb b k n + 1
end
end P1
end SP

/-! ## WP: well-founded, fixed parameters in a different order per function -/
namespace WP
namespace P0
mutual
def ha (k : Nat) (b : Bool) (n : Nat) : Nat := if h : n ≤ 1 then k else hb b k (n - 2) + 1
def hb (b : Bool) (k : Nat) (n : Nat) : Nat :=
  if h : n = 0 then (if b then 1 else 0) else ha k b (n - 1) + 2
end
end P0
namespace P1
mutual
def hb (b : Bool) (k : Nat) (n : Nat) : Nat :=
  if h : n = 0 then (if b then 1 else 0) else ha k b (n - 1) + 2
def ha (k : Nat) (b : Bool) (n : Nat) : Nat := if h : n ≤ 1 then k else hb b k (n - 2) + 1
end
end P1
end WP

/-! ## PT: `partial def` clique (a kernel-level SCC through `_unsafe_rec`) -/
namespace PT
namespace P0
mutual
partial def qa (n : Nat) : Nat := if n = 0 then 0 else qb (n - 1) + 1
partial def qb (n : Nat) : Nat := if n = 0 then 1 else qa (n / 2) + 2
end
end P0
namespace P1
mutual
partial def qb (n : Nat) : Nat := if n = 0 then 1 else qa (n / 2) + 2
partial def qa (n : Nat) : Nat := if n = 0 then 0 else qb (n - 1) + 1
end
end P1
end PT

/-! ## WA: the TACTIC-ASYM probe. `ta` calls `tb` and `tc`; its `decreasing_by`
handles its two goals with different proofs, in goal order. Lean groups the
goals per function (`WF/Fix.lean`, `groupGoalsByFunction`), in the order of the
calls in the body, so the order of the clique does not reach the script. -/
namespace WA
namespace P0
mutual
def ta (n : Nat) : Nat := if _h : n ≤ 2 then n else tb (n - 1) + tc (n - 3)
termination_by n
decreasing_by
  · exact Nat.sub_lt (by omega) (by decide)
  · omega
def tb (n : Nat) : Nat := if h : n = 0 then 0 else ta (n - 1) + 1
termination_by n
decreasing_by omega
def tc (n : Nat) : Nat := if h : n = 0 then 1 else ta (n - 1) + 2
termination_by n
decreasing_by omega
end
end P0
namespace P1
mutual
def tc (n : Nat) : Nat := if h : n = 0 then 1 else ta (n - 1) + 2
termination_by n
decreasing_by omega
def ta (n : Nat) : Nat := if _h : n ≤ 2 then n else tb (n - 1) + tc (n - 3)
termination_by n
decreasing_by
  · exact Nat.sub_lt (by omega) (by decide)
  · omega
def tb (n : Nat) : Nat := if h : n = 0 then 0 else ta (n - 1) + 1
termination_by n
decreasing_by omega
end
end P1
end WA

/-! ## TN: the NOSPEC probe. Two theorems with identical statements, each
proved by structural recursion through the other: the statements tie, so
Q6's first source cannot order the clique. -/
namespace TN
namespace P0
mutual
theorem na : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := nb n
    simp only [Nat.mul_succ, ev] at *
    simpa using this
theorem nb : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := na n
    simp only [Nat.mul_succ, ev] at *
    simpa using this
end
end P0
namespace P1
mutual
theorem nb : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := na n
    simp only [Nat.mul_succ, ev] at *
    simpa using this
theorem na : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := nb n
    simp only [Nat.mul_succ, ev] at *
    simpa using this
end
end P1
end TN

/-! ## RF: structural recursion over a reflexive inductive. The recursive
calls go through the field `f : Nat → Rt`, so the path into the `below`
dictionary applies the dictionary entry to the argument before projecting
into the packed motive. -/
namespace RF
namespace P0
mutual
def ra : Rt → Nat
  | .leaf n => n
  | .node f => rb (f 0) + 1
def rb : Rt → Nat
  | .leaf n => n + 1
  | .node f => ra (f 1) + rb (f 2)
end
end P0
namespace P1
mutual
def rb : Rt → Nat
  | .leaf n => n + 1
  | .node f => ra (f 1) + rb (f 2)
def ra : Rt → Nat
  | .leaf n => n
  | .node f => rb (f 0) + 1
end
end P1
-- regrouping: `rb` as a `where` function of `ra`
namespace P2
def ra : Rt → Nat
  | .leaf n => n
  | .node f => rb (f 0) + 1
where
  rb : Rt → Nat
    | .leaf n => n + 1
    | .node f => ra (f 1) + rb (f 2)
end P2
end RF

/-! ## NS: structural recursion over a nested inductive: two functions on
`Rose`, one on the nested occurrence `List Rose` (the nested block's
`below_1`/`brecOn_1`). -/
namespace NS
namespace P0
mutual
def na : Rose → Nat
  | .node n cs => n + nl cs
def nb : Rose → Nat
  | .node _ cs => nl cs + 1
def nl : List Rose → Nat
  | [] => 0
  | c :: cs => na c + nb c + nl cs
end
end P0
namespace P1
mutual
def nb : Rose → Nat
  | .node _ cs => nl cs + 1
def na : Rose → Nat
  | .node n cs => n + nl cs
def nl : List Rose → Nat
  | [] => 0
  | c :: cs => na c + nb c + nl cs
end
end P1
namespace P2
mutual
def nl : List Rose → Nat
  | [] => 0
  | c :: cs => na c + nb c + nl cs
def nb : Rose → Nat
  | .node _ cs => nl cs + 1
def na : Rose → Nat
  | .node n cs => n + nl cs
end
end P2
end NS

/-! ## LI: `inductive_fixpoint`, three predicates (the `CompleteLattice`
route: `ImplicationOrder`, `instCompleteLatticePProd`, `lfp_monotone`). -/
namespace LI
namespace P0
mutual
def la (n : Nat) : Prop := if n = 0 then True else lb (n - 1)
inductive_fixpoint
def lb (n : Nat) : Prop := if n = 0 then False else lc (n - 1) ∧ la (n - 1)
inductive_fixpoint
def lc (n : Nat) : Prop := la n ∨ lb (n + 1)
inductive_fixpoint
end
end P0
namespace P1
mutual
def lc (n : Nat) : Prop := la n ∨ lb (n + 1)
inductive_fixpoint
def la (n : Nat) : Prop := if n = 0 then True else lb (n - 1)
inductive_fixpoint
def lb (n : Nat) : Prop := if n = 0 then False else lc (n - 1) ∧ la (n - 1)
inductive_fixpoint
end
end P1
namespace P2
mutual
def lb (n : Nat) : Prop := if n = 0 then False else lc (n - 1) ∧ la (n - 1)
inductive_fixpoint
def la (n : Nat) : Prop := if n = 0 then True else lb (n - 1)
inductive_fixpoint
def lc (n : Nat) : Prop := la n ∨ lb (n + 1)
inductive_fixpoint
end
end P2
end LI

/-! ## LC: `coinductive_fixpoint`, two predicates
(`ReverseImplicationOrder`). -/
namespace LC
namespace P0
mutual
def ca (n : Nat) : Prop := cb (n + 1) ∧ n ≥ 0
coinductive_fixpoint
def cb (n : Nat) : Prop := ca (n + 1)
coinductive_fixpoint
end
end P0
namespace P1
mutual
def cb (n : Nat) : Prop := ca (n + 1)
coinductive_fixpoint
def ca (n : Nat) : Prop := cb (n + 1) ∧ n ≥ 0
coinductive_fixpoint
end
end P1
end LC

/-! ## PU: `partial_fixpoint` with user-written monotonicity proofs. `ua`'s
proof unfolds the order and projects the hypothesis `h : f ⊑ g` (an `And`
over the packing); `ub`'s is an explicit lemma chain, the shape `solveMono`
builds. Each presentation's proofs are written against its own packing, as
a user would write them. -/
namespace PU
namespace P0
mutual
def ua (n : Nat) : Option Nat := if n = 0 then some 0 else ub (n - 1)
partial_fixpoint monotonicity by
  intro f g h n
  dsimp only
  split
  · exact Lean.Order.PartialOrder.rel_refl
  · exact h.2 (n - 1)
def ub (n : Nat) : Option Nat := if n = 0 then some 1 else ua (n - 1)
partial_fixpoint monotonicity by
  apply Lean.Order.monotone_of_monotone_apply
  intro n
  apply Lean.Order.monotone_ite
  · apply Lean.Order.monotone_const
  · apply Lean.Order.monotone_apply
    apply Lean.Order.PProd.monotone_fst
    apply Lean.Order.monotone_id
end
end P0
namespace P1
mutual
def ub (n : Nat) : Option Nat := if n = 0 then some 1 else ua (n - 1)
partial_fixpoint monotonicity by
  apply Lean.Order.monotone_of_monotone_apply
  intro n
  apply Lean.Order.monotone_ite
  · apply Lean.Order.monotone_const
  · apply Lean.Order.monotone_apply
    apply Lean.Order.PProd.monotone_snd
    apply Lean.Order.monotone_id
def ua (n : Nat) : Option Nat := if n = 0 then some 0 else ub (n - 1)
partial_fixpoint monotonicity by
  intro f g h n
  dsimp only
  split
  · exact Lean.Order.PartialOrder.rel_refl
  · exact h.1 (n - 1)
end
end P1
end PU

/-! ## RA: the RECARG probe. Each function has two `Nat` arguments; the
recursion is structural on the first argument of one function together with
the second of the other, in either assignment, never on the same position
in both. Lean's `allCombinations` tries the combinations with the first
function's candidate varying slowest (`FindRecArg.lean`), so the two
presentations pick different recursive arguments. -/
namespace RA
namespace P0
mutual
def ra : Nat → Nat → Nat
  | n + 1, m + 1 => rb m n + 1
  | _, _ => 0
def rb : Nat → Nat → Nat
  | n + 1, m + 1 => ra m n + 2
  | _, _ => 1
end
end P0
namespace P1
mutual
def rb : Nat → Nat → Nat
  | n + 1, m + 1 => ra m n + 2
  | _, _ => 1
def ra : Nat → Nat → Nat
  | n + 1, m + 1 => rb m n + 1
  | _, _ => 0
end
end P1
end RA

/-! ## WH: the TACTIC-ASYM probe within one goal. The fixed parameters
include two proofs of `1 < k`, in another order per function; the decreasing
goals live in the packed function's context, whose fixed parameters follow
the first function (`FixedParams.lean`); `assumption` takes the most recent
matching hypothesis, so the proof it picks follows the clique order. `hb`'s
goals are closed by `omega`. -/
namespace WH
namespace P0
mutual
def ha (k : Nat) (h₁ : 1 < k) (h₂ : 1 < k) (n : Nat) : Nat :=
  if hn : n = 0 then 0 else hb k h₂ h₁ (n / k) + 1
termination_by n
decreasing_by all_goals (simp_wf; apply Nat.div_lt_self (by omega); assumption)
def hb (k : Nat) (g₂ : 1 < k) (g₁ : 1 < k) (n : Nat) : Nat :=
  if hn : n = 0 then 1 else ha k g₁ g₂ (n / k) + 2
termination_by n
decreasing_by all_goals (simp_wf; exact Nat.div_lt_self (by omega) (by omega))
end
end P0
namespace P1
mutual
def hb (k : Nat) (g₂ : 1 < k) (g₁ : 1 < k) (n : Nat) : Nat :=
  if hn : n = 0 then 1 else ha k g₁ g₂ (n / k) + 2
termination_by n
decreasing_by all_goals (simp_wf; exact Nat.div_lt_self (by omega) (by omega))
def ha (k : Nat) (h₁ : 1 < k) (h₂ : 1 < k) (n : Nat) : Nat :=
  if hn : n = 0 then 0 else hb k h₂ h₁ (n / k) + 1
termination_by n
decreasing_by all_goals (simp_wf; apply Nat.div_lt_self (by omega); assumption)
end
end P1
end WH

/-! ## TR: theorems by mutual structural recursion with identical statements
and different recursion (`ra` steps by one and calls `rb`; `rb` steps by two
and calls `ra`): the statements tie, the recovered specifications do not. -/
namespace TR
namespace P0
mutual
theorem ra : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := rb n
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
theorem rb : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    have := ra (n + 1)
    have h2 : 2 * (n + 2) = 2 * (n + 1) + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
end
end P0
namespace P1
mutual
theorem rb : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    have := ra (n + 1)
    have h2 : 2 * (n + 2) = 2 * (n + 1) + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
theorem ra : ∀ n, ev (2 * n) = true
  | 0 => rfl
  | n + 1 => by
    have := rb n
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
end
end P1
end TR

/-! ## TQ: theorems by mutual well-founded recursion with identical
statements and different recursion (different guards and base cases). -/
namespace TQ
namespace P0
mutual
theorem qa (n : Nat) : ev (2 * n) = true :=
  if h : n = 0 then by subst h; rfl
  else by
    have := qb (n - 1)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
termination_by n
theorem qb (n : Nat) : ev (2 * n) = true :=
  if h : n ≤ 1 then by
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  else by
    have := qa (n - 1)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
termination_by n
end
end P0
namespace P1
mutual
theorem qb (n : Nat) : ev (2 * n) = true :=
  if h : n ≤ 1 then by
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  else by
    have := qa (n - 1)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
termination_by n
theorem qa (n : Nat) : ev (2 * n) = true :=
  if h : n = 0 then by subst h; rfl
  else by
    have := qb (n - 1)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    rw [h2, ev.eq_2, ev.eq_2]
    simpa using this
termination_by n
end
end P1
end TQ

/-! ## WU: the position restriction's negative control. `wx` and `wy` build
user values of type `PSum Nat Nat`, exactly the clique's packing type, and
hand them to a user function and a user `let`: the encoding never generated
them, so transport must leave them alone. -/
namespace WU
namespace P0
mutual
def wx (n : Nat) : Nat :=
  if h : n = 0 then (let p : PSum Nat Nat := PSum.inr n; pv p) else wy (n - 1) + 1
def wy (n : Nat) : Nat := if h : n = 0 then pv (PSum.inl 3) else wx (n - 1) + 2
end
end P0
namespace P1
mutual
def wy (n : Nat) : Nat := if h : n = 0 then pv (PSum.inl 3) else wx (n - 1) + 2
def wx (n : Nat) : Nat :=
  if h : n = 0 then (let p : PSum Nat Nat := PSum.inr n; pv p) else wy (n - 1) + 1
end
end P1
end WU

end Tests.Ix.Compile.Twins.Cliques
