import IxAICommon.Hash

/-!
# Merkle roots and membership proofs

A binary BLAKE3 Merkle tree. A light client holds only a root. To use one constant from a large
store (a lemma from an FLT-sized library, say) it needs that constant plus a logarithmic-size path
to the root, never the rest of the store.

## Version 2 (`merkleRootV2`, `MerklePathV2`): the current format

The root commits to the leaf count: it is `H("merkle2/root", n, top)`, where `top` folds the
leaves level by level, joining adjacent nodes with `H("merkle2/node", ·, ·)` and carrying an
unpaired last node up unchanged. The tags are disjoint from every other domain in the pipeline.

A path carries the leaf count, the index and the siblings. `MerkleHash.verifyPath` accepts it only
if the index is below the count, the siblings are exactly the ones the tree's shape for that count
and index calls for (one per level, none where the node is the unpaired last one), and the
recomputed root matches. Proved for any hash, generic in `MerkleHash`:

* `rootOf_length`, `rootOf_ne_of_length_ne`: roots of lists of different lengths differ unless the
  root hash collides; `collision_of_rootOf_eq` produces the colliding pair of preimages.
* `verifyPath_index`: an accepted path's index is in range.
* `verifyPath_sound`: if the node and root hashes are injective, a path accepted against the root
  of `l` has count `l.length` and proves the leaf at its index of `l`.

## Version 1 (`merkleRootV1`): legacy, for re-verifying recorded roots only

Version 1 hashed an unpaired node with itself and did not commit to the leaf count, so
`[a, b, c]` and `[a, b, c, c]` had the same root, and its paths verified at out-of-range indices.
It is kept only to recompute roots recorded before version 2 (`rootsV1` in the dataset
manifests); no path check uses it.
-/

namespace IxAI

instance : Enc Unit := ⟨fun b _ => b⟩

/-! ## Version 2 -/

/-- The three hashes a tree is built from. -/
structure MerkleHash (δ : Type) where
  node : δ → δ → δ
  root : Nat → δ → δ
  empty : δ

namespace MerkleHash

variable {δ : Type} (H : MerkleHash δ)

/-- One level up: adjacent nodes joined, an unpaired last node carried up unchanged. -/
def pairUp : List δ → List δ
  | a :: b :: rest => H.node a b :: pairUp rest
  | [a] => [a]
  | [] => []

theorem pairUp_length : ∀ l : List δ, (H.pairUp l).length = (l.length + 1) / 2
  | a :: b :: rest => by
    simp only [pairUp, List.length_cons, pairUp_length rest]
    omega
  | [_] => by simp [pairUp]
  | [] => by simp [pairUp]

/-- Node `j` of the next level is the join of nodes `2j` and `2j + 1`, or node `2j` alone when it
is the unpaired last one. -/
theorem pairUp_getElem? : ∀ (l : List δ) (j : Nat),
    (H.pairUp l)[j]? = match l[2 * j]?, l[2 * j + 1]? with
      | some a, some b => some (H.node a b)
      | some a, none => some a
      | none, _ => none
  | [], j => by simp [pairUp]
  | [a], 0 => by simp [pairUp]
  | [a], j + 1 => by
    have h1 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    simp [pairUp, h1]
  | a :: b :: rest, 0 => by simp [pairUp]
  | a :: b :: rest, j + 1 => by
    have h1 : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    have h2 : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by omega
    rw [h2, h1]
    simp only [pairUp, List.getElem?_cons_succ]
    exact pairUp_getElem? rest j

/-- The top of the tree: levels folded until one node remains. -/
def top (l : List δ) : δ :=
  match l with
  | [] => H.empty
  | [a] => a
  | a :: b :: rest => top (H.pairUp (a :: b :: rest))
termination_by l.length
decreasing_by all_goals (try simp_wf); simp only [pairUp, List.length_cons, pairUp_length]; omega

/-- The root: the leaf count and the top, hashed together. -/
def rootOf (l : List δ) : δ := H.root l.length (H.top l)

/-- The siblings on the way up from leaf `i`: one per level, none at a level where the node is the
unpaired last one. -/
def path (l : List δ) (i : Nat) : List δ :=
  match l with
  | [] => []
  | [_] => []
  | a :: b :: rest =>
    (if i % 2 = 1 then [(a :: b :: rest).getD (i - 1) H.empty]
      else if i + 1 < rest.length + 2 then [(a :: b :: rest).getD (i + 1) H.empty] else []) ++
    path (H.pairUp (a :: b :: rest)) (i / 2)
termination_by l.length
decreasing_by all_goals (try simp_wf); simp only [pairUp, List.length_cons, pairUp_length]; omega

/-- Recompute the top from a node at index `i` of a level of `m` nodes, consuming exactly the
siblings the shape calls for; `none` if there are too few or too many. -/
def climb (m i : Nat) (sibs : List δ) (h : δ) : Option δ :=
  if hm : m ≤ 1 then (if sibs.isEmpty then some h else none)
  else if i % 2 = 1 then
    match sibs with
    | s :: ss => climb ((m + 1) / 2) (i / 2) ss (H.node s h)
    | [] => none
  else if i + 1 < m then
    match sibs with
    | s :: ss => climb ((m + 1) / 2) (i / 2) ss (H.node h s)
    | [] => none
  else climb ((m + 1) / 2) (i / 2) sibs h
termination_by m
decreasing_by all_goals (try simp_wf); omega

/-- Accept `leaf` at index `i` of an `n`-leaf tree with root `r`. -/
def verifyPath [DecidableEq δ] (n i : Nat) (sibs : List δ) (leaf r : δ) : Bool :=
  decide (i < n) && match H.climb n i sibs leaf with
    | some t => decide (H.root n t = r)
    | none => false

theorem verifyPath_index [DecidableEq δ] {n i : Nat} {sibs : List δ} {leaf r : δ}
    (h : H.verifyPath n i sibs leaf r = true) : i < n := by
  simp only [verifyPath, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem rootOf_length (hroot : ∀ n a m b, H.root n a = H.root m b → n = m)
    {l₁ l₂ : List δ} (h : H.rootOf l₁ = H.rootOf l₂) : l₁.length = l₂.length :=
  hroot _ _ _ _ h

theorem rootOf_ne_of_length_ne (hroot : ∀ n a m b, H.root n a = H.root m b → n = m)
    {l₁ l₂ : List δ} (h : l₁.length ≠ l₂.length) : H.rootOf l₁ ≠ H.rootOf l₂ :=
  fun e => h (H.rootOf_length hroot e)

/-- Equal roots of lists of different lengths are a collision of the root hash: two distinct
preimages, `(length, top)` of each list, with the same image. -/
theorem collision_of_rootOf_eq {l₁ l₂ : List δ} (h : H.rootOf l₁ = H.rootOf l₂)
    (hl : l₁.length ≠ l₂.length) :
    ∃ p q : Nat × δ, p ≠ q ∧ H.root p.1 p.2 = H.root q.1 q.2 :=
  ⟨(l₁.length, H.top l₁), (l₂.length, H.top l₂), fun e => hl (congrArg Prod.fst e), h⟩

theorem top_of_two_le : ∀ (l : List δ), ¬ l.length ≤ 1 → H.top l = H.top (H.pairUp l)
  | _ :: _ :: _, _ => by rw [top.eq_3]
  | [_], h => absurd (by simp) h
  | [], h => absurd (by simp) h

/-- With an injective node hash, a node that climbs from index `i` to the top of `l` is the leaf
at index `i`. -/
theorem climb_sound (hnode : ∀ a b c d, H.node a b = H.node c d → a = c ∧ b = d) :
    ∀ (k : Nat) (l : List δ), l.length ≤ k → ∀ (i : Nat) (sibs : List δ) (h : δ),
      i < l.length → H.climb l.length i sibs h = some (H.top l) → l[i]? = some h := by
  intro k
  induction k with
  | zero => intro l hk i _ _ hi; omega
  | succ k ih =>
    intro l hk i sibs h hi hc
    by_cases hm : l.length ≤ 1
    · rw [climb.eq_def, dif_pos hm] at hc
      match l, hm, hi, hc with
      | [a], _, hi, hc =>
        have hi0 : i = 0 := by simp at hi; omega
        subst hi0
        split at hc
        · simp only [Option.some.injEq] at hc
          rw [hc, top.eq_2]
          simp
        · simp at hc
      | [], _, hi, _ => simp at hi
      | _ :: _ :: _, hm, _, _ => simp at hm
    · rw [climb.eq_def, dif_neg hm, H.top_of_two_le l hm] at hc
      have hlen := H.pairUp_length l
      have hk' : (H.pairUp l).length ≤ k := by omega
      have hi' : i / 2 < (H.pairUp l).length := by omega
      have hget := H.pairUp_getElem? l (i / 2)
      rw [← hlen] at hc
      by_cases hodd : i % 2 = 1
      · rw [if_pos hodd] at hc
        match sibs, hc with
        | s :: ss, hc =>
          have hup := ih _ hk' (i / 2) ss _ hi' hc
          have e2 : 2 * (i / 2) + 1 = i := by omega
          have e1 : 2 * (i / 2) = i - 1 := by omega
          rw [e2, e1, List.getElem?_eq_getElem (by omega : i - 1 < l.length),
            List.getElem?_eq_getElem hi] at hget
          rw [hget] at hup
          simp only [Option.some.injEq] at hup
          rw [List.getElem?_eq_getElem hi, (hnode _ _ _ _ hup).2]
        | [], hc => simp at hc
      · rw [if_neg hodd] at hc
        have e1 : 2 * (i / 2) = i := by omega
        by_cases hnext : i + 1 < l.length
        · rw [if_pos hnext] at hc
          match sibs, hc with
          | s :: ss, hc =>
            have hup := ih _ hk' (i / 2) ss _ hi' hc
            rw [e1, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hnext] at hget
            rw [hget] at hup
            simp only [Option.some.injEq] at hup
            rw [List.getElem?_eq_getElem hi, (hnode _ _ _ _ hup).1]
          | [], hc => simp at hc
        · rw [if_neg hnext] at hc
          have hup := ih _ hk' (i / 2) sibs _ hi' hc
          have hnone : l[i + 1]? = none := List.getElem?_eq_none (by omega)
          rw [e1, List.getElem?_eq_getElem hi, hnone] at hget
          rw [hget] at hup
          simp only [Option.some.injEq] at hup
          rw [List.getElem?_eq_getElem hi, hup]

/-- A path accepted against the root of `l`, with injective node and root hashes, has count
`l.length` and proves the leaf at its index of `l`. -/
theorem verifyPath_sound [DecidableEq δ]
    (hnode : ∀ a b c d, H.node a b = H.node c d → a = c ∧ b = d)
    (hroot : ∀ n a m b, H.root n a = H.root m b → n = m ∧ a = b)
    {l : List δ} {n i : Nat} {sibs : List δ} {leaf : δ}
    (h : H.verifyPath n i sibs leaf (H.rootOf l) = true) : n = l.length ∧ l[i]? = some leaf := by
  simp only [verifyPath, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hi, hc⟩ := h
  split at hc
  · rename_i t ht
    have hc' := of_decide_eq_true hc
    simp only [rootOf] at hc'
    obtain ⟨hn, htop⟩ := hroot _ _ _ _ hc'
    subst hn
    rw [htop] at ht
    exact ⟨rfl, H.climb_sound hnode l.length l (Nat.le_refl _) i sibs leaf hi ht⟩
  · exact absurd hc (by simp)

end MerkleHash

/-- The BLAKE3 instance: each hash under its own domain tag. -/
def merkleV2 : MerkleHash Digest :=
  { node := fun a b => digestOf "merkle2/node" (a, b)
    root := fun n t => digestOf "merkle2/root" (n, t)
    empty := digestOf "merkle2/empty" () }

/-- The length-binding root of a list of leaves. -/
def merkleRootV2 (leaves : List Digest) : Digest := merkleV2.rootOf leaves

structure MerklePathV2 where
  count : Nat
  index : Nat
  siblings : List Digest
  deriving Repr

def merklePathV2 (leaves : List Digest) (i : Nat) : MerklePathV2 :=
  ⟨leaves.length, i, merkleV2.path leaves i⟩

def MerklePathV2.verify (p : MerklePathV2) (root leaf : Digest) : Bool :=
  merkleV2.verifyPath p.count p.index p.siblings leaf root

/-! ## Version 1 (legacy) -/

namespace MerkleV1

def hash2 (a b : Digest) : Digest := digestOf "merkle/node" (a, b)

def emptyRoot : Digest := digestOf "merkle/empty" ()

def pairUp : List Digest → List Digest
  | a :: b :: rest => hash2 a b :: pairUp rest
  | [a] => [hash2 a a]
  | [] => []

def rootAux : Nat → List Digest → Digest
  | _, [] => emptyRoot
  | _, [a] => a
  | 0, a :: _ => a
  | n + 1, l => rootAux n (pairUp l)

end MerkleV1

/-- The version 1 root, for recomputing roots recorded before version 2. It does not bind the leaf
count; never use it for a new commitment. -/
def merkleRootV1 (leaves : List Digest) : Digest := MerkleV1.rootAux leaves.length leaves

end IxAI
