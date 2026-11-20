import Mathlib
import IxAICore

/-!
# Exact dot products in any order, tiling or limb split

`Fx.dotRaw` is an exact integer sum, so every way a GPU may form it gives the same integer:

* `perm_sum_eq_dotRaw`, `partition_sum_eq_dotRaw`, `RTree.eval_eq_dotRaw`: any permutation of
  the products, any partition of them into partial sums, any reduction tree over them;
* `tiledDot_eq`: a sum of per-tile sums, for every tile size;
* `limbDot_eq`: operands split into base-256 limbs (low limbs in `[0, 256)`, a signed top limb),
  multiplied plane by plane and recombined with weights `256^(p+q)`; this is what an int8
  tensor-core GEMM computes, and `limbs_one_range` gives the 16-bit operand bound under which
  every limb is a signed or unsigned byte;
* `blockReduce_eq`: the reduction the CUDA kernels run, lanes striding over the terms and a
  halving tree across lanes, for every lane count `2^logLanes`.
-/

namespace IxAIGpu
open IxAICore Finset

/-! ## Sums over ranges -/

theorem foldl_add_eq (f : Nat → Int) (l : List Nat) (a : Int) :
    l.foldl (fun acc k => acc + f k) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons k l ih => simp [ih, add_assoc]

theorem sum_map_range (n : Nat) (f : Nat → Int) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem sum_filter_map (p : Nat → Bool) (f : Nat → Int) (l : List Nat) :
    ((l.filter p).map f).sum = (l.map fun k => if p k then f k else 0).sum := by
  induction l with
  | nil => simp
  | cons k l ih => by_cases h : p k <;> simp [h, ih]

theorem sum_zipWith_add (a b : List Int) (h : a.length = b.length) :
    (List.zipWith (· + ·) a b).sum = a.sum + b.sum := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.zipWith_cons_cons, List.sum_cons]
      rw [ih b (by simpa using h)]
      ring

/-! ## Exact dot products -/

/-- The exact products `Fx.dotRaw` adds. -/
def products (xs ys : List Fx) : List Int := List.zipWith (fun a b => a.raw * b.raw) xs ys

theorem dotRaw_eq_sum (xs ys : List Fx) : Fx.dotRaw xs ys = (products xs ys).sum := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a as ih =>
    cases ys with
    | nil => rfl
    | cons b bs => simp [Fx.dotRaw, products, ih]

/-- **Any order.** -/
theorem perm_sum_eq_dotRaw {xs ys : List Fx} {l : List Int} (h : l.Perm (products xs ys)) :
    l.sum = Fx.dotRaw xs ys := by
  rw [dotRaw_eq_sum, h.sum_eq]

/-- **Any partition** of the products into partial sums, added in any grouping. -/
theorem partition_sum_eq_dotRaw {xs ys : List Fx} {parts : List (List Int)}
    (h : parts.flatten.Perm (products xs ys)) : (parts.map List.sum).sum = Fx.dotRaw xs ys := by
  rw [← List.sum_flatten, perm_sum_eq_dotRaw h]

/-- A reduction tree: every leaf a term, every node one addition. -/
inductive RTree where
  | leaf (v : Int)
  | node (l r : RTree)

def RTree.leaves : RTree → List Int
  | .leaf v => [v]
  | .node l r => l.leaves ++ r.leaves

def RTree.eval : RTree → Int
  | .leaf v => v
  | .node l r => l.eval + r.eval

theorem RTree.eval_eq_sum (t : RTree) : t.eval = t.leaves.sum := by
  induction t with
  | leaf v => simp [eval, leaves]
  | node l r ihl ihr => simp [eval, leaves, ihl, ihr]

/-- **Any reduction tree** whose leaves are the products, in any order. -/
theorem RTree.eval_eq_dotRaw {xs ys : List Fx} (t : RTree) (h : t.leaves.Perm (products xs ys)) :
    t.eval = Fx.dotRaw xs ys := by
  rw [t.eval_eq_sum, perm_sum_eq_dotRaw h]

/-- Consecutive tiles of `size` elements (one tile when `size = 0`). -/
def tiles {α : Type} (size : Nat) (l : List α) : List (List α) :=
  if _h : 0 < size ∧ l ≠ [] then l.take size :: tiles size (l.drop size) else [l]
termination_by l.length
decreasing_by
  simp only [List.length_drop]
  have := List.length_pos_of_ne_nil ‹0 < size ∧ l ≠ []›.2
  omega

theorem flatten_tiles {α : Type} (size : Nat) (l : List α) : (tiles size l).flatten = l := by
  rw [tiles]
  split
  · rename_i h
    rw [List.flatten_cons, flatten_tiles size (l.drop size)]
    exact List.take_append_drop size l
  · simp
termination_by l.length
decreasing_by
  rename_i h
  have := List.length_pos_of_ne_nil h.2
  have := h.1
  simp only [List.length_drop]
  omega

/-- A tiled dot product: per-tile exact sums, then their sum. -/
def tiledDot (tile : Nat) (xs ys : List Fx) : Int :=
  ((tiles tile (products xs ys)).map List.sum).sum

/-- **Tiling.** Every tile size gives `dotRaw`. -/
theorem tiledDot_eq (tile : Nat) (xs ys : List Fx) : tiledDot tile xs ys = Fx.dotRaw xs ys :=
  partition_sum_eq_dotRaw (by rw [flatten_tiles])

/-! ## Limbs -/

/-- `k + 1` base-256 limbs, least significant first: `k` limbs in `[0, 256)` and a signed top
limb. -/
def limbs : Nat → Int → List Int
  | 0, x => [x]
  | k + 1, x => x % 256 :: limbs k (x / 256)

def limb (k p : Nat) (x : Int) : Int := (limbs k x).getD p 0

theorem limb_expand (k : Nat) (x : Int) : x = ∑ p ∈ range (k + 1), 256 ^ p * limb k p x := by
  induction k generalizing x with
  | zero => simp [limb, limbs]
  | succ k ih =>
    rw [Finset.sum_range_succ']
    have h : ∀ p, limb (k + 1) (p + 1) x = limb k p (x / 256) := fun p => by simp [limb, limbs]
    simp only [h, pow_succ]
    have h0 : limb (k + 1) 0 x = x % 256 := by simp [limb, limbs]
    rw [h0]
    have e : ∑ p ∈ range (k + 1), 256 ^ p * 256 * limb k p (x / 256) =
        256 * ∑ p ∈ range (k + 1), 256 ^ p * limb k p (x / 256) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [e, ← ih]
    simp
    omega

/-- The 16-bit case: two limbs, an unsigned low byte and a signed high byte. -/
theorem limbs_one_range (x : Int) (h : -32768 ≤ x ∧ x < 32768) :
    0 ≤ limb 1 0 x ∧ limb 1 0 x < 256 ∧ -128 ≤ limb 1 1 x ∧ limb 1 1 x < 128 := by
  simp only [limb, limbs]
  simp
  omega

/-- One limb plane: the exact dot product of limb `p` of `xs` with limb `q` of `ys`. -/
def planeDot (k p q : Nat) (xs ys : List Fx) : Int :=
  (List.zipWith (fun a b => limb k p a.raw * limb k q b.raw) xs ys).sum

/-- Every limb plane, recombined with weight `256^(p+q)`. -/
def limbDot (k : Nat) (xs ys : List Fx) : Int :=
  ∑ p ∈ range (k + 1), ∑ q ∈ range (k + 1), 256 ^ (p + q) * planeDot k p q xs ys

/-- **Limbs.** For every limb count, the recombined planes are `dotRaw`. -/
theorem limbDot_eq (k : Nat) (xs ys : List Fx) : limbDot k xs ys = Fx.dotRaw xs ys := by
  induction xs generalizing ys with
  | nil => simp [limbDot, planeDot, Fx.dotRaw]
  | cons a as ih =>
    cases ys with
    | nil => simp [limbDot, planeDot, Fx.dotRaw]
    | cons b bs =>
      have hcons : limbDot k (a :: as) (b :: bs) =
          (∑ p ∈ range (k + 1), 256 ^ p * limb k p a.raw) *
            (∑ q ∈ range (k + 1), 256 ^ q * limb k q b.raw) + limbDot k as bs := by
        simp only [limbDot, planeDot, List.zipWith_cons_cons, List.sum_cons, Finset.sum_mul_sum,
          mul_add, Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros
        rw [pow_add]; ring
      rw [hcons, ih, ← limb_expand, ← limb_expand]
      simp [Fx.dotRaw]

/-! ## The kernels' reduction -/

/-- Launch geometry of a reduction: `2^logLanes` lanes. -/
structure Geometry where
  logLanes : Nat

def Geometry.lanes (g : Geometry) : Nat := 2 ^ g.logLanes

/-- What lane `t` of `T` accumulates: terms `t, t + T, t + 2T, … < K`, left to right. -/
def threadSum (T K t : Nat) (f : Nat → Int) : Int :=
  ((List.range K).filter fun k => k % T == t).foldl (fun acc k => acc + f k) 0

/-- The shuffle tree over `2^n` lane values: lane `t` adds lane `t + 2^(n-1)`, halving until one
value is left. -/
def warpTree : Nat → List Int → Int
  | 0, l => l.headD 0
  | n + 1, l => warpTree n (List.zipWith (· + ·) (l.take (2 ^ n)) (l.drop (2 ^ n)))

/-- A reduction of `K` terms as one warp of the CUDA kernels computes it. -/
def blockReduce (g : Geometry) (f : Nat → Int) (K : Nat) : Int :=
  warpTree g.logLanes ((List.range g.lanes).map fun t => threadSum g.lanes K t f)

theorem warpTree_eq_sum (n : Nat) (l : List Int) (h : l.length = 2 ^ n) : warpTree n l = l.sum := by
  induction n generalizing l with
  | zero =>
    match l, h with
    | [a], _ => simp [warpTree]
  | succ n ih =>
    simp only [warpTree]
    rw [ih _ (by simp [List.length_zipWith, h, pow_succ]; omega)]
    rw [sum_zipWith_add _ _ (by simp [h, pow_succ]; omega)]
    rw [← List.sum_append, List.take_append_drop]

theorem threadSum_eq (T K t : Nat) (f : Nat → Int) :
    threadSum T K t f = ∑ k ∈ range K, if k % T = t then f k else 0 := by
  rw [threadSum, foldl_add_eq, zero_add, sum_filter_map, sum_map_range]
  simp

/-- **The kernels' reduction is the exact sum**, for every lane count. -/
theorem blockReduce_eq (g : Geometry) (f : Nat → Int) (K : Nat) :
    blockReduce g f K = ∑ k ∈ range K, f k := by
  rw [blockReduce, warpTree_eq_sum _ _ (by simp [Geometry.lanes]), sum_map_range]
  simp only [threadSum_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_ite_eq]
  have : k % g.lanes < g.lanes := Nat.mod_lt _ (by simp [Geometry.lanes])
  simp [this]

end IxAIGpu
