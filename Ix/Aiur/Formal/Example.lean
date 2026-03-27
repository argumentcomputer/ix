module
public import Ix.Aiur.Formal.ExampleMainSem

/-!
# Aiur Formal Verification — Example Proofs

Proves properties about the Aiur programs defined across two toplevels:
- `ExampleBase.lean`: `Pair`, `Expr`, `eval`, `swap` → `ExampleBaseSem.lean`
- `ExampleMain.lean`: `ExprList`, `list_sum`, `assert_eval` → `ExampleMainSem.lean`
-/

public section

open Aiur exampleBase exampleMain

-- ============================================================
-- 1. Eval is deterministic
-- ============================================================

theorem eval_deterministic {e : Expr} {v₁ v₂ : G} {P₁ P₂ : Prop}
    (h₁ : eval e v₁ P₁) (h₂ : eval e v₂ P₂)
    (hP₁ : P₁) (hP₂ : P₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ P₂ with
  | path0 => cases h₂; rfl
  | path1 _ _ ih₁ ih₂ =>
    cases h₂ with
    | path1 h₂a h₂b =>
      show _ + _ = _ + _
      congr 1
      · exact ih₁ h₂a hP₁.1 hP₂.1
      · exact ih₂ h₂b hP₁.2 hP₂.2
  | path2 _ ih =>
    cases h₂ with
    | path2 h₂a =>
      show (0 : G) - _ = (0 : G) - _
      congr 1; exact ih h₂a hP₁ hP₂

-- ============================================================
-- 2. Eval is total
-- ============================================================

theorem eval_total (e : Expr) :
    ∃ (v : G) (P : Prop), eval e v P ∧ P := by
  induction e with
  | Lit n => exact ⟨n, True, .path0, trivial⟩
  | Add a b iha ihb =>
    obtain ⟨va, Pa, ha, hPa⟩ := iha
    obtain ⟨vb, Pb, hb, hPb⟩ := ihb
    exact ⟨va + vb, Pa ∧ Pb, .path1 ha hb, hPa, hPb⟩
  | Neg a iha =>
    obtain ⟨va, Pa, ha, hPa⟩ := iha
    exact ⟨(0 : G) - va, Pa, .path2 ha, hPa⟩

-- ============================================================
-- 3. Swap is an involution
-- ============================================================

theorem swap_involution {p q r : Pair} {P₁ P₂ : Prop}
    (h₁ : swap p q P₁) (h₂ : swap q r P₂)
    (_ : P₁) (_ : P₂) : r = p := by
  cases h₁; cases h₂; rfl

-- ============================================================
-- 4. assert_eval semantics
-- ============================================================

theorem assert_eval_correct {e : Expr} {expected : G} {P : Prop}
    (h : assert_eval e expected () P) (hP : P) :
    ∃ v Pv, eval e v Pv ∧ Pv ∧ v = expected := by
  cases h with
  | path0 h_eval => exact ⟨_, _, h_eval, hP.1, hP.2⟩

-- ============================================================
-- 5. list_sum is deterministic (uses eval_deterministic cross-toplevel)
-- ============================================================

theorem list_sum_deterministic {xs : ExprList} {v₁ v₂ : G} {P₁ P₂ : Prop}
    (h₁ : list_sum xs v₁ P₁) (h₂ : list_sum xs v₂ P₂)
    (hP₁ : P₁) (hP₂ : P₂) : v₁ = v₂ := by
  induction h₁ generalizing v₂ P₂ with
  | path0 => cases h₂; rfl
  | path1 h₁e _ ih =>
    cases h₂ with
    | path1 h₂e h₂r =>
      show _ + _ = _ + _
      congr 1
      · exact eval_deterministic h₁e h₂e hP₁.1 hP₂.1
      · exact ih h₂r hP₁.2 hP₂.2

-- ============================================================
-- 6. Spec-based: eval matches a Lean function
-- ============================================================

def evalSpec : Expr → G
  | .Lit n => n
  | .Add a b => evalSpec a + evalSpec b
  | .Neg a => (0 : G) - evalSpec a

theorem eval_sound {e : Expr} {v : G} {P : Prop}
    (h : eval e v P) (hP : P) : v = evalSpec e := by
  induction h with
  | path0 => rfl
  | path1 _ _ ih₁ ih₂ => simp only [evalSpec, ih₁ hP.1, ih₂ hP.2]
  | path2 _ ih => simp only [evalSpec, ih hP]

-- ============================================================
-- 7. Mutual types: tree_sum / forest_sum match Lean specs
-- ============================================================

mutual
def treeSpec : Tree → G
  | .Leaf n => n
  | .Node n f => n + forestSpec f

def forestSpec : Forest → G
  | .Empty => 0
  | .Cons t rest => treeSpec t + forestSpec rest
end

mutual
def tree_sum_sound {t : Tree} {v : G} {P : Prop}
    (h : tree_sum t v P) (hP : P) : v = treeSpec t := by
  cases h with
  | path0 => rfl
  | path1 hf => simp only [treeSpec, forest_sum_sound hf hP]

def forest_sum_sound {f : Forest} {v : G} {P : Prop}
    (h : forest_sum f v P) (hP : P) : v = forestSpec f := by
  cases h with
  | path0 => rfl
  | path1 ht hf => simp only [forestSpec, tree_sum_sound ht hP.1, forest_sum_sound hf hP.2]
end

-- ============================================================
-- 8. Mutual recursion: is_even and is_odd constraints are exclusive
--
-- The path0 constraint (`G.eqZero n = 1`) and the path1 constraint
-- (`G.eqZero n = 0`) cannot both hold. This means path0 and path1
-- can never fire for the same `n`, which is what makes the mutual
-- semantic propositions deterministic.
-- ============================================================

theorem even_odd_path_exclusive {n : G}
    (h0 : G.eqZero n = (1 : G)) (h1 : G.eqZero n = (0 : G)) : False :=
  absurd (h0.symm.trans h1) G.one_ne_zero

theorem even_zero {n r : G} {P : Prop}
    (h : is_even n r P) (hP : P) (hz : G.eqZero n = (1 : G)) :
    r = (1 : G) := by
  cases h with
  | path0 => rfl
  | path1 _ => exact (even_odd_path_exclusive hz hP.2).elim

theorem odd_zero {n r : G} {P : Prop}
    (h : is_odd n r P) (hP : P) (hz : G.eqZero n = (1 : G)) :
    r = (0 : G) := by
  cases h with
  | path0 => rfl
  | path1 _ => exact (even_odd_path_exclusive hz hP.2).elim

end
