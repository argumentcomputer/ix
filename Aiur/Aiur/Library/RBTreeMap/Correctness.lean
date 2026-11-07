import Aiur.HeapMono
import Aiur.Library.Bytes.Correctness

/-!
# Red-Black Tree (`RBTreeMap` / `RoleMap`) and Canonical Address Ordering Correctness

This module formalizes the mathematical specification and correctness theorems for:
1. `canon_addr_cmp`: Lexicographic and 8-chunk big-endian `UInt32` comparison over
   32-byte `Address` values (`Vector UInt8 32`), establishing that `canonAddrCmp`
   forms a `LawfulCmp` strict weak order (`irrefl`, `trans`, `asymm`, `trichotomous`, `eq_iff`).
2. `RBTree K V`: Red-black search trees over arbitrary ordered keys (`LawfulCmp cmp`),
   bridged to `BinaryTree` and `RepBinaryTree` (`HeapMono`), with Okasaki-style
   `balanceFix`, `balance`, `ins`, `rbtreeInsert`, and `rbtreeGet` / `rbtreeLookupOrDefault`.
3. Lookup and BST preservation theorems: `allKeys_balance`, `allKeys_ins`,
   `rbtree_bst_balance`, `rbtree_bst_ins`, `rbtree_bst_insert`, `balance_lookup_eq`,
   `ins_lookup_eq`, `rbtree_get_insert`, `rbtree_get_insert_self`, `rbtree_get_insert_ne`.
4. Static balanced tree construction (`buildBalancedTree` / `RoleMap` over `0..102` keys):
   `toList_buildBalancedTree`, `bst_buildBalancedTree`, `rbtreeGet_eq_some_iff_mem_toList`,
   `rbtreeGet_eq_none_iff_forall_ne`, `role_tree_get_eq_some_iff`, and `role_tree_get_eq_none_iff`.
-/

namespace Aiur.Library.RBTreeMap

open Aiur.Library.Bytes

/-! ## Strict Weak Order Comparison Class (`LawfulCmp`) -/

/-- A comparison function `cmp : K → K → Ordering` is lawful when `.eq` coincides
with equality, `.lt` is transitive, and `.gt` is the dual of `.lt`. -/
structure LawfulCmp {K : Type*} (cmp : K → K → Ordering) : Prop where
  eq_iff : ∀ x y, cmp x y = .eq ↔ x = y
  lt_trans : ∀ {x y z}, cmp x y = .lt → cmp y z = .lt → cmp x z = .lt
  gt_iff : ∀ x y, cmp x y = .gt ↔ cmp y x = .lt

namespace LawfulCmp

variable {K : Type*} {cmp : K → K → Ordering}

theorem cmp_refl (h : LawfulCmp cmp) (x : K) : cmp x x = .eq :=
  (h.eq_iff x x).mpr rfl

theorem lt_irrefl (h : LawfulCmp cmp) (x : K) : cmp x x ≠ .lt := by
  rw [h.cmp_refl x]; decide

theorem gt_irrefl (h : LawfulCmp cmp) (x : K) : cmp x x ≠ .gt := by
  rw [h.cmp_refl x]; decide

theorem lt_asymm (h : LawfulCmp cmp) {x y : K} (hxy : cmp x y = .lt) : cmp y x ≠ .lt :=
  fun hyx => h.lt_irrefl x (h.lt_trans hxy hyx)

theorem lt_ne (h : LawfulCmp cmp) {x y : K} (hxy : cmp x y = .lt) : x ≠ y := by
  rintro rfl
  exact h.lt_irrefl x hxy

theorem gt_of_lt (h : LawfulCmp cmp) {x y : K} (hxy : cmp x y = .lt) : cmp y x = .gt :=
  (h.gt_iff y x).mpr hxy

theorem lt_of_gt (h : LawfulCmp cmp) {x y : K} (hxy : cmp x y = .gt) : cmp y x = .lt :=
  (h.gt_iff x y).mp hxy

theorem trichotomous (h : LawfulCmp cmp) (x y : K) :
    cmp x y = .lt ∨ x = y ∨ cmp y x = .lt := by
  cases hxy : cmp x y with
  | lt => exact Or.inl rfl
  | eq => exact Or.inr (Or.inl ((h.eq_iff x y).mp hxy))
  | gt => exact Or.inr (Or.inr (h.lt_of_gt hxy))

end LawfulCmp

/-- Standard `compare` on `Nat` satisfies `LawfulCmp`. -/
theorem lawfulCmp_nat : LawfulCmp (compare : Nat → Nat → Ordering) where
  eq_iff x y := by
    simp only [compare, compareOfLessAndEq]
    split_ifs <;> constructor <;> intro h <;> first | rfl | omega | cases h
  lt_trans {x y z} hxy hyz := by
    simp only [compare, compareOfLessAndEq] at hxy hyz ⊢
    split_ifs at hxy hyz ⊢ <;> first | rfl | omega
  gt_iff x y := by
    simp only [compare, compareOfLessAndEq]
    split_ifs <;> constructor <;> intro h <;> first | rfl | omega

/-! ## Lexicographic Comparison and `canon_addr_cmp` -/

/-- Lexicographic comparison on lists of natural numbers. -/
def lexCmpNat : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
      match compare x y with
      | .eq => lexCmpNat xs ys
      | ord => ord

/-- Lexicographic chaining combinator matching `canon_ord_then`. -/
def canonOrdThen (a b : Ordering) : Ordering :=
  match a with
  | .eq => b
  | ord => ord

/-- Field encoding of `Ordering` used in `KernelCanonicalCheck` (`0 = lt`, `1 = eq`, `2 = gt`). -/
def canonOrdToNat : Ordering → Nat
  | .lt => 0
  | .eq => 1
  | .gt => 2

@[simp]
theorem lexCmpNat_nil_nil : lexCmpNat [] [] = .eq := rfl

@[simp]
theorem lexCmpNat_cons_cons (x y : Nat) (xs ys : List Nat) :
    lexCmpNat (x :: xs) (y :: ys) = canonOrdThen (compare x y) (lexCmpNat xs ys) := rfl

theorem canonOrdThen_assoc (a b c : Ordering) :
    canonOrdThen (canonOrdThen a b) c = canonOrdThen a (canonOrdThen b c) := by
  cases a <;> rfl

theorem lexCmpNat_append {xs₁ ys₁ : List Nat} (hLen : xs₁.length = ys₁.length)
    (xs₂ ys₂ : List Nat) :
    lexCmpNat (xs₁ ++ xs₂) (ys₁ ++ ys₂) =
      canonOrdThen (lexCmpNat xs₁ ys₁) (lexCmpNat xs₂ ys₂) := by
  induction xs₁ generalizing ys₁ with
  | nil =>
      cases ys₁ with
      | nil => rfl
      | cons _ _ => simp at hLen
  | cons x xs₁ ih =>
      cases ys₁ with
      | nil => simp at hLen
      | cons y ys₁ =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hLen
          simp only [List.cons_append, lexCmpNat_cons_cons, ih hLen, canonOrdThen_assoc]

theorem lawfulCmp_lexCmpNat : LawfulCmp lexCmpNat where
  eq_iff xs ys := by
    induction xs generalizing ys with
    | nil =>
        cases ys <;> simp [lexCmpNat]
    | cons x xs ih =>
        cases ys with
        | nil => simp [lexCmpNat]
        | cons y ys =>
            simp only [lexCmpNat]
            cases hxy : compare x y with
            | lt =>
                have hne : x ≠ y := lawfulCmp_nat.lt_ne hxy
                simp [hne]
            | eq =>
                have heq : x = y := (lawfulCmp_nat.eq_iff x y).mp hxy
                subst heq
                simp [ih ys]
            | gt =>
                have hne : x ≠ y := Ne.symm (lawfulCmp_nat.lt_ne (lawfulCmp_nat.lt_of_gt hxy))
                simp [hne]
  lt_trans {xs ys zs} hxy hyz := by
    induction xs generalizing ys zs with
    | nil =>
        cases ys with
        | nil => simp [lexCmpNat] at hxy
        | cons y ys =>
            cases zs with
            | nil => simp [lexCmpNat] at hyz
            | cons z zs => rfl
    | cons x xs ih =>
        cases ys with
        | nil => simp [lexCmpNat] at hxy
        | cons y ys =>
            cases zs with
            | nil => simp [lexCmpNat] at hyz
            | cons z zs =>
                simp only [lexCmpNat] at hxy hyz ⊢
                cases h1 : compare x y <;> rw [h1] at hxy
                · cases h2 : compare y z <;> rw [h2] at hyz
                  · rw [lawfulCmp_nat.lt_trans h1 h2]
                  · have hyz_eq : y = z := (lawfulCmp_nat.eq_iff y z).mp h2
                    subst hyz_eq
                    rw [h1]
                  · nomatch hyz
                · have hxy_eq : x = y := (lawfulCmp_nat.eq_iff x y).mp h1
                  subst hxy_eq
                  cases h2 : compare x z
                  · rfl
                  · rw [h2] at hyz
                    exact ih hxy hyz
                  · rw [h2] at hyz
                    nomatch hyz
                · nomatch hxy
  gt_iff xs ys := by
    induction xs generalizing ys with
    | nil =>
        cases ys <;> simp [lexCmpNat]
    | cons x xs ih =>
        cases ys with
        | nil => simp [lexCmpNat]
        | cons y ys =>
            simp only [lexCmpNat]
            cases hxy : compare x y
            · have hyx : compare y x = .gt := lawfulCmp_nat.gt_of_lt hxy
              rw [hyx]; simp
            · have heq : x = y := (lawfulCmp_nat.eq_iff x y).mp hxy
              subst heq
              rw [lawfulCmp_nat.cmp_refl x]
              exact ih ys
            · have hyx : compare y x = .lt := lawfulCmp_nat.lt_of_gt hxy
              rw [hyx]; simp

/-- Big-endian 4-byte chunk value matching `canon_addr_chunk` in `KernelCanonicalCheck`. -/
def chunkVal (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat

private theorem compare_step_256 (a b c d : Nat) (hb : b < 256) (hd : d < 256) :
    compare (a * 256 + b) (c * 256 + d) = canonOrdThen (compare a c) (compare b d) := by
  simp only [canonOrdThen, compare, compareOfLessAndEq]
  split_ifs <;> first | rfl | (exfalso; omega)

@[simp]
private theorem canonOrdThen_eq_right (a : Ordering) : canonOrdThen a .eq = a := by
  cases a <;> rfl

/-- Comparing two 4-byte big-endian chunks as natural numbers is identical to
comparing their 4 bytes lexicographically. -/
theorem compare_chunkVal_eq_lexCmpNat (x0 x1 x2 x3 y0 y1 y2 y3 : UInt8) :
    compare (chunkVal x0 x1 x2 x3) (chunkVal y0 y1 y2 y3) =
      lexCmpNat [x0.toNat, x1.toNat, x2.toNat, x3.toNat]
        [y0.toNat, y1.toNat, y2.toNat, y3.toNat] := by
  have hL (b0 b1 b2 b3 : UInt8) :
      chunkVal b0 b1 b2 b3 = ((b0.toNat * 256 + b1.toNat) * 256 + b2.toNat) * 256 + b3.toNat := by
     unfold chunkVal; omega
  rw [hL x0 x1 x2 x3, hL y0 y1 y2 y3]
  rw [compare_step_256 _ _ _ _ x3.toNat_lt y3.toNat_lt]
  rw [compare_step_256 _ _ _ _ x2.toNat_lt y2.toNat_lt]
  rw [compare_step_256 _ _ _ _ x1.toNat_lt y1.toNat_lt]
  simp only [lexCmpNat_cons_cons, lexCmpNat_nil_nil, canonOrdThen_eq_right, canonOrdThen_assoc]

/-- Canonical comparison on 32-byte `Address` values. -/
def canonAddrCmp (x y : Address) : Ordering :=
  lexCmpNat (x.toList.map UInt8.toNat) (y.toList.map UInt8.toNat)

/-- Strict inequality on 32-byte `Address` values induced by `canonAddrCmp`. -/
def canonAddrLt (x y : Address) : Prop :=
  canonAddrCmp x y = .lt

private theorem list_map_u8_toNat_inj {xs ys : List UInt8}
    (h : xs.map UInt8.toNat = ys.map UInt8.toNat) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> simp at h ⊢
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at h
          exact List.cons_eq_cons.mpr ⟨UInt8.ext h.1, ih h.2⟩

/-- `canonAddrCmp` is a lawful strict weak order on 32-byte `Address` values. -/
theorem lawfulCmp_canonAddrCmp : LawfulCmp canonAddrCmp where
  eq_iff x y := by
    unfold canonAddrCmp
    rw [lawfulCmp_lexCmpNat.eq_iff]
    constructor
    · intro h
      exact Vector.toList_inj.mp (list_map_u8_toNat_inj h)
    · rintro rfl; rfl
  lt_trans hxy hyz := lawfulCmp_lexCmpNat.lt_trans hxy hyz
  gt_iff x y := lawfulCmp_lexCmpNat.gt_iff _ _

theorem canon_addr_cmp_refl (x : Address) : canonAddrCmp x x = .eq :=
  lawfulCmp_canonAddrCmp.cmp_refl x

theorem canon_addr_cmp_eq_iff (x y : Address) : canonAddrCmp x y = .eq ↔ x = y :=
  lawfulCmp_canonAddrCmp.eq_iff x y

theorem canon_addr_cmp_irrefl (x : Address) : ¬ canonAddrLt x x :=
  lawfulCmp_canonAddrCmp.lt_irrefl x

theorem canon_addr_cmp_trans {x y z : Address}
    (hxy : canonAddrLt x y) (hyz : canonAddrLt y z) : canonAddrLt x z :=
  lawfulCmp_canonAddrCmp.lt_trans hxy hyz

theorem canon_addr_cmp_asymm {x y : Address} (hxy : canonAddrLt x y) : ¬ canonAddrLt y x :=
  lawfulCmp_canonAddrCmp.lt_asymm hxy

theorem canon_addr_cmp_trichotomous (x y : Address) :
    canonAddrLt x y ∨ x = y ∨ canonAddrLt y x :=
  lawfulCmp_canonAddrCmp.trichotomous x y

theorem canon_addr_cmp_gt_iff (x y : Address) :
    canonAddrCmp x y = .gt ↔ canonAddrLt y x :=
  lawfulCmp_canonAddrCmp.gt_iff x y

/-! ## Red-Black Tree AST, `BinaryTree` Bridge, and `HeapMono` Representation -/

/-- Pure red-black search tree parameterized by key type `K` and value type `V`. -/
inductive RBTree (K V : Type*) where
  | nil : RBTree K V
  | node (color : Nat) (key : K) (val : V) (left right : RBTree K V) : RBTree K V
  deriving Repr, DecidableEq

/-- Embedding of `RBTree K V` into `Aiur.BinaryTree (Nat × K × V)`. -/
def RBTree.toBinaryTree {K V : Type*} : RBTree K V → BinaryTree (Nat × K × V)
  | .nil => .leaf
  | .node color key val left right =>
      .branch (color, key, val) left.toBinaryTree right.toBinaryTree

/-- Inverse projection from `Aiur.BinaryTree (Nat × K × V)` to `RBTree K V`. -/
def RBTree.ofBinaryTree {K V : Type*} : BinaryTree (Nat × K × V) → RBTree K V
  | .leaf => .nil
  | .branch (color, key, val) left right =>
      .node color key val (RBTree.ofBinaryTree left) (RBTree.ofBinaryTree right)

@[simp]
theorem RBTree.ofBinaryTree_toBinaryTree {K V : Type*} (t : RBTree K V) :
    RBTree.ofBinaryTree t.toBinaryTree = t := by
  induction t with
  | nil => rfl
  | node color key val left right ihl ihr =>
      simp [RBTree.toBinaryTree, RBTree.ofBinaryTree, ihl, ihr]

@[simp]
theorem RBTree.toBinaryTree_ofBinaryTree {K V : Type*} (t : BinaryTree (Nat × K × V)) :
    (RBTree.ofBinaryTree t).toBinaryTree = t := by
  induction t with
  | leaf => rfl
  | branch label left right ihl ihr =>
      rcases label with ⟨color, key, val⟩
      simp [RBTree.ofBinaryTree, RBTree.toBinaryTree, ihl, ihr]

/-- Heap-allocated `RBTree K V` pointer representation, defined via `RepBinaryTree`. -/
def RepRBTreePtr {F : Type} {K V : Type*} (enumName nilCtor nodeCtor : String)
    (RLabel : Heap F → (Nat × K × V) → SourceValue F → Prop)
    (h : Heap F) (t : RBTree K V) (ptr : SourceValue F) : Prop :=
  RepBinaryTree enumName nilCtor nodeCtor RLabel h t.toBinaryTree ptr

theorem RepRBTreePtr.mono {F : Type} {K V : Type*} {enumName nilCtor nodeCtor : String}
    {RLabel : Heap F → (Nat × K × V) → SourceValue F → Prop} (hR : HeapMono₂ RLabel)
    {h₁ h₂ : Heap F} {t : RBTree K V} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (rep : RepRBTreePtr enumName nilCtor nodeCtor RLabel h₁ t ptr) :
    RepRBTreePtr enumName nilCtor nodeCtor RLabel h₂ t ptr :=
  RepBinaryTree.mono hR ext rep

theorem HeapMono.repRBTreePtr {F : Type} {K V : Type*} (enumName nilCtor nodeCtor : String)
    {RLabel : Heap F → (Nat × K × V) → SourceValue F → Prop} (hR : HeapMono₂ RLabel)
    (t : RBTree K V) :
    HeapMono (fun h ptr => RepRBTreePtr enumName nilCtor nodeCtor RLabel h t ptr) :=
  HeapMono.repBinaryTree enumName nilCtor nodeCtor hR t.toBinaryTree

/-! ## Red-Black Tree Operations (`rbtreeGet`, `balance`, `ins`, `rbtreeInsert`) -/

variable {K V : Type*}

/-- Lookup key `k` in `RBTree K V` using `cmp`. -/
def rbtreeGet (cmp : K → K → Ordering) (k : K) : RBTree K V → Option V
  | .nil => none
  | .node _ nk nv left right =>
      match cmp k nk with
      | .lt => rbtreeGet cmp k left
      | .eq => some nv
      | .gt => rbtreeGet cmp k right

/-- Lookup key `k` with fallback `default`, matching `rbtree_map_lookup_or_default`
and `role_map_lookup_or_default`. -/
def rbtreeLookupOrDefault (cmp : K → K → Ordering) (k : K) (t : RBTree K V) (default : V) : V :=
  (rbtreeGet cmp k t).getD default

/-- Red-black tree rotation helper matching `rbtree_map_balance_fix` in `RBTreeMap.aiur`. -/
def balanceFix (k : K) (v : V) (left right : RBTree K V) : RBTree K V :=
  match left, right with
  | .node 0 yk yv (.node 0 xk xv a b) c, d =>
      .node 0 yk yv (.node 1 xk xv a b) (.node 1 k v c d)
  | .node 0 xk xv a (.node 0 yk yv b c), d =>
      .node 0 yk yv (.node 1 xk xv a b) (.node 1 k v c d)
  | a, .node 0 zk zv (.node 0 yk yv b c) d =>
      .node 0 yk yv (.node 1 k v a b) (.node 1 zk zv c d)
  | a, .node 0 yk yv b (.node 0 zk zv c d) =>
      .node 0 yk yv (.node 1 k v a b) (.node 1 zk zv c d)
  | _, _ =>
      .node 1 k v left right

/-- Red-black tree balance operation matching `rbtree_map_balance` in `RBTreeMap.aiur`. -/
def balance (color : Nat) (k : K) (v : V) (left right : RBTree K V) : RBTree K V :=
  match color with
  | 1 => balanceFix k v left right
  | _ => .node color k v left right

/-- Recursive red-black tree insertion helper matching `rbtree_map_ins` in `RBTreeMap.aiur`. -/
def ins (cmp : K → K → Ordering) (k : K) (v : V) : RBTree K V → RBTree K V
  | .nil => .node 0 k v .nil .nil
  | .node color nk nv left right =>
      match cmp k nk with
      | .lt => balance color nk nv (ins cmp k v left) right
      | .eq => .node color k v left right
      | .gt => balance color nk nv left (ins cmp k v right)

/-- Top-level red-black tree insertion matching `rbtree_map_insert` in `RBTreeMap.aiur`. -/
def rbtreeInsert (cmp : K → K → Ordering) (k : K) (v : V) (t : RBTree K V) : RBTree K V :=
  match ins cmp k v t with
  | .nil => .nil
  | .node _ nk nv left right => .node 1 nk nv left right

/-- Disjunctive characterization of the 5 branches of `balanceFix`. -/
theorem balanceFix_cases (k : K) (v : V) (left right : RBTree K V) :
    (∃ yk yv xk xv a b c,
      left = .node 0 yk yv (.node 0 xk xv a b) c ∧
      balanceFix k v left right = .node 0 yk yv (.node 1 xk xv a b) (.node 1 k v c right)) ∨
    (∃ xk xv a yk yv b c,
      left = .node 0 xk xv a (.node 0 yk yv b c) ∧
      balanceFix k v left right = .node 0 yk yv (.node 1 xk xv a b) (.node 1 k v c right)) ∨
    (∃ zk zv yk yv b c d,
      right = .node 0 zk zv (.node 0 yk yv b c) d ∧
      balanceFix k v left right = .node 0 yk yv (.node 1 k v left b) (.node 1 zk zv c d)) ∨
    (∃ yk yv b zk zv c d,
      right = .node 0 yk yv b (.node 0 zk zv c d) ∧
      balanceFix k v left right = .node 0 yk yv (.node 1 k v left b) (.node 1 zk zv c d)) ∨
    balanceFix k v left right = .node 1 k v left right := by
  unfold balanceFix
  split
  · exact Or.inl ⟨_, _, _, _, _, _, _, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-! ## Key Predicates (`AllKeys`) and Binary Search Tree (`BST`) Invariant -/

/-- Predicate asserting that every key in the tree satisfies `P`. -/
def AllKeys (P : K → Prop) : RBTree K V → Prop
  | .nil => True
  | .node _ k _ l r => P k ∧ AllKeys P l ∧ AllKeys P r

theorem AllKeys.imp {P Q : K → Prop} (hPQ : ∀ x, P x → Q x) {t : RBTree K V}
    (h : AllKeys P t) : AllKeys Q t := by
  induction t with
  | nil => trivial
  | node _ k _ l r ihl ihr =>
      exact ⟨hPQ k h.1, ihl h.2.1, ihr h.2.2⟩

/-- Binary Search Tree invariant wrt `cmp`. -/
def BST (cmp : K → K → Ordering) : RBTree K V → Prop
  | .nil => True
  | .node _ k _ l r =>
      AllKeys (fun x => cmp x k = .lt) l ∧
      AllKeys (fun x => cmp k x = .lt) r ∧
      BST cmp l ∧
      BST cmp r

theorem allKeys_balanceFix (P : K → Prop) (k : K) (v : V) (left right : RBTree K V) :
    AllKeys P (balanceFix k v left right) ↔ P k ∧ AllKeys P left ∧ AllKeys P right := by
  rcases balanceFix_cases k v left right with
    ⟨yk, yv, xk, xv, a, b, c, rfl, hEq⟩ |
    ⟨xk, xv, a, yk, yv, b, c, rfl, hEq⟩ |
    ⟨zk, zv, yk, yv, b, c, d, rfl, hEq⟩ |
    ⟨yk, yv, b, zk, zv, c, d, rfl, hEq⟩ |
    hEq
  · rw [hEq]; simp only [AllKeys]; tauto
  · rw [hEq]; simp only [AllKeys]; tauto
  · rw [hEq]; simp only [AllKeys]; tauto
  · rw [hEq]; simp only [AllKeys]; tauto
  · rw [hEq]; rfl

theorem allKeys_balance (P : K → Prop) (color : Nat) (k : K) (v : V) (left right : RBTree K V) :
    AllKeys P (balance color k v left right) ↔ P k ∧ AllKeys P left ∧ AllKeys P right := by
  unfold balance
  split
  · exact allKeys_balanceFix P k v left right
  · rfl

theorem allKeys_ins {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (P : K → Prop) (k : K) (v : V) (t : RBTree K V) :
    AllKeys P (ins cmp k v t) ↔ P k ∧ AllKeys P t := by
  induction t with
  | nil => simp [ins, AllKeys]
  | node color nk nv left right ihl ihr =>
      simp only [ins, AllKeys]
      cases hcmp : cmp k nk
      · rw [allKeys_balance, ihl]; tauto
      · have heq : k = nk := (hc.eq_iff k nk).mp hcmp
        subst heq
        simp only [AllKeys]
        tauto
      · rw [allKeys_balance, ihr]; tauto

/-- `balance` preserves the `BST` invariant whenever the children and root satisfy `BST`. -/
theorem rbtree_bst_balance {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (color : Nat) (k : K) (v : V) (left right : RBTree K V)
    (hLeftKeys : AllKeys (fun x => cmp x k = .lt) left)
    (hRightKeys : AllKeys (fun x => cmp k x = .lt) right)
    (hLeftBST : BST cmp left)
    (hRightBST : BST cmp right) :
    BST cmp (balance color k v left right) := by
  unfold balance
  split
  · rcases balanceFix_cases k v left right with
      ⟨yk, yv, xk, xv, a, b, c, rfl, hEq⟩ |
      ⟨xk, xv, a, yk, yv, b, c, rfl, hEq⟩ |
      ⟨zk, zv, yk, yv, b, c, d, rfl, hEq⟩ |
      ⟨yk, yv, b, zk, zv, c, d, rfl, hEq⟩ |
      hEq
    · rw [hEq]
      obtain ⟨hyk_k, ⟨hxk_k, ha_k, hb_k⟩, hc_k⟩ := hLeftKeys
      obtain ⟨⟨hxk_yk, ha_yk, hb_yk⟩, hc_yk, ⟨ha_xk, hb_xk, ha_bst, hb_bst⟩, hc_bst⟩ := hLeftBST
      refine ⟨⟨hxk_yk, ha_yk, hb_yk⟩, ⟨hyk_k, hc_yk, hRightKeys.imp (fun _ hx => hc.lt_trans hyk_k hx)⟩,
        ⟨ha_xk, hb_xk, ha_bst, hb_bst⟩, ⟨hc_k, hRightKeys, hc_bst, hRightBST⟩⟩
    · rw [hEq]
      obtain ⟨hxk_k, ha_k, hyk_k, hb_k, hc_k⟩ := hLeftKeys
      obtain ⟨ha_xk, ⟨hyk_xk, hb_xk, hc_xk⟩, ha_bst, hb_yk, hc_yk, hb_bst, hc_bst⟩ := hLeftBST
      refine ⟨⟨hyk_xk, ha_xk.imp (fun _ hx => hc.lt_trans hx hyk_xk), hb_yk⟩,
        ⟨hyk_k, hc_yk, hRightKeys.imp (fun _ hx => hc.lt_trans hyk_k hx)⟩,
        ⟨ha_xk, hb_xk, ha_bst, hb_bst⟩, ⟨hc_k, hRightKeys, hc_bst, hRightBST⟩⟩
    · rw [hEq]
      obtain ⟨hk_zk, ⟨hk_yk, hk_b, hk_c⟩, hk_d⟩ := hRightKeys
      obtain ⟨⟨hyk_zk, hb_zk, hc_zk⟩, hd_zk, ⟨hb_yk, hc_yk, hb_bst, hc_bst⟩, hd_bst⟩ := hRightBST
      refine ⟨⟨hk_yk, hLeftKeys.imp (fun _ hx => hc.lt_trans hx hk_yk), hb_yk⟩,
        ⟨hyk_zk, hc_yk, hd_zk.imp (fun _ hx => hc.lt_trans hyk_zk hx)⟩,
        ⟨hLeftKeys, hk_b, hLeftBST, hb_bst⟩, ⟨hc_zk, hd_zk, hc_bst, hd_bst⟩⟩
    · rw [hEq]
      obtain ⟨hk_yk, hk_b, hk_zk, hk_c, hk_d⟩ := hRightKeys
      obtain ⟨hb_yk, ⟨hzk_yk, hc_yk, hd_yk⟩, hb_bst, hc_zk, hd_zk, hc_bst, hd_bst⟩ := hRightBST
      refine ⟨⟨hk_yk, hLeftKeys.imp (fun _ hx => hc.lt_trans hx hk_yk), hb_yk⟩,
        ⟨hzk_yk, hc_yk, hd_yk⟩,
        ⟨hLeftKeys, hk_b, hLeftBST, hb_bst⟩, ⟨hc_zk, hd_zk, hc_bst, hd_bst⟩⟩
    · rw [hEq]
      exact ⟨hLeftKeys, hRightKeys, hLeftBST, hRightBST⟩
  · exact ⟨hLeftKeys, hRightKeys, hLeftBST, hRightBST⟩

/-- `ins` preserves the `BST` invariant. -/
theorem rbtree_bst_ins {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (k : K) (v : V) {t : RBTree K V} (ht : BST cmp t) :
    BST cmp (ins cmp k v t) := by
  induction t with
  | nil => exact ⟨trivial, trivial, trivial, trivial⟩
  | node color nk nv left right ihl ihr =>
      obtain ⟨hL, hR, hBSTL, hBSTR⟩ := ht
      simp only [ins]
      cases hcmp : cmp k nk
      · exact rbtree_bst_balance hc color nk nv (ins cmp k v left) right
          ((allKeys_ins hc _ k v left).mpr ⟨hcmp, hL⟩) hR (ihl hBSTL) hBSTR
      · have heq : k = nk := (hc.eq_iff k nk).mp hcmp
        subst heq
        exact ⟨hL, hR, hBSTL, hBSTR⟩
      · have hnk_k : cmp nk k = .lt := hc.lt_of_gt hcmp
        exact rbtree_bst_balance hc color nk nv left (ins cmp k v right)
          hL ((allKeys_ins hc _ k v right).mpr ⟨hnk_k, hR⟩) hBSTL (ihr hBSTR)

/-- `rbtreeInsert` preserves the `BST` invariant. -/
theorem rbtree_bst_insert {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (k : K) (v : V) {t : RBTree K V} (ht : BST cmp t) :
    BST cmp (rbtreeInsert cmp k v t) := by
  unfold rbtreeInsert
  have hIns := rbtree_bst_ins hc k v ht
  cases h : ins cmp k v t with
  | nil => trivial
  | node c nk nv l r =>
      rw [h] at hIns
      exact hIns

/-! ## Lookup Preservation Under `balance`, `ins`, and `rbtreeInsert` -/

private theorem lookup_rot_ll {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {yk k : K} {yv xv v : V} {xk : K} {a b c d : RBTree K V} {color : Nat}
    (hyk_k : cmp yk k = .lt) (q : K) :
    rbtreeGet cmp q (.node 0 yk yv (.node 1 xk xv a b) (.node 1 k v c d)) =
      rbtreeGet cmp q (.node color k v (.node 0 yk yv (.node 0 xk xv a b) c) d) := by
  simp only [rbtreeGet]
  cases hqy : cmp q yk
  · have hqk : cmp q k = .lt := hc.lt_trans hqy hyk_k
    simp [hqk]
  · have hq_eq : q = yk := (hc.eq_iff q yk).mp hqy
    subst hq_eq
    simp [hyk_k]
  · cases hqk : cmp q k <;> simp

private theorem lookup_rot_lr {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {xk yk k : K} {xv yv v : V} {a b c d : RBTree K V} {color : Nat}
    (hxk_yk : cmp xk yk = .lt) (hyk_k : cmp yk k = .lt) (q : K) :
    rbtreeGet cmp q (.node 0 yk yv (.node 1 xk xv a b) (.node 1 k v c d)) =
      rbtreeGet cmp q (.node color k v (.node 0 xk xv a (.node 0 yk yv b c)) d) := by
  simp only [rbtreeGet]
  cases hqy : cmp q yk
  · have hqk : cmp q k = .lt := hc.lt_trans hqy hyk_k
    simp only [hqk]
  · have hq_eq : q = yk := (hc.eq_iff q yk).mp hqy
    subst hq_eq
    have hyx : cmp q xk = .gt := hc.gt_of_lt hxk_yk
    simp [hyk_k, hyx]
  · have hqx : cmp q xk = .gt := hc.gt_of_lt (hc.lt_trans hxk_yk (hc.lt_of_gt hqy))
    cases hqk : cmp q k <;> simp [hqx]

private theorem lookup_rot_rl {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {k yk zk : K} {v yv zv : V} {a b c d : RBTree K V} {color : Nat}
    (hk_yk : cmp k yk = .lt) (hyk_zk : cmp yk zk = .lt) (q : K) :
    rbtreeGet cmp q (.node 0 yk yv (.node 1 k v a b) (.node 1 zk zv c d)) =
      rbtreeGet cmp q (.node color k v a (.node 0 zk zv (.node 0 yk yv b c) d)) := by
  simp only [rbtreeGet]
  cases hqy : cmp q yk
  · have hqz : cmp q zk = .lt := hc.lt_trans hqy hyk_zk
    cases hqk : cmp q k <;> simp [hqz]
  · have hq_eq : q = yk := (hc.eq_iff q yk).mp hqy
    subst hq_eq
    have hyk_k : cmp q k = .gt := hc.gt_of_lt hk_yk
    simp [hyk_k, hyk_zk]
  · have hqk : cmp q k = .gt := hc.gt_of_lt (hc.lt_trans hk_yk (hc.lt_of_gt hqy))
    simp only [hqk]

private theorem lookup_rot_rr {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {k yk zk : K} {v yv zv : V} {a b c d : RBTree K V} {color : Nat}
    (hk_yk : cmp k yk = .lt) (q : K) :
    rbtreeGet cmp q (.node 0 yk yv (.node 1 k v a b) (.node 1 zk zv c d)) =
      rbtreeGet cmp q (.node color k v a (.node 0 yk yv b (.node 0 zk zv c d))) := by
  simp only [rbtreeGet]
  cases hqy : cmp q yk
  · cases hqk : cmp q k <;> simp
  · have hq_eq : q = yk := (hc.eq_iff q yk).mp hqy
    subst hq_eq
    have hyk_k : cmp q k = .gt := hc.gt_of_lt hk_yk
    simp [hyk_k]
  · have hqk : cmp q k = .gt := hc.gt_of_lt (hc.lt_trans hk_yk (hc.lt_of_gt hqy))
    simp [hqk]

/-- `balance` preserves lookup results for all queries `q` on valid BST children. -/
theorem balance_lookup_eq {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (color : Nat) (k : K) (v : V) (left right : RBTree K V)
    (hLeftKeys : AllKeys (fun x => cmp x k = .lt) left)
    (hRightKeys : AllKeys (fun x => cmp k x = .lt) right)
    (hLeftBST : BST cmp left)
    (hRightBST : BST cmp right)
    (q : K) :
    rbtreeGet cmp q (balance color k v left right) =
      rbtreeGet cmp q (.node color k v left right) := by
  unfold balance
  split
  · rcases balanceFix_cases k v left right with
      ⟨yk, yv, xk, xv, a, b, c, rfl, hEq⟩ |
      ⟨xk, xv, a, yk, yv, b, c, rfl, hEq⟩ |
      ⟨zk, zv, yk, yv, b, c, d, rfl, hEq⟩ |
      ⟨yk, yv, b, zk, zv, c, d, rfl, hEq⟩ |
      hEq
    · rw [hEq]
      exact lookup_rot_ll hc hLeftKeys.1 q
    · rw [hEq]
      exact lookup_rot_lr hc hLeftBST.2.1.1 hLeftKeys.2.2.1 q
    · rw [hEq]
      exact lookup_rot_rl hc hRightKeys.2.1.1 hRightBST.1.1 q
    · rw [hEq]
      exact lookup_rot_rr hc hRightKeys.1 q
    · rw [hEq]
  · rfl

/-- Lookup characterization after `ins`: returns `some v` for `q = k`, and
preserves `rbtreeGet cmp q t` for `q ≠ k`. -/
theorem ins_lookup_eq [DecidableEq K] {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (k : K) (v : V) {t : RBTree K V} (ht : BST cmp t) (q : K) :
    rbtreeGet cmp q (ins cmp k v t) =
      if q = k then some v else rbtreeGet cmp q t := by
  induction t with
  | nil =>
      simp only [ins, rbtreeGet]
      cases hqk : cmp q k
      · have hne : q ≠ k := hc.lt_ne hqk
        simp [hne]
      · have heq : q = k := (hc.eq_iff q k).mp hqk
        simp [heq]
      · have hne : q ≠ k := Ne.symm (hc.lt_ne (hc.lt_of_gt hqk))
        simp [hne]
  | node color nk nv left right ihl ihr =>
      obtain ⟨hL, hR, hBSTL, hBSTR⟩ := ht
      simp only [ins]
      cases hknk : cmp k nk
      · rw [balance_lookup_eq hc color nk nv (ins cmp k v left) right
          ((allKeys_ins hc _ k v left).mpr ⟨hknk, hL⟩) hR (rbtree_bst_ins hc k v hBSTL) hBSTR q]
        simp only [rbtreeGet]
        cases hqnk : cmp q nk
        · exact ihl hBSTL
        · have hq_nk : q = nk := (hc.eq_iff q nk).mp hqnk
          subst hq_nk
          have hne : q ≠ k := Ne.symm (hc.lt_ne hknk)
          simp [hne]
        · have hnk_q : cmp nk q = .lt := hc.lt_of_gt hqnk
          have hne : q ≠ k := Ne.symm (hc.lt_ne (hc.lt_trans hknk hnk_q))
          simp [hne]
      · have hk_nk : k = nk := (hc.eq_iff k nk).mp hknk
        subst hk_nk
        simp only [rbtreeGet]
        cases hqk : cmp q k
        · have hne : q ≠ k := hc.lt_ne hqk
          simp [hne]
        · have heq : q = k := (hc.eq_iff q k).mp hqk
          simp [heq]
        · have hne : q ≠ k := Ne.symm (hc.lt_ne (hc.lt_of_gt hqk))
          simp [hne]
      · have hnk_k : cmp nk k = .lt := hc.lt_of_gt hknk
        rw [balance_lookup_eq hc color nk nv left (ins cmp k v right)
          hL ((allKeys_ins hc _ k v right).mpr ⟨hnk_k, hR⟩) hBSTL (rbtree_bst_ins hc k v hBSTR) q]
        simp only [rbtreeGet]
        cases hqnk : cmp q nk
        · have hne : q ≠ k := hc.lt_ne (hc.lt_trans hqnk hnk_k)
          simp [hne]
        · have hq_nk : q = nk := (hc.eq_iff q nk).mp hqnk
          subst hq_nk
          have hne : q ≠ k := hc.lt_ne hnk_k
          simp [hne]
        · exact ihr hBSTR

/-- Full lookup specification of `rbtreeInsert`. -/
theorem rbtree_get_insert [DecidableEq K] {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (k : K) (v : V) {t : RBTree K V} (ht : BST cmp t) (q : K) :
    rbtreeGet cmp q (rbtreeInsert cmp k v t) =
      if q = k then some v else rbtreeGet cmp q t := by
  unfold rbtreeInsert
  have hEq := ins_lookup_eq hc k v ht q
  cases h : ins cmp k v t with
  | nil =>
      rw [h] at hEq
      exact hEq
  | node c nk nv l r =>
      rw [h] at hEq
      exact hEq

/-- Looking up the newly inserted key `k` returns `some v`. -/
theorem rbtree_get_insert_self [DecidableEq K] {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (k : K) (v : V) {t : RBTree K V} (ht : BST cmp t) :
    rbtreeGet cmp k (rbtreeInsert cmp k v t) = some v := by
  rw [rbtree_get_insert hc k v ht k, ite_eq_left_iff]
  intro hne
  exact absurd rfl hne

/-- Looking up any key `q ≠ k` after inserting `(k, v)` preserves the previous lookup result. -/
theorem rbtree_get_insert_ne [DecidableEq K] {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    (k : K) (v : V) {t : RBTree K V} (ht : BST cmp t) {q : K} (hne : q ≠ k) :
    rbtreeGet cmp q (rbtreeInsert cmp k v t) = rbtreeGet cmp q t := by
  rw [rbtree_get_insert hc k v ht q]
  simp [hne]

/-! ## In-Order Traversal (`toList`) and Static Balanced Tree (`RoleMap` / `buildBalancedTree`) -/

/-- In-order list of `(key, value)` pairs in `RBTree K V`. -/
def RBTree.toList : RBTree K V → List (K × V)
  | .nil => []
  | .node _ k v l r => l.toList ++ (k, v) :: r.toList

theorem mem_toList_imp_allKeys {P : K → Prop} {t : RBTree K V}
    (hAll : AllKeys P t) {p : K × V} (hp : p ∈ t.toList) : P p.1 := by
  induction t with
  | nil => simp [RBTree.toList] at hp
  | node _ k v l r ihl ihr =>
      simp only [RBTree.toList, List.mem_append, List.mem_cons] at hp
      rcases hp with hp | rfl | hp
      · exact ihl hAll.2.1 hp
      · exact hAll.1
      · exact ihr hAll.2.2 hp

theorem allKeys_iff_forall_mem_toList (P : K → Prop) (t : RBTree K V) :
    AllKeys P t ↔ ∀ p ∈ t.toList, P p.1 := by
  induction t with
  | nil => simp [AllKeys, RBTree.toList]
  | node _ k v l r ihl ihr =>
      simp only [AllKeys, RBTree.toList, ihl, ihr, List.mem_append, List.mem_cons]
      constructor
      · rintro ⟨hk, hl, hr⟩ p (hp | rfl | hp)
        · exact hl p hp
        · exact hk
        · exact hr p hp
      · intro h
        exact ⟨h (k, v) (Or.inr (Or.inl rfl)),
          fun p hp => h p (Or.inl hp),
          fun p hp => h p (Or.inr (Or.inr hp))⟩

/-- In a valid `BST`, `rbtreeGet cmp q t = some v` iff `(q, v) ∈ t.toList`. -/
theorem rbtreeGet_eq_some_iff_mem_toList {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {t : RBTree K V} (ht : BST cmp t) (q : K) (v : V) :
    rbtreeGet cmp q t = some v ↔ (q, v) ∈ t.toList := by
  induction t with
  | nil => simp [rbtreeGet, RBTree.toList]
  | node _ nk nv l r ihl ihr =>
      obtain ⟨hL, hR, hBSTL, hBSTR⟩ := ht
      simp only [rbtreeGet, RBTree.toList, List.mem_append, List.mem_cons]
      cases hqnk : cmp q nk
      · rw [ihl hBSTL]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | ⟨rfl, rfl⟩ | h)
          · exact h
          · exact absurd hqnk (hc.lt_irrefl q)
          · have hnk_q : cmp nk q = .lt := mem_toList_imp_allKeys hR h
            exact absurd (hc.lt_trans hqnk hnk_q) (hc.lt_irrefl q)
      · have hq_nk : q = nk := (hc.eq_iff q nk).mp hqnk
        subst hq_nk
        simp only [Option.some.injEq]
        constructor
        · rintro rfl; exact Or.inr (Or.inl rfl)
        · rintro (h | ⟨_, rfl⟩ | h)
          · have hq_lt : cmp q q = .lt := mem_toList_imp_allKeys hL h
            exact absurd hq_lt (hc.lt_irrefl q)
          · rfl
          · have hq_lt : cmp q q = .lt := mem_toList_imp_allKeys hR h
            exact absurd hq_lt (hc.lt_irrefl q)
      · have hnk_q : cmp nk q = .lt := hc.lt_of_gt hqnk
        rw [ihr hBSTR]
        constructor
        · intro h; exact Or.inr (Or.inr h)
        · rintro (h | ⟨rfl, rfl⟩ | h)
          · have hq_nk : cmp q nk = .lt := mem_toList_imp_allKeys hL h
            exact absurd (hc.lt_trans hnk_q hq_nk) (hc.lt_irrefl nk)
          · exact absurd hnk_q (hc.lt_irrefl q)
          · exact h

/-- In a valid `BST`, `rbtreeGet cmp q t = none` iff no pair in `t.toList` has key `q`. -/
theorem rbtreeGet_eq_none_iff_forall_ne {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {t : RBTree K V} (ht : BST cmp t) (q : K) :
    rbtreeGet cmp q t = none ↔ ∀ p ∈ t.toList, p.1 ≠ q := by
  constructor
  · intro hNone ⟨k, v⟩ hp
    rintro rfl
    have hSome := (rbtreeGet_eq_some_iff_mem_toList hc ht k v).mpr hp
    rw [hNone] at hSome
    contradiction
  · intro hAll
    cases hGet : rbtreeGet cmp q t with
    | none => rfl
    | some v =>
        have hp := (rbtreeGet_eq_some_iff_mem_toList hc ht q v).mp hGet
        exact absurd rfl (hAll (q, v) hp)

/-- Fuel-bounded balanced binary search tree constructor from a slice of `(key, value)` bindings. -/
def buildBalancedTreeAux : Nat → List (K × V) → RBTree K V
  | 0, _ => .nil
  | _ + 1, [] => .nil
  | n + 1, head :: tail =>
      let half := (head :: tail).length / 2
      match (head :: tail).drop half with
      | [] => .nil
      | (k, v) :: rightEntries =>
          .node 1 k v
            (buildBalancedTreeAux n ((head :: tail).take half))
            (buildBalancedTreeAux n rightEntries)

/-- Balanced binary search tree constructor from a slice of `(key, value)` bindings,
matching `read_role_bindings` / `read_role_evidence` in `KernelRoles.aiur`. -/
def buildBalancedTree (entries : List (K × V)) : RBTree K V :=
  buildBalancedTreeAux entries.length entries

private theorem toList_buildBalancedTreeAux :
    ∀ (n : Nat) (entries : List (K × V)), entries.length ≤ n →
      (buildBalancedTreeAux n entries).toList = entries
  | 0, entries, hLen => by
      cases entries with
      | nil => rfl
      | cons _ _ => simp at hLen
  | n + 1, [], _ => rfl
  | n + 1, head :: tail, hLen => by
      simp only [buildBalancedTreeAux]
      have hDropNe : (head :: tail).drop ((head :: tail).length / 2) ≠ [] := by
        intro hEmpty
        have hL := congrArg List.length hEmpty
        rw [List.length_drop] at hL
        simp only [List.length_cons, List.length_nil] at hL
        omega
      split
      · contradiction
      · rename_i k v rightEntries hDrop
        have hTakeLe : ((head :: tail).take ((head :: tail).length / 2)).length ≤ n := by
          rw [List.length_take]
          simp only [List.length_cons] at hLen ⊢
          omega
        have hRightLe : rightEntries.length ≤ n := by
          have hL := congrArg List.length hDrop
          rw [List.length_drop, List.length_cons] at hL
          simp only [List.length_cons] at hL hLen ⊢
          omega
        simp only [RBTree.toList, toList_buildBalancedTreeAux n _ hTakeLe,
          toList_buildBalancedTreeAux n _ hRightLe]
        have hSplit := List.take_append_drop ((head :: tail).length / 2) (head :: tail)
        rw [hDrop] at hSplit
        exact hSplit

/-- `buildBalancedTree` preserves the exact in-order sequence of `(key, value)` pairs. -/
theorem toList_buildBalancedTree (entries : List (K × V)) :
    (buildBalancedTree entries).toList = entries :=
  toList_buildBalancedTreeAux entries.length entries (Nat.le_refl _)

private theorem bst_buildBalancedTreeAux {cmp : K → K → Ordering} :
    ∀ (n : Nat) (entries : List (K × V)), entries.length ≤ n →
      List.Pairwise (fun a b => cmp a.1 b.1 = .lt) entries →
      BST cmp (buildBalancedTreeAux n entries)
  | 0, entries, hLen, _ => by
      cases entries with
      | nil => trivial
      | cons _ _ => simp at hLen
  | n + 1, [], _, _ => trivial
  | n + 1, head :: tail, hLen, hSorted => by
      simp only [buildBalancedTreeAux]
      split
      · trivial
      · rename_i k v rightEntries hDrop
        have hTakeLe : ((head :: tail).take ((head :: tail).length / 2)).length ≤ n := by
          rw [List.length_take]
          simp only [List.length_cons] at hLen ⊢
          omega
        have hRightLe : rightEntries.length ≤ n := by
          have hL := congrArg List.length hDrop
          rw [List.length_drop, List.length_cons] at hL
          simp only [List.length_cons] at hL hLen ⊢
          omega
        have hSplit :
            (head :: tail).take ((head :: tail).length / 2) ++ (k, v) :: rightEntries =
              head :: tail := by
          have h := List.take_append_drop ((head :: tail).length / 2) (head :: tail)
          rw [hDrop] at h
          exact h
        rw [← hSplit, List.pairwise_append, List.pairwise_cons] at hSorted
        obtain ⟨hSortedTake, ⟨hMidRight, hSortedRight⟩, hCross⟩ := hSorted
        refine ⟨?_, ?_,
          bst_buildBalancedTreeAux n _ hTakeLe hSortedTake,
          bst_buildBalancedTreeAux n _ hRightLe hSortedRight⟩
        · rw [allKeys_iff_forall_mem_toList, toList_buildBalancedTreeAux n _ hTakeLe]
          intro p hp
          exact hCross p hp (k, v) (List.mem_cons_self ..)
        · rw [allKeys_iff_forall_mem_toList, toList_buildBalancedTreeAux n _ hRightLe]
          intro p hp
          exact hMidRight p hp

/-- If `entries` is strictly sorted wrt `cmp`, `buildBalancedTree entries` is a valid `BST`. -/
theorem bst_buildBalancedTree {cmp : K → K → Ordering}
    {entries : List (K × V)}
    (hSorted : List.Pairwise (fun a b => cmp a.1 b.1 = .lt) entries) :
    BST cmp (buildBalancedTree entries) :=
  bst_buildBalancedTreeAux entries.length entries (Nat.le_refl _) hSorted

/-- Lookup in `buildBalancedTree entries` (such as `RoleMap` over `0..102` role keys)
returns `some v` iff `(q, v) ∈ entries`. -/
theorem role_tree_get_eq_some_iff {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {entries : List (K × V)}
    (hSorted : List.Pairwise (fun a b => cmp a.1 b.1 = .lt) entries)
    (q : K) (v : V) :
    rbtreeGet cmp q (buildBalancedTree entries) = some v ↔ (q, v) ∈ entries := by
  rw [rbtreeGet_eq_some_iff_mem_toList hc (bst_buildBalancedTree hSorted),
    toList_buildBalancedTree]

/-- Lookup in `buildBalancedTree entries` returns `none` iff `q` is not a key in `entries`. -/
theorem role_tree_get_eq_none_iff {cmp : K → K → Ordering} (hc : LawfulCmp cmp)
    {entries : List (K × V)}
    (hSorted : List.Pairwise (fun a b => cmp a.1 b.1 = .lt) entries)
    (q : K) :
    rbtreeGet cmp q (buildBalancedTree entries) = none ↔ ∀ p ∈ entries, p.1 ≠ q := by
  rw [rbtreeGet_eq_none_iff_forall_ne hc (bst_buildBalancedTree hSorted),
    toList_buildBalancedTree]

end Aiur.Library.RBTreeMap
