import IxVMRefinement.Obs.Lists
import IxVMRefinement.Core.Obs
import Aiur.Library.List.Correctness

/-! # The generic `Lists` functions, over observed derivations

For every element type `t` and every representation `R` of the elements, an observed
derivation of a `Lists` function at the instance `t` on represented lists computes the
list operation of the same name: `length` the length (as a field element), `concat`
the concatenation, `drop`/`take` with a counter `n` the list without / with its first
`n.val` elements (a derivation exists only for `n.val` at most the length), `lookup`
the element at `i.val`, and so on. Each proof inverts the derivation with the
generated path lemma (`IxVMRefinement.Obs`, `«Lists::f».obs`) and recurses on the list
or the counter.

The list a derivation returns lives in the final heap; the heap only grows
(`ObsFn.heap_extends`), so an element representation that is heap-monotone
(`HeapMono₂ R`) carries over. -/

namespace IxVM.Refinement.Lib

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List
open IxVM.Refinement.Obs (W)
open IxVM (F)

set_option linter.unusedVariables false

/-! ## Helpers -/

theorem load_enum_cell {enumName : String} {heap : Heap F} {addr : Nat}
    {c : String} {xs : List (SourceValue F)}
    (cell : heap[addr]? = some (.construct enumName c xs)) :
    loadValue heap (.ptr (.enum enumName) addr) = .ok (.construct enumName c xs) := by
  simp [loadValue, cell, Value.type, bind, Except.bind, pure, Except.pure]

section
variable {α : Type} {en : String} {R : Heap F → α → SourceValue F → Prop}

/-- A list whose cell loads as `Nil` is empty. -/
theorem rep_nil_of_load {h : Heap F} {xs : List α} {p : SourceValue F}
    (rep : RepList en R h xs p) (hl : loadValue h p = .ok (.construct en "Nil" [])) :
    xs = [] := by
  cases rep with
  | nil _ => rfl
  | cons cell _ _ =>
    rw [load_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)

/-- A list whose cell loads as `Cons(x, y)`: its head is represented by `x`, its tail by `y`. -/
theorem rep_cons_of_load {h : Heap F} {xs : List α} {p x y : SourceValue F}
    (rep : RepList en R h xs p) (hl : loadValue h p = .ok (.construct en "Cons" [x, y])) :
    ∃ z zs, xs = z :: zs ∧ R h z x ∧ RepList en R h zs y := by
  cases rep with
  | nil cell =>
    rw [load_enum_cell cell] at hl
    injection hl with hv; injection hv with _ hc _
    exact absurd hc (by decide)
  | cons cell rh rt =>
    rw [load_enum_cell cell] at hl
    injection hl with hv; injection hv with _ _ hargs
    injection hargs with hx hrest; injection hrest with hy _
    subst hx hy
    exact ⟨_, _, rfl, rh, rt⟩

/-- A `Cons` cell stored at the end of the heap represents the list with one more head. -/
theorem rep_store_cons (hR : HeapMono₂ R) {h : Heap F} {x : α} {xs : List α}
    {v p : SourceValue F} (hx : R h x v) (hxs : RepList en R h xs p) :
    RepList en R (h ++ [.construct en "Cons" [v, p]]) (x :: xs) (.ptr (.enum en) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct en "Cons" [v, p]]) := Heap.Extends.snoc h _
  exact .cons (by simp) (hR ext hx) (RepLinkedList.mono hR ext hxs)

/-- A `Nil` cell stored at the end of the heap represents the empty list. -/
theorem rep_store_nil (h : Heap F) :
    RepList en R (h ++ [.construct en "Nil" []]) [] (.ptr (.enum en) h.length) :=
  .nil (by simp)

end

/-- **The counter's predecessor**: in the field, `n ≠ 0` has `(n - 1).val + 1 = n.val`. -/
theorem val_sub_one {n : F} (hn : n ≠ 0) : (n - 1).val + 1 = n.val := by
  have hv : n.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  have hsum : (n - 1) + 1 = n := by ring
  have key := congrArg ZMod.val hsum
  rw [ZMod.val_add, ZMod.val_one] at key
  have hlt := ZMod.val_lt (n - 1)
  by_cases h : (n - 1).val + 1 < Aiur.Library.U32.Goldilocks.modulus
  · rw [Nat.mod_eq_of_lt h] at key
    omega
  · have heq : (n - 1).val + 1 = Aiur.Library.U32.Goldilocks.modulus := by omega
    rw [heq, Nat.mod_self] at key
    omega

theorem sub_one_inv {n : F} {v : SourceValue F}
    (op : evalBinOp .sub (.field n : SourceValue F) (.field 1) = .ok v) : v = .field (n - 1) := by
  simp only [evalBinOp, Except.ok.injEq] at op
  exact op.symm

namespace Lists

variable {α : Type} {t : Generic.Ty} {R : Heap F → α → SourceValue F → Prop}

/-! ## `is_empty`, `length` -/

/-- **`Lists::is_empty`**: `1` on the empty list, `0` otherwise; no allocation. -/
theorem is_empty_spec {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {xs : List α}
    (ev : ObsFn W (Instance.mk "Lists::is_empty" [t]).symbol [l] h r h' cs)
    (hl : RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l) :
    r = .field (if xs.isEmpty then 1 else 0) ∧ h' = h := by
  rcases Obs.«Lists::is_empty».obs ev with ⟨ld, rfl, rfl, -⟩ | ⟨w1, w2, ld, rfl, rfl, -⟩
  · obtain rfl := rep_nil_of_load hl ld
    simp
  · obtain ⟨z, zs, rfl, -, -⟩ := rep_cons_of_load hl ld
    simp

/-- **`Lists::length`**: the length, as a field element; no allocation. -/
theorem length_spec {xs : List α} : ∀ {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    ObsFn W (Instance.mk "Lists::length" [t]).symbol [l] h r h' cs →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l →
    r = .field (xs.length : F) ∧ h' = h := by
  induction xs with
  | nil =>
    intro l r h h' cs ev hl
    rcases Obs.«Lists::length».obs ev with ⟨ld, rfl, rfl, -⟩ |
      ⟨w, rest, x, m, cs', ld, ev', rfl, op, -⟩
    · simp
    · obtain ⟨z, zs, he, -, -⟩ := rep_cons_of_load hl ld
      cases he
  | cons z zs ih =>
    intro l r h h' cs ev hl
    rcases Obs.«Lists::length».obs ev with ⟨ld, rfl, rfl, -⟩ |
      ⟨w, rest, x, m, cs', ld, ev', rfl, op, -⟩
    · cases rep_nil_of_load hl ld
    · obtain ⟨z', zs', he, -, hzs⟩ := rep_cons_of_load hl ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨rfl, rfl⟩ := ih ev' hzs
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      simp

/-! ## `concat`, `snoc`, `reverse` -/

/-- **`Lists::concat`**: the concatenation, in the final heap. -/
theorem concat_spec (hR : HeapMono₂ R) {xs : List α} :
    ∀ {ys : List α} {a b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    ObsFn W (Instance.mk "Lists::concat" [t]).symbol [a, b] h r h' cs →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h xs a →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h ys b →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h' (xs ++ ys) r := by
  induction xs with
  | nil =>
    intro ys a b r h h' cs ev ha hb
    rcases Obs.«Lists::concat».obs ev with ⟨ld, rfl, rfl, -⟩ |
      ⟨x, rest, v, m, cs', ld, rfl, rfl, ev', -⟩
    · simpa using hb
    · obtain ⟨z, zs, he, -, -⟩ := rep_cons_of_load ha ld
      cases he
  | cons z zs ih =>
    intro ys a b r h h' cs ev ha hb
    rcases Obs.«Lists::concat».obs ev with ⟨ld, rfl, rfl, -⟩ |
      ⟨x, rest, v, m, cs', ld, rfl, rfl, ev', -⟩
    · cases rep_nil_of_load ha ld
    · obtain ⟨z', zs', he, hz, hzs⟩ := rep_cons_of_load ha ld
      injection he with h1 h2
      subst h1 h2
      have hrec := ih ev' hzs hb
      exact rep_store_cons hR (hR ev'.heap_extends hz) hrec

/-- **`Lists::snoc`**: the list with one more element at the end. -/
theorem snoc_spec (hR : HeapMono₂ R) {xs : List α} :
    ∀ {x : α} {l v r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    ObsFn W (Instance.mk "Lists::snoc" [t]).symbol [l, v] h r h' cs →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l → R h x v →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h' (xs ++ [x]) r := by
  induction xs with
  | nil =>
    intro x l v r h h' cs ev hl hx
    rcases Obs.«Lists::snoc».obs ev with ⟨m, ld, rfl, rfl, rfl, -⟩ |
      ⟨y, rest, v', m, cs', ld, rfl, rfl, ev', -⟩
    · have hnil : RepList (Instance.mk "Lists::Node" [t]).symbol R
          (h ++ [.construct (Instance.mk "Lists::Node" [t]).symbol "Nil" []]) []
          (.ptr (.enum (Instance.mk "Lists::Node" [t]).symbol) h.length) :=
        rep_store_nil (R := R) h
      exact rep_store_cons hR (hR (Heap.Extends.snoc _ _) hx) hnil
    · obtain ⟨z, zs, he, -, -⟩ := rep_cons_of_load hl ld
      cases he
  | cons z zs ih =>
    intro x l v r h h' cs ev hl hx
    rcases Obs.«Lists::snoc».obs ev with ⟨m, ld, rfl, rfl, rfl, -⟩ |
      ⟨y, rest, v', m, cs', ld, rfl, rfl, ev', -⟩
    · cases rep_nil_of_load hl ld
    · obtain ⟨z', zs', he, hz, hzs⟩ := rep_cons_of_load hl ld
      injection he with h1 h2
      subst h1 h2
      have hrec := ih ev' hzs hx
      exact rep_store_cons hR (hR ev'.heap_extends hz) hrec

/-- **`Lists::reverse_acc`**: the reversed list in front of the accumulator. -/
theorem reverse_acc_spec (hR : HeapMono₂ R) {xs : List α} :
    ∀ {accs : List α} {l acc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    ObsFn W (Instance.mk "Lists::reverse_acc" [t]).symbol [l, acc] h r h' cs →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h accs acc →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h' (xs.reverse ++ accs) r := by
  induction xs with
  | nil =>
    intro accs l acc r h h' cs ev hl hacc
    rcases Obs.«Lists::reverse_acc».obs ev with ⟨ld, rfl, rfl, -⟩ |
      ⟨y, rest, cs', m, ld, rfl, ev', -⟩
    · simpa using hacc
    · obtain ⟨z, zs, he, -, -⟩ := rep_cons_of_load hl ld
      cases he
  | cons z zs ih =>
    intro accs l acc r h h' cs ev hl hacc
    rcases Obs.«Lists::reverse_acc».obs ev with ⟨ld, rfl, rfl, -⟩ |
      ⟨y, rest, cs', m, ld, rfl, ev', -⟩
    · cases rep_nil_of_load hl ld
    · obtain ⟨z', zs', he, hz, hzs⟩ := rep_cons_of_load hl ld
      injection he with h1 h2
      subst h1 h2
      have ext := Heap.Extends.snoc h
        (.construct (Instance.mk "Lists::Node" [t]).symbol "Cons" [y, acc])
      have hrec := ih ev' (RepLinkedList.mono hR ext hzs) (rep_store_cons hR hz hacc)
      simpa using hrec

/-- **`Lists::reverse`**: the reversed list. -/
theorem reverse_spec (hR : HeapMono₂ R) {xs : List α} {l r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W (Instance.mk "Lists::reverse" [t]).symbol [l] h r h' cs)
    (hl : RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l) :
    RepList (Instance.mk "Lists::Node" [t]).symbol R h' xs.reverse r := by
  obtain ⟨cs', m, rfl, ev', -⟩ := Obs.«Lists::reverse».obs ev
  have ext := Heap.Extends.snoc h (.construct (Instance.mk "Lists::Node" [t]).symbol "Nil" [])
  have hrec := reverse_acc_spec hR ev' (RepLinkedList.mono hR ext hl) (rep_store_nil (R := R) h)
  simpa using hrec

/-! ## `drop`, `take`, `lookup` -/

/-- **`Lists::drop`** with the counter `n`: a derivation exists only for `n.val` at most the
length, and returns the list without its first `n.val` elements (a suffix of the input:
no allocation). -/
theorem drop_spec (k : Nat) : ∀ {xs : List α} {l r : SourceValue F} {n : F} {h h' : Heap F}
    {cs : List (Call F)}, n.val = k →
    ObsFn W (Instance.mk "Lists::drop" [t]).symbol [l, .field n] h r h' cs →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l →
    n.val ≤ xs.length ∧ RepList (Instance.mk "Lists::Node" [t]).symbol R h (xs.drop n.val) r ∧
      h' = h := by
  induction k with
  | zero =>
    intro xs l r n h h' cs hk ev hl
    rcases Obs.«Lists::drop».obs ev with ⟨hv, rfl, rfl, -⟩ |
      ⟨m, p, cs', v, w, rest, hne, op, ev', ld, rfl, rfl, -⟩
    · injection hv with hn
      subst hn
      refine ⟨by simp, by simpa using hl, rfl⟩
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      have hpred := val_sub_one hn
      omega
  | succ k ih =>
    intro xs l r n h h' cs hk ev hl
    rcases Obs.«Lists::drop».obs ev with ⟨hv, rfl, rfl, -⟩ |
      ⟨m, p, cs', v, w, rest, hne, op, ev', ld, rfl, rfl, -⟩
    · injection hv with hn
      subst hn
      refine ⟨by simp, by simpa using hl, rfl⟩
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      obtain rfl := sub_one_inv op
      have hpred := val_sub_one hn
      obtain ⟨hle, hdrop, rfl⟩ := ih (n := n - 1) (by omega) ev' hl
      obtain ⟨z, zs, hzs, -, hrest⟩ := rep_cons_of_load hdrop ld
      have hlen : (n - 1).val < xs.length := by
        have := congrArg List.length hzs
        simp only [List.length_drop, List.length_cons] at this
        omega
      refine ⟨by omega, ?_, rfl⟩
      rw [← hpred, ← List.tail_drop, hzs]
      exact hrest

/-- **`Lists::take`** with the counter `n`: a derivation exists only for `n.val` at most the
length, and returns a fresh list of the first `n.val` elements. -/
theorem take_spec (hR : HeapMono₂ R) {xs : List α} :
    ∀ {l r : SourceValue F} {n : F} {h h' : Heap F} {cs : List (Call F)},
    ObsFn W (Instance.mk "Lists::take" [t]).symbol [l, .field n] h r h' cs →
    RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l →
    n.val ≤ xs.length ∧ RepList (Instance.mk "Lists::Node" [t]).symbol R h' (xs.take n.val) r := by
  induction xs with
  | nil =>
    intro l r n h h' cs ev hl
    rcases Obs.«Lists::take».obs ev with ⟨hv, rfl, rfl, -⟩ |
      ⟨x, rest, v, m, cs', w, hne, ld, rfl, rfl, op, ev', -⟩
    · injection hv with hn
      subst hn
      refine ⟨by simp, ?_⟩
      simpa using rep_store_nil (R := R) (en := (Instance.mk "Lists::Node" [t]).symbol) h
    · obtain ⟨z, zs, he, -, -⟩ := rep_cons_of_load hl ld
      cases he
  | cons z zs ih =>
    intro l r n h h' cs ev hl
    rcases Obs.«Lists::take».obs ev with ⟨hv, rfl, rfl, -⟩ |
      ⟨x, rest, v, m, cs', w, hne, ld, rfl, rfl, op, ev', -⟩
    · injection hv with hn
      subst hn
      refine ⟨by simp, ?_⟩
      simpa using rep_store_nil (R := R) (en := (Instance.mk "Lists::Node" [t]).symbol) h
    · have hn : n ≠ 0 := fun e => hne (by rw [e])
      obtain rfl := sub_one_inv op
      have hpred := val_sub_one hn
      obtain ⟨z', zs', he, hz, hzs⟩ := rep_cons_of_load hl ld
      injection he with h1 h2
      subst h1 h2
      obtain ⟨hle, hrec⟩ := ih ev' hzs
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      rw [← hpred, List.take_succ_cons]
      exact rep_store_cons hR (hR ev'.heap_extends hz) hrec

/-- **`Lists::lookup`** at the index `i`: the element at `i.val` (which exists); no
allocation. -/
theorem lookup_spec {xs : List α} {l r : SourceValue F} {i : F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W (Instance.mk "Lists::lookup" [t]).symbol [l, .field i] h r h' cs)
    (hl : RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l) :
    (∃ x, xs[i.val]? = some x ∧ R h x r) ∧ h' = h := by
  obtain ⟨m, p, cs', x, w, ev', ld, rfl, rfl, -⟩ := Obs.«Lists::lookup».obs ev
  obtain ⟨-, hdrop, rfl⟩ := drop_spec _ rfl ev' hl
  obtain ⟨z, zs, hzs, hz, -⟩ := rep_cons_of_load hdrop ld
  refine ⟨⟨z, ?_, hz⟩, rfl⟩
  rw [← List.head?_drop, hzs]
  rfl

/-- **`Lists::lookup_or_default`** at the index `i`: the element at `i.val`, or the default
exactly at `i.val = length` (a derivation exists only for `i.val` at most the length); no
allocation. -/
theorem lookup_or_default_spec {xs : List α} {l r dflt : SourceValue F} {i : F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W (Instance.mk "Lists::lookup_or_default" [t]).symbol [l, .field i, dflt] h r h' cs)
    (hl : RepList (Instance.mk "Lists::Node" [t]).symbol R h xs l) :
    h' = h ∧ ((∃ x, xs[i.val]? = some x ∧ R h x r) ∨ (i.val = xs.length ∧ r = dflt)) := by
  rcases Obs.«Lists::lookup_or_default».obs ev with ⟨m, p, cs', ev', ld, rfl, rfl, -⟩ |
    ⟨m, p, cs', x, w, ev', ld, rfl, rfl, -⟩
  · obtain ⟨hle, hdrop, rfl⟩ := drop_spec _ rfl ev' hl
    have hnil := rep_nil_of_load hdrop ld
    refine ⟨rfl, .inr ⟨?_, rfl⟩⟩
    have := congrArg List.length hnil
    simp only [List.length_drop, List.length_nil] at this
    omega
  · obtain ⟨-, hdrop, rfl⟩ := drop_spec _ rfl ev' hl
    obtain ⟨z, zs, hzs, hz, -⟩ := rep_cons_of_load hdrop ld
    refine ⟨rfl, .inl ⟨z, ?_, hz⟩⟩
    rw [← List.head?_drop, hzs]
    rfl

end Lists

end IxVM.Refinement.Lib
