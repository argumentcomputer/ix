import IxVMRefinement.Core.Registry
import IxVMRefinement.Obs.KernelLevels
import IxVMRefinement.Lib.Words
import IxVMRefinement.Lib.Lists
import IxC.Kernel.Verify.PropWhen

/-! # Step lemmas of the `Levels` family: the binder-datum and literal comparisons

`KernelLevels::pw_eq` compares the zero-ness data of two levels. The circuit reads a level's
datum as a pair (`KernelLevels::zero_set`): `(1, [])` for a level that is never zero, `(0, ps)`
for one that is zero exactly when every parameter of `ps` is, with `ps` strictly ascending
(the ascending union `glist_union` of the two sides' lists at a `max`). The pair is a function
of the datum (`zeroSet`, `zeronessOf_eq`), and it determines the datum: two strictly ascending
lists with the same members are equal (`pairwise_ext`), and the datum is canonical
(`PropWhen.ifAllZero_eq_iff`). So comparing the flags, then the lists (`glist_cmp`), decides
`la.zeronessOf = lb.zeronessOf` exactly.

`klimbs_eq`, `bytestream_eq` and `literal_eq` compare limb lists, byte strings and literals
element by element; each reads its recursive call (or its callee) from the induction
hypothesis.

`zero_set`, `glist_union` (and `glist_ordered_insert`, `glist_cmp`, which the level slice
already refines) are not registered: their lemmas here are proved by induction on the size of
the derivation (`ObsFn.strong_induction`). -/

namespace IxVM.Refinement.Core.LevelsAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepGuard RepGuardList repGuard_heapMono₂ glistCmp
  glistCmp_eq_zero_iff glistOrderedInsert glistOrderedInsert_mem glistOrderedInsert_pairwise
  glistCmp_refines glistOrderedInsert_refines natCast_lt_inj natCast_sub_eq_zero_iff)
open Ix.Kernel (PropWhen)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- A callee's derivation has fewer calls than its caller's. -/
macro "levels_lt_calls" : tactic =>
  `(tactic| (simp only [List.length_cons, List.length_append]; omega))

/-! ## The model -/

/-- The ascending union `KernelLevels::glist_union` computes: the elements of `xs` inserted
into `ys` one by one (`glistOrderedInsert`). -/
def glistUnion : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: rest, ys => glistUnion rest (glistOrderedInsert x ys).2

/-- The pair `KernelLevels::zero_set` computes, as a flag and a list: `(true, [])` for a level
that is never zero, `(false, ps)` for one that is zero exactly when every parameter of `ps`
is. -/
def zeroSet : KLevel → Bool × List Nat
  | .zero => (false, [])
  | .succ _ => (true, [])
  | .param n => (false, [n])
  | .max a b =>
    if (zeroSet a).1 then (true, [])
    else if (zeroSet b).1 then (true, [])
    else (false, glistUnion (zeroSet a).2 (zeroSet b).2)
  | .imax _ b => zeroSet b

/-- The zero-ness datum a `zero_set` pair stands for. -/
def toPW (z : Bool × List Nat) : PropWhen :=
  if z.1 then .never else .ifAllZero z.2

theorem mem_glistUnion : ∀ (xs ys : List Nat) (n : Nat),
    n ∈ glistUnion xs ys ↔ n ∈ xs ∨ n ∈ ys
  | [], ys, n => by simp [glistUnion]
  | x :: rest, ys, n => by
    rw [glistUnion, mem_glistUnion rest, glistOrderedInsert_mem, List.mem_cons]
    tauto

theorem pairwise_glistUnion : ∀ (xs : List Nat) {ys : List Nat},
    List.Pairwise (· < ·) ys → List.Pairwise (· < ·) (glistUnion xs ys)
  | [], _, h => by rw [glistUnion]; exact h
  | x :: rest, ys, h => by
    rw [glistUnion]
    exact pairwise_glistUnion rest (glistOrderedInsert_pairwise x h)

/-- Two strictly ascending lists with the same members are equal. -/
theorem pairwise_ext : ∀ {as bs : List Nat}, List.Pairwise (· < ·) as →
    List.Pairwise (· < ·) bs → (∀ n, n ∈ as ↔ n ∈ bs) → as = bs
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by simpa using (h b).mpr (by simp)
  | a :: _, [], _, _, h => by simpa using (h a).mp (by simp)
  | a :: as, b :: bs, ha, hb, h => by
    rw [List.pairwise_cons] at ha hb
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp (by simp)) with hx | hx
      · exact hx
      rcases List.mem_cons.mp ((h b).mpr (by simp)) with hy | hy
      · exact hy.symm
      exact absurd (hb.1 a hx) (Nat.lt_asymm (ha.1 b hy))
    subst hab
    have htail : ∀ n, n ∈ as ↔ n ∈ bs := by
      intro n
      constructor
      · intro hn
        rcases List.mem_cons.mp ((h n).mp (List.mem_cons_of_mem a hn)) with he | hn'
        · subst he
          exact absurd (ha.1 n hn) (Nat.lt_irrefl n)
        · exact hn'
      · intro hn
        rcases List.mem_cons.mp ((h n).mpr (List.mem_cons_of_mem a hn)) with he | hn'
        · subst he
          exact absurd (hb.1 n hn) (Nat.lt_irrefl n)
        · exact hn'
    rw [pairwise_ext ha.2 hb.2 htail]

/-- The lists `zero_set` produces are strictly ascending. -/
theorem zeroSet_pairwise : ∀ l : KLevel, List.Pairwise (· < ·) (zeroSet l).2
  | .zero => List.Pairwise.nil
  | .succ _ => List.Pairwise.nil
  | .param n => List.pairwise_singleton _ n
  | .max a b => by
    have hb := zeroSet_pairwise b
    rw [zeroSet]
    split
    · exact List.Pairwise.nil
    · split
      · exact List.Pairwise.nil
      · exact pairwise_glistUnion _ hb
  | .imax _ b => zeroSet_pairwise b

/-- **The pair is the datum**: a level's zero-ness datum is the one its `zero_set` pair stands
for. -/
theorem zeronessOf_eq : ∀ l : KLevel, l.zeronessOf = toPW (zeroSet l)
  | .zero => by simp [Ix.Kernel.Level.zeronessOf, zeroSet, toPW]
  | .succ _ => by simp [Ix.Kernel.Level.zeronessOf, zeroSet, toPW]
  | .param _ => by simp [Ix.Kernel.Level.zeronessOf, zeroSet, toPW]
  | .max a b => by
    have iha := zeronessOf_eq a
    have ihb := zeronessOf_eq b
    rw [Ix.Kernel.Level.zeronessOf, iha, ihb]
    cases ha : (zeroSet a).1 <;> cases hb : (zeroSet b).1 <;> simp [toPW, zeroSet, ha, hb]
    exact (PropWhen.ifAllZero_eq_iff _ _).mpr fun n => by rw [List.mem_append, mem_glistUnion]
  | .imax _ b => by
    rw [Ix.Kernel.Level.zeronessOf, zeroSet]
    exact zeronessOf_eq b

theorem toPW_never {z : Bool × List Nat} (h : z.1 = true) : toPW z = .never := by
  simp [toPW, h]

theorem toPW_ifAllZero {z : Bool × List Nat} (h : z.1 = false) : toPW z = .ifAllZero z.2 := by
  simp [toPW, h]

/-- Two data of strictly ascending lists are equal exactly when the lists are. -/
theorem ifAllZero_eq_iff_eq {sa sb : List Nat} (ha : List.Pairwise (· < ·) sa)
    (hb : List.Pairwise (· < ·) sb) :
    PropWhen.ifAllZero sa = PropWhen.ifAllZero sb ↔ sa = sb :=
  ⟨fun h => pairwise_ext ha hb ((PropWhen.ifAllZero_eq_iff sa sb).mp h), fun h => h ▸ rfl⟩

theorem glistCmp_lt_three : ∀ a b : List Nat, glistCmp a b < 3
  | [], [] => by simp [glistCmp]
  | [], _ :: _ => by simp [glistCmp]
  | _ :: _, [] => by simp [glistCmp]
  | x :: ar, y :: br => by
    have := glistCmp_lt_three ar br
    rw [glistCmp]
    split
    · omega
    · split
      · omega
      · exact this

theorem glistCmp_cast_eq_zero_iff (a b : List Nat) :
    ((glistCmp a b : Nat) : IxVM.F) = 0 ↔ a = b := by
  refine Iff.trans ?_ glistCmp_eq_zero_iff
  constructor
  · intro h
    exact natCast_lt_inj (B₁ := 3) (B₂ := 1) (glistCmp_lt_three a b) Nat.zero_lt_one
      (by rw [Nat.cast_zero]; exact h)
  · intro h
    rw [h, Nat.cast_zero]

/-! ## Values -/

/-- The guard parameter lists (`Lists::List<Field>`), as the path lemmas name their cells. -/
abbrev RepGL (h : Heap F) (xs : List Nat) (p : SourceValue F) : Prop :=
  RepList byteListEnum RepGuard h xs p

theorem repGL_mono {h₁ h₂ : Heap F} {xs : List Nat} {p : SourceValue F} (r : RepGL h₁ xs p)
    (ext : Heap.Extends h₁ h₂) : RepGL h₂ xs p :=
  RepLinkedList.mono repGuard_heapMono₂ ext r

theorem pair_inj {a b c d : SourceValue F} (h : Value.tuple [a, b] = .tuple [c, d]) :
    a = c ∧ b = d := by
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at h
  exact h

theorem flag_eq_one {b : Bool} (h : (Value.field (if b then 1 else 0) : SourceValue F) = .field 1) :
    b = true := by
  cases b
  · simp at h
  · rfl

theorem flag_ne_one {b : Bool} (h : (Value.field (if b then 1 else 0) : SourceValue F) ≠ .field 1) :
    b = false := by
  cases b
  · rfl
  · exact (h rfl).elim

/-- The difference of two flags is `0` exactly when they agree. -/
theorem flag_sub_inv {a b : Bool} {v : SourceValue F}
    (op : evalBinOp .sub (.field (if a then 1 else 0) : SourceValue F)
      (.field (if b then 1 else 0)) = .ok v) :
    v = .field 0 ↔ a = b := by
  simp only [evalBinOp, Except.ok.injEq] at op
  subst op
  cases a <;> cases b <;> simp

/-- The difference of two bytes is `0` exactly when they are equal. -/
theorem byte_sub_inv {a b : UInt8} {v : SourceValue F}
    (op : evalBinOp .sub (.field (a.toNat : F) : SourceValue F) (.field (b.toNat : F)) = .ok v) :
    v = .field 0 ↔ a = b := by
  simp only [evalBinOp, Except.ok.injEq] at op
  subst op
  constructor
  · intro hv
    have h0 : ((a.toNat : F) - (b.toNat : F)) = 0 := Value.field.inj hv
    exact UInt8.toNat_inj.mp
      ((natCast_sub_eq_zero_iff (B₁ := 256) (B₂ := 256) a.toNat_lt b.toNat_lt).mp h0)
  · intro e
    subst e
    simp

theorem load_nil {α : Type} {en : String} {R : Heap F → α → SourceValue F → Prop} {h : Heap F}
    {p : SourceValue F} (rep : RepList en R h [] p) :
    loadValue h p = .ok (.construct en "Nil" []) := by
  cases rep with
  | nil cell => exact loadValue_enum_cell cell

/-! ## Levels at their cells -/

theorem zero_of_load {h : Heap F} {l : KLevel} {p : SourceValue F} (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Zero" [])) : l = .zero := by
  cases rep with
  | zero cell => rfl
  | succ cell _ => exact (load_cell_ne cell ld (by decide)).elim
  | max cell _ _ => exact (load_cell_ne cell ld (by decide)).elim
  | imax cell _ _ => exact (load_cell_ne cell ld (by decide)).elim
  | param _ cell => exact (load_cell_ne cell ld (by decide)).elim

theorem succ_of_load {h : Heap F} {l : KLevel} {p x : SourceValue F} (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Succ" [x])) :
    ∃ u, l = .succ u ∧ RepKLevel h u x := by
  cases rep with
  | succ cell hu =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx
    subst hx
    exact ⟨_, rfl, hu⟩
  | zero cell => exact (load_cell_ne cell ld (by decide)).elim
  | max cell _ _ => exact (load_cell_ne cell ld (by decide)).elim
  | imax cell _ _ => exact (load_cell_ne cell ld (by decide)).elim
  | param _ cell => exact (load_cell_ne cell ld (by decide)).elim

theorem param_of_load {h : Heap F} {l : KLevel} {p x : SourceValue F} (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Param" [x])) :
    ∃ n, l = .param n ∧ n < 4294967296 ∧ x = .field (n : F) := by
  cases rep with
  | param hn cell =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx
    subst hx
    exact ⟨_, rfl, hn, rfl⟩
  | zero cell => exact (load_cell_ne cell ld (by decide)).elim
  | succ cell _ => exact (load_cell_ne cell ld (by decide)).elim
  | max cell _ _ => exact (load_cell_ne cell ld (by decide)).elim
  | imax cell _ _ => exact (load_cell_ne cell ld (by decide)).elim

theorem max_of_load {h : Heap F} {l : KLevel} {p x y : SourceValue F} (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "Max" [x, y])) :
    ∃ u v, l = .max u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | max cell hu hv =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx hrest
    injection hrest with hy
    subst hx hy
    exact ⟨_, _, rfl, hu, hv⟩
  | zero cell => exact (load_cell_ne cell ld (by decide)).elim
  | succ cell _ => exact (load_cell_ne cell ld (by decide)).elim
  | imax cell _ _ => exact (load_cell_ne cell ld (by decide)).elim
  | param _ cell => exact (load_cell_ne cell ld (by decide)).elim

theorem imax_of_load {h : Heap F} {l : KLevel} {p x y : SourceValue F} (rep : RepKLevel h l p)
    (ld : loadValue h p = .ok (.construct "KernelTypes::KLevelNode" "IMax" [x, y])) :
    ∃ u v, l = .imax u v ∧ RepKLevel h u x ∧ RepKLevel h v y := by
  cases rep with
  | imax cell hu hv =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with hx hrest
    injection hrest with hy
    subst hx hy
    exact ⟨_, _, rfl, hu, hv⟩
  | zero cell => exact (load_cell_ne cell ld (by decide)).elim
  | succ cell _ => exact (load_cell_ne cell ld (by decide)).elim
  | max cell _ _ => exact (load_cell_ne cell ld (by decide)).elim
  | param _ cell => exact (load_cell_ne cell ld (by decide)).elim

/-! ## `glist_union` and `zero_set` -/

theorem glist_union_spec_aux :
    ∀ (n : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
      (cs : List (Call F)), ObsFn W n args h r h' cs → n = "KernelLevels::glist_union" →
      ∀ (xs ys : List Nat) (px py : SourceValue F), args = [px, py] → RepGL h xs px →
        RepGL h ys py → RepGL h' (glistUnion xs ys) r :=
  ObsFn.strong_induction (world := W)
    (fun n args h r h' cs => n = "KernelLevels::glist_union" →
      ∀ (xs ys : List Nat) (px py : SourceValue F), args = [px, py] → RepGL h xs px →
        RepGL h ys py → RepGL h' (glistUnion xs ys) r)
    (fun n args h r h' cs ev ih hn xs ys px py hargs hxs hys => by
      subst hn hargs
      rcases Obs.«KernelLevels::glist_union».obs ev with
        ⟨ld12, he21, he22, hc23⟩ |
        ⟨x_x, x_rest, m42, cs52, x__ins, x_ys2, cs87, ld12, ev54, ev89, hc106⟩
      · obtain rfl := RepList.nil_of_load hxs ld12
        subst he21 he22
        rw [glistUnion]
        exact hys
      · obtain ⟨z, zs, rfl, ⟨hz, rfl⟩, hzs⟩ := RepList.cons_of_load hxs ld12
        subst hc106
        obtain ⟨po, hpo, hrep, ext⟩ := glistOrderedInsert_refines hz hys ev54.erase
        obtain ⟨-, rfl⟩ := pair_inj hpo
        rw [glistUnion]
        exact ih _ _ _ _ _ _ (by levels_lt_calls) ev89 rfl zs _ x_rest _ rfl (repGL_mono hzs ext)
          hrep)

/-- **`KernelLevels::glist_union`** on two guard lists: their ascending union, in the final
heap. -/
theorem glist_union_spec {xs ys : List Nat} {px py r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hxs : RepGL h xs px) (hys : RepGL h ys py)
    (ev : ObsFn W "KernelLevels::glist_union" [px, py] h r h' cs) :
    RepGL h' (glistUnion xs ys) r :=
  glist_union_spec_aux _ _ _ _ _ _ ev rfl xs ys px py rfl hxs hys

theorem zero_set_spec_aux :
    ∀ (n : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
      (cs : List (Call F)), ObsFn W n args h r h' cs → n = "KernelLevels::zero_set" →
      ∀ (l : KLevel) (p : SourceValue F), args = [p] → RepKLevel h l p →
        ∃ sp, r = .tuple [.field (if (zeroSet l).1 then 1 else 0), sp] ∧
          RepGL h' (zeroSet l).2 sp :=
  ObsFn.strong_induction (world := W)
    (fun n args h r h' cs => n = "KernelLevels::zero_set" →
      ∀ (l : KLevel) (p : SourceValue F), args = [p] → RepKLevel h l p →
        ∃ sp, r = .tuple [.field (if (zeroSet l).1 then 1 else 0), sp] ∧
          RepGL h' (zeroSet l).2 sp)
    (fun n args h r h' cs ev ih hn l p hargs hrep => by
      subst hn hargs
      rcases Obs.«KernelLevels::zero_set».obs ev with
        ⟨m32, ld12, he24, hm40, he44, hc45⟩ |
        ⟨w53, m71, ld12, he63, hm79, he83, hc84⟩ |
        ⟨x_i, m109, m131, ld12, he101, hm117, hm139, he143, hc144⟩ |
        ⟨x_a, x_b, m163, cs173, x_sa, m223, ld12, ev175, he215, hm231, he235, hc236⟩ |
        ⟨x_a, x_b, m163, cs173, x_na, x_sa, m242, cs252, x_sb, m302, ld12, ev175, hne237, ev254,
          he294, hm310, he314, hc315⟩ |
        ⟨x_a, x_b, m163, cs173, x_na, x_sa, m242, cs252, x_nb, x_sb, v323, m332, cs340, ld12,
          ev175, hne237, ev254, hne316, he324, ev342, he359, hc360⟩ |
        ⟨w368, x_b, cs382, ld12, ev384, hc393⟩
      · -- `Zero`: `(0, [])`
        obtain rfl := zero_of_load hrep ld12
        subst he44 hm40 he24
        exact ⟨_, rfl, Lib.rep_store_nil h⟩
      · -- `Succ`: `(1, [])`
        obtain ⟨u, rfl, -⟩ := succ_of_load hrep ld12
        subst he83 hm79 he63
        exact ⟨_, rfl, Lib.rep_store_nil h⟩
      · -- `Param(n)`: `(0, [n])`
        obtain ⟨k, rfl, hk, rfl⟩ := param_of_load hrep ld12
        subst he143 hm117 hm139 he101
        exact ⟨_, rfl, Lib.rep_store_cons repGuard_heapMono₂ ⟨hk, rfl⟩ (Lib.rep_store_nil h)⟩
      · -- `Max`, the left side never zero
        obtain ⟨u, v, rfl, hu, hv⟩ := max_of_load hrep ld12
        subst hc236
        obtain ⟨spu, hru, -⟩ := ih _ _ _ _ _ _ (by levels_lt_calls) ev175 rfl u x_a rfl hu
        have fu : (zeroSet u).1 = true := flag_eq_one (pair_inj hru).1.symm
        subst he235 hm231 he215
        have hz : zeroSet (.max u v) = (true, []) := by simp [zeroSet, fu]
        rw [hz]
        exact ⟨_, rfl, Lib.rep_store_nil m163⟩
      · -- `Max`, the right side never zero
        obtain ⟨u, v, rfl, hu, hv⟩ := max_of_load hrep ld12
        subst hc315
        obtain ⟨spu, hru, -⟩ := ih _ _ _ _ _ _ (by levels_lt_calls) ev175 rfl u x_a rfl hu
        obtain ⟨rfl, -⟩ := pair_inj hru
        have fu : (zeroSet u).1 = false := flag_ne_one hne237
        obtain ⟨spv, hrv, -⟩ := ih _ _ _ _ _ _ (by levels_lt_calls) ev254 rfl v x_b rfl
          (hv.mono (ObsFn.heap_extends ev175))
        have fv : (zeroSet v).1 = true := flag_eq_one (pair_inj hrv).1.symm
        subst he314 hm310 he294
        have hz : zeroSet (.max u v) = (true, []) := by simp [zeroSet, fu, fv]
        rw [hz]
        exact ⟨_, rfl, Lib.rep_store_nil m242⟩
      · -- `Max`, both sides possibly zero: the union
        obtain ⟨u, v, rfl, hu, hv⟩ := max_of_load hrep ld12
        subst hc360
        have e175 := ObsFn.heap_extends ev175
        have e254 := ObsFn.heap_extends ev254
        obtain ⟨spu, hru, hsu⟩ := ih _ _ _ _ _ _ (by levels_lt_calls) ev175 rfl u x_a rfl hu
        obtain ⟨rfl, rfl⟩ := pair_inj hru
        have fu : (zeroSet u).1 = false := flag_ne_one hne237
        obtain ⟨spv, hrv, hsv⟩ := ih _ _ _ _ _ _ (by levels_lt_calls) ev254 rfl v x_b rfl
          (hv.mono e175)
        obtain ⟨rfl, rfl⟩ := pair_inj hrv
        have fv : (zeroSet v).1 = false := flag_ne_one hne316
        have hun := glist_union_spec (repGL_mono hsu e254) hsv ev342
        subst he359 he324
        have hz : zeroSet (.max u v) = (false, glistUnion (zeroSet u).2 (zeroSet v).2) := by
          simp [zeroSet, fu, fv]
        rw [hz]
        exact ⟨_, rfl, hun⟩
      · -- `IMax`: the right side's
        obtain ⟨u, v, rfl, -, hv⟩ := imax_of_load hrep ld12
        subst hc393
        exact ih _ _ _ _ _ _ (by levels_lt_calls) ev384 rfl v x_b rfl hv)

/-- **`KernelLevels::zero_set`** on a represented level: the flag `1` exactly for a level that
is never zero, and the strictly ascending list of `zeroSet`, in the final heap. -/
theorem zero_set_spec {l : KLevel} {h h' : Heap F} {p r : SourceValue F} {cs : List (Call F)}
    (hrep : RepKLevel h l p) (ev : ObsFn W "KernelLevels::zero_set" [p] h r h' cs) :
    ∃ sp, r = .tuple [.field (if (zeroSet l).1 then 1 else 0), sp] ∧ RepGL h' (zeroSet l).2 sp :=
  zero_set_spec_aux _ _ _ _ _ _ ev rfl l p rfl hrep

/-! ## Literals -/

theorem lit_nat_inv {h : Heap F} {ld : Specs.Levels.LitData} {x : SourceValue F}
    (hr : Specs.Levels.LitRep h ld (.construct "KernelTypes::KLiteral" "Nat" [x])) :
    ∃ limbs, ld = .nat limbs ∧ RepList limbListEnum RepU64 h limbs x := by
  cases ld with
  | nat limbs =>
    obtain ⟨lp, hv, hl⟩ := hr
    injection hv with _ _ hargs
    injection hargs with hx
    subst hx
    exact ⟨limbs, rfl, hl⟩
  | str bytes =>
    obtain ⟨bp, hv, -⟩ := hr
    injection hv with _ hc _
    exact absurd hc (by decide)

theorem lit_str_inv {h : Heap F} {ld : Specs.Levels.LitData} {x : SourceValue F}
    (hr : Specs.Levels.LitRep h ld (.construct "KernelTypes::KLiteral" "Str" [x])) :
    ∃ bytes, ld = .str bytes ∧ RepBytes h bytes x := by
  cases ld with
  | str bytes =>
    obtain ⟨bp, hv, hl⟩ := hr
    injection hv with _ _ hargs
    injection hargs with hx
    subst hx
    exact ⟨bytes, rfl, hl⟩
  | nat limbs =>
    obtain ⟨lp, hv, -⟩ := hr
    injection hv with _ hc _
    exact absurd hc (by decide)

end IxVM.Refinement.Core.LevelsAux

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel glistCmp_refines)
open Ix.Kernel (PropWhen)
open LevelsAux

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## `pw_eq` -/

/-- `KernelLevels::pw_eq` decides whether two levels have the same zero-ness datum: equal
flags, and at flag `0` equal lists (`glist_cmp`). -/
theorem pw_eq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    {calls : List (Call F)} (ev : ObsFn W "KernelLevels::pw_eq" args h r h' calls) (ih : IH c calls) :
    Specs.Levels.pw_eq c args h r h' calls := by
  intro a b hargs good la lb ha hb
  subst hargs
  refine ⟨?_, ObsFn.heap_extends ev⟩
  rw [zeronessOf_eq la, zeronessOf_eq lb]
  rcases Obs.«KernelLevels::pw_eq».obs ev with
    ⟨m2, cs12, x_sa, m37, cs47, x_nb, x_sb, ev14, ev49, op87, he108, he109, hc110⟩ |
    ⟨m2, cs12, x_na, x_sa, m37, cs47, x_nb, x_sb, cs118, v121, m123, cs131, ev14, ev49, op87,
      hne111, ev133, ev120, hc150⟩ |
    ⟨m2, cs12, x_na, x_sa, m37, cs47, x_nb, x_sb, v71, ev14, ev49, op87, hne151, he155, he156,
      hc157⟩
  · -- both never zero
    obtain ⟨spa, hra, -⟩ := zero_set_spec ha ev14
    obtain ⟨spb, hrb, -⟩ := zero_set_spec (hb.mono (ObsFn.heap_extends ev14)) ev49
    have fa : (zeroSet la).1 = true := flag_eq_one (pair_inj hra).1.symm
    obtain ⟨rfl, -⟩ := pair_inj hrb
    have fb : (zeroSet lb).1 = true :=
      ((flag_sub_inv (a := true) op87).mp rfl).symm
    rw [he108, toPW_never fa, toPW_never fb, ite_eq_left rfl]
  · -- both possibly zero: the lists
    have e14 := ObsFn.heap_extends ev14
    have e49 := ObsFn.heap_extends ev49
    obtain ⟨spa, hra, hsa⟩ := zero_set_spec ha ev14
    obtain ⟨spb, hrb, hsb⟩ := zero_set_spec (hb.mono e14) ev49
    obtain ⟨rfl, rfl⟩ := pair_inj hra
    obtain ⟨rfl, rfl⟩ := pair_inj hrb
    have fa : (zeroSet la).1 = false := flag_ne_one hne111
    have fb : (zeroSet lb).1 = false := by
      rw [← fa]
      exact ((flag_sub_inv op87).mp rfl).symm
    obtain ⟨hv, rfl⟩ := glistCmp_refines (repGL_mono hsa e49) hsb ev133.erase
    subst hv
    obtain ⟨hr, -⟩ := Lib.is_zero_field ev120
    have hpw := ifAllZero_eq_iff_eq (zeroSet_pairwise la) (zeroSet_pairwise lb)
    rw [hr, toPW_ifAllZero fa, toPW_ifAllZero fb]
    by_cases hab : (zeroSet la).2 = (zeroSet lb).2
    · rw [ite_eq_left ((glistCmp_cast_eq_zero_iff _ _).mpr hab), ite_eq_left (hpw.mpr hab)]
    · rw [ite_eq_right (fun e => hab ((glistCmp_cast_eq_zero_iff _ _).mp e)),
        ite_eq_right (fun e => hab (hpw.mp e))]
  · -- different flags
    obtain ⟨spa, hra, -⟩ := zero_set_spec ha ev14
    obtain ⟨spb, hrb, -⟩ := zero_set_spec (hb.mono (ObsFn.heap_extends ev14)) ev49
    obtain ⟨rfl, -⟩ := pair_inj hra
    obtain ⟨rfl, -⟩ := pair_inj hrb
    have hne : (zeroSet la).1 ≠ (zeroSet lb).1 := fun e => hne151 ((flag_sub_inv op87).mpr e)
    rw [he155]
    cases fa : (zeroSet la).1 <;> cases fb : (zeroSet lb).1
    · exact absurd (fa.trans fb.symm) hne
    · rw [toPW_ifAllZero fa, toPW_never fb, ite_eq_right (PropWhen.ifAllZero_ne_never _)]
    · rw [toPW_never fa, toPW_ifAllZero fb, ite_eq_right (Ne.symm (PropWhen.ifAllZero_ne_never _))]
    · exact absurd (fa.trans fb.symm) hne

/-! ## Literals -/

/-- `KernelLevels::klimbs_eq` compares two limb lists limb by limb. -/
theorem klimbs_eq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::klimbs_eq" args h r h' calls) (ih : IH c calls) :
    Specs.Levels.klimbs_eq c args h r h' calls := by
  intro a b hargs good la lb ha hb
  subst hargs
  rcases Obs.«KernelLevels::klimbs_eq».obs ev with
    ⟨ld12, ld31, he39, he40, hc41⟩ |
    ⟨v20, ld12, ld31, hne42, he46, he47, hc48⟩ |
    ⟨x_la, x_ra, ld12, ld77, he85, he86, hc87⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, m106, cs116, cs152, ld12, ld77, ev118, ev154, hc171⟩ |
    ⟨x_la, x_ra, x_lb, x_rb, m106, cs116, ld12, ld77, ev118, he177, he178, hc179⟩
  · obtain rfl := RepList.nil_of_load ha ld12
    obtain rfl := RepList.nil_of_load hb ld31
    exact ⟨by rw [he39, ite_eq_left rfl], he40⟩
  · obtain rfl := RepList.nil_of_load ha ld12
    refine ⟨?_, he47⟩
    rw [he46]
    cases lb with
    | nil =>
      have hl := load_nil hb
      rw [ld31] at hl
      injection hl with hv
      exact absurd hv (hne42 [] rfl)
    | cons z zs => simp
  · obtain ⟨x, xs, rfl, -, -⟩ := RepList.cons_of_load ha ld12
    obtain rfl := RepList.nil_of_load hb ld77
    exact ⟨by rw [he85]; simp, he86⟩
  · obtain ⟨x, xs, rfl, hx, hxs⟩ := RepList.cons_of_load ha ld12
    obtain ⟨y, ys, rfl, hy, hys⟩ := RepList.cons_of_load hb ld77
    subst hc171
    obtain ⟨heq, rfl⟩ := Lib.u64_eq_spec hx hy ev118
    have hxy : x = y := by
      by_contra hne
      rw [ite_eq_right (fun e => hne (UInt64.toNat_inj.mp e))] at heq
      exact one_ne_zero (Value.field.inj heq)
    subst hxy
    obtain ⟨hr, hh⟩ := ih.get (.levels .klimbs_eq) (by levels_lt_calls) ev154 x_ra x_rb rfl
      (good.sub fun z hz => by simp [hz]) xs ys hxs hys
    refine ⟨?_, hh⟩
    rw [hr]
    simp
  · obtain ⟨x, xs, rfl, hx, -⟩ := RepList.cons_of_load ha ld12
    obtain ⟨y, ys, rfl, hy, -⟩ := RepList.cons_of_load hb ld77
    obtain ⟨heq, rfl⟩ := Lib.u64_eq_spec hx hy ev118
    have hxy : x ≠ y := by
      intro e
      subst e
      rw [ite_eq_left rfl] at heq
      exact zero_ne_one (Value.field.inj heq)
    refine ⟨?_, he178⟩
    rw [he177, ite_eq_right (fun e => hxy (List.cons.inj e).1)]

/-- `KernelLevels::bytestream_eq` compares two byte strings byte by byte. -/
theorem bytestream_eq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::bytestream_eq" args h r h' calls) (ih : IH c calls) :
    Specs.Levels.bytestream_eq c args h r h' calls := by
  intro a b hargs good xs ys ha hb
  subst hargs
  rcases Obs.«KernelLevels::bytestream_eq».obs ev with
    ⟨ld12, ld31, he39, he40, hc41⟩ |
    ⟨v20, ld12, ld31, hne42, he46, he47, hc48⟩ |
    ⟨x_ba, x_ra, ld12, ld77, he85, he86, hc87⟩ |
    ⟨x_ba, x_ra, x_bb, x_rb, m106, x114, y115, m116, cs125, cs139, cs157, ld12, ld77, ev127,
      ev141, op121, ev159, hc176⟩ |
    ⟨x_ba, x_ra, x_bb, x_rb, v105, m106, x114, y115, m116, cs125, cs139, ld12, ld77, ev127, ev141,
      op121, hne177, he181, he182, hc183⟩
  · obtain rfl := RepList.nil_of_load ha ld12
    obtain rfl := RepList.nil_of_load hb ld31
    exact ⟨by rw [he39, ite_eq_left rfl], he40⟩
  · obtain rfl := RepList.nil_of_load ha ld12
    refine ⟨?_, he47⟩
    rw [he46]
    cases ys with
    | nil =>
      have hl := load_nil hb
      rw [ld31] at hl
      injection hl with hv
      exact absurd hv (hne42 [] rfl)
    | cons z zs => simp
  · obtain ⟨x, xs', rfl, -, -⟩ := RepList.cons_of_load ha ld12
    obtain rfl := RepList.nil_of_load hb ld77
    exact ⟨by rw [he85]; simp, he86⟩
  · obtain ⟨x, xs', rfl, hx, hxs⟩ := RepList.cons_of_load ha ld12
    obtain ⟨y, ys', rfl, hy, hys⟩ := RepList.cons_of_load hb ld77
    subst hc176
    obtain ⟨e1, rfl⟩ := Lib.u8_to_field_spec ev127
    obtain ⟨e2, rfl⟩ := Lib.u8_to_field_spec ev141
    have hx' : x114 = .field (x.toNat : F) := e1.trans hx
    have hy' : y115 = .field (y.toNat : F) := e2.trans hy
    rw [hx', hy'] at op121
    have hxy : x = y := (byte_sub_inv op121).mp rfl
    subst hxy
    obtain ⟨hr, hh⟩ := ih.get (.levels .bytestream_eq) (by levels_lt_calls) ev159 x_ra x_rb rfl
      (good.sub fun z hz => by simp [hz]) xs' ys' hxs hys
    refine ⟨?_, hh⟩
    rw [hr]
    simp
  · obtain ⟨x, xs', rfl, hx, -⟩ := RepList.cons_of_load ha ld12
    obtain ⟨y, ys', rfl, hy, -⟩ := RepList.cons_of_load hb ld77
    obtain ⟨e1, rfl⟩ := Lib.u8_to_field_spec ev127
    obtain ⟨e2, rfl⟩ := Lib.u8_to_field_spec ev141
    have hx' : x114 = .field (x.toNat : F) := e1.trans hx
    have hy' : y115 = .field (y.toNat : F) := e2.trans hy
    rw [hx', hy'] at op121
    have hxy : x ≠ y := fun e => hne177 ((byte_sub_inv op121).mpr e)
    refine ⟨?_, he182⟩
    rw [he181, ite_eq_right (fun e => hxy (List.cons.inj e).1)]

/-- `KernelLevels::literal_eq` compares two literals of the same kind by their data, and answers
`0` across kinds. -/
theorem literal_eq_step (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelLevels::literal_eq" args h r h' calls) (ih : IH c calls) :
    Specs.Levels.literal_eq c args h r h' calls := by
  intro a b hargs good la lb ha hb
  subst hargs
  rcases Obs.«KernelLevels::literal_eq».obs ev with
    ⟨x_na, x_nb, cs46, hv15, hv36, ev48, hc65⟩ |
    ⟨x_na, hv15, hne66, he70, he71, hc72⟩ |
    ⟨x_sa, x_sb, cs109, hne73, hv78, hv99, ev111, hc128⟩ |
    ⟨x_sa, hne73, hv78, hne129, he133, he134, hc135⟩
  · subst hv15 hv36 hc65
    obtain ⟨la', rfl, hla⟩ := lit_nat_inv ha
    obtain ⟨lb', rfl, hlb⟩ := lit_nat_inv hb
    obtain ⟨hr, hh⟩ := ih.get (.levels .klimbs_eq) (by levels_lt_calls) ev48 x_na x_nb rfl
      (good.sub fun z hz => by simp [hz]) la' lb' hla hlb
    refine ⟨?_, hh⟩
    rw [hr]
    simp
  · subst hv15
    obtain ⟨la', rfl, -⟩ := lit_nat_inv ha
    refine ⟨?_, he71⟩
    rw [he70]
    cases lb with
    | nat lb' =>
      obtain ⟨lp, hlp, -⟩ := hb
      exact absurd hlp (hne66 [lp] rfl)
    | str bs => simp
  · subst hv78 hv99 hc128
    obtain ⟨la', rfl, hla⟩ := lit_str_inv ha
    obtain ⟨lb', rfl, hlb⟩ := lit_str_inv hb
    obtain ⟨hr, hh⟩ := ih.get (.levels .bytestream_eq) (by levels_lt_calls) ev111 x_sa x_sb rfl
      (good.sub fun z hz => by simp [hz]) la' lb' hla hlb
    refine ⟨?_, hh⟩
    rw [hr]
    simp
  · subst hv78
    obtain ⟨la', rfl, -⟩ := lit_str_inv ha
    refine ⟨?_, he134⟩
    rw [he133]
    cases lb with
    | str lb' =>
      obtain ⟨bp, hbp, -⟩ := hb
      exact absurd hbp (hne129 [bp] rfl)
    | nat ns => simp

/-! ## The family -/

/-- **The family's steps**, for the registry harness. -/
theorem levels_step (c : Ctx) :
    ∀ (f : Specs.Levels.Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F)
      (h' : Heap F) (cs : List (Call F)), ObsFn W (Fn.levels f).name args h r h' cs → IH c cs →
      (Fn.levels f).spec c args h r h' cs
  | .pw_eq, _, _, _, _, _, ev, ih => pw_eq_step c ev ih
  | .literal_eq, _, _, _, _, _, ev, ih => literal_eq_step c ev ih
  | .klimbs_eq, _, _, _, _, _, ev, ih => klimbs_eq_step c ev ih
  | .bytestream_eq, _, _, _, _, _, ev, ih => bytestream_eq_step c ev ih

end IxVM.Refinement.Core
