import Ix.CompileCert.Canon.Level

/-!
# M7 L1: names, addresses, and the constant-reference leaf

`Ix.Name` compares by its cached hash: `a == b` is `a.getHash == b.getHash` and `compare`
(`Ix.nameCompare`) is the byte order of the hashes. Both are lawful on the hashes
(`name_beq_iff`, `nameCompare_eq_iff`, `Std.TransCmp Ix.nameCompare`), so `==` is an
equivalence and the class context `MutCtx` (a `Std.TreeMap` under `nameCompare`) answers
alike for `==` names (`mutCtx_get?_congr`).

The leaf `compareRef` (design document §3.2, "constant references": the map `κ`) is a total
preorder on the ok-domain at a fixed context (`compareRef_total`), under one hypothesis on
the caller's address map: `addr?` gives `==` names the same answer (`AddrCongr`). The
comparison itself never needs it for `==` names (they are equal before any lookup); it is
needed for transitivity through a `==` pair, where one side's address stands for the
other's. The compiler's maps are hash maps keyed by `Ix.Name` under the same `==`.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name)

/-! ## Addresses -/

theorem addr_beq_iff {a b : Address} : (a == b) = true ↔ a = b := by
  obtain ⟨⟨x⟩⟩ := a
  obtain ⟨⟨y⟩⟩ := b
  show (ByteArray.beq ⟨x⟩ ⟨y⟩) = true ↔ _
  simp [ByteArray.beq]

theorem addr_data_inj {a b : Address} (h : a.hash.data.toList = b.hash.data.toList) : a = b := by
  obtain ⟨⟨x⟩⟩ := a
  obtain ⟨⟨y⟩⟩ := b
  simp only at h
  have : x = y := Array.toList_inj.1 h
  subst this; rfl

/-- Comparison of two `Ord` keys read through a function. -/
theorem transCmp_comap {α : Type u} {β : Type v} (cmp : β → β → Ordering) [Std.TransCmp cmp]
    (f : α → β) : Std.TransCmp (fun a b => cmp (f a) (f b)) where
  eq_swap := Std.OrientedCmp.eq_swap (cmp := cmp)
  isLE_trans h1 h2 := Std.TransCmp.isLE_trans (cmp := cmp) h1 h2

instance transCmp_address : Std.TransCmp (compare : Address → Address → Ordering) :=
  transCmp_comap (cmp := @compare (List UInt8) (@List.instOrd UInt8 UInt8.instOrd))
    (fun a : Address => a.hash.data.toList)

theorem address_compare_eq_iff {a b : Address} : compare a b = .eq ↔ a = b := by
  constructor
  · intro h
    have : @compare (List UInt8) (@List.instOrd UInt8 UInt8.instOrd)
        a.hash.data.toList b.hash.data.toList = .eq := h
    exact addr_data_inj (Std.LawfulEqCmp.eq_of_compare this)
  · rintro rfl; exact Std.ReflCmp.compare_self (cmp := (compare : Address → Address → Ordering))

/-! ## Names -/

theorem name_beq_iff {a b : Name} : (a == b) = true ↔ a.getHash = b.getHash :=
  addr_beq_iff

theorem name_beq_refl (a : Name) : (a == a) = true := name_beq_iff.2 rfl

theorem name_beq_symm {a b : Name} (h : (a == b) = true) : (b == a) = true :=
  name_beq_iff.2 (name_beq_iff.1 h).symm

theorem name_beq_trans {a b c : Name} (h1 : (a == b) = true) (h2 : (b == c) = true) :
    (a == c) = true :=
  name_beq_iff.2 ((name_beq_iff.1 h1).trans (name_beq_iff.1 h2))

theorem name_beq_comm (a b : Name) : (a == b) = (b == a) := by
  cases h : (a == b) <;> cases h' : (b == a) <;> first
    | rfl
    | (exfalso; simp_all [name_beq_symm h])
    | (have := name_beq_symm h'; simp_all)

instance transCmp_nameCompare : Std.TransCmp Ix.nameCompare :=
  transCmp_comap (cmp := (compare : Address → Address → Ordering)) Name.getHash

theorem nameCompare_eq_iff {a b : Name} : Ix.nameCompare a b = .eq ↔ (a == b) = true := by
  rw [name_beq_iff]; exact address_compare_eq_iff

/-- The class context answers alike for `==` names. -/
theorem mutCtx_get?_congr (m : Ix.MutCtx) {a b : Name} (h : (a == b) = true) :
    m.get? a = m.get? b := by
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.get?_eq_getElem?]
  exact Std.TreeMap.getElem?_congr (nameCompare_eq_iff.2 h)

/-! ## The reference leaf -/

/-- The caller's address map gives `==` names the same answer. -/
def AddrCongr (addr? : Name → Option Address) : Prop :=
  ∀ a b : Name, (a == b) = true → addr? a = addr? b

theorem mutCtx_getElem?_congr (m : Ix.MutCtx) {a b : Name} (h : (a == b) = true) :
    m[a]? = m[b]? :=
  Std.TreeMap.getElem?_congr (nameCompare_eq_iff.2 h)

theorem compareRef_beq (c : CmpCtx) {x y : Name} (h : (x == y) = true) :
    compareRef c x y = .ok ⟨true, .eq⟩ := by
  simp [compareRef, h, pure, Except.pure]

theorem compareRef_in_in (c : CmpCtx) {x y : Name} (h : (x == y) = false) {nx ny : Nat}
    (hx : c.mutCtx[x]? = some nx) (hy : c.mutCtx[y]? = some ny) :
    compareRef c x y = .ok ⟨false, compare nx ny⟩ := by
  simp only [compareRef, h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]
  rfl

theorem compareRef_in_out (c : CmpCtx) {x y : Name} (h : (x == y) = false) {nx : Nat}
    (hx : c.mutCtx[x]? = some nx) (hy : c.mutCtx[y]? = none) :
    compareRef c x y = .ok ⟨true, .lt⟩ := by
  simp only [compareRef, h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]
  rfl

theorem compareRef_out_in (c : CmpCtx) {x y : Name} (h : (x == y) = false) {ny : Nat}
    (hx : c.mutCtx[x]? = none) (hy : c.mutCtx[y]? = some ny) :
    compareRef c x y = .ok ⟨true, .gt⟩ := by
  simp only [compareRef, h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]
  rfl

theorem compareRef_out_out (c : CmpCtx) {x y : Name} (h : (x == y) = false)
    (hx : c.mutCtx[x]? = none) (hy : c.mutCtx[y]? = none) :
    compareRef c x y = compareExternal c x y := by
  simp only [compareRef, h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]

theorem compareExternal_swap (c : CmpCtx) (x y : Name) {s o}
    (h : compareExternal c x y = .ok ⟨s, o⟩) : compareExternal c y x = .ok ⟨s, o.swap⟩ := by
  unfold compareExternal at h ⊢
  cases hm : c.mode <;> simp only [hm] at h ⊢
  · cases hx : c.addr? x <;> cases hy : c.addr? y <;> simp_all [pure, Except.pure]
    obtain ⟨rfl, rfl⟩ := h
    exact Std.OrientedCmp.eq_swap (cmp := (compare : Address → Address → Ordering))
  · simp_all [pure, Except.pure]
    obtain ⟨rfl, rfl⟩ := h; rfl

/-- The block-membership tag of a name: `0` in the block, `1` external. -/
def refTag (c : CmpCtx) (n : Name) : Nat :=
  match c.mutCtx[n]? with
  | some _ => 0
  | none => 1

theorem nbeq_of_refTag (c : CmpCtx) {x y : Name} (ht : refTag c x ≠ refTag c y) :
    (x == y) = false := by
  cases h : (x == y)
  · rfl
  · exfalso; apply ht; simp [refTag, mutCtx_getElem?_congr c.mutCtx h]

theorem compareRef_total (c : CmpCtx) (hc : AddrCongr c.addr?) :
    TotalPre (compareRef c) := by
  -- in-block before external, strongly
  refine PreOn.ofTag (refTag c) ?_ ?_
  · intro x y _ _ ht
    have hne := nbeq_of_refTag c ht
    cases hx : c.mutCtx[x]? <;> cases hy : c.mutCtx[y]? <;> simp only [refTag, hx, hy] at ht
    · exact absurd rfl ht
    · rw [compareRef_out_in c hne hx hy]; simp only [refTag, hx, hy]; rfl
    · rw [compareRef_in_out c hne hx hy]; simp only [refTag, hx, hy]; rfl
    · exact absurd rfl ht
  intro T
  match T with
  | 0 =>
    -- two in-block names: by class index
    have key : ∀ x y, refTag c x = 0 → refTag c y = 0 →
        ∃ s, compareRef c x y = .ok ⟨s, compare ((c.mutCtx[x]?).getD 0)
          ((c.mutCtx[y]?).getD 0)⟩ ∧ (s = (x == y)) := by
      intro x y hx hy
      cases hnx : c.mutCtx[x]? with
      | none => simp [refTag, hnx] at hx
      | some nx =>
        cases hny : c.mutCtx[y]? with
        | none => simp [refTag, hny] at hy
        | some ny =>
          cases h : (x == y)
          · exact ⟨false, by rw [compareRef_in_in c h hnx hny]; rfl, rfl⟩
          · refine ⟨true, ?_, rfl⟩
            rw [compareRef_beq c h]
            rw [mutCtx_getElem?_congr c.mutCtx h] at hnx
            rw [hnx] at hny; cases hny
            simp
    constructor
    · intro x y hx hy s o hxy
      obtain ⟨s1, e1, h1⟩ := key x y hx.2 hy.2
      obtain ⟨s2, e2, h2⟩ := key y x hy.2 hx.2
      rw [e1] at hxy
      simp only [Except.ok.injEq, SOrder.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      rw [e2, h1, h2, name_beq_comm x y]
      simp only [Except.ok.injEq, SOrder.mk.injEq, true_and]
      exact Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering))
    · intro x y z hx hy hz h1 h2
      obtain ⟨s1, e1, -⟩ := key x y hx.2 hy.2
      obtain ⟨s2, e2, -⟩ := key y z hy.2 hz.2
      obtain ⟨s3, e3, -⟩ := key x z hx.2 hz.2
      obtain ⟨_, _, h1, n1⟩ := h1
      obtain ⟨_, _, h2, n2⟩ := h2
      rw [e1] at h1; rw [e2] at h2
      simp only [Except.ok.injEq, SOrder.mk.injEq] at h1 h2
      obtain ⟨-, rfl⟩ := h1; obtain ⟨-, rfl⟩ := h2
      refine ⟨s3, _, e3, ?_⟩
      exact Ordering.isLE_iff_ne_gt.1
        (Std.TransCmp.isLE_trans (cmp := (compare : Nat → Nat → Ordering))
          (Ordering.isLE_iff_ne_gt.2 n1) (Ordering.isLE_iff_ne_gt.2 n2))
  | 1 =>
    -- two external names: equal names first, then by address (or all equal, blind)
    have out : ∀ {x}, refTag c x = 1 → c.mutCtx[x]? = none := by
      intro x hx; cases h : c.mutCtx[x]? <;> simp_all [refTag]
    constructor
    · intro x y hx hy s o hxy
      cases h : (x == y)
      · rw [compareRef_out_out c h (out hx.2) (out hy.2)] at hxy
        rw [compareRef_out_out c (by rw [name_beq_comm]; exact h) (out hy.2) (out hx.2)]
        exact compareExternal_swap c x y hxy
      · rw [compareRef_beq c h] at hxy
        simp only [Except.ok.injEq, SOrder.mk.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        exact compareRef_beq c (name_beq_symm h)
    · intro x y z hx hy hz h1 h2
      have ex := out hx.2; have ey := out hy.2; have ez := out hz.2
      by_cases hxz : (x == z) = true
      · exact ⟨true, .eq, compareRef_beq c hxz, by decide⟩
      have hxz' : (x == z) = false := by simpa using hxz
      rw [compareRef_out_out c hxz' ex ez]
      unfold compareExternal
      cases hm : c.mode
      · -- by address: every step that is not `==` has both addresses
        have addrOf : ∀ u v, c.mutCtx[u]? = none → c.mutCtx[v]? = none → Le (compareRef c u v) →
            (u == v) = true ∨ ∃ au av, c.addr? u = some au ∧ c.addr? v = some av ∧
              compare au av ≠ .gt := by
          intro u v hu hv hle
          cases huv : (u == v)
          · right
            rw [compareRef_out_out c huv hu hv] at hle
            obtain ⟨s, o, he, hne⟩ := hle
            unfold compareExternal at he
            simp only [hm] at he
            cases hau : c.addr? u <;> cases hav : c.addr? v <;> simp_all [pure, Except.pure]
          · exact .inl rfl
        rcases addrOf x y ex ey h1 with hxy | ⟨ax, ay, hax, hay, n1⟩ <;>
          rcases addrOf y z ey ez h2 with hyz | ⟨ay', az, hay', haz, n2⟩
        · exact absurd (name_beq_trans hxy hyz) hxz
        · rw [hc x y hxy, hay', haz]
          exact ⟨true, _, rfl, n2⟩
        · rw [hax, ← hc y z hyz, hay]
          exact ⟨true, _, rfl, n1⟩
        · rw [hay] at hay'; cases hay'
          rw [hax, haz]
          refine ⟨true, _, rfl, ?_⟩
          exact Ordering.isLE_iff_ne_gt.1
            (Std.TransCmp.isLE_trans (cmp := (compare : Address → Address → Ordering))
              (Ordering.isLE_iff_ne_gt.2 n1) (Ordering.isLE_iff_ne_gt.2 n2))
      · exact ⟨true, .eq, rfl, by decide⟩
  | T + 2 =>
    refine PreOn.empty fun n ⟨_, h⟩ => ?_
    cases hn : c.mutCtx[n]? <;> simp only [refTag, hn] at h <;> omega

end Ix.CompileCert.Canon
