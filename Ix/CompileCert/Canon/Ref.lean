import Ix.CompileCert.Canon.Level

/-! # Names, addresses, and the constant-reference leaf

CS-01, ported from the donor `a9cf3607` (`Canon/Ref`) and adapted to
CQ2.25's exact name tables.

`Ix.Name`'s `==` compares the stored hashes and `compare` (`Ix.nameCompare`)
is the byte order of the hashes; both are lawful on the hashes
(`name_beq_iff`, `nameCompare_eq_iff`, `Std.TransCmp Ix.nameCompare`). Since
CQ2.25 the class context `MutCtx` is a tree map under `nameCompareExact`
(the hash order, ties broken structurally by `Ix.Name.cmpRaw`), a lawful
total order whose `eq` is equality (`Std.TransCmp nameCompareExact`,
`Std.LawfulEqCmp nameCompareExact`), and the compiler's address map
(`Ix.CompileM.constAddrLookup`) reads `ExactName` hash maps, which answer
for equal names only.

The leaf `compareRef` (the map `κ` of the design: same name equal,
in-block names by class index weakly, in-block before external, external
names by compiled address) compares names structurally too since the
CQ2.25 follow-up (`nameEq`), so it is a total preorder on its ok-domain on
every name (`compareRef_total`): the donor's hypothesis `AddrCongr` (an
address map answering alike for `==` names) has no counterpart. -/

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

/-! ## Names under `==` and `nameCompare` (the stored hash) -/

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

theorem name_beq_of_eq {a b : Name} (h : a = b) : (a == b) = true := h ▸ name_beq_refl a

instance transCmp_nameCompare : Std.TransCmp Ix.nameCompare :=
  transCmp_comap (cmp := (compare : Address → Address → Ordering)) Name.getHash

theorem nameCompare_eq_iff {a b : Name} : Ix.nameCompare a b = .eq ↔ (a == b) = true := by
  rw [name_beq_iff]; exact address_compare_eq_iff

/-! ## `nameCompareExact`: a lawful total order whose `eq` is equality -/

def nameSize : Name → Nat
  | .anonymous _ => 1
  | .str p _ _ | .num p _ _ => nameSize p + 1

def nameTag : Name → Nat
  | .anonymous _ => 0
  | .str .. => 1
  | .num .. => 2

def nameParent : Name → Name
  | .str p _ _ | .num p _ _ => p
  | n => n

def nameStr : Name → String
  | .str _ s _ => s
  | _ => ""

def nameNum : Name → Nat
  | .num _ i _ => i
  | _ => 0

theorem cmpHash_eq (h h' : Address) : Name.cmpHash h h' = compare h h' := by
  unfold Name.cmpHash
  split
  · rename_i e; rw [addr_beq_iff.1 e]; exact (address_compare_eq_iff.2 rfl).symm
  · rfl

theorem cmpRaw_str (p p' : Name) (s s' : String) (h h' : Address) :
    Name.cmpRaw (.str p s h) (.str p' s' h') =
      (Name.cmpRaw p p').then ((compare s s').then (compare h h')) := by
  rw [Name.cmpRaw, cmpHash_eq]
  cases Name.cmpRaw p p' <;> simp only [Ordering.then]
  by_cases e : s = s'
  · subst e; simp
  · have ne : compare s s' ≠ .eq := fun c => e (Std.LawfulEqCmp.eq_of_compare c)
    simp only [beq_iff_eq, e, ↓reduceIte]

theorem cmpRaw_num (p p' : Name) (i i' : Nat) (h h' : Address) :
    Name.cmpRaw (.num p i h) (.num p' i' h') =
      (Name.cmpRaw p p').then ((compare i i').then (compare h h')) := by
  rw [Name.cmpRaw, cmpHash_eq]
  cases Name.cmpRaw p p' <;> simp only [Ordering.then]
  by_cases e : i = i'
  · subst e; simp
  · have ne : compare i i' ≠ .eq := fun c => e (Nat.compare_eq_eq.1 c)
    simp only [beq_iff_eq, e, ↓reduceIte]

/-- `Ix.Name.cmpRaw` as a strong comparison. -/
def rawC (a b : Name) : Except Unit SOrder := pure ⟨true, Name.cmpRaw a b⟩

theorem rawC_total : TotalPre rawC := by
  refine PreOn.ofSize nameSize fun n ih => ?_
  refine PreOn.ofTag nameTag ?_ ?_
  · intro a b _ _ h
    cases a <;> cases b <;> simp_all [rawC, nameTag, Name.cmpRaw, pure, Except.pure] <;> rfl
  intro T
  have hP : ∀ a, nameSize a < n + 1 ∧ nameTag a = T → T = 1 ∨ T = 2 →
      nameSize (nameParent a) < n := by
    intro a ⟨hs, ht⟩ hT
    cases a <;> simp_all [nameSize, nameTag, nameParent]
    omega
  match T with
  | 0 =>
    refine (PreOn.pureCmp (compare : Address → Address → Ordering) Name.getHash).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp_all [rawC, nameTag, Name.cmpRaw, Name.getHash, cmpHash_eq]
  | 1 =>
    refine ((ih.comap nameParent fun a h => hP a h (by omega)).cmpM
      ((PreOn.pureCmp (compare : String → String → Ordering) nameStr).cmpM
        (PreOn.pureCmp (compare : Address → Address → Ordering) Name.getHash))).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp only [nameTag] at ha hb <;> try omega
    simp only [rawC, nameParent, nameStr, Name.getHash, cmpM_pure, cmpRaw_str]
  | 2 =>
    refine ((ih.comap nameParent fun a h => hP a h (by omega)).cmpM
      ((PreOn.pureCmp (compare : Nat → Nat → Ordering) nameNum).cmpM
        (PreOn.pureCmp (compare : Address → Address → Ordering) Name.getHash))).congr ?_
    intro a b ⟨_, ha⟩ ⟨_, hb⟩
    cases a <;> cases b <;> simp only [nameTag] at ha hb <;> try omega
    simp only [rawC, nameParent, nameNum, Name.getHash, cmpM_pure, cmpRaw_num]
  | T + 3 =>
    refine PreOn.empty fun a ⟨_, ha⟩ => ?_
    cases a <;> simp [nameTag] at ha

instance transCmp_cmpRaw : Std.TransCmp Name.cmpRaw := transCmp_of_total _ rawC_total

theorem cmpRaw_eq_iff : ∀ {a b : Name}, Name.cmpRaw a b = .eq ↔ a = b
  | .anonymous h, .anonymous h' => by
    simp only [Name.cmpRaw, cmpHash_eq, address_compare_eq_iff, Name.anonymous.injEq]
  | .str p s h, .str p' s' h' => by
    rw [cmpRaw_str]
    simp only [Ordering.then_eq_eq, cmpRaw_eq_iff, address_compare_eq_iff, Name.str.injEq]
    constructor
    · rintro ⟨rfl, hs, rfl⟩; exact ⟨rfl, Std.LawfulEqCmp.eq_of_compare hs, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, Std.ReflCmp.compare_self (cmp := (compare : String → String → Ordering)), rfl⟩
  | .num p i h, .num p' i' h' => by
    rw [cmpRaw_num]
    simp only [Ordering.then_eq_eq, cmpRaw_eq_iff, address_compare_eq_iff, Name.num.injEq,
      Nat.compare_eq_eq]
  | .anonymous _, .str .. | .anonymous _, .num .. | .str .., .anonymous _ | .str .., .num ..
  | .num .., .anonymous _ | .num .., .str .. => by simp [Name.cmpRaw]

theorem nameCompareExact_eq (a b : Name) :
    Ix.nameCompareExact a b = (Ix.nameCompare a b).then (Name.cmpRaw a b) := by
  unfold Ix.nameCompareExact
  cases Ix.nameCompare a b <;> rfl

instance transCmp_nameCompareExact : Std.TransCmp Ix.nameCompareExact :=
  transCmp_of_total _ <|
    ((PreOn.pureCmp (ε := Unit) Ix.nameCompare id).cmpM (rawC_total.comap id fun _ _ => trivial)).congr
      fun a b _ _ => by simp only [id, rawC, cmpM_pure, nameCompareExact_eq]

theorem nameCompareExact_eq_iff {a b : Name} : Ix.nameCompareExact a b = .eq ↔ a = b := by
  rw [nameCompareExact_eq, Ordering.then_eq_eq, cmpRaw_eq_iff]
  constructor
  · exact fun h => h.2
  · rintro rfl; exact ⟨nameCompare_eq_iff.2 (name_beq_refl a), rfl⟩

instance lawfulEqCmp_nameCompareExact : Std.LawfulEqCmp Ix.nameCompareExact where
  compare_self := nameCompareExact_eq_iff.2 rfl
  eq_of_compare := nameCompareExact_eq_iff.1

/-! ## The reference leaf -/

theorem nameEq_true {x y : Name} (h : x = y) : Ix.Compile.ExactKey.nameEq x y = true :=
  (Ix.Compile.ExactKey.nameEq_iff x y).2 h

theorem nameEq_false {x y : Name} (h : x ≠ y) : Ix.Compile.ExactKey.nameEq x y = false :=
  Bool.eq_false_iff.2 fun e => h ((Ix.Compile.ExactKey.nameEq_iff x y).1 e)

theorem nameEq_comm (x y : Name) : Ix.Compile.ExactKey.nameEq x y = Ix.Compile.ExactKey.nameEq y x := by
  by_cases h : x = y
  · subst h; rfl
  · rw [nameEq_false h, nameEq_false (Ne.symm h)]

theorem compareRef_self (c : CmpCtx) (x : Name) : compareRef c x x = .ok ⟨true, .eq⟩ := by
  simp [compareRef, nameEq_true (rfl : x = x), pure, Except.pure]

theorem compareRef_in_in (c : CmpCtx) {x y : Name} (h : x ≠ y) {nx ny : Nat}
    (hx : c.mutCtx[x]? = some nx) (hy : c.mutCtx[y]? = some ny) :
    compareRef c x y = .ok ⟨false, compare nx ny⟩ := by
  simp only [compareRef, nameEq_false h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]
  rfl

theorem compareRef_in_out (c : CmpCtx) {x y : Name} (h : x ≠ y) {nx : Nat}
    (hx : c.mutCtx[x]? = some nx) (hy : c.mutCtx[y]? = none) :
    compareRef c x y = .ok ⟨true, .lt⟩ := by
  simp only [compareRef, nameEq_false h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]
  rfl

theorem compareRef_out_in (c : CmpCtx) {x y : Name} (h : x ≠ y) {ny : Nat}
    (hx : c.mutCtx[x]? = none) (hy : c.mutCtx[y]? = some ny) :
    compareRef c x y = .ok ⟨true, .gt⟩ := by
  simp only [compareRef, nameEq_false h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]
  rfl

theorem compareRef_out_out (c : CmpCtx) {x y : Name} (h : x ≠ y)
    (hx : c.mutCtx[x]? = none) (hy : c.mutCtx[y]? = none) :
    compareRef c x y = compareExternal c x y := by
  simp only [compareRef, nameEq_false h, Bool.false_eq_true, ↓reduceIte, Std.TreeMap.get?_eq_getElem?, hx, hy]

theorem compareExternal_swap (c : CmpCtx) (x y : Name) {s o}
    (h : compareExternal c x y = .ok ⟨s, o⟩) : compareExternal c y x = .ok ⟨s, o.swap⟩ := by
  unfold compareExternal at h ⊢
  cases hx : c.addr? x <;> cases hy : c.addr? y <;> simp_all [pure, Except.pure]
  obtain ⟨rfl, rfl⟩ := h
  exact Std.OrientedCmp.eq_swap (cmp := (compare : Address → Address → Ordering))

/-- The block-membership tag of a name: `0` in the block, `1` external. -/
def refTag (c : CmpCtx) (n : Name) : Nat :=
  match c.mutCtx[n]? with
  | some _ => 0
  | none => 1

theorem ne_of_refTag (c : CmpCtx) {x y : Name} (ht : refTag c x ≠ refTag c y) : x ≠ y :=
  fun e => ht (e ▸ rfl)

/-- **The reference leaf is a total preorder** at a fixed context. -/
theorem compareRef_total (c : CmpCtx) : TotalPre (compareRef c) := by
  -- in-block before external, strongly
  refine PreOn.ofTag (refTag c) ?_ ?_
  · intro x y _ _ ht
    have hne := ne_of_refTag c ht
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
          ((c.mutCtx[y]?).getD 0)⟩ ∧ s = Ix.Compile.ExactKey.nameEq x y := by
      intro x y hx hy
      cases hnx : c.mutCtx[x]? with
      | none => simp [refTag, hnx] at hx
      | some nx =>
        cases hny : c.mutCtx[y]? with
        | none => simp [refTag, hny] at hy
        | some ny =>
          by_cases h : x = y
          · subst h
            rw [hnx] at hny; cases hny
            refine ⟨true, ?_, (nameEq_true rfl).symm⟩
            rw [compareRef_self]; simp
          · exact ⟨false, by rw [compareRef_in_in c h hnx hny]; rfl, (nameEq_false h).symm⟩
    constructor
    · intro x y hx hy s o hxy
      obtain ⟨s1, e1, h1⟩ := key x y hx.2 hy.2
      obtain ⟨s2, e2, h2⟩ := key y x hy.2 hx.2
      rw [e1] at hxy
      simp only [Except.ok.injEq, SOrder.mk.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      rw [e2, h1, h2, nameEq_comm x y]
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
    -- two external names: equal names first, then by address
    have out : ∀ {x}, refTag c x = 1 → c.mutCtx[x]? = none := by
      intro x hx; cases h : c.mutCtx[x]? <;> simp_all [refTag]
    constructor
    · intro x y hx hy s o hxy
      by_cases h : x = y
      · subst h
        rw [compareRef_self] at hxy
        simp only [Except.ok.injEq, SOrder.mk.injEq] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        exact compareRef_self c x
      · rw [compareRef_out_out c h (out hx.2) (out hy.2)] at hxy
        rw [compareRef_out_out c (Ne.symm h) (out hy.2) (out hx.2)]
        exact compareExternal_swap c x y hxy
    · intro x y z hx hy hz h1 h2
      have ex := out hx.2; have ey := out hy.2; have ez := out hz.2
      by_cases hxz : x = z
      · subst hxz; exact ⟨true, .eq, compareRef_self c x, by decide⟩
      rw [compareRef_out_out c hxz ex ez]
      unfold compareExternal
      -- every step between different names has both addresses
      have addrOf : ∀ u v, c.mutCtx[u]? = none → c.mutCtx[v]? = none → Le (compareRef c u v) →
          u = v ∨ ∃ au av, c.addr? u = some au ∧ c.addr? v = some av ∧ compare au av ≠ .gt := by
        intro u v hu hv hle
        by_cases huv : u = v
        · exact .inl huv
        · right
          rw [compareRef_out_out c huv hu hv] at hle
          obtain ⟨s, o, he, hne⟩ := hle
          unfold compareExternal at he
          cases hau : c.addr? u <;> cases hav : c.addr? v <;> simp_all [pure, Except.pure]
      rcases addrOf x y ex ey h1 with rfl | ⟨ax, ay, hax, hay, n1⟩ <;>
        rcases addrOf _ z ey ez h2 with rfl | ⟨ay', az, hay', haz, n2⟩
      · exact absurd rfl hxz
      · rw [hay', haz]
        exact ⟨true, _, rfl, n2⟩
      · rw [hax, hay]
        exact ⟨true, _, rfl, n1⟩
      · rw [hay] at hay'; cases hay'
        rw [hax, haz]
        refine ⟨true, _, rfl, ?_⟩
        exact Ordering.isLE_iff_ne_gt.1
          (Std.TransCmp.isLE_trans (cmp := (compare : Address → Address → Ordering))
            (Ordering.isLE_iff_ne_gt.2 n1) (Ordering.isLE_iff_ne_gt.2 n2))
  | T + 2 =>
    refine PreOn.empty fun n ⟨_, h⟩ => ?_
    cases hn : c.mutCtx[n]? <;> simp only [refTag, hn] at h <;> omega

end Ix.CompileCert.Canon
