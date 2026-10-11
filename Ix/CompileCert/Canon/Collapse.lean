import Ix.CompileCert.Canon.Rename
import Ix.CompileCert.Canon.BlockComp

/-!
# M7 L1, collapse: the quotient block has the same classes

Def 4.3's collapse (for cliques: equal members). Let `F` be the classes of `xs`. The quotient
presentation keeps one member `r` of each class (`keep`) and redirects every reference to a member
of a class (and to its constructors) to the kept member of that class (and its constructors),
by a renaming `σ` that sends each member's names to its class representative's names, fixes the
external names, and respects `==`. `sortClasses_collapse`: the quotient's classes are the classes of
`F` restricted to the kept members, in the same order, so each is a singleton
(`sortClasses_collapse_single`).

The renaming is not injective (it identifies the members of a class), so reference comparisons
agree only up to strength: two references to distinct members of one class compare `⟨false, eq⟩`
in the block and `⟨true, eq⟩` in the quotient (`compareRef_col`); the round comparison reads only
the order (`constOrd_iff`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst MutCtx ConstructorVal)

/-! ## Members of one class have the same number of constructors -/

theorem constP_size_of_eq {c : CmpCtx} {x y : MutConst} {s : Bool}
    (h : constP c x y = .ok ⟨s, .eq⟩) : x.ctors.size = y.ctors.size := by
  cases x <;> cases y <;> simp only [constP] at h
  · rfl
  · simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, kindTag] at h
    exact absurd h.2 (by decide)
  · simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, kindTag] at h
    exact absurd h.2 (by decide)
  · simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, kindTag] at h
    exact absurd h.2 (by decide)
  · rename_i x y
    unfold indP at h
    obtain ⟨a, ha, (⟨hne, he⟩ | ⟨heq, -⟩)⟩ := lexIf_ok.1 h
    · subst he; exact absurd rfl hne
    · simp only [pure, Except.pure, Except.ok.injEq] at ha
      subst ha
      rw [indHdr_eq] at heq
      simp only [Ordering.then_eq_eq] at heq
      exact Nat.compare_eq_eq.1 heq.2.2.2
  · simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, kindTag] at h
    exact absurd h.2 (by decide)
  · simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, kindTag] at h
    exact absurd h.2 (by decide)
  · simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq, kindTag] at h
    exact absurd h.2 (by decide)
  · rfl

theorem constOrd_size_of_eq {r : Rules} {addr? : Name → Option Address} {ctx : MutCtx}
    {x y : MutConst} (h : constOrd r addr? ctx x y = .ok .eq) : x.ctors.size = y.ctors.size := by
  unfold constOrd at h
  cases ht : r.tieBreak with
  | inline => simp only [ht] at h; obtain ⟨s, hs⟩ := map_ord_ok.1 h; exact constP_size_of_eq hs
  | blind => simp only [ht] at h; obtain ⟨s, hs⟩ := map_ord_ok.1 h; exact constP_size_of_eq hs
  | byAddress =>
    simp only [ht] at h
    obtain ⟨b, hb, h⟩ := except_bind_ok.1 h
    by_cases hbe : (b != .eq) = true
    · simp only [hbe, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact absurd hbe (by decide)
    · simp only [hbe, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨s, hs⟩ := map_ord_ok.1 h; exact constP_size_of_eq hs

/-- In a consistent partition, members of one class have the same number of constructors. -/
theorem consistent_size {r : Rules} {addr? : Name → Option Address} {F : List (List MutConst)}
    (hFc : Consistent r addr? F) : ∀ D ∈ F, ∀ m ∈ D, ∀ m' ∈ D, m.ctors.size = m'.ctors.size := by
  intro D hD m hm m' hm'
  by_cases e : m = m'
  · rw [e]
  · exact constOrd_size_of_eq (hFc D hD m hm m' hm' e)

/-! ## The largest constructor count -/

theorem maxC_le {C : List MutConst} {n : Nat} (h : ∀ m ∈ C, m.ctors.size ≤ n) : maxC C ≤ n := by
  induction C with
  | nil => simp [maxC]
  | cons m C ih =>
    have e : maxC (m :: C) = max m.ctors.size (maxC C) := by
      unfold maxC
      simp only [List.foldl_cons, Nat.zero_max]
      rw [foldl_max]
      rfl
    rw [e]
    have := ih (fun m' hm' => h m' (List.mem_cons_of_mem _ hm'))
    have := h m (List.mem_cons_self ..)
    omega

theorem maxC_eq_of {C D : List MutConst} (h1 : ∀ m ∈ C, ∃ m' ∈ D, m.ctors.size = m'.ctors.size)
    (h2 : ∀ m' ∈ D, ∃ m ∈ C, m'.ctors.size = m.ctors.size) : maxC C = maxC D := by
  apply Nat.le_antisymm
  · apply maxC_le; intro m hm
    obtain ⟨m', hm', e⟩ := h1 m hm; rw [e]; exact maxC_ge hm'
  · apply maxC_le; intro m' hm'
    obtain ⟨m, hm, e⟩ := h2 m' hm'; rw [e]; exact maxC_ge hm

theorem offs_restrict {keep : MutConst → Bool} {φ : MutConst → MutConst} :
    ∀ (P : List (List MutConst)), (∀ C ∈ P, maxC (restrictC keep φ C) = maxC C) →
      ∀ (j : Nat), offs (restrictP keep φ P) j = offs P j := by
  intro P
  induction P with
  | nil => intro _ j; simp [offs, sumMaxC, restrictP]
  | cons C P ih =>
    intro h j
    cases j with
    | zero => rw [offs_zero, offs_zero]
    | succ j =>
      show offs (restrictC keep φ C :: restrictP keep φ P) (j + 1) = _
      rw [offs_cons_succ, offs_cons_succ, ih (fun D hD => h D (List.mem_cons_of_mem _ hD)) j,
        h C (List.mem_cons_self ..)]

/-! ## Distinct keys, `==` -/

theorem beq_trans' {a b c : Name} (h1 : (a == b) = true) (h2 : (b == c) = true) : (a == c) = true :=
  name_beq_trans h1 h2

theorem pairwise_nbeq_map {f : Name → Name} :
    ∀ {l : List Name}, l.Pairwise (fun a b => (a == b) = false) → (∀ k ∈ l, (f k == k) = true) →
      (l.map f).Pairwise (fun a b => (a == b) = false) := by
  intro l hl hf
  rw [List.pairwise_map]
  refine hl.imp_of_mem fun {a b} ha hb e => ?_
  cases h : (f a == f b)
  · rfl
  · have : (a == b) = true :=
      name_beq_trans (name_beq_symm (hf a ha)) (name_beq_trans h (hf b hb))
    rw [this] at e; cases e

/-! ## The quotient -/

section collapse
variable {r : Rules} {addr? : Name → Option Address} {xs : List MutConst} (hk : KeysDistinct xs)
  {F : List (List MutConst)} (hFp : Partition F xs)
  (hsz : ∀ D ∈ F, ∀ m ∈ D, ∀ m' ∈ D, m.ctors.size = m'.ctors.size)
  {keep : MutConst → Bool} {σ : Name → Name} {S : Name → Prop} {φ : MutConst → MutConst}
  (hkeep : ∀ D ∈ F, ∃ r ∈ D, keep r = true ∧ ∀ b ∈ D, keep b = true → b = r)
  (hmr : ∀ a ∈ xs, keep a = true → MRen σ S a (φ a))
  (hS : ∀ a ∈ xs, ∀ k ∈ keysOf a, S k)
  (hcongr : ∀ x y, S x → S y → (x == y) = true → (σ x == σ y) = true)
  (hext : ∀ x, S x → (∀ k ∈ xs.flatMap keysOf, (k == x) = false) → σ x = x)
  (hrep : ∀ D ∈ F, ∀ m ∈ D, ∀ r ∈ D, keep r = true → (σ m.name == r.name) = true ∧
    ∀ (k : Nat) (c c' : ConstructorVal), m.ctors[k]? = some c → r.ctors[k]? = some c' →
      (σ c.cnst.name == c'.cnst.name) = true)

include hFp in
theorem exists_class {m : MutConst} (hm : m ∈ xs) : ∃ D ∈ F, m ∈ D :=
  List.mem_flatten.1 (hFp.1.mem_iff.2 hm)

include hk in
/-- A class of `F` lies in one class of any partition `F` refines. -/
theorem in_same_class {P : List (List MutConst)} (hP : Partition P xs) (href : Refines F P)
    {D : List MutConst} (hD : D ∈ F) {m a : MutConst} (hm : m ∈ D) (ha : a ∈ D) {C : List MutConst}
    (hC : C ∈ P) (hmC : m ∈ C) : a ∈ C := by
  obtain ⟨C', hC', hmC', haC'⟩ := href D hD m hm a ha
  have hn : P.flatten.Nodup := hP.1.nodup_iff.2 hk.nodup
  rw [mem_unique_of_nodup hn hC' hC hmC' hmC] at haC'
  exact haC'

include hrep in
/-- A kept member's renamed keys are `==` to its keys. -/
theorem rep_keys_beq {D : List MutConst} (hD : D ∈ F) {r : MutConst} (hr : r ∈ D) (hkr : keep r = true) :
    ∀ k ∈ keysOf r, (σ k == k) = true := by
  intro k hk'
  unfold keysOf at hk'
  rcases List.mem_cons.1 hk' with rfl | hk'
  · exact (hrep D hD r hr r hr hkr).1
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hk'
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hci : r.ctors[i]? = some r.ctors.toList[i] := by
      rw [← Array.getElem?_toList]; exact List.getElem?_eq_getElem hi
    exact (hrep D hD r hr r hr hkr).2 i _ _ hci hci

include hk hFp hmr hrep in
/-- The quotient's keys are distinct. -/
theorem keysDistinct_col {l : List MutConst} (hl : l.Sublist xs) :
    KeysDistinct (restrictC keep φ l) := by
  unfold KeysDistinct restrictC
  have hsub : (l.filter keep).Sublist xs := List.filter_sublist.trans hl
  rw [keys_map_ren (xs := l.filter keep) (fun a ha => hmr a (hsub.subset ha) (List.mem_filter.1 ha).2)
    (l.filter keep) (fun a ha => ha)]
  apply pairwise_nbeq_map
  · exact (hk : (xs.flatMap keysOf).Pairwise _).sublist (sublist_flatMap _ hsub)
  · intro k hk'
    obtain ⟨a, ha, hka⟩ := List.mem_flatMap.1 hk'
    obtain ⟨D, hD, haD⟩ := exists_class hFp (hsub.subset ha)
    exact rep_keys_beq hrep hD haD (List.mem_filter.1 ha).2 k hka

include hk hFp hsz hkeep hmr hS hcongr hext hrep in
/-- **The context of the quotient** answers for `σ x` as the block's context for `x`, at every
partition that the classes refine. -/
theorem ctx_col {P : List (List MutConst)} (hP : Partition P xs) (href : Refines F P) {x : Name}
    (hx : S x) : (MutConst.ctx (restrictP keep φ P))[σ x]? = (MutConst.ctx P)[x]? := by
  have hkP : KeysDistinct P.flatten := hk.perm hP.1.symm
  have hinP : ∀ a ∈ P.flatten, a ∈ xs := fun a ha => hP.1.mem_iff.1 ha
  have hkQ : KeysDistinct (restrictP keep φ P).flatten := by
    rw [restrictP_flatten]
    exact (keysDistinct_col hk hFp hmr hrep (List.Sublist.refl xs)).perm (restrictC_perm hP.1).symm
  have repIn : ∀ C ∈ P, ∀ m ∈ C, ∃ D ∈ F, m ∈ D ∧ ∃ r ∈ D, keep r = true ∧ r ∈ C := by
    intro C hC m hm
    obtain ⟨D, hD, hmD⟩ := exists_class hFp (hinP m (List.mem_flatten.2 ⟨C, hC, hm⟩))
    obtain ⟨r, hrD, hkr, -⟩ := hkeep D hD
    exact ⟨D, hD, hmD, r, hrD, hkr, in_same_class hk hP href hD hmD hrD hC hm⟩
  have hmax : ∀ C ∈ P, maxC (restrictC keep φ C) = maxC C := by
    intro C hC
    apply maxC_eq_of
    · intro m' hm'
      obtain ⟨a, ha, hka, rfl⟩ := mem_restrictC.1 hm'
      exact ⟨a, ha, ctors_size_ren (hmr a (hinP a (List.mem_flatten.2 ⟨C, hC, ha⟩)) hka)⟩
    · intro m hm
      obtain ⟨D, hD, hmD, r, hrD, hkr, hrC⟩ := repIn C hC m hm
      refine ⟨φ r, mem_restrictC.2 ⟨r, hrC, hkr, rfl⟩, ?_⟩
      rw [ctors_size_ren (hmr r (hinP r (List.mem_flatten.2 ⟨C, hC, hrC⟩)) hkr)]
      exact hsz D hD m hmD r hrD
  cases hv : (MutConst.ctx P)[x]? with
  | some v =>
    obtain ⟨j, C, m, hC, hm, hxv⟩ := ctx_val hkP hv
    have hCP : C ∈ P := List.mem_of_getElem? hC
    have hmx : m ∈ xs := hinP m (List.mem_flatten.2 ⟨C, hCP, hm⟩)
    obtain ⟨D, hD, hmD, r, hrD, hkr, hrC⟩ := repIn C hCP m hm
    have hrx : r ∈ xs := hinP r (List.mem_flatten.2 ⟨C, hCP, hrC⟩)
    have hQ : (restrictP keep φ P)[j]? = some (restrictC keep φ C) := by
      unfold restrictP; rw [List.getElem?_map, hC]; rfl
    have hrQ : φ r ∈ restrictC keep φ C := mem_restrictC.2 ⟨r, hrC, hkr, rfl⟩
    have hmr' := hmr r hrx hkr
    rcases hxv with ⟨hxe, rfl⟩ | ⟨k, c, hc, hxe, rfl⟩
    · have hSm : S m.name := hS m hmx m.name (List.mem_cons_self ..)
      have e1 : (σ x == σ m.name) = true := hcongr x m.name hx hSm (name_beq_symm hxe)
      have e2 : (σ m.name == r.name) = true := (hrep D hD m hmD r hrD hkr).1
      have e3 : (r.name == σ r.name) = true := name_beq_symm (hrep D hD r hrD r hrD hkr).1
      have e : (σ x == (φ r).name) = true := by
        rw [name_ren hmr']; exact name_beq_trans e1 (name_beq_trans e2 e3)
      rw [mutCtx_getElem?_congr _ e]
      exact ctx_member hkQ hQ hrQ
    · have hkm : k < m.ctors.size := by
        rcases Nat.lt_or_ge k m.ctors.size with hh | hh
        · exact hh
        · rw [Array.getElem?_eq_none hh] at hc; cases hc
      have hk' : k < r.ctors.size := by rw [← hsz D hD m hmD r hrD]; exact hkm
      have hc' : r.ctors[k]? = some r.ctors[k] := Array.getElem?_eq_getElem hk'
      obtain ⟨c'', hc'', hname''⟩ := ctor_ren hmr' hc'
      have hcm : c.cnst.name ∈ keysOf m := by
        unfold keysOf
        refine List.mem_cons_of_mem _ (List.mem_map.2 ⟨c, ?_, rfl⟩)
        rw [← Array.getElem?_toList] at hc
        exact List.mem_of_getElem? hc
      have e1 : (σ x == σ c.cnst.name) = true := hcongr x _ hx (hS m hmx _ hcm) (name_beq_symm hxe)
      have e2 : (σ c.cnst.name == r.ctors[k].cnst.name) = true :=
        (hrep D hD m hmD r hrD hkr).2 k c _ hc hc'
      have e3 : (r.ctors[k].cnst.name == σ r.ctors[k].cnst.name) = true :=
        name_beq_symm ((hrep D hD r hrD r hrD hkr).2 k _ _ hc' hc')
      have e : (σ x == c''.cnst.name) = true := by
        rw [hname'']; exact name_beq_trans e1 (name_beq_trans e2 e3)
      rw [mutCtx_getElem?_congr _ e, ctx_ctor hkQ hQ hrQ hc'', restrictP_length, offs_restrict P hmax]
  | none =>
    have d := ctx_dom P x
    rw [hv] at d
    have notkey : ∀ k ∈ P.flatten.flatMap keysOf, (k == x) = false := by
      intro k hk'
      cases e : (k == x)
      · rfl
      · have : (P.flatten.flatMap keysOf).any (· == x) = true := List.any_eq_true.2 ⟨k, hk', e⟩
        rw [← d] at this; cases this
    have hfix : σ x = x :=
      hext x hx (fun k hk' => notkey k ((List.Perm.flatMap_right keysOf hP.1).mem_iff.2 hk'))
    rw [hfix]
    have dQ := ctx_dom (restrictP keep φ P) x
    cases hw : (MutConst.ctx (restrictP keep φ P))[x]? with
    | none => rfl
    | some w =>
      exfalso
      rw [hw] at dQ
      obtain ⟨k', hk', e⟩ := List.any_eq_true.1 dQ.symm
      rw [restrictP_flatten] at hk'
      obtain ⟨b, hb, hkb⟩ := List.mem_flatMap.1 hk'
      obtain ⟨a, ha, hka, rfl⟩ := mem_restrictC.1 hb
      have hax : a ∈ xs := hinP a ha
      rw [keysOf_ren (hmr a hax hka)] at hkb
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hkb
      obtain ⟨D, hD, haD⟩ := exists_class hFp hax
      have e' : (σ k == k) = true := rep_keys_beq hrep hD haD hka k hk
      have : (k == x) = true := name_beq_trans (name_beq_symm e') e
      rw [notkey k (List.mem_flatMap.2 ⟨a, ha, hk⟩)] at this
      cases this

include hk hFp hsz hkeep hmr hS hcongr hext hrep in
/-- **References in the quotient compare in the same order** (the strength can differ: two
members of one class become one name). -/
theorem compareRef_col {P : List (List MutConst)} (hP : Partition P xs) (href : Refines F P)
    (rr : Rules) (ad : Name → Option Address) (mode : ExtMode) {x y : Name} (hx : S x) (hy : S y) :
    OrdIff (compareRef (ctxOf rr ad mode (MutConst.ctx P)) x y)
      (compareRef (ctxOf rr ad mode (MutConst.ctx (restrictP keep φ P))) (σ x) (σ y)) := by
  have ex := ctx_col hk hFp hsz hkeep hmr hS hcongr hext hrep hP href hx
  have ey := ctx_col hk hFp hsz hkeep hmr hS hcongr hext hrep hP href hy
  have fix : ∀ z, S z → (MutConst.ctx P)[z]? = none → σ z = z := by
    intro z hz hn
    apply hext z hz
    intro k hk'
    have d := ctx_dom P z
    rw [hn] at d
    have hk'' : k ∈ P.flatten.flatMap keysOf :=
      (List.Perm.flatMap_right keysOf hP.1).mem_iff.2 hk'
    cases e : (k == z)
    · rfl
    · have : (P.flatten.flatMap keysOf).any (· == z) = true := List.any_eq_true.2 ⟨k, hk'', e⟩
      rw [← d] at this; cases this
  have lk : ∀ (u v : Name), (σ u == σ v) = true →
      (MutConst.ctx (restrictP keep φ P))[σ u]? = (MutConst.ctx (restrictP keep φ P))[σ v]? :=
    fun u v e => mutCtx_getElem?_congr _ e
  cases hb : (x == y)
  · cases hx' : (MutConst.ctx P)[x]? <;> cases hy' : (MutConst.ctx P)[y]?
    · have fx := fix x hx hx'
      have fy := fix y hy hy'
      rw [fx] at ex; rw [fy] at ey; rw [fx, fy]
      rw [compareRef_out_out _ hb hx' hy', compareRef_out_out _ hb (ex.trans hx') (ey.trans hy')]
      exact ordIff.refl _
    · have hb' : (σ x == σ y) = false := by
        cases e : (σ x == σ y)
        · rfl
        · have := lk x y e; rw [ex, ey, hx', hy'] at this; cases this
      rw [compareRef_out_in _ hb hx' hy', compareRef_out_in _ hb' (ex.trans hx') (ey.trans hy')]
      exact ordIff.refl _
    · have hb' : (σ x == σ y) = false := by
        cases e : (σ x == σ y)
        · rfl
        · have := lk x y e; rw [ex, ey, hx', hy'] at this; cases this
      rw [compareRef_in_out _ hb hx' hy', compareRef_in_out _ hb' (ex.trans hx') (ey.trans hy')]
      exact ordIff.refl _
    · rename_i nx ny
      rw [compareRef_in_in _ hb hx' hy']
      cases hb' : (σ x == σ y)
      · rw [compareRef_in_in _ hb' (ex.trans hx') (ey.trans hy')]
        exact ordIff.refl _
      · have := lk x y hb'
        rw [ex, ey, hx', hy'] at this
        simp only [Option.some.injEq] at this
        subst this
        rw [compareRef_beq _ hb', Nat.compare_eq_eq.2 rfl]
        intro o
        constructor
        · rintro ⟨s, h⟩; cases h; exact ⟨true, rfl⟩
        · rintro ⟨s, h⟩; cases h; exact ⟨false, rfl⟩
  · rw [compareRef_beq _ hb, compareRef_beq _ (hcongr x y hx hy hb)]
    exact ordIff.refl _

end collapse

theorem restrictC_single {keep : MutConst → Bool} {φ : MutConst → MutConst} :
    ∀ {D : List MutConst}, D.Nodup → ∀ {r : MutConst}, r ∈ D → keep r = true →
      (∀ b ∈ D, keep b = true → b = r) → restrictC keep φ D = [φ r]
  | [], _, _, hr, _, _ => by cases hr
  | a :: t, hn, r, hr, hkr, huniq => by
    unfold restrictC
    by_cases hka : keep a = true
    · have e : a = r := huniq a (List.mem_cons_self ..) hka
      subst e
      rw [List.filter_cons_of_pos hka]
      have : t.filter keep = [] := List.filter_eq_nil_iff.2 fun b hb hkb => by
        have := huniq b (List.mem_cons_of_mem _ hb) hkb
        subst this
        exact (List.nodup_cons.1 hn).1 hb
      rw [this]; rfl
    · rw [List.filter_cons_of_neg hka]
      have hrt : r ∈ t := by
        rcases List.mem_cons.1 hr with rfl | hrt
        · exact absurd hkr hka
        · exact hrt
      have := restrictC_single (keep := keep) (φ := φ) (List.nodup_cons.1 hn).2 hrt hkr
        (fun b hb hkb => huniq b (List.mem_cons_of_mem _ hb) hkb)
      unfold restrictC at this
      exact this

/-- **Collapse** (Def 4.3: collapse; for cliques: equal members). The quotient presentation, one
member kept per class with every reference to a class (and to its constructors) redirected to
the kept member, has the classes of the block restricted to the kept members, in the same order. -/
theorem sortClasses_collapse {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {xs ys : List MutConst}
    (hk : KeysDistinct xs) {F : List (List MutConst)} {stats : SortStats}
    (h : sortClasses rules addr? xs = .ok (F, stats))
    {keep : MutConst → Bool} {σ : Name → Name} {S : Name → Prop} {φ : MutConst → MutConst}
    (hkeep : ∀ D ∈ F, ∃ r ∈ D, keep r = true ∧ ∀ b ∈ D, keep b = true → b = r)
    (hmr : ∀ a ∈ xs, keep a = true → MRen σ S a (φ a))
    (hS : ∀ a ∈ xs, ∀ k ∈ keysOf a, S k)
    (hcongr : ∀ x y, S x → S y → (x == y) = true → (σ x == σ y) = true)
    (hext : ∀ x, S x → (∀ k ∈ xs.flatMap keysOf, (k == x) = false) → σ x = x)
    (hrep : ∀ D ∈ F, ∀ m ∈ D, ∀ r ∈ D, keep r = true → (σ m.name == r.name) = true ∧
      ∀ (k : Nat) (c c' : ConstructorVal), m.ctors[k]? = some c → r.ctors[k]? = some c' →
        (σ c.cnst.name == c'.cnst.name) = true)
    (hys : (restrictC keep φ xs).Perm ys) :
    ∃ G stats', sortClasses rules addr? ys = .ok (G, stats') ∧ SetEq (restrictP keep φ F) G := by
  have e₁ := sortClasses_eq hpf hA hk
  rw [h] at e₁
  have hF : sortClassesP rules addr? xs = .ok F := e₁.symm
  obtain ⟨hFp, hFc, -⟩ := sortClassesP_coarsest rules hA hk hF
  have hsz := consistent_size hFc
  have hky := keysDistinct_col hk hFp hmr hrep (List.Sublist.refl xs)
  obtain ⟨G, hG, e⟩ := sortClassesP_sim (keep := keep) (φ := φ) (xs := xs) (ys := ys) hA hA hk hky hys hF
    (fun D hD => by obtain ⟨r, hr, hkr, -⟩ := hkeep D hD; exact ⟨r, hr, hkr⟩)
    (fun P hP href a ha b hb hka hkb o => constOrd_iff (fun mode => constP_ren ordIff
      (ctxOf rules addr? mode (MutConst.ctx P))
      (ctxOf rules addr? mode (MutConst.ctx (restrictP keep φ P))) rfl
      (fun x y hx hy => compareRef_col hk hFp hsz hkeep hmr hS hcongr hext hrep hP href rules addr? mode hx hy)
      (hmr a ha hka) (hmr b hb hkb)) o)
  have e₂ := sortClasses_eq hpf hA (hky.perm hys)
  rw [hG] at e₂
  cases h₂ : sortClasses rules addr? ys with
  | error err => rw [h₂] at e₂; cases e₂
  | ok v =>
    rw [h₂] at e₂
    simp only [Except.map, Except.ok.injEq] at e₂
    refine ⟨v.1, v.2, rfl, ?_⟩
    rw [e₂]; exact e

theorem nodup_of_mem_flatten {F : List (List MutConst)} (hn : F.flatten.Nodup) :
    ∀ {D : List MutConst}, D ∈ F → D.Nodup := by
  induction F with
  | nil => intro D hD; cases hD
  | cons E F ih =>
    intro D hD
    rw [List.flatten_cons] at hn
    rcases List.mem_cons.1 hD with rfl | hD
    · exact (List.nodup_append.1 hn).1
    · exact ih (List.nodup_append.1 hn).2.1 hD

/-- **Collapse, the classes of the quotient are singletons**: the `i`-th is the kept member of the
block's `i`-th class. -/
theorem sortClasses_collapse_single {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {xs ys : List MutConst}
    (hk : KeysDistinct xs) {F : List (List MutConst)} {stats : SortStats}
    (h : sortClasses rules addr? xs = .ok (F, stats))
    {keep : MutConst → Bool} {σ : Name → Name} {S : Name → Prop} {φ : MutConst → MutConst}
    (hkeep : ∀ D ∈ F, ∃ r ∈ D, keep r = true ∧ ∀ b ∈ D, keep b = true → b = r)
    (hmr : ∀ a ∈ xs, keep a = true → MRen σ S a (φ a))
    (hS : ∀ a ∈ xs, ∀ k ∈ keysOf a, S k)
    (hcongr : ∀ x y, S x → S y → (x == y) = true → (σ x == σ y) = true)
    (hext : ∀ x, S x → (∀ k ∈ xs.flatMap keysOf, (k == x) = false) → σ x = x)
    (hrep : ∀ D ∈ F, ∀ m ∈ D, ∀ r ∈ D, keep r = true → (σ m.name == r.name) = true ∧
      ∀ (k : Nat) (c c' : ConstructorVal), m.ctors[k]? = some c → r.ctors[k]? = some c' →
        (σ c.cnst.name == c'.cnst.name) = true)
    (hys : (restrictC keep φ xs).Perm ys) :
    ∃ G stats', sortClasses rules addr? ys = .ok (G, stats') ∧ G.length = F.length ∧
      ∀ (i : Nat) (D : List MutConst), F[i]? = some D →
        ∃ r ∈ D, keep r = true ∧ G[i]? = some [φ r] := by
  obtain ⟨G, stats', hG, e⟩ :=
    sortClasses_collapse hpf hA hk h hkeep hmr hS hcongr hext hrep hys
  have e₁ := sortClasses_eq hpf hA hk
  rw [h] at e₁
  obtain ⟨hFp, -, -⟩ := sortClassesP_coarsest rules hA hk e₁.symm
  refine ⟨G, stats', hG, by rw [← e.length, restrictP_length], fun i D hD => ?_⟩
  have hDF : D ∈ F := List.mem_of_getElem? hD
  obtain ⟨r, hr, hkr, huniq⟩ := hkeep D hDF
  have hnD : D.Nodup := nodup_of_mem_flatten (hFp.1.nodup_iff.2 hk.nodup) hDF
  have hs := restrictC_single (φ := φ) hnD hr hkr huniq
  have hi : (restrictP keep φ F)[i]? = some (restrictC keep φ D) := by
    unfold restrictP; rw [List.getElem?_map, hD]; rfl
  obtain ⟨Gi, hGi, p⟩ := e.getElem? hi
  rw [hs] at p
  exact ⟨r, hr, hkr, by rw [hGi, List.perm_singleton.1 p.symm]⟩

end Ix.CompileCert.Canon
