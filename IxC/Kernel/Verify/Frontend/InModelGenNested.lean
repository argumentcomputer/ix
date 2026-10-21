module

public import IxC.Kernel.Verify.Frontend.InModelNestedRename

@[expose] public section

/-!
# The nested rung under a renaming injective on a scope (parametricity, step 3)
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

/-- Close a goal relating two failures (a `throw`, or a `throw` followed by the rest). -/
macro "exrel_throw" : tactic =>
  `(tactic| first | exact ExRel.throw' | exact ExRel.throw_bind)

variable {md md' : Mode} {P : KeyScope md} {f : md.Id → md'.Id}

@[simp] theorem IndTypeRec.mapKeys_isReflexive (t : IndTypeRec md) :
    (t.mapKeys f).isReflexive = t.isReflexive := rfl

@[simp] theorem IndTypeRec.mapKeys_isRec (t : IndTypeRec md) : (t.mapKeys f).isRec = t.isRec := rfl

@[simp] theorem IndTypeRec.mapKeys_default : IndTypeRec.mapKeys f (default : IndTypeRec md) = default := rfl
@[simp] theorem IndRecRec.mapKeys_default : IndRecRec.mapKeys f (default : IndRecRec md) = default := rfl
@[simp] theorem Mem.mapKeys_default : Mem.mapKeys f (default : Mem md) = default := rfl
@[simp] theorem ACtor.mapKeys_default : ACtor.mapKeys f (default : ACtor md) = default := rfl

/-- `getD` through a map that keeps the default. -/
theorem getD_map_default {α β : Type} [Inhabited α] [Inhabited β] {g : α → β} (hg : g default = default)
    (l : List α) (i : Nat) : (l.map g).getD i default = g (l.getD i default) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hg]

theorem ListRel.mergeSort_map {α β : Type} {L : List α} {g : α → β} {G : α → Prop}
    {r : α → α → Bool} {s : β → β → Bool} (hl : ∀ a ∈ L, ∀ b ∈ L, r a b = s (g a) (g b))
    (hG : ∀ a ∈ L, G a) : ListRel (fun x x' => x' = g x ∧ G x) (L.mergeSort r) ((L.map g).mergeSort s) := by
  rw [← List.map_mergeSort hl]
  exact ListRel.of_map fun a ha => hG a ((List.mergeSort_perm L r).mem_iff.mp ha)

/-- **A `while` loop on both sides**, each step related and decreasing a measure of the
original state (`Lean.Loop.forIn` unfolds once per step, `Loop.forIn_eq_of_monadTail`). -/
theorem ExRel.loopForIn {ε ε' α β : Type} {R : α → β → Prop} (μ : α → Nat) {l l' : Lean.Loop}
    {f : Unit → α → Except ε (ForInStep α)} {f' : Unit → β → Except ε' (ForInStep β)}
    (hf : ∀ a b, R a b → ExRel (fun s s' => match s, s' with
        | .yield x, .yield y => R x y ∧ μ x < μ a
        | .done x, .done y => R x y
        | _, _ => False) (f () a) (f' () b)) :
    ∀ (n : Nat) (i : α) (i' : β), μ i < n → R i i' →
      ExRel R (Lean.Loop.forIn l i f) (Lean.Loop.forIn l' i' f')
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, i', h, hi => by
    rw [Lean.Loop.forIn_eq_of_monadTail, Lean.Loop.forIn_eq_of_monadTail]
    refine ExRel.bind (hf i i' hi) fun s s' hs => ?_
    cases s with
    | done x =>
      cases s' with
      | done y => exact ExRel.pure' hs
      | yield y => exact hs.elim
    | yield x =>
      cases s' with
      | done y => exact hs.elim
      | yield y => exact ExRel.loopForIn μ hf n x y (by have := hs.2; omega) hs.1

theorem length_filter_lt_of_mem {α : Type} {p : α → Bool} : ∀ {l : List α} {x : α}, x ∈ l → p x = false →
    (l.filter p).length < l.length
  | a :: as, x, hx, hpx => by
    rw [List.filter_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hpx]
      have := List.length_filter_le p as
      simp only [Bool.false_eq_true, if_false, List.length_cons]; omega
    · have := length_filter_lt_of_mem hx hpx
      cases p a <;> simp only [Bool.false_eq_true, if_false, if_true, List.length_cons] <;> omega

theorem keyList_map_beq (hf : InjOn f P) {l1 l2 : List (Key md)} (h1 : ∀ k ∈ l1, k.Good P)
    (h2 : ∀ k ∈ l2, k.Good P) : (l1.map (Key.map f) == l2.map (Key.map f)) = (l1 == l2) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a as ih =>
    cases l2 with
    | nil => simp at h
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [Key.map_inj hf (h1 a List.mem_cons_self) (h2 b List.mem_cons_self) h.1,
        ih (fun k hk => h1 k (List.mem_cons_of_mem _ hk)) (fun k hk => h2 k (List.mem_cons_of_mem _ hk)) h.2]

/-! ## Renamed good terms

The generated terms are built from the family, the members and the
constructors by the same code on both sides; `RG e e'` (`e'` is the
renaming of a good `e`) descends through that code one builder at a time
(`rg`). -/

/-- `e'` is the renaming of a good `e`. -/
def RG (P : KeyScope md) (f : md.Id → md'.Id) (e : Expr md) (e' : Expr md') : Prop :=
  e' = e.mapKeys f ∧ e.Good P

/-- `l'` is the renaming of a list of good terms. -/
def RGL (P : KeyScope md) (f : md.Id → md'.Id) (l : List (Expr md)) (l' : List (Expr md')) : Prop :=
  l' = l.map (Expr.mapKeys f) ∧ Expr.GoodList P l

/-- An optional term and its renaming. -/
def ORG (P : KeyScope md) (f : md.Id → md'.Id) (o : Option (Expr md)) (o' : Option (Expr md')) : Prop :=
  o' = o.map (Expr.mapKeys f) ∧ ∀ e, o = some e → e.Good P


theorem mkEq_good (hP : P.All) {ℓ : Level} {α a b : Expr md} (hα : α.Good P) (ha : a.Good P)
    (hb : b.Good P) : (mkEq ℓ α a b).Good P :=
  Expr.good_mkAppN_iff.2 ⟨hP _, fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl <;> assumption⟩

theorem mkRefl_good (hP : P.All) {ℓ : Level} {α a : Expr md} (hα : α.Good P) (ha : a.Good P) :
    (mkRefl ℓ α a).Good P :=
  Expr.good_mkAppN_iff.2 ⟨hP _, fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption⟩

theorem mkEqRec_good (hP : P.All) {ℓm ℓα : Level} {α a mo rf b h : Expr md} (hα : α.Good P)
    (ha : a.Good P) (hmo : mo.Good P) (hrf : rf.Good P) (hb : b.Good P) (hh : h.Good P) :
    (mkEqRec ℓm ℓα α a mo rf b h).Good P :=
  Expr.good_mkAppN_iff.2 ⟨hP _, fun x hx => by
    simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption⟩

@[simp] theorem Mem.mapKeys_pins_length (mem : Mem md) : (mem.mapKeys f).pins.length = mem.pins.length :=
  List.length_map ..

namespace RG

theorem eq_of {e : Expr md} {e' : Expr md'} (h : RG P f e e') : e' = e.mapKeys f := h.1
theorem of_good {e : Expr md} (h : e.Good P) : RG P f e (e.mapKeys f) := ⟨rfl, h⟩
theorem bvar (n : Nat) : RG P f (.bvar n : Expr md) (.bvar n) := ⟨rfl, trivial⟩
theorem sort (u : Level) : RG P f (.sort u : Expr md) (.sort u) := ⟨rfl, trivial⟩
theorem const {k : Key md} {k' : Key md'} (hk : k' = k.map f) (hg : k.Good P) {ls ls' : List Level}
    (hls : ls' = ls) : RG P f (.const k ls) (.const k' ls') := by
  subst hk hls; exact ⟨rfl, hg⟩
theorem cP {k : Key md} {k' : Key md'} (hk : k' = k.map f) (hg : k.Good P) (lps : List LevelParam) :
    RG P f (constP k lps) (constP k' lps) := const hk hg rfl
theorem app {a b : Expr md} {a' b' : Expr md'} (ha : RG P f a a') (hb : RG P f b b') :
    RG P f (.app a b) (.app a' b') := by
  obtain ⟨rfl, ha⟩ := ha; obtain ⟨rfl, hb⟩ := hb; exact ⟨rfl, ha, hb⟩
theorem lam {a b : Expr md} {a' b' : Expr md'} (ha : RG P f a a') (hb : RG P f b b') (m : BinderMeta) :
    RG P f (.lam a b m) (.lam a' b' m) := by
  obtain ⟨rfl, ha⟩ := ha; obtain ⟨rfl, hb⟩ := hb; exact ⟨rfl, ha, hb⟩
theorem pi {a b : Expr md} {a' b' : Expr md'} (ha : RG P f a a') (hb : RG P f b b') (m : BinderMeta) :
    RG P f (.forallE a b m) (.forallE a' b' m) := by
  obtain ⟨rfl, ha⟩ := ha; obtain ⟨rfl, hb⟩ := hb; exact ⟨rfl, ha, hb⟩
theorem lift {e : Expr md} {e' : Expr md'} (h : RG P f e e') (n c : Nat) :
    RG P f (e.liftLooseBVars n c) (e'.liftLooseBVars n c) := by
  obtain ⟨rfl, h⟩ := h; exact ⟨(Expr.mapKeys_liftLooseBVars n c e).symm, Expr.Good.liftLooseBVars h n c⟩
theorem appN {g : Expr md} {g' : Expr md'} {as : List (Expr md)} {as' : List (Expr md')}
    (hg : RG P f g g') (has : RGL P f as as') : RG P f (Expr.mkAppN g as) (Expr.mkAppN g' as') := by
  obtain ⟨rfl, hg⟩ := hg; obtain ⟨rfl, has⟩ := has
  exact ⟨(Expr.mapKeys_mkAppN g as).symm, Expr.good_mkAppN_iff.2 ⟨hg, has⟩⟩
theorem pis {bs : List (Expr md)} {bs' : List (Expr md')} {b : Expr md} {b' : Expr md'}
    (hbs : RGL P f bs bs') (hb : RG P f b b') : RG P f (mkPis bs b) (mkPis bs' b') := by
  obtain ⟨rfl, hbs⟩ := hbs; obtain ⟨rfl, hb⟩ := hb
  exact ⟨(mkPis_mapKeys bs b).symm, Expr.good_mkPis hbs hb⟩
theorem lams {bs : List (Expr md)} {bs' : List (Expr md')} {b : Expr md} {b' : Expr md'}
    (hbs : RGL P f bs bs') (hb : RG P f b b') : RG P f (mkLams bs b) (mkLams bs' b') := by
  obtain ⟨rfl, hbs⟩ := hbs; obtain ⟨rfl, hb⟩ := hb
  exact ⟨(mkLams_mapKeys bs b).symm, Expr.good_mkLams hbs hb⟩
theorem eq (hP : P.All) {ℓ : Level} {α a b : Expr md} {α' a' b' : Expr md'} (hα : RG P f α α')
    (ha : RG P f a a') (hb : RG P f b b') : RG P f (mkEq ℓ α a b) (mkEq ℓ α' a' b') := by
  obtain ⟨rfl, hα⟩ := hα; obtain ⟨rfl, ha⟩ := ha; obtain ⟨rfl, hb⟩ := hb
  exact ⟨(mkEq_mapKeys ℓ α a b).symm, mkEq_good hP hα ha hb⟩
theorem refl (hP : P.All) {ℓ : Level} {α a : Expr md} {α' a' : Expr md'} (hα : RG P f α α')
    (ha : RG P f a a') : RG P f (mkRefl ℓ α a) (mkRefl ℓ α' a') := by
  obtain ⟨rfl, hα⟩ := hα; obtain ⟨rfl, ha⟩ := ha
  exact ⟨(mkRefl_mapKeys ℓ α a).symm, mkRefl_good hP hα ha⟩
theorem eqRec (hP : P.All) {ℓm ℓα : Level} {α a mo rf b h : Expr md} {α' a' mo' rf' b' h' : Expr md'}
    (hα : RG P f α α') (ha : RG P f a a') (hmo : RG P f mo mo') (hrf : RG P f rf rf') (hb : RG P f b b')
    (hh : RG P f h h') : RG P f (mkEqRec ℓm ℓα α a mo rf b h) (mkEqRec ℓm ℓα α' a' mo' rf' b' h') := by
  obtain ⟨rfl, hα⟩ := hα; obtain ⟨rfl, ha⟩ := ha; obtain ⟨rfl, hmo⟩ := hmo
  obtain ⟨rfl, hrf⟩ := hrf; obtain ⟨rfl, hb⟩ := hb; obtain ⟨rfl, hh⟩ := hh
  exact ⟨(mkEqRec_mapKeys ℓm ℓα α a mo rf b h).symm, mkEqRec_good hP hα ha hmo hrf hb hh⟩
theorem spec (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) (o : Nat) {e : Expr md}
    {e' : Expr md'} (h : RG P f e e') : RG P f (specAll fam o e) (specAll (fam.mapKeys f) o e') := by
  obtain ⟨rfl, h⟩ := h; exact ⟨specAll_mapKeys hf hfam o h, specAll_good hfam o h⟩
theorem aux {fam : Family md} (hfam : fam.Good P) (tag o : Nat) {idx : List (Expr md)}
    {idx' : List (Expr md')} (h : RGL P f idx idx') :
    RG P f (auxAt fam tag o idx) (auxAt (fam.mapKeys f) tag o idx') := by
  obtain ⟨rfl, h⟩ := h; exact ⟨auxAt_mapKeys fam tag o idx, auxAt_good hfam h⟩
theorem carr (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) {mem : Mem md} (hmem : mem.Good P)
    (o : Nat) {idx : List (Expr md)} {idx' : List (Expr md')} (h : RGL P f idx idx') (model : Bool) :
    RG P f (carrierAt fam mem o idx model) (carrierAt (fam.mapKeys f) (mem.mapKeys f) o idx' model) := by
  obtain ⟨rfl, h⟩ := h; exact ⟨carrierAt_mapKeys hf hfam hmem o idx model, carrierAt_good hmem h model⟩
theorem carrD (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) {mems : List (Mem md)}
    (hmD : ∀ t, (mems.getD t default).Good P) (t o : Nat) {idx : List (Expr md)} {idx' : List (Expr md')}
    (h : RGL P f idx idx') (model : Bool) :
    RG P f (carrierAt fam (mems.getD t default) o idx model)
      (carrierAt (fam.mapKeys f) ((mems.getD t default).mapKeys f) o idx' model) :=
  carr hf hfam (hmD t) o h model
theorem rn (hf : InjOn f P) {bn : List (Key md)} (hbn : ∀ k ∈ bn, k.Good P) {e : Expr md}
    {e' : Expr md'} (h : RG P f e e') :
    RG P f (e.renameConsts fun x => bif bn.contains x then modelName x else x)
      (e'.renameConsts fun x => if (bn.map (Key.map f)).contains x = true then modelName x else x) := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨rn_map hf hbn h, rn_good h⟩
theorem cond {c : Bool} {a b : Expr md} {a' b' : Expr md'} (ha : c = true → RG P f a a')
    (hb : c = false → RG P f b b') : RG P f (bif c then a else b) (bif c then a' else b') := by
  cases c
  · exact hb rfl
  · exact ha rfl
theorem ite {c : Prop} [Decidable c] {a b : Expr md} {a' b' : Expr md'} (ha : c → RG P f a a')
    (hb : ¬ c → RG P f b b') : RG P f (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha h
  · rw [if_neg h, if_neg h]; exact hb h
theorem idxB {mem : Mem md} (hmem : mem.Good P) (j : Nat) :
    RG P f (mem.idxBs.getD j default) ((mem.mapKeys f).idxBs.getD j default) :=
  ⟨getD_mapKeys_default _ _, Expr.GoodList.getD_default hmem.2.2 j⟩
theorem idxBD {mems : List (Mem md)} (hmD : ∀ t, (mems.getD t default).Good P) (t j : Nat) :
    RG P f ((mems.getD t default).idxBs.getD j default) (((mems.getD t default).mapKeys f).idxBs.getD j default) :=
  idxB (hmD t) j
theorem dom {c : ACtor md} (hc : c.Good P) (i : Nat) :
    RG P f (c.doms.getD i default) ((c.mapKeys f).doms.getD i default) :=
  ⟨getD_mapKeys_default _ _, Expr.GoodList.getD_default hc.2.1 i⟩

theorem idxBm {mems : List (Mem md)} {mem : Mem md} (hx : mem ∈ mems) (hmG : ∀ m ∈ mems, m.Good P)
    (j : Nat) : RG P f (mem.idxBs.getD j default) ((mem.mapKeys f).idxBs.getD j default) :=
  idxB (hmG mem hx) j
theorem domm {cs : List (ACtor md)} {c : ACtor md} (hx : c ∈ cs) (hcG : ∀ c ∈ cs, c.Good P) (i : Nat) :
    RG P f (c.doms.getD i default) ((c.mapKeys f).doms.getD i default) :=
  dom (hcG c hx) i
end RG

namespace RGL

theorem nil : RGL P f ([] : List (Expr md)) [] := ⟨rfl, fun _ h => nomatch h⟩
theorem cons {e : Expr md} {e' : Expr md'} {l : List (Expr md)} {l' : List (Expr md')}
    (h : RG P f e e') (hl : RGL P f l l') : RGL P f (e :: l) (e' :: l') := by
  obtain ⟨rfl, h⟩ := h; obtain ⟨rfl, hl⟩ := hl
  exact ⟨rfl, Expr.goodList_cons.2 ⟨h, hl⟩⟩
theorem append {l1 l2 : List (Expr md)} {l1' l2' : List (Expr md')} (h1 : RGL P f l1 l1')
    (h2 : RGL P f l2 l2') : RGL P f (l1 ++ l2) (l1' ++ l2') := by
  obtain ⟨rfl, h1⟩ := h1; obtain ⟨rfl, h2⟩ := h2
  exact ⟨(List.map_append ..).symm, Expr.goodList_append.2 ⟨h1, h2⟩⟩
theorem vars (o n : Nat) : RGL P f (varsAt o n : List (Expr md)) (varsAt o n) :=
  ⟨(varsAt_mapKeys o n).symm, Expr.goodList_varsAt' o n⟩
theorem of_good {l : List (Expr md)} (h : Expr.GoodList P l) : RGL P f l (l.map (Expr.mapKeys f)) :=
  ⟨rfl, h⟩
theorem map {α : Type} {l l' : List α} {g : α → Expr md} {g' : α → Expr md'} (hl : l' = l)
    (h : ∀ x ∈ l, RG P f (g x) (g' x)) : RGL P f (l.map g) (l'.map g') := by
  subst hl
  refine ⟨?_, fun e he => ?_⟩
  · rw [List.map_map]; exact List.map_congr_left fun x hx => (h x hx).1
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he; exact (h x hx).2
/-- A map over a renamed list, each element good. -/
theorem mapG {α β : Type} {G : α → Prop} {l : List α} {k : α → β} {g : α → Expr md}
    {g' : β → Expr md'} (hG : ∀ x ∈ l, G x) (h : ∀ x, G x → RG P f (g x) (g' (k x))) :
    RGL P f (l.map g) ((l.map k).map g') := by
  rw [List.map_map]; exact map rfl fun x hx => h x (hG x hx)
/-- A map over a list of terms and its renaming. -/
theorem mapR {l : List (Expr md)} {l' : List (Expr md')} {g : Expr md → Expr md} {g' : Expr md' → Expr md'}
    (hl : RGL P f l l') (h : ∀ x x', RG P f x x' → RG P f (g x) (g' x')) :
    RGL P f (l.map g) (l'.map g') := by
  obtain ⟨rfl, hl⟩ := hl
  rw [List.map_map]; exact map rfl fun x hx => h x _ ⟨rfl, hl x hx⟩
theorem filterMap {α : Type} {l l' : List α} {g : α → Option (Expr md)} {g' : α → Option (Expr md')}
    (hl : l' = l) (h : ∀ x ∈ l, ORG P f (g x) (g' x)) : RGL P f (l.filterMap g) (l'.filterMap g') := by
  rw [hl]; clear hl
  induction l with
  | nil => exact nil
  | cons x xs ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨h1, h2⟩ := h x List.mem_cons_self
    rw [List.filterMap_cons, List.filterMap_cons, h1]
    cases hgx : g x with
    | none => exact ih'
    | some e => exact cons ⟨rfl, h2 e hgx⟩ ih'
theorem take {l : List (Expr md)} {l' : List (Expr md')} (h : RGL P f l l') (n : Nat) :
    RGL P f (l.take n) (l'.take n) := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨by simp only [List.map_take], fun e he => h e (List.mem_of_mem_take he)⟩
theorem args {e : Expr md} {e' : Expr md'} (h : RG P f e e') : RGL P f e.getAppArgs e'.getAppArgs := by
  obtain ⟨rfl, h⟩ := h; exact ⟨Expr.getAppArgs_mapKeys e, Expr.Good.getAppArgs h⟩
theorem lifts {l : List (Expr md)} {l' : List (Expr md')} (h : RGL P f l l') (n c : Nat) :
    RGL P f (l.map (·.liftLooseBVars n c)) (l'.map (·.liftLooseBVars n c)) := by
  obtain ⟨rfl, h⟩ := h
  refine ⟨by simp [List.map_map, Function.comp_def, Expr.mapKeys_liftLooseBVars], fun e he => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he; exact Expr.Good.liftLooseBVars (h x hx) n c
theorem liftAll {l : List (Expr md)} {l' : List (Expr md')} (h : RGL P f l l') (n : Nat) :
    RGL P f (liftAll n l) (liftAll n l') := lifts h n 0
theorem set {l : List (Expr md)} {l' : List (Expr md')} (h : RGL P f l l') (i : Nat) {e : Expr md}
    {e' : Expr md'} (he : RG P f e e') : RGL P f (l.set i e) (l'.set i e') := by
  obtain ⟨rfl, h⟩ := h; obtain ⟨rfl, he⟩ := he
  refine ⟨by simp only [List.map_set], fun x hx => ?_⟩
  rcases List.mem_or_eq_of_mem_set hx with hx | rfl
  · exact h x hx
  · exact he
theorem idx {c : ACtor md} (hc : c.Good P) : RGL P f c.idx (c.mapKeys f).idx := ⟨rfl, hc.2.2⟩
theorem pins {mem : Mem md} (hmem : mem.Good P) : RGL P f mem.pins (mem.mapKeys f).pins := ⟨rfl, hmem.2.1⟩
theorem idxBs {mem : Mem md} (hmem : mem.Good P) : RGL P f mem.idxBs (mem.mapKeys f).idxBs :=
  ⟨rfl, hmem.2.2⟩
theorem doms {c : ACtor md} (hc : c.Good P) : RGL P f c.doms (c.mapKeys f).doms := ⟨rfl, hc.2.1⟩
theorem pinsD {mems : List (Mem md)} (hmD : ∀ t, (mems.getD t default).Good P) (t : Nat) :
    RGL P f (mems.getD t default).pins ((mems.getD t default).mapKeys f).pins := pins (hmD t)
/-- A carrier occurrence's index arguments (`matchCarrier`). -/
theorem mc (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) (i : Nat) {d : Expr md}
    {d' : Expr md'} (h : RG P f d d') :
    RGL P f (((matchCarrier fam i d).map (·.2)).getD [])
      (((matchCarrier (fam.mapKeys f) i d').map (·.2)).getD []) := by
  obtain ⟨rfl, h⟩ := h
  rw [matchCarrier_mapKeys hf hfam i h]
  cases hm : matchCarrier fam i d with
  | none => exact nil
  | some p =>
    obtain ⟨t, idx⟩ := p
    exact ⟨rfl, fun y hy => Expr.Good.getAppArgs h y (matchCarrier_args hm y hy)⟩
/-- A field's index arguments off its domain (`fieldIdx`). -/
theorem fieldIdx (hf : InjOn f P) {fam : Family md} (hfam : fam.Good P) (i o' : Nat) {d : Expr md}
    {d' : Expr md'} (h : RG P f d d') :
    RGL P f ((((matchCarrier fam i d).map (·.2)).getD []).map (·.liftLooseBVars o' 0))
      ((((matchCarrier (fam.mapKeys f) i d').map (·.2)).getD []).map (·.liftLooseBVars o' 0)) :=
  lifts (mc hf hfam i h) o' 0

end RGL

namespace ORG
theorem none : ORG P f (none : Option (Expr md)) none := ⟨rfl, fun _ h => nomatch h⟩
theorem some {e : Expr md} {e' : Expr md'} (h : RG P f e e') : ORG P f (some e) (some e') := by
  obtain ⟨rfl, h⟩ := h; exact ⟨rfl, fun _ he => Option.some.inj he ▸ h⟩
end ORG

/-- The same `bif` on both sides, any relation. -/
theorem rel_cond {α β : Type} {R : α → β → Prop} {c : Bool} {a b : α} {a' b' : β}
    (ha : c = true → R a a') (hb : c = false → R b b') : R (bif c then a else b) (bif c then a' else b') := by
  cases c
  · exact hb rfl
  · exact ha rfl

/-- The same `if` on both sides, any relation. -/
theorem rel_ite {α β : Type} {R : α → β → Prop} {c : Prop} [Decidable c] {a b : α} {a' b' : β}
    (ha : c → R a a') (hb : ¬ c → R b b') : R (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha h
  · rw [if_neg h, if_neg h]; exact hb h

/-- A congruence chain's moved positions and their renaming. -/
def MRel (P : KeyScope md) (f : md.Id → md'.Id) (mv : List (Nat × Expr md × Expr md × Level))
    (mv' : List (Nat × Expr md' × Expr md' × Level)) : Prop :=
  mv' = movedMap f mv ∧ ∀ x ∈ mv, x.2.1.Good P ∧ x.2.2.1.Good P

/-- An optional moved position and its renaming. -/
def OMRel (P : KeyScope md) (f : md.Id → md'.Id) (o : Option (Nat × Expr md × Expr md × Level))
    (o' : Option (Nat × Expr md' × Expr md' × Level)) : Prop :=
  o' = o.map (fun x => (x.1, x.2.1.mapKeys f, x.2.2.1.mapKeys f, x.2.2.2)) ∧
    ∀ x, o = some x → x.2.1.Good P ∧ x.2.2.1.Good P

theorem OMRel.none : OMRel P f none none := ⟨rfl, fun _ h => nomatch h⟩
theorem OMRel.some (i : Nat) {e ty : Expr md} {e' ty' : Expr md'} (he : RG P f e e') (hty : RG P f ty ty')
    (ℓ : Level) : OMRel P f (some (i, e, ty, ℓ)) (some (i, e', ty', ℓ)) := by
  obtain ⟨rfl, he⟩ := he; obtain ⟨rfl, hty⟩ := hty
  exact ⟨rfl, fun x hx => by cases hx; exact ⟨he, hty⟩⟩

theorem MRel.filterMap {α : Type} {l l' : List α} {g : α → Option (Nat × Expr md × Expr md × Level)}
    {g' : α → Option (Nat × Expr md' × Expr md' × Level)} (hl : l' = l)
    (h : ∀ x ∈ l, OMRel P f (g x) (g' x)) : MRel P f (l.filterMap g) (l'.filterMap g') := by
  rw [hl]; clear hl
  induction l with
  | nil => exact ⟨rfl, fun _ h => nomatch h⟩
  | cons x xs ih =>
    obtain ⟨ih1, ih2⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨h1, h2⟩ := h x List.mem_cons_self
    rw [List.filterMap_cons, List.filterMap_cons, h1]
    cases hgx : g x with
    | none => exact ⟨ih1, ih2⟩
    | some y =>
      refine ⟨by simp [ih1, movedMap], fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h2 _ hgx
      · exact ih2 z hz

/-- **A congruence chain** and its renaming (by its recursion). -/
theorem RG.congrGo (hP : P.All) {ℓα : Level} {α : Expr md} {α' : Expr md'} (hα : RG P f α α')
    {F : Nat → List (Expr md) → Expr md} {F' : Nat → List (Expr md') → Expr md'}
    (hF : ∀ o l l', RGL P f l l' → RG P f (F o l) (F' o l'))
    {ls rs : List (Expr md)} (hlsG : Expr.GoodList P ls) (hrsG : Expr.GoodList P rs)
    {moved : List (Nat × Expr md × Expr md × Level)} (hmv : ∀ x ∈ moved, x.2.1.Good P ∧ x.2.2.1.Good P) :
    ∀ n k, moved.length - k = n →
      RG P f (congrChain.go ℓα α F ls rs moved k)
        (congrChain.go ℓα α' F' (ls.map (Expr.mapKeys f)) (rs.map (Expr.mapKeys f)) (movedMap f moved) k) := by
  have hls : RGL P f ls (ls.map (Expr.mapKeys f)) := ⟨rfl, hlsG⟩
  have hgetD : ∀ (l : List (Expr md)), Expr.GoodList P l → ∀ i,
      RG P f (l.getD i default) ((l.map (Expr.mapKeys f)).getD i default) :=
    fun l hl i => ⟨getD_mapKeys_default l i, Expr.GoodList.getD_default hl i⟩
  intro n
  induction n with
  | zero =>
    intro k hk
    have hnone : moved[k]? = none := List.getElem?_eq_none (by omega)
    have hnone' : (movedMap f moved)[k]? = none := by simp [movedMap, hnone]
    unfold congrChain.go
    split
    · split
      · exact RG.refl hP hα (hF 0 _ _ hls)
      · rename_i h; rw [hnone'] at h; exact nomatch h
    · rename_i h; rw [hnone] at h; exact nomatch h
  | succ n ih =>
    intro k hk
    unfold congrChain.go
    split
    · rename_i h
      have h' : (movedMap f moved)[k]? = none := by simp [movedMap, h]
      split
      · exact RG.refl hP hα (hF 0 _ _ hls)
      · rename_i h2; rw [h'] at h2; exact nomatch h2
    · rename_i pos e ty ℓ h
      have hh : (movedMap f moved)[k]? = some (pos, e.mapKeys f, ty.mapKeys f, ℓ) := by
        simp [movedMap, h]
      split
      · rename_i h2; rw [hh] at h2; exact nomatch h2
      · rename_i pos' e' ty' ℓ' h2
        rw [hh] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h2
        have hmem := hmv _ (List.mem_of_getElem? h)
        have hk1 : k < moved.length := (List.getElem?_eq_some_iff.mp h).1
        have hty : RG P f ty (ty.mapKeys f) := RG.of_good hmem.2
        have hmid : RGL P f ((List.range ls.length).map fun i =>
              if ((moved.drop k).any fun x => x.1 == i) = true then rs.getD i default else ls.getD i default)
            ((List.range (ls.map (Expr.mapKeys f)).length).map fun i =>
              if (((movedMap f moved).drop k).any fun x => x.1 == i) = true then
                (rs.map (Expr.mapKeys f)).getD i default else (ls.map (Expr.mapKeys f)).getD i default) := by
          refine RGL.map (by rw [List.length_map]) fun i _ => ?_
          rw [movedMap_drop_any]
          exact rel_ite (fun _ => hgetD rs hrsG i) (fun _ => hgetD ls hlsG i)
        exact RG.eqRec hP hty (hgetD ls hlsG pos)
          (RG.lam hty (RG.lam (RG.eq hP (RG.lift hty 1 0) (RG.lift (hgetD ls hlsG pos) 1 0) (RG.bvar 0))
            (RG.eq hP (RG.lift hα 2 0) (hF 2 _ _ (RGL.liftAll hls 2))
              (hF 2 _ _ (RGL.set (RGL.liftAll hmid 2) pos (RG.bvar 1)))) bm) bm)
          (ih (k + 1) (by omega)) (hgetD rs hrsG pos) (RG.of_good hmem.1)

theorem RG.congr (hP : P.All) {ℓα : Level} {α : Expr md} {α' : Expr md'} (hα : RG P f α α')
    {F : Nat → List (Expr md) → Expr md} {F' : Nat → List (Expr md') → Expr md'}
    (hF : ∀ o l l', RGL P f l l' → RG P f (F o l) (F' o l'))
    {ls rs : List (Expr md)} {ls' rs' : List (Expr md')} (hls : RGL P f ls ls') (hrs : RGL P f rs rs')
    {moved : List (Nat × Expr md × Expr md × Level)} {moved' : List (Nat × Expr md' × Expr md' × Level)}
    (hmv : MRel P f moved moved') :
    RG P f (congrChain ℓα α F ls rs moved) (congrChain ℓα α' F' ls' rs' moved') := by
  obtain ⟨rfl, hlsG⟩ := hls; obtain ⟨rfl, hrsG⟩ := hrs; obtain ⟨rfl, hmvG⟩ := hmv
  exact RG.congrGo hP hα hF hlsG hrsG hmvG _ 0 rfl

/-- **The adapted minor's transport chain** (`_impl.rec`'s real-member minors) and
its renaming, by its recursion over the packed positions. -/
theorem RG.go (hP : P.All) {u ℓ : Level} {c : ACtor md} {c' : ACtor md'} (hcn : c'.nF = c.nF)
    {fv : Nat → Expr md} {fv' : Nat → Expr md'} (hfv : ∀ i, RG P f (fv i) (fv' i)) {packed : List Nat}
    {ma : Nat → List (Expr md) → Expr md} {ma' : Nat → List (Expr md') → Expr md'}
    (hma : ∀ o l l', RGL P f l l' → RG P f (ma o l) (ma' o l'))
    {pu : Nat → Expr md × Expr md × Expr md} {pu' : Nat → Expr md' × Expr md' × Expr md'}
    (hpu : ∀ i, RG P f (pu i).1 (pu' i).1 ∧ RG P f (pu i).2.1 (pu' i).2.1 ∧ RG P f (pu i).2.2 (pu' i).2.2) :
    ∀ (ks done : List Nat) {acc : Expr md} {acc' : Expr md'}, RG P f acc acc' →
      RG P f (genNested.go u ℓ c fv packed ma pu ks done acc)
        (genNested.go u ℓ c' fv' packed ma' pu' ks done acc')
  | [], _, _, _, h => by simp only [genNested.go]; exact h
  | k :: rest, done, acc, acc', h => by
    simp only [genNested.go]
    obtain ⟨h1, h2, h3⟩ := hpu k
    revert h1 h2 h3
    rcases pu k with ⟨a, b, d⟩
    rcases pu' k with ⟨a', b', d'⟩
    intro h1 h2 h3
    refine RG.go hP hcn hfv hma hpu rest _ (RG.eqRec hP h3 h1 ?_ h (hfv k) h2)
    refine RG.lam h3 (RG.lam (RG.eq hP (RG.lift h3 1 0) (RG.lift h1 1 0) (RG.bvar 0)) (hma 2 _ _ ?_) bm) bm
    refine RGL.map (by rw [hcn]) fun i _ => ?_
    exact rel_ite (fun _ => RG.bvar 1) fun _ => rel_ite (fun _ => RG.lift (hfv i) 2 0) fun _ =>
      rel_ite (fun _ => RG.lift (hpu i).1 2 0) fun _ => RG.lift (hfv i) 2 0

/-- Optional terms per position, and their renaming. -/
def FORG (P : KeyScope md) (f : md.Id → md'.Id) (zs : Nat → Option (Expr md))
    (zs' : Nat → Option (Expr md')) : Prop :=
  ∀ i, ORG P f (zs i) (zs' i)

theorem FORG.none : FORG P f (fun _ => (none : Option (Expr md))) (fun _ => none) := fun _ => ORG.none

theorem ORG.lift {o : Option (Expr md)} {o' : Option (Expr md')} (h : ORG P f o o') (n c : Nat) :
    ORG P f (o.map (·.liftLooseBVars n c)) (o'.map (·.liftLooseBVars n c)) := by
  obtain ⟨rfl, h⟩ := h
  cases o with
  | none => exact ORG.none
  | some e => exact ORG.some (RG.lift ⟨rfl, h e rfl⟩ n c)

theorem RG.getDz {zs : Nat → Option (Expr md)} {zs' : Nat → Option (Expr md')} (h : FORG P f zs zs')
    (k : Nat) {d : Expr md} {d' : Expr md'} (hd : RG P f d d') : RG P f ((zs k).getD d) ((zs' k).getD d') := by
  obtain ⟨h1, h2⟩ := h k
  rw [h1]
  cases hz : zs k with
  | none => exact hd
  | some e => exact ⟨rfl, h2 e hz⟩

theorem goodRecD {recs : List (IndRecRec md)} (hrD : ∀ k, (recs.getD k default).cv.name.Good P) (k : Nat) :
    (modelName (recs.getD k default).cv.name).Good P := hrD k

theorem RG.constRecD {recs : List (IndRecRec md)} (hrD : ∀ k, (recs.getD k default).cv.name.Good P)
    (k : Nat) (ls : List Level) :
    RG P f (.const (modelName (recs.getD k default).cv.name) ls)
      (.const (modelName (Key.map f (recs.getD k default).cv.name)) ls) :=
  RG.const rfl (goodRecD hrD k) rfl

theorem MRel.map {α : Type} {l : List α} {g : α → Nat × Expr md × Expr md × Level}
    {g' : α → Nat × Expr md' × Expr md' × Level} (h : ∀ x ∈ l, OMRel P f (some (g x)) (some (g' x))) :
    MRel P f (l.map g) (l.map g') := by
  rw [← List.filterMap_eq_map, ← List.filterMap_eq_map]
  exact MRel.filterMap rfl h

/-- **The iota statement's transport chain** (a real member's `goT`) and its renaming. -/
theorem RG.goT (hP : P.All) {u ℓ : Level} {M n : Nat} {mems : List (Mem md)} {mems' : List (Mem md')}
    (hmj : ∀ t, (mems'.getD t default).j = (mems.getD t default).j)
    {fam : Family md} (hfam : fam.Good P)
    {rn : Expr md → Expr md} {rn' : Expr md' → Expr md'} (hrn : ∀ e e', RG P f e e' → RG P f (rn e) (rn' e'))
    {fI : ACtor md → Nat → Nat → List (Expr md)} {fI' : ACtor md' → Nat → Nat → List (Expr md')}
    {c : ACtor md} {c' : ACtor md'} (hck : c'.kinds = c.kinds)
    (hfI : ∀ k o, RGL P f (fI c k o) (fI' c' k o))
    {cpn : Nat → Key md} {cpn' : Nat → Key md'} (hcpn : ∀ j, cpn' j = (cpn j).map f)
    (hcpnG : ∀ j, (cpn j).Good P)
    {ai : Key md → Nat → List (Expr md) → List (Expr md) → Expr md}
    {ai' : Key md' → Nat → List (Expr md') → List (Expr md') → Expr md'}
    (hai : ∀ nm o l l' a a', nm.Good P → RGL P f l l' → RGL P f a a' → RG P f (ai nm o l a) (ai' (nm.map f) o l' a'))
    {nF oP : Nat} {packed : List Nat} {uOf : Nat → Nat → Expr md} {uOf' : Nat → Nat → Expr md'}
    (hu : ∀ o i, RG P f (uOf o i) (uOf' o i)) {o' : Nat} {zOf hOf : Nat → Expr md}
    {zOf' hOf' : Nat → Expr md'} (hz : ∀ i, RG P f (zOf i) (zOf' i)) (hh : ∀ i, RG P f (hOf i) (hOf' i))
    {pk : Nat → Nat → Expr md → Expr md} {pk' : Nat → Nat → Expr md' → Expr md'}
    (hpk : ∀ o i e e', RG P f e e' → RG P f (pk o i e) (pk' o i e'))
    {ma : Nat → List (Expr md) → Expr md} {ma' : Nat → List (Expr md') → Expr md'}
    (hma : ∀ o l l', RGL P f l l' → RG P f (ma o l) (ma' o l')) :
    ∀ (ks done : List Nat) {acc : Expr md} {acc' : Expr md'}, RG P f acc acc' →
      RG P f (genNested.goT u M n mems fam ℓ rn fI cpn ai c nF oP packed uOf o' zOf hOf pk ma ks done acc)
        (genNested.goT u M n mems' (fam.mapKeys f) ℓ rn' fI' cpn' ai' c' nF oP packed uOf' o' zOf' hOf' pk'
          ma' ks done acc')
  | [], _, _, _, h => by simp only [genNested.goT]; exact h
  | k :: rest, done, acc, acc', h => by
    simp only [genNested.goT]
    have hidx : RGL P f (liftAll o' (((fI c k (nF - k)).map rn).map (·.liftLooseBVars (M + n) nF)))
        (liftAll o' (((fI' c' k (nF - k)).map rn').map (·.liftLooseBVars (M + n) nF))) :=
      RGL.liftAll (RGL.lifts (RGL.mapR (hfI k _) hrn) _ _) o'
    have haux := RG.aux hfam ((c.kinds.getD k none).getD 0) (oP + o') hidx
    rw [hck, hmj, hcpn]
    refine RG.goT hP hmj hfam hrn hck hfI hcpn hcpnG hai hu hz hh hpk hma rest _
      (RG.eqRec hP haux (hpk 0 k _ _ (hu o' k)) ?_ h (hpk 0 k _ _ (hz k))
        (hai _ _ _ _ _ _ (hcpnG _) hidx (RGL.cons (hu o' k) (RGL.cons (hz k) (RGL.cons (hh k) RGL.nil)))))
    refine RG.lam haux (RG.lam (RG.eq hP (RG.lift haux 1 0) (hpk 1 k _ _ (RG.lift (hu o' k) 1 0))
      (RG.bvar 0)) (hma 2 _ _ ?_) bm) bm
    refine RGL.map rfl fun i _ => ?_
    exact rel_ite (fun _ => RG.bvar 1) fun _ =>
      rel_ite (fun _ => rel_ite (fun _ => hpk _ _ _ _ (RG.lift (hz i) _ _))
        fun _ => hpk _ _ _ _ (RG.lift (hu o' i) _ _)) fun _ => RG.lift (RG.bvar _) _ _

/-- **The iota proof's nested generalisations** and their renaming. -/
theorem RG.nest (hP : P.All) {u ℓ : Level} {nF : Nat} {uOf eOf cOf : Nat → Nat → Expr md}
    {uOf' eOf' cOf' : Nat → Nat → Expr md'} (hu : ∀ o i, RG P f (uOf o i) (uOf' o i))
    (he : ∀ o i, RG P f (eOf o i) (eOf' o i)) (hc : ∀ o i, RG P f (cOf o i) (cOf' o i))
    {st : Nat → (Nat → Option (Expr md)) → (Nat → Option (Expr md)) → Expr md × Expr md × Expr md}
    {st' : Nat → (Nat → Option (Expr md')) → (Nat → Option (Expr md')) → Expr md' × Expr md' × Expr md'}
    (hst : ∀ o zs zs' hs hs', FORG P f zs zs' → FORG P f hs hs' →
      RG P f (st o zs hs).1 (st' o zs' hs').1 ∧ RG P f (st o zs hs).2.1 (st' o zs' hs').2.1 ∧
        RG P f (st o zs hs).2.2 (st' o zs' hs').2.2) :
    ∀ (ks : List Nat) (o' : Nat) {zs hs : Nat → Option (Expr md)} {zs' hs' : Nat → Option (Expr md')},
      FORG P f zs zs' → FORG P f hs hs' →
      RG P f (genNested.nest u ℓ nF uOf eOf cOf st ks o' zs hs)
        (genNested.nest u ℓ nF uOf' eOf' cOf' st' ks o' zs' hs')
  | [], o', zs, hs, zs', hs', hz, hh => by
    simp only [genNested.nest]
    obtain ⟨h1, h2, -⟩ := hst o' zs zs' hs hs' hz hh
    exact RG.refl hP h1 h2
  | k :: rest, o', zs, hs, zs', hs', hz, hh => by
    simp only [genNested.nest]
    obtain ⟨h1, h2, h3⟩ := hst (o' + 2)
      (fun i => if (i == k) = true then some (Expr.bvar 1) else (zs i).map (·.liftLooseBVars 2 0))
      (fun i => if (i == k) = true then some (Expr.bvar 1) else (zs' i).map (·.liftLooseBVars 2 0))
      (fun i => if (i == k) = true then some (Expr.bvar 0) else (hs i).map (·.liftLooseBVars 2 0))
      (fun i => if (i == k) = true then some (Expr.bvar 0) else (hs' i).map (·.liftLooseBVars 2 0))
      (fun i => rel_ite (fun _ => ORG.some (RG.bvar 1)) (fun _ => ORG.lift (hz i) 2 0))
      (fun i => rel_ite (fun _ => ORG.some (RG.bvar 0)) (fun _ => ORG.lift (hh i) 2 0))
    exact RG.eqRec hP (hc o' k) (hu o' k)
      (RG.lam (hc o' k) (RG.lam (RG.eq hP (RG.lift (hc o' k) 1 0) (RG.lift (hu o' k) 1 0) (RG.bvar 0))
        (RG.eq hP h1 h2 h3) bm) bm)
      (RG.nest hP hu he hc hst rest o' (fun i => rel_ite (fun _ => ORG.some (hu o' k)) (fun _ => hz i))
        (fun i => rel_ite (fun _ => ORG.some (RG.refl hP (hc o' k) (hu o' k))) (fun _ => hh i)))
      (RG.lift (RG.bvar _) o' 0) (he o' k)

/-- A container group's constructors, in the container family's order, renamed. -/
theorem gctors_map (cs : List (ACtor md)) (tags : List Nat) :
    List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) (cs.map (ACtor.mapKeys f))) [] tags =
      (List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) cs) [] tags).map
        (ACtor.mapKeys f) := by
  suffices ∀ acc : List (ACtor md),
      List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) (cs.map (ACtor.mapKeys f)))
          (acc.map (ACtor.mapKeys f)) tags =
        (List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) cs) acc tags).map
          (ACtor.mapKeys f) from this []
  induction tags with
  | nil => intro acc; rfl
  | cons t ts ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [← ih, List.map_append, List.filter_map]
    rfl

theorem mem_gctors {cs : List (ACtor md)} {tags : List Nat} {c : ACtor md}
    (h : c ∈ List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) cs) [] tags) : c ∈ cs := by
  suffices ∀ acc : List (ACtor md),
      c ∈ List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) cs) acc tags → c ∈ acc ∨ c ∈ cs from
    (this [] h).resolve_left (fun h => nomatch h)
  clear h
  induction tags with
  | nil => intro acc h; exact Or.inl h
  | cons t ts ih =>
    intro acc h
    rcases ih _ h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_filter.mp h).1
    · exact Or.inr h

/-- **Descend through the generated code**: one builder per step, both
sides at once; what it cannot take apart (a `match`, a list over the
renamed members) is left as a goal. -/
macro "rg" : tactic => `(tactic| repeat' (first
  | (with_reducible exact RG.bvar _)
  | (with_reducible exact RG.sort _)
  | (with_reducible exact RGL.vars _ _)
  | (with_reducible exact RGL.nil)
  | (with_reducible exact RGL.of_good ‹_›)
  | (with_reducible exact RG.of_good ‹_›)
  | (with_reducible exact RG.idxB ‹_› _)
  | (with_reducible exact RG.idxBD ‹_› _ _)
  | (with_reducible exact RG.dom ‹_› _)
  | (with_reducible exact RG.idxBm ‹_› ‹_› _)
  | (with_reducible exact RG.domm ‹_› ‹_› _)
  | (with_reducible exact RGL.idx ‹_›)
  | (with_reducible exact RGL.pins ‹_›)
  | (with_reducible exact RGL.pinsD ‹_› _)
  | (with_reducible exact RGL.idxBs ‹_›)
  | (with_reducible exact RGL.doms ‹_›)
  | (with_reducible refine RG.appN ?_ ?_)
  | (with_reducible refine RG.pis ?_ ?_)
  | (with_reducible refine RG.lams ?_ ?_)
  | (with_reducible refine RG.lift ?_ _ _)
  | (with_reducible exact RG.constRecD ‹_› _ _)
  | (with_reducible refine RG.cP ?_ ?_ _)
  | (with_reducible refine RG.const ?_ ?_ ?_)
  | (with_reducible refine RG.spec ‹_› ‹_› _ ?_)
  | (with_reducible refine RG.aux ‹_› _ _ ?_)
  | (with_reducible refine RG.carr ‹_› ‹_› ‹_› _ ?_ _)
  | (with_reducible refine RG.carrD ‹_› ‹_› ‹_› _ _ ?_ _)
  | (with_reducible refine RG.rn ‹_› ‹_› ?_)
  | (with_reducible refine RG.eq ‹_› ?_ ?_ ?_)
  | (with_reducible refine RG.refl ‹_› ?_ ?_)
  | (with_reducible refine RG.eqRec ‹_› ?_ ?_ ?_ ?_ ?_ ?_)
  | (with_reducible refine RGL.fieldIdx ‹_› ‹_› _ _ ?_)
  | (with_reducible refine RGL.mc ‹_› ‹_› _ ?_)
  | (with_reducible refine RGL.cons ?_ ?_)
  | (with_reducible refine RGL.append ?_ ?_)
  | (with_reducible refine RGL.take ?_ _)
  | (with_reducible refine RGL.args ?_)
  | (with_reducible refine RGL.liftAll ?_ _)
  | (with_reducible refine RGL.lifts ?_ _ _)
  | (with_reducible refine RGL.set ?_ _ ?_)
  | (with_reducible refine RGL.mapG ‹_› ?_; intro _ _)
  | (with_reducible refine RGL.mapR ?_ ?_; rotate_left; intro _ _ _)
  | (with_reducible refine RGL.map ?_ ?_; rotate_left; intro _ _)
  | (with_reducible refine RGL.filterMap ?_ ?_; rotate_left; intro _ _)
  | (with_reducible refine rel_cond ?_ ?_ <;> intro _)
  | (with_reducible refine rel_ite ?_ ?_ <;> intro _)
  | (with_reducible refine RG.congr ‹_› ?_ ?_ ?_ ?_ ?_; rotate_left; intro _ _ _ _)
  | (with_reducible refine MRel.filterMap ?_ ?_; rotate_left; intro _ _)
  | (with_reducible exact OMRel.none)
  | (with_reducible refine OMRel.some _ ?_ ?_ _)
  | (with_reducible refine RG.go ‹_› ?_ ?_ ?_ ?_ _ _ ?_)
  | (with_reducible refine RG.goT ‹_› ?_ ‹_› ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ _ ?_)
  | (with_reducible refine RG.nest ‹_› ?_ ?_ ?_ ?_ _ _ ?_ ?_)
  | (with_reducible exact FORG.none)
  | (with_reducible refine RG.getDz ‹_› _ ?_)
  | (with_reducible refine MRel.map ?_; intro _ _)
  | intro _
  | (with_reducible refine ⟨?_, ?_⟩)
  | (with_reducible refine RG.app ?_ ?_)
  | (with_reducible refine RG.lam ?_ ?_ _)
  | (with_reducible refine RG.pi ?_ ?_ _)
  | (with_reducible exact ORG.none)
  | (with_reducible refine ORG.some ?_)
  | rfl
  | assumption
  | exact And.left ‹_›
  | (with_reducible exact goodRecD ‹_› _)
  | exact ‹KeyScope.All _› _
  | (simp only [Mem.mapKeys_tag, Mem.mapKeys_real?, Mem.mapKeys_j, Mem.mapKeys_nIdx, Mem.mapKeys_lv,
      Mem.mapKeys_pins_length, ACtor.mapKeys_mem, ACtor.mapKeys_kinds, ACtor.mapKeys_nF,
      ACtor.mapKeys_clv, ACtor.mapKeys_J, ACtor.mapKeys_jIn, ACtor.mapKeys_cname, Group.mapKeys_tags,
      Group.mapKeys_lv, Group.mapKeys_nPI, Group.mapKeys_large, getD_map_default Mem.mapKeys_default,
      getD_map_default IndRecRec.mapKeys_default, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_name,
      piBinders_mapBinders', mapBinders_getD])
  | (split <;> (rename_i h; try simp only [h]))))

/-- Prove an emitted type `need`ed through `replacePiBody`. -/
theorem ExRel.need_rpb (s s' : String) (k : Nat) {ty b : Expr md} {b' : Expr md'} (hb : RG P f b b') :
    ExRel (fun (a : Expr md) (a' : Expr md') => a' = a.mapKeys f ∧ True) (InModel.need s (Expr.replacePiBody k ty b))
      (InModel.need s' (Expr.replacePiBody k (ty.mapKeys f) b')) := by
  rw [hb.1, Expr.replacePiBody_mapKeys]; exact ExRel.need s s' fun _ _ => trivial

/-- A model value `need`ed through `pisToLams`, renamed and good. -/
theorem ExRel.need_pisRG (s s' : String) (k : Nat) {ty body : Expr md} {ty' body' : Expr md'}
    (ht : RG P f ty ty') (hb : RG P f body body') :
    ExRel (RG P f) (InModel.need s (Expr.pisToLams k ty body))
      (InModel.need s' (Expr.pisToLams k ty' body')) := by
  obtain ⟨rfl, ht⟩ := ht; obtain ⟨rfl, hb⟩ := hb
  rw [Expr.pisToLams_mapKeys]
  cases h : Expr.pisToLams k ty body with
  | none => exact ExRel.throw'
  | some a => exact ExRel.pure' ⟨rfl, Expr.pisToLams_good ht hb h⟩

/-- The state of the model-definition emission: the declarations and the heights. -/
def PS (P : KeyScope md) (f : md.Id → md'.Id) (s : Array (Declaration md) × List (Key md × Nat))
    (s' : Array (Declaration md') × List (Key md' × Nat)) : Prop :=
  s'.1 = s.1.map (Declaration.mapKeys f) ∧ s'.2 = keyMap f s.2 ∧ ∀ x ∈ s.2, x.1.Good P

/-- **One model definition pushed** on both sides (its hint through the heights). -/
theorem PS.push (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'} (hctx : CtxAgree f P ctx ctx')
    {s : Array (Declaration md) × List (Key md × Nat)} {s' : Array (Declaration md') × List (Key md' × Nat)}
    (hs : PS P f s s') {nm : Key md} {nm' : Key md'} (hnm : nm' = nm.map f) (hnmG : nm.Good P)
    (l : List LevelParam) {ty : Expr md} {ty' : Expr md'} (hty : ty' = ty.mapKeys f) {v : Expr md}
    {v' : Expr md'} (hv : RG P f v v') :
    PS P f
      (s.1.push (.defnDecl ⟨nm, l, ty⟩ v (hintFor (fun x => match List.find? (fun y => y.1 == x) s.2 with
          | some (_, h) => h
          | none => ctx.heights x) v)),
        (nm, hintHeight (hintFor (fun x => match List.find? (fun y => y.1 == x) s.2 with
          | some (_, h) => h
          | none => ctx.heights x) v)) :: s.2)
      (s'.1.push (.defnDecl ⟨nm', l, ty'⟩ v' (hintFor (fun x => match List.find? (fun y => y.1 == x) s'.2 with
          | some (_, h) => h
          | none => ctx'.heights x) v')),
        (nm', hintHeight (hintFor (fun x => match List.find? (fun y => y.1 == x) s'.2 with
          | some (_, h) => h
          | none => ctx'.heights x) v')) :: s'.2) := by
  obtain ⟨out, hs⟩ := s
  obtain ⟨out', hs'⟩ := s'
  obtain ⟨h1, h2, hsG⟩ := hs
  simp only at h1 h2 hsG ⊢
  subst h1 h2 hnm hty
  obtain ⟨rfl, hvG⟩ := hv
  refine ⟨?_, ?_, ?_⟩
  · simp only [Array.map_push, Declaration.mapKeys]
    exact congrArg (fun h => (Array.map (Declaration.mapKeys f) out).push
      (Declaration.defnDecl _ (Expr.mapKeys f v) h)) (hint_eq hf hctx hsG hvG)
  · simp only [keyMap_cons]
    exact congrArg (fun h => (Key.map f nm, hintHeight h) :: keyMap f hs) (hint_eq hf hctx hsG hvG)
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hnmG
    · exact hsG x hx

/-- A theorem pushed on both sides. -/
theorem PS.pushThm {s : Array (Declaration md) × List (Key md × Nat)}
    {s' : Array (Declaration md') × List (Key md' × Nat)} (hs : PS P f s s') {nm : Key md} {nm' : Key md'}
    (hnm : nm' = nm.map f) (l : List LevelParam) {ty v : Expr md} {ty' v' : Expr md'}
    (hty : ty' = ty.mapKeys f) (hv : v' = v.mapKeys f) :
    PS P f (s.1.push (.thmDecl ⟨nm, l, ty⟩ v), s.2) (s'.1.push (.thmDecl ⟨nm', l, ty'⟩ v'), s'.2) := by
  obtain ⟨h1, h2, hsG⟩ := hs
  subst hnm hty hv
  exact ⟨by rw [h1, Array.map_push]; rfl, h2, hsG⟩

/-- The projection-artifact loop's state: the emission state and the stop flag. -/
def PS3 (P : KeyScope md) (f : md.Id → md'.Id) (s : Array (Declaration md) × List (Key md × Nat) × Bool)
    (s' : Array (Declaration md') × List (Key md' × Nat) × Bool) : Prop :=
  PS P f (s.1, s.2.1) (s'.1, s'.2.1) ∧ s'.2.2 = s.2.2

theorem PS3.of {a : Array (Declaration md)} {b : List (Key md × Nat)} {a' : Array (Declaration md')}
    {b' : List (Key md' × Nat)} {c : Bool} (h : PS P f (a, b) (a', b')) : PS3 P f (a, b, c) (a', b', c) :=
  ⟨h, rfl⟩

/-- `pisToLams` at renamed good arguments. -/
theorem pisToLams_RG {k : Nat} {ty b : Expr md} {ty' b' : Expr md'} (ht : RG P f ty ty')
    (hb : RG P f b b') : Expr.pisToLams k ty' b' = (Expr.pisToLams k ty b).map (Expr.mapKeys f) := by
  obtain ⟨rfl, -⟩ := ht; obtain ⟨rfl, -⟩ := hb
  exact Expr.pisToLams_mapKeys k ty b

/-- A theorem pushed on a renamed array. -/
theorem push_thm_map {o : Array (Declaration md)} {nm : Key md} {nm' : Key md'} (hnm : nm' = nm.map f)
    (l : List LevelParam) {ty v : Expr md} {ty' v' : Expr md'} (hty : ty' = ty.mapKeys f)
    (hv : v' = v.mapKeys f) :
    (o.map (Declaration.mapKeys f)).push (.thmDecl ⟨nm', l, ty'⟩ v') =
      (o.push (.thmDecl ⟨nm, l, ty⟩ v)).map (Declaration.mapKeys f) := by
  subst hnm hty hv; rw [Array.map_push]; rfl

-- The elaboration budget: one theorem walks all of `genNested` (about 930 lines of
-- generator, each emitted term descended by `rg`); genMutual's 4000000 ran out at the
-- last step (the projection artifacts). It bounds elaboration only.
set_option maxHeartbeats 10000000 in
theorem genNested_mapKeys (hP : P.All) (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {b : BlockRec md} (hb : b.Good P) :
    ExRel (fun ds ds' => ds' = ds.map (Declaration.mapKeys f))
      (genNested ctx b) (genNested ctx' (b.mapKeys f)) := by
  obtain ⟨types, ctors, recs⟩ := b
  obtain ⟨hty, hct, hrc⟩ := hb
  unfold genNested
  simp only [← Bool.cond_eq_ite, except_throw_bind, BlockRec.mapKeys_types, BlockRec.mapKeys_ctors,
    BlockRec.mapKeys_recs, List.length_map]
  cases types with
  | nil => exact ExRel.throw'
  | cons t0 rest =>
  have ht0 := hty t0 List.mem_cons_self
  simp only [List.map_cons, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_name,
    ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_type, IndTypeRec.mapKeys_nP,
    IndTypeRec.mapKeys_nIdx, List.length_cons]
  have hl : ListRel (fun x x' => x' = IndTypeRec.mapKeys f x ∧ x.Good P) (t0 :: rest)
      (t0.mapKeys f :: rest.map (IndTypeRec.mapKeys f)) := ListRel.of_map (l := t0 :: rest) hty
  refine ExRel.bind (S := fun _ _ => True) (ExRel.forIn_list hl trivial fun t t' _ _ ht _ => ?_)
    fun _ _ _ => ?_
  · obtain ⟨rfl, htg⟩ := ht
    simp only [IndTypeRec.mapKeys_isReflexive, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_levelParams,
      IndTypeRec.mapKeys_nP]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw')
    exact ExRel.cond rfl (fun _ => ExRel.pure' trivial) (fun _ => ExRel.throw')
  simp only [Expr.stripPis_mapKeys]
  cases hs : Expr.stripPis (t0.nP + t0.nIdx) t0.cv.type with
  | none => first | exact ExRel.throw' | (simp only [Option.map_none]; exact ExRel.throw')
  | some q =>
  obtain ⟨pbs0, body⟩ := q
  have hpbs := Expr.stripPis_good ht0.1.2 hs
  cases body with
  | sort u => ?_
  | _ => exact ExRel.throw'
  simp only [Option.map_some, Expr.mapTele, Expr.mapKeys]
  refine ExRel.bind (S := fun _ _ => True) (ExRel.forIn_list hl trivial fun t t' _ _ ht _ => ?_)
    fun _ _ _ => ?_
  · obtain ⟨rfl, htg⟩ := ht
    simp only [IndTypeRec.mapKeys_nIdx, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_type,
      Expr.stripPis_mapKeys]
    cases Expr.stripPis (t0.nP + t.nIdx) t.cv.type with
    | none => exact ExRel.throw'
    | some q =>
      obtain ⟨_, body⟩ := q
      cases body <;> first | exact ExRel.throw' | exact ExRel.pure' trivial
  simp only [List.getElem?_map]
  cases hr0 : recs[0]? with
  | none => first | exact ExRel.throw' | (simp only [Option.map_none]; exact ExRel.throw')
  | some r0 =>
  have hr0g := hrc r0 (List.mem_of_getElem? hr0)
  simp only [Option.map_some, IndRecRec.mapKeys_nM, IndRecRec.mapKeys_nm, IndRecRec.mapKeys_cv,
    ConstantVal.mapKeys_type, ConstantVal.mapKeys_levelParams]
  refine ExRel.ite Iff.rfl (fun hM => ?_) (fun _ => ExRel.throw')
  simp only [Expr.stripPis_mapKeys]
  cases hp1 : Expr.stripPis t0.nP r0.cv.type with
  | none => first | exact ExRel.throw' | (simp only [Option.map_none]; exact ExRel.throw')
  | some q =>
  obtain ⟨_, afterP⟩ := q
  have hP1 := Expr.stripPis_good hr0g.1.2 hp1
  simp only [Option.map_some, Expr.mapTele, Expr.stripPis_mapKeys]
  cases hp2 : Expr.stripPis r0.nM afterP with
  | none => first | exact ExRel.throw' | (simp only [Option.map_none]; exact ExRel.throw')
  | some q =>
  obtain ⟨motiveBs, afterM⟩ := q
  have hP2 := Expr.stripPis_good hP1.2 hp2
  simp only [Option.map_some, Expr.mapTele, Expr.stripPis_mapKeys]
  cases hp3 : Expr.stripPis r0.nm afterM with
  | none => first | exact ExRel.throw' | (simp only [Option.map_none]; exact ExRel.throw')
  | some q =>
  obtain ⟨minorBs, _⟩ := q
  have hP3 := Expr.stripPis_good hP2.2 hp3
  simp only [Option.map_some, Expr.mapTele]
  have hmot : (Expr.mapBinders f motiveBs).map (fun x => x.1) =
      (motiveBs.map (fun x => x.1)).map (Expr.mapKeys f) := by
    simp [Expr.mapBinders, List.map_map, Function.comp_def]
  rw [hmot, ← List.map_cons]
  refine ExRel.bind (readMems_mapKeys hf _ _ hty (Expr.goodList_map fun b hb => hP2.1 b hb))
    fun mems mems' hm => ?_
  obtain ⟨rfl, hmG⟩ := hm
  refine ExRel.bind (S := fun _ _ => True)
    (ExRel.forIn_list (ListRel.of_map hmG) trivial fun mem mem' _ _ hmem _ => ?_) fun _ _ _ => ?_
  · obtain ⟨rfl, hmemG⟩ := hmem
    simp only [Mem.mapKeys_tag, Mem.mapKeys_nIdx]
    cases hrr : recs[mem.tag]? with
    | none => exact ExRel.throw_bind
    | some rr =>
    simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_nP, IndRecRec.mapKeys_nM,
      IndRecRec.mapKeys_nm, IndRecRec.mapKeys_nI, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_levelParams]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.throw')
    exact ExRel.cond rfl (fun _ => ExRel.pure' trivial) (fun _ => ExRel.throw')
  have hpbsEq : piBinders (List.take t0.nP (Expr.mapBinders f pbs0)) =
      (piBinders (List.take t0.nP pbs0)).map (Expr.mapKeys f) := by
    simp [piBinders, Expr.mapBinders, ← List.map_take, List.map_map, Function.comp_def]
  have hminEq : (Expr.mapBinders f minorBs).map (fun x => x.1) =
      (minorBs.map (fun x => x.1)).map (Expr.mapKeys f) := by
    simp [Expr.mapBinders, List.map_map, Function.comp_def]
  rw [hpbsEq, hminEq]
  refine ExRel.bind (readCtors_mapKeys hf ?hfamG _ (Expr.goodList_map fun b hb => hP3.1 b hb) ?hnF)
    fun cs cs' hcs => ?_
  case hfamG =>
    exact ⟨ht0.1.1, Expr.goodList_piBinders (Expr.BindersGood.take hpbs.1 _), hmG, (fun _ h => nomatch h)⟩
  case hnF =>
    intro k hk mem
    rw [find?_map_congr (p := fun x => x.tag == mem) fun x _ => rfl]
    cases List.find? (fun x => x.tag == mem) mems with
    | none => exact ExRel.throw'
    | some memR =>
      simp only [Option.map_some, Mem.mapKeys_real?, Mem.mapKeys_tag]
      cases memR.real? with
      | some _ =>
        simp only []
        rw [find?_map_congr (p := fun x => x.cv.name == k) fun c hc => by
          simp only [IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name]
          exact Key.map_beq hf (hct c hc).1 hk]
        cases List.find? (fun x => x.cv.name == k) ctors with
        | none => exact ExRel.throw'
        | some c => exact ExRel.pure' rfl
      | none =>
        simp only []
        cases hrr : recs[memR.tag]? with
        | none => exact ExRel.throw_bind
        | some rr =>
        have hrrG := hrc rr (List.mem_of_getElem? hrr)
        simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_rules, IndRecRec.mapKeys_cv]
        rw [find?_map_congr (p := fun x => x.ctor == k) fun x hx => by
          simp only [RecRule.mapKeys]
          exact Key.map_beq hf (hrrG.2 x hx).1 hk]
        cases List.find? (fun x => x.ctor == k) rr.rules with
        | none => exact ExRel.throw'
        | some rule => exact ExRel.pure' rfl
  obtain ⟨rfl, hcsG⟩ := hcs
  simp only [List.length_map]
  refine ExRel.cond rfl (fun _ => ?_) (fun _ => by exrel_throw)
  refine ExRel.bind (S := fun _ _ => True) (ExRel.forIn_same trivial fun m _ _ hm _ => ?_)
    fun _ _ _ => ?_
  · have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
    have hT := hty _ (getD_mem_of_lt hm' default)
    simp only [← Bool.cond_eq_ite, ← List.map_cons, getD_map_of_lt hm' default default,
      IndTypeRec.mapKeys_ctors, IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_name]
    refine ExRel.cond ?cm (fun _ => ?_) (fun _ => ?_)
    case cm =>
      rw [List.filter_map, show ((fun x : ACtor md' => x.mem == m) ∘ ACtor.mapKeys f) =
          (fun x : ACtor md => x.mem == m) from rfl, List.map_map,
        show ((fun x : ACtor md' => x.cname) ∘ ACtor.mapKeys f) = (Key.map f ∘ fun x : ACtor md => x.cname)
          from rfl, ← List.map_map,
        keyList_map_beq hf (fun k hk => by
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
          exact (hcsG c (List.mem_filter.mp hc).1).1) hT.2]
    · exact ExRel.pure' trivial
    · exrel_throw
  rw [List.filter_map, show ((fun x : Mem md' => x.real?.isNone) ∘ Mem.mapKeys f) =
    (fun x : Mem md => x.real?.isNone) from rfl]
  have hmimG : ∀ m ∈ List.filter (fun x => x.real?.isNone) mems, m.Good P :=
    fun m hm => hmG m (List.mem_filter.mp hm).1
  refine ExRel.bind (S := fun (gs : List (Group md)) gs' => gs' = gs.map (Group.mapKeys f) ∧
      ∀ g ∈ gs, g.Good P)
    (ExRel.forIn_list (ListRel.mergeSort_map ?hle hmimG) ⟨rfl, (fun _ h => nomatch h)⟩
      fun mem mem' gs gs' hmem hgs => ?_) fun gs gs' hgs => ?_
  case hle =>
    intro a ha b hb
    simp only [Mem.mapKeys_I, hctx.blocks a.I (hmimG a ha).1, hctx.blocks b.I (hmimG b hb).1]
    rw [decide_eq_decide]
    cases ctx.blocks a.I <;> cases ctx.blocks b.I <;> simp [List.getElem?_map] <;> exact Iff.rfl
  · obtain ⟨rfl, hmemG⟩ := hmem
    obtain ⟨rfl, hgsG⟩ := hgs
    simp only [List.any_map, Mem.mapKeys_tag, Function.comp_def,
      Group.mapKeys_tags, Mem.mapKeys_I, hctx.blocks mem.I hmemG.1]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => ?_)
    · exact ExRel.pure' ⟨rfl, hgsG⟩
    cases hcb : ctx.blocks mem.I with
    | none => simp only [Option.map_none]; exrel_throw
    | some cb =>
    have hcbG := hctx.blocksGood mem.I hmemG.1 cb hcb
    simp only [Option.map_some, BlockRec.mapKeys_types, BlockRec.mapKeys_recs,
      getD_map_default IndTypeRec.mapKeys_default, IndTypeRec.mapKeys_nP, IndTypeRec.mapKeys_cv,
      ConstantVal.mapKeys_levelParams, ConstantVal.mapKeys_name, Mem.mapKeys_pins, Mem.mapKeys_lv,
      List.length_map, List.getElem?_map]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => by exrel_throw)
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => by exrel_throw)
    cases hrI : cb.recs[0]? with
    | none => simp only [Option.map_none]; exrel_throw
    | some rI =>
    have hrIG := hcbG.2.2 rI (List.mem_of_getElem? hrI)
    simp only [Option.map_some, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_type, IndRecRec.mapKeys_nM,
      Expr.stripPis_mapKeys]
    cases hq1 : Expr.stripPis (cb.types.getD 0 default).nP rI.cv.type with
    | none => simp only [Option.map_none]; exrel_throw
    | some q =>
    obtain ⟨_, afterPI⟩ := q
    have hq1G := Expr.stripPis_good hrIG.1.2 hq1
    simp only [Option.map_some, Expr.mapTele, Expr.stripPis_mapKeys]
    cases hq2 : Expr.stripPis rI.nM afterPI with
    | none => simp only [Option.map_none]; exrel_throw
    | some q =>
    obtain ⟨motivesI, _⟩ := q
    have hq2G := Expr.stripPis_good hq1G.2 hq2
    simp only [Option.map_some, Expr.mapTele]
    rw [show (Expr.mapBinders f motivesI).map (fun x => x.1) =
        (motivesI.map (fun x => x.1)).map (Expr.mapKeys f) by
      simp [Expr.mapBinders, List.map_map, Function.comp_def]]
    refine ExRel.bind (readMems_mapKeys hf _ _ hcbG.1 (Expr.goodList_map fun b hb => hq2G.1 b hb))
      fun memsI memsI' hmI => ?_
    obtain ⟨rfl, hmIG⟩ := hmI
    have hcI0G : (cb.types.getD 0 default).Good P := by
      rw [List.getD_eq_getElem?_getD]
      cases h : cb.types[0]? with
      | none => exact ⟨⟨hP _, trivial⟩, (fun _ h => nomatch h)⟩
      | some t => exact hcbG.1 t (List.mem_of_getElem? h)
    refine ExRel.bind (S := fun (s : List Nat × List (Key md)) s' =>
        s'.1 = s.1 ∧ s'.2 = s.2.map (Key.map f) ∧ ∀ k ∈ s.2, k.Good P)
      (ExRel.forIn_list (ListRel.of_map (G := fun m => m.Good P ∧ m ∈ memsI) fun m hm => ⟨hmIG m hm, hm⟩)
        ⟨rfl, rfl, (fun _ h => nomatch h)⟩ fun memI memI' s s' hmemI hs => ?_) fun s s' hs => ?_
    · obtain ⟨rfl, hmemIG, -⟩ := hmemI
      obtain ⟨tags, rns⟩ := s
      obtain ⟨tags', rns'⟩ := s'
      obtain ⟨h1, h2, hrnG⟩ := hs
      simp only at h1 h2 hrnG
      subst h1 h2
      generalize hc : carrierAt _ memI memI.nIdx (varsAt 0 memI.nIdx) false = carrI
      have hcG : carrI.Good P := hc ▸ carrierAt_good hmemIG (Expr.goodList_varsAt _ _) false
      have h3 := congrArg (Expr.mapKeys f) hc
      rw [← carrierAt_mapKeys hf ⟨hcI0G.1.1, by simp [Expr.GoodList], hmIG, by simp⟩
        hmemIG] at h3
      simp only [Family.mapKeys, List.map_nil, varsAt_mapKeys] at h3
      simp only [Mem.mapKeys_nIdx]
      rw [h3, ← Expr.mapKeys_instantiateLevelParams]
      generalize hsp : substParams memI.nIdx (cb.types.getD 0 default).nP
        (List.map (fun x => Expr.liftLooseBVars memI.nIdx 0 x) mem.pins)
        (Expr.instantiateLevelParams (cb.types.getD 0 default).cv.levelParams mem.lv carrI) = E
      have hEG : E.Good P := hsp ▸ substParams_good
        (Expr.goodList_map fun p hp => Expr.Good.liftLooseBVars (hmemG.2.1 p hp) _ _)
        (Expr.Good.instantiateLevelParams hcG _ _)
      have h4 := congrArg (Expr.mapKeys f) hsp
      rw [← substParams_mapKeys] at h4
      simp only [List.map_map, Function.comp_def, Expr.mapKeys_liftLooseBVars] at h4 ⊢
      rw [h4]
      generalize hmc : matchCarrier _ memI.nIdx E = mc
      have h5 := congrArg (Option.map fun p => (p.1, p.2.map (Expr.mapKeys f))) hmc
      rw [← matchCarrier_mapKeys hf (fam := ⟨t0.cv.name, t0.cv.levelParams, t0.nP,
        piBinders (List.take t0.nP pbs0), u, rest.length + 1, mems, cs, _, _⟩)
        ⟨ht0.1.1, Expr.goodList_piBinders (Expr.BindersGood.take hpbs.1 _), hmG, hcsG⟩ _ hEG] at h5
      simp only [Family.mapKeys] at h5
      rw [h5]
      cases mc with
      | none => simp only [Option.map_none]; exrel_throw
      | some p =>
      obtain ⟨t, idx⟩ := p
      simp only [Option.map_some, Mem.mapKeys_tag]
      cases hrIm : cb.recs[memI.tag]? with
      | none => simp only [Option.map_none]; exrel_throw
      | some rIm =>
      have hrImG := hcbG.2.2 rIm (List.mem_of_getElem? hrIm)
      simp only [Option.map_some, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_name]
      refine ExRel.pure' ⟨rfl, by simp, fun k hk => ?_⟩
      rcases List.mem_append.mp hk with hk | hk
      · exact hrnG k hk
      · rw [List.mem_singleton.mp hk]; exact hrImG.1.1
    · obtain ⟨tags, rns⟩ := s
      obtain ⟨tags', rns'⟩ := s'
      obtain ⟨h1, h2, hrnG⟩ := hs
      simp only at h1 h2 hrnG
      subst h1 h2
      simp only [ConstantVal.mapKeys_levelParams]
      refine ExRel.cond rfl (fun _ => by exrel_throw) (fun _ => ?_)
      refine ExRel.pure' ⟨by simp [Group.mapKeys], fun g hg => ?_⟩
      rcases List.mem_append.mp hg with hg | hg
      · exact hgsG g hg
      · rw [List.mem_singleton.mp hg]; exact ⟨hrnG, hmemG.2.1⟩
  · obtain ⟨rfl, hgsG⟩ := hgs
    refine ExRel.bind (S := fun (s : List (Group md) × List (Group md) × Bool) s' =>
        s'.1 = s.1.map (Group.mapKeys f) ∧ s'.2.1 = s.2.1.map (Group.mapKeys f) ∧ s'.2.2 = s.2.2 ∧
          (∀ g ∈ s.1, g.Good P) ∧ ∀ g ∈ s.2.1, g.Good P)
      (ExRel.loopForIn (fun s => s.2.1.length + (if s.2.2 then 1 else 0)) ?hstep _ _ _
        (Nat.lt_succ_self _) ⟨rfl, rfl, rfl, (fun _ h => nomatch h), hgsG⟩) fun s s' hs => ?_
    case hstep =>
      intro a b hab
      obtain ⟨o, p, pr⟩ := a
      obtain ⟨o', p', pr'⟩ := b
      obtain ⟨h1, h2, h3, hoG, hpG⟩ := hab
      simp only at h1 h2 h3 hoG hpG
      subst h1 h2 h3
      simp only [List.isEmpty_map]
      refine ExRel.cond rfl (fun hc => ?_) (fun _ => ExRel.pure' ⟨rfl, rfl, rfl, hoG, hpG⟩)
      have hpr : pr' = true := by simp only [Bool.and_eq_true] at hc; exact hc.1
      refine ExRel.bind (S := fun (s : List (Group md) × List (Group md) × Bool) s' =>
          (s'.1 = s.1.map (Group.mapKeys f) ∧ s'.2.1 = s.2.1.map (Group.mapKeys f) ∧ s'.2.2 = s.2.2 ∧
            (∀ g ∈ s.1, g.Good P) ∧ ∀ g ∈ s.2.1, g.Good P) ∧
          s.2.1.Sublist p ∧ (s.2.2 = true → s.2.1.length < p.length))
        (ExRel.forIn_list (ListRel.of_map (G := fun g => g.Good P ∧ g ∈ p) fun g hg => ⟨hpG g hg, hg⟩)
          ⟨⟨rfl, rfl, rfl, hoG, hpG⟩, List.Sublist.refl p, fun h => nomatch h⟩
          fun g g' s s' hg hs => ?_) fun s s' hs => ?_
      · obtain ⟨rfl, hgG, hgp⟩ := hg
        obtain ⟨o2, p2, pr2⟩ := s
        obtain ⟨o2', p2', pr2'⟩ := s'
        obtain ⟨⟨h1, h2, h3, ho2G, hp2G⟩, hsub, hlen⟩ := hs
        simp only at h1 h2 h3 ho2G hp2G hsub hlen
        subst h1 h2 h3
        refine ExRel.cond ?cdep (fun _ => ?_) (fun _ => ?_)
        case cdep =>
          simp [Group.mapKeys_tags, List.filter_map, List.foldl_map, List.any_map, Function.comp_def] <;> rfl
        · refine ExRel.pure' ⟨⟨by simp, by simp [List.filter_map, Function.comp_def], rfl,
            fun x hx => ?_, fun x hx => hp2G x (List.mem_filter.mp hx).1⟩,
            (List.filter_sublist).trans hsub, fun _ => ?_⟩
          · rcases List.mem_append.mp hx with hx | hx
            · exact ho2G x hx
            · rw [List.mem_singleton.mp hx]; exact hgG
          · by_cases hl : p2.length < p.length
            · exact Nat.lt_of_le_of_lt (List.length_filter_le _ _) hl
            · have heq : p2 = p := hsub.eq_of_length (by have := hsub.length_le; omega)
              subst heq
              exact length_filter_lt_of_mem hgp (by simp)
        · exact ExRel.pure' ⟨⟨rfl, rfl, rfl, ho2G, hp2G⟩, hsub, hlen⟩
      · obtain ⟨o2, p2, pr2⟩ := s
        obtain ⟨o2', p2', pr2'⟩ := s'
        obtain ⟨⟨h1, h2, h3, ho2G, hp2G⟩, hsub, hlen⟩ := hs
        simp only at h1 h2 h3 ho2G hp2G hsub hlen
        subst h1 h2 h3
        refine ExRel.pure' ⟨⟨rfl, rfl, rfl, ho2G, hp2G⟩, ?_⟩
        simp only [hpr, if_true]
        have := hsub.length_le
        cases pr2'
        · simp only [Bool.false_eq_true, if_false]; omega
        · simp only [if_true]; have := hlen rfl; omega
    obtain ⟨o, p, pr⟩ := s
    obtain ⟨o', p', pr'⟩ := s'
    obtain ⟨h1, h2, h3, hoG, hpG⟩ := hs
    simp only at h1 h2 h3 hoG hpG
    subst h1 h2 h3
    simp only [List.isEmpty_map]
    refine ExRel.cond rfl (fun _ => ?_) (fun _ => by exrel_throw)
    refine ExRel.cond rfl (fun _ => by exrel_throw) (fun _ => ?_)
    have hbnG : ∀ k ∈ (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
        List.map (fun x => x.cv.name) ctors ++ List.map (fun x => x.cv.name) recs), k.Good P := by
      intro k hk
      simp only [List.mem_append, List.mem_cons, List.mem_map] at hk
      rcases hk with ((rfl | ⟨t, ht, rfl⟩) | ⟨c, hc, rfl⟩) | ⟨r, hr, rfl⟩
      · exact ht0.1.1
      · exact (hty t (List.mem_cons_of_mem _ ht)).1.1
      · exact (hct c hc).1
      · exact (hrc r hr).1.1
    have hbn : (Key.map f t0.cv.name ::
        List.map (fun x => x.cv.name) (List.map (IndTypeRec.mapKeys f) rest) ++
        List.map (fun x => x.cv.name) (List.map (IndCtorRec.mapKeys f) ctors) ++
        List.map (fun x => x.cv.name) (List.map (IndRecRec.mapKeys f) recs)) =
        (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
          List.map (fun x => x.cv.name) ctors ++ List.map (fun x => x.cv.name) recs).map
          (Key.map f) := by
      simp [List.map_map, Function.comp_def]
    simp only [hbn]
    generalize (t0.cv.name :: List.map (fun x => x.cv.name) rest ++
      List.map (fun x => x.cv.name) ctors ++ List.map (fun x => x.cv.name) recs) = bn at hbnG ⊢
    refine ExRel.bind (S := Eq) (ExRel.forIn_list (ListRel.of_map hmG) rfl fun mem mem' W W' hmem hW => ?_)
      fun W W' hW => ?_
    · obtain ⟨rfl, hmemG⟩ := hmem
      subst hW
      refine ExRel.bind (S := Eq) (ExRel.forIn_same rfl fun j W W' _ hW => ?_) fun W W' hW => ExRel.pure' hW
      subst hW
      simp only [Mem.mapKeys_idxBs, getD_mapKeys_default]
      rw [rn_map hf hbnG (Expr.GoodList.getD_default hmemG.2.2 j)]
      rw [idxSort_mapKeysOn' hP hctx.tbl
        (ctx := (piBinders (List.take t0.nP pbs0) ++ List.take j mem.idxBs).reverse) ?g1 ?g2 ?g3 rfl]
      case g1 =>
        intro x hx
        simp only [List.mem_reverse, List.mem_append] at hx
        rcases hx with hx | hx
        · exact Expr.goodList_piBinders (Expr.BindersGood.take hpbs.1 _) x hx
        · exact hmemG.2.2 x (List.mem_of_mem_take hx)
      case g2 => exact rn_good (Expr.GoodList.getD_default hmemG.2.2 j)
      case g3 => simp only [List.map_reverse, List.map_append, List.map_take]
      refine ExRel.bind (S := Eq) (ExRel.refl rfl) fun x x' hx => ?_
      subst hx
      cases x with
      | none => exrel_throw
      | some ℓ => exact ExRel.pure' rfl
    · subst hW
      generalize hFAM : (⟨t0.cv.name, t0.cv.levelParams, t0.nP, _, u, _, mems, cs, _, _⟩ : Family md) = FAM
      generalize hFAM' : (⟨Key.map f t0.cv.name, t0.cv.levelParams, t0.nP, _, u, _,
        List.map (Mem.mapKeys f) mems, List.map (ACtor.mapKeys f) cs, _, _⟩ : Family md') = FAM'
      have hFF : FAM' = FAM.mapKeys f := by rw [← hFAM, ← hFAM']; rfl
      subst hFF
      have hFAMG : FAM.Good P := by
        rw [← hFAM]
        exact ⟨ht0.1.1, Expr.goodList_piBinders (Expr.BindersGood.take hpbs.1 _), hmG, hcsG⟩
      -- the eliminator's level parameters, through the family
      have hlg := congrArg Family.large hFAM
      have heg := congrArg Family.elim hFAM
      dsimp only at hlg heg
      rw [hlg, heg]
      generalize (bif FAM.large then FAM.elim else freshLevelParam t0.cv.levelParams) = elimTag
      have hTG : t0.cv.name.Good P := ht0.1.1
      have hpbsG : Expr.GoodList P (piBinders (List.take t0.nP pbs0)) :=
        Expr.goodList_piBinders (Expr.BindersGood.take hpbs.1 _)
      have hmD : ∀ t, (mems.getD t default).Good P := by
        intro t
        rw [List.getD_eq_getElem?_getD]
        cases h : mems[t]? with
        | none => exact ⟨hP _, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
        | some m => exact hmG m (List.mem_of_getElem? h)
      have hcsn : cs.length = r0.nm := by simpa using ‹(cs.length == r0.nm) = true›
      -- 1. the tag block
      rw [replacePiBody_sort_mapKeys]
      refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial) fun tagTy tagTy' htt => ?_
      obtain ⟨rfl, -⟩ := htt
      refine ExRel.bind (S := ListRel fun c c' => c' = (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2) ∧ True)
        (ExRel.mapM (ListRel.of_map hmG) fun mem mem' hmem => ?_) fun tagCtors tagCtors' htc => ?_
      · obtain ⟨rfl, hmemG⟩ := hmem
        refine ExRel.bind (ExRel.need_rpb (P := P) _ _ _ ?_) fun ty ty' hty => ?_
        · rg
        obtain ⟨rfl, -⟩ := hty
        exact ExRel.pure' ⟨rfl, trivial⟩
      obtain ⟨rfl, -⟩ := forall₂_map_eq htc
      rw [show (tagCtors.map fun c => (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2)) = c4m f tagCtors
        from rfl]
      simp only [recTy_tag_map, recRhs_tag_map]
      refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
        fun tagRecTy tagRecTy' htr => ?_
      obtain ⟨rfl, -⟩ := htr
      refine ExRel.bind (S := ListRel fun r r' => r' = RecRule.mapKeys f r ∧ True)
        (ExRel.mapM (ListRel.of_map hmG) fun mem mem' hmem => ?_) fun tagRules tagRules' htru => ?_
      · obtain ⟨rfl, -⟩ := hmem
        refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial) fun rhs rhs' hrh => ?_
        obtain ⟨rfl, -⟩ := hrh
        exact ExRel.pure' ⟨rfl, trivial⟩
      obtain ⟨rfl, -⟩ := forall₂_map_eq htru
      -- 2. the auxiliary family
      rw [auxTyBody_map, Expr.replacePiBody_mapKeys]
      refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial) fun auxTy auxTy' hat => ?_
      obtain ⟨rfl, -⟩ := hat
      refine ExRel.bind (S := fun xs xs' => ListRel (fun c c' =>
          c' = (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2) ∧ True) xs xs' ∧ xs.length = cs.length)
        (ExRel.mapM_len (ListRel.of_map hcsG) fun c c' hc => ?_) fun auxCtors auxCtors' hac => ?_
      · obtain ⟨rfl, hcG⟩ := hc
        refine ExRel.bind (ExRel.need_rpb (P := P) _ _ _ ?_) fun ty ty' hty => ?_
        · rg
        obtain ⟨rfl, -⟩ := hty
        exact ExRel.pure' ⟨rfl, trivial⟩
      obtain ⟨hac, hlen⟩ := hac
      obtain ⟨rfl, -⟩ := forall₂_map_eq hac
      rw [show (auxCtors.map fun c => (c.1.map f, c.2.1, c.2.2.1.mapKeys f, c.2.2.2)) = c4m f auxCtors
        from rfl]
      simp only [recTy_aux_map, recRhs_aux_map]
      refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial)
        fun auxRecTy auxRecTy' har => ?_
      obtain ⟨rfl, -⟩ := har
      refine ExRel.bind (S := ListRel fun r r' => r' = RecRule.mapKeys f r ∧ True)
        (ExRel.mapM_same fun j hj => ?_) fun auxRules auxRules' haru => ?_
      · refine ExRel.bind (ExRel.need (G := fun _ => True) _ _ fun _ _ => trivial) fun rhs rhs' hrh => ?_
        obtain ⟨rfl, -⟩ := hrh
        have hj' : j < auxCtors.length := by have := List.mem_range.mp hj; omega
        rw [c4m_getD hj']
        exact ExRel.pure' ⟨rfl, trivial⟩
      obtain ⟨rfl, -⟩ := forall₂_map_eq haru
      -- 2b. the member models
      refine ExRel.bind (S := PS P f) (ExRel.forIn_same ?init fun m s s' hm hs => ?_) fun s s' hs => ?_
      case init =>
        refine ⟨?_, rfl, fun _ h => nomatch h⟩
        simp [Declaration.mapKeys, ConstantInfo.mapKeys, ConstantVal.mapKeys, IndCaps.mapKeys,
          List.map_append, List.map_map, Function.comp_def]
      · have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
        have hT := hty _ (getD_mem_of_lt hm' default)
        simp only [← List.map_cons, getD_map_of_lt hm' default default, IndTypeRec.mapKeys_nIdx,
          IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_type, ConstantVal.mapKeys_name]
        refine ExRel.bind (ExRel.need_pis (G := fun a => a.Good P) _ _ _ ?hb ?hG) fun v v' hv => ?_
        case hb => exact (RG.aux hFAMG _ _ (RGL.vars _ _)).1
        case hG =>
          intro a ha
          exact Expr.pisToLams_good hT.1.2 (auxAt_good hFAMG (Expr.goodList_varsAt' _ _)) ha
        obtain ⟨rfl, hvG⟩ := hv
        exact ExRel.pure' (PS.push hf hctx hs (by rfl) (by exact hT.1.1) _ (by rfl) ⟨rfl, hvG⟩)
      refine ExRel.cond rfl (fun _ => by exrel_throw) (fun _ => ?_)
      -- 3. `_impl.unpack`, then 4. per container group
      refine ExRel.bind (S := PS P f)
        (ExRel.forIn_list (ListRel.of_map hoG) (PS.push hf hctx hs (by rfl) (by exact hTG) _ ?uty ?uval)
          fun g g' s s' hg hs => ?_) fun s s' hs => ?_
      case uty => refine RG.eq_of (P := P) ?_; rg
      case uval => rg
      · obtain ⟨rfl, hgG⟩ := hg
        have hgcG : ∀ c ∈ List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) cs) [] g.tags,
            c.Good P := fun c hc => hcsG c (mem_gctors hc)
        simp only [Group.mapKeys_large, Group.mapKeys_tags, Group.mapKeys_lv, Group.mapKeys_nPI,
          Group.mapKeys_recNames, List.getElem?_map, getD_map_default Mem.mapKeys_default, Mem.mapKeys_j,
          Mem.mapKeys_nIdx, gctors_map]
        generalize List.foldl (fun acc t => acc ++ List.filter (fun x => x.mem == t) cs) [] g.tags = gctors
          at hgcG ⊢
        refine ExRel.cond rfl (fun _ => by exrel_throw) (fun _ => ?_)
        -- `pack_j`, by the member's container recursor at the group's motives
        refine ExRel.bind (S := PS P f) (ExRel.forIn_same hs fun k s s' hk hs => ?_) fun s s' hs => ?_
        · cases hrn : g.recNames[k]? with
          | none => simp only [Option.map_none]; exrel_throw
          | some rn =>
          have hrnG : rn.Good P := hgG.1 rn (List.mem_of_getElem? hrn)
          simp only [Option.map_some, pure_bind]
          refine ExRel.pure' (PS.push hf hctx hs (by rfl) (by exact hTG) _ ?_ ?_)
          · refine RG.eq_of (P := P) ?_; rg
          · rg
        -- `unpack_j` and `congrPack_j`
        refine ExRel.bind (S := PS P f) (ExRel.forIn_same hs fun t s s' ht hs => ?_) fun s s' hs => ?_
        · refine ExRel.pure' (PS.push hf hctx (PS.push hf hctx hs (by rfl) (by exact hTG) _ ?_ ?_)
            (by rfl) (by exact hTG) _ ?_ ?_)
          all_goals first | (refine RG.eq_of (P := P) ?_; rg) | rg
        -- `unpackPack_j`, by the container recursor into Prop
        obtain ⟨out, hts⟩ := s
        obtain ⟨out', hts'⟩ := s'
        obtain ⟨h1, h2, htsG⟩ := hs
        simp only at h1 h2 htsG
        subst h1 h2
        refine ExRel.bind (S := fun (o : Array (Declaration md)) o' => o' = o.map (Declaration.mapKeys f))
          (ExRel.forIn_same rfl fun k o o' hk ho => ?_) fun o o' ho => ExRel.pure' ⟨ho, rfl, htsG⟩
        subst ho
        cases hrn : g.recNames[k]? with
        | none => simp only [Option.map_none]; exrel_throw
        | some rn =>
        have hrnG : rn.Good P := hgG.1 rn (List.mem_of_getElem? hrn)
        simp only [Option.map_some, pure_bind]
        refine ExRel.pure' (push_thm_map (by rfl) _ ?_ ?_)
        all_goals refine RG.eq_of (P := P) ?_; rg
      -- 5. `_impl.packUnpack`, and `packUnpack_j` per mimic
      obtain ⟨out, hts⟩ := s
      obtain ⟨out', hts'⟩ := s'
      obtain ⟨h1, h2, htsG⟩ := hs
      simp only at h1 h2 htsG
      subst h1 h2
      refine ExRel.bind (S := fun (o : Array (Declaration md)) o' => o' = o.map (Declaration.mapKeys f))
        (ExRel.forIn_list (ListRel.mergeSort_map ?hle hmimG) (push_thm_map (by rfl) _ ?pty ?pval)
          fun mem mem' o o' hmem ho => ?_) fun o o' ho => ?_
      case hle =>
        intro a ha b hb
        simp only [Mem.mapKeys_I, hctx.blocks a.I (hmimG a ha).1, hctx.blocks b.I (hmimG b hb).1]
        rw [decide_eq_decide]
        cases ctx.blocks a.I <;> cases ctx.blocks b.I <;> simp [List.getElem?_map] <;> exact Iff.rfl
      case pty => refine RG.eq_of (P := P) ?_; rg
      case pval => refine RG.eq_of (P := P) ?_; rg
      · obtain ⟨rfl, hmemG⟩ := hmem
        subst ho
        refine ExRel.pure' (push_thm_map (by rfl) _ ?_ ?_)
        all_goals refine RG.eq_of (P := P) ?_; rg
      subst ho
      -- 6. the constructor models
      refine ExRel.bind (S := PS P f) (ExRel.forIn_list (ListRel.of_map hcsG) ⟨rfl, rfl, htsG⟩
        fun c c' s s' hc hs => ?_) fun s s' hs => ?_
      · obtain ⟨rfl, hcG⟩ := hc
        simp only [ACtor.mapKeys_mem, ACtor.mapKeys_cname, ACtor.mapKeys_nF, ACtor.mapKeys_kinds]
        refine ExRel.ite Iff.rfl (fun _ => ?_) (fun _ => ExRel.pure' hs)
        rw [find?_map_congr (p := fun x => x.cv.name == c.cname) fun c' hc' => by
          simp only [IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name]
          exact Key.map_beq hf (hct c' hc').1 hcG.1]
        cases hpc : List.find? (fun x => x.cv.name == c.cname) ctors with
        | none => simp only [Option.map_none]; exrel_throw
        | some pc =>
        have hpty : pc.cv.type.Good P := (hct pc (List.mem_of_find?_eq_some hpc)).2
        simp only [Option.map_some, IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_type]
        refine ExRel.bind (ExRel.need_pisRG (P := P) (f := f) _ _ _ ?_ ?_) fun v v' hv => ?_
        · rg
        · rg
        refine ExRel.pure' (PS.push hf hctx hs (by rfl) (by exact hcG.1) _ ?_ hv)
        refine RG.eq_of (P := P) ?_; rg
      -- 7. `_impl.rec`
      rw [rn_map hf hbnG hr0g.1.2, Expr.stripPis_mapKeys]
      cases hpre : Expr.stripPis (t0.nP + r0.nM + r0.nm)
          (Expr.renameConsts (fun x => bif bn.contains x then modelName x else x) r0.cv.type) with
      | none => simp only [Option.map_none]; exrel_throw
      | some q =>
      obtain ⟨prefixBs, _⟩ := q
      have hpreG : Expr.GoodList P (piBinders prefixBs) :=
        Expr.goodList_piBinders' (Expr.stripPis_good (rn_good hr0g.1.2) hpre).1
      simp only [Option.map_some, Expr.mapTele, piBinders_mapBinders']
      refine ExRel.bind (S := PS P f)
        (ExRel.forIn_list (ListRel.of_map hmG) (PS.push hf hctx hs (by rfl) (by exact hTG) _ ?rty ?rval)
          fun mem mem' s s' hmem hs => ?_) fun s s' hs => ?_
      case rty => refine RG.eq_of (P := P) ?_; rg
      case rval => rg
      · -- 8. the recursor models
        obtain ⟨rfl, hmemG⟩ := hmem
        simp only [Mem.mapKeys_tag]
        cases hrr : recs[mem.tag]? with
        | none => simp only [Option.map_none]; exrel_throw
        | some rr =>
        have hrrG := hrc rr (List.mem_of_getElem? hrr)
        have hrrT : rr.cv.type.Good P := hrrG.1.2
        simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_type,
          ConstantVal.mapKeys_name]
        refine ExRel.bind (ExRel.need_pisRG (P := P) (f := f) _ _ _ ?_ ?_) fun v v' hv => ?_
        · rg
        · rg
        refine ExRel.pure' (PS.push hf hctx hs (by rfl) (by exact hrrG.1.1) _ ?_ hv)
        refine RG.eq_of (P := P) ?_; rg
      -- 9. the iota theorems
      obtain ⟨out, hts⟩ := s
      obtain ⟨out', hts'⟩ := s'
      obtain ⟨h1, h2, htsG⟩ := hs
      simp only at h1 h2 htsG
      subst h1 h2
      have hrD : ∀ k, (recs.getD k default).cv.name.Good P := by
        intro k
        rw [List.getD_eq_getElem?_getD]
        cases h : recs[k]? with
        | none => exact hP _
        | some r => exact (hrc r (List.mem_of_getElem? h)).1.1
      refine ExRel.bind (S := fun (o : Array (Declaration md)) o' => o' = o.map (Declaration.mapKeys f))
        (ExRel.forIn_list (ListRel.of_map hmG) rfl fun mem mem' o o' hmem ho => ?_) fun o o' ho => ?_
      · obtain ⟨rfl, hmemG⟩ := hmem
        subst ho
        simp only [Mem.mapKeys_tag]
        cases hrr : recs[mem.tag]? with
        | none => simp only [Option.map_none]; exrel_throw
        | some rr =>
        have hrrG := hrc rr (List.mem_of_getElem? hrr)
        have hrrN : rr.cv.name.Good P := hrrG.1.1
        simp only [Option.map_some, pure_bind, IndRecRec.mapKeys_cv, ConstantVal.mapKeys_name]
        rw [List.filter_map, show ((fun x : ACtor md' => x.mem == mem.tag) ∘ ACtor.mapKeys f) =
          (fun x : ACtor md => x.mem == mem.tag) from rfl]
        refine ExRel.bind (S := fun (o : Array (Declaration md)) o' => o' = o.map (Declaration.mapKeys f))
          (ExRel.forIn_list (ListRel.of_map (G := fun c => c.Good P) fun c hc => hcsG c (List.mem_filter.mp hc).1)
            rfl fun c c' o o' hc ho => ?_) fun o o' ho => ExRel.pure' ho
        obtain ⟨rfl, hcG⟩ := hc
        subst ho
        refine ExRel.cond rfl (fun _ => ?_) (fun _ => ?_) <;>
        · refine ExRel.bind (ExRel.need_pisRG (P := P) (f := f) _ _ _ ?_ ?_) fun v v' hv => ?_
          · rg
          · rg
          refine ExRel.pure' (push_thm_map (by rfl) _ ?_ hv.1)
          refine RG.eq_of (P := P) ?_; rg
      subst ho
      -- 10. the projection artifacts
      refine ExRel.cond rfl (fun _ => ?_) (fun _ => ExRel.pure' (by rw [Array.toList_map]))
      refine ExRel.bind (S := PS P f) (ExRel.forIn_same ⟨rfl, rfl, htsG⟩ fun m s s' hm hs => ?_)
        fun s s' hs => ExRel.pure' (by rw [hs.1, Array.toList_map])
      obtain ⟨out, hs⟩ := s
      obtain ⟨out', hs'⟩ := s'
      obtain ⟨h1, h2, hsG⟩ := hs
      simp only at h1 h2 hsG
      subst h1 h2
      have hm' : m < (t0 :: rest).length := List.mem_range.mp hm
      have hT := hty _ (getD_mem_of_lt hm' default)
      rw [List.filter_map, show ((fun x : ACtor md' => x.mem == m) ∘ ACtor.mapKeys f) =
        (fun x : ACtor md => x.mem == m) from rfl]
      cases hown : List.filter (fun x => x.mem == m) cs with
      | nil => exact ExRel.pure' ⟨rfl, rfl, hsG⟩
      | cons c tl =>
      cases tl with
      | cons _ _ => exact ExRel.pure' ⟨rfl, rfl, hsG⟩
      | nil =>
      have hcG : c.Good P := by
        have : c ∈ List.filter (fun x => x.mem == m) cs := by rw [hown]; exact List.mem_singleton_self c
        exact hcsG c (List.mem_filter.mp this).1
      simp only [List.map_singleton]
      simp only [← List.map_cons, getD_map_of_lt hm' default default, IndTypeRec.mapKeys_nIdx,
        IndTypeRec.mapKeys_cv, ConstantVal.mapKeys_name, ConstantVal.mapKeys_type, ACtor.mapKeys_nF,
        ACtor.mapKeys_cname]
      refine ExRel.cond rfl (fun _ => ExRel.pure' ⟨rfl, rfl, hsG⟩) (fun _ => ?_)
      rw [find?_map_congr (p := fun x => x.cv.name == c.cname) fun c' hc' => by
        simp only [IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name]
        exact Key.map_beq hf (hct c' hc').1 hcG.1]
      cases hpc : List.find? (fun x => x.cv.name == c.cname) ctors with
      | none => exact ExRel.pure' ⟨rfl, rfl, hsG⟩
      | some pc =>
      have hpcG := hct pc (List.mem_of_find?_eq_some hpc)
      simp only [Option.map_some, IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_type, rn_map hf hbnG hpcG.2,
        Expr.stripPis_mapKeys]
      cases hcbs : Expr.stripPis (t0.nP + c.nF)
          (Expr.renameConsts (fun x => bif bn.contains x then modelName x else x) pc.cv.type) with
      | none => exact ExRel.pure' ⟨rfl, rfl, hsG⟩
      | some q =>
      obtain ⟨cbs, _⟩ := q
      have hcbsG := (Expr.stripPis_good (rn_good hpcG.2) hcbs).1
      simp only [Option.map_some, Expr.mapTele]
      refine ExRel.bind (S := PS3 P f) (ExRel.forIn_same ⟨⟨rfl, rfl, hsG⟩, rfl⟩ fun i s s' hi hs => ?_)
        fun s s' hs => ExRel.pure' hs.1
      obtain ⟨out, hs, stop⟩ := s
      obtain ⟨out', hs', stop'⟩ := s'
      obtain ⟨⟨h1, h2, hsG⟩, h3⟩ := hs
      simp only at h1 h2 h3 hsG
      subst h1 h2 h3
      refine ExRel.cond rfl (fun _ => ExRel.pure' ⟨⟨rfl, rfl, hsG⟩, rfl⟩) (fun _ => ?_)
      have hi' := List.mem_range.mp hi
      refine ExRel.bind (S := Eq) (ExRel.refl (congrArg Except.toOption
        (Eq.symm (sortOf_mapKeysOn' hP (tblOn_local hf hctx.tbl ?hgt ?hgtG) ?hC ?hE ?h1 ?h2))))
        fun x x' hx => ?_
      case hgt =>
        simp only [List.map_cons, List.map_append, List.map_map]
        refine append_congr' (cons_congr' rfl (List.map_congr_left fun t _ => rfl))
          (List.map_congr_left fun c'' hc'' => ?_)
        simp only [Function.comp_apply, IndCtorRec.mapKeys_cv, ConstantVal.mapKeys_name,
          ConstantVal.mapKeys_type, rn_map hf hbnG (hct c'' hc'').2]
        rfl
      case hgtG =>
        intro x hx
        simp only [List.mem_cons, List.mem_append, List.mem_map] at hx
        rcases hx with (rfl | ⟨t, ht, rfl⟩) | ⟨c'', hc'', rfl⟩
        · exact ⟨ht0.1.1, ht0.1.2⟩
        · exact (hty t (List.mem_cons_of_mem _ ht)).1
        · exact ⟨(hct c'' hc'').1, rn_good (hct c'' hc'').2⟩
      case hC =>
        intro x hx
        simp only [List.mem_reverse, List.mem_map] at hx
        obtain ⟨b, hb, rfl⟩ := hx
        exact hcbsG b (List.mem_of_mem_take hb)
      case hE => exact Expr.BindersGood.getD_fst hcbsG _
      case h1 =>
        simp only [Expr.mapBinders, List.map_map, List.map_reverse, ← List.map_take, Function.comp_def]
      case h2 => rw [mapBinders_getD]
      subst hx
      cases x with
      | none => exact ExRel.pure' ⟨⟨rfl, rfl, hsG⟩, rfl⟩
      | some ℓi =>
      simp only []
      generalize hip : Expr.instPisAtLift _ (Expr.renameConsts _ pc.cv.type) = ip
      have hipG : ∀ e, ip = some e → e.Good P := by
        intro e he
        refine Expr.instPisAtLift_good ?_ (rn_good hpcG.2) (hip ▸ he)
        intro x hx
        simp only [List.mem_append, List.mem_map] at hx
        rcases hx with hx | ⟨j, _, rfl⟩
        · exact Expr.goodList_structProjPs _ x hx
        · simp only [Expr.good_mkAppN_iff, Expr.goodList_append, Expr.goodList_cons, Expr.goodList_nil]
          exact ⟨hT.1.1, Expr.goodList_structProjPs _, trivial, trivial⟩
      have h2 := congrArg (Option.map (Expr.mapKeys f)) hip
      rw [← Expr.instPisAtLift_mapKeys] at h2
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        structProjPs_mapKeys, Expr.mapKeys_mkAppN, constP_mapKeys, projModelName_map, Expr.mapKeys] at h2 ⊢
      rw [h2]
      cases ip with
      | none => exact ExRel.pure' ⟨⟨rfl, rfl, hsG⟩, rfl⟩
      | some e =>
      have heG := hipG e rfl
      cases e with
      | forallE fdom fbody fm => ?_
      | _ => exact ExRel.pure' ⟨⟨rfl, rfl, hsG⟩, rfl⟩
      have hfdomG : fdom.Good P := heG.1
      simp only [Option.map_some, Expr.mapKeys]
      generalize hrp : Expr.replacePiBody t0.nP _ (Expr.forallE _ fdom bm) = rp
      have hrpG : ∀ e, rp = some e → e.Good P := by
        intro e he
        refine Expr.replacePiBody_good hT.1.2 ?_ (hrp ▸ he)
        exact ⟨Expr.good_mkAppN_iff.mpr ⟨hT.1.1, Expr.goodList_varsAt _ _⟩, heG.1⟩
      have h3 := congrArg (Option.map (Expr.mapKeys f)) hrp
      rw [← Expr.replacePiBody_mapKeys] at h3
      simp only [Expr.mapKeys, Expr.mapKeys_mkAppN, constP_mapKeys, modelName_map, varsAt_mapKeys] at h3
      rw [h3]
      cases rp with
      | none => exact ExRel.pure' ⟨⟨rfl, rfl, hsG⟩, rfl⟩
      | some pty =>
      simp only [Option.map_some]
      generalize hpf : Expr.pisToLams (t0.nP + c.nF) (mkPis (piBinders cbs) _) _ = pfo
      generalize hpf' : Expr.pisToLams (t0.nP + c.nF) (mkPis (piBinders (Expr.mapBinders f cbs)) _) _ = pfo'
      have hcbsL : Expr.GoodList P (piBinders cbs) := Expr.goodList_piBinders' hcbsG
      have hTn : ((t0 :: rest).getD m default).cv.name.Good P := hT.1.1
      have hps : PS P f (out, hs) (out.map (Declaration.mapKeys f), keyMap f hs) := ⟨rfl, rfl, hsG⟩
      have hdomG : ((cbs.getD (t0.nP + i) default).1).Good P := Expr.BindersGood.getD_fst hcbsG _
      have hpo : pfo' = pfo.map (Expr.mapKeys f) := by
        rw [← hpf, ← hpf']
        simp only [piBinders_mapBinders', mapBinders_getD]
        refine pisToLams_RG (P := P) ?_ ?_ <;> rg
      subst hpo
      cases pfo with
      | none =>
        refine ExRel.pure' (PS3.of (PS.push hf hctx hps (nm := projModelName _ i) (by rfl)
          (by exact hT.1.1) _ rfl ?_))
        rg
      | some pfL =>
        refine ExRel.pure' (PS3.of (PS.pushThm (PS.push hf hctx hps (nm := projModelName _ i) (by rfl)
          (by exact hT.1.1) _ rfl ?_)
          (by rfl) _ ?_ rfl))
        · rg
        · refine RG.eq_of (P := P) ?_; rg

/-! ## The generator -/

/-- **The generated records commute with the renaming** (parametricity, both rungs):
at a context agreeing with its renaming on the good keys (`CtxAgree`, which the
reader state built from the stream supplies), a good block's generation and the
renamed block's either both fail or give the renamed records. -/
theorem generate_mapKeys (hP : P.All) (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {b : BlockRec md} (hb : b.Good P) :
    ExRel (fun ds ds' => ds' = ds.map (Declaration.mapKeys f))
      (generate ctx b) (generate ctx' (b.mapKeys f)) := by
  unfold generate
  refine ExRel.ite ?_ (fun _ => genNested_mapKeys hP hf hctx hb) (fun _ => genMutual_mapKeys hP hf hctx hb)
  simp only [BlockRec.mapKeys_types, List.any_map, Function.comp_def, IndTypeRec.mapKeys_numNested]
  exact Iff.rfl

/-- `generate_mapKeys` as the runs' results: the renamed block's records are the
renamed records, or both runs fail. -/
theorem generate_toOption_mapKeys (hP : P.All) (hf : InjOn f P) {ctx : Ctx md} {ctx' : Ctx md'}
    (hctx : CtxAgree f P ctx ctx') {b : BlockRec md} (hb : b.Good P) :
    (generate ctx' (b.mapKeys f)).toOption = (generate ctx b).toOption.map (List.map (Declaration.mapKeys f)) :=
  ExRel.toOption_eq (generate_mapKeys hP hf hctx hb)

end Ix.Kernel.Frontend.InModel
