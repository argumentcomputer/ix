import Ix.Compile.Canon.Classes

/-!
# M7 L1: comparison results and total preorders on the ok-domain

Pass 1's comparators (`Ix/Compile/Canon/Order.lean`) return `Except String SOrder`: an
error (a metavariable, an unknown universe parameter, an external constant without a
compiled address, an undecodable contract) or an ordering with a strength flag. The
statement "the key is a total preorder at a fixed context" (design document §3.2) is made
precise here, on the comparisons that succeed:

* `Le r`: `r` succeeded with an ordering other than `gt`;
* `PreOn S F`: on the points satisfying `S`, the comparison `F` is **oriented** (a
  successful `F a b` read the other way is `F b a`, the same strength and the swapped
  ordering) and **transitive in the strong sense**: two successful `≤` steps give a
  successful `≤` (`F a b ≤`, `F b c ≤` imply that `F a c` succeeds and is `≤`).

Orientation gives reflexivity on the ok-domain and antisymmetry up to the equivalence
`F a b = eq`; transitivity in this form also closes the ok-domain under chains, so a class
whose adjacent members compared successfully is totally comparable (`Refine.lean`).

The combinators: lexicographic products (`SOrder.cmpM`, the `if o ≠ eq then o else …`
form of the constant case, `SOrder.zipM` on lists), comparisons by a lawful `cmp` on a key
(`PreOn.pureCmp`), and dispatch on a tag (`PreOn.ofTag`).
-/

namespace Ix.CompileCert.Canon

/-! ## Results -/

/-- `r` succeeded with an ordering other than `gt`. -/
def Le (r : Except ε SOrder) : Prop := ∃ s o, r = .ok ⟨s, o⟩ ∧ o ≠ .gt

/-- A comparison restricted to the points satisfying `S` is a total preorder on its
ok-domain (see the module docstring). -/
structure PreOn {α : Type u} (S : α → Prop) (F : α → α → Except ε SOrder) : Prop where
  swap : ∀ {a b}, S a → S b → ∀ {s o}, F a b = .ok ⟨s, o⟩ → F b a = .ok ⟨s, o.swap⟩
  trans : ∀ {a b c}, S a → S b → S c → Le (F a b) → Le (F b c) → Le (F a c)

/-- A total preorder on the ok-domain, on every point. -/
abbrev TotalPre {α : Type u} (F : α → α → Except ε SOrder) : Prop := PreOn (fun _ => True) F

theorem le_ok {r : Except ε SOrder} {s o} (h : r = .ok ⟨s, o⟩) (ho : o ≠ .gt) : Le r :=
  ⟨s, o, h, ho⟩

theorem Le.ok {r : Except ε SOrder} (h : Le r) : ∃ x, r = .ok x := by
  obtain ⟨s, o, h, -⟩ := h; exact ⟨_, h⟩

theorem not_le_error {e : ε} : ¬ Le (.error e : Except ε SOrder) := by
  rintro ⟨s, o, h, -⟩; cases h

/-- `Ix.Common` derives its own `BEq Ordering` (`instBEqOrdering_ix`), which shadows core's
wherever it is imported; Pass 1's `o != .eq` tests use it. It is lawful. -/
instance instLawfulBEqOrderingIx : LawfulBEq Ordering where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  rfl {a} := by cases a <;> decide

namespace PreOn

variable {α : Type u} {S : α → Prop} {F : α → α → Except ε SOrder}

theorem mono {S' : α → Prop} (h : PreOn S F) (hs : ∀ a, S' a → S a) : PreOn S' F where
  swap ha hb := h.swap (hs _ ha) (hs _ hb)
  trans ha hb hc := h.trans (hs _ ha) (hs _ hb) (hs _ hc)

theorem comap {β : Type v} {S' : β → Prop} (h : PreOn S F) (g : β → α)
    (hs : ∀ b, S' b → S (g b)) : PreOn S' (fun a b => F (g a) (g b)) where
  swap ha hb := h.swap (hs _ ha) (hs _ hb)
  trans ha hb hc := h.trans (hs _ ha) (hs _ hb) (hs _ hc)

theorem congr {G : α → α → Except ε SOrder} (h : PreOn S F)
    (he : ∀ a b, S a → S b → F a b = G a b) : PreOn S G where
  swap ha hb := by
    intro s o hab
    rw [← he _ _ hb ha]; rw [← he _ _ ha hb] at hab; exact h.swap ha hb hab
  trans ha hb hc := by
    rw [← he _ _ ha hb, ← he _ _ hb hc, ← he _ _ ha hc]; exact h.trans ha hb hc

theorem swap_iff (h : PreOn S F) {a b} (ha : S a) (hb : S b) {s o} :
    F a b = .ok ⟨s, o⟩ ↔ F b a = .ok ⟨s, o.swap⟩ := by
  refine ⟨h.swap ha hb, fun h' => ?_⟩
  have := h.swap hb ha h'; simpa using this

/-- Reflexivity where the comparison succeeds. -/
theorem refl (h : PreOn S F) {a} (ha : S a) {s o} (hab : F a a = .ok ⟨s, o⟩) : o = .eq := by
  have := h.swap ha ha hab
  rw [hab] at this
  cases o <;> simp [Ordering.swap] at this ⊢

theorem lt_of_lt_le (h : PreOn S F) {a b c} (ha : S a) (hb : S b) (hc : S c) {s}
    (hab : F a b = .ok ⟨s, .lt⟩) (hbc : Le (F b c)) : ∃ s', F a c = .ok ⟨s', .lt⟩ := by
  obtain ⟨s3, o3, hac, hne⟩ := h.trans ha hb hc (le_ok hab (by decide)) hbc
  cases o3 with
  | lt => exact ⟨s3, hac⟩
  | gt => exact absurd rfl hne
  | eq =>
    exfalso
    have hca := h.swap ha hc hac
    have hba := h.swap ha hb hab
    obtain ⟨s4, o4, hba', hne4⟩ := h.trans hb hc ha hbc (le_ok hca (by decide))
    rw [hba] at hba'
    simp only [Except.ok.injEq, SOrder.mk.injEq] at hba'
    obtain ⟨-, h4⟩ := hba'
    exact hne4 (by rw [← h4]; rfl)

theorem lt_of_le_lt (h : PreOn S F) {a b c} (ha : S a) (hb : S b) (hc : S c) {s}
    (hab : Le (F a b)) (hbc : F b c = .ok ⟨s, .lt⟩) : ∃ s', F a c = .ok ⟨s', .lt⟩ := by
  obtain ⟨s3, o3, hac, hne⟩ := h.trans ha hb hc hab (le_ok hbc (by decide))
  cases o3 with
  | lt => exact ⟨s3, hac⟩
  | gt => exact absurd rfl hne
  | eq =>
    exfalso
    have hca := h.swap ha hc hac
    have hcb := h.swap hb hc hbc
    obtain ⟨s4, o4, hcb', hne4⟩ := h.trans hc ha hb (le_ok hca (by decide)) hab
    rw [hcb] at hcb'
    simp only [Except.ok.injEq, SOrder.mk.injEq] at hcb'
    obtain ⟨-, h4⟩ := hcb'
    exact hne4 (by rw [← h4]; rfl)

theorem eq_trans (h : PreOn S F) {a b c} (ha : S a) (hb : S b) (hc : S c) {s1 s2}
    (hab : F a b = .ok ⟨s1, .eq⟩) (hbc : F b c = .ok ⟨s2, .eq⟩) : ∃ s, F a c = .ok ⟨s, .eq⟩ := by
  obtain ⟨s3, o3, hac, hne⟩ := h.trans ha hb hc (le_ok hab (by decide)) (le_ok hbc (by decide))
  have hcb := h.swap hb hc hbc
  have hba := h.swap ha hb hab
  obtain ⟨s4, o4, hca, hne4⟩ := h.trans hc hb ha (le_ok hcb (by decide)) (le_ok hba (by decide))
  have hca' := h.swap ha hc hac
  rw [hca'] at hca
  simp only [Except.ok.injEq, SOrder.mk.injEq] at hca
  obtain ⟨-, h4⟩ := hca
  cases o3 with
  | eq => exact ⟨s3, hac⟩
  | gt => exact absurd rfl hne
  | lt => exact absurd (by rw [← h4]; rfl) hne4

/-! ### Combinators -/

/-- Comparison of keys by a lawful `cmp`, with a fixed strength. -/
theorem pureCmp {β : Type v} (cmp : β → β → Ordering) [Std.TransCmp cmp] (k : α → β)
    (s : Bool := true) : PreOn S (fun a b => (pure ⟨s, cmp (k a) (k b)⟩ : Except ε SOrder)) where
  swap _ _ := by
    intro s' o h
    simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    rw [Std.OrientedCmp.eq_swap (cmp := cmp)]
  trans _ _ _ := by
    rintro ⟨s1, o1, h1, n1⟩ ⟨s2, o2, h2, n2⟩
    simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2
    refine ⟨s, cmp (k _) (k _), rfl, ?_⟩
    exact Ordering.isLE_iff_ne_gt.1
      (Std.TransCmp.isLE_trans (Ordering.isLE_iff_ne_gt.2 n1) (Ordering.isLE_iff_ne_gt.2 n2))

/-- A constant result `⟨s, eq⟩`. -/
theorem const_eq (s : Bool) : PreOn S (fun _ _ => (pure ⟨s, .eq⟩ : Except ε SOrder)) where
  swap _ _ := by
    intro s' o h
    simp only [pure, Except.pure, Except.ok.injEq, SOrder.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  trans _ _ _ := fun _ _ => ⟨s, .eq, rfl, by decide⟩

end PreOn

/-! ## The lexicographic step of `SOrder.cmpM` -/

theorem cmpM_ok {x y : Except ε SOrder} {r : SOrder} :
    SOrder.cmpM x y = .ok r ↔ ∃ a, x = .ok a ∧
      ((a.ord ≠ .eq ∧ r = a) ∨ (a.ord = .eq ∧ ∃ b, y = .ok b ∧ r = ⟨a.strong && b.strong, b.ord⟩)) := by
  cases x with
  | error e => simp [SOrder.cmpM, bind, Except.bind]
  | ok a =>
    obtain ⟨sa, oa⟩ := a
    cases y with
    | error e =>
      cases sa <;> cases oa <;>
        simp [SOrder.cmpM, bind, Except.bind, pure, Except.pure, eq_comm]
    | ok b =>
      obtain ⟨sb, ob⟩ := b
      cases sa <;> cases oa <;>
        simp [SOrder.cmpM, bind, Except.bind, pure, Except.pure, eq_comm]

/-- The constant case's form: `do let u ← x; if u.ord != .eq then pure u else y`. -/
def lexIf (x y : Except ε SOrder) : Except ε SOrder := do
  let u ← x
  if u.ord != .eq then pure u else y

theorem lexIf_error (e : ε) (y : Except ε SOrder) : lexIf (.error e) y = .error e := rfl

theorem lexIf_okLeft (a : SOrder) (y : Except ε SOrder) :
    lexIf (.ok a) y = if a.ord != .eq then .ok a else y := rfl

theorem lexIf_ok {x y : Except ε SOrder} {r : SOrder} :
    lexIf x y = .ok r ↔ ∃ a, x = .ok a ∧ ((a.ord ≠ .eq ∧ r = a) ∨ (a.ord = .eq ∧ y = .ok r)) := by
  cases x with
  | error e => rw [lexIf_error]; simp
  | ok a =>
    rw [lexIf_okLeft]
    by_cases h : a.ord = .eq
    · have hb : (a.ord != .eq) = false := by simp [h]
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro e; exact ⟨a, rfl, .inr ⟨h, e⟩⟩
      · rintro ⟨a', e, (⟨h', -⟩ | ⟨-, e'⟩)⟩
        · cases e; exact absurd h h'
        · exact e'
    · have hb : (a.ord != .eq) = true := by simpa using h
      simp only [hb, ↓reduceIte]
      constructor
      · intro e; cases e; exact ⟨_, rfl, .inl ⟨h, rfl⟩⟩
      · rintro ⟨a', e, (⟨-, rfl⟩ | ⟨h', -⟩)⟩
        · cases e; rfl
        · cases e; exact absurd h' h

namespace PreOn

variable {α : Type u} {S : α → Prop} {F G : α → α → Except ε SOrder}

/-- The ordering of a successful `≤` lexicographic step: the first component is `lt`, or
it is `eq` and the second is `≤`. -/
private theorem lex_le_cases {x y : Except ε SOrder}
    (h : Le (SOrder.cmpM x y)) :
    (∃ s, x = .ok ⟨s, .lt⟩) ∨ ((∃ s, x = .ok ⟨s, .eq⟩) ∧ Le y) := by
  obtain ⟨s, o, hr, hne⟩ := h
  obtain ⟨a, hx, (⟨ha, he⟩ | ⟨ha, b, hy, he⟩)⟩ := cmpM_ok.1 hr
  · subst he
    cases o
    · exact .inl ⟨s, hx⟩
    · exact absurd rfl ha
    · exact absurd rfl hne
  · obtain ⟨sa, oa⟩ := a
    obtain ⟨sb, ob⟩ := b
    simp only [SOrder.mk.injEq] at ha he
    subst ha
    obtain ⟨-, rfl⟩ := he
    exact .inr ⟨⟨sa, hx⟩, ⟨sb, o, hy, hne⟩⟩

private theorem lexIf_le_cases {x y : Except ε SOrder}
    (h : Le (lexIf x y)) :
    (∃ s, x = .ok ⟨s, .lt⟩) ∨ ((∃ s, x = .ok ⟨s, .eq⟩) ∧ Le y) := by
  obtain ⟨s, o, hr, hne⟩ := h
  obtain ⟨a, hx, (⟨ha, he⟩ | ⟨ha, hy⟩)⟩ := lexIf_ok.1 hr
  · subst he
    cases o
    · exact .inl ⟨s, hx⟩
    · exact absurd rfl ha
    · exact absurd rfl hne
  · obtain ⟨sa, oa⟩ := a
    simp only at ha
    subst ha
    exact .inr ⟨⟨sa, hx⟩, ⟨s, o, hy, hne⟩⟩

/-- The lexicographic product of two preorders, combined by `SOrder.cmpM`. -/
theorem cmpM (hF : PreOn S F) (hG : PreOn S G) :
    PreOn S (fun a b => SOrder.cmpM (F a b) (G a b)) where
  swap ha hb := by
    intro s o h
    obtain ⟨a, hx, (⟨hne, he⟩ | ⟨heq, b, hy, he⟩)⟩ := cmpM_ok.1 h
    · subst he
      refine cmpM_ok.2 ⟨⟨s, o.swap⟩, hF.swap ha hb hx, .inl ⟨?_, rfl⟩⟩
      cases o <;> simp_all [Ordering.swap]
    · obtain ⟨sa, oa⟩ := a
      obtain ⟨sb, ob⟩ := b
      simp only [SOrder.mk.injEq] at heq he
      subst heq
      obtain ⟨rfl, rfl⟩ := he
      exact cmpM_ok.2 ⟨⟨sa, .eq⟩, hF.swap ha hb hx, .inr ⟨rfl, _, hG.swap ha hb hy, rfl⟩⟩
  trans ha hb hc := by
    intro h1 h2
    rcases lex_le_cases h1 with ⟨s1, hab⟩ | ⟨⟨s1, hab⟩, gab⟩ <;>
      rcases lex_le_cases h2 with ⟨s2, hbc⟩ | ⟨⟨s2, hbc⟩, gbc⟩
    · obtain ⟨s, hac⟩ := hF.lt_of_lt_le ha hb hc hab (le_ok hbc (by decide))
      exact le_ok (cmpM_ok.2 ⟨_, hac, .inl ⟨by simp, rfl⟩⟩) (by decide)
    · obtain ⟨s, hac⟩ := hF.lt_of_lt_le ha hb hc hab (le_ok hbc (by decide))
      exact le_ok (cmpM_ok.2 ⟨_, hac, .inl ⟨by simp, rfl⟩⟩) (by decide)
    · obtain ⟨s, hac⟩ := hF.lt_of_le_lt ha hb hc (le_ok hab (by decide)) hbc
      exact le_ok (cmpM_ok.2 ⟨_, hac, .inl ⟨by simp, rfl⟩⟩) (by decide)
    · obtain ⟨s, hac⟩ := hF.eq_trans ha hb hc hab hbc
      obtain ⟨s3, o3, gac, hne⟩ := hG.trans ha hb hc gab gbc
      exact le_ok (cmpM_ok.2 ⟨_, hac, .inr ⟨rfl, _, gac, rfl⟩⟩) hne

/-- The lexicographic product in the constant case's form (`lexIf`). -/
theorem lexIf (hF : PreOn S F) (hG : PreOn S G) :
    PreOn S (fun a b => Canon.lexIf (F a b) (G a b)) where
  swap ha hb := by
    intro s o h
    obtain ⟨a, hx, (⟨hne, he⟩ | ⟨heq, hy⟩)⟩ := lexIf_ok.1 h
    · subst he
      refine lexIf_ok.2 ⟨⟨s, o.swap⟩, hF.swap ha hb hx, .inl ⟨?_, rfl⟩⟩
      cases o <;> simp_all [Ordering.swap]
    · obtain ⟨sa, oa⟩ := a
      simp only at heq
      subst heq
      exact lexIf_ok.2 ⟨⟨sa, .eq⟩, hF.swap ha hb hx, .inr ⟨rfl, hG.swap ha hb hy⟩⟩
  trans ha hb hc := by
    intro h1 h2
    rcases lexIf_le_cases h1 with ⟨s1, hab⟩ | ⟨⟨s1, hab⟩, gab⟩ <;>
      rcases lexIf_le_cases h2 with ⟨s2, hbc⟩ | ⟨⟨s2, hbc⟩, gbc⟩
    · obtain ⟨s, hac⟩ := hF.lt_of_lt_le ha hb hc hab (le_ok hbc (by decide))
      exact le_ok (lexIf_ok.2 ⟨_, hac, .inl ⟨by simp, rfl⟩⟩) (by decide)
    · obtain ⟨s, hac⟩ := hF.lt_of_lt_le ha hb hc hab (le_ok hbc (by decide))
      exact le_ok (lexIf_ok.2 ⟨_, hac, .inl ⟨by simp, rfl⟩⟩) (by decide)
    · obtain ⟨s, hac⟩ := hF.lt_of_le_lt ha hb hc (le_ok hab (by decide)) hbc
      exact le_ok (lexIf_ok.2 ⟨_, hac, .inl ⟨by simp, rfl⟩⟩) (by decide)
    · obtain ⟨s, hac⟩ := hF.eq_trans ha hb hc hab hbc
      obtain ⟨s3, o3, gac, hne⟩ := hG.trans ha hb hc gab gbc
      exact le_ok (lexIf_ok.2 ⟨_, hac, .inr ⟨rfl, gac⟩⟩) hne

/-- Dispatch on a tag: points of different tags compare by tag, strongly; points of one
tag by a preorder of that tag. -/
theorem ofTag (τ : α → Nat)
    (hdiff : ∀ a b, S a → S b → τ a ≠ τ b → F a b = .ok ⟨true, compare (τ a) (τ b)⟩)
    (hsame : ∀ T, PreOn (fun a => S a ∧ τ a = T) F) : PreOn S F where
  swap {a b} ha hb := by
    intro s o h
    by_cases ht : τ a = τ b
    · exact (hsame _).swap ⟨ha, rfl⟩ ⟨hb, ht.symm⟩ h
    · rw [hdiff _ _ ha hb ht] at h
      simp only [Except.ok.injEq, SOrder.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hdiff _ _ hb ha (Ne.symm ht)]
      simp only [Except.ok.injEq, SOrder.mk.injEq, true_and]
      exact (Std.OrientedCmp.eq_swap (cmp := (compare : Nat → Nat → Ordering)))
  trans := by
    intro a b c ha hb hc h1 h2
    -- `≤` across tags forces the tags to be ordered
    have tle : ∀ {x y}, S x → S y → Le (F x y) → τ x ≤ τ y := by
      intro x y hx hy hle
      by_cases ht : τ x = τ y
      · exact Nat.le_of_eq ht
      · obtain ⟨s, o, h, hne⟩ := hle
        rw [hdiff _ _ hx hy ht] at h
        simp only [Except.ok.injEq, SOrder.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have : ¬ τ y < τ x := fun hl => hne (Nat.compare_eq_gt.2 hl)
        omega
    have t1 := tle ha hb h1
    have t2 := tle hb hc h2
    by_cases h13 : τ a = τ c
    · have h12 : τ b = τ a := by omega
      have h23 : τ c = τ a := by omega
      exact (hsame (τ a)).trans ⟨ha, rfl⟩ ⟨hb, h12⟩ ⟨hc, h23⟩ h1 h2
    · rw [hdiff _ _ ha hc h13]
      refine ⟨true, _, rfl, ?_⟩
      intro hg; rw [Nat.compare_eq_gt] at hg; omega

/-- Points outside `good` make every comparison fail; it suffices to prove the preorder on
the good points. -/
theorem ofGood (good : α → Prop)
    (hbad : ∀ a b, S a → S b → (¬ good a ∨ ¬ good b) → ∀ x, F a b ≠ .ok x)
    (h : PreOn (fun a => S a ∧ good a) F) : PreOn S F where
  swap {a b} ha hb := by
    intro s o hab
    by_cases ga : good a
    · by_cases gb : good b
      · exact h.swap ⟨ha, ga⟩ ⟨hb, gb⟩ hab
      · exact absurd hab (hbad _ _ ha hb (.inr gb) _)
    · exact absurd hab (hbad _ _ ha hb (.inl ga) _)
  trans {a b c} ha hb hc := by
    intro h1 h2
    obtain ⟨x1, e1⟩ := h1.ok
    obtain ⟨x2, e2⟩ := h2.ok
    have ga : good a := Classical.byContradiction fun g => hbad _ _ ha hb (.inl g) _ e1
    have gb : good b := Classical.byContradiction fun g => hbad _ _ ha hb (.inr g) _ e1
    have gc : good c := Classical.byContradiction fun g => hbad _ _ hb hc (.inr g) _ e2
    exact h.trans ⟨ha, ga⟩ ⟨hb, gb⟩ ⟨hc, gc⟩ h1 h2

end PreOn

/-! ## Lists: `SOrder.zipM` -/

theorem zipM_cons {β : Type v} (f : β → β → Except ε SOrder) (x y : β) (xs ys : List β) :
    SOrder.zipM f (x :: xs) (y :: ys) = SOrder.cmpM (f x y) (SOrder.zipM f xs ys) := by
  simp only [SOrder.zipM]
  cases f x y with
  | error e => simp [SOrder.cmpM, bind, Except.bind]
  | ok a =>
    obtain ⟨sa, oa⟩ := a
    cases sa <;> cases oa <;> simp [SOrder.cmpM, bind, Except.bind, pure, Except.pure]

theorem zipM_nil_nil {β : Type v} (f : β → β → Except ε SOrder) :
    SOrder.zipM f [] [] = .ok ⟨true, .eq⟩ := rfl

theorem zipM_nil_cons {β : Type v} (f : β → β → Except ε SOrder) (y : β) (ys : List β) :
    SOrder.zipM f [] (y :: ys) = .ok ⟨true, .lt⟩ := rfl

theorem zipM_cons_nil {β : Type v} (f : β → β → Except ε SOrder) (x : β) (xs : List β) :
    SOrder.zipM f (x :: xs) [] = .ok ⟨true, .gt⟩ := rfl

/-- Lexicographic comparison of lists (shorter first) of points, each list carrying a
context `γ` that the element comparison reads (the level-parameter list of its side). -/
def zipCtx {γ : Type w} {β : Type v} (F : γ × β → γ × β → Except ε SOrder)
    (a b : γ × List β) : Except ε SOrder :=
  SOrder.zipM (fun u v => F (a.1, u) (b.1, v)) a.2 b.2

theorem PreOn.zipCtx {γ : Type w} {β : Type v} {S : γ × β → Prop}
    {F : γ × β → γ × β → Except ε SOrder} (hF : PreOn S F) :
    PreOn (fun a : γ × List β => ∀ u ∈ a.2, S (a.1, u)) (Canon.zipCtx F) := by
  -- induction on a bound of the list lengths
  suffices h : ∀ n, PreOn (fun a : γ × List β => (∀ u ∈ a.2, S (a.1, u)) ∧ a.2.length < n)
      (Canon.zipCtx F) by
    constructor
    · intro a b ha hb
      exact (h (a.2.length + b.2.length + 1)).swap ⟨ha, by omega⟩ ⟨hb, by omega⟩
    · intro a b c ha hb hc
      exact (h (a.2.length + b.2.length + c.2.length + 1)).trans
        ⟨ha, by omega⟩ ⟨hb, by omega⟩ ⟨hc, by omega⟩
  intro n
  induction n with
  | zero => exact ⟨fun ha => absurd ha.2 (by omega), fun ha => absurd ha.2 (by omega)⟩
  | succ n ih =>
    refine PreOn.ofTag (fun a => if a.2.isEmpty then 0 else 1) ?_ ?_
    · rintro ⟨g, xs⟩ ⟨g', ys⟩ - - ht
      cases xs <;> cases ys <;> simp_all [Canon.zipCtx, zipM_nil_cons, zipM_cons_nil] <;> rfl
    · intro T
      by_cases hT : T = 0
      · subst hT
        refine (PreOn.const_eq (S := fun a : γ × List β =>
          ((∀ u ∈ a.2, S (a.1, u)) ∧ a.2.length < n + 1) ∧
            (if a.2.isEmpty then 0 else 1) = 0) true).congr ?_
        rintro ⟨g, xs⟩ ⟨g', ys⟩ ⟨-, hx⟩ ⟨-, hy⟩
        cases xs <;> cases ys <;> simp_all [Canon.zipCtx, zipM_nil_nil, pure, Except.pure]
      · -- every point is a cons: head, then tail
        by_cases hne : Nonempty β
        · obtain ⟨d⟩ := hne
          have hhd : PreOn (fun a : γ × List β => ((∀ u ∈ a.2, S (a.1, u)) ∧ a.2.length < n + 1) ∧
              (if a.2.isEmpty then 0 else 1) = T)
              (fun a b => F (a.1, a.2.headD d) (b.1, b.2.headD d)) :=
            hF.comap (fun a : γ × List β => (a.1, a.2.headD d)) (by
              rintro ⟨g, xs⟩ ⟨⟨hm, -⟩, ht⟩
              cases xs with
              | nil => simp at ht; exact absurd ht.symm hT
              | cons x xs => exact hm x (by simp))
          have htl : PreOn (fun a : γ × List β => ((∀ u ∈ a.2, S (a.1, u)) ∧ a.2.length < n + 1) ∧
              (if a.2.isEmpty then 0 else 1) = T)
              (fun a b => Canon.zipCtx F (a.1, a.2.tail) (b.1, b.2.tail)) :=
            ih.comap (fun a : γ × List β => (a.1, a.2.tail)) (by
              rintro ⟨g, xs⟩ ⟨⟨hm, hl⟩, ht⟩
              cases xs with
              | nil => simp at ht; exact absurd ht.symm hT
              | cons x xs =>
                refine ⟨fun u hu => hm u (by simp at hu ⊢; exact .inr hu), ?_⟩
                simp at hl ⊢; omega)
          refine (hhd.cmpM htl).congr ?_
          rintro ⟨g, xs⟩ ⟨g', ys⟩ ⟨-, hx⟩ ⟨-, hy⟩
          cases xs with
          | nil => simp at hx; exact absurd hx.symm hT
          | cons x xs =>
            cases ys with
            | nil => simp at hy; exact absurd hy.symm hT
            | cons y ys => simp [Canon.zipCtx, zipM_cons]
        · have hno : ∀ a : γ × List β, ¬ (((∀ u ∈ a.2, S (a.1, u)) ∧ a.2.length < n + 1) ∧
              (if a.2.isEmpty then 0 else 1) = T) := by
            rintro ⟨g, xs⟩ ⟨-, ht⟩
            cases xs with
            | nil => simp at ht; exact hT ht.symm
            | cons x xs => exact hne ⟨x⟩
          constructor
          · intro a b ha; exact absurd ha (hno a)
          · intro a b c ha; exact absurd ha (hno a)

end Ix.CompileCert.Canon
