import IxCC.Anf.Proof.Spec.Basic

/-! # P4: value trees reproduce what they describe

At a call site the specialiser describes each masked argument by a value
tree over the caller's definitions (`tree`, `trees`, `siteTrees`). Every
operand a tree describes ends up **covered** (`Covered`): a literal or □
(reproduced as itself), a level that becomes a hole (an extra parameter), a
level the prologue rebuilds (`needed`), or a level known to hold a literal.
Every rebuilt level's own operands are covered in turn (`NeedOk`: a
constructor's fields, a local function's free variables), hole sources read
levels in scope (`TreesOk`), and every unmasked parameter has a hole
(`siteTrees_ok`). -/

set_option autoImplicit false

namespace IxCC.Anf.Specialize.Proof

/-! ## Association lists -/

theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · next he =>
      cases h
      simp only [beq_iff_eq] at he
      subst he
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem lookup_of_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β}, (l.map (·.1)).Nodup →
    (a, b) ∈ l → l.lookup a = some b
  | [], _, _, _, h => by simp at h
  | (k, v) :: l, a, b, hn, h => by
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [List.lookup]
    rcases List.mem_cons.1 h with e | hm
    · cases e; simp
    · have hne : a ≠ k := fun e => hn.1 (by subst e; exact List.mem_map.2 ⟨(a, b), hm, rfl⟩)
      have : (a == k) = false := by simp [hne]
      rw [this]
      exact lookup_of_mem hn.2 hm

theorem lookup_isSome_of_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β}, (a, b) ∈ l →
    (l.lookup a).isSome
  | [], _, _, h => by simp at h
  | (k, v) :: l, a, b, h => by
    simp only [List.lookup]
    split
    · rfl
    · next he =>
      rcases List.mem_cons.1 h with e | h
      · cases e; simp at he
      · exact lookup_isSome_of_mem h

theorem lookup_none {β : Type} : ∀ {l : List (Nat × β)} {a : Nat}, (∀ b, (a, b) ∉ l) → l.lookup a = none
  | [], _, _ => rfl
  | (k, v) :: l, a, h => by
    simp only [List.lookup]
    have hne : a ≠ k := fun e => h v (by subst e; exact List.mem_cons_self)
    have : (a == k) = false := by simp [hne]
    rw [this]
    exact lookup_none fun b hb => h b (List.mem_cons_of_mem _ hb)

/-! ## Covered operands and the trees' invariant -/

/-- A caller operand the specialisation reproduces: a literal or □ (as
itself), a level that is a hole or is rebuilt, or a level known to hold a
literal. -/
def Covered (defs : Src.NatMap Def) (t : Trees) : Opd → Prop
  | .lvl l => (∃ h, (l, h) ∈ t.levelHoles) ∨ l ∈ t.needed ∨ ∃ n, defs.get? l = some (.lit n)
  | _ => True

/-- What a rebuilt level needs: its constructor's fields, or its local
function's free variables, covered. -/
def NeedOk (defs : Src.NatMap Def) (t : Trees) (l : Nat) : Prop :=
  match defs.get? l with
  | some (.con _ fs) => ∀ o ∈ fs, Covered defs t o
  | some (.fn df ps b _) => ∀ j ∈ b.free ps.length, j < df → Covered defs t (.lvl (df - 1 - j))
  | _ => True

/-- Trees grow. -/
structure Ext (t t' : Trees) : Prop where
  holes : t.holes <+: t'.holes
  lh : ∀ p ∈ t.levelHoles, p ∈ t'.levelHoles
  need : ∀ l ∈ t.needed, l ∈ t'.needed

/-- The trees' invariant at caller depth `d`, except for the needs of the
levels in `E` (being described). -/
structure TreesOk (defs : Src.NatMap Def) (d np : Nat) (E : List Nat) (t : Trees) : Prop where
  lh : ∀ (l h : Nat), (l, h) ∈ t.levelHoles → t.holes[h]? = some (.level l)
  lvl : ∀ (k l : Nat), t.holes[k]? = some (.level l) → l < d
  needLt : ∀ l ∈ t.needed, l < d
  need : ∀ l ∈ t.needed, l ∉ E → NeedOk defs t l
  param : ∀ (h i : Nat), t.holes[h]? = some (.param i) → i < np
  atom : ∀ (h : Nat) (o : Opd), t.holes[h]? = some (.atom o) → InRange d o

variable {defs : Src.NatMap Def} {d np : Nat}

theorem Ext.refl (t : Trees) : Ext t t := ⟨List.prefix_refl _, fun _ h => h, fun _ h => h⟩

theorem Ext.trans {t₁ t₂ t₃ : Trees} (h₁ : Ext t₁ t₂) (h₂ : Ext t₂ t₃) : Ext t₁ t₃ :=
  ⟨h₁.holes.trans h₂.holes, fun p hp => h₂.lh p (h₁.lh p hp), fun l hl => h₂.need l (h₁.need l hl)⟩

theorem Covered.mono {t t' : Trees} (he : Ext t t') : ∀ {o : Opd}, Covered defs t o → Covered defs t' o
  | .lvl _, .inl ⟨h, hm⟩ => .inl ⟨h, he.lh _ hm⟩
  | .lvl _, .inr (.inl hm) => .inr (.inl (he.need _ hm))
  | .lvl _, .inr (.inr hn) => .inr (.inr hn)
  | .lit _, _ => trivial
  | .box, _ => trivial

theorem NeedOk.mono {t t' : Trees} (he : Ext t t') {l : Nat} (h : NeedOk defs t l) : NeedOk defs t' l := by
  unfold NeedOk at h ⊢
  split
  · next fs hl => rw [hl] at h; exact fun o ho => (h o ho).mono he
  · next df ps b _ hl => rw [hl] at h; exact fun j hj hjd => (h j hj hjd).mono he
  · trivial

theorem holes_get_of_prefix {t t' : Trees} (he : t.holes <+: t'.holes) {h : Nat} {s : HoleSrc}
    (hs : t.holes[h]? = some s) : t'.holes[h]? = some s := by
  obtain ⟨u, hu⟩ := he
  rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hs).1]
  exact hs

/-- A tree whose holes and rebuilt levels grew keeps its invariant when
nothing new needs anything. -/
theorem TreesOk.weaken {E E' : List Nat} {t : Trees} (h : TreesOk defs d np E t) (hE : ∀ l ∈ E, l ∈ E') :
    TreesOk defs d np E' t :=
  ⟨h.lh, h.lvl, h.needLt, fun l hl hn => h.need l hl fun he => hn (hE l he), h.param, h.atom⟩

/-! ## Holes and rebuilt levels -/

theorem hole_eq (t : Trees) (s : HoleSrc) :
    t.hole s = ({ holes := t.holes ++ [s], levelHoles := t.levelHoles, needed := t.needed }, t.holes.length) :=
  rfl

/-- The holes after appending one: the old ones, then the new one. -/
theorem holes_append_get {hs : List HoleSrc} {s s' : HoleSrc} {k : Nat} (h : (hs ++ [s])[k]? = some s') :
    hs[k]? = some s' ∨ s' = s := by
  by_cases hkl : k < hs.length
  · rw [List.getElem?_append_left hkl] at h; exact .inl h
  · rw [List.getElem?_append_right (by omega)] at h
    have hk0 : k - hs.length = 0 := by
      rcases Nat.lt_or_ge (k - hs.length) 1 with h1 | h1
      · omega
      · rw [List.getElem?_eq_none (by simp; omega)] at h; cases h
    rw [hk0] at h
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact .inr h.symm

theorem hole_ok {E : List Nat} {t : Trees} {s : HoleSrc} (hs : ∀ l, s = .level l → l < d)
    (hp : ∀ i, s = .param i → i < np) (ha : ∀ o, s = .atom o → InRange d o) (ht : TreesOk defs d np E t)
    {t' : Trees} {h : Nat}
    (heq : t.hole s = (t', h)) :
    TreesOk defs d np E t' ∧ Ext t t' ∧ t'.holes[h]? = some s := by
  rw [hole_eq] at heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hext : Ext t { holes := t.holes ++ [s], levelHoles := t.levelHoles, needed := t.needed } :=
    ⟨List.prefix_append _ _, fun _ h => h, fun _ h => h⟩
  refine ⟨⟨fun l h hm => holes_get_of_prefix hext.holes (ht.lh l h hm), fun k l hk => ?_, ht.needLt,
    fun l hl hn => (ht.need l hl hn).mono hext, fun k i hk => ?_, fun k o hk => ?_⟩, hext, by simp⟩
  · rcases holes_append_get hk with hk | hk
    · exact ht.lvl k l hk
    · exact hs l hk.symm
  · rcases holes_append_get hk with hk | hk
    · exact ht.param k i hk
    · exact hp i hk.symm
  · rcases holes_append_get hk with hk | hk
    · exact ht.atom k o hk
    · exact ha o hk.symm

theorem levelHole_ok {E : List Nat} {t : Trees} {l : Nat} (hl : l < d) (ht : TreesOk defs d np E t)
    {t' : Trees} {h : Nat} (heq : t.levelHole l = (t', h)) :
    TreesOk defs d np E t' ∧ Ext t t' ∧ (l, h) ∈ t'.levelHoles := by
  rw [Trees.levelHole.eq_1] at heq
  split at heq
  · next h' hlk =>
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨ht, Ext.refl _, lookup_mem hlk⟩
  · next hlk =>
    cases hh : t.hole (.level l) with
    | mk t1 h1 =>
      rw [hh] at heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨ht1, he1, hget⟩ := hole_ok (fun l' e => by cases e; exact hl) (by intro _ e; cases e) (by intro _ e; cases e) ht hh
      have hext : Ext t1 { holes := t1.holes, levelHoles := t1.levelHoles ++ [(l, h1)], needed := t1.needed } :=
        ⟨List.prefix_refl _, fun p hp => List.mem_append_left _ hp, fun _ h => h⟩
      refine ⟨⟨fun l' h' hm => ?_, ht1.lvl, ht1.needLt, fun l' hl' hn => (ht1.need l' hl' hn).mono hext, ht1.param, ht1.atom⟩,
        he1.trans hext, List.mem_append_right _ List.mem_cons_self⟩
      rcases List.mem_append.1 hm with hm | hm
      · exact ht1.lh l' h' hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact hget

theorem need_ok {E : List Nat} {t : Trees} {l : Nat} (hl : l < d) (ht : TreesOk defs d np E t) :
    TreesOk defs d np (l :: E) (t.need l) ∧ Ext t (t.need l) ∧ l ∈ (t.need l).needed := by
  unfold Trees.need
  split
  · next hc =>
    exact ⟨ht.weaken fun _ h => List.mem_cons_of_mem _ h, Ext.refl _, List.contains_iff_mem.1 hc⟩
  · have hext : Ext t { holes := t.holes, levelHoles := t.levelHoles, needed := t.needed ++ [l] } :=
      ⟨List.prefix_refl _, fun _ h => h, fun _ h => List.mem_append_left _ h⟩
    refine ⟨⟨ht.lh, ht.lvl, fun l' hl' => ?_, fun l' hl' hn => ?_, ht.param, ht.atom⟩, hext, List.mem_append_right _ List.mem_cons_self⟩
    · rcases List.mem_append.1 hl' with h | h
      · exact ht.needLt l' h
      · rw [List.mem_singleton.1 h]; exact hl
    · rcases List.mem_append.1 hl' with h | h
      · exact (ht.need l' h fun he => hn (List.mem_cons_of_mem _ he)).mono hext
      · exact absurd (List.mem_cons.2 (.inl (List.mem_singleton.1 h))) hn

theorem holeOf_ok {E : List Nat} {t : Trees} {o : Opd} (ho : InRange d o) (ht : TreesOk defs d np E t)
    {t' : Trees} {k : Key.ArgKey} (heq : t.holeOf o = (t', k)) :
    TreesOk defs d np E t' ∧ Ext t t' ∧ Covered defs t' o := by
  cases o with
  | lvl l =>
    rw [Trees.holeOf.eq_1] at heq
    cases hh : t.levelHole l with
    | mk t1 h1 =>
      rw [hh] at heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      obtain ⟨ht1, he1, hm⟩ := levelHole_ok ho ht hh
      exact ⟨ht1, he1, .inl ⟨h1, hm⟩⟩
  | lit l =>
    simp only [Trees.holeOf] at heq
    cases hh : t.hole (.atom (.lit l)) with
    | mk t1 h1 =>
      rw [hh] at heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      obtain ⟨ht1, he1, -⟩ := hole_ok (by intro _ e; cases e) (by intro _ e; cases e) (fun _ e => by cases e; trivial) ht hh
      exact ⟨ht1, he1, trivial⟩
  | box =>
    simp only [Trees.holeOf] at heq
    cases hh : t.hole (.atom .box) with
    | mk t1 h1 =>
      rw [hh] at heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      obtain ⟨ht1, he1, -⟩ := hole_ok (by intro _ e; cases e) (by intro _ e; cases e) (fun _ e => by cases e; trivial) ht hh
      exact ⟨ht1, he1, trivial⟩

theorem holesOf_ok {E : List Nat} : ∀ {os : List Opd} {t : Trees}, (∀ o ∈ os, InRange d o) →
    TreesOk defs d np E t → ∀ {t' : Trees} {ks : List Key.ArgKey}, t.holesOf os = (t', ks) →
    TreesOk defs d np E t' ∧ Ext t t' ∧ ∀ o ∈ os, Covered defs t' o
  | [], t, _, ht, t', ks, heq => by
    simp only [Trees.holesOf, Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact ⟨ht, Ext.refl _, fun _ h => by simp at h⟩
  | o :: os, t, hr, ht, t', ks, heq => by
    rw [Trees.holesOf.eq_2] at heq
    cases h1 : t.holeOf o with
    | mk t1 k1 =>
      rw [h1] at heq
      dsimp only at heq
      cases h2 : t1.holesOf os with
      | mk t2 ks2 =>
        rw [h2] at heq
        dsimp only at heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        obtain ⟨ht1, he1, hc1⟩ := holeOf_ok (hr o List.mem_cons_self) ht h1
        obtain ⟨ht2, he2, hc2⟩ := holesOf_ok (fun o' h => hr o' (List.mem_cons_of_mem _ h)) ht1 h2
        refine ⟨ht2, he1.trans he2, fun o' h => ?_⟩
        rcases List.mem_cons.1 h with rfl | h
        · exact hc1.mono he2
        · exact hc2 o' h

/-! ## Trees -/

section

variable {P : Program} {ρ : List Val} (hD : DefsOk P defs ρ) (fkey : Key.GKey) (inv : Nat)
include hD

mutual

theorem tree_ok : ∀ (fuel : Nat) {E : List Nat} {t : Trees} {o : Opd}, InRange ρ.length o →
    TreesOk defs ρ.length np E t → ∀ {t' : Trees} {k : Key.ArgKey}, tree P defs fkey inv fuel t o = (t', k) →
    TreesOk defs ρ.length np E t' ∧ Ext t t' ∧ Covered defs t' o
  | 0, _, _, _, ho, ht, _, _, heq => by
    rw [tree.eq_1] at heq
    exact holeOf_ok ho ht heq
  | fuel + 1, E, t, o, ho, ht, t', k, heq => by
    cases o with
    | lit l =>
      cases l with
      | nat n =>
        rw [tree.eq_2] at heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        exact ⟨ht, Ext.refl _, trivial⟩
      | str s =>
        rw [tree.eq_4] at heq
        exact holeOf_ok ho ht heq
    | box =>
      rw [tree.eq_5] at heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      exact ⟨ht, Ext.refl _, trivial⟩
    | lvl l =>
      have hl : l < ρ.length := ho
      rw [tree.eq_3] at heq
      split at heq
      · -- a constructor: its fields
        next c fs hdl =>
        obtain ⟨hlt, -⟩ := hD l _ hdl
        obtain ⟨ht1, he1, hm1⟩ := need_ok hl ht
        cases h2 : trees P defs fkey inv fuel (t.need l) fs with
        | mk t2 ks =>
          rw [h2] at heq
          dsimp only at heq
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, -⟩ := heq
          have hr : ∀ o ∈ fs, InRange ρ.length o := fun o hof => by
            cases o with
            | lvl j => exact Nat.lt_trans (hlt j hof) hl
            | lit _ => trivial
            | box => trivial
          obtain ⟨ht2, he2, hc2⟩ := trees_ok fuel hr ht1 h2
          have hneed : NeedOk defs t2 l := by unfold NeedOk; rw [hdl]; exact hc2
          refine ⟨⟨ht2.lh, ht2.lvl, ht2.needLt, fun l' hl' hn => ?_, ht2.param, ht2.atom⟩, he1.trans he2,
            .inr (.inl (he2.need l hm1))⟩
          by_cases he : l' = l
          · subst he; exact hneed
          · exact ht2.need l' hl' fun h => by
              rcases List.mem_cons.1 h with h | h
              · exact he h
              · exact hn h
      · -- a literal
        next n hdl =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        exact ⟨ht, Ext.refl _, .inr (.inr ⟨n, hdl⟩)⟩
      · -- a function global
        next g hdl =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        obtain ⟨ht1, he1, hm1⟩ := need_ok hl ht
        refine ⟨⟨ht1.lh, ht1.lvl, ht1.needLt, fun l' hl' hn => ?_, ht1.param, ht1.atom⟩, he1, .inr (.inl hm1)⟩
        by_cases he : l' = l
        · subst he; unfold NeedOk; rw [hdl]; trivial
        · exact ht1.need l' hl' fun h => by
            rcases List.mem_cons.1 h with h | h
            · exact he h
            · exact hn h
      · -- a local function: its free variables
        next df ps b idx hdl =>
        obtain ⟨hle, -⟩ := hD l _ hdl
        dsimp only at heq
        obtain ⟨ht1, he1, hm1⟩ := need_ok hl ht
        cases h2 : trees P defs fkey inv fuel (t.need l)
            ((dedup (b.free ps.length)).map fun j => Opd.lvl (df - 1 - j)) with
        | mk t2 ks =>
          rw [h2] at heq
          dsimp only at heq
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, -⟩ := heq
          have hr : ∀ o ∈ (dedup (b.free ps.length)).map (fun j => Opd.lvl (df - 1 - j)), InRange ρ.length o :=
            fun o hof => by
              obtain ⟨j, -, rfl⟩ := List.mem_map.1 hof
              show df - 1 - j < ρ.length
              omega
          obtain ⟨ht2, he2, hc2⟩ := trees_ok fuel hr ht1 h2
          have hneed : NeedOk defs t2 l := by
            unfold NeedOk; rw [hdl]
            exact fun j hj _ => hc2 _ (List.mem_map.2 ⟨j, mem_dedup.2 hj, rfl⟩)
          refine ⟨⟨ht2.lh, ht2.lvl, ht2.needLt, fun l' hl' hn => ?_, ht2.param, ht2.atom⟩, he1.trans he2,
            .inr (.inl (he2.need l hm1))⟩
          by_cases he : l' = l
          · subst he; exact hneed
          · exact ht2.need l' hl' fun h => by
              rcases List.mem_cons.1 h with h | h
              · exact he h
              · exact hn h
      · exact holeOf_ok ho ht heq

theorem trees_ok : ∀ (fuel : Nat) {E : List Nat} {t : Trees} {os : List Opd}, (∀ o ∈ os, InRange ρ.length o) →
    TreesOk defs ρ.length np E t → ∀ {t' : Trees} {ks : List Key.ArgKey},
    trees P defs fkey inv fuel t os = (t', ks) →
    TreesOk defs ρ.length np E t' ∧ Ext t t' ∧ ∀ o ∈ os, Covered defs t' o
  | 0, _, _, _, hr, ht, _, _, heq => by
    rw [trees.eq_1] at heq
    exact holesOf_ok hr ht heq
  | fuel + 1, _, _, [], _, ht, _, _, heq => by
    rw [trees.eq_2 _ _ _ _ _ _ (by omega)] at heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact ⟨ht, Ext.refl _, fun _ h => by simp at h⟩
  | fuel + 1, E, t, o :: os, hr, ht, t', ks, heq => by
    rw [trees.eq_3] at heq
    cases h1 : tree P defs fkey inv fuel t o with
    | mk t1 k1 =>
      rw [h1] at heq
      dsimp only at heq
      cases h2 : trees P defs fkey inv fuel t1 os with
      | mk t2 ks2 =>
        rw [h2] at heq
        dsimp only at heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, -⟩ := heq
        obtain ⟨ht1, he1, hc1⟩ := tree_ok fuel (hr o List.mem_cons_self) ht h1
        obtain ⟨ht2, he2, hc2⟩ := trees_ok fuel (fun o' h => hr o' (List.mem_cons_of_mem _ h)) ht1 h2
        refine ⟨ht2, he1.trans he2, fun o' h => ?_⟩
        rcases List.mem_cons.1 h with rfl | h
        · exact hc1.mono he2
        · exact hc2 o' h

end

/-! ## A site's trees -/

/-- What a site's fold keeps: the trees' invariant, its roots are covered and
are the masked items done so far, and every unmasked item done has a hole. -/
structure SiteInv (t : Trees) (roots : List (Nat × Opd)) (done : List ((Opd × Nat) × Bool)) : Prop where
  trees : TreesOk defs ρ.length np [] t
  cov : ∀ p ∈ roots, Covered defs t p.2
  roots : roots = (done.filter (·.2)).map fun x => (x.1.2, x.1.1)
  params : ∀ x ∈ done, x.2 = false → ∃ h : Nat, t.holes[h]? = some (HoleSrc.param x.1.2)

theorem siteStep_fold : ∀ (xs : List ((Opd × Nat) × Bool)) {t : Trees} {ks : List Key.ArgKey}
    {roots : List (Nat × Opd)} {done : List ((Opd × Nat) × Bool)},
    (∀ x ∈ xs, InRange ρ.length x.1.1 ∧ x.1.2 < np) → SiteInv (np := np) (defs := defs) (ρ := ρ) t roots done →
    ∀ {t' : Trees} {ks' : List Key.ArgKey} {roots' : List (Nat × Opd)},
    xs.foldl (siteStep P defs fkey inv) (t, ks, roots) = (t', ks', roots') →
    SiteInv (np := np) (defs := defs) (ρ := ρ) t' roots' (done ++ xs)
  | [], t, ks, roots, done, _, hi, t', ks', roots', h => by
    simp only [List.foldl_nil, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    simpa using hi
  | ((o, i), m) :: xs, t, ks, roots, done, hxs, hi, t', ks', roots', h => by
    rw [List.foldl_cons] at h
    have hx := hxs ((o, i), m) List.mem_cons_self
    have hrest : ∀ x ∈ xs, InRange ρ.length x.1.1 ∧ x.1.2 < np := fun x hx => hxs x (List.mem_cons_of_mem _ hx)
    rw [show done ++ ((o, i), m) :: xs = (done ++ [((o, i), m)]) ++ xs by simp]
    unfold siteStep at h
    dsimp only at h
    cases m with
    | true =>
      simp only [if_true] at h
      cases ht : tree P defs fkey inv (4 * P.size + 1024) t o with
      | mk t1 k =>
        rw [ht] at h
        dsimp only at h
        obtain ⟨ht1, he1, hc1⟩ := tree_ok hD fkey inv _ hx.1 hi.trees ht
        refine siteStep_fold xs hrest ⟨ht1, fun p hp => ?_, ?_, fun x hx' hf => ?_⟩ h
        · rcases List.mem_append.1 hp with hp | hp
          · exact (hi.cov p hp).mono he1
          · rw [List.mem_singleton.1 hp]; exact hc1
        · rw [hi.roots]; simp
        · rcases List.mem_append.1 hx' with hx' | hx'
          · obtain ⟨h, hh⟩ := hi.params x hx' hf
            exact ⟨h, holes_get_of_prefix he1.holes hh⟩
          · rw [List.mem_singleton.1 hx'] at hf; cases hf
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      cases hh : t.hole (.param i) with
      | mk t1 h1 =>
        rw [hh] at h
        dsimp only at h
        obtain ⟨ht1, he1, hg1⟩ := hole_ok (by intro _ e; cases e) (fun _ e => by cases e; exact hx.2) (by intro _ e; cases e) hi.trees hh
        refine siteStep_fold xs hrest ⟨ht1, fun p hp => (hi.cov p hp).mono he1, ?_, fun x hx' hf => ?_⟩ h
        · rw [hi.roots]; simp
        · rcases List.mem_append.1 hx' with hx' | hx'
          · obtain ⟨h, hh⟩ := hi.params x hx' hf
            exact ⟨h, holes_get_of_prefix he1.holes hh⟩
          · rw [List.mem_singleton.1 hx']; exact ⟨h1, hg1⟩

omit hD in
/-- The items of a site: each argument's operand, its index and its mask
bit. -/
theorem siteItems_get {d : Nat} {mask : List Bool} {as : List Atom} {x : (Opd × Nat) × Bool} {j : Nat}
    (h : ((as.map (·.opd d)).zipIdx.zip mask)[j]? = some x) :
    ∃ a, as[j]? = some a ∧ mask[j]? = some x.2 ∧ x.1 = (a.opd d, j) := by
  rw [List.getElem?_zip_eq_some, List.getElem?_zipIdx] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨o, ho, he⟩ := Option.map_eq_some_iff.1 h1
  rw [List.getElem?_map] at ho
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 ho
  exact ⟨a, ha, h2, by rw [← he]; simp⟩

omit hD in
theorem siteItems_keys {d : Nat} {mask : List Bool} {as : List Atom} :
    (((as.map (·.opd d)).zipIdx.zip mask).map (·.1.2)).Nodup := by
  have : ((as.map (·.opd d)).zipIdx.zip mask).map (·.1.2) =
      List.range (((as.map (·.opd d)).zipIdx.zip mask).length) := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map]
    by_cases hj : j < ((as.map (·.opd d)).zipIdx.zip mask).length
    · rw [List.getElem?_range hj]
      cases hx : ((as.map (·.opd d)).zipIdx.zip mask)[j]? with
      | none => rw [List.getElem?_eq_none_iff] at hx; omega
      | some x =>
        obtain ⟨a, -, -, he⟩ := siteItems_get hx
        simp [he]
    · have h1 : ((as.map (·.opd d)).zipIdx.zip mask)[j]? = none := List.getElem?_eq_none (by omega)
      have h2 : (List.range ((as.map (·.opd d)).zipIdx.zip mask).length)[j]? = none :=
        List.getElem?_eq_none (by rw [List.length_range]; omega)
      rw [h1, h2]; rfl
  rw [this]; exact List.nodup_range

/-- A site's trees: the invariant, holes for the unmasked arguments, and
the masked arguments' operands as roots, covered. -/
theorem siteTrees_ok {mask : List Bool} {as : List Atom} {vs : List Val} (hvs : evalAtoms ρ as = some vs)
    {t : Trees} {keys : List Key.ArgKey} {roots : List (Nat × Opd)}
    (h : siteTrees P defs fkey inv ρ.length mask as = (t, keys, roots)) :
    TreesOk defs ρ.length as.length [] t ∧
    (∀ i o, roots.lookup i = some o → Covered defs t o ∧ InRange ρ.length o ∧
      ∃ a, as[i]? = some a ∧ mask[i]? = some true ∧ o = a.opd ρ.length) ∧
    (∀ i a, as[i]? = some a → mask[i]? = some true → roots.lookup i = some (a.opd ρ.length)) ∧
    (∀ (i : Nat) (a : Atom), as[i]? = some a → mask[i]? = some false → ∃ h : Nat, t.holes[h]? = some (HoleSrc.param i)) := by
  unfold siteTrees at h
  have hitems : ∀ x ∈ (as.map (·.opd ρ.length)).zipIdx.zip mask, InRange ρ.length x.1.1 ∧ x.1.2 < as.length := by
    intro x hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨a, ha, -, he⟩ := siteItems_get (d := ρ.length) (mask := mask) (as := as) hj
    rw [he]
    refine ⟨?_, (List.getElem?_eq_some_iff.1 ha).1⟩
    obtain ⟨v, hv⟩ := evalAtoms_get hvs ha
    exact inRange_of_val (atom_opd_val hv.1)
  have hinv := siteStep_fold hD fkey inv (np := as.length) _ hitems
    (t := {}) (ks := []) (roots := []) (done := [])
    ⟨⟨fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩, fun _ h => by simp at h, rfl, fun _ h => by simp at h⟩ h
  simp only [List.nil_append] at hinv
  have hnd : (roots.map (·.1)).Nodup := by
    rw [hinv.roots, List.map_map]
    exact (List.Sublist.map _ List.filter_sublist).nodup siteItems_keys
  refine ⟨hinv.trees, fun i o hl => ?_, fun i a ha hm => ?_, fun i a ha hm => ?_⟩
  · have hm := lookup_mem hl
    refine ⟨hinv.cov _ hm, ?_⟩
    rw [hinv.roots] at hm
    obtain ⟨x, hx, he⟩ := List.mem_map.1 hm
    obtain ⟨hx, hx2⟩ := List.mem_filter.1 hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨a, ha, hmj, hx1⟩ := siteItems_get (d := ρ.length) (mask := mask) (as := as) hj
    simp only [Prod.mk.injEq] at he
    rw [hx1] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨(hitems x (List.mem_of_getElem? hj)).1 |> fun h => by rw [hx1] at h; exact h, a, ha, ?_, rfl⟩
    rw [hmj, hx2]
  · apply lookup_of_mem hnd
    rw [hinv.roots]
    refine List.mem_map.2 ⟨((a.opd ρ.length, i), true), List.mem_filter.2 ⟨?_, rfl⟩, rfl⟩
    refine List.mem_iff_getElem?.2 ⟨i, ?_⟩
    rw [List.getElem?_zip_eq_some, List.getElem?_zipIdx, List.getElem?_map, ha]
    exact ⟨by simp, hm⟩
  · refine hinv.params ((a.opd ρ.length, i), false) (List.mem_iff_getElem?.2 ⟨i, ?_⟩) rfl
    rw [List.getElem?_zip_eq_some, List.getElem?_zipIdx, List.getElem?_map, ha]
    exact ⟨by simp, hm⟩

end

end IxCC.Anf.Specialize.Proof
