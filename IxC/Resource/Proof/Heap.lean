import IxC.Resource.Statement

/-!
# Concrete Heap, Value, Taint, and Ownership Lemmas

Core invariants and framing lemmas for `IxC.Resource.Eval` (`runR`), shared by
both `DefaultOk` and the full `ModeOk → Safe` (F4) soundness proof.
-/

namespace IxC.Resource.Proof

open IxC.Resource Ixon

/-! ## 1. `natUnion`, `taints`, `addTaint`, `renameTaint` -/

theorem mem_natUnion {a b : List Nat} {x : Nat} :
    x ∈ natUnion a b ↔ x ∈ a ∨ x ∈ b := by
  unfold natUnion
  induction b generalizing a with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hy : a.contains y = true
    · have hyMem : y ∈ a := by simpa using hy
      simp only [hy, ↓reduceIte]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hyMem
        · exact Or.inr h
    · simp only [hy, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr h

theorem natUnion_subset_iff {a b c : List Nat} :
    (∀ x ∈ natUnion a b, x ∈ c) ↔ (∀ x ∈ a, x ∈ c) ∧ (∀ x ∈ b, x ∈ c) := by
  simp only [mem_natUnion]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨ha, hb⟩ x (hx | hx)
    · exact ha x hx
    · exact hb x hx

theorem mem_foldl_taints {init : List Nat} {vs : List Val} {s : Nat} :
    s ∈ vs.foldl (fun t v => natUnion t v.taint) init ↔
      s ∈ init ∨ ∃ v ∈ vs, s ∈ v.taint := by
  induction vs generalizing init with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, mem_natUnion]
    constructor
    · rintro ((h | h) | ⟨w, hw, hsw⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, Or.inl rfl, h⟩
      · exact Or.inr ⟨w, Or.inr hw, hsw⟩
    · rintro (h | ⟨w, rfl | hw, hsw⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr hsw)
      · exact Or.inr ⟨w, hw, hsw⟩

theorem mem_taints {vs : List Val} {s : Nat} :
    s ∈ taints vs ↔ ∃ v ∈ vs, s ∈ v.taint := by
  unfold taints
  rw [mem_foldl_taints]
  simp

theorem taint_addTaint_imm (s : Nat) (i : Imm) :
    (addTaint s (.imm i)).taint = [] := rfl

theorem mem_taint_addTaint_ref {s loc cap : Nat} {t : List Nat} {r : Nat} :
    r ∈ (addTaint s (.ref loc cap t)).taint ↔ r = s ∨ r ∈ t := by
  dsimp only [addTaint, Val.taint]
  cases hc : t.contains s with
  | true =>
    have hs : s ∈ t := by simpa using hc
    simp only [↓reduceIte]
    constructor
    · exact Or.inr
    · rintro (rfl | h); exact hs; exact h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]

theorem mem_taint_addTaint {s : Nat} {v : Val} {r : Nat} :
    r ∈ (addTaint s v).taint → r = s ∨ r ∈ v.taint := by
  cases v with
  | imm i => simp [addTaint, Val.taint]
  | ref l c t => exact mem_taint_addTaint_ref.mp

theorem mem_taint_foldl_addTaint {ts : List Nat} {v : Val} {r : Nat} :
    r ∈ (ts.foldl (fun v s => addTaint s v) v).taint → r ∈ ts ∨ r ∈ v.taint := by
  induction ts generalizing v with
  | nil => intro h; exact Or.inr h
  | cons s ss ih =>
    intro h
    simp only [List.foldl_cons] at h
    rcases ih h with hss | hv
    · exact Or.inl (List.mem_cons_of_mem _ hss)
    · rcases mem_taint_addTaint hv with rfl | hvt
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inr hvt

theorem foldl_addTaint_imm (ts : List Nat) (i : Imm) :
    ts.foldl (fun v s => addTaint s v) (.imm i) = .imm i := by
  induction ts with
  | nil => rfl
  | cons s ss ih => simpa [addTaint] using ih

theorem foldl_addTaint_ref (ts : List Nat) (loc cap : Nat) (tv : List Nat) :
    ∃ tv', ts.foldl (fun v s => addTaint s v) (.ref loc cap tv) = .ref loc cap tv' := by
  induction ts generalizing tv with
  | nil => exact ⟨tv, rfl⟩
  | cons s ss ih =>
    simp only [List.foldl_cons, addTaint]
    exact ih _

theorem mem_taint_renameTaint {s cur : Nat} {v : Val} {r : Nat} :
    r ∈ (renameTaint s cur v).taint →
      (r ≠ s ∧ r ∈ v.taint) ∨ (r = cur ∧ cur ≠ 0 ∧ s ∈ v.taint) := by
  cases v with
  | imm i => simp [renameTaint, Val.taint]
  | ref l c t =>
    dsimp only [renameTaint]
    cases hhas : t.contains s with
    | true =>
      have hs : s ∈ t := by simpa using hhas
      simp only [↓reduceIte]
      cases hcond : (cur == 0 || (t.filter (· != s)).contains cur) with
      | true =>
        simp only [↓reduceIte, Val.taint, List.mem_filter, bne_iff_ne, ne_eq]
        rintro ⟨hrt, hrne⟩
        exact Or.inl ⟨hrne, hrt⟩
      | false =>
        have hcur0 : cur ≠ 0 := by
          intro hc0
          simp [hc0] at hcond
        simp only [Bool.false_eq_true, ↓reduceIte, Val.taint, List.mem_cons,
          List.mem_filter, bne_iff_ne, ne_eq]
        rintro (rfl | ⟨hrt, hrne⟩)
        · exact Or.inr ⟨rfl, hcur0, hs⟩
        · exact Or.inl ⟨hrne, hrt⟩
    | false =>
      have hns : s ∉ t := by simpa using hhas
      simp only [Bool.false_eq_true, ↓reduceIte, Val.taint]
      intro hrt
      exact Or.inl ⟨fun h => hns (h ▸ hrt), hrt⟩

theorem confinedTo_eq_true {s : Nat} {v : Val} :
    confinedTo s v = true ↔ s ∈ v.taint := by
  unfold confinedTo
  simp

theorem confinedTo_eq_false {s : Nat} {v : Val} :
    confinedTo s v = false ↔ s ∉ v.taint := by
  unfold confinedTo
  simp

/-! ## 2. `collect` and `termSpine` (`CollectTotal`) -/

theorem collect_ne_app : ∀ (t : Term) (acc : List Term) (f a : Term) (c : Cls),
    (collect t acc).1 ≠ .app f a c
  | .app f' a' _, acc, f, a, c => collect_ne_app f' (a' :: acc) f a c
  | .irr, _, _, _, _ | .var .., _, _, _, _ | .const .., _, _, _, _
  | .lam .., _, _, _, _ | .letE .., _, _, _, _ | .case .., _, _, _, _
  | .natLit _, _, _, _, _ | .strLit _, _, _, _, _ | .proj .., _, _, _, _ => by
    simp [collect]

theorem collect_acc : ∀ (t : Term) (acc : List Term),
    collect t acc = ((collect t []).1, (collect t []).2 ++ acc)
  | .app f a _, acc => by
    simp only [collect]
    rw [collect_acc f (a :: acc), collect_acc f [a]]
    simp [List.append_assoc]
  | .irr, _ | .var .., _ | .const .., _ | .lam .., _ | .letE .., _
  | .case .., _ | .natLit _, _ | .strLit _, _ | .proj .., _ => by
    simp [collect]

theorem termSpine_eq_collect : ∀ (t : Term),
    (termSpine t).1 = (collect t []).1 ∧ (termSpine t).2.toList = (collect t []).2
  | .app f a _ => by
    have ih := termSpine_eq_collect f
    simp only [termSpine, collect]
    rw [collect_acc f [a]]
    simp [ih.1, ih.2]
  | .irr | .var .. | .const .. | .lam .. | .letE ..
  | .case .. | .natLit _ | .strLit _ | .proj .. => by
    simp [termSpine, collect]

/-! ## 3. `Skel.admits`, `Skel.admitsNA`, and `Skel.isDefault` -/

theorem Skel.admits_and_admitsNA_refl (s : Skel) :
    s.admits s = true ∧ s.admitsNA s = true := by
  induction s with
  | data | unknown => exact ⟨rfl, rfl⟩
  | dataApp f a ihf iha =>
    simp [Skel.admits, Skel.admitsNA, ihf.1, ihf.2, iha.1, iha.2]
  | arrow i d r c ihd ihc =>
    constructor
    · simp only [Skel.admits, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
      constructor
      · split
        · exact ihd.2
        · exact ihd.1
      · split
        · exact ihc.2
        · exact ihc.1
    · simp only [Skel.admitsNA, beq_self_eq_true, Bool.true_and, ihc.2, Bool.and_true]
      split
      · exact ihd.2
      · exact ihd.1

theorem Skel.admits_refl (s : Skel) : s.admits s = true :=
  (Skel.admits_and_admitsNA_refl s).1

theorem Skel.admitsNA_refl (s : Skel) : s.admitsNA s = true :=
  (Skel.admits_and_admitsNA_refl s).2

theorem Skel.admits_and_admitsNA_symm (s₁ s₂ : Skel) :
    s₁.admits s₂ = s₂.admits s₁ ∧ s₁.admitsNA s₂ = s₂.admitsNA s₁ := by
  induction s₁ generalizing s₂ with
  | unknown =>
    cases s₂ <;> exact ⟨rfl, rfl⟩
  | data =>
    cases s₂ <;> simp [Skel.admits, Skel.admitsNA, Skel.isDefault]
  | dataApp f a ihf iha =>
    cases s₂ with
    | dataApp g b =>
      simp [Skel.admits, Skel.admitsNA, (ihf g).1, (ihf g).2, (iha b).1, (iha b).2]
    | unknown => exact ⟨rfl, rfl⟩
    | data => simp [Skel.admits, Skel.admitsNA, Skel.isDefault]
    | arrow _ _ _ _ => exact ⟨rfl, rfl⟩
  | arrow i d r c ihd ihc =>
    cases s₂ with
    | arrow i' d' r' c' =>
      have hbi : (i == i') = (i' == i) := by cases i <;> cases i' <;> rfl
      have hbr : (r == r') = (r' == r) := by cases r <;> cases r' <;> rfl
      constructor
      · simp only [Skel.admits]
        by_cases hi : i = i'
        · subst hi
          simp only [beq_self_eq_true, Bool.true_and, hbr, (ihd d').1, (ihd d').2, (ihc c').1, (ihc c').2]
        · have hf1 : (i == i') = false := beq_false_of_ne hi
          have hf2 : (i' == i) = false := beq_false_of_ne (Ne.symm hi)
          simp [hf1, hf2]
      · simp only [Skel.admitsNA]
        by_cases hi : i = i'
        · subst hi
          simp only [beq_self_eq_true, Bool.true_and, hbr, (ihd d').1, (ihd d').2, (ihc c').2]
        · have hf1 : (i == i') = false := beq_false_of_ne hi
          have hf2 : (i' == i) = false := beq_false_of_ne (Ne.symm hi)
          simp [hf1, hf2]
    | unknown => exact ⟨rfl, rfl⟩
    | data => exact ⟨rfl, rfl⟩
    | dataApp _ _ => exact ⟨rfl, rfl⟩

theorem Skel.admits_symm (s₁ s₂ : Skel) : s₁.admits s₂ = s₂.admits s₁ :=
  (Skel.admits_and_admitsNA_symm s₁ s₂).1

theorem Skel.admitsNA_symm (s₁ s₂ : Skel) : s₁.admitsNA s₂ = s₂.admitsNA s₁ :=
  (Skel.admits_and_admitsNA_symm s₁ s₂).2

theorem Skel.admitsNA_to_admits {s₁ s₂ : Skel} (h : s₁.admitsNA s₂ = true) :
    s₁.admits s₂ = true := by
  induction s₁ generalizing s₂ with
  | unknown =>
    cases s₂ with
    | unknown | data => rfl
    | dataApp _ _ => simpa [Skel.admitsNA, Skel.admits] using h
    | arrow _ _ _ _ => simp [Skel.admitsNA] at h
  | data =>
    cases s₂ with
    | unknown | data => rfl
    | dataApp _ _ => simpa [Skel.admitsNA, Skel.admits] using h
    | arrow _ _ _ _ => simp [Skel.admitsNA] at h
  | dataApp f a ihf iha =>
    cases s₂ with
    | dataApp g b =>
      simp only [Skel.admitsNA, Skel.admits, Bool.and_eq_true] at h ⊢
      exact ⟨ihf h.1, iha h.2⟩
    | unknown => simpa [Skel.admitsNA, Skel.admits] using h
    | data => simpa [Skel.admitsNA, Skel.admits] using h
    | arrow _ _ _ _ => simp [Skel.admitsNA] at h
  | arrow i d r c ihd ihc =>
    cases s₂ with
    | arrow i' d' r' c' =>
      simp only [Skel.admitsNA, Skel.admits, Bool.and_eq_true] at h ⊢
      refine ⟨⟨h.1.1, h.1.2⟩, ?_⟩
      split
      · exact h.2
      · exact ihc h.2
    | unknown | data | dataApp _ _ =>
      simp [Skel.admitsNA] at h

theorem Skel.admits_and_admitsNA_default_left {s₁ s₂ : Skel} (hd : s₁.isDefault = true) :
    (s₁.admits s₂ = true → s₂.isDefault = true) ∧
    (s₁.admitsNA s₂ = true → s₂.isDefault = true) := by
  induction s₁ generalizing s₂ with
  | unknown =>
    constructor
    · intro ha; simpa [Skel.admits] using ha
    · intro ha
      cases s₂ with
      | unknown | data => rfl
      | dataApp _ _ => simpa [Skel.admitsNA] using ha
      | arrow _ _ _ _ => simp [Skel.admitsNA] at ha
  | data =>
    constructor
    · intro ha
      cases s₂ with
      | unknown | data => rfl
      | dataApp _ _ => simpa [Skel.admits, Skel.isDefault] using ha
      | arrow _ _ _ _ => simp [Skel.admits] at ha
    · intro ha
      cases s₂ with
      | unknown | data => rfl
      | dataApp _ _ => simpa [Skel.admitsNA, Skel.isDefault] using ha
      | arrow _ _ _ _ => simp [Skel.admitsNA] at ha
  | dataApp f a ihf iha =>
    simp only [Skel.isDefault, Bool.and_eq_true] at hd
    constructor
    · intro ha
      cases s₂ with
      | unknown | data => rfl
      | dataApp g b =>
        simp only [Skel.admits, Bool.and_eq_true] at ha
        simp [Skel.isDefault, (ihf hd.1).1 ha.1, (iha hd.2).1 ha.2]
      | arrow _ _ _ _ => simp [Skel.admits] at ha
    · intro ha
      cases s₂ with
      | unknown | data => rfl
      | dataApp g b =>
        simp only [Skel.admitsNA, Bool.and_eq_true] at ha
        simp [Skel.isDefault, (ihf hd.1).2 ha.1, (iha hd.2).2 ha.2]
      | arrow _ _ _ _ => simp [Skel.admitsNA] at ha
  | arrow i d r c ihd ihc =>
    simp only [Skel.isDefault, Bool.and_eq_true, beq_iff_eq] at hd
    rcases hd with ⟨⟨⟨rfl, rfl⟩, hdd⟩, hdc⟩
    constructor
    · intro ha
      cases s₂ with
      | unknown => rfl
      | data | dataApp _ _ => simp [Skel.admits] at ha
      | arrow i' d' r' c' =>
        simp only [Skel.admits, Bool.and_eq_true, beq_iff_eq] at ha
        rcases ha with ⟨⟨⟨rfl, rfl⟩, had⟩, hac⟩
        simp [Skel.isDefault, (ihd hdd).1 had, (ihc hdc).1 hac]
    · intro ha
      cases s₂ with
      | unknown | data | dataApp _ _ => simp [Skel.admitsNA] at ha
      | arrow i' d' r' c' =>
        simp only [Skel.admitsNA, Bool.and_eq_true, beq_iff_eq] at ha
        rcases ha with ⟨⟨⟨rfl, rfl⟩, had⟩, hac⟩
        simp [Skel.isDefault, (ihd hdd).1 had, (ihc hdc).2 hac]

theorem Skel.admits_default_left {s₁ s₂ : Skel} (hd : s₁.isDefault = true)
    (ha : s₁.admits s₂ = true) : s₂.isDefault = true :=
  (Skel.admits_and_admitsNA_default_left hd).1 ha

theorem Skel.admits_default_right {s₁ s₂ : Skel} (hd : s₂.isDefault = true)
    (ha : s₁.admits s₂ = true) : s₁.isDefault = true := by
  rw [Skel.admits_symm] at ha
  exact Skel.admits_default_left hd ha

theorem Skel.admitsNA_default_left {s₁ s₂ : Skel} (hd : s₁.isDefault = true)
    (ha : s₁.admitsNA s₂ = true) : s₂.isDefault = true :=
  (Skel.admits_and_admitsNA_default_left hd).2 ha

theorem Skel.admitsNA_default_right {s₁ s₂ : Skel} (hd : s₂.isDefault = true)
    (ha : s₁.admitsNA s₂ = true) : s₁.isDefault = true := by
  rw [Skel.admitsNA_symm] at ha
  exact Skel.admitsNA_default_left hd ha

theorem Skel.isDefault_ifaceSkel {ps : List Param} {r : ResultMode} {cod : Skel}
    (hps : ∀ p ∈ ps, p.mode = .many ∧ p.skel.isDefault = true)
    (hr : r = .shared) (hcod : cod.isDefault = true) :
    (ifaceSkel ps r cod).isDefault = true := by
  induction ps with
  | nil => exact hcod
  | cons p ps ih =>
    cases ps with
    | nil =>
      have hp := hps p (List.mem_cons_self ..)
      simp [ifaceSkel, Skel.isDefault, hp.1, hp.2, hr, hcod]
    | cons p2 ps' =>
      have hp := hps p (List.mem_cons_self ..)
      have hrest := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      simp [ifaceSkel, Skel.isDefault, hp.1, hp.2, hrest]

/-! ## 4. `Reach`, `HeldBy`, `OwnReach`, `Cell` slots & values -/

theorem Reach.step_trans {h : Heap} {v w : Val} {l₁ l₂ : Nat} {o₁ : Obj}
    (h1 : Reach h v l₁) (ho : h.objs[l₁]? = some o₁) (hmem : w ∈ o₁.cell.vals)
    (h2 : Reach h w l₂) : Reach h v l₂ := by
  induction h1 with
  | here => exact .step ho hmem h2
  | step ho' hm' _ ih => exact .step ho' hm' (ih ho)

/-- Value `w` is held inside `v` (either `w = v`, or `w` sits in `o.cell.vals` of some cell
reachable from `v`). -/
def HeldBy (h : Heap) (v w : Val) : Prop :=
  w = v ∨ ∃ l o, Reach h v l ∧ h.objs[l]? = some o ∧ w ∈ o.cell.vals

theorem HeldBy.refl (h : Heap) (v : Val) : HeldBy h v v := Or.inl rfl

theorem HeldBy.trans {h : Heap} {a b c : Val} (h1 : HeldBy h a b) (h2 : HeldBy h b c) :
    HeldBy h a c := by
  rcases h1 with rfl | ⟨l1, o1, hr1, ho1, hm1⟩
  · exact h2
  · rcases h2 with rfl | ⟨l2, o2, hr2, ho2, hm2⟩
    · exact Or.inr ⟨l1, o1, hr1, ho1, hm1⟩
    · exact Or.inr ⟨l2, o2, Reach.step_trans hr1 ho1 hm1 hr2, ho2, hm2⟩

theorem Reach_of_HeldBy {h : Heap} {a b : Val} {l : Nat}
    (hb : HeldBy h a b) (hr : Reach h b l) : Reach h a l := by
  rcases hb with rfl | ⟨l1, o1, hr1, ho1, hm1⟩
  · exact hr
  · exact Reach.step_trans hr1 ho1 hm1 hr

theorem HeldBy_of_mem_vals {h : Heap} {loc cap : Nat} {t : List Nat} {o : Obj} {w : Val}
    (ho : h.objs[loc]? = some o) (hmem : w ∈ o.cell.vals) :
    HeldBy h (.ref loc cap t) w :=
  Or.inr ⟨loc, o, .here, ho, hmem⟩

theorem HeldBy_ref_taint {h : Heap} {loc cap : Nat} {t1 t2 : List Nat} {w : Val}
    (hw : HeldBy h (.ref loc cap t1) w) :
    w = .ref loc cap t1 ∨ HeldBy h (.ref loc cap t2) w := by
  rcases hw with rfl | ⟨l, o, hr, ho, hm⟩
  · exact Or.inl rfl
  · refine Or.inr (Or.inr ⟨l, o, ?_, ho, hm⟩)
    cases hr with
    | here => exact .here
    | step ho' hm' hr' => exact .step ho' hm' hr'

theorem Reach_ref_taint {h : Heap} {loc cap1 cap2 : Nat} {t1 t2 : List Nat} {l : Nat} :
    Reach h (.ref loc cap1 t1) l ↔ Reach h (.ref loc cap2 t2) l := by
  constructor <;> (intro hr; cases hr with | here => exact .here | step ho hm h' => exact .step ho hm h')

theorem mem_vals_of_ownedSlot {P : Prog} {c : Cell} {i : Nat} {w : Val}
    (hi : i ∈ ownedSlots P c) (hs : c.slot? i = some w) : w ∈ c.vals := by
  cases c with
  | ctor r fs =>
    simp only [Cell.slot?, Cell.vals] at hs ⊢
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs)
  | clo env p res rc fvs body =>
    simp only [ownedSlots, Cell.slot?, Cell.vals] at hi hs ⊢
    exact List.mem_filterMap.mpr ⟨i, hi, hs⟩
  | pap r as =>
    simp only [Cell.slot?, Cell.vals] at hs ⊢
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs)
  | once t sp =>
    simp only [ownedSlots, List.mem_singleton] at hi
    subst hi
    simp only [Cell.slot?, Option.some.injEq] at hs
    subst hs
    simp [Cell.vals]
  | num n => simp [ownedSlots] at hi
  | str s => simp [ownedSlots] at hi

theorem OwnReach_toReach {P : Prog} {h : Heap} {v : Val} {l : Nat}
    (hr : OwnReach P h v l) : Reach h v l := by
  induction hr with
  | here => exact .here
  | step ho hi hs _ ih => exact .step ho (mem_vals_of_ownedSlot hi hs) ih

theorem OwnReach_ref_taint {P : Prog} {h : Heap} {loc cap1 cap2 : Nat} {t1 t2 : List Nat} {l : Nat} :
    OwnReach P h (.ref loc cap1 t1) l ↔ OwnReach P h (.ref loc cap2 t2) l := by
  constructor <;> (
    intro hr
    cases hr with
    | here ho hn => exact .here ho hn
    | step ho hi hs h' => exact .step ho hi hs h')

theorem OwnReach_step_trans {P : Prog} {h : Heap} {v sv : Val} {l₁ l₂ i : Nat} {o₁ : Obj}
    (h1 : OwnReach P h v l₁) (ho : h.objs[l₁]? = some o₁)
    (hi : i ∈ ownedSlots P o₁.cell) (hs : o₁.cell.slot? i = some sv)
    (h2 : OwnReach P h sv l₂) : OwnReach P h v l₂ := by
  induction h1 with
  | here => exact .step ho hi hs h2
  | step ho' hi' hs' _ ih => exact .step ho' hi' hs' (ih ho)

theorem OwnReach_nonNum {P : Prog} {h : Heap} {v : Val} {l : Nat}
    (hr : OwnReach P h v l) :
    ∃ o, h.objs[l]? = some o ∧ (o.cell.isNum = false ∨ natClass ≠ .leaf) := by
  induction hr with
  | here ho hn => exact ⟨_, ho, hn⟩
  | step _ _ _ _ ih => exact ih

theorem setBnd_length (env : List Bnd) (i : Nat) (v : Val) :
    (setBnd env i v).length = env.length := by
  induction env generalizing i with
  | nil => rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ n => simp [setBnd, ih]

theorem setBnd_getElem?_same {env : List Bnd} {i : Nat} {b : Bnd} {v : Val}
    (hb : env[i]? = some b) :
    (setBnd env i v)[i]? = some { b with val := v } := by
  induction env generalizing i with
  | nil => simp at hb
  | cons b0 bs ih =>
    cases i with
    | zero => simp at hb; subst hb; simp [setBnd]
    | succ n => simp [setBnd]; exact ih (by simpa using hb)

theorem setBnd_getElem?_other {env : List Bnd} {i j : Nat} {v : Val} (hne : j ≠ i) :
    (setBnd env i v)[j]? = env[j]? := by
  induction env generalizing i j with
  | nil => simp [setBnd]
  | cons b0 bs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ m => simp [setBnd]
    | succ n =>
      cases j with
      | zero => simp [setBnd]
      | succ m => simp [setBnd]; exact ih (fun h => hne (congrArg Nat.succ h))

theorem setSlot_isNum (c : Cell) (i : Nat) (v : Val) :
    (c.setSlot i v).isNum = c.isNum := by
  cases c <;> cases i <;> rfl

theorem setSlot_ownedSlots (P : Prog) (c : Cell) (i : Nat) (v : Val) :
    ownedSlots P (c.setSlot i v) = ownedSlots P c := by
  cases c with
  | ctor r fs => simp [Cell.setSlot, ownedSlots]
  | clo env p res rc fvs b => simp [Cell.setSlot, ownedSlots]
  | pap r as => simp [Cell.setSlot, ownedSlots]
  | once t sp => cases i <;> simp [Cell.setSlot, ownedSlots]
  | num n => rfl
  | str s => rfl

theorem setSlot_slot?_same {c : Cell} {i : Nat} {w v : Val}
    (hs : c.slot? i = some w) : (c.setSlot i v).slot? i = some v := by
  cases c with
  | ctor r fs =>
    simp only [Cell.slot?] at hs
    have hlt : i < fs.size := (Array.getElem?_eq_some_iff.mp hs).1
    simp [Cell.setSlot, Cell.slot?, Array.set!, hlt]
  | clo env p res rc fvs b =>
    simp only [Cell.slot?] at hs
    obtain ⟨bd, hbd, _⟩ := Option.map_eq_some_iff.mp hs
    simp [Cell.setSlot, Cell.slot?, setBnd_getElem?_same hbd]
  | pap r as =>
    simp only [Cell.slot?] at hs
    have hlt : i < as.size := (Array.getElem?_eq_some_iff.mp hs).1
    simp [Cell.setSlot, Cell.slot?, Array.set!, hlt]
  | once t sp =>
    cases i with
    | zero => simp [Cell.setSlot, Cell.slot?]
    | succ n => simp [Cell.slot?] at hs
  | num n => simp [Cell.slot?] at hs
  | str s => simp [Cell.slot?] at hs

theorem setSlot_slot?_other {c : Cell} {i j : Nat} {v : Val} (hne : j ≠ i) :
    (c.setSlot i v).slot? j = c.slot? j := by
  cases c with
  | ctor r fs =>
    simp only [Cell.setSlot, Cell.slot?, Array.set!]
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
  | clo env p res rc fvs b =>
    simp [Cell.setSlot, Cell.slot?, setBnd_getElem?_other hne]
  | pap r as =>
    simp only [Cell.setSlot, Cell.slot?, Array.set!]
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
  | once t sp =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ m => simp [Cell.setSlot, Cell.slot?]
    | succ n => simp [Cell.setSlot, Cell.slot?]
  | num n => rfl
  | str s => rfl

theorem mem_array_setIfInBounds {α : Type} {xs : Array α} {i : Nat} {v w : α}
    (h : w ∈ xs.setIfInBounds i v) : w = v ∨ w ∈ xs := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp h
  have hj' : j < xs.size := by simpa using hj
  by_cases hji : j = i
  · subst hji
    left
    simp [Array.getElem_setIfInBounds_self hj]
  · right
    rw [Array.getElem_setIfInBounds_ne hj' (Ne.symm hji)]
    exact Array.getElem_mem hj'

theorem mem_vals_setSlot_iff {c : Cell} {i : Nat} {v w : Val} :
    w ∈ (c.setSlot i v).vals → w = v ∨ w ∈ c.vals := by
  cases c with
  | ctor r fs =>
    intro h
    simp only [Cell.setSlot, Cell.vals, Array.set!, Array.mem_toList_iff] at h ⊢
    exact mem_array_setIfInBounds h
  | clo env p res rc fvs b =>
    intro h
    simp only [Cell.setSlot, Cell.vals, List.mem_filterMap] at h ⊢
    rcases h with ⟨k, hk, hget⟩
    by_cases hki : k = i
    · subst hki
      cases henv : env[k]? with
      | none =>
        have hlen := setBnd_length env k v
        have hge : env.length ≤ k := List.getElem?_eq_none_iff.mp henv
        have : (setBnd env k v)[k]? = none := List.getElem?_eq_none (by omega)
        simp [this] at hget
      | some bd =>
        rw [setBnd_getElem?_same henv] at hget
        simp at hget
        exact Or.inl hget.symm
    · rw [setBnd_getElem?_other hki] at hget
      exact Or.inr ⟨k, hk, hget⟩
  | pap r as =>
    intro h
    simp only [Cell.setSlot, Cell.vals, Array.set!, Array.mem_toList_iff] at h ⊢
    exact mem_array_setIfInBounds h
  | once t sp =>
    cases i with
    | zero =>
      simp only [Cell.setSlot, Cell.vals, List.mem_singleton]
      exact Or.inl
    | succ n =>
      simp only [Cell.setSlot, Cell.vals]
      exact Or.inr
  | num n => intro h; exact Or.inr h
  | str s => intro h; exact Or.inr h

/-! ## 5. Core Heap & Value Predicates -/

/-- A value is either an immediate or a reference whose cell exists with matching capability. -/
def LiveRef (h : Heap) : Val → Prop
  | .imm _ => True
  | .ref loc cap _ => ∃ o : Obj, h.objs[loc]? = some o ∧ o.cap = cap

theorem ValOk_iff_LiveRef_taint {h : Heap} {v : Val} :
    ValOk h v ↔ LiveRef h v ∧ v.taint = [] := by
  cases v <;> simp [ValOk, LiveRef, Val.taint, and_comm]

/-- Finalized L1 invariant: a number cell reference never carries any region taint. -/
def LeafUntainted (h : Heap) : Val → Prop
  | .imm _ => True
  | .ref loc _ t => ∀ (o : Obj) (n : Nat), h.objs[loc]? = some o → o.cell = .num n → t = []

/-- Value matches class `c` in heap `h` (with L1 `t = []` on `.leaf`). -/
def ClsOk (h : Heap) : Cls → Val → Prop
  | .irr, v => v = .imm .irr
  | .imm, v => ∃ i, v = .imm i
  | .leaf, v => ∃ (loc cap : Nat) (o : Obj) (n : Nat), v = .ref loc cap [] ∧ h.objs[loc]? = some o ∧ o.cell = .num n ∧ o.cap = cap
  | .val, _ => True

/-- Every cell's capability is strictly below `h.nextCap`. -/
def CapsOk (h : Heap) : Prop :=
  ∀ (loc : Nat) (o : Obj), h.objs[loc]? = some o → o.cap < h.nextCap

/-- Every value held by `v` (including `v` itself) is live and satisfies L1 `LeafUntainted`. -/
def DeepLive (h : Heap) (v : Val) : Prop :=
  ∀ w, HeldBy h v w → LiveRef h w ∧ LeafUntainted h w

/-- No cell reachable from `v` reaches itself. -/
def AcyclicFrom (h : Heap) (v : Val) : Prop :=
  ∀ (l : Nat) (o : Obj) (w : Val), Reach h v l → h.objs[l]? = some o → w ∈ o.cell.vals → ¬ Reach h w l

/-- Every currently open region in `v`'s taint is listed in `allowed`. -/
def OpenUnder (openRegs allowed : List Nat) (v : Val) : Prop :=
  ∀ r ∈ v.taint, r ∈ openRegs → r ∈ allowed

/-- Every value held by `v` (including `v` itself) has its open-region taint in `allowed`. -/
def DeepOpenUnder (h : Heap) (openRegs allowed : List Nat) (v : Val) : Prop :=
  ∀ w, HeldBy h v w → OpenUnder openRegs allowed w

/-- Ownership tree with non-owned-slot (`@shared` `.ctor` field) disjointness (alias for
`Statement.lean`'s `OwnTree`, which already includes both clauses). -/
abbrev OwnTreeFull (P : Prog) (h : Heap) (v : Val) : Prop :=
  OwnTree P h v

theorem DeepLive.self {h : Heap} {v : Val} (hd : DeepLive h v) :
    LiveRef h v ∧ LeafUntainted h v :=
  hd v (HeldBy.refl h v)

theorem DeepLive.sub {h : Heap} {v w : Val} (hd : DeepLive h v) (hw : HeldBy h v w) :
    DeepLive h w :=
  fun u hu => hd u (HeldBy.trans hw hu)

theorem DeepOpenUnder.self {h : Heap} {rs A : List Nat} {v : Val}
    (hd : DeepOpenUnder h rs A v) : OpenUnder rs A v :=
  hd v (HeldBy.refl h v)

theorem DeepOpenUnder.sub {h : Heap} {rs A : List Nat} {v w : Val}
    (hd : DeepOpenUnder h rs A v) (hw : HeldBy h v w) : DeepOpenUnder h rs A w :=
  fun u hu => hd u (HeldBy.trans hw hu)

theorem OpenUnder.mono {rs A B : List Nat} {v : Val}
    (h : OpenUnder rs A v) (hsub : ∀ x ∈ A, x ∈ B) : OpenUnder rs B v :=
  fun r hr hopen => hsub r (h r hr hopen)

theorem DeepOpenUnder.mono {h : Heap} {rs A B : List Nat} {v : Val}
    (hd : DeepOpenUnder h rs A v) (hsub : ∀ x ∈ A, x ∈ B) : DeepOpenUnder h rs B v :=
  fun w hw => (hd w hw).mono hsub

theorem OpenUnder.weaken_open {rs rs' A : List Nat} {v : Val}
    (h : OpenUnder rs A v) (hsub : ∀ x ∈ rs', x ∈ rs) : OpenUnder rs' A v :=
  fun r hr hopen => h r hr (hsub r hopen)

theorem DeepOpenUnder.weaken_open {h : Heap} {rs rs' A : List Nat} {v : Val}
    (hd : DeepOpenUnder h rs A v) (hsub : ∀ x ∈ rs', x ∈ rs) : DeepOpenUnder h rs' A v :=
  fun w hw => (hd w hw).weaken_open hsub

theorem OpenUnder.of_nil {rs A : List Nat} {v : Val} (ht : v.taint = []) :
    OpenUnder rs A v := by
  intro r hr; simp [ht] at hr

theorem OpenUnder.confinedTo_false {rs A : List Nat} {s : Nat} {v : Val}
    (h : OpenUnder rs A v) (hs : s ∈ rs) (hnot : s ∉ A) :
    confinedTo s v = false := by
  rw [confinedTo_eq_false]
  intro hmem
  exact hnot (h s hmem hs)

theorem OpenUnder.confinedOpen_false {rs : List Nat} {v : Val}
    (h : OpenUnder rs [] v) :
    v.taint.any (fun s => rs.contains s) = false := by
  rw [List.any_eq_false]
  intro s hs
  simp only [List.contains_eq_mem, decide_eq_true_eq]
  intro hopen
  exact List.not_mem_nil (h s hs hopen)

theorem AcyclicFrom.sub {h : Heap} {v w : Val} (ha : AcyclicFrom h v) (hw : HeldBy h v w) :
    AcyclicFrom h w :=
  fun l o u hrl ho hu => ha l o u (Reach_of_HeldBy hw hrl) ho hu

theorem OwnTreeFull.sub {P : Prog} {h : Heap} {v : Val} {loc cap : Nat} {t : List Nat}
    {o : Obj} {i : Nat} {sv : Val}
    (ht : OwnTreeFull P h v) (hv : v = .ref loc cap t)
    (ho : h.objs[loc]? = some o)
    (hi : i ∈ ownedSlots P o.cell) (hs : o.cell.slot? i = some sv) :
    OwnTreeFull P h sv := by
  subst hv
  have hstep : ∀ l, OwnReach P h sv l → OwnReach P h (.ref loc cap t) l :=
    fun l hl => .step ho hi hs hl
  constructor
  · intro p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁ hp₂ ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnl
    exact ht.1 p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ (hstep p₁ hp₁) (hstep p₂ hp₂)
      ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnl
  · intro p l j o' r fs w hp ho' hcell hj hs' hl
    exact ht.2 p l j o' r fs w (hstep p hp) ho' hcell hj hs' (hstep l hl)

/-! ## 6. Framing (`PreservesLocs`) -/

/-- Heap `h'` agrees with `h` on all locations satisfying `S`. -/
def PreservesLocs (S : Nat → Prop) (h h' : Heap) : Prop :=
  ∀ l, S l → h'.objs[l]? = h.objs[l]?

theorem PreservesLocs.mono {S₁ S₂ : Nat → Prop} {h h' : Heap}
    (hp : PreservesLocs S₂ h h') (hsub : ∀ l, S₁ l → S₂ l) :
    PreservesLocs S₁ h h' :=
  fun l hl => hp l (hsub l hl)

theorem PreservesLocs.refl (S : Nat → Prop) (h : Heap) : PreservesLocs S h h :=
  fun _ _ => rfl

theorem PreservesLocs.trans {S : Nat → Prop} {h₁ h₂ h₃ : Heap}
    (h12 : PreservesLocs S h₁ h₂) (h23 : PreservesLocs S h₂ h₃) :
    PreservesLocs S h₁ h₃ :=
  fun l hl => (h23 l hl).trans (h12 l hl)

theorem Reach_of_preserves {h h' : Heap} {v : Val} {l : Nat}
    (hp : PreservesLocs (Reach h v) h h') (hr : Reach h v l) : Reach h' v l := by
  induction hr with
  | here => exact .here
  | @step loc cap t o w l' ho hmem hr' ih =>
    have ho' : h'.objs[loc]? = some o := by rw [hp loc .here, ho]
    have hp' : PreservesLocs (Reach h w) h h' :=
      hp.mono (fun x hx => .step ho hmem hx)
    exact .step ho' hmem (ih hp')

theorem Reach_of_preserves_rev {h h' : Heap} {v : Val} {l : Nat}
    (hp : PreservesLocs (Reach h v) h h') (hr : Reach h' v l) : Reach h v l := by
  induction hr with
  | here => exact .here
  | @step loc cap t o w l' ho' hmem hr' ih =>
    have ho : h.objs[loc]? = some o := by rw [← hp loc .here, ho']
    have hp' : PreservesLocs (Reach h w) h h' :=
      hp.mono (fun x hx => .step ho hmem hx)
    exact .step ho hmem (ih hp')

theorem Reach_congr {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') (l : Nat) :
    Reach h' v l ↔ Reach h v l :=
  ⟨Reach_of_preserves_rev hp, Reach_of_preserves hp⟩

theorem HeldBy_congr {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') (w : Val) :
    HeldBy h' v w ↔ HeldBy h v w := by
  unfold HeldBy
  constructor
  · rintro (rfl | ⟨l, o, hr, ho', hm⟩)
    · exact Or.inl rfl
    · have hrl := (Reach_congr hp l).mp hr
      exact Or.inr ⟨l, o, hrl, (hp l hrl).symm.trans ho', hm⟩
  · rintro (rfl | ⟨l, o, hr, ho, hm⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨l, o, (Reach_congr hp l).mpr hr, (hp l hr).trans ho, hm⟩

theorem OwnReach_congr {P : Prog} {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') (l : Nat) :
    OwnReach P h' v l ↔ OwnReach P h v l := by
  constructor
  · intro hr
    induction hr with
    | @here loc cap t o ho' hn =>
      exact .here ((hp loc .here).symm.trans ho') hn
    | @step loc cap t o i w l' ho' hi hs _ ih =>
      have ho : h.objs[loc]? = some o := (hp loc .here).symm.trans ho'
      have hp' : PreservesLocs (Reach h w) h h' :=
        hp.mono (fun x hx => .step ho (mem_vals_of_ownedSlot hi hs) hx)
      exact .step ho hi hs (ih hp')
  · intro hr
    induction hr with
    | @here loc cap t o ho hn =>
      exact .here ((hp loc .here).trans ho) hn
    | @step loc cap t o i w l' ho hi hs _ ih =>
      have ho' : h'.objs[loc]? = some o := (hp loc .here).trans ho
      have hp' : PreservesLocs (Reach h w) h h' :=
        hp.mono (fun x hx => .step ho (mem_vals_of_ownedSlot hi hs) hx)
      exact .step ho' hi hs (ih hp')

theorem LiveRef_congr {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    LiveRef h' v ↔ LiveRef h v := by
  cases v with
  | imm _ => simp [LiveRef]
  | ref loc cap t => simp [LiveRef, hp loc .here]

theorem LeafUntainted_congr {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    LeafUntainted h' v ↔ LeafUntainted h v := by
  cases v with
  | imm _ => simp [LeafUntainted]
  | ref loc cap t => simp [LeafUntainted, hp loc .here]

theorem ClsOk_congr {h h' : Heap} {c : Cls} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    ClsOk h' c v ↔ ClsOk h c v := by
  cases c with
  | irr | imm | val => simp [ClsOk]
  | leaf =>
    cases v with
    | imm _ => simp [ClsOk]
    | ref loc cap t =>
      have hloc := hp loc .here
      simp only [ClsOk]
      constructor
      · rintro ⟨l, cap', o, n, heq, ho', hcell, hcap⟩
        cases heq
        exact ⟨loc, cap, o, n, rfl, hloc.symm.trans ho', hcell, hcap⟩
      · rintro ⟨l, cap', o, n, heq, ho, hcell, hcap⟩
        cases heq
        exact ⟨loc, cap, o, n, rfl, hloc.trans ho, hcell, hcap⟩

theorem DeepLive_congr {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    DeepLive h' v ↔ DeepLive h v := by
  unfold DeepLive
  constructor
  · intro hd w hw
    have hw' := (HeldBy_congr hp w).mpr hw
    have hp' := hp.mono (fun x hx => Reach_of_HeldBy hw hx)
    have ⟨hl, hlu⟩ := hd w hw'
    exact ⟨(LiveRef_congr hp').mp hl, (LeafUntainted_congr hp').mp hlu⟩
  · intro hd w hw'
    have hw := (HeldBy_congr hp w).mp hw'
    have hp' := hp.mono (fun x hx => Reach_of_HeldBy hw hx)
    have ⟨hl, hlu⟩ := hd w hw
    exact ⟨(LiveRef_congr hp').mpr hl, (LeafUntainted_congr hp').mpr hlu⟩

theorem DeepOpenUnder_congr {h h' : Heap} {rs A : List Nat} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    DeepOpenUnder h' rs A v ↔ DeepOpenUnder h rs A v := by
  unfold DeepOpenUnder
  constructor
  · intro hd w hw; exact hd w ((HeldBy_congr hp w).mpr hw)
  · intro hd w hw; exact hd w ((HeldBy_congr hp w).mp hw)

theorem AcyclicFrom_congr {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    AcyclicFrom h' v ↔ AcyclicFrom h v := by
  unfold AcyclicFrom
  constructor
  · intro ha l o w hrl ho hmem hwl
    have hrl' := (Reach_congr hp l).mpr hrl
    have ho' := (hp l hrl).trans ho
    have hp' := hp.mono (fun x hx => Reach.step_trans hrl ho hmem hx)
    exact ha l o w hrl' ho' hmem ((Reach_congr hp' l).mpr hwl)
  · intro ha l o w hrl' ho' hmem hwl'
    have hrl := (Reach_congr hp l).mp hrl'
    have ho := (hp l hrl).symm.trans ho'
    have hp' := hp.mono (fun x hx => Reach.step_trans hrl ho hmem hx)
    exact ha l o w hrl ho hmem ((Reach_congr hp' l).mp hwl')

theorem OwnTree_congr {P : Prog} {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    OwnTree P h' v ↔ OwnTree P h v := by
  unfold OwnTree
  apply and_congr
  · constructor
    · intro ht p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁ hp₂ ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnl
      have hnl' : ∀ o, h'.objs[l]? = some o → o.cell.isNum = false ∨ natClass ≠ .leaf := by
        intro o ho'
        have hrl : Reach h v l := Reach.step_trans (OwnReach_toReach hp₁) ho₁ (mem_vals_of_ownedSlot hi₁ hs₁) .here
        exact hnl o ((hp l hrl).symm.trans ho')
      exact ht p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂
        ((OwnReach_congr hp p₁).mpr hp₁) ((OwnReach_congr hp p₂).mpr hp₂)
        ((hp p₁ (OwnReach_toReach hp₁)).trans ho₁) ((hp p₂ (OwnReach_toReach hp₂)).trans ho₂)
        hi₁ hi₂ hs₁ hs₂ hnl'
    · intro ht p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁' hp₂' ho₁' ho₂' hi₁ hi₂ hs₁ hs₂ hnl'
      have hp₁ := (OwnReach_congr hp p₁).mp hp₁'
      have hp₂ := (OwnReach_congr hp p₂).mp hp₂'
      have ho₁ := (hp p₁ (OwnReach_toReach hp₁)).symm.trans ho₁'
      have ho₂ := (hp p₂ (OwnReach_toReach hp₂)).symm.trans ho₂'
      have hnl : ∀ o, h.objs[l]? = some o → o.cell.isNum = false ∨ natClass ≠ .leaf := by
        intro o ho
        have hrl : Reach h v l := Reach.step_trans (OwnReach_toReach hp₁) ho₁ (mem_vals_of_ownedSlot hi₁ hs₁) .here
        exact hnl' o ((hp l hrl).trans ho)
      exact ht p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁ hp₂ ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnl
  · constructor
    · intro hdis p l i o r fs w hrp ho hcell hi hs hrl hwl
      have hrp' := (OwnReach_congr hp p).mpr hrp
      have ho' := (hp p (OwnReach_toReach hrp)).trans ho
      have hrl' := (OwnReach_congr hp l).mpr hrl
      have hwmem : w ∈ o.cell.vals := by
        rw [hcell]; exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs)
      have hp' := hp.mono (fun x hx => Reach.step_trans (OwnReach_toReach hrp) ho hwmem hx)
      exact hdis p l i o r fs w hrp' ho' hcell hi hs hrl' ((Reach_congr hp' l).mpr hwl)
    · intro hdis p l i o r fs w hrp' ho' hcell hi hs hrl' hwl'
      have hrp := (OwnReach_congr hp p).mp hrp'
      have ho := (hp p (OwnReach_toReach hrp)).symm.trans ho'
      have hrl := (OwnReach_congr hp l).mp hrl'
      have hwmem : w ∈ o.cell.vals := by
        rw [hcell]; exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hs)
      have hp' := hp.mono (fun x hx => Reach.step_trans (OwnReach_toReach hrp) ho hwmem hx)
      exact hdis p l i o r fs w hrp ho hcell hi hs hrl ((Reach_congr hp' l).mp hwl')

theorem OwnTreeFull_congr {P : Prog} {h h' : Heap} {v : Val}
    (hp : PreservesLocs (Reach h v) h h') :
    OwnTreeFull P h' v ↔ OwnTreeFull P h v :=
  OwnTree_congr hp

/-! ## 7. Primitive `M` Operations -/

theorem M_pure_run {α : Type} (a : α) (st : St) :
    ((pure a : M α).run st) = .ok (a, st) := rfl

theorem M_bind_run {α β : Type} (m : M α) (f : α → M β) (st : St) :
    ((m >>= f).run st) =
      (match m.run st with
       | Except.ok (a, st') => (f a).run st'
       | Except.error e => Except.error e) := by
  change (m.run st).bind (fun p => (f p.1).run p.2) = _
  cases m.run st <;> rfl

theorem M_get_run (st : St) :
    ((get : M St).run st) = .ok (st, st) := rfl

theorem M_set_run (st' st : St) :
    ((set st' : M Unit).run st) = .ok ((), st') := rfl

theorem M_modify_run (f : St → St) (st : St) :
    ((modify f : M Unit).run st) = .ok ((), f st) := rfl

theorem obj_ok {st : St} {loc : Nat} {o : Obj} (ho : st.heap.objs[loc]? = some o) :
    (obj loc).run st = .ok (o, st) := by
  unfold obj
  rw [M_bind_run, M_get_run]
  dsimp only
  rw [ho]
  rfl

theorem setObj_run (loc : Nat) (o : Obj) (st : St) :
    (setObj loc o).run st =
      .ok ((), { st with heap := { st.heap with objs := st.heap.objs.set! loc o } }) := rfl

theorem freshCap_run (st : St) :
    freshCap.run st =
      .ok (st.heap.nextCap, { st with heap := { st.heap with nextCap := st.heap.nextCap + 1 } }) := rfl

theorem alloc_run (c : Cell) (t : List Nat) (st : St) :
    (alloc c t).run st =
      .ok (.ref st.heap.objs.size st.heap.nextCap t,
        { st with heap := { objs := st.heap.objs.push ⟨c, st.heap.nextCap⟩,
                            nextCap := st.heap.nextCap + 1 } }) := rfl

theorem alloc_preserves_old (c : Cell) (_t : List Nat) (st : St) :
    PreservesLocs (fun l => l < st.heap.objs.size) st.heap
      { objs := st.heap.objs.push ⟨c, st.heap.nextCap⟩, nextCap := st.heap.nextCap + 1 } := by
  intro l hl
  simp [Array.getElem?_push_lt hl]

theorem alloc_capsOk {c : Cell} {st : St} (hc : CapsOk st.heap) :
    CapsOk { objs := st.heap.objs.push ⟨c, st.heap.nextCap⟩, nextCap := st.heap.nextCap + 1 } := by
  intro l o ho
  dsimp only at ho ⊢
  by_cases hlt : l < st.heap.objs.size
  · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at ho
    have := hc l o ho
    omega
  · by_cases heq : l = st.heap.objs.size
    · subst heq
      rw [Array.getElem?_push_size] at ho
      cases ho
      dsimp only
      omega
    · have hnone : (st.heap.objs.push ⟨c, st.heap.nextCap⟩)[l]? = none :=
        Array.getElem?_eq_none (by simp; omega)
      rw [hnone] at ho
      contradiction

theorem Reach_lt_size {h : Heap} {v : Val} {l : Nat}
    (hd : DeepLive h v) (hr : Reach h v l) : l < h.objs.size := by
  induction hr with
  | @here loc cap t =>
    obtain ⟨o, ho, _⟩ := hd.self.1
    exact (Array.getElem?_eq_some_iff.mp ho).1
  | @step loc cap t o w l' ho hmem hr' ih =>
    exact ih (hd.sub (HeldBy_of_mem_vals ho hmem))

theorem Reach_alloc_new {h : Heap} {c : Cell} {t : List Nat} {l : Nat}
    (hsub : ∀ w ∈ c.vals, DeepLive h w) :
    let h' : Heap := { objs := h.objs.push ⟨c, h.nextCap⟩, nextCap := h.nextCap + 1 }
    Reach h' (.ref h.objs.size h.nextCap t) l ↔
      l = h.objs.size ∨ ∃ w ∈ c.vals, Reach h w l := by
  intro h'
  have hpOld : PreservesLocs (fun x => x < h.objs.size) h h' := by
    intro x hx; simp [h', Array.getElem?_push_lt hx]
  have hoNew : h'.objs[h.objs.size]? = some ⟨c, h.nextCap⟩ := by
    simp [h']
  constructor
  · intro hr
    cases hr with
    | here => exact Or.inl rfl
    | step ho hmem hr' =>
      rw [hoNew] at ho
      cases ho
      have hpw : PreservesLocs (Reach h _) h h' :=
        hpOld.mono (fun x hx => Reach_lt_size (hsub _ hmem) hx)
      exact Or.inr ⟨_, hmem, (Reach_congr hpw l).mp hr'⟩
  · rintro (rfl | ⟨w, hw, hrl⟩)
    · exact .here
    · have hpw : PreservesLocs (Reach h w) h h' :=
        hpOld.mono (fun x hx => Reach_lt_size (hsub w hw) hx)
      exact .step hoNew hw ((Reach_congr hpw l).mpr hrl)

theorem openRegion_run (st : St) :
    openRegion.run st =
      .ok ((st.nextRegion, st.regions.headD 0),
        { st with nextRegion := st.nextRegion + 1, regions := st.nextRegion :: st.regions }) := rfl

theorem closeRegion_run (r : Nat) (st : St) :
    (closeRegion r).run st =
      .ok ((), { st with regions := st.regions.filter (· != r) }) := rfl

theorem live_ok {st : St} {v : Val} (hl : LiveRef st.heap v) :
    (live v).run st = .ok ((), st) := by
  cases v with
  | imm _ => rfl
  | ref loc cap t =>
    obtain ⟨o, ho, hcap⟩ := hl
    unfold live
    rw [M_bind_run, obj_ok ho]
    simp only [hcap, beq_self_eq_true, ↓reduceIte]
    rfl

theorem isLeaf_ok {st : St} {v : Val} (hl : LiveRef st.heap v) :
    (isLeaf v).run st =
      .ok (match v with
           | .ref loc _ _ => match st.heap.objs[loc]? with
             | some o => o.cell.isNum
             | none => false
           | .imm _ => false, st) := by
  cases v with
  | imm _ => rfl
  | ref loc cap t =>
    obtain ⟨o, ho, _⟩ := hl
    unfold isLeaf
    have hnat : (natClass != .leaf) = false := rfl
    simp only [hnat, Bool.false_eq_true, ↓reduceIte]
    rw [M_bind_run, obj_ok ho]
    dsimp only
    rw [ho]
    cases hc : o.cell <;> simp [hc, Cell.isNum] <;> rfl

theorem numOf?_ok {st : St} {v : Val} (hl : LiveRef st.heap v) :
    (numOf? v).run st =
      .ok (match v with
           | .imm (.bits n) => some n
           | .ref loc _ _ => match st.heap.objs[loc]? with
             | some o => match o.cell with | .num n => some n | _ => none
             | none => none
           | .imm _ => none, st) := by
  cases v with
  | imm i => cases i <;> rfl
  | ref loc cap t =>
    obtain ⟨o, ho, hcap⟩ := hl
    unfold numOf?
    rw [M_bind_run, obj_ok ho]
    dsimp only
    rw [ho]
    simp only [hcap, beq_self_eq_true, ↓reduceIte]
    cases hc : o.cell <;> simp <;> rfl

theorem readOut_ok {st : St} {inherit : Bool} {t : List Nat} {v : Val}
    (hl : LiveRef st.heap v) (hlu : LeafUntainted st.heap v) :
    ∃ v', (readOut inherit t v).run st = .ok (v', st) ∧
      LiveRef st.heap v' ∧ LeafUntainted st.heap v' ∧
      (∀ r ∈ v'.taint, r ∈ v.taint ∨ (inherit = true ∧ r ∈ t)) ∧
      (∀ l, Reach st.heap v' l ↔ Reach st.heap v l) ∧
      (∀ w, HeldBy st.heap v' w → w = v' ∨ HeldBy st.heap v w) := by
  have stepNonNum : ∀ {loc cap : Nat} {tv : List Nat} {o : Obj},
      st.heap.objs[loc]? = some o → o.cap = cap → o.cell.isNum = false →
      LeafUntainted st.heap (.ref loc cap tv) →
      ∃ v', (readOut inherit t (.ref loc cap tv)).run st = .ok (v', st) ∧
        LiveRef st.heap v' ∧ LeafUntainted st.heap v' ∧
        (∀ r ∈ v'.taint, r ∈ (Val.ref loc cap tv).taint ∨ (inherit = true ∧ r ∈ t)) ∧
        (∀ l, Reach st.heap v' l ↔ Reach st.heap (.ref loc cap tv) l) ∧
        (∀ w, HeldBy st.heap v' w → w = v' ∨ HeldBy st.heap (.ref loc cap tv) w) := by
    intro loc cap tv o ho hcap hnn hlu'
    have hlive : LiveRef st.heap (.ref loc cap tv) := ⟨o, ho, hcap⟩
    cases inherit with
    | false =>
      refine ⟨.ref loc cap tv, ?_, hlive, hlu', fun r hr => Or.inl hr,
        fun _ => Iff.rfl, fun _ hw => Or.inr hw⟩
      unfold readOut
      rw [M_bind_run, isLeaf_ok hlive]
      simp only [ho, hnn, Bool.false_eq_true, ↓reduceIte]
      rfl
    | true =>
      obtain ⟨tv1, htv1⟩ := foldl_addTaint_ref t loc cap tv
      refine ⟨.ref loc cap tv1, ?_, ⟨o, ho, hcap⟩, ?_, ?_, fun _ => Reach_ref_taint,
        fun _ hw => HeldBy_ref_taint hw⟩
      · unfold readOut
        rw [M_bind_run, isLeaf_ok hlive]
        simp only [ho, hnn, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
        rw [M_pure_run, htv1]
      · intro o' n ho' hc'
        rw [ho] at ho'; cases ho'
        simp [hc', Cell.isNum] at hnn
      · intro r hr
        have hr' : r ∈ (t.foldl (fun v s => addTaint s v) (.ref loc cap tv)).taint := by
          rw [htv1]; exact hr
        rcases mem_taint_foldl_addTaint hr' with ht | htv
        · exact Or.inr ⟨rfl, ht⟩
        · exact Or.inl htv
  cases v with
  | imm i =>
    refine ⟨.imm i, ?_, trivial, trivial, by simp [Val.taint],
      fun _ => Iff.rfl, fun _ hw => Or.inr hw⟩
    unfold readOut
    rw [M_bind_run, isLeaf_ok hl]
    cases inherit
    · rfl
    · dsimp only
      rw [foldl_addTaint_imm]
      rfl
  | ref loc cap tv =>
    obtain ⟨o, ho, hcap⟩ := hl
    cases hc : o.cell with
    | num n =>
      have htv : tv = [] := hlu o n ho hc
      subst htv
      have hlive0 : LiveRef st.heap (.ref loc cap []) := ⟨o, ho, hcap⟩
      refine ⟨.ref loc cap [], ?_, hlive0, fun _ _ _ _ => rfl, by simp [Val.taint],
        fun _ => Iff.rfl, fun _ hw => Or.inr hw⟩
      unfold readOut
      rw [M_bind_run, isLeaf_ok hlive0]
      simp only [ho, hc, Cell.isNum, ↓reduceIte]
      rfl
    | ctor _ _ => exact stepNonNum ho hcap (by simp [hc, Cell.isNum]) hlu
    | str _ => exact stepNonNum ho hcap (by simp [hc, Cell.isNum]) hlu
    | clo _ _ _ _ _ _ => exact stepNonNum ho hcap (by simp [hc, Cell.isNum]) hlu
    | pap _ _ => exact stepNonNum ho hcap (by simp [hc, Cell.isNum]) hlu
    | once _ _ => exact stepNonNum ho hcap (by simp [hc, Cell.isNum]) hlu

/-! ## 7b. `confinedOpen`, `mkNum`, `natValue`, `conform`, `prim`, `strValue`, `construct` -/

theorem confinedOpen_run (v : Val) (st : St) :
    (confinedOpen v).run st = .ok (v.taint.any (fun s => st.regions.contains s), st) := rfl

theorem mkNum_ok (c : Cls) (n : Nat) (st : St) (hc : CapsOk st.heap) :
    ∃ v st', (mkNum c n).run st = .ok (v, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      DeepLive st'.heap v ∧ v.taint = [] ∧ AcyclicFrom st'.heap v ∧
      (c = .imm → v = .imm (.bits n)) ∧
      (c ≠ .imm → ∃ loc cap o, v = .ref loc cap [] ∧ st'.heap.objs[loc]? = some o ∧
        o.cell = .num n ∧ o.cap = cap ∧ st.heap.objs.size ≤ loc) := by
  cases c with
  | imm =>
    refine ⟨.imm (.bits n), st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, ?_, rfl, ?_, fun _ => rfl, fun h => absurd rfl h⟩
    · intro w hw
      rcases hw with rfl | ⟨_, _, hr, _, _⟩
      · exact ⟨trivial, trivial⟩
      · cases hr
    · intro _ _ _ hr; cases hr
  | irr | leaf | val =>
    refine ⟨.ref st.heap.objs.size st.heap.nextCap [],
      { st with heap := { objs := st.heap.objs.push ⟨.num n, st.heap.nextCap⟩,
                          nextCap := st.heap.nextCap + 1 } },
      rfl, rfl, rfl, rfl, rfl, by simp, Nat.le_succ _,
      alloc_preserves_old (.num n) [] st, alloc_capsOk hc, ?_, rfl, ?_,
      (fun h => by cases h),
      fun _ => ⟨st.heap.objs.size, st.heap.nextCap, ⟨.num n, st.heap.nextCap⟩, rfl,
        by simp, rfl, rfl, Nat.le_refl _⟩⟩
    · intro w hw
      rcases hw with rfl | ⟨l, o, hr, ho, hm⟩
      · exact ⟨⟨⟨.num n, st.heap.nextCap⟩, by simp, rfl⟩, fun _ _ _ _ => rfl⟩
      · cases hr with
        | here =>
          simp only [Array.getElem?_push_size, Option.some.injEq] at ho
          subst ho; simp [Cell.vals] at hm
        | step ho' hm' _ =>
          simp only [Array.getElem?_push_size, Option.some.injEq] at ho'
          subst ho'; simp [Cell.vals] at hm'
    · intro l o w hr ho hm
      cases hr with
      | here =>
        simp only [Array.getElem?_push_size, Option.some.injEq] at ho
        subst ho; simp [Cell.vals] at hm
      | step ho' hm' _ =>
        simp only [Array.getElem?_push_size, Option.some.injEq] at ho'
        subst ho'; simp [Cell.vals] at hm'

theorem natValue_ok (n : Nat) (st : St) (hc : CapsOk st.heap) :
    ∃ v st', (natValue n).run st = .ok (v, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      DeepLive st'.heap v ∧ ClsOk st'.heap natClass v ∧
      v.taint = [] ∧ AcyclicFrom st'.heap v := by
  obtain ⟨v, st', hrun, h1, h2, h3, h4, hsz, hcap, hpres, hc', hdl, ht, hacyc, _, hnum⟩ :=
    mkNum_ok natClass n st hc
  obtain ⟨loc, cap, o, rfl, ho, hcell, hocap, _⟩ := hnum (by decide)
  exact ⟨.ref loc cap [], st', hrun, h1, h2, h3, h4, hsz, hcap, hpres, hc', hdl,
    ⟨loc, cap, o, n, rfl, ho, hcell, hocap⟩, ht, hacyc⟩

theorem conform_spec {st : St} {c : Cls} {v : Val}
    (hc : CapsOk st.heap) (hdl : DeepLive st.heap v) (hacyc : AcyclicFrom st.heap v) :
    (conform c v).run st = .error .stuck ∨
    ∃ v' st', (conform c v).run st = .ok (v', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      DeepLive st'.heap v' ∧ ClsOk st'.heap c v' ∧ AcyclicFrom st'.heap v' ∧
      (∀ r ∈ v'.taint, r ∈ v.taint) ∧
      (∀ l, Reach st'.heap v' l → st.heap.objs.size ≤ l ∨ Reach st.heap v l) ∧
      (∀ w, HeldBy st'.heap v' w → w = v' ∨ HeldBy st.heap v w) := by
  have hImm : ∀ i, DeepLive st.heap (.imm i) ∧ AcyclicFrom st.heap (.imm i) := by
    intro i
    refine ⟨fun w hw => ?_, fun _ _ _ hr => by cases hr⟩
    rcases hw with rfl | ⟨_, _, hr, _, _⟩
    · exact ⟨trivial, trivial⟩
    · cases hr
  cases c with
  | irr =>
    right
    refine ⟨.imm .irr, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, (hImm .irr).1, rfl, (hImm .irr).2,
      by simp [Val.taint], (fun _ hr => by cases hr), fun w hw => ?_⟩
    rcases hw with rfl | ⟨_, _, hr, _, _⟩
    · exact Or.inl rfl
    · cases hr
  | val =>
    right
    exact ⟨v, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, hdl, trivial, hacyc, fun _ hr => hr,
      fun _ hr => Or.inr hr, fun _ hw => Or.inr hw⟩
  | imm =>
    cases v with
    | imm i =>
      right
      refine ⟨.imm i, st, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
        PreservesLocs.refl _ _, hc, (hImm i).1, ⟨i, rfl⟩, (hImm i).2,
        by simp [Val.taint], (fun _ hr => by cases hr), fun w hw => ?_⟩
      rcases hw with rfl | ⟨_, _, hr, _, _⟩
      · exact Or.inl rfl
      · cases hr
    | ref loc cap t =>
      obtain ⟨o, ho, hcap⟩ := hdl.self.1
      cases hcell : o.cell with
      | num n =>
        right
        refine ⟨.imm (.bits n), st, ?_, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
          PreservesLocs.refl _ _, hc, (hImm (.bits n)).1, ⟨.bits n, rfl⟩, (hImm (.bits n)).2,
          by simp [Val.taint], (fun _ hr => by cases hr), fun w hw => ?_⟩
        · unfold conform
          rw [M_bind_run, numOf?_ok hdl.self.1]
          dsimp only; rw [ho]; dsimp only; rw [hcell]; rfl
        · rcases hw with rfl | ⟨_, _, hr, _, _⟩
          · exact Or.inl rfl
          · cases hr
      | ctor _ _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
        left
        unfold conform
        rw [M_bind_run, numOf?_ok hdl.self.1]
        dsimp only; rw [ho]; dsimp only; rw [hcell]; rfl
  | leaf =>
    cases v with
    | imm i =>
      cases i with
      | bits n =>
        right
        obtain ⟨v', st', hrun, h1, h2, h3, h4, hsz, hcap, hpres, hc', hdl', ht', hacyc', _, hnum⟩ :=
          mkNum_ok .leaf n st hc
        obtain ⟨loc, cap, o, rfl, ho, hcell, hocap, hge⟩ := hnum (by decide)
        refine ⟨.ref loc cap [], st', ?_, h1, h2, h3, h4, hsz, hcap, hpres, hc', hdl',
          ⟨loc, cap, o, n, rfl, ho, hcell, hocap⟩, hacyc', by simp [Val.taint], ?_, ?_⟩
        · exact hrun
        · intro l hr
          cases hr with
          | here => exact Or.inl hge
          | step ho' hm' _ =>
            rw [ho] at ho'; cases ho'; rw [hcell] at hm'; simp [Cell.vals] at hm'
        · intro w hw
          rcases hw with rfl | ⟨l, o', hr, ho', hm'⟩
          · exact Or.inl rfl
          · cases hr with
            | here => rw [ho] at ho'; cases ho'; rw [hcell] at hm'; simp [Cell.vals] at hm'
            | step ho'' hm'' _ => rw [ho] at ho''; cases ho''; rw [hcell] at hm''; simp [Cell.vals] at hm''
      | con _ | irr => left; rfl
    | ref loc cap t =>
      obtain ⟨o, ho, hcap⟩ := hdl.self.1
      cases hcell : o.cell with
      | num n =>
        have ht : t = [] := hdl.self.2 o n ho hcell
        subst ht
        right
        refine ⟨.ref loc cap [], st, ?_, rfl, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
          PreservesLocs.refl _ _, hc, hdl, ⟨loc, cap, o, n, rfl, ho, hcell, hcap⟩, hacyc,
          fun _ hr => hr, fun _ hr => Or.inr hr, fun _ hw => Or.inr hw⟩
        unfold conform
        rw [M_bind_run, numOf?_ok hdl.self.1]
        dsimp only; rw [ho]; dsimp only; rw [hcell]; rfl
      | ctor _ _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
        left
        unfold conform
        rw [M_bind_run, numOf?_ok hdl.self.1]
        dsimp only; rw [ho]; dsimp only; rw [hcell]; rfl

theorem strValue_ok (s : String) (st : St) (hc : CapsOk st.heap)
    (hstrs : ∀ p ∈ st.strs.toList, DeepLive st.heap p.2 ∧ p.2.taint = [] ∧ AcyclicFrom st.heap p.2) :
    ∃ v st', (strValue s).run st = .ok (v, st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧
      st.heap.objs.size ≤ st'.heap.objs.size ∧ st.heap.nextCap ≤ st'.heap.nextCap ∧
      PreservesLocs (fun l => l < st.heap.objs.size) st.heap st'.heap ∧
      CapsOk st'.heap ∧
      DeepLive st'.heap v ∧ v.taint = [] ∧ AcyclicFrom st'.heap v ∧
      (∀ p ∈ st'.strs.toList, DeepLive st'.heap p.2 ∧ p.2.taint = [] ∧ AcyclicFrom st'.heap p.2) := by
  unfold strValue
  rw [M_bind_run, M_get_run]
  dsimp only
  cases hfind : st.strs.find? (·.1 == s) with
  | some p =>
    have hmem : p ∈ st.strs.toList := by
      exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind)
    have ⟨hdl, ht, hacyc⟩ := hstrs p hmem
    refine ⟨p.2, st, ?_, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _,
      PreservesLocs.refl _ _, hc, hdl, ht, hacyc, hstrs⟩
    rw [M_bind_run, live_ok hdl.self.1]
    rfl
  | none =>
    let st1 : St := { st with
      heap := { objs := st.heap.objs.push ⟨.str s, st.heap.nextCap⟩,
                nextCap := st.heap.nextCap + 1 } }
    let st2 : St := { st1 with strs := st1.strs.push (s, .ref st.heap.objs.size st.heap.nextCap []) }
    have hpres : PreservesLocs (fun l => l < st.heap.objs.size) st.heap st2.heap :=
      alloc_preserves_old (.str s) [] st
    have hc' : CapsOk st2.heap := alloc_capsOk hc
    have hdlNew : DeepLive st2.heap (.ref st.heap.objs.size st.heap.nextCap []) := by
      intro w hw
      rcases hw with rfl | ⟨l, o, hr, ho, hm⟩
      · exact ⟨⟨⟨.str s, st.heap.nextCap⟩, by simp [st2, st1], rfl⟩,
          fun _ _ _ _ => rfl⟩
      · cases hr with
        | here =>
          simp only [st2, st1, Array.getElem?_push_size, Option.some.injEq] at ho
          subst ho; simp [Cell.vals] at hm
        | step ho' hm' _ =>
          simp only [st2, st1, Array.getElem?_push_size, Option.some.injEq] at ho'
          subst ho'; simp [Cell.vals] at hm'
    have hacycNew : AcyclicFrom st2.heap (.ref st.heap.objs.size st.heap.nextCap []) := by
      intro l o w hr ho hm
      cases hr with
      | here =>
        simp only [st2, st1, Array.getElem?_push_size, Option.some.injEq] at ho
        subst ho; simp [Cell.vals] at hm
      | step ho' hm' _ =>
        simp only [st2, st1, Array.getElem?_push_size, Option.some.injEq] at ho'
        subst ho'; simp [Cell.vals] at hm'
    refine ⟨.ref st.heap.objs.size st.heap.nextCap [], st2, ?_, rfl, rfl, rfl,
      by simp [st2, st1], Nat.le_succ _, hpres, hc', hdlNew, rfl, hacycNew, ?_⟩
    · rw [M_bind_run, alloc_run]
      rfl
    · intro q hq
      simp only [st2, st1, Array.toList_push, List.mem_append, List.mem_singleton] at hq
      rcases hq with hqOld | rfl
      · have ⟨hdlq, htq, hacycq⟩ := hstrs q hqOld
        have hpq : PreservesLocs (Reach st.heap q.2) st.heap st2.heap :=
          hpres.mono (fun x hx => Reach_lt_size hdlq hx)
        exact ⟨(DeepLive_congr hpq).mpr hdlq, htq, (AcyclicFrom_congr hpq).mpr hacycq⟩
      · exact ⟨hdlNew, rfl, hacycNew⟩

/-! ## 8. `ValSameShape`, `CellSameShape`, `HeapSameShape`, and `renew` / `transfer` -/

/-- Two values have identical runtime structure (differing at most in cell capabilities). -/
def ValSameShape : Val → Val → Prop
  | .imm i₁, .imm i₂ => i₁ = i₂
  | .ref l₁ _ t₁, .ref l₂ _ t₂ => l₁ = l₂ ∧ t₁ = t₂
  | _, _ => False

theorem ValSameShape.refl : ∀ v, ValSameShape v v
  | .imm _ => rfl
  | .ref _ _ _ => ⟨rfl, rfl⟩

theorem ValSameShape.symm {v₁ v₂ : Val} (h : ValSameShape v₁ v₂) : ValSameShape v₂ v₁ := by
  cases v₁ <;> cases v₂ <;> simp [ValSameShape] at h ⊢
  · exact h.symm
  · exact ⟨h.1.symm, h.2.symm⟩

theorem ValSameShape.trans {v₁ v₂ v₃ : Val} (h1 : ValSameShape v₁ v₂) (h2 : ValSameShape v₂ v₃) :
    ValSameShape v₁ v₃ := by
  cases v₁ <;> cases v₂ <;> cases v₃ <;> simp [ValSameShape] at h1 h2 ⊢
  · exact h1.trans h2
  · exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem ValSameShape.taint_eq {v₁ v₂ : Val} (h : ValSameShape v₁ v₂) : v₁.taint = v₂.taint := by
  cases v₁ <;> cases v₂ <;> simp [ValSameShape, Val.taint] at h ⊢
  exact h.2

/-- Two cells have identical constructor/metadata/slot-shapes (differing at most in capabilities). -/
def CellSameShape : Cell → Cell → Prop
  | .ctor r₁ fs₁, .ctor r₂ fs₂ =>
    r₁ = r₂ ∧ fs₁.size = fs₂.size ∧
      ∀ i, (h₁ : i < fs₁.size) → (h₂ : i < fs₂.size) → ValSameShape fs₁[i] fs₂[i]
  | .num n₁, .num n₂ => n₁ = n₂
  | .str s₁, .str s₂ => s₁ = s₂
  | .clo e₁ p₁ r₁ rc₁ fvs₁ body₁, .clo e₂ p₂ r₂ rc₂ fvs₂ body₂ =>
    p₁ = p₂ ∧ r₁ = r₂ ∧ rc₁ = rc₂ ∧ fvs₁ = fvs₂ ∧ body₁ = body₂ ∧
      e₁.length = e₂.length ∧
      ∀ (i : Nat), match e₁[i]?, e₂[i]? with
        | some bd₁, some bd₂ => bd₁.mode = bd₂.mode ∧ ValSameShape bd₁.val bd₂.val
        | none, none => True
        | _, _ => False
  | .pap r₁ as₁, .pap r₂ as₂ =>
    r₁ = r₂ ∧ as₁.size = as₂.size ∧
      ∀ i, (h₁ : i < as₁.size) → (h₂ : i < as₂.size) → ValSameShape as₁[i] as₂[i]
  | .once t₁ sp₁, .once t₂ sp₂ => sp₁ = sp₂ ∧ ValSameShape t₁ t₂
  | _, _ => False

theorem CellSameShape.refl : ∀ c, CellSameShape c c
  | .ctor _ _ => ⟨rfl, rfl, fun _ _ _ => ValSameShape.refl _⟩
  | .num _ => rfl
  | .str _ => rfl
  | .clo e _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun i => by
      cases e[i]? with
      | none => trivial
      | some b => exact ⟨rfl, ValSameShape.refl _⟩⟩
  | .pap _ _ => ⟨rfl, rfl, fun _ _ _ => ValSameShape.refl _⟩
  | .once _ _ => ⟨rfl, ValSameShape.refl _⟩

theorem CellSameShape.symm {c₁ c₂ : Cell} (h : CellSameShape c₁ c₂) : CellSameShape c₂ c₁ := by
  cases c₁ with
  | ctor r₁ fs₁ =>
    cases c₂ with
    | ctor r₂ fs₂ =>
      rcases h with ⟨rfl, hsz, hfs⟩
      exact ⟨rfl, hsz.symm, fun i h2 h1 => (hfs i h1 h2).symm⟩
    | _ => exact h
  | num n₁ =>
    cases c₂ with
    | num n₂ => exact Eq.symm h
    | _ => exact h
  | str s₁ =>
    cases c₂ with
    | str s₂ => exact Eq.symm h
    | _ => exact h
  | clo e₁ p₁ r₁ rc₁ fvs₁ body₁ =>
    cases c₂ with
    | clo e₂ p₂ r₂ rc₂ fvs₂ body₂ =>
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, hlen, he⟩
      refine ⟨rfl, rfl, rfl, rfl, rfl, hlen.symm, fun i => ?_⟩
      have hi := he i
      cases h1 : e₁[i]? <;> cases h2 : e₂[i]? <;> simp [h1, h2] at hi ⊢
      exact ⟨hi.1.symm, hi.2.symm⟩
    | _ => exact h
  | pap r₁ as₁ =>
    cases c₂ with
    | pap r₂ as₂ =>
      rcases h with ⟨rfl, hsz, has⟩
      exact ⟨rfl, hsz.symm, fun i h2 h1 => (has i h1 h2).symm⟩
    | _ => exact h
  | once t₁ sp₁ =>
    cases c₂ with
    | once t₂ sp₂ => exact ⟨h.1.symm, h.2.symm⟩
    | _ => exact h

theorem CellSameShape.trans {c₁ c₂ c₃ : Cell} (h1 : CellSameShape c₁ c₂) (h2 : CellSameShape c₂ c₃) :
    CellSameShape c₁ c₃ := by
  cases c₁ with
  | ctor r₁ fs₁ =>
    cases c₂ with
    | ctor r₂ fs₂ =>
      cases c₃ with
      | ctor r₃ fs₃ =>
        rcases h1 with ⟨rfl, hsz1, hfs1⟩
        rcases h2 with ⟨rfl, hsz2, hfs2⟩
        exact ⟨rfl, hsz1.trans hsz2, fun i hi1 hi3 => (hfs1 i hi1 (hsz1 ▸ hi1)).trans (hfs2 i (hsz1 ▸ hi1) hi3)⟩
      | _ => exact h2
    | _ => exact False.elim h1
  | num n₁ =>
    cases c₂ with
    | num n₂ => cases c₃ with | num n₃ => exact Eq.trans h1 h2 | _ => exact h2
    | _ => exact False.elim h1
  | str s₁ =>
    cases c₂ with
    | str s₂ => cases c₃ with | str s₃ => exact Eq.trans h1 h2 | _ => exact h2
    | _ => exact False.elim h1
  | clo e₁ p₁ r₁ rc₁ fvs₁ body₁ =>
    cases c₂ with
    | clo e₂ p₂ r₂ rc₂ fvs₂ body₂ =>
      cases c₃ with
      | clo e₃ p₃ r₃ rc₃ fvs₃ body₃ =>
        rcases h1 with ⟨rfl, rfl, rfl, rfl, rfl, hlen1, he1⟩
        rcases h2 with ⟨rfl, rfl, rfl, rfl, rfl, hlen2, he2⟩
        refine ⟨rfl, rfl, rfl, rfl, rfl, hlen1.trans hlen2, fun i => ?_⟩
        have hi1 := he1 i
        have hi2 := he2 i
        cases heq1 : e₁[i]? <;> cases heq2 : e₂[i]? <;> cases heq3 : e₃[i]? <;>
          simp [heq1, heq2, heq3] at hi1 hi2 ⊢
        exact ⟨hi1.1.trans hi2.1, hi1.2.trans hi2.2⟩
      | _ => exact h2
    | _ => exact False.elim h1
  | pap r₁ as₁ =>
    cases c₂ with
    | pap r₂ as₂ =>
      cases c₃ with
      | pap r₃ as₃ =>
        rcases h1 with ⟨rfl, hsz1, has1⟩
        rcases h2 with ⟨rfl, hsz2, has2⟩
        exact ⟨rfl, hsz1.trans hsz2, fun i hi1 hi3 => (has1 i hi1 (hsz1 ▸ hi1)).trans (has2 i (hsz1 ▸ hi1) hi3)⟩
      | _ => exact h2
    | _ => exact False.elim h1
  | once t₁ sp₁ =>
    cases c₂ with
    | once t₂ sp₂ =>
      cases c₃ with
      | once t₃ sp₃ => exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
      | _ => exact h2
    | _ => exact False.elim h1

theorem CellSameShape.isNum_eq {c₁ c₂ : Cell} (h : CellSameShape c₁ c₂) : c₁.isNum = c₂.isNum := by
  cases c₁ <;> cases c₂ <;> simp [CellSameShape, Cell.isNum] at h ⊢

theorem CellSameShape.ownedSlots_eq {P : Prog} {c₁ c₂ : Cell} (h : CellSameShape c₁ c₂) :
    ownedSlots P c₁ = ownedSlots P c₂ := by
  cases c₁ <;> cases c₂ <;> simp [CellSameShape, ownedSlots] at h ⊢
  · rcases h with ⟨rfl, hsz, _⟩; simp [hsz]
  · rcases h with ⟨_, _, _, rfl, _⟩; rfl
  · rcases h with ⟨_, hsz, _⟩; simp [hsz]

theorem CellSameShape.slot? {c₁ c₂ : Cell} (h : CellSameShape c₁ c₂) (i : Nat) :
    match c₁.slot? i, c₂.slot? i with
    | some w₁, some w₂ => ValSameShape w₁ w₂
    | none, none => True
    | _, _ => False := by
  cases c₁ with
  | ctor r₁ fs₁ =>
    cases c₂ with
    | ctor r₂ fs₂ =>
      rcases h with ⟨rfl, hsz, hfs⟩
      simp only [Cell.slot?]
      by_cases hi : i < fs₁.size
      · have hi2 : i < fs₂.size := hsz ▸ hi
        simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi2]
        exact hfs i hi hi2
      · have hi2 : ¬ i < fs₂.size := fun hlt => hi (hsz.symm ▸ hlt)
        simp [Array.getElem?_eq_none (Nat.le_of_not_lt hi),
          Array.getElem?_eq_none (Nat.le_of_not_lt hi2)]
    | _ => exact False.elim h
  | num _ => cases c₂ with | num _ => trivial | _ => exact False.elim h
  | str _ => cases c₂ with | str _ => trivial | _ => exact False.elim h
  | clo e₁ p₁ r₁ rc₁ fvs₁ body₁ =>
    cases c₂ with
    | clo e₂ p₂ r₂ rc₂ fvs₂ body₂ =>
      rcases h with ⟨_, _, _, _, _, _, he⟩
      have hi := he i
      simp only [Cell.slot?]
      cases h1 : e₁[i]? <;> cases h2 : e₂[i]? <;> simp [h1, h2] at hi ⊢
      exact hi.2
    | _ => exact False.elim h
  | pap r₁ as₁ =>
    cases c₂ with
    | pap r₂ as₂ =>
      rcases h with ⟨rfl, hsz, has⟩
      simp only [Cell.slot?]
      by_cases hi : i < as₁.size
      · have hi2 : i < as₂.size := hsz ▸ hi
        simp only [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi2]
        exact has i hi hi2
      · have hi2 : ¬ i < as₂.size := fun hlt => hi (hsz.symm ▸ hlt)
        simp [Array.getElem?_eq_none (Nat.le_of_not_lt hi),
          Array.getElem?_eq_none (Nat.le_of_not_lt hi2)]
    | _ => exact False.elim h
  | once t₁ sp₁ =>
    cases c₂ with
    | once t₂ sp₂ =>
      cases i with
      | zero => exact h.2
      | succ _ => trivial
    | _ => exact False.elim h

theorem CellSameShape.vals_fwd {c₁ c₂ : Cell} (h : CellSameShape c₁ c₂) {w₁ : Val}
    (hw : w₁ ∈ c₁.vals) : ∃ w₂ ∈ c₂.vals, ValSameShape w₁ w₂ := by
  cases c₁ with
  | ctor r₁ fs₁ =>
    cases c₂ with
    | ctor r₂ fs₂ =>
      rcases h with ⟨rfl, hsz, hfs⟩
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hw)
      have hi2 : i < fs₂.size := hsz ▸ hi
      exact ⟨fs₂[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi2), hfs i hi hi2⟩
    | _ => exact False.elim h
  | num _ | str _ => simp [Cell.vals] at hw
  | clo e₁ p₁ r₁ rc₁ fvs₁ body₁ =>
    cases c₂ with
    | clo e₂ p₂ r₂ rc₂ fvs₂ body₂ =>
      rcases h with ⟨_, _, _, rfl, _, _, he⟩
      simp only [Cell.vals, List.mem_filterMap] at hw ⊢
      rcases hw with ⟨i, hi, hmap⟩
      obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp hmap
      have hbi := he i
      cases hb2 : e₂[i]? with
      | none => simp [hb1, hb2] at hbi
      | some b2 =>
        simp [hb1, hb2] at hbi
        exact ⟨b2.val, ⟨i, hi, by simp [hb2]⟩, hbi.2⟩
    | _ => exact False.elim h
  | pap r₁ as₁ =>
    cases c₂ with
    | pap r₂ as₂ =>
      rcases h with ⟨rfl, hsz, has⟩
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hw)
      have hi2 : i < as₂.size := hsz ▸ hi
      exact ⟨as₂[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi2), has i hi hi2⟩
    | _ => exact False.elim h
  | once t₁ sp₁ =>
    cases c₂ with
    | once t₂ sp₂ =>
      simp only [Cell.vals, List.mem_singleton] at hw ⊢
      subst hw
      exact ⟨t₂, rfl, h.2⟩
    | _ => exact False.elim h

theorem CellSameShape.setSlot_right {c : Cell} {i : Nat} {w w' : Val}
    (hs : c.slot? i = some w) (hsh : ValSameShape w w') :
    CellSameShape c (c.setSlot i w') := by
  cases c with
  | ctor r fs =>
    simp only [Cell.slot?] at hs
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hs
    refine ⟨rfl, by simp [Array.set!], fun j hj1 hj2 => ?_⟩
    by_cases hji : j = i
    · subst hji
      simp only [Array.set!] at hj2 ⊢
      rw [Array.getElem_setIfInBounds_self hj2]
      exact hget ▸ hsh
    · simp only [Array.set!] at hj2 ⊢
      rw [Array.getElem_setIfInBounds_ne hj1 (Ne.symm hji)]
      exact ValSameShape.refl _
  | clo env p res rc fvs b =>
    simp only [Cell.slot?] at hs
    obtain ⟨bd, hbd, rfl⟩ := Option.map_eq_some_iff.mp hs
    refine ⟨rfl, rfl, rfl, rfl, rfl, (setBnd_length env i w').symm, fun j => ?_⟩
    by_cases hji : j = i
    · subst hji
      rw [hbd, setBnd_getElem?_same hbd]
      exact ⟨rfl, hsh⟩
    · rw [setBnd_getElem?_other hji]
      cases env[j]? with
      | none => trivial
      | some _ => exact ⟨rfl, ValSameShape.refl _⟩
  | pap r as =>
    simp only [Cell.slot?] at hs
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hs
    refine ⟨rfl, by simp [Array.set!], fun j hj1 hj2 => ?_⟩
    by_cases hji : j = i
    · subst hji
      simp only [Array.set!] at hj2 ⊢
      rw [Array.getElem_setIfInBounds_self hj2]
      exact hget ▸ hsh
    · simp only [Array.set!] at hj2 ⊢
      rw [Array.getElem_setIfInBounds_ne hj1 (Ne.symm hji)]
      exact ValSameShape.refl _
  | once t sp =>
    cases i with
    | zero =>
      simp only [Cell.slot?, Option.some.injEq] at hs
      subst hs
      exact ⟨rfl, hsh⟩
    | succ _ => simp [Cell.slot?] at hs
  | num _ | str _ => simp [Cell.slot?] at hs

/-- Two heaps have the same size and same cell shapes at every location. -/
def HeapSameShape (h₁ h₂ : Heap) : Prop :=
  h₁.objs.size = h₂.objs.size ∧
  ∀ (l : Nat) (o₁ o₂ : Obj), h₁.objs[l]? = some o₁ → h₂.objs[l]? = some o₂ → CellSameShape o₁.cell o₂.cell

theorem HeapSameShape.refl (h : Heap) : HeapSameShape h h :=
  ⟨rfl, fun _ _ _ h1 h2 => by rw [h1] at h2; cases h2; exact CellSameShape.refl _⟩

theorem HeapSameShape.symm {h₁ h₂ : Heap} (h : HeapSameShape h₁ h₂) : HeapSameShape h₂ h₁ :=
  ⟨h.1.symm, fun l o₂ o₁ h2 h1 => (h.2 l o₁ o₂ h1 h2).symm⟩

theorem HeapSameShape.trans {h₁ h₂ h₃ : Heap} (h12 : HeapSameShape h₁ h₂) (h23 : HeapSameShape h₂ h₃) :
    HeapSameShape h₁ h₃ := by
  refine ⟨h12.1.trans h23.1, fun l o₁ o₃ ho1 ho3 => ?_⟩
  have hlt1 : l < h₁.objs.size := (Array.getElem?_eq_some_iff.mp ho1).1
  have hlt2 : l < h₂.objs.size := h12.1 ▸ hlt1
  have ho2 : h₂.objs[l]? = some h₂.objs[l] := Array.getElem?_eq_getElem hlt2
  exact (h12.2 l o₁ _ ho1 ho2).trans (h23.2 l _ o₃ ho2 ho3)

theorem HeapSameShape.getElem?_some {h₁ h₂ : Heap} (h : HeapSameShape h₁ h₂) {l : Nat} {o₁ : Obj}
    (ho1 : h₁.objs[l]? = some o₁) : ∃ o₂, h₂.objs[l]? = some o₂ ∧ CellSameShape o₁.cell o₂.cell := by
  have hlt2 : l < h₂.objs.size := h.1 ▸ (Array.getElem?_eq_some_iff.mp ho1).1
  have ho2 : h₂.objs[l]? = some h₂.objs[l] := Array.getElem?_eq_getElem hlt2
  exact ⟨h₂.objs[l], ho2, h.2 l o₁ _ ho1 ho2⟩

theorem HeapSameShape.setObj {h : Heap} {loc : Nat} {o o' : Obj}
    (ho : h.objs[loc]? = some o) (hsh : CellSameShape o.cell o'.cell) :
    HeapSameShape h { h with objs := h.objs.set! loc o' } := by
  refine ⟨by simp [Array.set!], fun l o₁ o₂ h1 h2 => ?_⟩
  by_cases hloc : l = loc
  · subst hloc
    rw [ho] at h1; cases h1
    have hlt : l < h.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
    simp only [Array.set!, Array.getElem?_setIfInBounds_self, hlt, ↓reduceIte, Option.some.injEq] at h2
    subst h2; exact hsh
  · simp only [Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hloc)] at h2
    rw [h1] at h2; cases h2
    exact CellSameShape.refl _

theorem Reach_of_sameShape {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) {l : Nat} (hr : Reach h₁ v₁ l) :
    Reach h₂ v₂ l := by
  induction hr generalizing v₂ with
  | @here loc cap t =>
    cases v₂ with
    | imm _ => exact False.elim hv
    | ref l2 c2 t2 =>
      rcases hv with ⟨rfl, _⟩
      exact .here
  | @step loc cap t o₁ w₁ l' ho1 hm1 _ ih =>
    cases v₂ with
    | imm _ => exact False.elim hv
    | ref l2 c2 t2 =>
      rcases hv with ⟨rfl, _⟩
      obtain ⟨o₂, ho2, hsh⟩ := hh.getElem?_some ho1
      obtain ⟨w₂, hm2, hwsh⟩ := hsh.vals_fwd hm1
      exact .step ho2 hm2 (ih hwsh)

theorem Reach_iff_sameShape {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) (l : Nat) :
    Reach h₁ v₁ l ↔ Reach h₂ v₂ l :=
  ⟨Reach_of_sameShape hh hv, Reach_of_sameShape hh.symm hv.symm⟩

theorem OwnReach_of_sameShape {P : Prog} {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) {l : Nat} (hr : OwnReach P h₁ v₁ l) :
    OwnReach P h₂ v₂ l := by
  induction hr generalizing v₂ with
  | @here loc cap t o₁ ho1 hnn =>
    cases v₂ with
    | imm _ => exact False.elim hv
    | ref l2 c2 t2 =>
      rcases hv with ⟨rfl, _⟩
      obtain ⟨o₂, ho2, hsh⟩ := hh.getElem?_some ho1
      exact .here ho2 (by rw [← hsh.isNum_eq]; exact hnn)
  | @step loc cap t o₁ i w₁ l' ho1 hi hs1 _ ih =>
    cases v₂ with
    | imm _ => exact False.elim hv
    | ref l2 c2 t2 =>
      rcases hv with ⟨rfl, _⟩
      obtain ⟨o₂, ho2, hsh⟩ := hh.getElem?_some ho1
      have hslot := hsh.slot? i
      cases hs2 : o₂.cell.slot? i with
      | none => simp [hs1, hs2] at hslot
      | some w₂ =>
        simp [hs1, hs2] at hslot
        exact .step ho2 (by rw [← hsh.ownedSlots_eq (P := P)]; exact hi) hs2 (ih hslot)

theorem OwnReach_iff_sameShape {P : Prog} {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) (l : Nat) :
    OwnReach P h₁ v₁ l ↔ OwnReach P h₂ v₂ l :=
  ⟨OwnReach_of_sameShape hh hv, OwnReach_of_sameShape hh.symm hv.symm⟩

theorem AcyclicFrom_of_sameShape {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) (ha : AcyclicFrom h₁ v₁) :
    AcyclicFrom h₂ v₂ := by
  intro l o₂ w₂ hrl2 ho2 hm2 hwl2
  have hrl1 := (Reach_iff_sameShape hh hv l).mpr hrl2
  obtain ⟨o₁, ho1, hsh⟩ := hh.symm.getElem?_some ho2
  obtain ⟨w₁, hm1, hwsh⟩ := hsh.vals_fwd hm2
  exact ha l o₁ w₁ hrl1 ho1 hm1 ((Reach_iff_sameShape hh hwsh.symm l).mpr hwl2)

theorem OwnTreeFull_of_sameShape {P : Prog} {h₁ h₂ : Heap} (hh : HeapSameShape h₁ h₂)
    {v₁ v₂ : Val} (hv : ValSameShape v₁ v₂) (ht : OwnTreeFull P h₁ v₁) :
    OwnTreeFull P h₂ v₂ := by
  constructor
  · intro p₁ p₂ i₁ i₂ l c₁ c₂ o₁ o₂ t₁ t₂ hp₁ hp₂ ho₁ ho₂ hi₁ hi₂ hs₁ hs₂ hnl
    have hp₁' := (OwnReach_iff_sameShape hh hv p₁).mpr hp₁
    have hp₂' := (OwnReach_iff_sameShape hh hv p₂).mpr hp₂
    obtain ⟨o₁', ho₁', hsh₁⟩ := hh.symm.getElem?_some ho₁
    obtain ⟨o₂', ho₂', hsh₂⟩ := hh.symm.getElem?_some ho₂
    have hslot1 := hsh₁.slot? i₁
    have hslot2 := hsh₂.slot? i₂
    cases hs₁' : o₁'.cell.slot? i₁ with
    | none => simp [hs₁, hs₁'] at hslot1
    | some w₁' =>
      cases hs₂' : o₂'.cell.slot? i₂ with
      | none => simp [hs₂, hs₂'] at hslot2
      | some w₂' =>
        simp [hs₁, hs₁'] at hslot1
        simp [hs₂, hs₂'] at hslot2
        cases w₁' with
        | imm _ => exact False.elim hslot1
        | ref l₁' c₁' t₁' =>
          cases w₂' with
          | imm _ => exact False.elim hslot2
          | ref l₂' c₂' t₂' =>
            rcases hslot1 with ⟨rfl, _⟩
            rcases hslot2 with ⟨rfl, _⟩
            have hnl' : ∀ (o : Obj), h₁.objs[l]? = some o → o.cell.isNum = false ∨ natClass ≠ .leaf := by
              intro o ho
              obtain ⟨o', ho', hsho⟩ := hh.getElem?_some ho
              rw [hsho.isNum_eq]
              exact hnl o' ho'
            exact ht.1 p₁ p₂ i₁ i₂ l c₁' c₂' o₁' o₂' t₁' t₂' hp₁' hp₂' ho₁' ho₂'
              (by rw [← hsh₁.ownedSlots_eq (P := P)]; exact hi₁)
              (by rw [← hsh₂.ownedSlots_eq (P := P)]; exact hi₂)
              hs₁' hs₂' hnl'
  · intro p l i o₂ r fs₂ w₂ hrp2 ho2 hcell2 hi2 hs2 hrl2 hwl2
    have hrp1 := (OwnReach_iff_sameShape hh hv p).mpr hrp2
    have hrl1 := (OwnReach_iff_sameShape hh hv l).mpr hrl2
    obtain ⟨o₁, ho1, hsh⟩ := hh.symm.getElem?_some ho2
    have hi1 : i ∉ ownedSlots P o₁.cell := by
      rw [← hsh.ownedSlots_eq (P := P)]; exact hi2
    cases hcell1 : o₁.cell with
    | ctor r₁ fs₁ =>
      have hsh' : CellSameShape (.ctor r₁ fs₁) (.ctor r fs₂) := by
        rw [← hcell1, ← hcell2]; exact hsh.symm
      rcases hsh' with ⟨rfl, hsz, hfs⟩
      obtain ⟨hlt2, hw2eq⟩ := Array.getElem?_eq_some_iff.mp hs2
      have hlt1 : i < fs₁.size := hsz ▸ hlt2
      have hs1 : fs₁[i]? = some fs₁[i] := Array.getElem?_eq_getElem hlt1
      have hwsh : ValSameShape fs₁[i] w₂ := hw2eq ▸ hfs i hlt1 hlt2
      exact ht.2 p l i o₁ r₁ fs₁ fs₁[i] hrp1 ho1 hcell1 hi1 hs1 hrl1
        ((Reach_iff_sameShape hh hwsh l).mpr hwl2)
    | num _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
      rw [hcell1, hcell2] at hsh; exact hsh

/-! ## 8b. Disjointness under `OwnTreeFull` and `renew` / `transfer` Soundness -/

/-- Reverse-indexed `OwnReach` (stepping from root to parent to child) for clean parent induction. -/
inductive OwnPath (P : Prog) (h : Heap) (v : Val) : Nat → Nat → Prop
  | root {loc cap : Nat} {t : List Nat} {o : Obj} :
      v = .ref loc cap t → h.objs[loc]? = some o → (o.cell.isNum = false ∨ natClass ≠ .leaf) →
      OwnPath P h v loc 0
  | snoc {p l c i d : Nat} {o ol : Obj} {t : List Nat} :
      OwnPath P h v p d → h.objs[p]? = some o →
      i ∈ ownedSlots P o.cell → o.cell.slot? i = some (.ref l c t) →
      h.objs[l]? = some ol → (ol.cell.isNum = false ∨ natClass ≠ .leaf) →
      OwnPath P h v l (d + 1)

theorem OwnPath.toOwnReach {P : Prog} {h : Heap} {v : Val} {l d : Nat}
    (hp : OwnPath P h v l d) : OwnReach P h v l := by
  induction hp with
  | root hv ho hn => subst hv; exact .here ho hn
  | snoc _ ho hi hs hol hnl ih =>
    exact OwnReach_step_trans ih ho hi hs (.here hol hnl)

theorem OwnPath.cons {P : Prog} {h : Heap} {v sv : Val} {loc cap i l d : Nat}
    {t : List Nat} {o : Obj}
    (hv : v = .ref loc cap t) (ho : h.objs[loc]? = some o)
    (hnn : o.cell.isNum = false ∨ natClass ≠ .leaf)
    (hi : i ∈ ownedSlots P o.cell) (hs : o.cell.slot? i = some sv)
    (hp : OwnPath P h sv l d) : OwnPath P h v l (d + 1) := by
  induction hp with
  | root hsv hol hnl =>
    subst hsv
    exact .snoc (.root hv ho hnn) ho hi hs hol hnl
  | snoc _ ho' hi' hs' hol hnl ih =>
    exact .snoc ih ho' hi' hs' hol hnl

theorem OwnReach_toOwnPath {P : Prog} {h : Heap} {v : Val} {l : Nat}
    (hr : OwnReach P h v l) : ∃ d, OwnPath P h v l d := by
  induction hr with
  | here ho hn => exact ⟨0, .root rfl ho hn⟩
  | @step loc cap t o i sv l' ho hi hs hr' ih =>
    obtain ⟨d, hp⟩ := ih
    have hnn : o.cell.isNum = false ∨ natClass ≠ .leaf := by
      left
      cases hc : o.cell with
      | num _ => simp [hc, ownedSlots] at hi
      | _ => rfl
    exact ⟨d + 1, hp.cons rfl ho hnn hi hs⟩

theorem OwnPath_parent {P : Prog} {h : Heap} {v sv : Val} {loc cap i x d : Nat}
    {t : List Nat} {o : Obj}
    (hv : v = .ref loc cap t) (ho : h.objs[loc]? = some o)
    (hnn : o.cell.isNum = false ∨ natClass ≠ .leaf)
    (hi : i ∈ ownedSlots P o.cell) (hs : o.cell.slot? i = some sv)
    (hp : OwnPath P h sv x d) :
    ∃ p k o_p c_x t_x,
      OwnReach P h v p ∧ h.objs[p]? = some o_p ∧ k ∈ ownedSlots P o_p.cell ∧
      o_p.cell.slot? k = some (.ref x c_x t_x) ∧
      ((d = 0 ∧ p = loc ∧ k = i) ∨ (∃ d', d = d' + 1 ∧ OwnPath P h sv p d')) := by
  cases hp with
  | @root lx cx tx ox hsv hox hnx =>
    subst hsv
    exact ⟨loc, i, o, cx, tx, hv ▸ .here ho hnn, ho, hi, hs, Or.inl ⟨rfl, rfl, rfl⟩⟩
  | @snoc p _ cx k d' o_p _ tx hp_p hop hk hsp _ _ =>
    exact ⟨p, k, o_p, cx, tx, hv ▸ .step ho hi hs hp_p.toOwnReach, hop, hk, hsp,
      Or.inr ⟨d', rfl, hp_p⟩⟩

/-- Distinct owned slots of an acyclic `OwnTree` have disjoint `OwnReach` sets. -/
theorem OwnTree_disjoint_slots {P : Prog} {h : Heap} {loc cap i j x : Nat}
    {t : List Nat} {o : Obj} {svi svj : Val}
    (ht : OwnTree P h (.ref loc cap t))
    (hacyc : AcyclicFrom h (.ref loc cap t))
    (ho : h.objs[loc]? = some o)
    (hi : i ∈ ownedSlots P o.cell) (hsi : o.cell.slot? i = some svi)
    (hj : j ∈ ownedSlots P o.cell) (hsj : o.cell.slot? j = some svj)
    (hne : i ≠ j)
    (hri : OwnReach P h svi x) (hrj : OwnReach P h svj x) : False := by
  have hnn : o.cell.isNum = false ∨ natClass ≠ .leaf := by
    left
    cases hc : o.cell with
    | num _ => simp [hc, ownedSlots] at hi
    | _ => rfl
  obtain ⟨di, hpi⟩ := OwnReach_toOwnPath hri
  obtain ⟨dj, hpj⟩ := OwnReach_toOwnPath hrj
  suffices ∀ d x dj, OwnPath P h svi x d → OwnPath P h svj x dj → False from
    this di x dj hpi hpj
  intro d
  induction d with
  | zero =>
    intro x dj hpi0 hpj0
    obtain ⟨p1, k1, o1, c1, t1, hrp1, ho1, hk1, hs1, hcase1⟩ :=
      OwnPath_parent rfl ho hnn hi hsi hpi0
    obtain ⟨p2, k2, o2, c2, t2, hrp2, ho2, hk2, hs2, hcase2⟩ :=
      OwnPath_parent rfl ho hnn hj hsj hpj0
    obtain ⟨ox, hox, hnx⟩ := OwnReach_nonNum hpi0.toOwnReach
    have hnl : ∀ o', h.objs[x]? = some o' → o'.cell.isNum = false ∨ natClass ≠ .leaf := by
      intro o' ho'; rw [hox] at ho'; cases ho'; exact hnx
    have ⟨hpEq, hkEq⟩ := ht.1 p1 p2 k1 k2 x c1 c2 o1 o2 t1 t2 hrp1 hrp2 ho1 ho2 hk1 hk2 hs1 hs2 hnl
    rcases hcase1 with ⟨_, hp1Loc, hk1Eq⟩ | ⟨_, hcontra, _⟩
    · rcases hcase2 with ⟨_, _, hk2Eq⟩ | ⟨d', _, hpp2⟩
      · exact hne (hk1Eq.symm.trans (hkEq.trans hk2Eq))
      · rw [← hpEq, hp1Loc] at hpp2
        exact hacyc loc o svj .here ho (mem_vals_of_ownedSlot hj hsj) (OwnReach_toReach hpp2.toOwnReach)
    · cases hcontra
  | succ d' ih =>
    intro x dj hpiS hpj0
    obtain ⟨p1, k1, o1, c1, t1, hrp1, ho1, hk1, hs1, hcase1⟩ :=
      OwnPath_parent rfl ho hnn hi hsi hpiS
    obtain ⟨p2, k2, o2, c2, t2, hrp2, ho2, hk2, hs2, hcase2⟩ :=
      OwnPath_parent rfl ho hnn hj hsj hpj0
    obtain ⟨ox, hox, hnx⟩ := OwnReach_nonNum hpiS.toOwnReach
    have hnl : ∀ o', h.objs[x]? = some o' → o'.cell.isNum = false ∨ natClass ≠ .leaf := by
      intro o' ho'; rw [hox] at ho'; cases ho'; exact hnx
    have ⟨hpEq, _⟩ := ht.1 p1 p2 k1 k2 x c1 c2 o1 o2 t1 t2 hrp1 hrp2 ho1 ho2 hk1 hk2 hs1 hs2 hnl
    rcases hcase1 with ⟨hcontra, _, _⟩ | ⟨d1, hd1, hpp1⟩
    · cases hcontra
    · cases hd1
      rcases hcase2 with ⟨_, hp2Loc, _⟩ | ⟨d2, _, hpp2⟩
      · rw [hpEq, hp2Loc] at hpp1
        exact hacyc loc o svi .here ho (mem_vals_of_ownedSlot hi hsi) (OwnReach_toReach hpp1.toOwnReach)
      · subst hpEq
        exact ih p1 d2 hpp1 hpp2

/-- If `w` is an owned slot disjoint from `svi`'s `OwnReach`, then `Reach h w` is
    completely disjoint from `OwnReach P h svi` (using `OwnTreeFull` for `@shared` fields). -/
theorem OwnTreeFull_reach_disjoint_of_ownReach_disjoint
    {P : Prog} {h : Heap} {v svi u : Val} {l : Nat}
    (ht : OwnTreeFull P h v)
    (huSub : ∀ x, OwnReach P h u x → OwnReach P h v x)
    (hdisj : ∀ x, OwnReach P h svi x → ¬ OwnReach P h u x)
    (hsviSub : ∀ x, OwnReach P h svi x → OwnReach P h v x)
    (hrl : OwnReach P h svi l) (hrul : Reach h u l) : False := by
  induction hrul with
  | @here lu cu tu =>
    obtain ⟨ol, hol, hnl⟩ := OwnReach_nonNum hrl
    exact hdisj lu hrl (.here hol hnl)
  | @step lu cu tu ou w l' hou hmw hrwl ih =>
    have hnn : ou.cell.isNum = false ∨ natClass ≠ .leaf := by
      left
      cases hc : ou.cell with
      | num _ => simp [hc, Cell.vals] at hmw
      | _ => rfl
    have hOwnU : OwnReach P h (.ref lu cu tu) lu := .here hou hnn
    have hOwnV : OwnReach P h v lu := huSub lu hOwnU
    cases hcell : ou.cell with
    | num _ => rw [hcell] at hmw; simp [Cell.vals] at hmw
    | str _ => rw [hcell] at hmw; simp [Cell.vals] at hmw
    | ctor r fs =>
      rw [hcell] at hmw
      obtain ⟨m, hm, hwEq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hmw)
      have hsm : fs[m]? = some w := hwEq ▸ Array.getElem?_eq_getElem hm
      by_cases hown : m ∈ ownedSlots P ou.cell
      · have hslot : ou.cell.slot? m = some w := by simp [hcell, Cell.slot?, hsm]
        exact ih
          (fun x hx => huSub x (.step hou hown hslot hx))
          (fun x hxi hxw => hdisj x hxi (.step hou hown hslot hxw))
          hrl
      · exact ht.2 lu l' m ou r fs w hOwnV hou hcell hown hsm (hsviSub l' hrl) hrwl
    | clo env p res rc fvs body =>
      rw [hcell] at hmw
      simp only [Cell.vals, List.mem_filterMap] at hmw
      rcases hmw with ⟨m, hm, hmap⟩
      have hown : m ∈ ownedSlots P ou.cell := by simp [hcell, ownedSlots, hm]
      have hslot : ou.cell.slot? m = some w := by simpa [hcell, Cell.slot?] using hmap
      exact ih
        (fun x hx => huSub x (.step hou hown hslot hx))
        (fun x hxi hxw => hdisj x hxi (.step hou hown hslot hxw))
        hrl
    | pap r as =>
      rw [hcell] at hmw
      obtain ⟨m, hm, hwEq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hmw)
      have hown : m ∈ ownedSlots P ou.cell := by simp [hcell, ownedSlots, hm]
      have hslot : ou.cell.slot? m = some w := by
        simp [hcell, Cell.slot?, hwEq ▸ Array.getElem?_eq_getElem hm]
      exact ih
        (fun x hx => huSub x (.step hou hown hslot hx))
        (fun x hxi hxw => hdisj x hxi (.step hou hown hslot hxw))
        hrl
    | once t sp =>
      rw [hcell] at hmw
      simp only [Cell.vals, List.mem_singleton] at hmw
      subst hmw
      have hown : 0 ∈ ownedSlots P ou.cell := by simp [hcell, ownedSlots]
      have hslot : ou.cell.slot? 0 = some w := by simp [hcell, Cell.slot?]
      exact ih
        (fun x hx => huSub x (.step hou hown hslot hx))
        (fun x hxi hxw => hdisj x hxi (.step hou hown hslot hxw))
        hrl

/-- Under `OwnTreeFull` + `AcyclicFrom`, for any owned slot `i` (`slot? i = some svi`)
    and any other value `w` held at slot `j ≠ i` (owned OR `@shared`), `Reach h w` is
    completely disjoint from `OwnReach P h svi`. -/
theorem OwnTreeFull_other_slot_disjoint {P : Prog} {h : Heap} {loc cap i j l : Nat}
    {t : List Nat} {o : Obj} {svi w : Val}
    (ht : OwnTreeFull P h (.ref loc cap t))
    (hacyc : AcyclicFrom h (.ref loc cap t))
    (ho : h.objs[loc]? = some o)
    (hi : i ∈ ownedSlots P o.cell) (hsi : o.cell.slot? i = some svi)
    (hj : o.cell.slot? j = some w) (hne : j ≠ i)
    (hLiveSlot : j ∈ ownedSlots P o.cell ∨ ∃ r fs, o.cell = .ctor r fs ∧ fs[j]? = some w)
    (hrl : OwnReach P h svi l) : ¬ Reach h w l := by
  have hnn : o.cell.isNum = false ∨ natClass ≠ .leaf := by
    left
    cases hc : o.cell with
    | num _ => simp [hc, ownedSlots] at hi
    | _ => rfl
  rcases hLiveSlot with hjOwn | ⟨r, fs, hcell, hfsj⟩
  · intro hrwl
    exact OwnTreeFull_reach_disjoint_of_ownReach_disjoint ht
      (fun x hx => .step ho hjOwn hj hx)
      (fun x hxi hxj => OwnTree_disjoint_slots ht hacyc ho hi hsi hjOwn hj (Ne.symm hne) hxi hxj)
      (fun x hx => .step ho hi hsi hx)
      hrl hrwl
  · by_cases hjOwn : j ∈ ownedSlots P o.cell
    · intro hrwl
      exact OwnTreeFull_reach_disjoint_of_ownReach_disjoint ht
        (fun x hx => .step ho hjOwn hj hx)
        (fun x hxi hxj => OwnTree_disjoint_slots ht hacyc ho hi hsi hjOwn hj (Ne.symm hne) hxi hxj)
        (fun x hx => .step ho hi hsi hx)
        hrl hrwl
    · exact ht.2 loc l j o r fs w (.here ho hnn) ho hcell hjOwn hfsj (.step ho hi hsi hrl)

/-- Explicit loop helper matching the `for i in ownedSlots P o.cell` loop inside `renew`. -/
def renewLoop (P : Prog) (n : Nat) : List Nat → Cell → M Cell
  | [], cell => pure cell
  | i :: rest, cell =>
    match cell.slot? i with
    | some sv => do
      let sv' ← renew P n sv
      renewLoop P n rest (cell.setSlot i sv')
    | none => renewLoop P n rest cell

theorem forIn_list_renewLoop (P : Prog) (n : Nat) (xs : List Nat) (cell : Cell) (st : St) :
    (forIn (m := M) xs cell
      (fun i __s =>
        match __s.slot? i with
        | some sv => do
          let __do_lift ← renew P n sv
          pure (ForInStep.yield (__s.setSlot i __do_lift))
        | none => pure (ForInStep.yield __s))).run st =
    (renewLoop P n xs cell).run st := by
  induction xs generalizing cell st with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.forIn_cons, renewLoop]
    cases cell.slot? i with
    | none =>
      rw [M_bind_run, M_pure_run]
      exact ih cell st
    | some sv =>
      rw [M_bind_run, M_bind_run, M_bind_run]
      cases (renew P n sv).run st with
      | error e => rfl
      | ok p =>
        simp only [M_pure_run]
        exact ih (cell.setSlot i p.1) p.2

/-- **Crown jewel: `renew` exclusivity & revocation theorem.**
    Under `CapsOk`, `DeepLive`, `AcyclicFrom`, and `OwnTreeFull`, `renew P n v`
    never violates or gets stuck, and on success:
    * preserves `regions`, `nextRegion`, `statics`, `strs`, and `heap.objs.size`;
    * preserves every location outside `OwnReach P st.heap v` untouched;
    * preserves heap & value shape (`HeapSameShape`, `ValSameShape`);
    * bumps caps only on `OwnReach P st.heap v` while maintaining `CapsOk` and `DeepLive`! -/
theorem renew_spec (P : Prog) (n : Nat) :
    ∀ (v : Val) (st : St),
      CapsOk st.heap → DeepLive st.heap v → AcyclicFrom st.heap v → OwnTreeFull P st.heap v →
      (renew P n v).run st = .error .outOfFuel ∨
      ∃ v' st', (renew P n v).run st = .ok (v', st') ∧
        st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
        st'.statics = st.statics ∧ st'.strs = st.strs ∧
        st'.heap.objs.size = st.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        CapsOk st'.heap ∧
        HeapSameShape st.heap st'.heap ∧
        ValSameShape v v' ∧
        DeepLive st'.heap v' ∧
        PreservesLocs (fun l => ¬ OwnReach P st.heap v l) st.heap st'.heap := by
  induction n with
  | zero => intro v st _ _ _ _; left; rfl
  | succ n ih =>
    intro v st hc hdl hacyc htree
    cases v with
    | imm i =>
      right
      exact ⟨.imm i, st, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc,
        HeapSameShape.refl _, ValSameShape.refl _, hdl, PreservesLocs.refl _ _⟩
    | ref loc cap t =>
      obtain ⟨o, ho, hcap⟩ := hdl.self.1
      have hlocLt : loc < st.heap.objs.size := (Array.getElem?_eq_some_iff.mp ho).1
      cases hnum : o.cell.isNum with
      | true =>
        right
        refine ⟨.ref loc cap t, st, ?_, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc,
          HeapSameShape.refl _, ValSameShape.refl _, hdl, PreservesLocs.refl _ _⟩
        unfold renew
        rw [M_bind_run, obj_ok ho]
        simp only [hcap, beq_self_eq_true, ↓reduceIte]
        rw [M_bind_run, isLeaf_ok hdl.self.1]
        simp only [ho, hnum, ↓reduceIte]
        rfl
      | false =>
        have hnn : o.cell.isNum = false ∨ natClass ≠ .leaf := Or.inl hnum
        let cap' := st.heap.nextCap
        let st1 : St := { st with
          heap := { objs := st.heap.objs.set! loc { o with cap := cap' },
                    nextCap := cap' + 1 } }
        have hsz1 : st1.heap.objs.size = st.heap.objs.size := by simp [st1, Array.set!]
        have hc1 : CapsOk st1.heap := by
          intro l o' ho'
          by_cases hloc : l = loc
          · subst hloc
            simp only [st1, Array.set!, Array.getElem?_setIfInBounds_self, hlocLt, ↓reduceIte,
              Option.some.injEq] at ho'
            subst ho'
            dsimp only [st1, cap']; omega
          · simp only [st1, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hloc)] at ho'
            have := hc l o' ho'
            dsimp only [st1, cap']; omega
        have hsh1 : HeapSameShape st.heap st1.heap := by
          have := HeapSameShape.setObj (o' := { o with cap := cap' }) ho (CellSameShape.refl o.cell)
          exact ⟨this.1, this.2⟩
        have hloc1 : st1.heap.objs[loc]? = some { o with cap := cap' } := by
          simp [st1, Array.set!, hlocLt]
        have hpres1 : PreservesLocs (fun l => l ≠ loc) st.heap st1.heap := by
          intro l hne
          simp [st1, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
        -- Every live value held inside `o.cell` does not reach `loc` (by acyclicity), so it is DeepLive in `st1`!
        have hvalsLive1 : ∀ w ∈ o.cell.vals, DeepLive st1.heap w := by
          intro w hw
          have hnoLoc : ∀ l, Reach st.heap w l → l ≠ loc := by
            intro l hrl hEq; subst hEq
            exact hacyc l o w .here ho hw hrl
          exact (DeepLive_congr (hpres1.mono hnoLoc)).mpr (hdl.sub (HeldBy_of_mem_vals ho hw))
        -- Loop invariant over any suffix `xs` of `ownedSlots P o.cell`:
        have hLoop : ∀ (xs : List Nat) (cellk : Cell) (stk : St),
            (∀ i ∈ xs, i ∈ ownedSlots P o.cell) →
            stk.regions = st.regions → stk.nextRegion = st.nextRegion →
            stk.statics = st.statics → stk.strs = st.strs →
            stk.heap.objs.size = st.heap.objs.size →
            cap' + 1 ≤ stk.heap.nextCap →
            CapsOk stk.heap →
            HeapSameShape st.heap stk.heap →
            CellSameShape o.cell cellk →
            stk.heap.objs[loc]? = some { o with cap := cap' } →
            PreservesLocs (fun l => ¬ OwnReach P st.heap (.ref loc cap t) l) st.heap stk.heap →
            (∀ w ∈ cellk.vals, DeepLive stk.heap w) →
            (renewLoop P n xs cellk).run stk = .error .outOfFuel ∨
            ∃ cellf stf, (renewLoop P n xs cellk).run stk = .ok (cellf, stf) ∧
              stf.regions = st.regions ∧ stf.nextRegion = st.nextRegion ∧
              stf.statics = st.statics ∧ stf.strs = st.strs ∧
              stf.heap.objs.size = st.heap.objs.size ∧
              cap' + 1 ≤ stf.heap.nextCap ∧
              CapsOk stf.heap ∧
              HeapSameShape st.heap stf.heap ∧
              CellSameShape o.cell cellf ∧
              stf.heap.objs[loc]? = some { o with cap := cap' } ∧
              PreservesLocs (fun l => ¬ OwnReach P st.heap (.ref loc cap t) l) st.heap stf.heap ∧
              (∀ w ∈ cellf.vals, DeepLive stf.heap w) := by
          intro xs
          induction xs with
          | nil =>
            intro cellk stk _ h1 h2 h3 h4 hsz hcapk hck hshk hcellk hlock hpresk hlivek
            right
            exact ⟨cellk, stk, rfl, h1, h2, h3, h4, hsz, hcapk, hck, hshk, hcellk, hlock, hpresk, hlivek⟩
          | cons i rest ihLoop =>
            intro cellk stk hxs h1 h2 h3 h4 hsz hcapk hck hshk hcellk hlock hpresk hlivek
            have hiOwn : i ∈ ownedSlots P o.cell := hxs i (List.mem_cons_self ..)
            have hiOwnK : i ∈ ownedSlots P cellk := by rw [← hcellk.ownedSlots_eq]; exact hiOwn
            unfold renewLoop
            cases hsk : cellk.slot? i with
            | none =>
              exact ihLoop cellk stk (fun j hj => hxs j (List.mem_cons_of_mem _ hj))
                h1 h2 h3 h4 hsz hcapk hck hshk hcellk hlock hpresk hlivek
            | some sv =>
              have hslotOrig := hcellk.slot? i
              cases hso : o.cell.slot? i with
              | none => simp [hso, hsk] at hslotOrig
              | some sv0 =>
                simp only [hso, hsk] at hslotOrig
                have hsvLive : DeepLive stk.heap sv := hlivek sv (mem_vals_of_ownedSlot hiOwnK hsk)
                have hsvAcyc : AcyclicFrom stk.heap sv :=
                  AcyclicFrom_of_sameShape hshk hslotOrig
                    (hacyc.sub (HeldBy_of_mem_vals ho (mem_vals_of_ownedSlot hiOwn hso)))
                have hsvTree : OwnTreeFull P stk.heap sv :=
                  OwnTreeFull_of_sameShape hshk hslotOrig (htree.sub rfl ho hiOwn hso)
                rcases ih sv stk hck hsvLive hsvAcyc hsvTree with hOOF | ⟨sv', stk', hrun,
                    h1', h2', h3', h4', hsz', hcap', hck', hsh', hsvsh, hsvLive', hpres'⟩
                · left
                  rw [M_bind_run, hOOF]
                · have hshTotal : HeapSameShape st.heap stk'.heap := hshk.trans hsh'
                  have hcellNext : CellSameShape o.cell (cellk.setSlot i sv') :=
                    hcellk.trans (CellSameShape.setSlot_right hsk hsvsh)
                  have hnoLocSv : ¬ OwnReach P stk.heap sv loc := by
                    intro hlocOwn
                    have hlocOrig := (OwnReach_iff_sameShape hshk hslotOrig loc).mpr hlocOwn
                    exact hacyc loc o sv0 .here ho (mem_vals_of_ownedSlot hiOwn hso)
                      (OwnReach_toReach hlocOrig)
                  have hlock' : stk'.heap.objs[loc]? = some { o with cap := cap' } := by
                    rw [hpres' loc hnoLocSv, hlock]
                  have hpresTotal : PreservesLocs (fun l => ¬ OwnReach P st.heap (.ref loc cap t) l)
                      st.heap stk'.heap := by
                    intro l hnotOwn
                    have hnotSv : ¬ OwnReach P stk.heap sv l := by
                      intro hlSv
                      have hlSv0 := (OwnReach_iff_sameShape hshk hslotOrig l).mpr hlSv
                      exact hnotOwn (.step ho hiOwn hso hlSv0)
                    rw [hpres' l hnotSv, hpresk l hnotOwn]
                  -- Show every value in `(cellk.setSlot i sv').vals` is DeepLive in `stk'`!
                  have hliveNext : ∀ w ∈ (cellk.setSlot i sv').vals, DeepLive stk'.heap w := by
                    intro w hw
                    -- Locate which slot `j` holds `w` in `cellk.setSlot i sv'`
                    have hSlotCase : w = sv' ∨
                        ∃ j, j ≠ i ∧ cellk.slot? j = some w ∧
                          (j ∈ ownedSlots P cellk ∨ ∃ r fs, cellk = .ctor r fs ∧ fs[j]? = some w) := by
                      cases hcK : cellk with
                      | ctor r fs =>
                        rw [hcK] at hw
                        simp only [Cell.setSlot, Cell.vals, Array.set!, Array.mem_toList_iff] at hw
                        obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hw
                        have hj' : j < fs.size := by simpa using hj
                        by_cases hji : j = i
                        · subst hji; left; simp [Array.getElem_setIfInBounds_self hj]
                        · right
                          rw [Array.getElem_setIfInBounds_ne hj' (Ne.symm hji)]
                          exact ⟨j, hji, by simp [Cell.slot?, Array.getElem?_eq_getElem hj'],
                            Or.inr ⟨r, fs, rfl, Array.getElem?_eq_getElem hj'⟩⟩
                      | clo env p res rc fvs body =>
                        rw [hcK] at hw
                        simp only [Cell.setSlot, Cell.vals, List.mem_filterMap] at hw
                        rcases hw with ⟨j, hj, hmap⟩
                        by_cases hji : j = i
                        · subst hji
                          rw [hcK] at hsk
                          simp only [Cell.slot?] at hsk
                          obtain ⟨bd, hbd, _⟩ := Option.map_eq_some_iff.mp hsk
                          rw [setBnd_getElem?_same hbd] at hmap
                          simp only [Option.map_some, Option.some.injEq] at hmap
                          exact Or.inl hmap.symm
                        · rw [setBnd_getElem?_other hji] at hmap
                          exact Or.inr ⟨j, hji, by simpa [Cell.slot?] using hmap,
                            Or.inl (by simp [ownedSlots, hj])⟩
                      | pap r as =>
                        rw [hcK] at hw
                        simp only [Cell.setSlot, Cell.vals, Array.set!, Array.mem_toList_iff] at hw
                        obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hw
                        have hj' : j < as.size := by simpa using hj
                        by_cases hji : j = i
                        · subst hji; left; simp [Array.getElem_setIfInBounds_self hj]
                        · right
                          rw [Array.getElem_setIfInBounds_ne hj' (Ne.symm hji)]
                          exact ⟨j, hji, by simp [Cell.slot?, Array.getElem?_eq_getElem hj'],
                            Or.inl (by simp [ownedSlots, hj'])⟩
                      | once t0 sp0 =>
                        rw [hcK] at hw hsk
                        cases i with
                        | zero =>
                          simp only [Cell.setSlot, Cell.vals, List.mem_singleton] at hw
                          exact Or.inl hw
                        | succ _ => simp [Cell.slot?] at hsk
                      | num _ | str _ => rw [hcK] at hsk; simp [Cell.slot?] at hsk
                    rcases hSlotCase with rfl | ⟨j, hji, hsjK, hLiveJ⟩
                    · exact hsvLive'
                    · have hwMemK : w ∈ cellk.vals := by
                        rcases hLiveJ with hjOwnK | ⟨r, fs, hcK, hfsj⟩
                        · exact mem_vals_of_ownedSlot hjOwnK hsjK
                        · rw [hcK]; exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hfsj)
                      have hwLiveK : DeepLive stk.heap w := hlivek w hwMemK
                      -- Show `Reach stk.heap w` is disjoint from `OwnReach P stk.heap sv`
                      have hslotJOrig := hcellk.slot? j
                      cases hsjO : o.cell.slot? j with
                      | none => simp [hsjO, hsjK] at hslotJOrig
                      | some w0 =>
                        simp only [hsjO, hsjK] at hslotJOrig
                        have hLiveJOrig : j ∈ ownedSlots P o.cell ∨
                            ∃ r fs, o.cell = .ctor r fs ∧ fs[j]? = some w0 := by
                          rcases hLiveJ with hjOwnK | ⟨r, fsK, hcK, hfsjK⟩
                          · exact Or.inl (by rw [hcellk.ownedSlots_eq]; exact hjOwnK)
                          · cases hcO : o.cell with
                            | ctor rO fsO =>
                              have hshC : CellSameShape (.ctor rO fsO) (.ctor r fsK) := by
                                rw [← hcO, ← hcK]; exact hcellk
                              rcases hshC with ⟨rfl, _, _⟩
                              simp only [hcO, Cell.slot?] at hsjO
                              exact Or.inr ⟨rO, fsO, rfl, hsjO⟩
                            | num _ | str _ | clo _ _ _ _ _ _ | pap _ _ | once _ _ =>
                              rw [hcO, hcK] at hcellk; exact False.elim hcellk
                        have hdisjW : ∀ l, Reach stk.heap w l → ¬ OwnReach P stk.heap sv l := by
                          intro l hrlW hrlSv
                          have hrlW0 := (Reach_iff_sameShape hshk hslotJOrig l).mpr hrlW
                          have hrlSv0 := (OwnReach_iff_sameShape hshk hslotOrig l).mpr hrlSv
                          exact OwnTreeFull_other_slot_disjoint htree hacyc ho hiOwn hso
                            hsjO hji hLiveJOrig hrlSv0 hrlW0
                        exact (DeepLive_congr (hpres'.mono hdisjW)).mpr hwLiveK
                  have hNext := ihLoop (cellk.setSlot i sv') stk'
                    (fun j hj => hxs j (List.mem_cons_of_mem _ hj))
                    (h1'.trans h1) (h2'.trans h2) (h3'.trans h3) (h4'.trans h4)
                    (hsz'.trans hsz) (Nat.le_trans hcapk hcap') hck' hshTotal hcellNext
                    hlock' hpresTotal hliveNext
                  rcases hNext with hOOF2 | ⟨cellf, stf, hrun2, rest⟩
                  · left
                    rw [M_bind_run, hrun]
                    exact hOOF2
                  · right
                    refine ⟨cellf, stf, ?_, rest⟩
                    rw [M_bind_run, hrun]
                    exact hrun2
        -- Apply `hLoop` to `ownedSlots P o.cell`, `o.cell`, `st1`
        rcases hLoop (ownedSlots P o.cell) o.cell st1 (fun _ h => h)
            rfl rfl rfl rfl hsz1 (Nat.le_refl _) hc1 hsh1 (CellSameShape.refl _) hloc1
            (hpres1.mono (fun l hnot hEq => hnot (hEq.symm ▸ .here ho hnn)))
            hvalsLive1 with hOOF | ⟨cellf, stf, hrunLoop, h1f, h2f, h3f, h4f, hszf, hcapf,
              hcf, hshf, hcellf, hlocf, hpresf, hlivef⟩
        · left
          unfold renew
          rw [M_bind_run, obj_ok ho]
          simp only [hcap, beq_self_eq_true, ↓reduceIte]
          rw [M_bind_run, isLeaf_ok hdl.self.1]
          simp only [ho, hnum, Bool.false_eq_true, ↓reduceIte]
          rw [M_bind_run, freshCap_run]
          dsimp only
          rw [M_bind_run, setObj_run]
          dsimp only
          rw [M_bind_run]
          erw [forIn_list_renewLoop]
          rw [hOOF]
        · let stEnd : St := { stf with heap := { stf.heap with objs := stf.heap.objs.set! loc ⟨cellf, cap'⟩ } }
          have hlocLtF : loc < stf.heap.objs.size := hszf ▸ hlocLt
          have hszEnd : stEnd.heap.objs.size = st.heap.objs.size := by
            simp [stEnd, Array.set!, hszf]
          have hcEnd : CapsOk stEnd.heap := by
            intro l o' ho'
            by_cases hloc : l = loc
            · subst hloc
              simp only [stEnd, Array.set!, Array.getElem?_setIfInBounds_self, hlocLtF, ↓reduceIte,
                Option.some.injEq] at ho'
              subst ho'
              dsimp only [stEnd]; omega
            · simp only [stEnd, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hloc)] at ho'
              exact hcf l o' ho'
          have hshEnd : HeapSameShape st.heap stEnd.heap :=
            hshf.trans (HeapSameShape.setObj hlocf hcellf)
          have hpresEnd : PreservesLocs (fun l => ¬ OwnReach P st.heap (.ref loc cap t) l)
              st.heap stEnd.heap := by
            intro l hnot
            have hne : l ≠ loc := fun hEq => hnot (hEq.symm ▸ .here ho hnn)
            simp only [stEnd, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
            exact hpresf l hnot
          have hlocEnd : stEnd.heap.objs[loc]? = some ⟨cellf, cap'⟩ := by
            simp [stEnd, Array.set!, hlocLtF]
          have hpresLocEnd : PreservesLocs (fun l => l ≠ loc) stf.heap stEnd.heap := by
            intro l hne
            simp [stEnd, Array.set!, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
          have hvalsEnd : ∀ w ∈ cellf.vals, DeepLive stEnd.heap w := by
            intro w hw
            have hnoLoc : ∀ l, Reach stf.heap w l → l ≠ loc := by
              intro l hrl hEq; subst hEq
              obtain ⟨w0, hw0, hwsh⟩ := hcellf.symm.vals_fwd hw
              exact hacyc l o w0 .here ho hw0 ((Reach_iff_sameShape hshf hwsh.symm l).mpr hrl)
            exact (DeepLive_congr (hpresLocEnd.mono hnoLoc)).mpr (hlivef w hw)
          have hdlEnd : DeepLive stEnd.heap (.ref loc cap' t) := by
            intro w hw
            rcases hw with rfl | ⟨l, ol, hr, hol, hm⟩
            · refine ⟨⟨⟨cellf, cap'⟩, hlocEnd, rfl⟩, fun o' m ho' hcm => ?_⟩
              rw [hlocEnd] at ho'; cases ho'
              dsimp only at hcm
              have := hcellf.isNum_eq
              rw [hnum, hcm] at this; simp [Cell.isNum] at this
            · cases hr with
              | here =>
                rw [hlocEnd] at hol; cases hol
                exact (hvalsEnd w hm).self
              | step ho' hm' hr' =>
                rw [hlocEnd] at ho'; cases ho'
                exact (hvalsEnd _ hm') w (Or.inr ⟨l, ol, hr', hol, hm⟩)
          right
          refine ⟨.ref loc cap' t, stEnd, ?_, h1f, h2f, h3f, h4f, hszEnd,
            Nat.le_trans (Nat.le_succ _) hcapf, hcEnd, hshEnd, ⟨rfl, rfl⟩, hdlEnd, hpresEnd⟩
          unfold renew
          rw [M_bind_run, obj_ok ho]
          simp only [hcap, beq_self_eq_true, ↓reduceIte]
          rw [M_bind_run, isLeaf_ok hdl.self.1]
          simp only [ho, hnum, Bool.false_eq_true, ↓reduceIte]
          rw [M_bind_run, freshCap_run]
          dsimp only
          rw [M_bind_run, setObj_run]
          dsimp only
          rw [M_bind_run]
          erw [forIn_list_renewLoop]
          rw [hrunLoop]
          rfl

/-- **`transfer` soundness theorem** (from `renew_spec` + `OpenUnder`). -/
theorem transfer_spec {P : Prog} {fuel : Nat} {toBorrowed : Bool} {v : Val} {st : St}
    (hc : CapsOk st.heap) (hdl : DeepLive st.heap v)
    (hacyc : AcyclicFrom st.heap v) (htree : OwnTreeFull P st.heap v)
    (hconf : toBorrowed = false → OpenUnder st.regions [] v) :
    (transfer P fuel toBorrowed v).run st = .error .outOfFuel ∨
    ∃ v' st', (transfer P fuel toBorrowed v).run st = .ok (v', st') ∧
      st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
      st'.statics = st.statics ∧ st'.strs = st.strs ∧
      st'.heap.objs.size = st.heap.objs.size ∧
      st.heap.nextCap ≤ st'.heap.nextCap ∧
      CapsOk st'.heap ∧
      HeapSameShape st.heap st'.heap ∧
      ValSameShape v v' ∧
      DeepLive st'.heap v' ∧
      PreservesLocs (fun l => ¬ OwnReach P st.heap v l) st.heap st'.heap := by
  have hdoRenew :
      (renew P fuel v).run st = .error .outOfFuel ∨
      ∃ v' st', (renew P fuel v).run st = .ok (v', st') ∧
        st'.regions = st.regions ∧ st'.nextRegion = st.nextRegion ∧
        st'.statics = st.statics ∧ st'.strs = st.strs ∧
        st'.heap.objs.size = st.heap.objs.size ∧
        st.heap.nextCap ≤ st'.heap.nextCap ∧
        CapsOk st'.heap ∧
        HeapSameShape st.heap st'.heap ∧
        ValSameShape v v' ∧
        DeepLive st'.heap v' ∧
        PreservesLocs (fun l => ¬ OwnReach P st.heap v l) st.heap st'.heap :=
    renew_spec P fuel v st hc hdl hacyc htree
  cases v with
  | imm i =>
    rcases hdoRenew with hOOF | ⟨v', st', hrun, rest⟩
    · left
      unfold transfer
      rw [M_bind_run, isLeaf_ok hdl.self.1]
      dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [M_bind_run, confinedOpen_run]
      simp only [Val.taint, List.any_nil, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact hOOF
    · right
      refine ⟨v', st', ?_, rest⟩
      unfold transfer
      rw [M_bind_run, isLeaf_ok hdl.self.1]
      dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [M_bind_run, confinedOpen_run]
      simp only [Val.taint, List.any_nil, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact hrun
  | ref loc cap t =>
    obtain ⟨o, ho, hcap⟩ := hdl.self.1
    cases hnum : o.cell.isNum with
    | true =>
      right
      refine ⟨.ref loc cap t, st, ?_, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, hc,
        HeapSameShape.refl _, ValSameShape.refl _, hdl, PreservesLocs.refl _ _⟩
      unfold transfer
      rw [M_bind_run, isLeaf_ok hdl.self.1]
      simp only [ho, hnum, ↓reduceIte]
      rfl
    | false =>
      have hcondFalse : ((!toBorrowed) && (Val.ref loc cap t).taint.any (fun s => st.regions.contains s)) = false := by
        cases toBorrowed with
        | true => rfl
        | false =>
          simp only [Bool.not_false, Bool.true_and]
          exact (hconf rfl).confinedOpen_false
      rcases hdoRenew with hOOF | ⟨v', st', hrun, rest⟩
      · left
        unfold transfer
        rw [M_bind_run, isLeaf_ok hdl.self.1]
        simp only [ho, hnum, Bool.false_eq_true, ↓reduceIte]
        rw [M_bind_run, confinedOpen_run]
        dsimp only
        rw [hcondFalse]
        simpa using hOOF
      · right
        refine ⟨v', st', ?_, rest⟩
        unfold transfer
        rw [M_bind_run, isLeaf_ok hdl.self.1]
        simp only [ho, hnum, Bool.false_eq_true, ↓reduceIte]
        rw [M_bind_run, confinedOpen_run]
        dsimp only
        rw [hcondFalse]
        simpa using hrun

end IxC.Resource.Proof
