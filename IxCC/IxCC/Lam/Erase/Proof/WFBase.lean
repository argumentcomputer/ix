import IxCC.Lam.Erase.Proof.Reg
import IxCC.Lam.WellFormed

/-! # Well-formedness of erased terms: the pieces

Contexts whose levels lie below their depth (`CxOk`), well-formedness of
the shapes erasure builds (`Term.apps`, `Term.lams`, `wrapLets`,
`setModes`), kept-field counting (`rank`), and what `ProgWF` says of
`alias`: a constructor and the one it is retagged as have the same
kept-field count, and two constructors of one inductive with the same key
are the same. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

/-! ## Contexts -/

/-- Every level of the context map lies below the depth. -/
def CxOk (cx : Cx) : Prop := ∀ (i l : Nat), cx.ctx[i]? = some (some l) → l < cx.depth

theorem CxOk.bind {cx : Cx} (h : CxOk cx) : CxOk cx.bind := by
  intro i l hi
  cases i with
  | zero =>
    simp only [Cx.bind, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    exact Nat.lt_succ_self _
  | succ i =>
    simp only [Cx.bind, List.getElem?_cons_succ] at hi
    exact Nat.lt_succ_of_lt (h i l hi)

theorem CxOk.extra {cx : Cx} (h : CxOk cx) (n : Nat) : CxOk (cx.extra n) :=
  fun i l hi => Nat.lt_of_lt_of_le (h i l hi) (Nat.le_add_right _ _)

theorem CxOk.under {cx : Cx} (h : CxOk cx) {slots : List (Option Nat)}
    (hs : ∀ l, some l ∈ slots → l < cx.depth) : CxOk (cx.under slots) := by
  intro i l hi
  simp only [Cx.under] at hi ⊢
  rw [List.getElem?_append] at hi
  split at hi
  · exact hs l (List.mem_reverse.1 (List.mem_of_getElem? hi))
  · exact h _ l hi

/-! ## Terms -/

variable {S : Sig}

theorem wfList_iff {d : Nat} : ∀ {ts : List Term}, Term.WFList S d ts ↔ ∀ t ∈ ts, Term.WF S d t
  | [] => by simp [Term.WFList]
  | t :: ts => by simp [Term.WFList, wfList_iff (ts := ts)]

theorem wf_lvl {cx : Cx} {l : Nat} (h : l < cx.depth) : Term.WF S cx.depth (cx.lvl l) := by
  show cx.depth - 1 - l < cx.depth
  omega

theorem wf_apps {d : Nat} : ∀ {h : Term} {args : List (Term × Mode)}, Term.WF S d h →
    (∀ a ∈ args, Term.WF S d a.1) → Term.WF S d (Term.apps h args)
  | _, [], hh, _ => hh
  | _, (a, m) :: args, hh, ha => by
    unfold Term.apps
    rw [List.foldl_cons]
    exact wf_apps (args := args) ⟨hh, ha _ List.mem_cons_self⟩
      fun b hb => ha b (List.mem_cons_of_mem _ hb)

theorem wf_lams : ∀ {ms : List Mode} {d : Nat} {b : Term}, Term.WF S (d + ms.length) b →
    Term.WF S d (Term.lams ms b)
  | [], _, _, h => h
  | m :: ms, d, _, h => by
    unfold Term.lams
    rw [List.foldr_cons]
    show Term.WF S (d + 1) _
    exact wf_lams (ms := ms) (by simpa [Nat.add_assoc, Nat.add_comm 1] using h)

theorem wf_wrapLets : ∀ {lets : List Term} {d : Nat} {b : Term},
    (∀ (i : Nat) v, lets[i]? = some v → Term.WF S (d + i) v) → Term.WF S (d + lets.length) b →
    Term.WF S d (Erase.wrapLets lets b)
  | [], _, _, _, hb => hb
  | v :: lets, d, _, hv, hb => by
    unfold Erase.wrapLets
    rw [List.foldr_cons]
    refine ⟨by simpa using hv 0 v rfl, ?_⟩
    exact wf_wrapLets (lets := lets) (fun i w hw => by
        have := hv (i + 1) w (by simpa using hw)
        rwa [← Nat.add_assoc, Nat.add_right_comm] at this)
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)

theorem wf_setModes : ∀ {ms : List Mode} {t t' : Term} {d : Nat}, Term.setModes ms t = some t' →
    Term.WF S d t → Term.WF S d t'
  | [], _, _, _, e, h => by cases e; exact h
  | m :: ms, .lam m' c b, t', d, e, h => by
    simp only [Term.setModes, Option.map_eq_some_iff] at e
    obtain ⟨b', hb, rfl⟩ := e
    exact wf_setModes (d := d + 1) hb h
  | _ :: _, .var _, _, _, e, _ | _ :: _, .glob _, _, _, e, _ | _ :: _, .app .., _, _, e, _
  | _ :: _, .letE .., _, _, e, _ | _ :: _, .con .., _, _, e, _ | _ :: _, .case .., _, _, e, _
  | _ :: _, .proj .., _, _, e, _ | _ :: _, .lit _, _, _, e, _ | _ :: _, .prim .., _, _, e, _
  | _ :: _, .tick _, _, _, e, _ | _ :: _, .box, _, _, e, _ | _ :: _, .trap, _, _, e, _ => by
    simp [Term.setModes] at e

/-! ## Registered keys, inverted -/

namespace RegT

variable {T : CTab}

theorem apps_inv : ∀ {h : Term} {args : List (Term × Mode)}, RegT T (Term.apps h args) →
    RegT T h ∧ ∀ a ∈ args, RegT T a.1
  | _, [], hh => ⟨hh, fun _ h => by cases h⟩
  | _, (a, m) :: args, hh => by
    unfold Term.apps at hh
    rw [List.foldl_cons] at hh
    obtain ⟨h₁, h₂⟩ := apps_inv (args := args) hh
    cases h₁ with
    | app hf ha =>
      exact ⟨hf, fun b hb => (List.mem_cons.1 hb).elim (fun e => e ▸ ha) (h₂ b)⟩

theorem lams_inv : ∀ {ms : List Mode} {b : Term}, RegT T (Term.lams ms b) → RegT T b
  | [], _, h => h
  | m :: ms, _, h => by
    unfold Term.lams at h
    rw [List.foldr_cons] at h
    cases h with
    | lam hb => exact lams_inv (ms := ms) hb

theorem wrapLets_inv : ∀ {lets : List Term} {b : Term}, RegT T (Erase.wrapLets lets b) →
    (∀ v ∈ lets, RegT T v) ∧ RegT T b
  | [], _, h => ⟨fun _ h => (by cases h), h⟩
  | v :: lets, _, h => by
    unfold Erase.wrapLets at h
    rw [List.foldr_cons] at h
    cases h with
    | letE hv hb =>
      obtain ⟨h₁, h₂⟩ := wrapLets_inv (lets := lets) hb
      exact ⟨fun w hw => (List.mem_cons.1 hw).elim (fun e => e ▸ hv) (h₁ w), h₂⟩

theorem setModes_inv : ∀ {ms : List Mode} {t t' : Term}, Term.setModes ms t = some t' →
    RegT T t' → RegT T t
  | [], _, _, e, h => by cases e; exact h
  | m :: ms, .lam m' c b, t', e, h => by
    simp only [Term.setModes, Option.map_eq_some_iff] at e
    obtain ⟨b', hb, rfl⟩ := e
    cases h with
    | lam hb' => exact .lam (setModes_inv hb hb')
  | _ :: _, .var _, _, e, _ | _ :: _, .glob _, _, e, _ | _ :: _, .app .., _, e, _
  | _ :: _, .letE .., _, e, _ | _ :: _, .con .., _, e, _ | _ :: _, .case .., _, e, _
  | _ :: _, .proj .., _, e, _ | _ :: _, .lit _, _, e, _ | _ :: _, .prim .., _, e, _
  | _ :: _, .tick _, _, e, _ | _ :: _, .box, _, e, _ | _ :: _, .trap, _, e, _ => by
    simp [Term.setModes] at e

end RegT

/-! ## Kept fields -/

section Count

variable (I : Input)

theorem rank_succ (c : CId) (q : Profile) (i : Nat) :
    I.rank c q (i + 1) = I.rank c q i + if I.kept c q i then 1 else 0 := by
  cases hk : I.kept c q i <;> simp [Input.rank, List.range_succ, List.filter_append, hk]

theorem rank_mono (c : CId) (q : Profile) {i j : Nat} (h : i ≤ j) :
    I.rank c q i ≤ I.rank c q j := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [rank_succ]; exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem rank_lt {c : CId} {q : Profile} {i n : Nat} (hk : I.kept c q i = true) (hi : i < n) :
    I.rank c q i < I.rank c q n := by
  have := rank_mono I c q hi
  rw [rank_succ, hk] at this
  simp only [↓reduceIte] at this
  omega

theorem keptCount_fieldless {k : CId} (h : I.fieldless k = true) (q : Profile) (n : Nat) :
    I.keptCount k q n = 0 := by
  unfold Input.keptCount Input.rank
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro i _
  unfold Input.fieldless at h
  unfold Input.kept
  cases hf : I.fields? k with
  | none => rw [hf] at h; cases h
  | some fs =>
    rw [hf] at h
    simp only
    cases hc : fs[i]? with
    | none => simp
    | some cls =>
      have := List.all_eq_true.1 h cls (List.mem_of_getElem? hc)
      have hd : cls.dropWhen = .allZero [] := by
        unfold Src.Relevance.FieldClass.alwaysDropped at this
        cases hw : cls.dropWhen with
        | never => rw [hw] at this; cases this
        | allZero ps =>
          rw [hw] at this
          cases ps with
          | nil => rfl
          | cons p ps => cases this
      simp [Src.Relevance.FieldClass.dropP, hd, Src.PropWhen.holdsP]

end Count

/-! ## `alias` -/

section Alias

variable {I : Input} (wf : ProgWF I)

omit wf in
/-- What `alias` does: nothing, or it retags a fieldless pinned `Decidable`
constructor as the pinned `Bool` one. -/
theorem alias_retags (c : CId) : I.alias c = c ∨
    (I.known.decIsFalse = some c ∧ I.fieldless c = true ∧ I.known.boolFalse = some (I.alias c)) ∨
    (I.known.decIsTrue = some c ∧ I.fieldless c = true ∧ I.known.boolTrue = some (I.alias c)) := by
  unfold Input.alias
  split
  · next df dt bf bt hdf hdt hbf hbt =>
    by_cases h₁ : (c == df && I.fieldless df) = true
    · simp only [h₁, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq] at h₁
      obtain ⟨rfl, hf⟩ := h₁
      exact .inr (.inl ⟨hdf, hf, hbf⟩)
    · simp only [h₁, Bool.false_eq_true, ↓reduceIte]
      by_cases h₂ : (c == dt && I.fieldless dt) = true
      · simp only [h₂, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at h₂
        obtain ⟨rfl, hf⟩ := h₂
        exact .inr (.inr ⟨hdt, hf, hbt⟩)
      · simp only [h₂, Bool.false_eq_true, ↓reduceIte]
        first | exact .inl rfl | exact .inl trivial
  · exact .inl rfl

include wf

theorem bool_pins_ne {x : CId} (hf : I.known.boolFalse = some x) (ht : I.known.boolTrue = some x) :
    False := by
  obtain ⟨_, _, _, _, _, h₁, _⟩ := wf.boolFalse hf
  obtain ⟨_, _, _, _, _, h₂, _⟩ := wf.boolTrue ht
  rw [h₁] at h₂
  cases h₂

/-- The constructor a key is retagged as has the same kept-field count. -/
theorem alias_count {c : CId} {sf : Bool} {lv : Nat} {ind : CId} {cidx np nf : Nat}
    {ty : Src.Term} (hd : I.decl? c = some (.ctor sf lv ind cidx np nf ty)) :
    ∃ sf' lv' ind' cidx' np' nf' ty',
      I.decl? (I.alias c) = some (.ctor sf' lv' ind' cidx' np' nf' ty') ∧
      I.keptCount c [] nf = I.keptCount (I.alias c) [] nf' := by
  rcases alias_retags c with h | ⟨_, hfl, hbf⟩ | ⟨_, hfl, hbt⟩
  · rw [h]
    exact ⟨sf, lv, ind, cidx, np, nf, ty, hd, rfl⟩
  · obtain ⟨sf', lv', B, np', ty', h₁, _⟩ := wf.boolFalse hbf
    exact ⟨sf', lv', B, 0, np', 0, ty', h₁, by rw [keptCount_fieldless I hfl]; rfl⟩
  · obtain ⟨sf', lv', B, np', ty', h₁, _⟩ := wf.boolTrue hbt
    exact ⟨sf', lv', B, 1, np', 0, ty', h₁, by rw [keptCount_fieldless I hfl]; rfl⟩

/-- Constructors retagged as one key have the same kept-field count. -/
theorem keptCount_alias_eq {c₀ c : CId} {sf₀ sf : Bool} {lv₀ lv : Nat} {ind₀ ind : CId}
    {cidx₀ cidx np₀ np nf₀ nf : Nat} {ty₀ ty : Src.Term}
    (h₀ : I.decl? c₀ = some (.ctor sf₀ lv₀ ind₀ cidx₀ np₀ nf₀ ty₀))
    (h : I.decl? c = some (.ctor sf lv ind cidx np nf ty)) (ha : I.alias c₀ = I.alias c) :
    I.keptCount c₀ [] nf₀ = I.keptCount c [] nf := by
  obtain ⟨_, _, _, _, _, n₀, _, d₀, e₀⟩ := alias_count wf h₀
  obtain ⟨_, _, _, _, _, n₁, _, d₁, e₁⟩ := alias_count wf h
  rw [ha] at d₀
  rw [d₀] at d₁
  cases d₁
  rw [e₀, e₁, ha]

/-- Two constructors of one inductive with one key have one index. -/
theorem ctorKey_cidx {c₁ c₂ : CId} {sf₁ sf₂ : Bool} {lv₁ lv₂ : Nat} {ind : CId}
    {cidx₁ cidx₂ np₁ np₂ nf₁ nf₂ : Nat} {ty₁ ty₂ : Src.Term}
    (h₁ : I.decl? c₁ = some (.ctor sf₁ lv₁ ind cidx₁ np₁ nf₁ ty₁))
    (h₂ : I.decl? c₂ = some (.ctor sf₂ lv₂ ind cidx₂ np₂ nf₂ ty₂))
    (hk : I.ctorKey c₁ = I.ctorKey c₂) : cidx₁ = cidx₂ := by
  have ha : I.alias c₁ = I.alias c₂ := by
    unfold Input.ctorKey at hk
    injection hk
  have same : c₁ = c₂ → cidx₁ = cidx₂ := fun e => by
    subst e; rw [h₁] at h₂; cases h₂; rfl
  -- A `Decidable` constructor is not a `Bool` one of the same inductive.
  have noMix : ∀ {d b : CId}, (I.known.decIsFalse = some d ∨ I.known.decIsTrue = some d) →
      (I.known.boolFalse = some b ∨ I.known.boolTrue = some b) →
      (d = c₁ ∧ b = c₂ ∨ d = c₂ ∧ b = c₁) → False := by
    intro d b hd hb e
    rcases e with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact wf.decOther hd (hb.elim .inl fun h => .inr (.inl h)) h₁ h₂ rfl
    · exact wf.decOther hd (hb.elim .inl fun h => .inr (.inl h)) h₂ h₁ rfl
  rcases alias_retags c₁ with e₁ | ⟨hd₁, _, hb₁⟩ | ⟨hd₁, _, hb₁⟩ <;>
    rcases alias_retags c₂ with e₂ | ⟨hd₂, _, hb₂⟩ | ⟨hd₂, _, hb₂⟩
  · exact same (by rw [← e₁, ← e₂, ha])
  · exact (noMix (.inl hd₂) (.inl (show I.known.boolFalse = some c₁ by rw [hb₂, ← ha, e₁]))
      (.inr ⟨rfl, rfl⟩)).elim
  · exact (noMix (.inr hd₂) (.inr (show I.known.boolTrue = some c₁ by rw [hb₂, ← ha, e₁]))
      (.inr ⟨rfl, rfl⟩)).elim
  · exact (noMix (.inl hd₁) (.inl (show I.known.boolFalse = some c₂ by rw [hb₁, ha, e₂]))
      (.inl ⟨rfl, rfl⟩)).elim
  · exact same (by rw [hd₁] at hd₂; cases hd₂; rfl)
  · exact (bool_pins_ne wf hb₁ (by rw [hb₂, ← ha])).elim
  · exact (noMix (.inr hd₁) (.inr (show I.known.boolTrue = some c₂ by rw [hb₁, ha, e₂]))
      (.inl ⟨rfl, rfl⟩)).elim
  · exact (bool_pins_ne wf (by rw [hb₂, ← ha]) hb₁).elim
  · exact same (by rw [hd₁] at hd₂; cases hd₂; rfl)

end Alias

end IxCC.Lam.Erase.Proof
