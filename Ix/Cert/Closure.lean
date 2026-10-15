import Ix.Cert.Statement

/-! # The computed closure is the closure

`closureCorrect : ClosureCorrect`: the worklist `Ix.Cert.closure` keeps
exactly the constants of `env` that `roots` reach under `DependsOn`.

Names are compared as the maps compare them, by `Ix.Name`'s `==` (the stored
hash), which is an equivalence (the `EquivBEq` and `LawfulHashable`
instances of `Ix.Cert.Statement`); `Reaches` and
`DependsOn` respect it in the reached name. The one structural comparison,
of an inductive block's first member with a recursor's in `DependsOn`, is
made structurally by the worklist too (`nameEq`).

The worklist is a `repeatM` loop (`closureLoop`), unfolded one step at a time
(`repeatM.Internal.eq_of_monadTail`); it ends because every step either pops
the stack or marks a constant of `env` not yet marked. -/

namespace Ix.Cert

namespace Closure

/-! ## Names -/

theorem nameEq_iff (a b : Ix.Name) : nameEq a b = true ↔ a = b := by
  induction a generalizing b with
  | anonymous h =>
    cases b with
    | anonymous h' => simp only [nameEq, Address.beq_iff_eq, Ix.Name.anonymous.injEq]
    | _ => simp [nameEq]
  | str p s h ih =>
    cases b with
    | str p' s' h' =>
      simp only [nameEq, Bool.and_eq_true, beq_iff_eq, ih, Ix.Name.str.injEq]
      constructor
      · rintro ⟨⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, rfl⟩
    | _ => simp [nameEq]
  | num p i h ih =>
    cases b with
    | num p' i' h' =>
      simp only [nameEq, Bool.and_eq_true, beq_iff_eq, ih, Ix.Name.num.injEq]
      constructor
      · rintro ⟨⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, rfl⟩
    | _ => simp [nameEq]

theorem list_contains_of_beq {l : List Ix.Name} {a b : Ix.Name} (hab : (a == b) = true)
    (ha : l.contains a = true) : l.contains b = true := by
  obtain ⟨a', ha', haa'⟩ := List.contains_iff_exists_mem_beq.mp ha
  exact List.contains_iff_exists_mem_beq.mpr ⟨a', ha', BEq.trans (BEq.symm hab) haa'⟩

theorem array_contains_of_beq {l : Array Ix.Name} {a b : Ix.Name} (hab : (a == b) = true)
    (ha : l.contains a = true) : l.contains b = true := by
  obtain ⟨a', ha', haa'⟩ := Array.contains_iff_exists_mem_beq.mp ha
  exact Array.contains_iff_exists_mem_beq.mpr ⟨a', ha', BEq.trans (BEq.symm hab) haa'⟩

/-- `DependsOn` respects `==` in the needed name. -/
theorem dependsOn_congr {env : Ix.Environment} {a b b' : Ix.Name} (h : DependsOn env a b)
    (hb : (b == b') = true) : DependsOn env a b' := by
  obtain ⟨ci, hci, hd⟩ := h
  refine ⟨ci, hci, ?_⟩
  rcases hd with hr | hm
  · exact .inl (by rw [← Std.HashSet.contains_congr (m := refsOf ci) hb]; exact hr)
  · right
    cases ci with
    | inductInfo v =>
      rcases hm with hall | ⟨first, rv, h0, hrec, h0'⟩
      · exact .inl (array_contains_of_beq hb hall)
      · refine .inr ⟨first, rv, h0, ?_, h0'⟩
        show env.consts[b']? = _
        rw [← Std.HashMap.getElem?_congr hb]; exact hrec
    | recInfo rv => exact array_contains_of_beq hb hm
    | _ => exact hm

/-- `Reaches` respects `==`. -/
theorem reaches_congr {env : Ix.Environment} {roots : List Ix.Name} {a b : Ix.Name}
    (h : Reaches env roots a) (hab : (a == b) = true) : Reaches env roots b := by
  cases h with
  | root hr => exact .root (list_contains_of_beq hab hr)
  | step hx hd => exact .step hx (dependsOn_congr hd hab)

theorem get?_of_mem_toList {m : Std.HashMap Ix.Name Ix.ConstantInfo} {k : Ix.Name}
    {v : Ix.ConstantInfo} (h : (k, v) ∈ m.toList) : m.get? k = some v :=
  (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some.mp h).2

/-! ## The recursor index -/

/-- One step of `recursorsByBlock`'s fold. -/
def recStep (m : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name))) (p : Ix.Name × Ix.ConstantInfo) :
    Ix.Map Ix.Name (Array (Ix.Name × Ix.Name)) :=
  match p.2 with
  | .recInfo rv =>
    match rv.all[0]? with
    | some first => m.insert first ((m.getD first #[]).push (first, p.1))
    | none => m
  | _ => m

theorem recursorsByBlock_eq (env : Ix.Environment) :
    recursorsByBlock env = env.consts.toList.foldl recStep {} := by
  unfold recursorsByBlock
  rw [Std.HashMap.fold_eq_foldl_toList]
  rfl

/-- What the index lists is a recursor of the listed entries with that first
member. -/
theorem foldl_recStep_sound (E : List (Ix.Name × Ix.ConstantInfo)) :
    ∀ (L : List (Ix.Name × Ix.ConstantInfo)) (m : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name))),
      (∀ p ∈ L, p ∈ E) →
      (∀ f x, x ∈ m.getD f #[] → ∃ rv, (x.2, Ix.ConstantInfo.recInfo rv) ∈ E ∧ rv.all[0]? = some x.1) →
      ∀ f x, x ∈ (L.foldl recStep m).getD f #[] →
        ∃ rv, (x.2, Ix.ConstantInfo.recInfo rv) ∈ E ∧ rv.all[0]? = some x.1
  | [], _, _, hm => hm
  | p :: L, m, hL, hm => by
    refine foldl_recStep_sound E L (recStep m p) (fun q hq => hL q (List.mem_cons_of_mem _ hq)) ?_
    intro f x hx
    obtain ⟨n, ci⟩ := p
    unfold recStep at hx
    cases ci with
    | recInfo rv =>
      cases h0 : rv.all[0]? with
      | none => simp only [h0] at hx; exact hm f x hx
      | some first =>
        simp only [h0, Std.HashMap.getD_insert] at hx
        split at hx
        · rcases Array.mem_push.mp hx with hx | rfl
          · exact hm first x hx
          · exact ⟨rv, hL _ List.mem_cons_self, h0⟩
        · exact hm f x hx
    | _ => exact hm f x hx

/-- The index keeps what it listed. -/
theorem recStep_mono (m : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name))) (p : Ix.Name × Ix.ConstantInfo)
    {f : Ix.Name} {x : Ix.Name × Ix.Name} (hx : x ∈ m.getD f #[]) : x ∈ (recStep m p).getD f #[] := by
  obtain ⟨n, ci⟩ := p
  unfold recStep
  cases ci with
  | recInfo rv =>
    cases h0 : rv.all[0]? with
    | none => simpa only [h0]
    | some first =>
      simp only [h0, Std.HashMap.getD_insert]
      split
      · rename_i hf
        exact Array.mem_push.mpr (.inl (by rw [Std.HashMap.getD_congr hf]; exact hx))
      · exact hx
  | _ => exact hx

theorem foldl_recStep_mono :
    ∀ (L : List (Ix.Name × Ix.ConstantInfo)) (m : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name)))
      {f : Ix.Name} {x : Ix.Name × Ix.Name}, x ∈ m.getD f #[] → x ∈ (L.foldl recStep m).getD f #[]
  | [], _, _, _, hx => hx
  | p :: L, m, _, _, hx => foldl_recStep_mono L (recStep m p) (recStep_mono m p hx)

/-- The index lists every recursor of the entries under its first member. -/
theorem foldl_recStep_complete :
    ∀ (L : List (Ix.Name × Ix.ConstantInfo)) (m : Ix.Map Ix.Name (Array (Ix.Name × Ix.Name))),
      ∀ n rv first, (n, Ix.ConstantInfo.recInfo rv) ∈ L → rv.all[0]? = some first →
        (first, n) ∈ (L.foldl recStep m).getD first #[]
  | [], _, _, _, _, h, _ => absurd h List.not_mem_nil
  | p :: L, m, n, rv, first, h, h0 => by
    rcases List.mem_cons.mp h with rfl | h
    · refine foldl_recStep_mono L _ ?_
      simp only [recStep, h0, Std.HashMap.getD_insert, BEq.rfl, ite_true]
      exact Array.mem_push_self
    · exact foldl_recStep_complete L (recStep m p) n rv first h h0

theorem recursors_sound {env : Ix.Environment} {f : Ix.Name} {x : Ix.Name × Ix.Name}
    (hx : x ∈ (recursorsByBlock env).getD f #[]) :
    ∃ rv, env.consts.get? x.2 = some (.recInfo rv) ∧ rv.all[0]? = some x.1 := by
  rw [recursorsByBlock_eq] at hx
  obtain ⟨rv, hmem, h0⟩ := foldl_recStep_sound env.consts.toList env.consts.toList {}
    (fun _ h => h) (fun f x hx => by simp at hx) f x hx
  exact ⟨rv, get?_of_mem_toList hmem, h0⟩

theorem recursors_complete {env : Ix.Environment} {n first : Ix.Name} {rv : Ix.RecursorVal}
    (hn : env.consts.get? n = some (.recInfo rv)) (h0 : rv.all[0]? = some first) :
    ∃ k, (n == k) = true ∧ (first, k) ∈ (recursorsByBlock env).getD first #[] := by
  obtain ⟨k, hnk, hk⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp hn
  rw [recursorsByBlock_eq]
  exact ⟨k, hnk, foldl_recStep_complete _ {} k rv first hk h0⟩

/-! ## The names a constant needs -/

theorem dependencies_sound {env : Ix.Environment} {a : Ix.Name} {ci : Ix.ConstantInfo}
    (ha : env.consts.get? a = some ci) {d : Ix.Name}
    (hd : d ∈ dependencies (recursorsByBlock env) ci) : DependsOn env a d := by
  unfold dependencies at hd
  rcases Array.mem_append.mp hd with hr | hm
  · refine ⟨ci, ha, .inl ?_⟩
    rw [← Std.HashSet.contains_toArray]
    exact Array.contains_eq_true_of_mem hr
  · refine ⟨ci, ha, .inr ?_⟩
    cases ci with
    | inductInfo v =>
      rcases Array.mem_append.mp hm with hall | hrec
      · exact .inl (Array.contains_eq_true_of_mem hall)
      · refine .inr ?_
        cases h0 : v.all[0]? with
        | none => simp [h0] at hrec
        | some first =>
          simp only [h0] at hrec
          obtain ⟨x, hx, rfl⟩ := Array.mem_map.mp hrec
          obtain ⟨hx, hxf⟩ := Array.mem_filter.mp hx
          obtain ⟨rv, hrv, hr0⟩ := recursors_sound hx
          exact ⟨first, rv, rfl, hrv, by rw [hr0, (nameEq_iff _ _).mp hxf]⟩
    | recInfo rv => exact Array.contains_eq_true_of_mem hm
    | _ => simp at hm

theorem dependencies_complete {env : Ix.Environment} {a b : Ix.Name} {ci : Ix.ConstantInfo}
    (ha : env.consts.get? a = some ci) (h : DependsOn env a b) :
    ∃ d ∈ dependencies (recursorsByBlock env) ci, (b == d) = true := by
  obtain ⟨ci', ha', hd⟩ := h
  rw [ha] at ha'
  cases ha'
  unfold dependencies
  rcases hd with hr | hm
  · rw [← Std.HashSet.contains_toArray] at hr
    obtain ⟨d, hd, hbd⟩ := Array.contains_iff_exists_mem_beq.mp hr
    exact ⟨d, Array.mem_append.mpr (.inl hd), hbd⟩
  · cases ci with
    | inductInfo v =>
      rcases hm with hall | ⟨first, rv, h0, hrec, h0'⟩
      · obtain ⟨d, hd, hbd⟩ := Array.contains_iff_exists_mem_beq.mp hall
        exact ⟨d, Array.mem_append.mpr (.inr (Array.mem_append.mpr (.inl hd))), hbd⟩
      · obtain ⟨k, hbk, hk⟩ := recursors_complete hrec h0'
        refine ⟨k, Array.mem_append.mpr (.inr (Array.mem_append.mpr (.inr ?_))), hbk⟩
        simp only [h0]
        exact Array.mem_map.mpr ⟨(first, k),
          Array.mem_filter.mpr ⟨hk, (nameEq_iff _ _).mpr rfl⟩, rfl⟩
    | recInfo rv =>
      obtain ⟨d, hd, hbd⟩ := Array.contains_iff_exists_mem_beq.mp hm
      exact ⟨d, Array.mem_append.mpr (.inr hd), hbd⟩
    | _ => exact hm.elim

/-! ## The worklist -/

section Loop

variable (env : Ix.Environment) (roots : List Ix.Name)

/-- `x` is marked, waiting on the stack, or not a constant of `env`. -/
def Pending (seen : Ix.Set Ix.Name) (todo : List Ix.Name) (x : Ix.Name) : Prop :=
  seen.contains x = true ∨ x ∈ todo ∨ env.consts.get? x = none

/-- The loop invariant: every marked or stacked name is reached, every root
and every name a marked constant needs is pending. -/
structure Inv (s : Ix.Set Ix.Name × List Ix.Name) : Prop where
  sound : ∀ n, s.1.contains n = true → Reaches env roots n
  stacked : ∀ n ∈ s.2, Reaches env roots n
  roots : ∀ r ∈ roots, Pending env s.1 s.2 r
  closed : ∀ a, s.1.contains a = true → ∀ ci, env.consts.get? a = some ci →
    ∀ d ∈ dependencies (recursorsByBlock env) ci, Pending env s.1 s.2 d

/-- The constants of `env` not marked yet: the outer termination measure. -/
def unmarked (seen : Ix.Set Ix.Name) : Nat :=
  env.consts.keys.countP fun k => !seen.contains k

end Loop

theorem inv_init (env : Ix.Environment) (roots : List Ix.Name) : Inv env roots (∅, roots) where
  sound n h := by simp at h
  stacked n h := .root (List.elem_eq_true_of_mem h)
  roots r h := .inr (.inl h)
  closed a h := by simp at h

/-- A popped name stays pending in every step. -/
theorem pending_step {env : Ix.Environment} {seen seen' : Ix.Set Ix.Name} {n : Ix.Name}
    {todo todo' : List Ix.Name} (hseen : ∀ k, seen.contains k = true → seen'.contains k = true)
    (htodo : ∀ k ∈ todo, k ∈ todo')
    (hn : seen'.contains n = true ∨ env.consts.get? n = none) {x : Ix.Name}
    (hx : Pending env seen (n :: todo) x) : Pending env seen' todo' x := by
  rcases hx with hs | hm | hE
  · exact .inl (hseen x hs)
  · rcases List.mem_cons.mp hm with rfl | hm
    · rcases hn with hs | hE
      · exact .inl hs
      · exact .inr (.inr hE)
    · exact .inr (.inl (htodo x hm))
  · exact .inr (.inr hE)

theorem inv_step {env : Ix.Environment} {roots : List Ix.Name} {s s' : Ix.Set Ix.Name × List Ix.Name}
    (hI : Inv env roots s) (hs : closureStep env (recursorsByBlock env) s = .inl s') :
    Inv env roots s' := by
  obtain ⟨seen, todo⟩ := s
  cases todo with
  | nil => simp [closureStep] at hs
  | cons n todo =>
    have hnR : Reaches env roots n := hI.stacked n List.mem_cons_self
    simp only [closureStep] at hs
    split at hs
    · -- already marked
      rename_i hsn
      cases hs
      have hp := @pending_step env seen seen n todo todo (fun _ h => h) (fun _ h => h) (.inl hsn)
      exact { sound := hI.sound
              stacked := fun k hk => hI.stacked k (List.mem_cons_of_mem _ hk)
              roots := fun r hr => hp (hI.roots r hr)
              closed := fun a ha ci hci d hd => hp (hI.closed a ha ci hci d hd) }
    · rename_i hsn
      split at hs
      · -- not a constant of `env`
        rename_i hE
        cases hs
        have hp := @pending_step env seen seen n todo todo (fun _ h => h) (fun _ h => h) (.inr hE)
        exact { sound := hI.sound
                stacked := fun k hk => hI.stacked k (List.mem_cons_of_mem _ hk)
                roots := fun r hr => hp (hI.roots r hr)
                closed := fun a ha ci hci d hd => hp (hI.closed a ha ci hci d hd) }
      · -- marked now, its needs pushed
        rename_i ci hE
        cases hs
        have hins : ∀ k, (seen.insert n).contains k = true ↔ ((n == k) = true ∨ seen.contains k = true) := by
          intro k; rw [Std.HashSet.contains_insert]; simp
        have hp := @pending_step env seen (seen.insert n) n todo
          ((dependencies (recursorsByBlock env) ci).toList ++ todo)
          (fun k h => (hins k).mpr (.inr h)) (fun k h => List.mem_append_right _ h)
          (.inl Std.HashSet.contains_insert_self)
        refine { sound := ?_, stacked := ?_, roots := fun r hr => hp (hI.roots r hr), closed := ?_ }
        · intro k hk
          rcases (hins k).mp hk with hnk | hk
          · exact reaches_congr hnR hnk
          · exact hI.sound k hk
        · intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact .step hnR (dependencies_sound hE (Array.mem_toList_iff.mp hk))
          · exact hI.stacked k (List.mem_cons_of_mem _ hk)
        · intro a ha ci' hci' d hd
          rcases (hins a).mp ha with hna | ha
          · have : ci' = ci := by
              have h1 : env.consts.get? a = env.consts.get? n :=
                Std.HashMap.getElem?_congr (BEq.symm hna)
              rw [h1, hE] at hci'
              exact (Option.some.inj hci').symm
            subst this
            exact .inr (.inl (List.mem_append_left _ (Array.mem_toList_iff.mpr hd)))
          · exact hp (hI.closed a ha ci' hci' d hd)

theorem countP_lt {α : Type} {L : List α} {p q : α → Bool}
    (hqp : ∀ x, q x = true → p x = true) {y : α} (hy : y ∈ L) (hp : p y = true)
    (hq : q y = false) : L.countP q < L.countP p := by
  induction L with
  | nil => cases hy
  | cons x L ih =>
    rw [List.countP_cons, List.countP_cons]
    have hle : L.countP q ≤ L.countP p := List.countP_mono_left fun x _ h => hqp x h
    have hx : (if q x = true then 1 else 0) ≤ (if p x = true then 1 else 0) := by
      by_cases h : q x = true
      · simp [h, hqp x h]
      · simp [h]
    rcases List.mem_cons.mp hy with rfl | hy
    · simp [hq, hp]; omega
    · have := ih hy; omega

/-- Every step decreases (unmarked constants, stack height) lexicographically. -/
theorem step_decreases {env : Ix.Environment} {s s' : Ix.Set Ix.Name × List Ix.Name}
    (hs : closureStep env (recursorsByBlock env) s = .inl s') :
    Prod.Lex (· < ·) (· < ·) (unmarked env s'.1, s'.2.length) (unmarked env s.1, s.2.length) := by
  obtain ⟨seen, todo⟩ := s
  cases todo with
  | nil => simp [closureStep] at hs
  | cons n todo =>
    simp only [closureStep] at hs
    split at hs
    · cases hs; exact .right _ (by simp)
    · rename_i hsn
      split at hs
      · cases hs; exact .right _ (by simp)
      · rename_i ci hE
        cases hs
        refine .left _ _ ?_
        have hc : env.consts.keys.contains n = true := by
          rw [Std.HashMap.contains_keys, Std.HashMap.contains_eq_isSome_getElem?]
          exact Option.isSome_iff_exists.mpr ⟨ci, hE⟩
        obtain ⟨k, hk, hnk⟩ := List.contains_iff_exists_mem_beq.mp hc
        refine countP_lt (y := k) ?_ hk ?_ ?_
        · intro x hx
          simp only [Bool.not_eq_true'] at hx ⊢
          rw [Std.HashSet.contains_insert] at hx
          simp only [Bool.or_eq_false_iff] at hx
          exact hx.2
        · simp only [Bool.not_eq_true']
          rw [← Std.HashSet.contains_congr hnk]
          simpa using hsn
        · simp only [Bool.not_eq_false']
          rw [Std.HashSet.contains_insert]
          simp [hnk]

/-- One step of the loop, unfolded. -/
theorem closureLoop_eq (env : Ix.Environment) (s : Ix.Set Ix.Name × List Ix.Name) :
    closureLoop env s = match closureStep env (recursorsByBlock env) s with
      | .inl s' => closureLoop env s'
      | .inr seen => seen := by
  unfold closureLoop
  rw [repeatM.Internal.eq_of_monadTail]
  simp only [repeatM.body, pure_bind]
  cases closureStep env (recursorsByBlock env) s <;> rfl

/-- The loop ends in a state that keeps the invariant with an empty stack. -/
theorem closureLoop_inv {env : Ix.Environment} {roots : List Ix.Name} :
    ∀ (s : Ix.Set Ix.Name × List Ix.Name), Inv env roots s →
      Inv env roots (closureLoop env s, [])
  | s, hI => by
    rw [closureLoop_eq]
    match hs : closureStep env (recursorsByBlock env) s with
    | .inl s' => exact closureLoop_inv s' (inv_step hI hs)
    | .inr seen =>
      obtain ⟨seen₀, todo⟩ := s
      cases todo with
      | nil =>
        simp only [closureStep, Sum.inr.injEq] at hs
        subst hs
        exact hI
      | cons n todo =>
        simp only [closureStep] at hs
        split at hs
        · cases hs
        · split at hs <;> cases hs
termination_by s => (unmarked env s.1, s.2.length)
decreasing_by exact step_decreases hs

/-- With an empty stack, every reached constant of `env` is marked. -/
theorem marked_of_reaches {env : Ix.Environment} {roots : List Ix.Name} {seen : Ix.Set Ix.Name}
    (hI : Inv env roots (seen, [])) {n : Ix.Name} (hr : Reaches env roots n) :
    env.consts.contains n = true → seen.contains n = true := by
  induction hr with
  | @root n h =>
    intro hc
    obtain ⟨r, hr, hnr⟩ := List.contains_iff_exists_mem_beq.mp h
    rcases hI.roots r hr with hs | hm | hE
    · rw [Std.HashSet.contains_congr hnr]; exact hs
    · cases hm
    · rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_congr hnr] at hc
      simp [show env.consts[r]? = none from hE] at hc
  | @step a b ha hd ih =>
    intro hc
    have ⟨ci, hci, _⟩ := hd
    have hsa := ih (by
      rw [Std.HashMap.contains_eq_isSome_getElem?]
      exact Option.isSome_iff_exists.mpr ⟨ci, hci⟩)
    obtain ⟨d, hdm, hbd⟩ := dependencies_complete hci hd
    rcases hI.closed a hsa ci hci d hdm with hs | hm | hE
    · rw [Std.HashSet.contains_congr hbd]; exact hs
    · cases hm
    · rw [Std.HashMap.contains_eq_isSome_getElem?, Std.HashMap.getElem?_congr hbd] at hc
      simp [show env.consts[d]? = none from hE] at hc

end Closure

/-- A filter by marked names keeps a constant exactly when it is marked. -/
theorem Closure.get?_filter_marked (consts : Std.HashMap Ix.Name Ix.ConstantInfo)
    (seen : Ix.Set Ix.Name) (n : Ix.Name) :
    (consts.filter fun n _ => seen.contains n).get? n =
      if seen.contains n = true then consts.get? n else none := by
  show (consts.filter fun n _ => seen.contains n)[n]? = if seen.contains n = true then consts[n]? else none
  by_cases hc : n ∈ consts
  · rw [Std.HashMap.getElem?_filter_of_getKey?_eq_some (Std.HashMap.getKey?_eq_some_getKey hc)]
    simp only [Std.HashSet.contains_congr (Std.HashMap.getKey_beq hc)]
    cases seen.contains n <;> cases consts[n]? <;> simp [Option.filter]
  · have h1 : consts[n]? = none := Std.HashMap.getElem?_eq_none hc
    have h2 : (consts.filter fun n _ => seen.contains n)[n]? = none :=
      Std.HashMap.getElem?_eq_none fun h => hc (Std.HashMap.mem_of_mem_filter h)
    rw [h1, h2]
    simp

open Closure in
/-- **The computed closure is the closure.** -/
theorem closureCorrect : ClosureCorrect := by
  intro env roots n
  show (Reaches env roots n → (env.consts.filter fun n _ =>
      (closureLoop env (∅, roots)).contains n).get? n = env.consts.get? n) ∧
    (¬ Reaches env roots n → (env.consts.filter fun n _ =>
      (closureLoop env (∅, roots)).contains n).get? n = none)
  have hI := closureLoop_inv (roots := roots) (∅, roots) (inv_init env roots)
  generalize closureLoop env (∅, roots) = seen at hI ⊢
  rw [get?_filter_marked]
  constructor
  · intro hr
    split
    · rfl
    · rename_i hs
      cases hE : env.consts.get? n with
      | none => rfl
      | some ci =>
        exact absurd (marked_of_reaches hI hr (by
          rw [Std.HashMap.contains_eq_isSome_getElem?]
          exact Option.isSome_iff_exists.mpr ⟨ci, hE⟩)) hs
  · intro hr
    split
    · rename_i hs; exact absurd (hI.sound n hs) hr
    · rfl

end Ix.Cert
