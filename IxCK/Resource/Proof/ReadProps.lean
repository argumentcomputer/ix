import IxCK.Resource.Statement
import IxCK.Resource.Proof.ModeOk

/-!
# Properties of the Reading (`IxCK.Resource.Read`)

Proves:
1. **`closureOf` determinism, uniqueness, and reachability** (`closureOf_eq_of_walked`,
   `Reading.make_eq_of_walked`, `closureOf_nodup`, `closureOf_mem_of_root`,
   `closureOf_mem_of_ref`, `closureOf_mem_of_prj`).
2. **`unshare` pigeonhole lemma and `readSkel`/`readTele` independence** from the class
   oracle and kernel reader context (`readForalls_rcx_eq_bare`), plus
   `caseShape_arity_eq_lams_length`.
3. **Default-mode preservation** from `recordDefault = .ok true` to `readSkel`, `readTele`,
   `ifaceErased`, `readTerm`, and `Reading.readDef`.
4. **`refsOf` / `readProg` uniqueness & lookup** (`readProg_defs_nodup`, `readProg_find_elim`,
   `readProg_ctorsIndexed`).
5. **`IxCK.Resource.ReadsRespectErasure`** (`readsRespectErasure`).
6. **Term structural properties** from `readTerm` / `caseShape` (`freeVars` completeness,
   case-field distinctness, de Bruijn scoping, static `res = .shared`).
-/

namespace IxCK.Resource.Proof

open IxCK.Resource Ixon
open Ix.Kernel (ConstRef)

/-! ## 0. Small Collection, Monad & `forIn` Helpers -/

theorem nodup_singleton {α : Type} (x : α) : [x].Nodup := by simp

theorem exists_min_nat {P : Nat → Prop} [DecidablePred P] :
    ∀ n, P n → ∃ m ≤ n, P m ∧ ∀ m' < m, ¬ P m' := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hlt : ∃ k < n, P k
    · obtain ⟨k, hklt, hk⟩ := hlt
      obtain ⟨m, hmk, hm, hmin⟩ := ih k hklt hk
      exact ⟨m, Nat.le_trans hmk (Nat.le_of_lt hklt), hm, hmin⟩
    · exact ⟨n, Nat.le_refl _, hn, fun m' hm' hpm' => hlt ⟨m', hm', hpm'⟩⟩

@[simp] theorem RM_run_pure {α : Type} (a : α) (cs : Cursor) :
    ((pure a : RM α).run cs) = .ok (a, cs) := rfl

@[simp] theorem RM_run_throw {α : Type} (e : String) (cs : Cursor) :
    ((throw e : RM α).run cs) = .error e := rfl

@[simp] theorem RM_run_lift {α : Type} (e : Except String α) (cs : Cursor) :
    ((liftM e : RM α).run cs) = e.map (·, cs) := rfl

@[simp] theorem Ex_map_ok {α β : Type} (f : α → β) (a : α) :
    Except.map f (Except.ok a : Except String α) = .ok (f a) := rfl

@[simp] theorem Ex_map_err {α β : Type} (f : α → β) (e : String) :
    Except.map f (Except.error e : Except String α) = .error e := rfl

@[simp] theorem RM_run_lift_ok {α : Type} (a : α) (cs : Cursor) :
    ((liftM (Except.ok a : Except String α) : RM α).run cs) = .ok (a, cs) := rfl

@[simp] theorem RM_run_lift_pure {α : Type} (a : α) (cs : Cursor) :
    ((liftM (pure a : Except String α) : RM α).run cs) = .ok (a, cs) := rfl

@[simp] theorem RM_run_lift_err {α : Type} (e : String) (cs : Cursor) :
    ((liftM (Except.error e : Except String α) : RM α).run cs) = .error e := rfl

@[simp] theorem RM_run_bind {α β : Type} (m : RM α) (f : α → RM β) (cs : Cursor) :
    ((m >>= f).run cs) =
      match m.run cs with
      | .ok (a, cs') => (f a).run cs'
      | .error e => .error e := by
  change (m.run cs).bind (fun p => (f p.1).run p.2) = _
  cases m.run cs <;> rfl

@[simp] theorem RM_run_get (cs : Cursor) :
    ((get : RM Cursor).run cs) = .ok (cs, cs) := rfl

@[simp] theorem RM_run_set (cs' cs : Cursor) :
    ((set cs' : RM Unit).run cs) = .ok ((), cs') := rfl

@[simp] theorem Ex_bind_ok {α β : Type} (a : α) (f : α → Except String β) :
    ((Except.ok a : Except String α) >>= f) = f a := rfl

@[simp] theorem Ex_bind_err {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

@[simp] theorem Ex_pure {α : Type} (a : α) :
    (pure a : Except String α) = .ok a := rfl

@[simp] theorem Ex_throw {α : Type} (e : String) :
    (throw e : Except String α) = .error e := rfl

@[simp] theorem Opt_guard_true : (guard true : Option Unit) = some () := rfl
@[simp] theorem Opt_guard_false : (guard false : Option Unit) = none := rfl
@[simp] theorem Opt_guard_True : (guard True : Option Unit) = some () := rfl
@[simp] theorem Opt_guard_False : (guard False : Option Unit) = none := rfl
@[simp] theorem Opt_guard_prop_true {p : Prop} [Decidable p] (h : p) :
    (guard p : Option Unit) = some () := by simp [guard, h]
@[simp] theorem Opt_guard_prop_false {p : Prop} [Decidable p] (h : ¬ p) :
    (guard p : Option Unit) = none := by simp [guard, h]; rfl
@[simp] theorem Opt_bind_some {α β : Type} (a : α) (f : α → Option β) :
    ((some a : Option α) >>= f) = f a := rfl
@[simp] theorem Opt_bind_none {α β : Type} (f : α → Option β) :
    ((none : Option α) >>= f) = none := rfl
@[simp] theorem Opt_pure {α : Type} (a : α) : (pure a : Option α) = some a := rfl

theorem Ex_bind_elim {α β : Type} {m : Except String α} {f : α → Except String β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem RM_bind_elim {α β : Type} {m : RM α} {f : α → RM β} {cs cs' : Cursor} {b : β}
    (h : (m >>= f).run cs = .ok (b, cs')) :
    ∃ a cs₁, m.run cs = .ok (a, cs₁) ∧ (f a).run cs₁ = .ok (b, cs') := by
  rw [RM_run_bind] at h
  cases hm : m.run cs with
  | error _ => simp [hm] at h
  | ok p => simp only [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

theorem RM_lift_elim {α : Type} {e : Except String α} {cs cs' : Cursor} {a : α}
    (h : (liftM e : RM α).run cs = .ok (a, cs')) :
    e = .ok a ∧ cs' = cs := by
  cases he : e with
  | error err => simp [he] at h
  | ok v =>
    simp only [he, RM_run_lift, Ex_map_ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.1], h.2.symm⟩

theorem Ex_map_elim {α β : Type} {m : Except String α} {f : α → β} {b : β}
    (h : m.map f = .ok b) : ∃ a, m = .ok a ∧ f a = b := by
  cases m with
  | error _ => cases h
  | ok a => simp only [Except.map, Except.ok.injEq] at h; exact ⟨a, rfl, h⟩

theorem Opt_bind_elim {α β : Type} {m : Option α} {f : α → Option β} {b : β}
    (h : (m >>= f) = some b) : ∃ a, m = some a ∧ f a = some b := by
  cases m with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem array_mem_toList_of_getElem?' {α : Type} {arr : Array α} {i : Nat} {x : α}
    (h : arr[i]? = some x) : x ∈ arr.toList := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp h
  exact Array.mem_toList_iff.mpr (Array.getElem_mem hlt)

theorem list_mem_of_mem_zipIdx' {α : Type} {l : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ l.zipIdx) : x ∈ l := by
  have aux : ∀ (l : List α) (k : Nat), (x, i) ∈ l.zipIdx k → x ∈ l := by
    intro l
    induction l with
    | nil => intro k h; simp at h
    | cons a rest ih =>
      intro k h
      simp only [List.zipIdx_cons, List.mem_cons] at h
      rcases h with h | h
      · injection h with h1 _
        exact h1 ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih (k + 1) h)
  exact aux l 0 h

theorem list_getElem?_of_mem_zipIdx {α : Type} {l : List α} {x : α} {i : Nat}
    (h : (x, i) ∈ l.zipIdx) : l[i]? = some x := by
  have aux : ∀ (l : List α) (k : Nat), (x, i) ∈ l.zipIdx k → k ≤ i ∧ l[i - k]? = some x := by
    intro l
    induction l with
    | nil => intro k h; simp at h
    | cons a rest ih =>
      intro k h
      simp only [List.zipIdx_cons, List.mem_cons] at h
      rcases h with h | h
      · injection h with h1 h2
        subst h1; subst h2
        exact ⟨Nat.le_refl _, by simp⟩
      · obtain ⟨hle, hget⟩ := ih (k + 1) h
        refine ⟨Nat.le_of_succ_le hle, ?_⟩
        have hsub : i - k = (i - (k + 1)) + 1 := by omega
        rw [hsub]
        exact hget
  have ⟨_, hget⟩ := aux l 0 h
  simpa using hget

theorem mem_zipIdx_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : (x, i) ∈ l.zipIdx := by
  have aux : ∀ (l : List α) (k i : Nat), l[i]? = some x → (x, k + i) ∈ l.zipIdx k := by
    intro l
    induction l with
    | nil => intro k i h; simp at h
    | cons a rest ih =>
      intro k i h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        simp [List.zipIdx_cons]
      | succ i =>
        simp only [List.getElem?_cons_succ] at h
        simp only [List.zipIdx_cons, List.mem_cons]
        right
        have heq : k + (i + 1) = (k + 1) + i := by omega
        rw [heq]
        exact ih (k + 1) i h
  have := aux l 0 i h
  simpa using this

/-- Iterate a pure `ForInStep` transition `n` times. -/
def iterStep {β : Type} (step : β → ForInStep β) : Nat → β → β
  | 0, b => b
  | n + 1, b =>
    match step b with
    | .done b' => b'
    | .yield b' => iterStep step n b'

theorem forIn_range'_id {β : Type} (step : β → ForInStep β) :
    ∀ (n s : Nat) (init : β),
      (forIn (m := Id) (List.range' s n 1) init (fun _ b => pure (step b))).run =
        iterStep step n init
  | 0, _, _ => rfl
  | n + 1, s, init => by
    rw [List.range'_succ, List.forIn_cons]
    change (match step init with
      | .done b => b
      | .yield b => (forIn (m := Id) (List.range' (s + 1) n 1) b (fun _ b => pure (step b))).run) =
      iterStep step (n + 1) init
    unfold iterStep
    cases step init with
    | done b => rfl
    | yield b => exact forIn_range'_id step n (s + 1) b

theorem forIn_range_id {β : Type} (step : β → ForInStep β) (n : Nat) (init : β) :
    (forIn (m := Id) [0:n] init (fun _ b => pure (step b))).run = iterStep step n init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : ([0:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  have hst : ([0:n] : Std.Legacy.Range).start = 0 := rfl
  have hsp : ([0:n] : Std.Legacy.Range).step = 1 := rfl
  rw [hsz, hst, hsp]
  exact forIn_range'_id step n 0 init

theorem forIn_range'_opt {β : Type} (step : β → ForInStep β) :
    ∀ (n s : Nat) (init : β),
      forIn (m := Option) (List.range' s n 1) init (fun _ b => pure (step b)) =
        some (iterStep step n init)
  | 0, _, _ => rfl
  | n + 1, s, init => by
    rw [List.range'_succ, List.forIn_cons]
    simp only [Opt_pure, Opt_bind_some]
    unfold iterStep
    cases step init with
    | done b => rfl
    | yield b => exact forIn_range'_opt step n (s + 1) b

theorem forIn_range_opt {β : Type} (step : β → ForInStep β) (n : Nat) (init : β) :
    forIn (m := Option) [0:n] init (fun _ b => pure (step b)) = some (iterStep step n init) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : ([0:n] : Std.Legacy.Range).size = n := by simp [Std.Legacy.Range.size]
  have hst : ([0:n] : Std.Legacy.Range).start = 0 := rfl
  have hsp : ([0:n] : Std.Legacy.Range).step = 1 := rfl
  rw [hsz, hst, hsp]
  exact forIn_range'_opt step n 0 init

theorem iterStep_eq_of_done {β : Type} {step : β → ForInStep β}
    {P : β → Prop} (hdone : ∀ b, P b → step b = .done b) :
    ∀ {n₁ n₂ : Nat} {b : β},
      P (iterStep step n₁ b) → P (iterStep step n₂ b) →
      iterStep step n₁ b = iterStep step n₂ b := by
  intro n₁
  induction n₁ with
  | zero =>
    intro n₂ b h₁ _
    cases n₂ with
    | zero => rfl
    | succ n₂ =>
      have hd := hdone b h₁
      simp only [iterStep, hd]
  | succ n₁ ih =>
    intro n₂ b h₁ h₂
    cases n₂ with
    | zero =>
      have hd := hdone b h₂
      simp only [iterStep, hd]
    | succ n₂ =>
      simp only [iterStep] at h₁ h₂ ⊢
      cases hs : step b with
      | done b' => rfl
      | yield b' =>
        rw [hs] at h₁ h₂
        exact ih h₁ h₂

/-! ## 1. `closureOf` Determinism, Nodup, and Reachability -/

/-- State of `closureOf`: `(seen, out, todo)`. -/
abbrev ClosureSt := Std.HashSet Address × Array Address × List Address

/-- Single iteration of `closureOf`'s `for` loop. -/
def closureStep (store : Ix.Kernel.Reader.Store) (st : ClosureSt) : ForInStep ClosureSt :=
  let (seen, out, todo) := st
  match todo with
  | [] => .done (seen, out, [])
  | a :: rest =>
    if seen.contains a then .yield (seen, out, rest)
    else
      let seen := seen.insert a
      match store a with
      | none => .yield (seen, out, rest)
      | some c =>
        let out := out.push a
        let todo := c.refs.toList ++ rest
        let todo := match c.info with
          | .dPrj p => p.block :: todo
          | .iPrj p => p.block :: todo
          | .cPrj p => p.block :: todo
          | .rPrj p => p.block :: todo
          | _ => todo
        .yield (seen, out, todo)

theorem closureOf_eq_iterStep (store : Ix.Kernel.Reader.Store) (roots : List Address) (fuel : Nat) :
    closureOf store roots fuel =
      let res := iterStep (closureStep store) fuel (∅, #[], roots)
      (res.2.1, res.2.2.isEmpty) := by
  unfold closureOf
  dsimp only
  have hfun : (fun (_ : Nat) (st : ClosureSt) =>
      (have seen := st.fst
       have __s := st.snd
       have out := __s.fst
       have todo := __s.snd
       match todo with
       | [] => pure (ForInStep.done (seen, out, todo))
       | a :: rest =>
         have todo := rest
         if seen.contains a = true then pure (ForInStep.yield (seen, out, todo))
         else
           have seen := seen.insert a
           match store a with
           | none => pure (ForInStep.yield (seen, out, todo))
           | some c =>
             have out := out.push a
             have todo := c.refs.toList ++ todo
             match c.info with
             | Ixon.ConstantInfo.dPrj p =>
               have todo := p.block :: todo
               pure (ForInStep.yield (seen, out, todo))
             | Ixon.ConstantInfo.iPrj p =>
               have todo := p.block :: todo
               pure (ForInStep.yield (seen, out, todo))
             | Ixon.ConstantInfo.cPrj p =>
               have todo := p.block :: todo
               pure (ForInStep.yield (seen, out, todo))
             | Ixon.ConstantInfo.rPrj p =>
               have todo := p.block :: todo
               pure (ForInStep.yield (seen, out, todo))
             | _ => pure (ForInStep.yield (seen, out, todo)) : Id (ForInStep ClosureSt))) =
      (fun _ st => pure (closureStep store st)) := by
    funext _ ⟨seen, out, todo⟩
    cases todo with
    | nil => rfl
    | cons a rest =>
      dsimp only [closureStep]
      cases hcon : seen.contains a with
      | true => simp
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases hst : store a with
        | none => rfl
        | some c =>
          dsimp only
          cases c.info <;> rfl
  have hgoal : (do
      let __s ← forIn (m := Id) [:fuel] ((∅, #[], roots) : ClosureSt) fun _ __s =>
          have seen := __s.fst
          have __s := __s.snd
          have out := __s.fst
          have todo := __s.snd
          match todo with
          | [] => pure (ForInStep.done (seen, out, todo))
          | a :: rest =>
            have todo := rest
            if seen.contains a = true then pure (ForInStep.yield (seen, out, todo))
            else
              have seen := seen.insert a
              match store a with
              | none => pure (ForInStep.yield (seen, out, todo))
              | some c =>
                have out := out.push a
                have todo := c.refs.toList ++ todo
                match c.info with
                | Ixon.ConstantInfo.dPrj p =>
                  have todo := p.block :: todo
                  pure (ForInStep.yield (seen, out, todo))
                | Ixon.ConstantInfo.iPrj p =>
                  have todo := p.block :: todo
                  pure (ForInStep.yield (seen, out, todo))
                | Ixon.ConstantInfo.cPrj p =>
                  have todo := p.block :: todo
                  pure (ForInStep.yield (seen, out, todo))
                | Ixon.ConstantInfo.rPrj p =>
                  have todo := p.block :: todo
                  pure (ForInStep.yield (seen, out, todo))
                | _ => pure (ForInStep.yield (seen, out, todo))
      pure (__s.2.1, __s.2.2.isEmpty)).run =
      let res := iterStep (closureStep store) fuel (∅, #[], roots)
      (res.2.1, res.2.2.isEmpty) := by
    rw [hfun]
    exact congrArg (fun res => (res.2.1, res.2.2.isEmpty)) (forIn_range_id (closureStep store) fuel (∅, #[], roots))
  exact hgoal

/-- If `closureOf` completes its walk under two fuel bounds, it produces the exact same output. -/
theorem closureOf_eq_of_walked (store : Ix.Kernel.Reader.Store) (roots : List Address)
    {f₁ f₂ : Nat}
    (h₁ : (closureOf store roots f₁).2 = true)
    (h₂ : (closureOf store roots f₂).2 = true) :
    closureOf store roots f₁ = closureOf store roots f₂ := by
  rw [closureOf_eq_iterStep] at h₁ h₂
  rw [closureOf_eq_iterStep, closureOf_eq_iterStep]
  have heq : iterStep (closureStep store) f₁ (∅, #[], roots) =
      iterStep (closureStep store) f₂ (∅, #[], roots) :=
    iterStep_eq_of_done (P := fun st => st.2.2.isEmpty = true)
      (fun ⟨seen, out, todo⟩ ht => by
        cases todo with
        | nil => rfl
        | cons _ _ => simp at ht)
      h₁ h₂
  rw [heq]

/-- Two completed `Reading.make` calls on the same `Subject` are identical regardless of fuel. -/
theorem Reading.make_eq_of_walked (s : Subject) {f₁ f₂ : Nat}
    (h₁ : (Reading.make s f₁).walked = true)
    (h₂ : (Reading.make s f₂).walked = true) :
    Reading.make s f₁ = Reading.make s f₂ := by
  unfold Reading.make at h₁ h₂ ⊢
  dsimp only at h₁ h₂ ⊢
  have heq := closureOf_eq_of_walked s.store (s.seeds ++ s.runTable ++ s.externs) h₁ h₂
  rw [heq]

/-- Loop invariant for `closureOf`:
1. `out` has no duplicates.
2. `a ∈ out.toList ↔ seen.contains a = true ∧ (store a).isSome`.
3. Every `a` in `roots` is either already `seen` or still in `todo`.
4. Every `a` in `out` has all its `refs` (and projection `block`, if any) either `seen` or in `todo`. -/
structure ClosureInv (store : Ix.Kernel.Reader.Store) (roots : List Address) (st : ClosureSt) : Prop where
  nodup : st.2.1.toList.Nodup
  out_iff : ∀ a, a ∈ st.2.1.toList ↔ st.1.contains a = true ∧ (store a).isSome = true
  roots_cov : ∀ a ∈ roots, st.1.contains a = true ∨ a ∈ st.2.2
  refs_cov : ∀ a c, a ∈ st.2.1.toList → store a = some c →
    (∀ b ∈ c.refs.toList, st.1.contains b = true ∨ b ∈ st.2.2) ∧
    (match c.info with
     | .dPrj p => st.1.contains p.block = true ∨ p.block ∈ st.2.2
     | .iPrj p => st.1.contains p.block = true ∨ p.block ∈ st.2.2
     | .cPrj p => st.1.contains p.block = true ∨ p.block ∈ st.2.2
     | .rPrj p => st.1.contains p.block = true ∨ p.block ∈ st.2.2
     | _ => True)

theorem closureInv_step {store : Ix.Kernel.Reader.Store} {roots : List Address} {st : ClosureSt}
    (h : ClosureInv store roots st) :
    match closureStep store st with
    | .done st' | .yield st' => ClosureInv store roots st' := by
  obtain ⟨seen, out, todo⟩ := st
  cases todo with
  | nil => exact h
  | cons a rest =>
    dsimp only [closureStep]
    by_cases hcon : seen.contains a = true
    · simp only [hcon, ↓reduceIte]
      have hcov : ∀ x, seen.contains x = true ∨ x ∈ a :: rest → seen.contains x = true ∨ x ∈ rest := by
        intro x hx
        rcases hx with hs | hmem
        · exact Or.inl hs
        · rcases List.mem_cons.mp hmem with rfl | hrest
          · exact Or.inl hcon
          · exact Or.inr hrest
      refine ⟨h.nodup, h.out_iff, fun x hx => hcov x (h.roots_cov x hx), fun x cx hx hstx => ?_⟩
      obtain ⟨hr, hp⟩ := h.refs_cov x cx hx hstx
      refine ⟨fun b hb => hcov b (hr b hb), ?_⟩
      cases hci : cx.info <;> rw [hci] at hp <;> first | exact trivial | exact hcov _ hp
    · simp only [hcon, Bool.false_eq_true, ↓reduceIte]
      have hcov_ins : ∀ {todo' : List Address}, (∀ y ∈ rest, y ∈ todo') →
          ∀ x, seen.contains x = true ∨ x ∈ a :: rest → (seen.insert a).contains x = true ∨ x ∈ todo' := by
        intro todo' hsub x hx
        rcases hx with hs | hmem
        · left; simp [Std.HashSet.contains_insert, hs]
        · rcases List.mem_cons.mp hmem with rfl | hrest
          · left; simp [Std.HashSet.contains_insert]
          · right; exact hsub x hrest
      cases hstore : store a with
      | none =>
        refine ⟨h.nodup, ?_, fun x hx => hcov_ins (fun _ hy => hy) x (h.roots_cov x hx), fun x cx hx hstx => ?_⟩
        · intro x
          rw [h.out_iff x]
          simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
          constructor
          · intro ⟨hs, hst⟩; exact ⟨Or.inr hs, hst⟩
          · intro ⟨hdisj, hst⟩
            rcases hdisj with rfl | hs
            · simp [hstore] at hst
            · exact ⟨hs, hst⟩
        · obtain ⟨hr, hp⟩ := h.refs_cov x cx hx hstx
          refine ⟨fun b hb => hcov_ins (fun _ hy => hy) b (hr b hb), ?_⟩
          cases hci : cx.info <;> rw [hci] at hp <;> first | exact trivial | exact hcov_ins (fun _ hy => hy) _ hp
      | some c =>
        have hnotmem : a ∉ out.toList := by
          intro hmem
          have := (h.out_iff a).mp hmem
          exact hcon this.1
        have hnodup' : (out.push a).toList.Nodup := by
          rw [Array.toList_push]
          exact List.nodup_append.mpr ⟨h.nodup, nodup_singleton _, fun x hx y hy hxy => by
            simp only [List.mem_singleton] at hy; subst hy; subst hxy; exact hnotmem hx⟩
        have hout_iff' : ∀ x, x ∈ (out.push a).toList ↔ (seen.insert a).contains x = true ∧ (store x).isSome = true := by
          intro x
          rw [Array.toList_push, List.mem_append, List.mem_singleton, h.out_iff x]
          simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
          constructor
          · rintro (⟨hs, hst⟩ | rfl)
            · exact ⟨Or.inr hs, hst⟩
            · exact ⟨Or.inl rfl, by simp [hstore]⟩
          · rintro ⟨rfl | hs, hst⟩
            · exact Or.inr rfl
            · exact Or.inl ⟨hs, hst⟩
        let todo' : List Address :=
          match c.info with
          | .dPrj p => p.block :: (c.refs.toList ++ rest)
          | .iPrj p => p.block :: (c.refs.toList ++ rest)
          | .cPrj p => p.block :: (c.refs.toList ++ rest)
          | .rPrj p => p.block :: (c.refs.toList ++ rest)
          | _ => c.refs.toList ++ rest
        have hsub_rest : ∀ y ∈ rest, y ∈ todo' := by
          intro y hy
          dsimp only [todo']
          cases c.info <;> simp [hy]
        have hsub_refs : ∀ b ∈ c.refs.toList, b ∈ todo' := by
          intro b hb
          dsimp only [todo']
          cases c.info <;> simp [hb]
        refine ⟨hnodup', hout_iff', fun x hx => hcov_ins hsub_rest x (h.roots_cov x hx), ?_⟩
        intro x cx hx hstx
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · obtain ⟨hr, hp⟩ := h.refs_cov x cx hx hstx
          refine ⟨fun b hb => hcov_ins hsub_rest b (hr b hb), ?_⟩
          cases hci : cx.info <;> rw [hci] at hp <;> first | exact trivial | exact hcov_ins hsub_rest _ hp
        · rw [hstore] at hstx; cases hstx
          refine ⟨fun b hb => Or.inr (hsub_refs b hb), ?_⟩
          dsimp only [todo']
          cases c.info <;> simp

theorem closureInv_iter (store : Ix.Kernel.Reader.Store) (roots : List Address) (fuel : Nat) :
    ClosureInv store roots (iterStep (closureStep store) fuel (∅, #[], roots)) := by
  have aux : ∀ n st, ClosureInv store roots st →
      ClosureInv store roots (iterStep (closureStep store) n st) := by
    intro n
    induction n with
    | zero => intro st h; exact h
    | succ n ih =>
      intro st h
      have hstep := closureInv_step h
      unfold iterStep
      cases hs : closureStep store st with
      | done st' => rw [hs] at hstep; exact hstep
      | yield st' => rw [hs] at hstep; exact ih st' hstep
  apply aux
  refine ⟨by simp, ?_, fun a ha => Or.inr ha, fun _ _ h _ => by simp at h⟩
  intro a
  simp [Std.HashSet.contains_empty]

theorem closureOf_nodup (store : Ix.Kernel.Reader.Store) (roots : List Address) (fuel : Nat) :
    (closureOf store roots fuel).1.toList.Nodup := by
  rw [closureOf_eq_iterStep]
  exact (closureInv_iter store roots fuel).nodup

theorem closureOf_mem_of_root {store : Ix.Kernel.Reader.Store} {roots : List Address} {fuel : Nat}
    (hwalk : (closureOf store roots fuel).2 = true)
    {a : Address} {c : Ixon.Constant} (hroot : a ∈ roots) (hstore : store a = some c) :
    a ∈ (closureOf store roots fuel).1.toList := by
  rw [closureOf_eq_iterStep] at hwalk ⊢
  have hinv := closureInv_iter store roots fuel
  have hnil : (iterStep (closureStep store) fuel (∅, #[], roots)).2.2 = [] :=
    List.isEmpty_iff.mp hwalk
  rcases hinv.roots_cov a hroot with hseen | htodo
  · exact (hinv.out_iff a).mpr ⟨hseen, by simp [hstore]⟩
  · rw [hnil] at htodo; cases htodo

theorem closureOf_mem_of_ref {store : Ix.Kernel.Reader.Store} {roots : List Address} {fuel : Nat}
    (hwalk : (closureOf store roots fuel).2 = true)
    {a b : Address} {ca cb : Ixon.Constant}
    (ha : a ∈ (closureOf store roots fuel).1.toList)
    (hsa : store a = some ca) (hb : b ∈ ca.refs.toList) (hsb : store b = some cb) :
    b ∈ (closureOf store roots fuel).1.toList := by
  rw [closureOf_eq_iterStep] at hwalk ha ⊢
  have hinv := closureInv_iter store roots fuel
  have hnil : (iterStep (closureStep store) fuel (∅, #[], roots)).2.2 = [] :=
    List.isEmpty_iff.mp hwalk
  rcases (hinv.refs_cov a ca ha hsa).1 b hb with hseen | htodo
  · exact (hinv.out_iff b).mpr ⟨hseen, by simp [hsb]⟩
  · rw [hnil] at htodo; cases htodo

theorem closureOf_mem_of_prj {store : Ix.Kernel.Reader.Store} {roots : List Address} {fuel : Nat}
    (hwalk : (closureOf store roots fuel).2 = true)
    {a b : Address} {ca cb : Ixon.Constant}
    (ha : a ∈ (closureOf store roots fuel).1.toList)
    (hsa : store a = some ca)
    (hprj : (∃ p, ca.info = .dPrj p ∧ p.block = b) ∨
            (∃ p, ca.info = .iPrj p ∧ p.block = b) ∨
            (∃ p, ca.info = .cPrj p ∧ p.block = b) ∨
            (∃ p, ca.info = .rPrj p ∧ p.block = b))
    (hsb : store b = some cb) :
    b ∈ (closureOf store roots fuel).1.toList := by
  rw [closureOf_eq_iterStep] at hwalk ha ⊢
  have hinv := closureInv_iter store roots fuel
  have hnil : (iterStep (closureStep store) fuel (∅, #[], roots)).2.2 = [] :=
    List.isEmpty_iff.mp hwalk
  have hp := (hinv.refs_cov a ca ha hsa).2
  have hdisj : (iterStep (closureStep store) fuel (∅, #[], roots)).1.contains b = true ∨
      b ∈ (iterStep (closureStep store) fuel (∅, #[], roots)).2.2 := by
    rcases hprj with ⟨p, hi, rfl⟩ | ⟨p, hi, rfl⟩ | ⟨p, hi, rfl⟩ | ⟨p, hi, rfl⟩ <;>
      · rw [hi] at hp; exact hp
  rcases hdisj with hseen | htodo
  · exact (hinv.out_iff b).mpr ⟨hseen, by simp [hsb]⟩
  · rw [hnil] at htodo; cases htodo

/-! ## 2. `unshare` Pigeonhole Lemma, `readSkel`/`readTele` Independence, and `caseShape` Arity -/

theorem unshare_go_nonShare {c : Ixon.Constant} {e : Ixon.Expr}
    (hns : ∀ j, e ≠ .share j) (n : Nat) :
    Ix.Kernel.Reader.unshare.go c n e = e := by
  cases n with
  | zero => rfl
  | succ n =>
    cases e with
    | share j => exact False.elim (hns j rfl)
    | _ => rfl

theorem unshare_go_mono {c : Ixon.Constant} {e res : Ixon.Expr}
    (hns : ∀ j, res ≠ .share j) :
    ∀ {n₁ n₂ : Nat}, n₁ ≤ n₂ →
      Ix.Kernel.Reader.unshare.go c n₁ e = res →
      Ix.Kernel.Reader.unshare.go c n₂ e = res := by
  intro n₁
  induction n₁ generalizing e with
  | zero =>
    intro n₂ _ h
    simp only [Ix.Kernel.Reader.unshare.go] at h
    subst h
    exact unshare_go_nonShare hns n₂
  | succ n₁ ih =>
    intro n₂ hle h
    cases n₂ with
    | zero => omega
    | succ n₂ =>
      cases e with
      | share i =>
        simp only [Ix.Kernel.Reader.unshare.go] at h ⊢
        cases hs : c.sharing[i.toNat]? with
        | none => rw [hs] at h; exact False.elim (hns i h.symm)
        | some ent =>
          rw [hs] at h
          exact ih (Nat.le_of_succ_le_succ hle) h
      | _ =>
        simp only [Ix.Kernel.Reader.unshare.go] at h ⊢
        exact h

/-- A list of distinct naturals all strictly below `N` has length at most `N`. -/
theorem nodup_lt_length_le : ∀ {N : Nat} {l : List Nat},
    l.Nodup → (∀ x ∈ l, x < N) → l.length ≤ N := by
  have filter_len : ∀ (k : Nat) (l : List Nat), l.Nodup →
      l.length ≤ (l.filter (· != k)).length + 1 := by
    intro k l
    induction l with
    | nil => intro _; simp
    | cons a rest ih =>
      intro hnd
      obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
      by_cases hak : a = k
      · subst hak
        have hnone : rest.filter (· != a) = rest :=
          List.filter_eq_self.mpr fun x hx => by
            simp only [bne_iff_ne, ne_eq]
            intro hxa; subst hxa; exact hna hx
        simp [hnone]
      · have hne : (a != k) = true := bne_iff_ne.mpr hak
        have ih' := ih hnd'
        simp [hne]
        omega
  intro N
  induction N with
  | zero =>
    intro l _ hlt
    cases l with
    | nil => exact Nat.le_refl 0
    | cons x _ => exact absurd (hlt x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | succ N ih =>
    intro l hnd hlt
    have hnd' : (l.filter (· != N)).Nodup := hnd.filter _
    have hlt' : ∀ x ∈ l.filter (· != N), x < N := by
      intro x hx
      obtain ⟨hm, hne⟩ := List.mem_filter.mp hx
      have hne' : x ≠ N := bne_iff_ne.mp hne
      have hxlt := hlt x hm
      omega
    have hlen' := ih hnd' hlt'
    have hfl := filter_len N l hnd
    omega

/-- The list of sharing indices followed in `n` steps of `unshare.go`. -/
def shareTrace (c : Ixon.Constant) : Nat → Ixon.Expr → List Nat
  | 0, _ => []
  | n + 1, .share i =>
    match c.sharing[i.toNat]? with
    | some ent => i.toNat :: shareTrace c n ent
    | none => []
  | _, _ => []

theorem shareTrace_lt {c : Ixon.Constant} : ∀ n e k, k ∈ shareTrace c n e → k < c.sharing.size
  | 0, _, _, hk => by simp [shareTrace] at hk
  | n + 1, .share i, k, hk => by
    simp only [shareTrace] at hk
    cases hs : c.sharing[i.toNat]? with
    | none => rw [hs] at hk; simp at hk
    | some ent =>
      rw [hs] at hk
      rcases List.mem_cons.mp hk with rfl | hk'
      · exact (Array.getElem?_eq_some_iff.mp hs).1
      · exact shareTrace_lt n ent k hk'
  | n + 1, .sort _, _, hk | n + 1, .var _, _, hk | n + 1, .ref _ _, _, hk
  | n + 1, .recur _ _, _, hk | n + 1, .prj _ _ _, _, hk | n + 1, .str _, _, hk
  | n + 1, .nat _, _, hk | n + 1, .app _ _, _, hk | n + 1, .lam _ _, _, hk
  | n + 1, .all _ _, _, hk | n + 1, .letE _ _ _ _ _, _, hk => by simp [shareTrace] at hk

theorem shareTrace_mem_go {c : Ixon.Constant} {res : Ixon.Expr} :
    ∀ {n : Nat} {e : Ixon.Expr} {k : Nat},
      Ix.Kernel.Reader.unshare.go c n e = res →
      k ∈ shareTrace c n e →
      ∃ m ≤ n, ∀ j : UInt64, j.toNat = k → Ix.Kernel.Reader.unshare.go c m (.share j) = res
  | 0, _, _, _, hk => by simp [shareTrace] at hk
  | n + 1, .share i, k, hgo, hk => by
    simp only [shareTrace] at hk
    cases hs : c.sharing[i.toNat]? with
    | none => rw [hs] at hk; simp at hk
    | some ent =>
      rw [hs] at hk
      simp only [Ix.Kernel.Reader.unshare.go, hs] at hgo
      rcases List.mem_cons.mp hk with rfl | hk'
      · refine ⟨n + 1, Nat.le_refl _, fun j hj => ?_⟩
        simp only [Ix.Kernel.Reader.unshare.go, hj, hs]
        exact hgo
      · obtain ⟨m, hm, hjm⟩ := shareTrace_mem_go hgo hk'
        exact ⟨m, Nat.le_succ_of_le hm, hjm⟩
  | n + 1, .sort _, _, _, hk | n + 1, .var _, _, _, hk | n + 1, .ref _ _, _, _, hk
  | n + 1, .recur _ _, _, _, hk | n + 1, .prj _ _ _, _, _, hk | n + 1, .str _, _, _, hk
  | n + 1, .nat _, _, _, hk | n + 1, .app _ _, _, _, hk | n + 1, .lam _ _, _, _, hk
  | n + 1, .all _ _, _, _, hk | n + 1, .letE _ _ _ _ _, _, _, hk => by simp [shareTrace] at hk

theorem shareTrace_min_nodup_len {c : Ixon.Constant} {res : Ixon.Expr}
    (hns : ∀ j, res ≠ .share j) :
    ∀ {m : Nat} {e : Ixon.Expr},
      Ix.Kernel.Reader.unshare.go c m e = res →
      (∀ m' < m, Ix.Kernel.Reader.unshare.go c m' e ≠ res) →
      (shareTrace c m e).Nodup ∧ (shareTrace c m e).length = m := by
  intro m
  induction m with
  | zero =>
    intro e _ _
    exact ⟨List.nodup_nil, rfl⟩
  | succ m ih =>
    intro e hgo hmin
    cases e with
    | share i =>
      simp only [Ix.Kernel.Reader.unshare.go] at hgo
      cases hs : c.sharing[i.toNat]? with
      | none => rw [hs] at hgo; exact False.elim (hns i hgo.symm)
      | some ent =>
        rw [hs] at hgo
        have hmin' : ∀ m' < m, Ix.Kernel.Reader.unshare.go c m' ent ≠ res := by
          intro m' hm' heq
          apply hmin (m' + 1) (Nat.succ_lt_succ hm')
          simp only [Ix.Kernel.Reader.unshare.go, hs]
          exact heq
        obtain ⟨hnd, hlen⟩ := ih hgo hmin'
        have hnotmem : i.toNat ∉ shareTrace c m ent := by
          intro hmem
          obtain ⟨k, hkle, hjk⟩ := shareTrace_mem_go hgo hmem
          exact hmin k (Nat.lt_succ_of_le hkle) (hjk i rfl)
        simp only [shareTrace, hs]
        exact ⟨List.nodup_cons.mpr ⟨hnotmem, hnd⟩, by simp [hlen]⟩
    | _ =>
      simp only [Ix.Kernel.Reader.unshare.go] at hgo
      exact False.elim (hmin 0 (Nat.zero_lt_succ m) hgo)

/-- Any `unshare.go` chain reaching a non-`.share` expression succeeds within `c.sharing.size` steps. -/
theorem unshare_go_le_size {c : Ixon.Constant} {res : Ixon.Expr}
    (hns : ∀ j, res ≠ .share j) {n : Nat} {e : Ixon.Expr}
    (hgo : Ix.Kernel.Reader.unshare.go c n e = res) :
    Ix.Kernel.Reader.unshare.go c c.sharing.size e = res := by
  classical
  obtain ⟨m, _, hm, hmin⟩ := exists_min_nat (P := fun k => Ix.Kernel.Reader.unshare.go c k e = res) n hgo
  obtain ⟨hnd, hlen⟩ := shareTrace_min_nodup_len hns hm hmin
  have hle : m ≤ c.sharing.size := by
    rw [← hlen]
    exact nodup_lt_length_le hnd (shareTrace_lt m e)
  exact unshare_go_mono hns hle hm

/-- **Pigeonhole congruence for `unshare`**: stepping through one valid `.share i` entry never
changes the non-`.share` result of `unshare`. -/
theorem unshare_share_iff_nonShare {c : Ixon.Constant} {i : UInt64} {ent res : Ixon.Expr}
    (hs : c.sharing[i.toNat]? = some ent) (hns : ∀ j, res ≠ .share j) :
    Ix.Kernel.Reader.unshare c (.share i) = res ↔ Ix.Kernel.Reader.unshare c ent = res := by
  unfold Ix.Kernel.Reader.unshare
  simp only [Ix.Kernel.Reader.unshare.go, hs]
  constructor
  · intro h
    exact unshare_go_mono hns (Nat.le_succ _) h
  · intro h
    exact unshare_go_le_size hns h

theorem unshare_share_iff_lam {c : Ixon.Constant} {i : UInt64} {ent ty b : Ixon.Expr}
    (hs : c.sharing[i.toNat]? = some ent) :
    Ix.Kernel.Reader.unshare c (.share i) = .lam ty b ↔ Ix.Kernel.Reader.unshare c ent = .lam ty b :=
  unshare_share_iff_nonShare hs (fun _ h => by cases h)

/-- `readSkel` depends only on `x.s`, `x.c`, `x.rm`, `x.recur` (independent of `x.cl` and `x.rd.cx`). -/
theorem readSkel_congr {x₁ x₂ : RCx}
    (hs : x₁.s = x₂.s) (hc : x₁.c = x₂.c) (hrm : x₁.rm = x₂.rm) (hrec : x₁.recur = x₂.recur) :
    ∀ n e, readSkel x₁ n e = readSkel x₂ n e := by
  have hisInd : ∀ e, x₁.isInd e = x₂.isInd e := by
    intro e
    unfold RCx.isInd RCx.refAt
    rw [hs, hc, hrec]
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih =>
    intro e
    funext cs
    change (readSkel x₁ (n + 1) e).run cs = (readSkel x₂ (n + 1) e).run cs
    unfold readSkel
    cases view e with
    | error err => simp only [RM_run_bind, RM_run_lift_err]
    | ok v =>
      simp only [RM_run_bind, RM_run_lift_ok]
      cases v with
      | all ty b =>
        simp only [RM_run_bind]
        cases nextBinder.run cs with
        | error _ => rfl
        | ok p1 =>
          dsimp only
          rw [ih ty]
          cases (readSkel x₂ n ty).run p1.2 with
          | error _ => rfl
          | ok p2 => dsimp only; rw [ih b]
      | sort | nat _ | str _ | var _ => rfl
      | ref _ | recur _ => simp only [hisInd]
      | app _ _ =>
        cases ixSpine n e with
        | error err => simp only [RM_run_bind, RM_run_lift_err]
        | ok ha =>
          simp only [RM_run_bind, RM_run_lift_ok, hisInd, hrm]
          by_cases hi : x₂.isInd ha.1 = true
          · simp only [hi, ↓reduceIte]
            have hfun : (fun (a : Ixon.Expr) (s : Skel) => (do
                let __do_lift ← readSkel x₁ n a
                pure (ForInStep.yield (.dataApp s __do_lift)) : RM (ForInStep Skel))) =
              (fun (a : Ixon.Expr) (s : Skel) => (do
                let __do_lift ← readSkel x₂ n a
                pure (ForInStep.yield (.dataApp s __do_lift)) : RM (ForInStep Skel))) := by
              funext a s; rw [ih a]
            rw [hfun]
          · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      | share i =>
        dsimp only
        rw [hc, hrm]
        cases x₂.c.sharing[i]? with
        | none => rfl
        | some ent => dsimp only; rw [ih ent]
      | prj _ _ _ | lam _ _ | letE _ _ _ _ => dsimp only; rw [hrm]

/-- `readTele` depends only on `x.s`, `x.c`, `x.rm`, `x.recur` and its continuation `k`. -/
theorem readTele_congr {β : Type} {x₁ x₂ : RCx}
    (hs : x₁.s = x₂.s) (hc : x₁.c = x₂.c) (hrm : x₁.rm = x₂.rm) (hrec : x₁.recur = x₂.recur)
    {lam : Bool} {k₁ k₂ : List TeleBinder → Ixon.Expr → RM β}
    (hk : ∀ bs e, k₁ bs e = k₂ bs e) :
    ∀ n acc e, readTele x₁ lam k₁ n acc e = readTele x₂ lam k₂ n acc e := by
  intro n
  induction n with
  | zero => intro acc e; rfl
  | succ n ih =>
    intro acc e
    funext cs
    change (readTele x₁ lam k₁ (n + 1) acc e).run cs = (readTele x₂ lam k₂ (n + 1) acc e).run cs
    unfold readTele
    cases view e with
    | error err => simp only [RM_run_bind, RM_run_lift_err]
    | ok v =>
      simp only [RM_run_bind, RM_run_lift_ok]
      cases v with
      | all ty b =>
        cases lam with
        | true => simp only [↓reduceIte]; rw [hk]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, RM_run_bind]
          cases nextBinder.run cs with
          | error _ => rfl
          | ok p1 =>
            dsimp only
            rw [readSkel_congr hs hc hrm hrec n ty]
            cases (readSkel x₂ n ty).run p1.2 with
            | error _ => rfl
            | ok p2 => dsimp only; rw [ih]
      | lam ty b =>
        cases lam with
        | true =>
          simp only [↓reduceIte, RM_run_bind]
          cases nextBinder.run cs with
          | error _ => rfl
          | ok p1 =>
            dsimp only
            rw [readSkel_congr hs hc hrm hrec n ty]
            cases (readSkel x₂ n ty).run p1.2 with
            | error _ => rfl
            | ok p2 => dsimp only; rw [ih]
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [hk]
      | share i =>
        dsimp only
        rw [hc, hrm]
        cases x₂.c.sharing[i]? with
        | none => dsimp only; rw [hk]
        | some ent =>
          dsimp only
          cases continuesTele x₂.c lam ent with
          | true => simp only [↓reduceIte]; rw [ih]
          | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [hk]
      | _ => dsimp only; rw [hk]

/-- `readForalls` on `rd.rcx cl r` equals `readForalls` on `(Reading.bare rd.s).rcx noClasses r`. -/
theorem readForalls_rcx_eq_bare {rd : Reading} {cl : Classifier} {r : Ref} {x x0 : RCx}
    (hx : rd.rcx cl r = .ok x) (hx0 : (Reading.bare rd.s).rcx noClasses r = .ok x0)
    (fuel : Nat) (ty : Ixon.Expr) :
    x.c = x0.c ∧ x.rm = x0.rm ∧
    readForalls x fuel ty (readSkel x fuel) = readForalls x0 fuel ty (readSkel x0 fuel) := by
  unfold Reading.rcx at hx hx0
  cases hst : rd.s.store r.block with
  | none =>
    simp only [hst, Ex_throw] at hx
    cases hx
  | some c =>
    have hst0 : (Reading.bare rd.s).s.store r.block = some c := hst
    simp only [hst, hst0] at hx hx0
    cases hrm : recordModes c with
    | error e => simp [hrm] at hx
    | ok rm =>
      simp only [hrm, Ex_bind_ok, Ex_pure, Except.ok.injEq] at hx hx0
      have h1 : x.s = x0.s := by rw [← hx, ← hx0]; rfl
      have h2 : x.c = x0.c := by rw [← hx, ← hx0]
      have h3 : x.rm = x0.rm := by rw [← hx, ← hx0]
      have h4 : x.recur = x0.recur := by rw [← hx, ← hx0]
      refine ⟨h2, h3, ?_⟩
      unfold readForalls
      exact readTele_congr h1 h2 h3 h4 (fun bs e => by
        rw [readSkel_congr h1 h2 h3 h4 fuel e]) fuel [] ty

theorem nextBinder_nodes {cs cs' : Cursor} {m : AllMode}
    (h : nextBinder.run cs = .ok (m, cs')) : cs'.nodes = cs.nodes := by
  unfold nextBinder nextNode at h
  simp only [RM_run_bind, RM_run_get] at h
  cases hget : cs.nodes[cs.pos]? with
  | none => simp [hget] at h
  | some nd =>
    simp only [hget, RM_run_bind, RM_run_set, RM_run_pure] at h
    cases nd with
    | share _ => simp at h
    | binder _ => simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]

theorem nextShare_nodes {cs cs' : Cursor} {v : Nat}
    (h : nextShare.run cs = .ok (v, cs')) : cs'.nodes = cs.nodes := by
  unfold nextShare nextNode at h
  simp only [RM_run_bind, RM_run_get] at h
  cases hget : cs.nodes[cs.pos]? with
  | none => simp [hget] at h
  | some nd =>
    simp only [hget, RM_run_bind, RM_run_set, RM_run_pure] at h
    cases nd with
    | binder _ => simp at h
    | share _ => simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.2]

theorem inBlock_nodes_preserved {α : Type} {rm : RecordModes} {key : BlockKey} {k : RM α}
    {cs cs' : Cursor} {a : α}
    (h : (inBlock rm key k).run cs = .ok (a, cs')) :
    ∃ cs₁, k.run { nodes := (rm.block? key).getD #[], pos := 0 } = .ok (a, cs₁) ∧ cs' = cs := by
  unfold inBlock at h
  simp only [RM_run_bind, RM_run_get, RM_run_set] at h
  cases hk : k.run { nodes := (rm.block? key).getD #[], pos := 0 } with
  | error _ => simp [hk] at h
  | ok p =>
    obtain ⟨a1, cs1⟩ := p
    simp only [hk] at h
    split at h
    · simp only [RM_run_bind, RM_run_pure, RM_run_set, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨cs1, rfl, rfl⟩
    · simp only [RM_run_bind, RM_run_throw] at h; cases h

theorem enterShare_ok {α : Type} {rm : RecordModes} {n : Nat} {k : RM α}
    {cs cs' : Cursor} {a : α}
    (h : (enterShare rm n k).run cs = .ok (a, cs')) :
    ∃ key cs₁, k.run { nodes := (rm.block? key).getD #[], pos := 0 } = .ok (a, cs₁) ∧
      cs'.nodes = cs.nodes := by
  unfold enterShare at h
  split at h
  · simp only [RM_run_bind] at h
    cases hns : nextShare.run cs with
    | error _ => simp [hns] at h
    | ok pns =>
      simp only [hns] at h
      split at h
      · obtain ⟨cs₁, hk, rfl⟩ := inBlock_nodes_preserved h
        exact ⟨_, cs₁, hk, nextShare_nodes hns⟩
      · simp only [RM_run_bind, RM_run_throw] at h; cases h
  · obtain ⟨cs₁, hk, rfl⟩ := inBlock_nodes_preserved h
    exact ⟨_, cs₁, hk, rfl⟩

/-! ### `caseShape` arity equals `readLamNodes`'s `lams.length` -/

/-- Single step of `caseShape`'s λ-stripping loop. -/
def caseLamStep (c : Ixon.Constant) (kb : Nat × Ixon.Expr) : ForInStep (Nat × Ixon.Expr) :=
  match view (Ix.Kernel.Reader.unshare c kb.2) with
  | .ok (.lam _ b) => .yield (kb.1 + 1, b)
  | _ => .done kb

theorem caseLamStep_unshare_eq {c : Ixon.Constant} {k : Nat} {e₁ e₂ : Ixon.Expr}
    (hu : Ix.Kernel.Reader.unshare c e₁ = Ix.Kernel.Reader.unshare c e₂) :
    caseLamStep c (k, e₁) = match caseLamStep c (k, e₂) with
      | .yield p => .yield p
      | .done _ => .done (k, e₁) := by
  unfold caseLamStep
  rw [hu]
  cases view (Ix.Kernel.Reader.unshare c e₂) with
  | error _ => rfl
  | ok v => cases v <;> rfl

theorem iterStep_caseLamStep_shift {c : Ixon.Constant} :
    ∀ n k₁ k₂ e,
      (iterStep (caseLamStep c) n (k₁ + k₂, e)).1 = k₁ + (iterStep (caseLamStep c) n (k₂, e)).1 ∧
      (iterStep (caseLamStep c) n (k₁ + k₂, e)).2 = (iterStep (caseLamStep c) n (k₂, e)).2 := by
  intro n
  induction n with
  | zero => intro _ _ _; exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro k₁ k₂ e
    simp only [iterStep, caseLamStep]
    cases view (Ix.Kernel.Reader.unshare c e) with
    | error _ => exact ⟨rfl, rfl⟩
    | ok v =>
      cases v with
      | lam _ b =>
        have hadd : k₁ + k₂ + 1 = k₁ + (k₂ + 1) := by omega
        rw [hadd]
        exact ih k₁ (k₂ + 1) b
      | _ => exact ⟨rfl, rfl⟩

theorem caseLam_zero_of_nonLam {c : Ixon.Constant} {e : Ixon.Expr}
    (h : ∀ ty b, Ix.Kernel.Reader.unshare c e ≠ .lam ty b) :
    ∀ m, (iterStep (caseLamStep c) m (0, e)).1 = 0
  | 0 => rfl
  | _ + 1 => by
    simp only [iterStep, caseLamStep]
    cases hu : Ix.Kernel.Reader.unshare c e with
    | lam ty b => exact False.elim (h ty b hu)
    | _ => simp [view]

/-- If `caseLamStep` stops on `e` at a non-`.lam` expression after `iterStep`, then `readTele x true`
consumes the exact same number of λs as `iterStep (caseLamStep x.c) n (0, e)`. -/
theorem readTele_lam_length_eq_caseLam {β : Type} {x : RCx} {k : List TeleBinder → Ixon.Expr → RM β}
    {m : Nat} :
    ∀ {fuel : Nat} {acc : List TeleBinder} {e : Ixon.Expr} {cs cs' : Cursor} {lams : List TeleBinder}
      {body : Ixon.Expr} {v : β},
      (∀ ty b, Ix.Kernel.Reader.unshare x.c (iterStep (caseLamStep x.c) m (0, e)).2 ≠ .lam ty b) →
      (readTele x true (fun ls bd => do pure (ls, bd, ← k ls bd)) fuel acc e).run cs =
        .ok ((lams, body, v), cs') →
      lams.length = acc.length + (iterStep (caseLamStep x.c) m (0, e)).1 := by
  intro fuel
  induction fuel generalizing m with
  | zero =>
    intro _ _ _ _ _ _ _ _ h
    simp [readTele] at h
  | succ fuel ih =>
    intro acc e cs cs' lams body v hnonlam hrun
    unfold readTele at hrun
    cases e with
    | lam ty b =>
      simp only [view, RM_run_bind, RM_run_lift, Ex_pure, Ex_map_ok, ↓reduceIte] at hrun
      have hu : Ix.Kernel.Reader.unshare x.c (.lam ty b) = .lam ty b :=
        unshare_go_nonShare (fun _ h => by cases h) _
      cases m with
      | zero =>
        simp only [iterStep] at hnonlam
        exact False.elim (hnonlam ty b hu)
      | succ m' =>
        dsimp only [iterStep, caseLamStep] at hnonlam ⊢
        rw [hu] at hnonlam ⊢
        dsimp only [view, Ex_pure] at hnonlam ⊢
        have hshift := iterStep_caseLamStep_shift (c := x.c) m' 1 0 b
        have hnonlam' : ∀ ty' b', Ix.Kernel.Reader.unshare x.c (iterStep (caseLamStep x.c) m' (0, b)).2 ≠ .lam ty' b' := by
          rw [← hshift.2]; exact hnonlam
        cases h1 : nextBinder.run cs with
        | error _ => simp [h1] at hrun
        | ok p1 =>
          simp only [h1] at hrun
          cases h2 : (readSkel x fuel ty).run p1.2 with
          | error _ => simp [h2] at hrun
          | ok p2 =>
            simp only [h2] at hrun
            have hih := ih (m := m') hnonlam' hrun
            simp only [List.length_cons] at hih
            rw [hshift.1]
            omega
    | share i =>
      simp only [view, RM_run_bind, RM_run_lift, Ex_pure, Ex_map_ok] at hrun
      cases hs : x.c.sharing[i.toNat]? with
      | none =>
        simp only [hs, RM_run_bind] at hrun
        have hu : Ix.Kernel.Reader.unshare x.c (.share i) = .share i := by
          unfold Ix.Kernel.Reader.unshare
          simp [Ix.Kernel.Reader.unshare.go, hs]
        rw [caseLam_zero_of_nonLam (by intro _ _ h; rw [hu] at h; cases h) m]
        cases hk : (k acc.reverse (.share i)).run cs with
        | error _ => simp [hk] at hrun
        | ok p =>
          simp only [hk, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨⟨rfl, _, _⟩, _⟩ := hrun
          simp
      | some ent =>
        simp only [hs] at hrun
        by_cases hcont : continuesTele x.c true ent = true
        · simp only [hcont, ↓reduceIte] at hrun
          unfold continuesTele at hcont
          cases hue : Ix.Kernel.Reader.unshare x.c ent with
          | lam ty b =>
            have hui : Ix.Kernel.Reader.unshare x.c (.share i) = .lam ty b :=
              (unshare_share_iff_lam hs).mpr hue
            have hiterEq : iterStep (caseLamStep x.c) m (0, .share i) =
                iterStep (caseLamStep x.c) m (0, ent) := by
              cases m with
              | zero =>
                simp only [iterStep] at hnonlam
                exact False.elim (hnonlam ty b hui)
              | succ m' =>
                dsimp only [iterStep, caseLamStep]
                rw [hui, hue]
                simp only [view, Ex_pure]
            rw [hiterEq] at hnonlam ⊢
            obtain ⟨_, cs₁, hr2, _⟩ := enterShare_ok hrun
            exact ih (m := m) hnonlam hr2
          | _ => rw [hue] at hcont; simp at hcont
        · simp only [hcont, Bool.false_eq_true, ↓reduceIte, RM_run_bind] at hrun
          have hnotlam : ∀ ty b, Ix.Kernel.Reader.unshare x.c (.share i) ≠ .lam ty b := by
            intro ty b hui
            have hue := (unshare_share_iff_lam hs).mp hui
            apply hcont
            simp [continuesTele, hue]
          rw [caseLam_zero_of_nonLam hnotlam m]
          cases hk : (k acc.reverse (.share i)).run cs with
          | error _ => simp [hk] at hrun
          | ok p =>
            simp only [hk, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hrun
            obtain ⟨⟨rfl, _, _⟩, _⟩ := hrun
            simp
    | all _ _ =>
      rw [caseLam_zero_of_nonLam (by intro _ _ h; simp [Ix.Kernel.Reader.unshare, Ix.Kernel.Reader.unshare.go] at h) m]
      simp only [view, RM_run_bind, RM_run_lift, Ex_pure, Ex_map_ok, ↓reduceIte] at hrun
      rename_i a1 a2
      cases hk : (k acc.reverse (.all a1 a2)).run cs with
      | error _ => simp [hk] at hrun
      | ok p =>
        simp only [hk, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨⟨rfl, _, _⟩, _⟩ := hrun
        simp
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | letE _ _ _ _ _ =>
      rw [caseLam_zero_of_nonLam (by intro _ _ h; simp [Ix.Kernel.Reader.unshare, Ix.Kernel.Reader.unshare.go] at h) m]
      rw [RM_run_bind] at hrun
      simp only [view, RM_run_lift, Ex_pure, Ex_map_ok] at hrun
      obtain ⟨v0, cs1, _, hrun⟩ := RM_bind_elim hrun
      simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨⟨rfl, _, _⟩, _⟩ := hrun
      simp

/-- If `ixSpineU c n body = .ok (h, args)` and `headRefOf s owner c h = some hr`, then
`unshare c body` is NOT a `.lam`. -/
theorem ixSpineU_headRef_nonLam {s : Subject} {owner : Address} {c : Ixon.Constant}
    {n : Nat} {body h : Ixon.Expr} {args : Array Ixon.Expr} {hr : Ref}
    (hsp : ixSpineU c n body = .ok (h, args))
    (hhr : headRefOf s owner c h = some hr) :
    ∀ ty b, Ix.Kernel.Reader.unshare c body ≠ .lam ty b := by
  intro ty b hlam
  cases n with
  | zero => simp [ixSpineU] at hsp
  | succ n =>
    simp only [ixSpineU, hlam, Ex_pure, Except.ok.injEq, Prod.mk.injEq] at hsp
    obtain ⟨rfl, _⟩ := hsp
    have hu : Ix.Kernel.Reader.unshare c (.lam ty b) = .lam ty b :=
      unshare_go_nonShare (fun _ h => by cases h) _
    simp [headRefOf, hu, view] at hhr

/-- In `caseShape`, the recognized `info.arity` equals the exact number of leading λs read by
`readLamNodes`. -/
theorem caseShape_arity_eq_lams_length {s : Subject} {rt : Array (Ref × RunDef)} {depth : Nat}
    {r : Ref} {info : CaseInfo} {c : Ixon.Constant} {d : Ixon.Definition} {x : RCx}
    {β : Type} {cont : List TeleBinder → Ixon.Expr → RM β}
    {fuel : Nat} {valKey : BlockKey} {lams : List TeleBinder} {body : Ixon.Expr} {v : β} {cs : Cursor}
    (hcs : caseShape s rt depth r = some info)
    (hdef : definitionAt? s r = some (c, d))
    (hxc : x.c = c)
    (hread : (inBlock x.rm valKey (readLamNodes x fuel d.value cont)).run {} = .ok ((lams, body, v), cs)) :
    lams.length = info.arity := by
  cases depth with
  | zero => simp [caseShape] at hcs
  | succ depth =>
    unfold caseShape at hcs
    simp only [hdef, Opt_bind_some] at hcs
    cases hrb : (!runBound rt r) with
    | false =>
      simp [hrb] at hcs
    | true =>
      simp only [hrb] at hcs
      cases hkd : (d.kind == .defn && d.safety == .safe) with
      | false =>
        simp [hkd] at hcs
      | true =>
        simp only [hkd, Opt_guard_True, Opt_bind_some] at hcs
        have hfun :
            (fun (_ : Nat) (__s : Nat × Ixon.Expr) =>
              (match view (Ix.Kernel.Reader.unshare c __s.snd) with
               | .ok (.lam _ b) => pure (ForInStep.yield (__s.fst + 1, b))
               | _ => pure (ForInStep.done (__s.fst, __s.snd)) : Option (ForInStep (Nat × Ixon.Expr)))) =
            (fun _ kb => pure (caseLamStep c kb)) := by
          funext _ ⟨k, bd⟩
          dsimp only [caseLamStep]
          cases view (Ix.Kernel.Reader.unshare c bd) with
          | error _ => rfl
          | ok vv => cases vv <;> rfl
        have hloop : forIn (m := Option) [:4096] (0, d.value) (fun _ __s =>
            match view (Ix.Kernel.Reader.unshare c __s.snd) with
            | .ok (.lam _ b) => pure (ForInStep.yield (__s.fst + 1, b))
            | _ => pure (ForInStep.done (__s.fst, __s.snd))) =
            some (iterStep (caseLamStep c) 4096 (0, d.value)) := by
          rw [hfun, forIn_range_opt]
        erw [hloop] at hcs
        simp only [Opt_bind_some] at hcs
        generalize hkb : iterStep (caseLamStep c) 4096 (0, d.value) = kb at hcs
        obtain ⟨⟨h, args⟩, hspOpt, hcs⟩ := Opt_bind_elim hcs
        have hsp : ixSpineU c 4096 kb.2 = .ok (h, args) := by
          cases hsp' : ixSpineU c 4096 kb.2 with
          | error _ => simp [hsp', Except.toOption] at hspOpt
          | ok ha => simp [hsp', Except.toOption] at hspOpt; rw [hspOpt]
        obtain ⟨hr, hhr, hcs⟩ := Opt_bind_elim hcs
        have hnonlam : ∀ ty b, Ix.Kernel.Reader.unshare c kb.2 ≠ .lam ty b :=
          ixSpineU_headRef_nonLam hsp hhr
        have harity : info.arity = kb.1 := by
          cases hrec : recursorAt? s hr with
          | some rcr =>
            obtain ⟨rc, rr⟩ := rcr
            simp only [hrec] at hcs
            obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
            obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
            obtain ⟨mj, _, hcs⟩ := Opt_bind_elim hcs
            obtain ⟨dr, _, hcs⟩ := Opt_bind_elim hcs
            cases hvw : view (Ix.Kernel.Reader.unshare rc dr.2) with
            | error _ => simp [hvw] at hcs
            | ok vv =>
              cases vv with
              | all ty _ =>
                simp only [hvw] at hcs
                obtain ⟨ind, _, hcs⟩ := Opt_bind_elim hcs
                obtain ⟨alts, _, hcs⟩ := Opt_bind_elim hcs
                simp only [Opt_pure, Option.some.injEq] at hcs
                rw [← hcs]
              | _ => simp [hvw] at hcs
          | none =>
            simp only [hrec] at hcs
            obtain ⟨ch, _, hcs⟩ := Opt_bind_elim hcs
            obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
            obtain ⟨mj, _, hcs⟩ := Opt_bind_elim hcs
            obtain ⟨alts, _, hcs⟩ := Opt_bind_elim hcs
            simp only [Opt_pure, Option.some.injEq] at hcs
            rw [← hcs]
        obtain ⟨cs₁, hrt', _⟩ := inBlock_nodes_preserved hread
        unfold readLamNodes at hrt'
        rw [harity]
        subst hxc
        have hlen := readTele_lam_length_eq_caseLam (m := 4096) (by rw [hkb]; exact hnonlam) hrt'
        rw [hkb] at hlen
        simpa using hlen

/-! ## 3. Default-Mode Preservation (`BlocksDefault` and `recordDefault`) -/

/-- Every binder node in every block of `rm` has the default mode. -/
def BlocksDefault (rm : RecordModes) : Prop :=
  ∀ kv ∈ rm.blocks.toList, ∀ n ∈ kv.2.toList, ∀ m, n = .binder m → m.isDefault = true

theorem BlocksDefault.block? {rm : RecordModes} (h : BlocksDefault rm) (key : BlockKey) :
    ∀ n ∈ ((rm.block? key).getD #[]).toList, ∀ m, n = .binder m → m.isDefault = true := by
  unfold RecordModes.block?
  cases hf : rm.blocks.find? (·.1 == key) with
  | none => simp
  | some kv =>
    simp only [Option.map_some, Option.getD_some]
    exact h kv (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hf))

theorem cursor_allDefault_nextBinder {cs cs' : Cursor} {m : AllMode}
    (hcs : ∀ n ∈ cs.nodes.toList, ∀ m', n = .binder m' → m'.isDefault = true)
    (h : nextBinder.run cs = .ok (m, cs')) :
    m.isDefault = true ∧ cs'.nodes = cs.nodes := by
  unfold nextBinder nextNode at h
  simp only [RM_run_bind, RM_run_get] at h
  cases hget : cs.nodes[cs.pos]? with
  | none => simp [hget] at h
  | some nd =>
    simp only [hget, RM_run_bind, RM_run_set, RM_run_pure] at h
    cases nd with
    | share _ => simp at h
    | binder m' =>
      simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hcs (.binder m') (array_mem_toList_of_getElem?' hget) m' rfl, rfl⟩

theorem cursor_allDefault_skip {rm : RecordModes} :
    ∀ n e {cs cs' : Cursor},
      (skip rm n e).run cs = .ok ((), cs') → cs'.nodes = cs.nodes := by
  intro n
  induction n with
  | zero => intro _ _ _ h; simp [skip] at h
  | succ n ih =>
    intro e cs cs' h
    unfold skip at h
    cases hv : view e with
    | error _ => simp [hv] at h
    | ok v =>
      simp only [hv, RM_run_bind, RM_run_lift, Ex_map_ok] at h
      cases v with
      | lam ty b | all ty b =>
        simp only [RM_run_bind] at h
        cases h1 : nextBinder.run cs with
        | error _ => simp [h1] at h
        | ok p1 =>
          simp only [h1] at h
          cases h2 : (skip rm n ty).run p1.2 with
          | error _ => simp [h2] at h
          | ok p2 =>
            simp only [h2] at h
            exact (ih b h).trans ((ih ty h2).trans (nextBinder_nodes h1))
      | app f a =>
        simp only [RM_run_bind] at h
        cases h1 : (skip rm n f).run cs with
        | error _ => simp [h1] at h
        | ok p1 =>
          simp only [h1] at h
          exact (ih a h).trans (ih f h1)
      | letE _ t v b =>
        simp only [RM_run_bind] at h
        cases h1 : (skip rm n t).run cs with
        | error _ => simp [h1] at h
        | ok p1 =>
          simp only [h1] at h
          cases h2 : (skip rm n v).run p1.2 with
          | error _ => simp [h2] at h
          | ok p2 =>
            simp only [h2] at h
            exact (ih b h).trans ((ih v h2).trans (ih t h1))
      | prj _ _ v => exact ih v h
      | share i =>
        dsimp only at h
        split at h
        · simp only [RM_run_bind] at h
          cases h1 : nextShare.run cs with
          | error _ => simp [h1] at h
          | ok p1 =>
            simp only [h1] at h
            split at h
            · simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2, nextShare_nodes h1]
            · simp only [RM_run_throw] at h; cases h
        · simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
      | _ =>
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]

theorem readSkel_isDefault_of_blocksDefault {x : RCx} (hbd : BlocksDefault x.rm) :
    ∀ n e {cs cs' : Cursor} {sk : Skel},
      (∀ nd ∈ cs.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
      (readSkel x n e).run cs = .ok (sk, cs') →
      sk.isDefault = true ∧ cs'.nodes = cs.nodes := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; simp [readSkel] at h
  | succ n ih =>
    intro e cs cs' sk hcs h
    unfold readSkel at h
    cases hv : view e with
    | error _ => simp [hv] at h
    | ok v =>
      simp only [hv, RM_run_bind, RM_run_lift, Ex_map_ok] at h
      cases v with
      | all ty b =>
        simp only [RM_run_bind] at h
        cases h1 : nextBinder.run cs with
        | error _ => simp [h1] at h
        | ok p1 =>
          simp only [h1] at h
          obtain ⟨hm, hn1⟩ := cursor_allDefault_nextBinder hcs h1
          have hcs1 : ∀ nd ∈ p1.2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
            rw [hn1]; exact hcs
          cases h2 : (readSkel x n ty).run p1.2 with
          | error _ => simp [h2] at h
          | ok p2 =>
            simp only [h2] at h
            obtain ⟨hd, hn2⟩ := ih ty hcs1 h2
            have hcs2 : ∀ nd ∈ p2.2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
              rw [hn2]; exact hcs1
            cases h3 : (readSkel x n b).run p2.2 with
            | error _ => simp [h3] at h
            | ok p3 =>
              simp only [h3, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hc, hn3⟩ := ih b hcs2 h3
              obtain ⟨rfl, rfl⟩ := h
              have hmEq : p1.1 = {} := by simpa [AllMode.isDefault] using hm
              refine ⟨?_, hn3.trans (hn2.trans hn1)⟩
              simp [Skel.isDefault, hmEq, hd, hc]
      | sort | nat _ | str _ | var _ =>
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
      | ref _ | recur _ =>
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases x.isInd e <;> exact ⟨rfl, rfl⟩
      | app _ _ =>
        simp only [RM_run_bind] at h
        cases hsp : ixSpine n e with
        | error _ => simp [hsp] at h
        | ok ha =>
          simp only [hsp, RM_run_lift, Ex_map_ok] at h
          cases hind : x.isInd ha.1 with
          | true =>
            simp only [hind, ↓reduceIte] at h
            have hfor : ∀ (l : List Ixon.Expr) (s0 : Skel) (c0 c1 : Cursor) (s1 : Skel),
                s0.isDefault = true →
                (∀ nd ∈ c0.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
                (forIn (m := RM) l s0 fun a s => do
                  pure (ForInStep.yield (.dataApp s (← readSkel x n a)))).run c0 = .ok (s1, c1) →
                s1.isDefault = true ∧ c1.nodes = c0.nodes := by
              intro l
              induction l with
              | nil =>
                intro s0 c0 c1 s1 hs0 _ hf
                simp only [List.forIn_nil, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hf
                obtain ⟨rfl, rfl⟩ := hf
                exact ⟨hs0, rfl⟩
              | cons a rest ihr =>
                intro s0 c0 c1 s1 hs0 hc0 hf
                rw [List.forIn_cons] at hf
                simp only [RM_run_bind] at hf
                cases hra : (readSkel x n a).run c0 with
                | error _ => simp [hra] at hf
                | ok pa =>
                  simp only [hra, RM_run_pure] at hf
                  obtain ⟨haDef, hna⟩ := ih a hc0 hra
                  have hc1 : ∀ nd ∈ pa.2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
                    rw [hna]; exact hc0
                  obtain ⟨hs1, hnc⟩ := ihr (.dataApp s0 pa.1) pa.2 c1 s1
                    (by simp [Skel.isDefault, hs0, haDef]) hc1 hf
                  exact ⟨hs1, hnc.trans hna⟩
            rw [← Array.forIn_toList] at h
            obtain ⟨s1, cs1, hfl, h⟩ := RM_bind_elim h
            simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hfor ha.2.toList .data cs cs1 s1 rfl hcs hfl
          | false =>
            simp only [hind, Bool.false_eq_true, ↓reduceIte, RM_run_bind] at h
            cases hsk : (skip x.rm n e).run cs with
            | error _ => simp [hsk] at h
            | ok psk =>
              simp only [hsk, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨rfl, cursor_allDefault_skip n e hsk⟩
      | share i =>
        cases hsh : x.c.sharing[i]? with
        | none => simp [hsh] at h
        | some ent =>
          simp only [hsh] at h
          obtain ⟨key, cs₁, hinner, hnodes⟩ := enterShare_ok h
          have hdef := (ih ent (hbd.block? key) hinner).1
          exact ⟨hdef, hnodes⟩
      | prj _ _ _ | lam _ _ | letE _ _ _ _ =>
        simp only [RM_run_bind] at h
        cases hsk : (skip x.rm n e).run cs with
        | error _ => simp [hsk] at h
        | ok psk =>
          simp only [hsk, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, cursor_allDefault_skip n e hsk⟩

theorem readTele_isDefault_of_blocksDefault {β : Type} {x : RCx} (hbd : BlocksDefault x.rm)
    {lam : Bool} {k : List TeleBinder → Ixon.Expr → RM β} :
    ∀ {n : Nat} {acc : List TeleBinder} {e : Ixon.Expr} {cs cs' : Cursor} {lams : List TeleBinder}
      {body : Ixon.Expr} {v : β},
      (∀ tb ∈ acc, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) →
      (∀ nd ∈ cs.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
      (readTele x lam (fun ls bd => do pure (ls, bd, ← k ls bd)) n acc e).run cs =
        .ok ((lams, body, v), cs') →
      (∀ tb ∈ lams, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ h; simp [readTele] at h
  | succ n ih =>
    intro acc e cs cs' lams body v hacc hcs h
    unfold readTele at h
    cases hv : view e with
    | error _ => simp [hv] at h
    | ok vv =>
      simp only [hv, RM_run_bind, RM_run_lift, Ex_map_ok] at h
      have hstop : ∀ {e0},
          (do pure (acc.reverse, e0, ← k acc.reverse e0)).run cs = .ok ((lams, body, v), cs') →
          ∀ tb ∈ lams, tb.1.isDefault = true ∧ tb.2.1.isDefault = true := by
        intro e0 hs
        simp only [RM_run_bind] at hs
        cases hk : (k acc.reverse e0).run cs with
        | error _ => simp [hk] at hs
        | ok pk =>
          simp only [hk, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hs
          obtain ⟨⟨rfl, _, _⟩, _⟩ := hs
          intro tb htb
          exact hacc tb (List.mem_reverse.mp htb)
      cases vv with
      | all ty b =>
        cases lam with
        | true => simp only [↓reduceIte] at h; exact hstop h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, RM_run_bind] at h
          cases h1 : nextBinder.run cs with
          | error _ => simp [h1] at h
          | ok p1 =>
            simp only [h1] at h
            obtain ⟨hm, hn1⟩ := cursor_allDefault_nextBinder hcs h1
            have hcs1 : ∀ nd ∈ p1.2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
              rw [hn1]; exact hcs
            cases h2 : (readSkel x n ty).run p1.2 with
            | error _ => simp [h2] at h
            | ok p2 =>
              simp only [h2] at h
              obtain ⟨hd, hn2⟩ := readSkel_isDefault_of_blocksDefault hbd n ty hcs1 h2
              have hcs2 : ∀ nd ∈ p2.2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
                rw [hn2]; exact hcs1
              exact ih (fun tb htb => by
                rcases List.mem_cons.mp htb with rfl | htb'
                · exact ⟨hm, hd⟩
                · exact hacc tb htb') hcs2 h
      | lam ty b =>
        cases lam with
        | true =>
          simp only [↓reduceIte, RM_run_bind] at h
          cases h1 : nextBinder.run cs with
          | error _ => simp [h1] at h
          | ok p1 =>
            simp only [h1] at h
            obtain ⟨hm, hn1⟩ := cursor_allDefault_nextBinder hcs h1
            have hcs1 : ∀ nd ∈ p1.2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
              rw [hn1]; exact hcs
            cases h2 : (readSkel x n ty).run p1.2 with
            | error _ => simp [h2] at h
            | ok p2 =>
              simp only [h2] at h
              obtain ⟨hd, hn2⟩ := readSkel_isDefault_of_blocksDefault hbd n ty hcs1 h2
              have hcs2 : ∀ nd ∈ p2.2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
                rw [hn2]; exact hcs1
              exact ih (fun tb htb => by
                rcases List.mem_cons.mp htb with rfl | htb'
                · exact ⟨hm, hd⟩
                · exact hacc tb htb') hcs2 h
        | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact hstop h
      | share i =>
        cases hsh : x.c.sharing[i]? with
        | none => simp only [hsh] at h; exact hstop h
        | some ent =>
          simp only [hsh] at h
          cases hc : continuesTele x.c lam ent with
          | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact hstop h
          | true =>
            simp only [hc, ↓reduceIte] at h
            obtain ⟨key, cs₁, hinner, _⟩ := enterShare_ok h
            exact ih hacc (hbd.block? key) hinner
      | _ => exact hstop h

theorem recordDefault_ok_true {c : Ixon.Constant} (h : recordDefault c = .ok true) :
    ∃ rm, recordModes c = .ok rm ∧ BlocksDefault rm ∧ fieldModesDefault c = true ∧
      (∀ root ∈ (binderRoots c.info ++ c.sharing).toList, letsDefault readFuel root = .ok true) := by
  unfold recordDefault at h
  cases hrm : recordModes c with
  | error e => simp [hrm, bind, Except.bind] at h
  | ok rm =>
    simp only [hrm, bind, Except.bind] at h
    let ok0 : Bool := rm.blocks.all fun (_, ns) => ns.all fun
      | .binder m => m.isDefault
      | .share _ => true
    have hfor : ∀ (l : List Ixon.Expr) (b0 b1 : Bool),
        (forIn (m := Except String) l b0 fun root ok => do
          pure (ForInStep.yield (ok && (← letsDefault readFuel root)))) = .ok b1 →
        (b1 = true → b0 = true ∧ ∀ root ∈ l, letsDefault readFuel root = .ok true) := by
      intro l
      induction l with
      | nil =>
        intro b0 b1 hf hb1
        simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hf
        subst hf; exact ⟨hb1, by simp⟩
      | cons a rest ih =>
        intro b0 b1 hf hb1
        rw [List.forIn_cons] at hf
        simp only [bind, Except.bind] at hf
        cases hla : letsDefault readFuel a with
        | error _ => simp [hla] at hf
        | ok ba =>
          simp only [hla, pure, Except.pure] at hf
          obtain ⟨hba, hrest⟩ := ih (b0 && ba) b1 hf hb1
          simp only [Bool.and_eq_true] at hba
          refine ⟨hba.1, fun root hr => ?_⟩
          rcases List.mem_cons.mp hr with rfl | hr'
          · rw [hla, hba.2]
          · exact hrest root hr'
    rw [← Array.forIn_toList] at h
    obtain ⟨ok1, hfl, h⟩ := Ex_bind_elim h
    simp only [Ex_pure, Except.ok.injEq, Bool.and_eq_true] at h
    obtain ⟨⟨hok1, hfm⟩, _⟩ := h
    obtain ⟨hok0, hlets⟩ := hfor _ ok0 ok1 hfl hok1
    have hbd : BlocksDefault rm := by
      intro kv hkv nd hnd m hmeq
      have hall1 := Array.all_eq_true.mp hok0
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hkv
      have hidx' : idx < rm.blocks.size := by simpa using hidx
      have hall2 := hall1 idx hidx'
      have hall3 := Array.all_eq_true.mp hall2
      obtain ⟨j, hj, hndEq⟩ := List.mem_iff_getElem.mp hnd
      have hj' : j < rm.blocks[idx].2.size := by simpa using hj
      have hres := hall3 j hj'
      have hndEq' : rm.blocks[idx].2[j] = nd := hndEq
      change (match rm.blocks[idx].2[j] with
        | ModeNode.binder m => m.isDefault
        | ModeNode.share _ => true) = true at hres
      rw [hndEq', hmeq] at hres
      exact hres
    exact ⟨rm, rfl, hbd, hfm, hlets⟩

theorem ifaceErased_nil_of_recordDefault {s : Subject} {r : Ref} {c : Ixon.Constant} {es : List Nat}
    (hst : s.store r.block = some c) (hd : recordDefault c = .ok true)
    (he : ifaceErased s r = .ok es) : es = [] := by
  obtain ⟨rm, hrm, hbd, _, _⟩ := recordDefault_ok_true hd
  unfold ifaceErased at he
  simp only [hst, bind, Except.bind] at he
  cases htr : typeRootOf c r with
  | none => simp [htr, throw, throwThe, MonadExceptOf.throw] at he
  | some tr =>
    simp only [htr] at he
    cases hrcx : (Reading.bare s).rcx noClasses r with
    | error _ => simp [hrcx] at he
    | ok x =>
      simp only [hrcx] at he
      have hxrm : x.rm = rm := by
        unfold Reading.rcx Reading.bare at hrcx
        simp only [hst, hrm, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hrcx
        rw [← hrcx]
      cases hrf : (inBlock x.rm (rootKey tr.1) (readForalls x readFuel tr.2 (readSkel x readFuel))).run {} with
      | error _ => simp [hrf] at he
      | ok res =>
        simp only [hrf, pure, Except.pure, Except.ok.injEq] at he
        obtain ⟨cs₁, hinner, _⟩ := inBlock_nodes_preserved hrf
        rw [hxrm] at hinner
        have hbdx : BlocksDefault x.rm := by rw [hxrm]; exact hbd
        have hall := readTele_isDefault_of_blocksDefault hbdx (by simp) (hbd.block? (rootKey tr.1)) hinner
        rw [← he]
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro i hi
        rw [List.mem_filterMap] at hi
        obtain ⟨⟨⟨m, sk, dom⟩, idx⟩, hmem, hif⟩ := hi
        have hmdef := (hall (m, sk, dom) (list_mem_of_mem_zipIdx' hmem)).1
        have hmEq : m = {} := by simpa [AllMode.isDefault] using hmdef
        simp [hmEq] at hif

/-! ## 4. `refsOf`, `readProg` Lookup, and `CtorsIndexed` -/

theorem refsOf_block (a : Address) (c : Ixon.Constant) :
    ∀ r ∈ (refsOf a c).toList, r.block = a := by
  unfold refsOf
  cases c.info with
  | defn _ | recr _ | axio _ | quot _ =>
    intro r hr; simp at hr; subst hr; rfl
  | muts ms =>
    -- Prove invariant over `for (m, i) in ms.zipIdx`
    have hstep : ∀ (l : List (Ixon.MutConst × Nat)) (acc : Array Ref),
        (∀ r ∈ acc.toList, r.block = a) →
        ∀ r ∈ ((forIn (m := Id) l acc fun (m, i) out =>
          have out := out.push (.member a i)
          match m with
          | .indc ind => do
            let __s ← forIn [0:ind.ctors.size] out fun ci out => pure (ForInStep.yield (out.push (.ctor a i ci)))
            pure (ForInStep.yield __s)
          | _ => pure (ForInStep.yield out)).run).toList, r.block = a := by
      intro l
      induction l with
      | nil => intro acc hacc r hr; exact hacc r hr
      | cons mi rest ih =>
        obtain ⟨m, i⟩ := mi
        intro acc hacc
        rw [List.forIn_cons]
        have hacc1 : ∀ r ∈ (acc.push (.member a i)).toList, r.block = a := by
          intro r hr
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact hacc r hr
          · rfl
        cases m with
        | indc ind =>
          have hinner : ∀ (n s : Nat) (arr : Array Ref), (∀ r ∈ arr.toList, r.block = a) →
              ∀ r ∈ ((forIn (m := Id) (List.range' s n 1) arr fun ci out =>
                pure (ForInStep.yield (out.push (.ctor a i ci)))).run).toList, r.block = a := by
            intro n
            induction n with
            | zero => intro _ arr harr r hr; exact harr r hr
            | succ n ihn =>
              intro s arr harr
              rw [List.range'_succ, List.forIn_cons]
              apply ihn (s + 1) (arr.push (.ctor a i s))
              intro r hr
              simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
              rcases hr with hr | rfl
              · exact harr r hr
              · rfl
          apply ih _
          rw [Std.Legacy.Range.forIn_eq_forIn_range']
          exact hinner _ _ _ hacc1
        | defn _ | recr _ => exact ih _ hacc1
    intro r hr
    dsimp only at hr
    rw [← Array.forIn_toList] at hr
    exact hstep _ #[] (by simp) r hr
  | _ => intro r hr; simp at hr

theorem refsOf_nodup (a : Address) (c : Ixon.Constant) : (refsOf a c).toList.Nodup := by
  unfold refsOf
  cases c.info with
  | defn _ | recr _ | axio _ | quot _ => exact nodup_singleton _
  | muts ms =>
    have hinner : ∀ (i n s : Nat) (arr : Array Ref),
        arr.toList.Nodup →
        (∀ r ∈ arr.toList, ∀ ci ≥ s, r ≠ .ctor a i ci) →
        let out := (forIn (m := Id) (List.range' s n 1) arr fun ci out =>
          pure (ForInStep.yield (out.push (.ctor a i ci)))).run
        out.toList.Nodup ∧
        (∀ r ∈ out.toList, r ∈ arr.toList ∨ ∃ ci, s ≤ ci ∧ ci < s + n ∧ r = .ctor a i ci) := by
      intro i n
      induction n with
      | zero =>
        intro s arr hnd _
        exact ⟨hnd, fun r hr => Or.inl hr⟩
      | succ n ihn =>
        intro s arr hnd hdisj
        rw [List.range'_succ, List.forIn_cons]
        have hnot : ConstRef.ctor a i s ∉ arr.toList := fun hm => hdisj _ hm s (Nat.le_refl _) rfl
        have hnd1 : (arr.push (.ctor a i s)).toList.Nodup := by
          rw [Array.toList_push]
          exact List.nodup_append.mpr ⟨hnd, nodup_singleton _, fun x hx y hy hxy => by
            simp only [List.mem_singleton] at hy; subst hy; subst hxy; exact hnot hx⟩
        have hdisj1 : ∀ r ∈ (arr.push (.ctor a i s)).toList, ∀ ci ≥ s + 1, r ≠ .ctor a i ci := by
          intro r hr ci hci hEq
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact hdisj r hr ci (by omega) hEq
          · cases hEq; omega
        obtain ⟨hnd2, hmem2⟩ := ihn (s + 1) (arr.push (.ctor a i s)) hnd1 hdisj1
        refine ⟨hnd2, fun r hr => ?_⟩
        rcases hmem2 r hr with hr1 | ⟨ci, hlo, hhi, rfl⟩
        · rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr1
          rcases hr1 with hr0 | rfl
          · exact Or.inl hr0
          · exact Or.inr ⟨s, Nat.le_refl _, by omega, rfl⟩
        · exact Or.inr ⟨ci, by omega, by omega, rfl⟩
    have houter : ∀ (l : List Ixon.MutConst) (k : Nat) (arr : Array Ref),
        arr.toList.Nodup →
        (∀ r ∈ arr.toList, (∀ j ≥ k, r ≠ .member a j) ∧ (∀ j ≥ k, ∀ ci, r ≠ .ctor a j ci)) →
        let out := (forIn (m := Id) (l.zipIdx k) arr fun (m, i) out =>
          have out := out.push (.member a i)
          match m with
          | .indc ind => do
            let __s ← forIn [0:ind.ctors.size] out fun ci out => pure (ForInStep.yield (out.push (.ctor a i ci)))
            pure (ForInStep.yield __s)
          | _ => pure (ForInStep.yield out)).run
        out.toList.Nodup := by
      intro l
      induction l with
      | nil => intro _ _ hnd _; exact hnd
      | cons m rest ih =>
        intro k arr hnd hdisj
        rw [List.zipIdx_cons, List.forIn_cons]
        have hnotm : ConstRef.member a k ∉ arr.toList := fun hm => (hdisj _ hm).1 k (Nat.le_refl _) rfl
        have hnd1 : (arr.push (.member a k)).toList.Nodup := by
          rw [Array.toList_push]
          exact List.nodup_append.mpr ⟨hnd, nodup_singleton _, fun x hx y hy hxy => by
            simp only [List.mem_singleton] at hy; subst hy; subst hxy; exact hnotm hx⟩
        have hdisj1 : ∀ r ∈ (arr.push (.member a k)).toList,
            (∀ j ≥ k + 1, r ≠ .member a j) ∧ (∀ j ≥ k + 1, ∀ ci, r ≠ .ctor a j ci) := by
          intro r hr
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr
          rcases hr with hr | rfl
          · exact ⟨fun j hj => (hdisj r hr).1 j (by omega), fun j hj => (hdisj r hr).2 j (by omega)⟩
          · exact ⟨fun j hj hEq => by cases hEq; omega, fun _ _ _ hEq => by cases hEq⟩
        cases m with
        | indc ind =>
          have hdisjC : ∀ r ∈ (arr.push (.member a k)).toList, ∀ ci ≥ 0, r ≠ .ctor a k ci := by
            intro r hr ci _
            rw [Array.toList_push, List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact (hdisj r hr).2 k (Nat.le_refl _) ci
            · intro hEq; cases hEq
          have hrange := hinner k ind.ctors.size 0 (arr.push (.member a k)) hnd1 hdisjC
          dsimp only
          rw [Std.Legacy.Range.forIn_eq_forIn_range']
          have hsz : ([0:ind.ctors.size] : Std.Legacy.Range).size = ind.ctors.size := by simp [Std.Legacy.Range.size]
          have hst : ([0:ind.ctors.size] : Std.Legacy.Range).start = 0 := rfl
          have hsp : ([0:ind.ctors.size] : Std.Legacy.Range).step = 1 := rfl
          rw [hsz, hst, hsp]
          apply ih (k + 1) _ hrange.1
          intro r hr
          rcases hrange.2 r hr with hr1 | ⟨ci, _, _, rfl⟩
          · exact hdisj1 r hr1
          · exact ⟨(fun _ _ hEq => by cases hEq), (fun j hj _ hEq => by cases hEq; omega)⟩
        | defn _ | recr _ => exact ih (k + 1) _ hnd1 hdisj1
    dsimp only
    rw [← Array.forIn_toList]
    have hzip : ms.zipIdx.toList = ms.toList.zipIdx 0 := by simp [Array.toList_zipIdx]
    rw [hzip]
    exact houter ms.toList 0 #[] List.nodup_nil (by simp)
  | _ => exact List.nodup_nil

theorem refsOf_mem_indc {a : Address} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i : Nat} {ind : Ixon.Inductive}
    (hinfo : c.info = .muts ms) (hmi : ms[i]? = some (.indc ind)) :
    ConstRef.member a i ∈ (refsOf a c).toList := by
  unfold refsOf
  rw [hinfo]
  have hmem_push : ∀ (l : List (Ixon.MutConst × Nat)) (acc : Array Ref) (r : Ref),
      (r ∈ acc.toList ∨ ∃ m, (m, i) ∈ l ∧ r = .member a i) →
      r ∈ ((forIn (m := Id) l acc fun (m, j) out =>
        have out := out.push (.member a j)
        match m with
        | .indc ind' => do
          let __s ← forIn [0:ind'.ctors.size] out fun ci out => pure (ForInStep.yield (out.push (.ctor a j ci)))
          pure (ForInStep.yield __s)
        | _ => pure (ForInStep.yield out)).run).toList := by
    have hinner_sub : ∀ (j n s : Nat) (arr : Array Ref) (r : Ref), r ∈ arr.toList →
        r ∈ ((forIn (m := Id) (List.range' s n 1) arr fun ci out =>
          pure (ForInStep.yield (out.push (.ctor a j ci)))).run).toList := by
      intro j n
      induction n with
      | zero => intro _ _ _ hr; exact hr
      | succ n ihn =>
        intro s arr r hr
        rw [List.range'_succ, List.forIn_cons]
        apply ihn (s + 1) (arr.push (.ctor a j s)) r
        simp [Array.toList_push, hr]
    intro l
    induction l with
    | nil =>
      intro acc r hr
      rcases hr with hr | ⟨_, hm, _⟩
      · exact hr
      · cases hm
    | cons mj rest ih =>
      obtain ⟨m, j⟩ := mj
      intro acc r hr
      rw [List.forIn_cons]
      have hsub1 : ∀ x ∈ acc.toList, x ∈ (acc.push (.member a j)).toList := fun x hx => by
        simp [Array.toList_push, hx]
      have hnext : r ∈ (acc.push (.member a j)).toList ∨ ∃ m', (m', i) ∈ rest ∧ r = .member a i := by
        rcases hr with hr | ⟨m', hm', rfl⟩
        · exact Or.inl (hsub1 r hr)
        · rcases List.mem_cons.mp hm' with hEq | hrest
          · injection hEq with _ hj; subst hj
            exact Or.inl (by simp [Array.toList_push])
          · exact Or.inr ⟨m', hrest, rfl⟩
      cases m with
      | indc ind' =>
        apply ih _ r
        rcases hnext with h1 | h2
        · left
          rw [Std.Legacy.Range.forIn_eq_forIn_range']
          exact hinner_sub j _ _ _ r h1
        · exact Or.inr h2
      | defn _ | recr _ => exact ih _ r hnext
  dsimp only
  rw [← Array.forIn_toList]
  apply hmem_push
  right
  refine ⟨.indc ind, ?_, rfl⟩
  have hget : ms.toList[i]? = some (.indc ind) := by simpa using hmi
  have hz := mem_zipIdx_of_getElem? hget
  simpa [Array.toList_zipIdx] using hz

theorem array_find?_eq_some_iff_of_nodup {α β : Type} [BEq α] [LawfulBEq α]
    {arr : Array (α × β)} (hnd : (arr.toList.map Prod.fst).Nodup) {k : α} {v : β} :
    (arr.find? (·.1 == k)).map Prod.snd = some v ↔ (k, v) ∈ arr.toList := by
  rw [← Array.find?_toList]
  have aux : ∀ (l : List (α × β)), (l.map Prod.fst).Nodup →
      ((l.find? (·.1 == k)).map Prod.snd = some v ↔ (k, v) ∈ l) := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons p rest ih =>
      obtain ⟨a, b⟩ := p
      intro hnod
      simp only [List.map_cons, List.nodup_cons] at hnod
      obtain ⟨hna, hnd'⟩ := hnod
      simp only [List.find?_cons]
      by_cases hak : a = k
      · subst hak
        simp only [beq_self_eq_true, Option.map_some, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
          true_and]
        constructor
        · intro rfl; exact Or.inl rfl
        · intro h
          rcases h with rfl | hrest
          · rfl
          · exact False.elim (hna (List.mem_map.mpr ⟨(a, v), hrest, rfl⟩))
      · have hne : (a == k) = false := beq_false_of_ne hak
        simp only [hne, List.mem_cons, Prod.mk.injEq]
        rw [ih hnd']
        constructor
        · intro hr; exact Or.inr hr
        · rintro (⟨h1, _⟩ | hr)
          · exact False.elim (hak h1.symm)
          · exact hr
  exact aux arr.toList hnd

/-- Every entry pushed into `P.defs` by `readProg` comes from a unique `(a, r)` pair with
`a ∈ rd.closure`, `s.store a = some c`, `r ∈ refsOf a c`, and `rd.readDef cl rt true r = .ok d`. -/
theorem readProg_elim {s : Subject} {cl : Classifier} {P : Prog}
    (hp : readProg s cl = .ok P) :
    let rd := Reading.make s
    rd.complete = .ok () ∧
    ∃ rt, rd.runTable cl = .ok rt ∧
      (P.defs.toList.map Prod.fst).Nodup ∧
      (∀ r d, P.find? r = some d ↔ (r, d) ∈ P.defs.toList) ∧
      (∀ r d, P.find? r = some d →
        ∃ c, r.block ∈ rd.closure.toList ∧ s.store r.block = some c ∧
          r ∈ (refsOf r.block c).toList ∧ rd.readDef cl rt true r = .ok d) ∧
      (∀ a c r, a ∈ rd.closure.toList → s.store a = some c → r ∈ (refsOf a c).toList →
        ∃ d, rd.readDef cl rt true r = .ok d ∧ P.find? r = some d) ∧
      rd.rawRecursors cl P.defs = .ok () ∧
      P.nat = roleRef? s .nat := by
  unfold readProg at hp
  dsimp only at hp ⊢
  generalize hrd : Reading.make s = rd at hp ⊢
  have hndCl : rd.closure.toList.Nodup := by rw [← hrd]; exact closureOf_nodup s.store _ _
  cases hcomp : rd.complete with
  | error _ => simp [hcomp, Ex_bind_err] at hp
  | ok u =>
    cases u
    simp only [hcomp, Ex_bind_ok] at hp
    cases hrt : rd.runTable cl with
    | error _ => simp [hrt, Ex_bind_err] at hp
    | ok rt =>
      simp only [hrt, Ex_bind_ok] at hp
      -- Analyze the nested `forIn` loops building `defs`
      have hinner : ∀ (a : Address) (rs : List Ref) (acc defs' : Array (Ref × RunDef)),
          rs.Nodup →
          (∀ r ∈ rs, r.block = a) →
          (acc.toList.map Prod.fst).Nodup →
          (∀ p ∈ acc.toList, p.1.block ≠ a) →
          (forIn (m := Except String) rs acc fun r defs => do
            pure (ForInStep.yield (defs.push (r, ← rd.readDef cl rt true r)))) = .ok defs' →
          (defs'.toList.map Prod.fst).Nodup ∧
          (∀ p ∈ defs'.toList, p ∈ acc.toList ∨ (p.1 ∈ rs ∧ rd.readDef cl rt true p.1 = .ok p.2)) ∧
          (∀ p ∈ acc.toList, p ∈ defs'.toList) ∧
          (∀ r ∈ rs, ∃ d, rd.readDef cl rt true r = .ok d ∧ (r, d) ∈ defs'.toList) := by
        intro a rs
        induction rs with
        | nil =>
          intro acc defs' _ _ hnd _ hf
          simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hf
          subst hf
          exact ⟨hnd, fun _ h => Or.inl h, fun _ h => h, fun _ h => by cases h⟩
        | cons r rest ih =>
          intro acc defs' hndR hblk hndA hdisj hf
          rw [List.forIn_cons] at hf
          simp only [bind, Except.bind] at hf
          cases hrd : rd.readDef cl rt true r with
          | error _ => simp [hrd] at hf
          | ok d =>
            simp only [hrd, pure, Except.pure] at hf
            obtain ⟨hnr, hndRest⟩ := List.nodup_cons.mp hndR
            have hnotInAcc : r ∉ acc.toList.map Prod.fst := by
              intro hm
              rw [List.mem_map] at hm
              obtain ⟨p, hp', hpeq⟩ := hm
              have hpb := hdisj p hp'
              rw [hpeq, hblk r (List.mem_cons_self ..)] at hpb
              exact hpb rfl
            have hndA1 : ((acc.push (r, d)).toList.map Prod.fst).Nodup := by
              rw [Array.toList_push, List.map_append, List.map_singleton]
              exact List.nodup_append.mpr ⟨hndA, nodup_singleton _, fun x hx y hy hxy => by
                simp only [List.mem_singleton] at hy; subst hy; subst hxy; exact hnotInAcc hx⟩
            have hrest_step : ∀ (rs' : List Ref) (acc1 : Array (Ref × RunDef)),
                rs'.Nodup →
                (acc1.toList.map Prod.fst).Nodup →
                (∀ r' ∈ rs', r' ∉ acc1.toList.map Prod.fst) →
                (forIn (m := Except String) rs' acc1 fun r' defs => do
                  pure (ForInStep.yield (defs.push (r', ← rd.readDef cl rt true r')))) = .ok defs' →
                (defs'.toList.map Prod.fst).Nodup ∧
                (∀ p ∈ defs'.toList, p ∈ acc1.toList ∨ (p.1 ∈ rs' ∧ rd.readDef cl rt true p.1 = .ok p.2)) ∧
                (∀ p ∈ acc1.toList, p ∈ defs'.toList) ∧
                (∀ r' ∈ rs', ∃ d', rd.readDef cl rt true r' = .ok d' ∧ (r', d') ∈ defs'.toList) := by
              intro rs'
              induction rs' with
              | nil =>
                intro acc1 _ hnd1 _ hf1
                simp only [List.forIn_nil, Ex_pure, Except.ok.injEq] at hf1
                subst hf1
                exact ⟨hnd1, fun _ h => Or.inl h, fun _ h => h, fun _ h => by cases h⟩
              | cons r2 rest2 ih2 =>
                intro acc1 hndR2 hnd1 hdisj1 hf1
                rw [List.forIn_cons] at hf1
                obtain ⟨d2, hrd2, hf1⟩ := Ex_bind_elim (by simpa using hf1)
                obtain ⟨hnr2, hndRest2⟩ := List.nodup_cons.mp hndR2
                have hnd2 : ((acc1.push (r2, d2)).toList.map Prod.fst).Nodup := by
                  rw [Array.toList_push, List.map_append, List.map_singleton]
                  exact List.nodup_append.mpr ⟨hnd1, nodup_singleton _, fun x hx y hy hxy => by
                    simp only [List.mem_singleton] at hy
                    have hxr : x = r2 := hxy.trans hy
                    rw [hxr] at hx
                    exact hdisj1 r2 (List.mem_cons_self ..) hx⟩
                have hdisj2 : ∀ r' ∈ rest2, r' ∉ (acc1.push (r2, d2)).toList.map Prod.fst := by
                  intro r' hr' hm
                  rw [Array.toList_push, List.map_append, List.map_singleton, List.mem_append,
                    List.mem_singleton] at hm
                  rcases hm with hm1 | hEq
                  · exact hdisj1 r' (List.mem_cons_of_mem _ hr') hm1
                  · subst hEq; exact hnr2 hr'
                obtain ⟨hndF, hmemF, hsubF, hexF⟩ := ih2 (acc1.push (r2, d2)) hndRest2 hnd2 hdisj2 hf1
                refine ⟨hndF, ?_, ?_, ?_⟩
                · intro p hpF
                  rcases hmemF p hpF with h1 | ⟨hr', hd'⟩
                  · rw [Array.toList_push, List.mem_append, List.mem_singleton] at h1
                    rcases h1 with h0 | rfl
                    · exact Or.inl h0
                    · exact Or.inr ⟨List.mem_cons_self .., hrd2⟩
                  · exact Or.inr ⟨List.mem_cons_of_mem _ hr', hd'⟩
                · intro p hp1
                  exact hsubF p (by simp [Array.toList_push, hp1])
                · intro r' hr'
                  rcases List.mem_cons.mp hr' with rfl | hr2
                  · exact ⟨d2, hrd2, hsubF (r', d2) (by simp [Array.toList_push])⟩
                  · exact hexF r' hr2
            have hdisj1 : ∀ r' ∈ rest, r' ∉ (acc.push (r, d)).toList.map Prod.fst := by
              intro r' hr' hm
              rw [Array.toList_push, List.map_append, List.map_singleton, List.mem_append,
                List.mem_singleton] at hm
              rcases hm with hm0 | rfl
              · rw [List.mem_map] at hm0
                obtain ⟨p, hp0, rfl⟩ := hm0
                exact hdisj p hp0 (hblk p.1 (List.mem_cons_of_mem _ hr'))
              · exact hnr hr'
            obtain ⟨hndF, hmemF, hsubF, hexF⟩ := hrest_step rest (acc.push (r, d)) hndRest hndA1 hdisj1 hf
            refine ⟨hndF, ?_, ?_, ?_⟩
            · intro p hpF
              rcases hmemF p hpF with h1 | ⟨hr', hd'⟩
              · rw [Array.toList_push, List.mem_append, List.mem_singleton] at h1
                rcases h1 with h0 | rfl
                · exact Or.inl h0
                · exact Or.inr ⟨List.mem_cons_self .., hrd⟩
              · exact Or.inr ⟨List.mem_cons_of_mem _ hr', hd'⟩
            · intro p hp0
              exact hsubF p (by simp [Array.toList_push, hp0])
            · intro r' hr'
              rcases List.mem_cons.mp hr' with rfl | hr2
              · exact ⟨d, hrd, hsubF (r', d) (by simp [Array.toList_push])⟩
              · exact hexF r' hr2
      -- Outer loop over `rd.closure.toList`
      have houter : ∀ (addrs : List Address) (acc defs' : Array (Ref × RunDef)),
          addrs.Nodup →
          (acc.toList.map Prod.fst).Nodup →
          (∀ p ∈ acc.toList, p.1.block ∉ addrs) →
          (forIn (m := Except String) addrs acc fun a defs =>
            match s.store a with
            | some c => do
              let __s ← forIn (refsOf a c) defs fun r defs => do
                pure (ForInStep.yield (defs.push (r, ← rd.readDef cl rt true r)))
              pure (ForInStep.yield __s)
            | _ => pure (ForInStep.yield defs)) = .ok defs' →
          (defs'.toList.map Prod.fst).Nodup ∧
          (∀ p ∈ defs'.toList, p ∈ acc.toList ∨
            ∃ c, p.1.block ∈ addrs ∧ s.store p.1.block = some c ∧
              p.1 ∈ (refsOf p.1.block c).toList ∧ rd.readDef cl rt true p.1 = .ok p.2) ∧
          (∀ p ∈ acc.toList, p ∈ defs'.toList) ∧
          (∀ a c r, a ∈ addrs → s.store a = some c → r ∈ (refsOf a c).toList →
            ∃ d, rd.readDef cl rt true r = .ok d ∧ (r, d) ∈ defs'.toList) := by
        intro addrs
        induction addrs with
        | nil =>
          intro acc defs' _ hnd _ hf
          simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hf
          subst hf
          exact ⟨hnd, fun _ h => Or.inl h, fun _ h => h, fun _ _ _ h => by cases h⟩
        | cons a rest ih =>
          intro acc defs' hndA hndD hdisj hf
          rw [List.forIn_cons] at hf
          obtain ⟨hna, hndRest⟩ := List.nodup_cons.mp hndA
          cases hst : s.store a with
          | none =>
            simp only [hst, Ex_pure, Ex_bind_ok] at hf
            obtain ⟨hndF, hmemF, hsubF, hexF⟩ := ih acc defs' hndRest hndD
              (fun p hp hm => hdisj p hp (List.mem_cons_of_mem _ hm)) hf
            refine ⟨hndF, ?_, hsubF, ?_⟩
            · intro p hpF
              rcases hmemF p hpF with h0 | ⟨c, hma, hsc, hr, hrd⟩
              · exact Or.inl h0
              · exact Or.inr ⟨c, List.mem_cons_of_mem _ hma, hsc, hr, hrd⟩
            · intro a' c r ha' hsc hr
              rcases List.mem_cons.mp ha' with rfl | hrest
              · rw [hst] at hsc; cases hsc
              · exact hexF a' c r hrest hsc hr
          | some c =>
            simp only [hst] at hf
            obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
            rw [← Array.forIn_toList] at hstep
            obtain ⟨mid, hmid, hstep⟩ := Ex_bind_elim hstep
            simp only [Ex_pure, Except.ok.injEq] at hstep
            subst hstep
            dsimp only at hf
            obtain ⟨hndM, hmemM, hsubM, hexM⟩ := hinner a (refsOf a c).toList acc mid
              (refsOf_nodup a c) (refsOf_block a c) hndD
              (fun p hp hEq => hdisj p hp (hEq ▸ List.mem_cons_self ..)) hmid
            have hdisjM : ∀ p ∈ mid.toList, p.1.block ∉ rest := by
              intro p hpM hm
              rcases hmemM p hpM with h0 | ⟨hr, _⟩
              · exact hdisj p h0 (List.mem_cons_of_mem _ hm)
              · rw [refsOf_block a c p.1 hr] at hm
                exact hna hm
            obtain ⟨hndF, hmemF, hsubF, hexF⟩ := ih mid defs' hndRest hndM hdisjM hf
            refine ⟨hndF, ?_, fun p hp0 => hsubF p (hsubM p hp0), ?_⟩
            · intro p hpF
              rcases hmemF p hpF with hm | ⟨c', hma, hsc, hr, hrd⟩
              · rcases hmemM p hm with h0 | ⟨hr, hrd⟩
                · exact Or.inl h0
                · have hblk := refsOf_block a c p.1 hr
                  right
                  refine ⟨c, ?_, ?_, ?_, hrd⟩
                  · rw [hblk]; exact List.mem_cons_self ..
                  · rw [hblk]; exact hst
                  · rw [hblk]; exact hr
              · exact Or.inr ⟨c', List.mem_cons_of_mem _ hma, hsc, hr, hrd⟩
            · intro a' c' r ha' hsc' hr'
              rcases List.mem_cons.mp ha' with rfl | hrest
              · rw [hst] at hsc'; cases hsc'
                obtain ⟨d, hrd, hm⟩ := hexM r hr'
                exact ⟨d, hrd, hsubF (r, d) hm⟩
              · exact hexF a' c' r hrest hsc' hr'
      rw [← Array.forIn_toList] at hp
      obtain ⟨defs, hdefs, hp⟩ := Ex_bind_elim hp
      obtain ⟨_, hraw, hp⟩ := Ex_bind_elim hp
      simp only [Ex_pure, Except.ok.injEq] at hp
      subst hp
      obtain ⟨hndDefs, hmemDefs, _, hexDefs⟩ := houter rd.closure.toList #[] defs hndCl
        List.nodup_nil (by simp) hdefs
      refine ⟨rfl, rt, rfl, hndDefs, ?_, ?_, ?_, hraw, rfl⟩
      · intro r d
        exact array_find?_eq_some_iff_of_nodup hndDefs
      · intro r d hfind
        have hmem := (array_find?_eq_some_iff_of_nodup hndDefs).mp hfind
        rcases hmemDefs (r, d) hmem with h0 | hex
        · simp at h0
        · exact hex
      · intro a c r ha hsc hr
        obtain ⟨d, hrd, hmem⟩ := hexDefs a c r ha hsc hr
        exact ⟨d, hrd, (array_find?_eq_some_iff_of_nodup hndDefs).mpr hmem⟩

/-- No primitive role (`natZero`, `natSucc`, `natAdd`, ...) is bound to an inductive type. -/
def RolesDisjointFromInductives (s : Subject) : Prop :=
  ∀ r role, roleOf? s r = some role → (primOf s role).isSome → inductiveAt? s r = none

/-- Every entry in `Reading.runTable` is a `.body` definition of a safe definition (`definitionAt?`),
never an inductive. -/
theorem readEquation_mem_body {rd : Reading} {cl : Classifier} {x : RCx}
    {eqRef andRef : Option Ref} {targets : Array (Ref × RunDef)} :
    ∀ {n : Nat} {ctx : List Local} {e : Ixon.Expr} {cs cs' : Cursor} {entries : Array (Ref × RunDef)},
      (readEquation rd cl x eqRef andRef targets n ctx e).run cs = .ok (entries, cs') →
      ∀ p ∈ entries.toList,
        (∃ params res rc rs rhs, p.2 = .body params res rc rs rhs) ∧
        (∃ fc fd, definitionAt? rd.s p.1 = some (fc, fd)) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; simp [readEquation, throw, throwThe, MonadExceptOf.throw] at h
  | succ n ih =>
    intro ctx e cs cs' entries h
    unfold readEquation at h
    obtain ⟨vv, cs0, hvl, h⟩ := RM_bind_elim h
    cases hv : view e with
    | error _ => simp [hv] at hvl
    | ok vv' =>
      simp only [hv, RM_run_lift, Ex_map_ok, Except.ok.injEq, Prod.mk.injEq] at hvl
      obtain ⟨rfl, rfl⟩ := hvl
      cases vv' with
      | all ty b =>
        obtain ⟨m, cs1, _, h⟩ := RM_bind_elim h
        split at h
        · obtain ⟨k, cs2, _, h⟩ := RM_bind_elim h
          obtain ⟨pc, cs3, _, h⟩ := RM_bind_elim h
          obtain ⟨_, cs4, _, h⟩ := RM_bind_elim h
          exact ih h
        · simp only [RM_run_bind, RM_run_throw] at h; cases h
      | share i =>
        cases hsh : x.c.sharing[i]? with
        | none => simp [hsh, RM_run_throw] at h
        | some ent =>
          simp only [hsh] at h
          obtain ⟨_, cs₁, hinner, _⟩ := enterShare_ok h
          exact ih hinner
      | app fArg lastArg =>
        obtain ⟨ha, cs1, _, h⟩ := RM_bind_elim h
        by_cases hand : (ctx.isEmpty && (headRefOf rd.s x.owner x.c ha.1).isSome &&
            headRefOf rd.s x.owner x.c ha.1 == andRef && ha.2.size == 2) = true
        · simp only [hand, ↓reduceIte] at h
          have hleft : ∀ m fArg' cs0 cs1 a,
              (readAndLeft x (readEquation rd cl x eqRef andRef targets n []) m fArg').run cs0 = .ok (a, cs1) →
              ∀ p ∈ a.toList,
                (∃ params res rc rs rhs, p.2 = .body params res rc rs rhs) ∧
                (∃ fc fd, definitionAt? rd.s p.1 = some (fc, fd)) := by
            intro m
            induction m with
            | zero => intro _ _ _ _ hl; simp [readAndLeft, RM_run_throw] at hl
            | succ m ihm =>
              intro fArg' cs0 cs1 a hl
              unfold readAndLeft at hl
              obtain ⟨vf, cs0', hvf', hl⟩ := RM_bind_elim hl
              cases hvf : view fArg' with
              | error _ => simp [hvf] at hvf'
              | ok vf' =>
                simp only [hvf, RM_run_lift, Ex_map_ok, Except.ok.injEq, Prod.mk.injEq] at hvf'
                obtain ⟨rfl, rfl⟩ := hvf'
                cases vf' with
                | app _ a0 => exact ih hl
                | share i =>
                  cases hsh : x.c.sharing[i]? with
                  | none => simp [hsh, RM_run_throw] at hl
                  | some ent =>
                    simp only [hsh] at hl
                    obtain ⟨_, cs2, hinner, _⟩ := enterShare_ok hl
                    exact ihm ent _ cs2 a hinner
                | _ => simp [RM_run_throw] at hl
          obtain ⟨ea, cs2, hla, h⟩ := RM_bind_elim h
          obtain ⟨eb, cs3, hlb, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          intro p hp
          rw [Array.toList_append, List.mem_append] at hp
          rcases hp with hp1 | hp2
          · exact hleft n fArg cs1 cs2 ea hla p hp1
          · exact ih hlb p hp2
        · simp only [hand, Bool.false_eq_true, ↓reduceIte] at h
          split at h
          · obtain ⟨lha, cs2, _, h⟩ := RM_bind_elim h
            cases hlf : headRefOf rd.s x.owner x.c lha.1 with
            | none => simp [hlf, RM_run_throw] at h
            | some f =>
              simp only [hlf] at h
              split at h
              · obtain ⟨_, cs3, _, h⟩ := RM_bind_elim h
                obtain ⟨tyK, cs4, _, h⟩ := RM_bind_elim h
                obtain ⟨rc, cs5, _, h⟩ := RM_bind_elim h
                obtain ⟨_, cs6, _, h⟩ := RM_bind_elim h
                obtain ⟨rhs, cs7, _, h⟩ := RM_bind_elim h
                cases hdef : definitionAt? rd.s f with
                | none => simp [hdef, RM_run_throw] at h
                | some fcd =>
                  simp only [hdef] at h
                  split at h
                  · obtain ⟨fx, cs8, _, h⟩ := RM_bind_elim h
                    obtain ⟨prf, cs9, _, h⟩ := RM_bind_elim h
                    split at h
                    · obtain ⟨_, cs10, _, h⟩ := RM_bind_elim h
                      obtain ⟨_, cs11, _, h⟩ := RM_bind_elim h
                      simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, _⟩ := h
                      intro p hp
                      simp only [List.mem_singleton] at hp
                      subst hp
                      exact ⟨⟨_, _, _, _, _, rfl⟩, ⟨fcd.1, fcd.2, hdef⟩⟩
                    · simp only [RM_run_bind, RM_run_throw] at h; cases h
                  · simp only [RM_run_bind, RM_run_throw] at h; cases h
              · simp only [RM_run_bind, RM_run_throw] at h; cases h
          · simp only [RM_run_bind, RM_run_throw] at h; cases h
      | _ => simp [RM_run_throw] at h

theorem runTable_mem_body {rd : Reading} {cl : Classifier} {rt : Array (Ref × RunDef)}
    (hrt : rd.runTable cl = .ok rt) :
    ∀ p ∈ rt.toList,
      (∃ params res rc rs rhs, p.2 = .body params res rc rs rhs) ∧
      (∃ fc fd, definitionAt? rd.s p.1 = some (fc, fd)) := by
  unfold Reading.runTable at hrt
  by_cases hemp : rd.s.runTable.isEmpty = true
  · simp only [hemp, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hrt
    subst hrt; intro _ hp; simp at hp
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hrt
    have hloop : ∀ (l : List Address) (acc out : Array (Ref × RunDef)),
        (∀ p ∈ acc.toList, (∃ params res rc rs rhs, p.2 = .body params res rc rs rhs) ∧
          (∃ fc fd, definitionAt? rd.s p.1 = some (fc, fd))) →
        (forIn (m := Except String) l acc fun a entries => do
          let some r := Ix.Kernel.Reader.resolve rd.s.store a | throw "the run table does not resolve"
          let some (c, d) := definitionAt? rd.s r | throw "the run table is not a definition"
          unless d.kind == .thm do throw "the run table is not a theorem"
          let x ← rd.rcx cl r
          let base := match r with | .member _ i => rootBase c i | _ => 0
          let es ← ((inBlock x.rm (rootKey base)
            (readEquation rd cl x (roleRef? rd.s .eq) (roleRef? rd.s .and) (runTableTargets rd) readFuel [] d.typ)).run {}).map (·.1)
          pure (ForInStep.yield (entries ++ es))) = .ok out →
        ∀ p ∈ out.toList, (∃ params res rc rs rhs, p.2 = .body params res rc rs rhs) ∧
          (∃ fc fd, definitionAt? rd.s p.1 = some (fc, fd)) := by
      intro l
      induction l with
      | nil =>
        intro acc out hacc hf
        simp only [List.forIn_nil, Ex_pure, Except.ok.injEq] at hf
        subst hf; exact hacc
      | cons a rest ih =>
        intro acc out hacc hf
        rw [List.forIn_cons] at hf
        cases hres : Ix.Kernel.Reader.resolve rd.s.store a with
        | none => simp [hres, Ex_throw, Ex_bind_err] at hf
        | some r =>
          simp only [hres] at hf
          cases hdef : definitionAt? rd.s r with
          | none => simp [hdef, Ex_throw, Ex_bind_err] at hf
          | some cd =>
            simp only [hdef] at hf
            obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
            split at hstep
            · obtain ⟨x, _, hstep⟩ := Ex_bind_elim hstep
              obtain ⟨es, hesMap, hstep⟩ := Ex_bind_elim hstep
              simp only [Ex_pure, Except.ok.injEq] at hstep
              subst hstep
              obtain ⟨pes, hes, rfl⟩ := Ex_map_elim hesMap
              obtain ⟨cs₁, hinner, _⟩ := inBlock_nodes_preserved hes
              have hnew := readEquation_mem_body hinner
              dsimp only at hf
              apply ih (acc ++ pes.1) out _ hf
              intro p hp
              rw [Array.toList_append, List.mem_append] at hp
              rcases hp with hp1 | hp2
              · exact hacc p hp1
              · exact hnew p hp2
            · simp only [Ex_throw] at hstep; cases hstep
    obtain ⟨entries, hfl, hrt⟩ := Ex_bind_elim hrt
    obtain ⟨_, _, hrt⟩ := Ex_bind_elim hrt
    simp only [Ex_pure, Except.ok.injEq] at hrt
    subst hrt
    exact hloop rd.s.runTable #[] entries (by simp) hfl

theorem rcx_c_eq {rd : Reading} {cl : Classifier} {r : Ref} {x : RCx} {c : Ixon.Constant}
    (hx : rd.rcx cl r = .ok x) (hst : rd.s.store r.block = some c) : x.c = c := by
  unfold Reading.rcx at hx
  simp only [hst, bind, Except.bind] at hx
  cases hrm : recordModes c with
  | error _ => simp [hrm] at hx
  | ok _ => simp only [hrm, Ex_pure, Except.ok.injEq] at hx; rw [← hx]

theorem rcx_bare_of_rcx {rd : Reading} {cl : Classifier} {r : Ref} {x : RCx}
    (hx : rd.rcx cl r = .ok x) : ∃ x0, (Reading.bare rd.s).rcx noClasses r = .ok x0 := by
  unfold Reading.rcx at hx ⊢
  cases hst : rd.s.store r.block with
  | none =>
    simp only [hst, Ex_throw] at hx; cases hx
  | some c =>
    have hst0 : (Reading.bare rd.s).s.store r.block = some c := hst
    simp only [hst, hst0, bind, Except.bind] at hx ⊢
    cases hrm : recordModes c with
    | error _ => simp [hrm] at hx
    | ok _ => exact ⟨_, rfl⟩

theorem externAt_ok {x : RCx} {ty : Ixon.Expr} {key : BlockKey} {d : RunDef}
    (h : externAt x ty key = .ok d) :
    ∃ ps res rc rs, d = .extern ps res rc rs ∧ ifaceAt x ty key = .ok (ps, res, rc, rs) := by
  unfold externAt at h
  cases hi : ifaceAt x ty key with
  | error _ => simp [hi, bind, Except.bind] at h
  | ok p =>
    obtain ⟨ps, res, rc, rs⟩ := p
    simp only [hi, Ex_bind_ok, Ex_pure, Except.ok.injEq] at h
    exact ⟨ps, res, rc, rs, h.symm, rfl⟩

theorem stuckAt_ok {x : RCx} {ty : Ixon.Expr} {key : BlockKey} {d : RunDef}
    (h : stuckAt x ty key = .ok d) :
    ∃ ps res rc rs, d = .stuck ps res rc rs ∧ ifaceAt x ty key = .ok (ps, res, rc, rs) ∧
      ps.all (·.mode == .many) = true ∧ res = .shared := by
  unfold stuckAt at h
  cases hi : ifaceAt x ty key with
  | error _ => simp [hi, bind, Except.bind] at h
  | ok p =>
    obtain ⟨ps, res, rc, rs⟩ := p
    simp only [hi, Ex_bind_ok] at h
    split at h
    · rename_i hok
      simp only [Ex_pure, Except.ok.injEq] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact ⟨ps, res, rc, rs, h.symm, rfl, hok.1, hok.2⟩
    · simp only [Ex_throw] at h; cases h

theorem readBody_ok {x : RCx} {caseOf : Ref → Option CaseInfo} {fuel : Nat} {bodies : Bool}
    {ty val : Ixon.Expr} {tyKey valKey : BlockKey} {d : RunDef}
    (h : readBody x caseOf fuel bodies ty val tyKey valKey = .ok d) :
    ∃ ps res rc rs t, d = .body ps res rc rs t := by
  unfold readBody at h
  obtain ⟨⟨⟨alls, cod, codSkel⟩, cs1⟩, _, h⟩ := Ex_bind_elim h
  obtain ⟨⟨⟨lams, body, ctx, params, bodyT, bodyC?⟩, cs2⟩, _, h⟩ := Ex_bind_elim h
  obtain ⟨_, _, h⟩ := Ex_bind_elim h
  dsimp only at h
  split at h
  · obtain ⟨rest, _, h⟩ := Ex_bind_elim h
    obtain ⟨k, _, h⟩ := Ex_bind_elim h
    obtain ⟨rc, _, h⟩ := Ex_bind_elim h
    simp only [Ex_pure, Except.ok.injEq] at h
    exact ⟨_, _, _, _, _, h.symm⟩
  · cases bodyC? with
    | some c =>
      obtain ⟨bc, _, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq] at h
      exact ⟨_, _, _, _, _, h.symm⟩
    | none =>
      obtain ⟨bc, _, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq] at h
      exact ⟨_, _, _, _, _, h.symm⟩

/-- Exact case decomposition of `Reading.readDef rd cl rt bodies r = .ok d`. -/
inductive ReadDefCase (rd : Reading) (cl : Classifier) (rt : Array (Ref × RunDef)) (bodies : Bool)
    (r : Ref) : RunDef → Prop where
  | prim (role : Ix.Kernel.Role) (c : Ixon.Constant) (p : Prim)
      (hro : roleOf? rd.s r = some role) (hst : rd.s.store r.block = some c)
      (hdef : recordDefault c = .ok true) (hpr : primOf rd.s role = some p) :
      ReadDefCase rd cl rt bodies r (.prim p)
  | runTable (p : Ref × RunDef) (hrt : rt.find? (·.1 == r) = some p) :
      ReadDefCase rd cl rt bodies r p.2
  | ctor (x : RCx) (b : Address) (i ci : Nat) (ms : Array Ixon.MutConst)
      (indV : Ixon.Inductive) (ctor : Ixon.Constructor) (fs : Array Field)
      (hr : r = .ctor b i ci) (hx : rd.rcx cl r = .ok x)
      (hinfo : x.c.info = .muts ms) (hmi : ms[i]? = some (.indc indV))
      (hci : indV.ctors[ci]? = some ctor)
      (hfs : readCtorFields x i ci indV.params.toNat ctor.fields.toNat ctor.typ
        (rootKey (rootBase x.c i + 1 + ci)) = .ok fs) :
      ReadDefCase rd cl rt bodies r (.ctor (.member b i) ci indV.params.toNat fs)
  | caseDef (x : RCx) (b : Address) (i : Nat) (info : CaseInfo)
      (c' : Ixon.Constant) (dd : Ixon.Definition)
      (hr : r = .member b i) (hx : rd.rcx cl r = .ok x)
      (hcs : caseShape rd.s rt 16 r = some info)
      (hdef : definitionAt? rd.s r = some (c', dd))
      (hcm : caseModes x info dd.typ dd.value (rootKey (rootBase x.c i))
        (rootKey (rootBase x.c i + 1)) = .ok ()) :
      ReadDefCase rd cl rt bodies r (.caseDef info)
  | ind (x : RCx) (b : Address) (i : Nat) (ms : Array Ixon.MutConst) (indV : Ixon.Inductive)
      (hr : r = .member b i) (hx : rd.rcx cl r = .ok x)
      (hinfo : x.c.info = .muts ms) (hmi : ms[i]? = some (.indc indV)) :
      ReadDefCase rd cl rt bodies r
        (.ind ((List.range indV.ctors.size).toArray.map fun ci => ConstRef.ctor b i ci))
  | extern (x : RCx) (b : Address) (i root : Nat) (ty : Ixon.Expr)
      (ps : Array Param) (res : ResultMode) (rc : Cls) (rs : Skel)
      (hr : r = .member b i) (hx : rd.rcx cl r = .ok x)
      (hsrc : (∃ a, x.c.info = .axio a ∧ root = 0 ∧ ty = a.typ) ∨
              (∃ dd, x.c.info = .defn dd ∧ root = rootBase x.c i ∧ ty = dd.typ) ∨
              (∃ ms dd, x.c.info = .muts ms ∧ ms[i]? = some (.defn dd) ∧
                root = rootBase x.c i ∧ ty = dd.typ))
      (hext : externAt x ty (rootKey root) = .ok (.extern ps res rc rs)) :
      ReadDefCase rd cl rt bodies r (.extern ps res rc rs)
  | stuck (x : RCx) (b : Address) (i root : Nat) (ty : Ixon.Expr)
      (ps : Array Param) (res : ResultMode) (rc : Cls) (rs : Skel)
      (hr : r = .member b i) (hx : rd.rcx cl r = .ok x)
      (hnotInd : ∀ ms indV, x.c.info = .muts ms → ms[i]? ≠ some (.indc indV))
      (hstk : stuckAt x ty (rootKey root) = .ok (.stuck ps res rc rs)) :
      ReadDefCase rd cl rt bodies r (.stuck ps res rc rs)
  | body (x : RCx) (b : Address) (i : Nat) (dd : Ixon.Definition)
      (ps : Array Param) (res : ResultMode) (rc : Cls) (rs : Skel) (t : Term)
      (hr : r = .member b i) (hx : rd.rcx cl r = .ok x)
      (hsrc : x.c.info = .defn dd ∨ ∃ ms, x.c.info = .muts ms ∧ ms[i]? = some (.defn dd))
      (hbd : readBody x (caseShape rd.s rt 16) readFuel bodies dd.typ dd.value
        (rootKey (rootBase x.c i)) (rootKey (rootBase x.c i + 1)) = .ok (.body ps res rc rs t)) :
      ReadDefCase rd cl rt bodies r (.body ps res rc rs t)

theorem readDef_elim {rd : Reading} {cl : Classifier} {rt : Array (Ref × RunDef)} {bodies : Bool}
    {r : Ref} {d : RunDef} (hrd : rd.readDef cl rt bodies r = .ok d) :
    ReadDefCase rd cl rt bodies r d := by
  have hbody : ((do
      if let some (_, d') := rt.find? (fun p : Ref × RunDef => p.1 == r) then
        return d'
      let x ← rd.rcx cl r
      let caseOf := caseShape rd.s rt 16
      match r with
      | .ctor b i ci => do
        let .muts ms := x.c.info | throw "a constructor outside a block"
        let some (.indc ind) := ms[i]? | throw "a constructor of no inductive"
        let some ctor := ind.ctors[ci]? | throw "constructor index out of range"
        let fields ← readCtorFields x i ci ind.params.toNat ctor.fields.toNat ctor.typ
          (rootKey (rootBase x.c i + 1 + ci))
        pure (RunDef.ctor (.member b i) ci ind.params.toNat fields)
      | .member _ i => do
        let base := rootBase x.c i
        if let some info := caseOf r then
          let some (_, d') := definitionAt? rd.s r | throw "a case shape that is no definition"
          caseModes x info d'.typ d'.value (rootKey base) (rootKey (base + 1))
          return RunDef.caseDef info
        let member : Option Ixon.MutConst := match x.c.info with
          | .muts ms => ms[i]?
          | .defn d' => some (.defn d')
          | .recr rr => some (.recr rr)
          | _ => none
        match x.c.info, member with
        | .axio a, _ =>
          if isExtern rd.s r then externAt x a.typ (rootKey 0) else stuckAt x a.typ (rootKey 0)
        | .quot q, _ => stuckAt x q.typ (rootKey 0)
        | _, some (.indc ind) =>
          pure (RunDef.ind ((List.range ind.ctors.size).toArray.map fun ci => ConstRef.ctor r.block i ci))
        | _, some (.recr rr) => stuckAt x rr.typ (rootKey base)
        | _, some (.defn d') =>
          let runnable := d'.kind == Ix.DefKind.defn && d'.safety == Ix.DefinitionSafety.safe
          if isExtern rd.s r then externAt x d'.typ (rootKey base)
          else if runnable then readBody x caseOf readFuel bodies d'.typ d'.value (rootKey base) (rootKey (base + 1))
          else stuckAt x d'.typ (rootKey base)
        | _, _ => throw "no constant at this reference") : Except String RunDef) = .ok d →
      ReadDefCase rd cl rt bodies r d := by
    intro h
    cases hrt : rt.find? (·.1 == r) with
    | some p =>
      simp only [hrt, Ex_pure, Except.ok.injEq] at h
      subst h
      exact .runTable p hrt
    | none =>
      simp only [hrt, bind, Except.bind] at h
      cases hx : rd.rcx cl r with
      | error _ => simp [hx] at h
      | ok x =>
        simp only [hx] at h
        cases r with
        | ctor b i ci =>
          cases hinfo : x.c.info with
          | muts ms =>
            simp only [hinfo] at h
            cases hmi : ms[i]? with
            | none => simp [hmi, Ex_throw] at h
            | some mc =>
              cases mc with
              | indc indV =>
                simp only [hmi] at h
                cases hci : indV.ctors[ci]? with
                | none => simp [hci, Ex_throw] at h
                | some ctor =>
                  simp only [hci] at h
                  cases hfs : readCtorFields x i ci indV.params.toNat ctor.fields.toNat ctor.typ
                      (rootKey (rootBase x.c i + 1 + ci)) with
                  | error _ => simp [hfs] at h
                  | ok fs =>
                    simp only [hfs, Ex_pure, Except.ok.injEq] at h
                    subst h
                    exact .ctor x b i ci ms indV ctor fs rfl hx hinfo hmi hci hfs
              | _ => simp [hmi, Ex_throw] at h
          | _ => simp [hinfo, Ex_throw] at h
        | member b i =>
          cases hcs : caseShape rd.s rt 16 (.member b i) with
          | some info =>
            simp only [hcs] at h
            cases hdef : definitionAt? rd.s (.member b i) with
            | none => simp [hdef, Ex_throw] at h
            | some cd =>
              simp only [hdef] at h
              cases hcm : caseModes x info cd.2.typ cd.2.value
                  (rootKey (rootBase x.c i)) (rootKey (rootBase x.c i + 1)) with
              | error _ => simp [hcm] at h
              | ok _ =>
                simp only [hcm, Ex_pure, Except.ok.injEq] at h
                subst h
                exact .caseDef x b i info cd.1 cd.2 rfl hx hcs hdef hcm
          | none =>
            simp only [hcs] at h
            cases hinfo : x.c.info with
            | axio a =>
              simp only [hinfo] at h
              split at h
              · obtain ⟨ps, res, rc, rs, rfl, _⟩ := externAt_ok h
                exact .extern x b i 0 a.typ ps res rc rs rfl hx (Or.inl ⟨a, hinfo, rfl, rfl⟩) h
              · obtain ⟨ps, res, rc, rs, rfl, _, _, _⟩ := stuckAt_ok h
                exact .stuck x b i 0 a.typ ps res rc rs rfl hx
                  (fun _ _ hm => by rw [hinfo] at hm; cases hm) h
            | quot q =>
              simp only [hinfo] at h
              obtain ⟨ps, res, rc, rs, rfl, _, _, _⟩ := stuckAt_ok h
              exact .stuck x b i 0 q.typ ps res rc rs rfl hx
                (fun _ _ hm => by rw [hinfo] at hm; cases hm) h
            | recr rr =>
              simp only [hinfo] at h
              obtain ⟨ps, res, rc, rs, rfl, _, _, _⟩ := stuckAt_ok h
              exact .stuck x b i (rootBase x.c i) rr.typ ps res rc rs rfl hx
                (fun _ _ hm => by rw [hinfo] at hm; cases hm) h
            | defn dd =>
              simp only [hinfo] at h
              split at h
              · obtain ⟨ps, res, rc, rs, rfl, _⟩ := externAt_ok h
                exact .extern x b i (rootBase x.c i) dd.typ ps res rc rs rfl hx
                  (Or.inr (Or.inl ⟨dd, hinfo, rfl, rfl⟩)) h
              · split at h
                · obtain ⟨ps, res, rc, rs, t, rfl⟩ := readBody_ok h
                  exact .body x b i dd ps res rc rs t rfl hx (Or.inl hinfo) h
                · obtain ⟨ps, res, rc, rs, rfl, _, _, _⟩ := stuckAt_ok h
                  exact .stuck x b i (rootBase x.c i) dd.typ ps res rc rs rfl hx
                    (fun _ _ hm => by rw [hinfo] at hm; cases hm) h
            | muts ms =>
              simp only [hinfo] at h
              cases hmi : ms[i]? with
              | none => simp [hmi, Ex_throw] at h
              | some mc =>
                simp only [hmi] at h
                cases mc with
                | indc indV =>
                  simp only [Ex_pure, Except.ok.injEq] at h
                  subst h
                  exact .ind x b i ms indV rfl hx hinfo hmi
                | recr rr =>
                  dsimp only at h
                  obtain ⟨ps, res, rc, rs, rfl, _, _, _⟩ := stuckAt_ok h
                  exact .stuck x b i (rootBase x.c i) rr.typ ps res rc rs rfl hx
                    (fun ms' _ hm hEq => by rw [hinfo] at hm; injection hm with hms; subst hms; rw [hmi] at hEq; cases hEq) h
                | defn dd =>
                  dsimp only at h
                  split at h
                  · obtain ⟨ps, res, rc, rs, rfl, _⟩ := externAt_ok h
                    exact .extern x b i (rootBase x.c i) dd.typ ps res rc rs rfl hx
                      (Or.inr (Or.inr ⟨ms, dd, hinfo, hmi, rfl, rfl⟩)) h
                  · split at h
                    · obtain ⟨ps, res, rc, rs, t, rfl⟩ := readBody_ok h
                      exact .body x b i dd ps res rc rs t rfl hx (Or.inr ⟨ms, hinfo, hmi⟩) h
                    · obtain ⟨ps, res, rc, rs, rfl, _, _, _⟩ := stuckAt_ok h
                      exact .stuck x b i (rootBase x.c i) dd.typ ps res rc rs rfl hx
                        (fun ms' _ hm hEq => by rw [hinfo] at hm; injection hm with hms; subst hms; rw [hmi] at hEq; cases hEq) h
            | _ => simp [hinfo, Ex_throw] at h
  unfold Reading.readDef at hrd
  cases hro : roleOf? rd.s r with
  | none =>
    simp only [hro] at hrd
    exact hbody hrd
  | some role =>
    simp only [hro] at hrd
    cases hst : rd.s.store r.block with
    | none => simp only [hst, Ex_throw] at hrd; cases hrd
    | some c =>
      simp only [hst, bind, Except.bind] at hrd
      cases hdef : recordDefault c with
      | error _ => simp [hdef] at hrd
      | ok b =>
        simp only [hdef] at hrd
        cases b with
        | false => simp [Ex_throw] at hrd
        | true =>
          simp only [↓reduceIte, Ex_pure] at hrd
          cases hpr : primOf rd.s role with
          | some p =>
            simp only [hpr, Except.ok.injEq] at hrd
            subst hrd
            exact .prim role c p hro hst hdef hpr
          | none =>
            simp only [hpr] at hrd
            exact hbody hrd

/-- Under `RolesDisjointFromInductives s`, every constructor in a program produced by `readProg`
appears at its constructor index in its inductive's `ctorsOf` array (`CtorsIndexed P`). -/
theorem readProg_ctorsIndexed {s : Subject} {cl : Classifier} {P : Prog}
    (hp : readProg s cl = .ok P) (hroles : RolesDisjointFromInductives s) :
    ∀ r ind cidx nP fs, P.ctorOf? r = some (ind, cidx, nP, fs) →
      (P.ctorsOf ind)[cidx]? = some r := by
  obtain ⟨_, rt, hrt, _, _, hfindElim, hmemFind, _, _⟩ := readProg_elim hp
  intro r ind cidx nP fs hco
  unfold Prog.ctorOf? at hco
  cases hfr : P.find? r with
  | none => simp [hfr] at hco
  | some d =>
    rw [hfr] at hco
    cases d with
    | ctor ind' cidx' nP' fs' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hco
      obtain ⟨c, hcl, hst, _, hrd⟩ := hfindElim r (.ctor ind' cidx' nP' fs') hfr
      generalize hd0 : RunDef.ctor ind' cidx' nP' fs' = d0 at hrd
      cases readDef_elim hrd with
      | runTable p hrtF =>
        obtain ⟨_, _, _, _, _, hbd⟩ :=
          (runTable_mem_body hrt p (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hrtF))).1
        rw [hbd] at hd0; cases hd0
      | prim _ _ _ _ _ _ _ => cases hd0
      | caseDef _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | ind _ _ _ _ _ _ _ _ _ => cases hd0
      | extern _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | stuck _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | body _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | ctor x b i ci ms indV ctor _ hr hx hinfo hmi hci _ =>
        injection hd0 with hIndEq hCiEq _ _
        subst ind'; subst cidx'
        subst hr
        simp only [ConstRef.block] at hst
        have hxc := rcx_c_eq hx hst
        have hinfoC : c.info = .muts ms := hxc ▸ hinfo
        have hlt : ci < indV.ctors.size := (Array.getElem?_eq_some_iff.mp hci).1
        have hmemInd : ConstRef.member b i ∈ (refsOf b c).toList := refsOf_mem_indc hinfoC hmi
        obtain ⟨d_ind, hrd_ind, hfind_ind⟩ := hmemFind b c (.member b i) hcl hst hmemInd
        have hindAt : inductiveAt? s (.member b i) = some indV := by
          simp [inductiveAt?, hst, hinfoC, hmi]
        have hdefAt : definitionAt? s (.member b i) = none := by
          simp [definitionAt?, hst, hinfoC, hmi]
        have hd_ind_eq :
            d_ind = .ind ((List.range indV.ctors.size).toArray.map fun j => ConstRef.ctor b i j) := by
          cases readDef_elim hrd_ind with
          | prim role _ p hro _ _ hpr =>
            change roleOf? s (.member b i) = some role at hro
            change primOf s role = some p at hpr
            have hnone := hroles (.member b i) role hro (by simp [hpr])
            rw [hindAt] at hnone; cases hnone
          | runTable q hrf =>
            have hqeq : q.1 = .member b i :=
              beq_iff_eq.mp (Array.find?_some (p := fun x : Ref × RunDef => x.1 == .member b i) hrf)
            obtain ⟨_, _, hfd⟩ :=
              (runTable_mem_body hrt q (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hrf))).2
            change definitionAt? s q.1 = some _ at hfd
            rw [hqeq, hdefAt] at hfd; cases hfd
          | ctor _ _ _ _ _ _ _ _ hr' => cases hr'
          | caseDef _ _ _ _ _ _ _ _ _ hdef' =>
            change definitionAt? s (.member b i) = some _ at hdef'
            rw [hdefAt] at hdef'; cases hdef'
          | ind x2 _ i2 ms2 indV2 hr2 hx2 hinfo2 hmi2 =>
            injection hr2 with hb2 hi2; subst b; subst hi2
            have hx2c := rcx_c_eq hx2 hst
            rw [hx2c, hinfoC] at hinfo2; injection hinfo2 with hms; subst hms
            rw [hmi] at hmi2; injection hmi2 with hmc; injection hmc with hindEq; subst hindEq
            rfl
          | extern x2 _ i2 _ _ _ _ _ _ hr2 hx2 hsrc _ =>
            injection hr2 with _ hi2; subst hi2
            have hx2c := rcx_c_eq hx2 hst
            rw [hx2c, hinfoC] at hsrc
            rcases hsrc with ⟨_, h1, _, _⟩ | ⟨_, h1, _, _⟩ | ⟨ms2, _, h1, h2, _, _⟩
            · cases h1
            · cases h1
            · injection h1 with hms; subst hms; rw [hmi] at h2; cases h2
          | stuck x2 _ i2 _ _ _ _ _ _ hr2 hx2 hnotInd _ =>
            injection hr2 with _ hi2; subst hi2
            have hx2c := rcx_c_eq hx2 hst
            exact False.elim (hnotInd ms indV (by rw [hx2c, hinfoC]) hmi)
          | body x2 _ i2 _ _ _ _ _ _ hr2 hx2 hsrc _ =>
            injection hr2 with _ hi2; subst hi2
            have hx2c := rcx_c_eq hx2 hst
            rw [hx2c, hinfoC] at hsrc
            rcases hsrc with h1 | ⟨ms2, h1, h2⟩
            · cases h1
            · injection h1 with hms; subst hms; rw [hmi] at h2; cases h2
        unfold Prog.ctorsOf
        rw [hfind_ind, hd_ind_eq]
        simp [hlt]
    | _ => simp at hco

/-! ## 5. Main Theorem: `IxCK.Resource.ReadsRespectErasure` -/

theorem openParams_getElem?_mode {x : RCx} :
    ∀ {tele : List (AllMode × Skel × Ixon.Expr)} {ctx : List Local} {ps : Array Param},
      openParams x tele = .ok (ctx, ps) →
      ps.size = tele.length ∧
      ∀ (i : Nat) (m : AllMode) (sk : Skel) (dom : Ixon.Expr),
        tele[i]? = some (m, sk, dom) → ∃ p : Param, ps[i]? = some p ∧ p.mode = m.input := by
  have hloop : ∀ (tele : List (AllMode × Skel × Ixon.Expr))
      (accCtx : List Local) (accPs : Array Param) (ctx : List Local) (ps : Array Param),
      (forIn (m := Except String) tele (accCtx, accPs) fun (m, sk, dom) (ctx, ps) => do
        let k ← x.toK ctx dom
        let pc ← x.cl.type ctx.length k
        let ps := ps.push { mode := m.input, cls := pc, skel := sk, noLeaf := x.noLeafType dom }
        let ctx := ⟨.fvar ctx.length k, pc⟩ :: ctx
        pure (ForInStep.yield (ctx, ps))) = .ok (ctx, ps) →
      ps.size = accPs.size + tele.length ∧
      (∀ j < accPs.size, ps[j]? = accPs[j]?) ∧
      (∀ (i : Nat) (m : AllMode) (sk : Skel) (dom : Ixon.Expr),
        tele[i]? = some (m, sk, dom) → ∃ p : Param, ps[accPs.size + i]? = some p ∧ p.mode = m.input) := by
    intro tele
    induction tele with
    | nil =>
      intro accCtx accPs ctx ps h
      simp only [List.forIn_nil, Ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, fun _ _ => rfl, fun _ _ _ _ h => by simp at h⟩
    | cons hd rest ih =>
      obtain ⟨m0, sk0, dom0⟩ := hd
      intro accCtx accPs ctx ps h
      rw [List.forIn_cons] at h
      cases hk : x.toK accCtx dom0 with
      | error _ => simp [hk, Ex_bind_err] at h
      | ok k =>
        simp only [hk, Ex_bind_ok] at h
        cases hpc : x.cl.type accCtx.length k with
        | error _ => simp [hpc, Ex_bind_err] at h
        | ok pc =>
          simp only [hpc, Ex_bind_ok, Ex_pure] at h
          let p0 : Param := { mode := m0.input, cls := pc, skel := sk0, noLeaf := x.noLeafType dom0 }
          obtain ⟨hsz, hpre, hrest⟩ := ih _ (accPs.push p0) ctx ps h
          refine ⟨by simp [hsz]; omega, ?_, ?_⟩
          · intro j hj
            rw [hpre j (by simp; omega), Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj]
          · intro i m sk dom hi
            cases i with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
              obtain ⟨rfl, rfl, rfl⟩ := hi
              refine ⟨p0, ?_, rfl⟩
              have hlt : accPs.size < (accPs.push p0).size := by simp
              rw [Nat.add_zero, hpre accPs.size hlt]
              simp
            | succ i =>
              simp only [List.getElem?_cons_succ] at hi
              have hadd : accPs.size + (i + 1) = (accPs.push p0).size + i := by simp; omega
              rw [hadd]
              exact hrest i m sk dom hi
  intro tele ctx ps h
  unfold openParams at h
  obtain ⟨p, hf, h⟩ := Ex_bind_elim h
  simp only [Ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hsz, _, hget⟩ := hloop tele [] #[] p.1 p.2 hf
  exact ⟨by simpa using hsz, fun i m sk dom hi => by simpa using hget i m sk dom hi⟩

theorem readCtorFields_getElem?_mode {x : RCx} {member ci nP nF : Nat} {ty : Ixon.Expr}
    {key : BlockKey} {fs : Array Field}
    (h : readCtorFields x member ci nP nF ty key = .ok fs) :
    ∃ alls rest cs,
      (inBlock x.rm key (readForalls x readFuel ty (readSkel x readFuel))).run {} = .ok ((alls, rest), cs) ∧
      (∀ (i : Nat) (m : AllMode) (sk : Skel) (dom : Ixon.Expr), alls[i]? = some (m, sk, dom) →
        (i < nP → m.input = .many) ∧
        (nP ≤ i → ∃ f : Field, fs[i - nP]? = some f ∧ f.mode = m.input)) := by
  unfold readCtorFields at h
  cases hrf : (inBlock x.rm key (readForalls x readFuel ty (readSkel x readFuel))).run {} with
  | error _ => simp [hrf, Ex_bind_err] at h
  | ok p =>
    obtain ⟨⟨alls, cod, codSkel⟩, cs⟩ := p
    simp only [hrf, Ex_bind_ok] at h
    split at h
    · -- Loop over `alls.zipIdx`
      have hloop : ∀ (l : List ((AllMode × Skel × Ixon.Expr) × Nat)) (k : Nat)
          (accCtx : List Local) (accOut : Array Field) (outCtx : List Local) (outFs : Array Field),
          (∀ idx x', l[idx]? = some x' → x'.2 = k + idx) →
          accOut.size = (if k ≤ nP then 0 else k - nP) →
          (forIn (m := Except String) l (accCtx, accOut) fun ((m, _, dom), i) (ctx, out) => do
            let kv ← x.toK ctx dom
            let pc ← x.cl.type ctx.length kv
            let ctx := ⟨.fvar ctx.length kv, pc⟩ :: ctx
            unless m.result == .shared do throw "a constructor binder with a result mode"
            if i < nP then
              unless m.input == .many do throw "a moded constructor parameter"
              pure (ForInStep.yield (ctx, out))
            else
              unless m.input == .many || m.input == .erased do
                throw "a constructor field binder with a mode other than erased"
              pure (ForInStep.yield (ctx, out.push { mode := m.input, fmode := fieldMode x.c member ci (i - nP), cls := pc }))) =
            .ok (outCtx, outFs) →
          (∀ j < accOut.size, outFs[j]? = accOut[j]?) ∧
          (∀ (m : AllMode) (sk : Skel) (dom : Ixon.Expr) (i : Nat), ((m, sk, dom), i) ∈ l →
            (i < nP → m.input = .many) ∧
            (nP ≤ i → ∃ f : Field, outFs[i - nP]? = some f ∧ f.mode = m.input)) := by
        intro l
        induction l with
        | nil =>
          intro _ _ _ _ _ _ _ hf
          simp only [List.forIn_nil, Ex_pure, Except.ok.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          exact ⟨fun _ _ => rfl, fun _ _ _ _ hm => by cases hm⟩
        | cons hd rest ih =>
          obtain ⟨⟨m0, sk0, dom0⟩, i0⟩ := hd
          intro k accCtx accOut outCtx outFs hidx hsz hf
          have hi0 : i0 = k := by
            have := hidx 0 ((m0, sk0, dom0), i0) rfl
            omega
          subst i0
          rw [List.forIn_cons] at hf
          obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
          obtain ⟨kv, _, hstep⟩ := Ex_bind_elim hstep
          obtain ⟨pc, _, hstep⟩ := Ex_bind_elim hstep
          dsimp only at hstep
          split at hstep
          · have hidx' : ∀ idx x', rest[idx]? = some x' → x'.2 = (k + 1) + idx := by
              intro idx x' hx'
              have := hidx (idx + 1) x' (by simpa using hx')
              omega
            by_cases hlt : k < nP
            · simp only [hlt, ↓reduceIte] at hstep
              split at hstep
              · rename_i hmany
                have hmany' : m0.input = .many := by simpa using hmany
                simp only [Ex_pure, Except.ok.injEq] at hstep
                subst hstep
                dsimp only at hf
                have hsz' : accOut.size = (if k + 1 ≤ nP then 0 else k + 1 - nP) := by
                  rw [hsz]; split <;> split <;> omega
                obtain ⟨hpre, hrest⟩ := ih (k + 1) _ accOut outCtx outFs hidx' hsz' hf
                refine ⟨hpre, fun m sk dom i hm => ?_⟩
                rcases List.mem_cons.mp hm with hEq | hmem
                · injection hEq with h1 h2; injection h1 with h3 _; subst h2; subst h3
                  exact ⟨fun _ => hmany', fun hge => by omega⟩
                · exact hrest m sk dom i hmem
              · simp only [Ex_throw] at hstep; cases hstep
            · simp only [hlt, ↓reduceIte] at hstep
              split at hstep
              · simp only [Ex_pure, Except.ok.injEq] at hstep
                subst hstep
                dsimp only at hf
                let f0 : Field := { mode := m0.input, fmode := fieldMode x.c member ci (k - nP), cls := pc }
                have hsz0 : accOut.size = k - nP := by
                  rw [hsz]; split <;> omega
                have hsz' : (accOut.push f0).size = (if k + 1 ≤ nP then 0 else k + 1 - nP) := by
                  simp only [Array.size_push, hsz0]
                  split <;> omega
                obtain ⟨hpre, hrest⟩ := ih (k + 1) _ (accOut.push f0) outCtx outFs hidx' hsz' hf
                refine ⟨fun j hj => by
                  rw [hpre j (by simp; omega), Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj],
                  fun m sk dom i hm => ?_⟩
                rcases List.mem_cons.mp hm with hEq | hmem
                · injection hEq with h1 h2; injection h1 with h3 _; subst h2; subst h3
                  refine ⟨fun hlt' => by omega, fun _ => ?_⟩
                  refine ⟨f0, ?_, rfl⟩
                  rw [← hsz0, hpre accOut.size (by simp)]
                  simp
                · exact hrest m sk dom i hmem
              · simp only [Ex_throw] at hstep; cases hstep
          · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
      obtain ⟨res, hfl, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq] at h
      subst h
      have hidx : ∀ idx x', alls.zipIdx[idx]? = some x' → x'.2 = 0 + idx := by
        intro idx x' hx'
        simp only [List.getElem?_zipIdx, Option.map_eq_some_iff] at hx'
        obtain ⟨a, _, hEq⟩ := hx'
        rw [← hEq]
      obtain ⟨_, hmem⟩ := hloop alls.zipIdx 0 [] #[] res.1 res.2 hidx (by simp) hfl
      exact ⟨alls, (cod, codSkel), cs, rfl, fun i m sk dom hi =>
        hmem m sk dom i (mem_zipIdx_of_getElem? hi)⟩
    · simp [Ex_throw] at h

theorem teleAgree_elim {alls lams : List (AllMode × Skel × Ixon.Expr)}
    (h : teleAgree alls lams = .ok ()) :
    (∀ i, i < lams.length → i < alls.length → lams[i]!.1 = alls[i]!.1) ∧
    (∀ i, lams.length ≤ i → i < alls.length → alls[i]!.1.isDefault = true) := by
  unfold teleAgree at h
  have hfor1 : ∀ (l : List Nat),
      (forIn (m := Except String) l () fun i _ => do
        let (lm, lsk, _) := lams[i]!
        if i < alls.length then
          let (tm, tsk, _) := alls[i]!
          unless lm == tm do throw "a λ's mode differs from its type's ∀"
          unless tsk.admits lsk do throw "a λ's domain skeleton differs from its type's ∀"
        else
          unless lm.isDefault && lsk.isDefault do throw "a moded λ beyond its type's ∀s"
        if i + 1 < lams.length then
          unless lm.result == .shared do throw "a non-default result mode before a definition's last λ"
        pure (ForInStep.yield ())) = .ok () →
      ∀ i ∈ l, i < alls.length → lams[i]!.1 = alls[i]!.1 := by
    intro l
    induction l with
    | nil => intro _ _ hm; cases hm
    | cons i rest ih =>
      intro hf j hj hjlt
      rw [List.forIn_cons] at hf
      obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
      dsimp only at hstep
      rcases List.mem_cons.mp hj with rfl | hrest
      · simp only [hjlt, ↓reduceIte] at hstep
        split at hstep
        · rename_i heq; exact beq_iff_eq.mp (by simpa using heq)
        · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
      · have hstepY : stepV = .yield () := by
          by_cases hilt : i < alls.length
          · simp only [hilt, ↓reduceIte] at hstep
            split at hstep
            · split at hstep
              · by_cases hi1 : i + 1 < lams.length
                · simp only [hi1, ↓reduceIte] at hstep
                  split at hstep
                  · simp only [Ex_pure, Except.ok.injEq] at hstep; exact hstep.symm
                  · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
                · simp only [hi1, ↓reduceIte, Ex_pure, Except.ok.injEq] at hstep; exact hstep.symm
              · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
            · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
          · simp only [hilt, ↓reduceIte] at hstep
            split at hstep
            · by_cases hi1 : i + 1 < lams.length
              · simp only [hi1, ↓reduceIte] at hstep
                split at hstep
                · simp only [Ex_pure, Except.ok.injEq] at hstep; exact hstep.symm
                · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
              · simp only [hi1, ↓reduceIte, Ex_pure, Except.ok.injEq] at hstep; exact hstep.symm
            · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
        subst hstepY
        dsimp only at hf
        exact ih hf j hrest hjlt
  have hfor2 : ∀ (l : List Nat),
      (forIn (m := Except String) l () fun i _ => do
        let (tm, _, _) := alls[i]!
        unless tm.isDefault do throw "a moded ∀ beyond its definition's λs"
        pure (ForInStep.yield ())) = .ok () →
      ∀ i ∈ l, alls[i]!.1.isDefault = true := by
    intro l
    induction l with
    | nil => intro _ _ hm; cases hm
    | cons i rest ih =>
      intro hf j hj
      rw [List.forIn_cons] at hf
      obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
      dsimp only at hstep
      split at hstep
      · rename_i hdef
        simp only [Ex_pure, Except.ok.injEq] at hstep
        subst hstep
        dsimp only at hf
        rcases List.mem_cons.mp hj with rfl | hrest
        · simpa using hdef
        · exact ih hf j hrest
      · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
  obtain ⟨_, hf1, h⟩ := Ex_bind_elim h
  obtain ⟨_, hf2, _⟩ := Ex_bind_elim h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at hf1 hf2
  have h1 := hfor1 _ hf1
  have h2 := hfor2 _ hf2
  refine ⟨fun i hi hia => h1 i ?_ hia, fun i hle hia => h2 i ?_⟩
  · simp only [Std.Legacy.Range.size, List.mem_range']; exact ⟨i, by omega, by omega⟩
  · simp only [Std.Legacy.Range.size, List.mem_range']; exact ⟨i - lams.length, by omega, by omega⟩

theorem caseModes_elim {x : RCx} {k : CaseInfo} {ty val : Ixon.Expr} {tyKey valKey : BlockKey}
    (h : caseModes x k ty val tyKey valKey = .ok ()) :
    ∃ alls lams res1 res2 cs1 cs2,
      (inBlock x.rm tyKey (readForalls x readFuel ty (readSkel x readFuel))).run {} = .ok ((alls, res1), cs1) ∧
      (inBlock x.rm valKey (readLamNodes x readFuel val fun _ body => skip x.rm readFuel body)).run {} = .ok ((lams, res2), cs2) ∧
      teleAgree alls lams = .ok () ∧
      ∀ i m sk dom, lams[i]? = some (m, sk, dom) →
        (i == k.major || k.alts.any (·.alt == i)) = true → m.input = .many := by
  unfold caseModes at h
  obtain ⟨p1, hrf, h⟩ := Ex_bind_elim h
  obtain ⟨p2, hrl, h⟩ := Ex_bind_elim h
  obtain ⟨_, hta, h⟩ := Ex_bind_elim h
  obtain ⟨_, hfor, _⟩ := Ex_bind_elim h
  have hloop : ∀ (l : List ((AllMode × Skel × Ixon.Expr) × Nat)),
      (forIn (m := Except String) l () fun ((m, _, _), i) _ => do
        unless m.result == .shared do throw "a case definition's binder with a result mode"
        if i == k.major || k.alts.any (·.alt == i) then
          unless m.input == .many do
            throw "a case definition's major premise or alternative is not of the default mode: its case rule reads it"
          pure (ForInStep.yield ())
        else
          unless m.input == .many || m.input == .erased do
            throw "a case definition's binder with a mode other than erased"
          pure (ForInStep.yield ())) = .ok () →
      ∀ m sk dom i, ((m, sk, dom), i) ∈ l →
        (i == k.major || k.alts.any (·.alt == i)) = true → m.input = .many := by
    intro l
    induction l with
    | nil => intro _ _ _ _ _ hm; cases hm
    | cons hd rest ih =>
      obtain ⟨⟨m0, sk0, dom0⟩, i0⟩ := hd
      intro hf m sk dom i hm hcond
      rw [List.forIn_cons] at hf
      obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
      dsimp only at hstep
      split at hstep
      · by_cases hc0 : (i0 == k.major || k.alts.any (·.alt == i0)) = true
        · simp only [hc0, ↓reduceIte] at hstep
          split at hstep
          · rename_i hmany
            simp only [Ex_pure, Except.ok.injEq] at hstep
            subst hstep; dsimp only at hf
            rcases List.mem_cons.mp hm with hEq | hrest
            · injection hEq with h1 _; injection h1 with h2 _; subst h2
              simpa using hmany
            · exact ih hf m sk dom i hrest hcond
          · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
        · simp only [hc0, Bool.false_eq_true, ↓reduceIte] at hstep
          split at hstep
          · simp only [Ex_pure, Except.ok.injEq] at hstep
            subst hstep; dsimp only at hf
            rcases List.mem_cons.mp hm with hEq | hrest
            · injection hEq with _ h2; subst h2; rw [hcond] at hc0; exact False.elim (hc0 rfl)
            · exact ih hf m sk dom i hrest hcond
          · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
      · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
  refine ⟨p1.1.1, p2.1.1, p1.1.2, p2.1.2, p1.2, p2.2, hrf, hrl, hta, ?_⟩
  intro i m sk dom hi hcond
  exact hloop p2.1.1.zipIdx hfor m sk dom i (mem_zipIdx_of_getElem? hi) hcond

/-- **Supplied run behaviours respect erasure (`IxCK.Resource.ReadsRespectErasure`).** -/
theorem readsRespectErasure : ReadsRespectErasure := by
  intro lim env s P hReads r d reads es i hfind hsup her hmem
  obtain ⟨_, rt, hrt, _, _, hfindElim, _, _, _⟩ := readProg_elim hReads
  obtain ⟨c, _, hst, _, hrd⟩ := hfindElim r d hfind
  have hErElim : ∀ root ty x0,
      typeRootOf c r = some (root, ty) →
      (Reading.bare s).rcx noClasses r = .ok x0 →
      ∃ alls res0 cs0 m sk dom,
        (inBlock x0.rm (rootKey root) (readForalls x0 readFuel ty (readSkel x0 readFuel))).run {} =
          .ok ((alls, res0), cs0) ∧
        alls[i]? = some (m, sk, dom) ∧ m.input = .erased := by
    intro root ty x0 htr' hx0
    unfold ifaceErased at her
    simp only [hst, htr', hx0, bind, Except.bind] at her
    cases hrf : (inBlock x0.rm (rootKey root) (readForalls x0 readFuel ty (readSkel x0 readFuel))).run {} with
    | error _ => simp [hrf] at her
    | ok p0 =>
      simp only [hrf, Ex_pure, Except.ok.injEq] at her
      rw [← her, List.mem_filterMap] at hmem
      obtain ⟨⟨⟨m, sk, dom⟩, idx⟩, hmz, hif⟩ := hmem
      by_cases hme : (m.input == .erased) = true
      · simp only [hme, ↓reduceIte, Option.some.injEq] at hif
        subst hif
        exact ⟨p0.1.1, p0.1.2, p0.2, m, sk, dom, rfl, list_getElem?_of_mem_zipIdx hmz, beq_iff_eq.mp hme⟩
      · simp [hme] at hif
  cases readDef_elim hrd with
  | prim role c' p _ hst' hdef _ =>
    change s.store r.block = some c' at hst'
    rw [hst] at hst'; injection hst' with hcEq; subst hcEq
    have hnil := ifaceErased_nil_of_recordDefault hst hdef her
    rw [hnil] at hmem; cases hmem
  | runTable q hrtF =>
    obtain ⟨_, _, _, _, _, hb⟩ :=
      (runTable_mem_body hrt q (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hrtF))).1
    rw [hb] at hsup; simp [RunDef.suppliedReads] at hsup
  | ind _ _ _ _ _ _ _ _ _ => simp [RunDef.suppliedReads] at hsup
  | stuck _ _ _ _ _ _ _ _ _ _ _ _ _ => simp [RunDef.suppliedReads] at hsup
  | body _ _ _ _ _ _ _ _ _ _ _ _ _ => simp [RunDef.suppliedReads] at hsup
  | ctor x b idx ci' ms indV ctor fs hr hx hinfo hmi hci hrcf =>
    subst hr
    simp only [RunDef.suppliedReads, Option.some.injEq] at hsup
    subst hsup
    obtain ⟨alls, _, _, hrf1, hmodes⟩ := readCtorFields_getElem?_mode hrcf
    obtain ⟨x0, hx0⟩ := rcx_bare_of_rcx hx
    have ⟨_, hxrm0, hrfEq⟩ := readForalls_rcx_eq_bare hx hx0 readFuel ctor.typ
    have hxc := rcx_c_eq hx hst
    have htr : typeRootOf c (.ctor b idx ci') = some (rootBase c idx + 1 + ci', ctor.typ) := by
      simp [typeRootOf, ← hxc, hinfo, hmi, hci]
    obtain ⟨alls0, _, _, m, sk, dom, hrf0, hget0, hmer⟩ := hErElim _ ctor.typ x0 htr hx0
    rw [← hxc, ← hxrm0, ← hrfEq] at hrf0
    rw [hrf1] at hrf0
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrf0
    obtain ⟨⟨rfl, _⟩, _⟩ := hrf0
    obtain ⟨hlo, hhi⟩ := hmodes i m sk dom hget0
    by_cases hlt : i < indV.params.toNat
    · have hm := hlo hlt
      rw [hmer] at hm; cases hm
    · obtain ⟨f, hf, hfm⟩ := hhi (Nat.le_of_not_lt hlt)
      simp [hf, Field.kept, hfm, hmer]
  | extern x b idx root ty ps res rc rs hr hx hsrc hext =>
    subst hr
    simp only [RunDef.suppliedReads, Option.some.injEq] at hsup
    subst hsup
    have hxc := rcx_c_eq hx hst
    have htrEx : ∃ r0 ty0, typeRootOf c (.member b idx) = some (r0, ty0) := by
      unfold ifaceErased at her
      simp only [hst, bind, Except.bind] at her
      cases htr : typeRootOf c (.member b idx) with
      | none => simp [htr, Ex_throw] at her
      | some tr => exact ⟨tr.1, tr.2, rfl⟩
    obtain ⟨r0, ty0, htr⟩ := htrEx
    have htrEq : r0 = root ∧ ty0 = ty := by
      rw [hxc] at hsrc
      rcases hsrc with ⟨a, hci, rfl, rfl⟩ | ⟨dd, hci, rfl, rfl⟩ | ⟨ms, dd, hci, hmi, rfl, rfl⟩
      · simp only [typeRootOf, hci] at htr
        split at htr
        · simp only [Option.some.injEq, Prod.mk.injEq] at htr; exact ⟨htr.1.symm, htr.2.symm⟩
        · cases htr
      · simp only [typeRootOf, hci] at htr
        split at htr
        · simp only [Option.some.injEq, Prod.mk.injEq] at htr
          exact ⟨by simp [← htr.1, rootBase, hci], htr.2.symm⟩
        · cases htr
      · simp only [typeRootOf, hci, hmi, Option.some.injEq, Prod.mk.injEq] at htr
        exact ⟨by simp [← htr.1], htr.2.symm⟩
    obtain ⟨rfl, rfl⟩ := htrEq
    obtain ⟨_, _, _, _, hExtEq, hi⟩ := externAt_ok hext
    injection hExtEq with hpsExt _ _ _
    unfold ifaceAt at hi
    obtain ⟨pri, hri, hpriEq⟩ := Ex_map_elim hi
    have hpsPri : pri.1.1 = ps := by
      rw [hpriEq]; exact hpsExt.symm
    obtain ⟨_, hinner, _⟩ := inBlock_nodes_preserved hri
    unfold readIface at hinner
    obtain ⟨⟨alls1, cod1, codSkel1⟩, cs1, hrf1, hinner⟩ := RM_bind_elim hinner
    obtain ⟨⟨ctx1, ps1⟩, cs2, hopL, hinner⟩ := RM_bind_elim hinner
    have hop : openParams x alls1 = .ok (ctx1, ps1) := by
      cases hop' : openParams x alls1 with
      | error _ => simp [hop'] at hopL
      | ok p => simp only [hop', RM_run_lift, Ex_map_ok, Except.ok.injEq, Prod.mk.injEq] at hopL; rw [← hopL.1]
    obtain ⟨_, cs3, _, hinner⟩ := RM_bind_elim hinner
    obtain ⟨kv, cs4, _, hinner⟩ := RM_bind_elim hinner
    obtain ⟨rc', cs5, _, hinner⟩ := RM_bind_elim hinner
    simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hinner
    have hpsEq : ps = ps1 := by
      rw [← hpsPri, ← hinner.1]
    obtain ⟨x0, hx0⟩ := rcx_bare_of_rcx hx
    have ⟨_, hxrm0, hrfEq⟩ := readForalls_rcx_eq_bare hx hx0 readFuel ty0
    obtain ⟨alls0, _, _, m, sk, dom, hrf0, hget0, hmer⟩ := hErElim r0 ty0 x0 htr hx0
    obtain ⟨_, hrf0_in, _⟩ := inBlock_nodes_preserved hrf0
    rw [← hxrm0, ← hrfEq, hrf1] at hrf0_in
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrf0_in
    obtain ⟨⟨rfl, _⟩, _⟩ := hrf0_in
    obtain ⟨_, hgetP⟩ := openParams_getElem?_mode hop
    obtain ⟨p, hp, hpm⟩ := hgetP i m sk dom hget0
    rw [hpsEq]
    simp [hp, hpm, hmer]
  | caseDef x b idx k c' defn hr hx hcs hdef hcm =>
    subst hr
    simp only [RunDef.suppliedReads, Option.some.injEq] at hsup
    subst hsup
    change s.store b = some c at hst
    change definitionAt? s (.member b idx) = some (c', defn) at hdef
    change caseShape s rt 16 (.member b idx) = some k at hcs
    have hxc := rcx_c_eq hx hst
    have hcdc_tr : c' = c ∧ typeRootOf c (.member b idx) = some (rootBase c idx, defn.typ) := by
      unfold definitionAt? at hdef
      simp only [hst, Opt_bind_some] at hdef
      cases hci : c.info with
      | defn dd =>
        simp only [hci] at hdef
        split at hdef
        · rename_i hidx0
          simp only [Option.some.injEq, Prod.mk.injEq] at hdef
          obtain ⟨rfl, rfl⟩ := hdef
          exact ⟨rfl, by simp [typeRootOf, rootBase, hci, hidx0]⟩
        · cases hdef
      | muts ms =>
        simp only [hci] at hdef
        cases hmi : ms[idx]? with
        | none => simp [hmi] at hdef
        | some mc =>
          cases mc with
          | defn dd =>
            simp only [hmi, Option.some.injEq, Prod.mk.injEq] at hdef
            obtain ⟨rfl, rfl⟩ := hdef
            exact ⟨rfl, by simp [typeRootOf, hci, hmi]⟩
          | _ => simp [hmi] at hdef
      | _ => simp [hci] at hdef
    obtain ⟨hcEq, htr⟩ := hcdc_tr
    subst c'
    rw [hxc] at hcm
    obtain ⟨alls, lams, _, _, _, _, hrf1, hrl1, hta, hcmMode⟩ := caseModes_elim hcm
    have harity : lams.length = k.arity :=
      caseShape_arity_eq_lams_length hcs hdef hxc hrl1
    obtain ⟨x0, hx0⟩ := rcx_bare_of_rcx hx
    have ⟨_, hxrm0, hrfEq⟩ := readForalls_rcx_eq_bare hx hx0 readFuel defn.typ
    obtain ⟨alls0, _, _, m, sk, dom, hrf0, hget0, hmer⟩ := hErElim (rootBase c idx) defn.typ x0 htr hx0
    rw [← hxrm0, ← hrfEq, hrf1] at hrf0
    simp only [Except.ok.injEq, Prod.mk.injEq] at hrf0
    obtain ⟨⟨rfl, _⟩, _⟩ := hrf0
    obtain ⟨htaAgree, htaTail⟩ := teleAgree_elim hta
    have hiltA : i < alls.length := (List.getElem?_eq_some_iff.mp hget0).1
    have hallBang : alls[i]! = (m, sk, dom) := by
      rw [getElem!_pos alls i hiltA]
      have := List.getElem?_eq_getElem hiltA
      rw [hget0] at this; exact (Option.some.inj this).symm
    have hiltL : i < lams.length := by
      by_cases hlt : i < lams.length
      · exact hlt
      · exfalso
        have hdefM := htaTail i (Nat.le_of_not_lt hlt) hiltA
        rw [hallBang] at hdefM
        have hmEq : m = {} := by simpa [AllMode.isDefault] using hdefM
        rw [hmEq] at hmer; cases hmer
    have hltK : ¬ (k.arity ≤ i) := by omega
    have hlamAgree : lams[i]!.1 = m := by
      have := htaAgree i hiltL hiltA
      rw [hallBang] at this; exact this
    have hlamGet : ∃ sk' dom', lams[i]? = some (m, sk', dom') := by
      refine ⟨lams[i]!.2.1, lams[i]!.2.2, ?_⟩
      rw [List.getElem?_eq_getElem hiltL, ← getElem!_pos lams i hiltL, ← hlamAgree]
    obtain ⟨sk', dom', hlg⟩ := hlamGet
    have hnotMjAlt : (i == k.major || k.alts.any (·.alt == i)) = false := by
      cases hc : (i == k.major || k.alts.any (·.alt == i)) with
      | false => rfl
      | true =>
        have hmany := hcmMode i m sk' dom' hlg hc
        rw [hmer] at hmany; cases hmany
    simp [hnotMjAlt, hltK]

/-! ## 6. Structural & Default-Mode Properties for `ModeOk` and `F5` -/

theorem natUnion_mem {x : Nat} : ∀ (a b : List Nat), x ∈ natUnion a b ↔ x ∈ a ∨ x ∈ b := by
  intro a b
  unfold natUnion
  induction b generalizing a with
  | nil => simp
  | cons y rest ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hy : a.contains y = true
    · simp only [hy, ↓reduceIte]
      have hya : y ∈ a := List.contains_iff_mem.mp hy
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hya
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

/-- `freeVars` characterizes the exact set of structural free variables (`FreeVarIn`). -/
theorem freeVars_iff :
    ∀ {n d : Nat} {t : Term} {fvs : List Nat},
      freeVars n d t = .ok fvs → ∀ x, x ∈ fvs ↔ FreeVarIn d t x := by
  intro n
  induction n with
  | zero => intro _ _ _ h; simp [freeVars, Ex_throw] at h
  | succ n ih =>
    intro d t fvs h x
    unfold freeVars at h
    cases t with
    | irr | const _ _ | natLit _ | strLit _ =>
      simp only [Ex_pure, Except.ok.injEq] at h
      subst h
      constructor
      · intro hm; cases hm
      · intro hfv; cases hfv
    | var i c =>
      simp only [Ex_pure, Except.ok.injEq] at h
      subst h
      constructor
      · intro hm
        by_cases hge : i ≥ d
        · simp only [hge, ↓reduceIte, List.mem_singleton] at hm
          subst hm
          exact .var hge
        · simp [hge] at hm
      · intro hfv
        cases hfv with
        | var hle =>
          have hge : i ≥ d := hle
          simp [hge]
    | app f a c =>
      obtain ⟨fvs1, h1, h⟩ := Ex_bind_elim h
      obtain ⟨fvs2, h2, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq] at h
      subst h
      rw [natUnion_mem]
      constructor
      · rintro (h1' | h2')
        · exact .appL ((ih h1 x).mp h1')
        · exact .appR ((ih h2 x).mp h2')
      · intro hfv
        cases hfv with
        | appL h1' => exact Or.inl ((ih h1 x).mpr h1')
        | appR h2' => exact Or.inr ((ih h2 x).mpr h2')
    | lam p res rc fv b =>
      constructor
      · intro hm; exact .lam ((ih h x).mp hm)
      · intro hfv; cases hfv with | lam hb => exact (ih h x).mpr hb
    | letE m dc v b =>
      obtain ⟨fvs1, h1, h⟩ := Ex_bind_elim h
      obtain ⟨fvs2, h2, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq] at h
      subst h
      rw [natUnion_mem]
      constructor
      · rintro (h1' | h2')
        · exact .letV ((ih h1 x).mp h1')
        · exact .letB ((ih h2 x).mp h2')
      · intro hfv
        cases hfv with
        | letV hv => exact Or.inl ((ih h1 x).mpr hv)
        | letB hb => exact Or.inr ((ih h2 x).mpr hb)
    | proj s i e c =>
      constructor
      · intro hm; exact .proj ((ih h x).mp hm)
      · intro hfv; cases hfv with | proj he => exact (ih h x).mpr he
    | case k mj alts ex c =>
      have hfor : ∀ (l : List Term) (acc out : List Nat),
          (forIn (m := Except String) l acc fun a acc => do
            pure (ForInStep.yield (natUnion acc (← freeVars n d a)))) = .ok out →
          ∀ y, y ∈ out ↔ y ∈ acc ∨ ∃ a ∈ l, FreeVarIn d a y := by
        intro l
        induction l with
        | nil =>
          intro acc out hf y
          simp only [List.forIn_nil, Ex_pure, Except.ok.injEq] at hf
          subst hf
          simp
        | cons a rest ihr =>
          intro acc out hf y
          rw [List.forIn_cons] at hf
          obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
          obtain ⟨fva, hfa, hstep⟩ := Ex_bind_elim hstep
          simp only [Ex_pure, Except.ok.injEq] at hstep
          subst hstep; dsimp only at hf
          rw [ihr (natUnion acc fva) out hf y, natUnion_mem, ih hfa y]
          constructor
          · rintro ((hy | hfv) | ⟨a', ha', hfv⟩)
            · exact Or.inl hy
            · exact Or.inr ⟨a, List.mem_cons_self .., hfv⟩
            · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hfv⟩
          · rintro (hy | ⟨a', ha', hfv⟩)
            · exact Or.inl (Or.inl hy)
            · rcases List.mem_cons.mp ha' with rfl | hrest
              · exact Or.inl (Or.inr hfv)
              · exact Or.inr ⟨a', hrest, hfv⟩
      obtain ⟨acc0, hmj, h⟩ := Ex_bind_elim h
      dsimp only at h
      rw [← Array.forIn_toList] at h
      obtain ⟨acc1, halts, h⟩ := Ex_bind_elim h
      rw [← Array.forIn_toList] at h
      obtain ⟨acc2, hex, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq] at h
      subst h
      rw [hfor ex.toList acc1 acc2 hex x, hfor alts.toList acc0 acc1 halts x, ih hmj x]
      constructor
      · rintro ((h1 | ⟨a, ha, h1⟩) | ⟨a, ha, h1⟩)
        · exact .caseMj h1
        · exact .caseAlt ha h1
        · exact .caseEx ha h1
      · intro hfv
        cases hfv with
        | caseMj h1 => exact Or.inl (Or.inl h1)
        | caseAlt ha h1 => exact Or.inl (Or.inr ⟨_, ha, h1⟩)
        | caseEx ha h1 => exact Or.inr ⟨_, ha, h1⟩

/-- `freeVars` includes every structural free variable (`FreeVarIn`). -/
theorem freeVars_sound {n d : Nat} {t : Term} {fvs : List Nat}
    (h : freeVars n d t = .ok fvs) : ∀ x, FreeVarIn d t x → x ∈ fvs :=
  fun x hfv => (freeVars_iff h x).mpr hfv

/-- Pairwise distinctness of `.field q` entries in a `CaseAlt`. -/
def CaseAltDistinct (ca : CaseAlt) : Prop :=
  ∀ i₁ i₂ q : Nat, ca.args[i₁]? = some (.field q) → ca.args[i₂]? = some (.field q) → i₁ = i₂

/-- Every alternative of a `CaseInfo` has pairwise distinct `.field q` entries. -/
def CaseInfoDistinct (k : CaseInfo) : Prop :=
  ∀ ca ∈ k.alts.toList, CaseAltDistinct ca

theorem forwarded_distinct {s : Subject} {c : Ixon.Constant} {k m : Nat}
    {map : Nat → Option FieldArg} {e : Ixon.Expr} {ca : CaseAlt}
    (h : forwarded s c k m map e = some ca) : CaseAltDistinct ca := by
  unfold forwarded at h
  obtain ⟨body, _, h⟩ := Opt_bind_elim h
  obtain ⟨⟨hd, args⟩, _, h⟩ := Opt_bind_elim h
  obtain ⟨w, _, h⟩ := Opt_bind_elim h
  obtain ⟨_, _, h⟩ := Opt_bind_elim h
  have hfor : ∀ (l : List Ixon.Expr) (acc out : Array FieldArg),
      (∀ i₁ i₂ q : Nat, acc[i₁]? = some (FieldArg.field q) → acc[i₂]? = some (FieldArg.field q) → i₁ = i₂) →
      (forIn (m := Option) l acc fun a out =>
        match varOf? c a with
        | some y => do
          guard (y < m)
          let fa ← map (m - 1 - y)
          if let .field _ := fa then
            guard (!out.contains fa)
          pure (ForInStep.yield (out.push fa))
        | none =>
          match view (Ix.Kernel.Reader.unshare c a) with
          | .ok (.ref i) => do
            let some addr := c.refs[i]? | none
            guard ((roleRef? s .punitUnit).isSome && Ix.Kernel.Reader.resolve s.store addr == roleRef? s .punitUnit)
            pure (ForInStep.yield (out.push .unit))
          | _ => none) = some out →
      ∀ i₁ i₂ q : Nat, out[i₁]? = some (FieldArg.field q) → out[i₂]? = some (FieldArg.field q) → i₁ = i₂ := by
    intro l
    induction l with
    | nil =>
      intro acc out hacc hf
      simp only [List.forIn_nil, Opt_pure, Option.some.injEq] at hf
      subst hf; exact hacc
    | cons a rest ih =>
      intro acc out hacc hf
      rw [List.forIn_cons] at hf
      obtain ⟨stepV, hstep, hf⟩ := Opt_bind_elim hf
      have hpushNonField : ∀ (fa : FieldArg), (∀ q, fa ≠ FieldArg.field q) →
          ∀ i₁ i₂ q : Nat, (acc.push fa)[i₁]? = some (FieldArg.field q) → (acc.push fa)[i₂]? = some (FieldArg.field q) → i₁ = i₂ := by
        intro fa hnf i₁ i₂ q h1 h2
        have hlt1 : i₁ < acc.size := by
          have := (Array.getElem?_eq_some_iff.mp h1).1
          simp only [Array.size_push] at this
          by_cases he : i₁ = acc.size
          · subst he; simp at h1; exact False.elim (hnf q h1)
          · omega
        have hlt2 : i₂ < acc.size := by
          have := (Array.getElem?_eq_some_iff.mp h2).1
          simp only [Array.size_push] at this
          by_cases he : i₂ = acc.size
          · subst he; simp at h2; exact False.elim (hnf q h2)
          · omega
        rw [Array.getElem?_push_lt hlt1] at h1
        rw [Array.getElem?_push_lt hlt2] at h2
        exact hacc i₁ i₂ q (by rw [Array.getElem?_eq_getElem hlt1]; exact h1)
          (by rw [Array.getElem?_eq_getElem hlt2]; exact h2)
      cases hv : varOf? c a with
      | some y =>
        simp only [hv] at hstep
        obtain ⟨_, _, hstep⟩ := Opt_bind_elim hstep
        obtain ⟨fa, _, hstep⟩ := Opt_bind_elim hstep
        cases fa with
        | field q0 =>
          dsimp only at hstep
          obtain ⟨_, hg, hstep⟩ := Opt_bind_elim hstep
          simp only [Opt_pure, Option.some.injEq] at hstep
          subst hstep; dsimp only at hf
          have hnot : FieldArg.field q0 ∉ acc.toList := by
            intro hm
            haveI : LawfulBEq FieldArg := {
              rfl := fun {a} => by cases a with | field n => exact beq_self_eq_true n | irr => rfl | unit => rfl
              eq_of_beq := fun {a b} h => by
                cases a <;> cases b
                · exact congrArg FieldArg.field (beq_iff_eq.mp h)
                · cases h
                · cases h
                · cases h
                · rfl
                · cases h
                · cases h
                · cases h
                · rfl
            }
            simp [guard] at hg
            exact hg (Array.mem_toList_iff.mp hm)
          apply ih (acc.push (.field q0)) out _ hf
          intro i₁ i₂ q h1 h2
          have hsz1 := (Array.getElem?_eq_some_iff.mp h1).1
          have hsz2 := (Array.getElem?_eq_some_iff.mp h2).1
          simp only [Array.size_push] at hsz1 hsz2
          by_cases he1 : i₁ = acc.size <;> by_cases he2 : i₂ = acc.size
          · omega
          · subst he1
            simp only [Array.getElem?_push_size, Option.some.injEq, FieldArg.field.injEq] at h1
            subst h1
            have hlt2 : i₂ < acc.size := by omega
            rw [Array.getElem?_push_lt hlt2] at h2
            have hm2 : FieldArg.field q0 ∈ acc.toList := by
              have : acc[i₂]? = some (FieldArg.field q0) := by rw [Array.getElem?_eq_getElem hlt2]; exact h2
              exact array_mem_toList_of_getElem?' this
            exact False.elim (hnot hm2)
          · subst he2
            simp only [Array.getElem?_push_size, Option.some.injEq, FieldArg.field.injEq] at h2
            subst h2
            have hlt1 : i₁ < acc.size := by omega
            rw [Array.getElem?_push_lt hlt1] at h1
            have hm1 : FieldArg.field q0 ∈ acc.toList := by
              have : acc[i₁]? = some (FieldArg.field q0) := by rw [Array.getElem?_eq_getElem hlt1]; exact h1
              exact array_mem_toList_of_getElem?' this
            exact False.elim (hnot hm1)
          · have hlt1 : i₁ < acc.size := by omega
            have hlt2 : i₂ < acc.size := by omega
            rw [Array.getElem?_push_lt hlt1] at h1
            rw [Array.getElem?_push_lt hlt2] at h2
            exact hacc i₁ i₂ q (by rw [Array.getElem?_eq_getElem hlt1]; exact h1)
              (by rw [Array.getElem?_eq_getElem hlt2]; exact h2)
        | irr =>
          dsimp only at hstep
          simp only [Opt_pure, Option.some.injEq] at hstep
          subst hstep; dsimp only at hf
          exact ih (acc.push .irr) out (hpushNonField .irr (fun _ h => by cases h)) hf
        | unit =>
          dsimp only at hstep
          simp only [Opt_pure, Option.some.injEq] at hstep
          subst hstep; dsimp only at hf
          exact ih (acc.push .unit) out (hpushNonField .unit (fun _ h => by cases h)) hf
      | none =>
        simp only [hv] at hstep
        cases hvw : view (Ix.Kernel.Reader.unshare c a) with
        | error _ => simp [hvw] at hstep
        | ok vv =>
          simp only [hvw] at hstep
          cases vv with
          | ref i =>
            cases hrf : c.refs[i]? with
            | none => simp [hrf] at hstep
            | some addr =>
              simp only [hrf] at hstep
              obtain ⟨_, _, hstep⟩ := Opt_bind_elim hstep
              simp only [Opt_pure, Option.some.injEq] at hstep
              subst hstep; dsimp only at hf
              exact ih (acc.push .unit) out (hpushNonField .unit (fun _ h => by cases h)) hf
          | _ => simp at hstep
  dsimp only at h
  rw [← Array.forIn_toList] at h
  obtain ⟨out, hfl, h⟩ := Opt_bind_elim h
  simp only [Opt_pure, Option.some.injEq] at h
  subst h
  exact hfor args.toList #[] out (fun _ _ _ h1 => by simp at h1) hfl

theorem caseShape_distinct {s : Subject} {rt : Array (Ref × RunDef)} :
    ∀ {depth : Nat} {r : Ref} {info : CaseInfo},
      caseShape s rt depth r = some info → CaseInfoDistinct info := by
  intro depth
  induction depth with
  | zero => intro _ _ h; simp [caseShape] at h
  | succ depth ih =>
    intro r info hcs
    unfold caseShape at hcs
    obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
    obtain ⟨⟨c, d⟩, _, hcs⟩ := Opt_bind_elim hcs
    obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
    obtain ⟨kb, _, hcs⟩ := Opt_bind_elim hcs
    obtain ⟨⟨h, args⟩, _, hcs⟩ := Opt_bind_elim hcs
    obtain ⟨hr, _, hcs⟩ := Opt_bind_elim hcs
    cases hrec : recursorAt? s hr with
    | some rcr =>
      obtain ⟨rc, rr⟩ := rcr
      simp only [hrec] at hcs
      obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
      obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
      obtain ⟨mj, _, hcs⟩ := Opt_bind_elim hcs
      obtain ⟨dr, _, hcs⟩ := Opt_bind_elim hcs
      cases hvw : view (Ix.Kernel.Reader.unshare rc dr.2) with
      | error _ => simp [hvw] at hcs
      | ok vv =>
        cases vv with
        | all majorTy _ =>
          simp only [hvw] at hcs
          obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
          obtain ⟨ind, _, hcs⟩ := Opt_bind_elim hcs
          obtain ⟨alts, halts, hcs⟩ := Opt_bind_elim hcs
          simp only [Opt_pure, Option.some.injEq] at hcs
          subst hcs
          have hfor : ∀ (l : List Nat) (acc out : Array CaseAlt),
              (∀ ca ∈ acc.toList, CaseAltDistinct ca) →
              (forIn (m := Option) l acc fun j alts => do
                let nf := rr.rules[j]!.fields.toNat
                let dom ← dr.1[rr.params.toNat + 1 + j]?
                let tele := (Ix.Kernel.Reader.stripAllFull rc 4096 dom).1.length
                guard (nf ≤ tele)
                let nih := tele - nf
                let arg ← args[rr.params.toNat + 1 + j]?
                match varOf? c arg with
                | some w =>
                  guard (nih == 0 && w < kb.1)
                  pure (ForInStep.yield (alts.push { alt := kb.1 - 1 - w, args := (List.range nf).toArray.map fun q => FieldArg.field q }))
                | none =>
                  let a ← forwarded s c kb.1 tele (fun q => if q < nf then some (.field q) else none) arg
                  pure (ForInStep.yield (alts.push a))) = some out →
              ∀ ca ∈ out.toList, CaseAltDistinct ca := by
            intro l
            induction l with
            | nil =>
              intro acc out hacc hf
              simp only [List.forIn_nil, Opt_pure, Option.some.injEq] at hf
              subst hf; exact hacc
            | cons j rest ihr =>
              intro acc out hacc hf
              rw [List.forIn_cons] at hf
              obtain ⟨stepV, hstep, hf⟩ := Opt_bind_elim hf
              obtain ⟨dom, _, hstep⟩ := Opt_bind_elim hstep
              obtain ⟨_, _, hstep⟩ := Opt_bind_elim hstep
              obtain ⟨arg, _, hstep⟩ := Opt_bind_elim hstep
              cases hvo : varOf? c arg with
              | some w =>
                simp only [hvo] at hstep
                obtain ⟨_, _, hstep⟩ := Opt_bind_elim hstep
                simp only [Opt_pure, Option.some.injEq] at hstep
                subst hstep; dsimp only at hf
                apply ihr _ out _ hf
                intro ca hca
                rw [Array.toList_push, List.mem_append, List.mem_singleton] at hca
                rcases hca with h0 | rfl
                · exact hacc ca h0
                · intro i₁ i₂ q h1 h2
                  simp only [Array.getElem?_map, List.getElem?_toArray] at h1 h2
                  have hp1 : i₁ = q := by
                    by_cases hlt1 : i₁ < rr.rules[j]!.fields.toNat
                    · rw [List.getElem?_range hlt1] at h1
                      simp only [Option.map_some, Option.some.injEq, FieldArg.field.injEq] at h1
                      exact h1
                    · rw [List.getElem?_eq_none (by simp; omega)] at h1
                      simp at h1
                  have hp2 : i₂ = q := by
                    by_cases hlt2 : i₂ < rr.rules[j]!.fields.toNat
                    · rw [List.getElem?_range hlt2] at h2
                      simp only [Option.map_some, Option.some.injEq, FieldArg.field.injEq] at h2
                      exact h2
                    · rw [List.getElem?_eq_none (by simp; omega)] at h2
                      simp at h2
                  omega
              | none =>
                simp only [hvo] at hstep
                obtain ⟨a, ha, hstep⟩ := Opt_bind_elim hstep
                simp only [Opt_pure, Option.some.injEq] at hstep
                subst hstep; dsimp only at hf
                apply ihr _ out _ hf
                intro ca hca
                rw [Array.toList_push, List.mem_append, List.mem_singleton] at hca
                rcases hca with h0 | rfl
                · exact hacc ca h0
                · exact forwarded_distinct ha
          rw [Std.Legacy.Range.forIn_eq_forIn_range'] at halts
          exact hfor _ #[] alts (by simp) halts
        | _ => simp [hvw] at hcs
    | none =>
      simp only [hrec] at hcs
      obtain ⟨ch, hch, hcs⟩ := Opt_bind_elim hcs
      obtain ⟨_, _, hcs⟩ := Opt_bind_elim hcs
      obtain ⟨mj, _, hcs⟩ := Opt_bind_elim hcs
      rw [← Array.forIn_toList] at hcs
      obtain ⟨alts, halts, hcs⟩ := Opt_bind_elim hcs
      simp only [Opt_pure, Option.some.injEq] at hcs
      subst hcs
      have hchDist : CaseInfoDistinct ch := ih hch
      have hfor : ∀ (l : List CaseAlt) (acc out : Array CaseAlt),
          (∀ ca ∈ l, CaseAltDistinct ca) →
          (∀ ca ∈ acc.toList, CaseAltDistinct ca) →
          (forIn (m := Option) l acc fun ca alts => do
            let arg ← args[ca.alt]?
            match varOf? c arg with
            | some w =>
              guard (w < kb.1)
              pure (ForInStep.yield (alts.push { alt := kb.1 - 1 - w, args := ca.args }))
            | none =>
              let map (q : Nat) : Option FieldArg := do
                let fa ← ca.args[q]?
                guard (fa != .irr)
                pure fa
              let a ← forwarded s c kb.1 ca.args.size map arg
              pure (ForInStep.yield (alts.push a))) = some out →
          ∀ ca ∈ out.toList, CaseAltDistinct ca := by
        intro l
        induction l with
        | nil =>
          intro acc out _ hacc hf
          simp only [List.forIn_nil, Opt_pure, Option.some.injEq] at hf
          subst hf; exact hacc
        | cons ca0 rest ihr =>
          intro acc out hl hacc hf
          rw [List.forIn_cons] at hf
          obtain ⟨stepV, hstep, hf⟩ := Opt_bind_elim hf
          obtain ⟨arg, _, hstep⟩ := Opt_bind_elim hstep
          cases hvo : varOf? c arg with
          | some w =>
            simp only [hvo] at hstep
            obtain ⟨_, _, hstep⟩ := Opt_bind_elim hstep
            simp only [Opt_pure, Option.some.injEq] at hstep
            subst hstep; dsimp only at hf
            apply ihr _ out (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ hf
            intro ca hca
            rw [Array.toList_push, List.mem_append, List.mem_singleton] at hca
            rcases hca with h0 | rfl
            · exact hacc ca h0
            · exact hl ca0 (List.mem_cons_self ..)
          | none =>
            simp only [hvo] at hstep
            obtain ⟨a, ha, hstep⟩ := Opt_bind_elim hstep
            simp only [Opt_pure, Option.some.injEq] at hstep
            subst hstep; dsimp only at hf
            apply ihr _ out (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ hf
            intro ca hca
            rw [Array.toList_push, List.mem_append, List.mem_singleton] at hca
            rcases hca with h0 | rfl
            · exact hacc ca h0
            · exact forwarded_distinct ha
      exact hfor ch.alts.toList #[] alts hchDist (by simp) halts

/-! ### Structural & default-mode preservation of `readTerm` -/

/-- Structural fuel-free predicate: every `letE` in `e` carries the default mode `.value .many`. -/
def ExprLetsDefault : Ixon.Expr → Prop
  | .letE _ m t v b => m = .value .many ∧ ExprLetsDefault t ∧ ExprLetsDefault v ∧ ExprLetsDefault b
  | .lam t b | .all t b => ExprLetsDefault t ∧ ExprLetsDefault b
  | .app f a => ExprLetsDefault f ∧ ExprLetsDefault a
  | .prj _ _ v => ExprLetsDefault v
  | _ => True

theorem letsDefault_ok_true : ∀ {n : Nat} {e : Ixon.Expr}, letsDefault n e = .ok true → ExprLetsDefault e := by
  intro n
  induction n with
  | zero => intro _ h; simp [letsDefault, Ex_throw] at h
  | succ n ih =>
    intro e h
    unfold letsDefault at h
    obtain ⟨vv, hv, h⟩ := Ex_bind_elim h
    cases e with
    | letE nonDep m t v b =>
      simp only [view, Ex_pure, Except.ok.injEq] at hv; subst hv
      obtain ⟨b1, h1, h⟩ := Ex_bind_elim h
      obtain ⟨b2, h2, h⟩ := Ex_bind_elim h
      obtain ⟨b3, h3, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, hb1⟩, hb2⟩, hb3⟩ := h
      subst hb1; subst hb2; subst hb3
      exact ⟨rfl, ih h1, ih h2, ih h3⟩
    | lam t b | all t b =>
      simp only [view, Ex_pure, Except.ok.injEq] at hv; subst hv
      obtain ⟨b1, h1, h⟩ := Ex_bind_elim h
      obtain ⟨b2, h2, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq, Bool.and_eq_true] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ih h1, ih h2⟩
    | app f a =>
      simp only [view, Ex_pure, Except.ok.injEq] at hv; subst hv
      obtain ⟨b1, h1, h⟩ := Ex_bind_elim h
      obtain ⟨b2, h2, h⟩ := Ex_bind_elim h
      simp only [Ex_pure, Except.ok.injEq, Bool.and_eq_true] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ih h1, ih h2⟩
    | prj _ _ v =>
      simp only [view, Ex_pure, Except.ok.injEq] at hv; subst hv
      dsimp only [ExprLetsDefault]
      exact ih h
    | _ => trivial

theorem ixSpine_letsDefault :
    ∀ {n : Nat} {e h : Ixon.Expr} {args : Array Ixon.Expr},
      ExprLetsDefault e → ixSpine n e = .ok (h, args) →
      ExprLetsDefault h ∧ ∀ a ∈ args.toList, ExprLetsDefault a := by
  intro n
  induction n with
  | zero => intro _ _ _ _ hsp; simp [ixSpine, Ex_throw] at hsp
  | succ n ih =>
    intro e h args he hsp
    unfold ixSpine at hsp
    obtain ⟨vv, hv, hsp⟩ := Ex_bind_elim hsp
    cases e with
    | app f a =>
      simp only [view, Ex_pure, Except.ok.injEq] at hv; subst hv
      obtain ⟨⟨h0, as0⟩, hsp0, hsp⟩ := Ex_bind_elim hsp
      simp only [Ex_pure, Except.ok.injEq, Prod.mk.injEq] at hsp
      obtain ⟨rfl, rfl⟩ := hsp
      obtain ⟨hh, has⟩ := ih he.1 hsp0
      refine ⟨hh, fun x hx => ?_⟩
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx0 | rfl
      · exact has x hx0
      · exact he.2
    | _ =>
      simp only [view, Ex_pure, Except.ok.injEq] at hv; subst hv
      simp only [Ex_pure, Except.ok.injEq, Prod.mk.injEq] at hsp
      obtain ⟨rfl, rfl⟩ := hsp
      exact ⟨he, by simp⟩

/-- Every `.lam` and `.letE` binder in `t` carries only default modes (`.many`/`.shared` and `.value .many`). -/
inductive TermModesDefault : Term → Prop
  | irr : TermModesDefault .irr
  | var {i c} : TermModesDefault (.var i c)
  | const {r c} : TermModesDefault (.const r c)
  | natLit {n} : TermModesDefault (.natLit n)
  | strLit {s} : TermModesDefault (.strLit s)
  | app {f a c} : TermModesDefault f → TermModesDefault a → TermModesDefault (.app f a c)
  | lam {p res rc fvs b} :
      p.mode = .many → res = .shared → TermModesDefault b → TermModesDefault (.lam p res rc fvs b)
  | letE {d v b} : TermModesDefault v → TermModesDefault b → TermModesDefault (.letE (.value .many) d v b)
  | proj {s i e c} : TermModesDefault e → TermModesDefault (.proj s i e c)
  | case {k mj alts ex c} :
      TermModesDefault mj →
      (∀ a ∈ alts.toList, TermModesDefault a) →
      (∀ a ∈ ex.toList, TermModesDefault a) →
      TermModesDefault (.case k mj alts ex c)

theorem termSpine_props : ∀ {t h : Term} {pre : Array Term}, termSpine t = (h, pre) →
    (LamsClosed t → LamsClosed h ∧ ∀ a ∈ pre.toList, LamsClosed a) ∧
    (CaseFieldsDistinct t → CaseFieldsDistinct h ∧ ∀ a ∈ pre.toList, CaseFieldsDistinct a) ∧
    (TermModesDefault t → TermModesDefault h ∧ ∀ a ∈ pre.toList, TermModesDefault a)
  | .app f a c, h, pre, hsp => by
    unfold termSpine at hsp
    cases hsf : termSpine f with
    | mk hf asf =>
      rw [hsf] at hsp
      simp only [Prod.mk.injEq] at hsp
      obtain ⟨rfl, rfl⟩ := hsp
      obtain ⟨ihL, ihC, ihD⟩ := termSpine_props hsf
      refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩
      · cases ht with
        | app hfl hal =>
          obtain ⟨h1, h2⟩ := ihL hfl
          refine ⟨h1, fun x hx => ?_⟩
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx0 | rfl
          · exact h2 x hx0
          · exact hal
      · cases ht with
        | app hfl hal =>
          obtain ⟨h1, h2⟩ := ihC hfl
          refine ⟨h1, fun x hx => ?_⟩
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx0 | rfl
          · exact h2 x hx0
          · exact hal
      · cases ht with
        | app hfl hal =>
          obtain ⟨h1, h2⟩ := ihD hfl
          refine ⟨h1, fun x hx => ?_⟩
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx0 | rfl
          · exact h2 x hx0
          · exact hal
  | .irr, h, pre, hsp | .var _ _, h, pre, hsp | .const _ _, h, pre, hsp | .natLit _, h, pre, hsp
  | .strLit _, h, pre, hsp | .lam _ _ _ _ _, h, pre, hsp | .letE _ _ _ _, h, pre, hsp
  | .proj _ _ _ _, h, pre, hsp | .case _ _ _ _ _, h, pre, hsp => by
    unfold termSpine at hsp
    simp only [Prod.mk.injEq] at hsp
    obtain ⟨rfl, rfl⟩ := hsp
    exact ⟨fun ht => ⟨ht, by simp⟩, fun ht => ⟨ht, by simp⟩, fun ht => ⟨ht, by simp⟩⟩

theorem foldApp_props {h : Term} {args : Array Term} {c : Cls} :
    (LamsClosed h → (∀ a ∈ args.toList, LamsClosed a) → LamsClosed (foldApp h args c)) ∧
    (CaseFieldsDistinct h → (∀ a ∈ args.toList, CaseFieldsDistinct a) → CaseFieldsDistinct (foldApp h args c)) ∧
    (TermModesDefault h → (∀ a ∈ args.toList, TermModesDefault a) → TermModesDefault (foldApp h args c)) := by
  unfold foldApp
  rw [← Array.foldl_toList]
  have aux : ∀ (l : List (Term × Nat)) (acc : Term),
      (LamsClosed acc → (∀ p ∈ l, LamsClosed p.1) → LamsClosed (l.foldl (fun f (a, i) => Term.app f a (if i + 1 == args.size then c else .val)) acc)) ∧
      (CaseFieldsDistinct acc → (∀ p ∈ l, CaseFieldsDistinct p.1) → CaseFieldsDistinct (l.foldl (fun f (a, i) => Term.app f a (if i + 1 == args.size then c else .val)) acc)) ∧
      (TermModesDefault acc → (∀ p ∈ l, TermModesDefault p.1) → TermModesDefault (l.foldl (fun f (a, i) => Term.app f a (if i + 1 == args.size then c else .val)) acc)) := by
    intro l
    induction l with
    | nil => intro acc; exact ⟨fun h _ => h, fun h _ => h, fun h _ => h⟩
    | cons p rest ih =>
      intro acc
      simp only [List.foldl_cons]
      obtain ⟨ihL, ihC, ihD⟩ := ih (Term.app acc p.1 (if p.2 + 1 == args.size then c else .val))
      refine ⟨fun ha hl => ihL (.app ha (hl p (List.mem_cons_self ..))) (fun q hq => hl q (List.mem_cons_of_mem _ hq)),
              fun ha hl => ihC (.app ha (hl p (List.mem_cons_self ..))) (fun q hq => hl q (List.mem_cons_of_mem _ hq)),
              fun ha hl => ihD (.app ha (hl p (List.mem_cons_self ..))) (fun q hq => hl q (List.mem_cons_of_mem _ hq))⟩
  obtain ⟨hL, hC, hD⟩ := aux args.zipIdx.toList h
  have hzip : ∀ p ∈ args.zipIdx.toList, p.1 ∈ args.toList := by
    intro p hp
    rw [Array.toList_zipIdx] at hp
    exact list_mem_of_mem_zipIdx' hp
  exact ⟨fun hh ha => hL hh (fun p hp => ha p.1 (hzip p hp)),
         fun hh ha => hC hh (fun p hp => ha p.1 (hzip p hp)),
         fun hh ha => hD hh (fun p hp => ha p.1 (hzip p hp))⟩

theorem array_extract_mem {α : Type} {arr : Array α} {s e : Nat} {x : α}
    (hx : x ∈ (arr.extract s e).toList) : x ∈ arr.toList := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < (arr.extract s e).size := by rw [← Array.length_toList]; exact hi
  rw [Array.getElem_toList, Array.getElem_extract]
  have hlt : s + i < arr.size := by
    rw [Array.size_extract] at hi'; omega
  exact Array.mem_toList_iff.mpr (Array.getElem_mem hlt)

/-- Every term returned by `readTerm` satisfies `LamsClosed` and `CaseFieldsDistinct` (when
`caseOf` returns `CaseInfoDistinct` shapes). -/
theorem readTerm_struct {x : RCx} {caseOf : Ref → Option CaseInfo}
    (hcase : ∀ r k, caseOf r = some k → CaseInfoDistinct k) :
    ∀ {n : Nat} {ctx : List Local} {e : Ixon.Expr} {cs cs' : Cursor} {t : Term} {tc : Cls},
      (readTerm x caseOf n ctx e).run cs = .ok ((t, tc), cs') →
      LamsClosed t ∧ CaseFieldsDistinct t := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ h; simp [readTerm, RM_run_throw] at h
  | succ n ih =>
    intro ctx e cs cs' t tc h
    unfold readTerm at h
    obtain ⟨v, cs0, _, h⟩ := RM_bind_elim h
    have hnonVar : ((do
        let c ← x.cl.node ctx.length (← x.toK ctx e)
        if c == .irr then do
          skip x.rm n e
          return (.irr, .irr)
        match v with
        | .var _ | .sort | .all .. => do skip x.rm n e; pure (.irr, .irr)
        | .ref i => return (.const (← x.refAt i) c, c)
        | .recur i =>
          match x.recur i with
          | some r => pure (.const r c, c)
          | none => throw "recursive reference outside its block"
        | .nat i => return (.natLit (Ix.Kernel.Reader.natural (← x.blobAt i)), c)
        | .str i => do
          let some s := String.fromUTF8? (← x.blobAt i) | throw "string literal is not valid UTF-8"
          pure (.strLit s, c)
        | .prj t f v => do
          let s ← x.refAt t
          let (vt, _) ← readTerm x caseOf n ctx v
          pure (.proj s f vt c, c)
        | .app .. => do
          let (h, args) ← ixSpine n e
          let (ht, _) ← readTerm x caseOf n ctx h
          let mut ats : Array Term := #[]
          for a in args do ats := ats.push (← readTerm x caseOf n ctx a).1
          let (h', pre) := termSpine ht
          let all := pre ++ ats
          match h' with
          | .const r _ =>
            match caseOf r with
            | some k =>
              if all.size ≥ k.arity then
                let alts := k.alts.map fun a => all[a.alt]?.getD .irr
                return (.case k (all[k.major]?.getD .irr) alts (all.extract k.arity all.size) c, c)
              else pure (foldApp h' all c, c)
            | none => pure (foldApp h' all c, c)
          | _ => pure (foldApp h' all c, c)
        | .lam ty b => do
          let m ← nextBinder
          let k ← x.toK ctx ty
          let pc ← x.cl.type ctx.length k
          let ps ← readSkel x n ty
          let (bt, bc) ← readTerm x caseOf n (⟨.fvar ctx.length k, pc⟩ :: ctx) b
          let fvs ← freeVars n 1 bt
          pure (.lam { mode := m.input, cls := pc, skel := ps, noLeaf := x.noLeafType ty } m.result bc
            fvs.toArray bt, c)
        | .letE m ty v b => do
          let k ← x.toK ctx ty
          let dc ← x.cl.type ctx.length k
          skip x.rm n ty
          let (vt, _) ← readTerm x caseOf n ctx v
          let (bt, bc) ← readTerm x caseOf n (⟨.fvar ctx.length k, dc⟩ :: ctx) b
          pure (.letE m dc vt bt, bc)
        | .share i => do
          let some ent := x.c.sharing[i]? | throw "sharing reference out of range"
          enterShare x.rm i (readTerm x caseOf n ctx ent)) : RM (Term × Cls)).run cs0 = .ok ((t, tc), cs') →
        LamsClosed t ∧ CaseFieldsDistinct t := by
      intro h
      obtain ⟨k0, cs1, _, h⟩ := RM_bind_elim h
      obtain ⟨c0, cs2, _, h⟩ := RM_bind_elim h
      by_cases hirr : (c0 == .irr) = true
      · simp only [hirr, ↓reduceIte] at h
        obtain ⟨_, cs3, _, h⟩ := RM_bind_elim h
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, _⟩, _⟩ := h
        exact ⟨.irr, .irr⟩
      · simp only [hirr, Bool.false_eq_true, ↓reduceIte] at h
        cases v with
        | var _ | sort | all _ _ =>
          obtain ⟨_, cs3, _, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, _⟩ := h
          exact ⟨.irr, .irr⟩
        | ref i =>
          obtain ⟨rf, cs3, _, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, _⟩ := h
          exact ⟨.const, .const⟩
        | recur i =>
          cases hr : x.recur i with
          | none => simp [hr, RM_run_throw] at h
          | some rf =>
            simp only [hr, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, _⟩, _⟩ := h
            exact ⟨.const, .const⟩
        | nat i =>
          obtain ⟨bl, cs3, _, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, _⟩ := h
          exact ⟨.natLit, .natLit⟩
        | str i =>
          obtain ⟨bl, cs3, _, h⟩ := RM_bind_elim h
          cases hs : String.fromUTF8? bl with
          | none => simp [hs, RM_run_throw] at h
          | some str =>
            simp only [hs, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, _⟩, _⟩ := h
            exact ⟨.strLit, .strLit⟩
        | prj ty f val =>
          obtain ⟨s0, cs3, _, h⟩ := RM_bind_elim h
          obtain ⟨⟨vt, vc⟩, cs4, hvt, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, _⟩ := h
          obtain ⟨hL, hC⟩ := ih hvt
          exact ⟨.proj hL, .proj hC⟩
        | app _ _ =>
          obtain ⟨⟨hd, args⟩, cs3, _, h⟩ := RM_bind_elim h
          obtain ⟨⟨ht, hc⟩, cs4, hht, h⟩ := RM_bind_elim h
          have hfor : ∀ (l : List Ixon.Expr) (acc out : Array Term) (c0 c1 : Cursor),
              (∀ a ∈ acc.toList, LamsClosed a ∧ CaseFieldsDistinct a) →
              (forIn (m := RM) l acc fun a ats => do
                pure (ForInStep.yield (ats.push (← readTerm x caseOf n ctx a).1))).run c0 = .ok (out, c1) →
              ∀ a ∈ out.toList, LamsClosed a ∧ CaseFieldsDistinct a := by
            intro l
            induction l with
            | nil =>
              intro acc out c0 c1 hacc hf
              simp only [List.forIn_nil, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, _⟩ := hf; exact hacc
            | cons a rest ihr =>
              intro acc out c0 c1 hacc hf
              rw [List.forIn_cons] at hf
              obtain ⟨stepV, cMid, hstep, hf⟩ := RM_bind_elim hf
              obtain ⟨⟨at0, ac0⟩, cMid2, hat0, hstep⟩ := RM_bind_elim hstep
              simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              dsimp only at hf
              apply ihr (acc.push at0) out cMid2 c1 _ hf
              intro y hy
              rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
              rcases hy with hy0 | rfl
              · exact hacc y hy0
              · exact ih hat0
          dsimp only at h
          rw [← Array.forIn_toList] at h
          obtain ⟨ats, cs5, hats, h⟩ := RM_bind_elim h
          obtain ⟨hhtL, hhtC⟩ := ih hht
          have hatsOk := hfor args.toList #[] ats cs4 cs5 (by simp) hats
          cases hsp : termSpine ht with
          | mk h' pre =>
            obtain ⟨hspL, hspC, _⟩ := termSpine_props hsp
            obtain ⟨hh'L, hpreL⟩ := hspL hhtL
            obtain ⟨hh'C, hpreC⟩ := hspC hhtC
            have hallOk : ∀ a ∈ (pre ++ ats).toList, LamsClosed a ∧ CaseFieldsDistinct a := by
              intro a ha
              rw [Array.toList_append, List.mem_append] at ha
              rcases ha with hp | hb
              · exact ⟨hpreL a hp, hpreC a hp⟩
              · exact hatsOk a hb
            have hgetOk : ∀ idx : Nat, LamsClosed ((pre ++ ats)[idx]?.getD .irr) ∧
                CaseFieldsDistinct ((pre ++ ats)[idx]?.getD .irr) := by
              intro idx
              cases hg : (pre ++ ats)[idx]? with
              | none => exact ⟨.irr, .irr⟩
              | some a => exact hallOk a (array_mem_toList_of_getElem?' hg)
            have hfoldOk : LamsClosed (foldApp h' (pre ++ ats) c0) ∧
                CaseFieldsDistinct (foldApp h' (pre ++ ats) c0) :=
              ⟨foldApp_props.1 hh'L (fun a ha => (hallOk a ha).1),
               foldApp_props.2.1 hh'C (fun a ha => (hallOk a ha).2)⟩
            simp only [hsp] at h
            cases h' with
            | const r rc =>
              cases hco : caseOf r with
              | none =>
                simp only [hco, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨⟨rfl, _⟩, _⟩ := h; exact hfoldOk
              | some k =>
                simp only [hco] at h
                split at h
                · simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨⟨rfl, _⟩, _⟩ := h
                  refine ⟨.case (hgetOk k.major).1 ?_ ?_, .case (hcase r k hco) (hgetOk k.major).2 ?_ ?_⟩
                  · intro a ha
                    rw [Array.toList_map, List.mem_map] at ha
                    obtain ⟨ca, _, rfl⟩ := ha
                    exact (hgetOk ca.alt).1
                  · intro a ha
                    exact (hallOk a (array_extract_mem ha)).1
                  · intro a ha
                    rw [Array.toList_map, List.mem_map] at ha
                    obtain ⟨ca, _, rfl⟩ := ha
                    exact (hgetOk ca.alt).2
                  · intro a ha
                    exact (hallOk a (array_extract_mem ha)).2
                · simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨⟨rfl, _⟩, _⟩ := h; exact hfoldOk
            | _ =>
              simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨⟨rfl, _⟩, _⟩ := h; exact hfoldOk
        | lam ty b =>
          obtain ⟨m, cs3, _, h⟩ := RM_bind_elim h
          obtain ⟨k, cs4, _, h⟩ := RM_bind_elim h
          obtain ⟨pc, cs5, _, h⟩ := RM_bind_elim h
          obtain ⟨ps, cs6, _, h⟩ := RM_bind_elim h
          obtain ⟨⟨bt, bc⟩, cs7, hbt, h⟩ := RM_bind_elim h
          obtain ⟨fvs, cs8, hfvsL, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, _⟩ := h
          have hfvs : freeVars n 1 bt = .ok fvs := by
            cases hf : freeVars n 1 bt with
            | error _ => simp [hf] at hfvsL
            | ok v => simp only [hf, RM_run_lift, Ex_map_ok, Except.ok.injEq, Prod.mk.injEq] at hfvsL; rw [← hfvsL.1]
          obtain ⟨hbL, hbC⟩ := ih hbt
          refine ⟨.lam hbL (fun v => by
            simpa using freeVars_iff hfvs v), .lam hbC⟩
        | letE m ty val b =>
          obtain ⟨k, cs3, _, h⟩ := RM_bind_elim h
          obtain ⟨dc, cs4, _, h⟩ := RM_bind_elim h
          obtain ⟨_, cs5, _, h⟩ := RM_bind_elim h
          obtain ⟨⟨vt, _⟩, cs6, hvt, h⟩ := RM_bind_elim h
          obtain ⟨⟨bt, _⟩, cs7, hbt, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, _⟩ := h
          obtain ⟨hvL, hvC⟩ := ih hvt
          obtain ⟨hbL, hbC⟩ := ih hbt
          exact ⟨.letE hvL hbL, .letE hvC hbC⟩
        | share i =>
          cases hsh : x.c.sharing[i]? with
          | none => simp [hsh, RM_run_throw] at h
          | some ent =>
            simp only [hsh] at h
            obtain ⟨_, cs₁, hinner, _⟩ := enterShare_ok h
            exact ih hinner
    cases v with
    | var i =>
      cases hget : ctx[i]? with
      | none => simp [hget, RM_run_throw] at h
      | some l =>
        simp only [hget, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, _⟩, _⟩ := h
        cases l.cls == .irr <;> exact ⟨by constructor, by constructor⟩
    | _ => exact hnonVar h

/-- Under `BlocksDefault x.rm` and `ExprLetsDefault` on `e` and `x.c.sharing`, every term returned
by `readTerm` satisfies `TermModesDefault`. -/
theorem readTerm_modesDefault {x : RCx} {caseOf : Ref → Option CaseInfo}
    (hbd : BlocksDefault x.rm) (hshDef : ∀ ent ∈ x.c.sharing.toList, ExprLetsDefault ent) :
    ∀ {n : Nat} {ctx : List Local} {e : Ixon.Expr} {cs cs' : Cursor} {t : Term} {tc : Cls},
      ExprLetsDefault e →
      (∀ nd ∈ cs.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
      (readTerm x caseOf n ctx e).run cs = .ok ((t, tc), cs') →
      TermModesDefault t ∧ cs'.nodes = cs.nodes := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [readTerm, RM_run_throw] at h
  | succ n ih =>
    intro ctx e cs cs' t tc he hcs h
    unfold readTerm at h
    obtain ⟨v, cs0, hvl, h⟩ := RM_bind_elim h
    obtain ⟨hv, hcs0⟩ := RM_lift_elim hvl
    subst cs0
    have hnonVar : ((do
        let c ← x.cl.node ctx.length (← x.toK ctx e)
        if c == .irr then do
          skip x.rm n e
          return (.irr, .irr)
        match v with
        | .var _ | .sort | .all .. => do skip x.rm n e; pure (.irr, .irr)
        | .ref i => return (.const (← x.refAt i) c, c)
        | .recur i =>
          match x.recur i with
          | some r => pure (.const r c, c)
          | none => throw "recursive reference outside its block"
        | .nat i => return (.natLit (Ix.Kernel.Reader.natural (← x.blobAt i)), c)
        | .str i => do
          let some s := String.fromUTF8? (← x.blobAt i) | throw "string literal is not valid UTF-8"
          pure (.strLit s, c)
        | .prj t f v => do
          let s ← x.refAt t
          let (vt, _) ← readTerm x caseOf n ctx v
          pure (.proj s f vt c, c)
        | .app .. => do
          let (h, args) ← ixSpine n e
          let (ht, _) ← readTerm x caseOf n ctx h
          let mut ats : Array Term := #[]
          for a in args do ats := ats.push (← readTerm x caseOf n ctx a).1
          let (h', pre) := termSpine ht
          let all := pre ++ ats
          match h' with
          | .const r _ =>
            match caseOf r with
            | some k =>
              if all.size ≥ k.arity then
                let alts := k.alts.map fun a => all[a.alt]?.getD .irr
                return (.case k (all[k.major]?.getD .irr) alts (all.extract k.arity all.size) c, c)
              else pure (foldApp h' all c, c)
            | none => pure (foldApp h' all c, c)
          | _ => pure (foldApp h' all c, c)
        | .lam ty b => do
          let m ← nextBinder
          let k ← x.toK ctx ty
          let pc ← x.cl.type ctx.length k
          let ps ← readSkel x n ty
          let (bt, bc) ← readTerm x caseOf n (⟨.fvar ctx.length k, pc⟩ :: ctx) b
          let fvs ← freeVars n 1 bt
          pure (.lam { mode := m.input, cls := pc, skel := ps, noLeaf := x.noLeafType ty } m.result bc
            fvs.toArray bt, c)
        | .letE m ty v b => do
          let k ← x.toK ctx ty
          let dc ← x.cl.type ctx.length k
          skip x.rm n ty
          let (vt, _) ← readTerm x caseOf n ctx v
          let (bt, bc) ← readTerm x caseOf n (⟨.fvar ctx.length k, dc⟩ :: ctx) b
          pure (.letE m dc vt bt, bc)
        | .share i => do
          let some ent := x.c.sharing[i]? | throw "sharing reference out of range"
          enterShare x.rm i (readTerm x caseOf n ctx ent)) : RM (Term × Cls)).run cs = .ok ((t, tc), cs') →
        TermModesDefault t ∧ cs'.nodes = cs.nodes := by
      intro h
      obtain ⟨k0, cs1, hk0, h⟩ := RM_bind_elim h
      obtain ⟨_, hcs1⟩ := RM_lift_elim hk0; subst cs1
      obtain ⟨c0, cs2, hc0, h⟩ := RM_bind_elim h
      obtain ⟨_, hcs2⟩ := RM_lift_elim hc0; subst cs2
      by_cases hirr : (c0 == .irr) = true
      · simp only [hirr, ↓reduceIte] at h
        obtain ⟨_, cs3, hsk, h⟩ := RM_bind_elim h
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, _⟩, rfl⟩ := h
        exact ⟨.irr, cursor_allDefault_skip n e hsk⟩
      · simp only [hirr, Bool.false_eq_true, ↓reduceIte] at h
        cases v with
        | var _ | sort | all _ _ =>
          obtain ⟨_, cs3, hsk, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, rfl⟩ := h
          exact ⟨.irr, cursor_allDefault_skip n e hsk⟩
        | ref i =>
          obtain ⟨rf, cs3, hrf, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs3⟩ := RM_lift_elim hrf; subst cs3
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, rfl⟩ := h
          exact ⟨.const, rfl⟩
        | recur i =>
          cases hr : x.recur i with
          | none => simp [hr, RM_run_throw] at h
          | some rf =>
            simp only [hr, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, _⟩, rfl⟩ := h
            exact ⟨.const, rfl⟩
        | nat i =>
          obtain ⟨bl, cs3, hbl, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs3⟩ := RM_lift_elim hbl; subst cs3
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, rfl⟩ := h
          exact ⟨.natLit, rfl⟩
        | str i =>
          obtain ⟨bl, cs3, hbl, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs3⟩ := RM_lift_elim hbl; subst cs3
          cases hs : String.fromUTF8? bl with
          | none => simp [hs, RM_run_throw] at h
          | some str =>
            simp only [hs, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨⟨rfl, _⟩, rfl⟩ := h
            exact ⟨.strLit, rfl⟩
        | prj ty f val =>
          have hvalDef : ExprLetsDefault val := by
            cases e <;> simp [view, Ex_pure] at hv
            obtain ⟨_, _, rfl⟩ := hv; exact he
          obtain ⟨s0, cs3, hs0, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs3⟩ := RM_lift_elim hs0; subst cs3
          obtain ⟨⟨vt, vc⟩, cs4, hvt, h⟩ := RM_bind_elim h
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, rfl⟩ := h
          obtain ⟨hD, hnd⟩ := ih hvalDef hcs hvt
          exact ⟨.proj hD, hnd⟩
        | app _ _ =>
          obtain ⟨⟨hd, args⟩, cs3, hspL, h⟩ := RM_bind_elim h
          obtain ⟨hsp, hcs3⟩ := RM_lift_elim hspL; subst cs3
          obtain ⟨hhdDef, hargsDef⟩ := ixSpine_letsDefault he hsp
          obtain ⟨⟨ht, hc⟩, cs4, hht, h⟩ := RM_bind_elim h
          obtain ⟨hhtD, hnd4⟩ := ih hhdDef hcs hht
          have hcs4 : ∀ nd ∈ cs4.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
            rw [hnd4]; exact hcs
          have hfor : ∀ (l : List Ixon.Expr) (acc out : Array Term) (c0 c1 : Cursor),
              (∀ a ∈ l, ExprLetsDefault a) →
              (∀ a ∈ acc.toList, TermModesDefault a) →
              (∀ nd ∈ c0.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
              (forIn (m := RM) l acc fun a ats => do
                pure (ForInStep.yield (ats.push (← readTerm x caseOf n ctx a).1))).run c0 = .ok (out, c1) →
              (∀ a ∈ out.toList, TermModesDefault a) ∧ c1.nodes = c0.nodes := by
            intro l
            induction l with
            | nil =>
              intro acc out c0 c1 _ hacc _ hf
              simp only [List.forIn_nil, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf; exact ⟨hacc, rfl⟩
            | cons a rest ihr =>
              intro acc out c0 c1 hl hacc hc0 hf
              rw [List.forIn_cons] at hf
              obtain ⟨stepV, cMid, hstep, hf⟩ := RM_bind_elim hf
              obtain ⟨⟨at0, ac0⟩, cMid2, hat0, hstep⟩ := RM_bind_elim hstep
              simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hstep
              obtain ⟨rfl, rfl⟩ := hstep
              dsimp only at hf
              obtain ⟨hatD, hndA⟩ := ih (hl a (List.mem_cons_self ..)) hc0 hat0
              have hcMid : ∀ nd ∈ cMid2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
                rw [hndA]; exact hc0
              obtain ⟨houtD, hndR⟩ := ihr (acc.push at0) out cMid2 c1
                (fun y hy => hl y (List.mem_cons_of_mem _ hy))
                (fun y hy => by
                  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
                  rcases hy with hy0 | rfl
                  · exact hacc y hy0
                  · exact hatD) hcMid hf
              exact ⟨houtD, hndR.trans hndA⟩
          dsimp only at h
          rw [← Array.forIn_toList] at h
          obtain ⟨ats, cs5, hats, h⟩ := RM_bind_elim h
          obtain ⟨hatsD, hnd5⟩ := hfor args.toList #[] ats cs4 cs5 hargsDef (by simp) hcs4 hats
          have hndEnd : cs5.nodes = cs.nodes := hnd5.trans hnd4
          cases hspT : termSpine ht with
          | mk h' pre =>
            obtain ⟨hh'D, hpreD⟩ := (termSpine_props hspT).2.2 hhtD
            have hallD : ∀ a ∈ (pre ++ ats).toList, TermModesDefault a := by
              intro a ha
              rw [Array.toList_append, List.mem_append] at ha
              rcases ha with hp | hb
              · exact hpreD a hp
              · exact hatsD a hb
            have hgetD : ∀ idx : Nat, TermModesDefault ((pre ++ ats)[idx]?.getD .irr) := by
              intro idx
              cases hg : (pre ++ ats)[idx]? with
              | none => exact .irr
              | some a => exact hallD a (array_mem_toList_of_getElem?' hg)
            have hfoldD : TermModesDefault (foldApp h' (pre ++ ats) c0) :=
              foldApp_props.2.2 hh'D hallD
            simp only [hspT] at h
            cases h' with
            | const r rc =>
              cases hco : caseOf r with
              | none =>
                simp only [hco, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨⟨rfl, _⟩, rfl⟩ := h; exact ⟨hfoldD, hndEnd⟩
              | some k =>
                simp only [hco] at h
                split at h
                · simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨⟨rfl, _⟩, rfl⟩ := h
                  refine ⟨.case (hgetD k.major) ?_ ?_, hndEnd⟩
                  · intro a ha
                    rw [Array.toList_map, List.mem_map] at ha
                    obtain ⟨ca, _, rfl⟩ := ha
                    exact hgetD ca.alt
                  · intro a ha
                    exact hallD a (array_extract_mem ha)
                · simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨⟨rfl, _⟩, rfl⟩ := h; exact ⟨hfoldD, hndEnd⟩
            | _ =>
              simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨⟨rfl, _⟩, rfl⟩ := h; exact ⟨hfoldD, hndEnd⟩
        | lam ty b =>
          have hbDef : ExprLetsDefault b := by
            cases e <;> simp [view, Ex_pure] at hv
            obtain ⟨_, rfl⟩ := hv; exact he.2
          obtain ⟨m, cs3, hm, h⟩ := RM_bind_elim h
          obtain ⟨hmDef, hnd3⟩ := cursor_allDefault_nextBinder hcs hm
          have hcs3 : ∀ nd ∈ cs3.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
            rw [hnd3]; exact hcs
          obtain ⟨k, cs4, hk, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs4⟩ := RM_lift_elim hk; subst cs4
          obtain ⟨pc, cs5, hpc, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs5⟩ := RM_lift_elim hpc; subst cs5
          obtain ⟨ps, cs6, hps, h⟩ := RM_bind_elim h
          obtain ⟨_, hnd6⟩ := readSkel_isDefault_of_blocksDefault hbd n ty hcs3 hps
          have hcs6 : ∀ nd ∈ cs6.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
            rw [hnd6]; exact hcs3
          obtain ⟨⟨bt, bc⟩, cs7, hbt, h⟩ := RM_bind_elim h
          obtain ⟨hbD, hnd7⟩ := ih hbDef hcs6 hbt
          obtain ⟨fvs, cs8, hfvs, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs8⟩ := RM_lift_elim hfvs; subst cs8
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, rfl⟩ := h
          have hmEq : m = {} := by simpa [AllMode.isDefault] using hmDef
          exact ⟨.lam (by simp [hmEq]) (by simp [hmEq]) hbD, hnd7.trans (hnd6.trans hnd3)⟩
        | letE m ty val b =>
          have hletDef : m = .value .many ∧ ExprLetsDefault val ∧ ExprLetsDefault b := by
            cases e <;> simp [view, Ex_pure] at hv
            obtain ⟨rfl, _, rfl, rfl⟩ := hv; exact ⟨he.1, he.2.2.1, he.2.2.2⟩
          obtain ⟨rfl, hvalDef, hbDef⟩ := hletDef
          obtain ⟨k, cs3, hk, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs3⟩ := RM_lift_elim hk; subst cs3
          obtain ⟨dc, cs4, hdc, h⟩ := RM_bind_elim h
          obtain ⟨_, hcs4⟩ := RM_lift_elim hdc; subst cs4
          obtain ⟨_, cs5, hsk, h⟩ := RM_bind_elim h
          have hnd5 : cs5.nodes = cs.nodes := cursor_allDefault_skip n ty hsk
          have hcs5 : ∀ nd ∈ cs5.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
            rw [hnd5]; exact hcs
          obtain ⟨⟨vt, _⟩, cs6, hvt, h⟩ := RM_bind_elim h
          obtain ⟨hvD, hnd6⟩ := ih hvalDef hcs5 hvt
          have hcs6 : ∀ nd ∈ cs6.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
            rw [hnd6]; exact hcs5
          obtain ⟨⟨bt, _⟩, cs7, hbt, h⟩ := RM_bind_elim h
          obtain ⟨hbD, hnd7⟩ := ih hbDef hcs6 hbt
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, _⟩, rfl⟩ := h
          exact ⟨.letE hvD hbD, hnd7.trans (hnd6.trans hnd5)⟩
        | share i =>
          cases hsh : x.c.sharing[i]? with
          | none => simp [hsh, RM_run_throw] at h
          | some ent =>
            simp only [hsh] at h
            obtain ⟨key, cs₁, hinner, hnodes⟩ := enterShare_ok h
            have hentDef := hshDef ent (array_mem_toList_of_getElem?' hsh)
            obtain ⟨htD, _⟩ := ih hentDef (hbd.block? key) hinner
            exact ⟨htD, hnodes⟩
    cases v with
    | var i =>
      cases hget : ctx[i]? with
      | none => simp [hget, RM_run_throw] at h
      | some l =>
        simp only [hget, RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, _⟩, rfl⟩ := h
        cases l.cls == .irr <;> exact ⟨by constructor, rfl⟩
    | _ => exact hnonVar h

/-! ### Default interfaces & structural properties of `readProg` / `readDef` -/

theorem arrowChain_isDefault :
    ∀ (l : List (AllMode × Skel)) (cod : Skel),
      (∀ p ∈ l, p.1.isDefault = true ∧ p.2.isDefault = true) →
      cod.isDefault = true →
      (arrowChain l cod).isDefault = true := by
  intro l
  induction l with
  | nil => intro cod _ hc; exact hc
  | cons p rest ih =>
    intro cod hl hc
    obtain ⟨hm, hsk⟩ := hl p (List.mem_cons_self ..)
    have hmEq : p.1 = {} := by simpa [AllMode.isDefault] using hm
    simp only [arrowChain, Skel.isDefault, hmEq, hsk, ih cod (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hc]
    rfl

theorem openParams_isDefault {x : RCx} {tele : List (AllMode × Skel × Ixon.Expr)}
    {ctx : List Local} {ps : Array Param}
    (h : openParams x tele = .ok (ctx, ps))
    (hdef : ∀ tb ∈ tele, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) :
    ∀ p ∈ ps.toList, p.mode = .many ∧ p.skel.isDefault = true := by
  have hloop : ∀ (l : List (AllMode × Skel × Ixon.Expr))
      (accCtx : List Local) (accPs : Array Param) (outCtx : List Local) (outPs : Array Param),
      (∀ tb ∈ l, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) →
      (∀ p ∈ accPs.toList, p.mode = .many ∧ p.skel.isDefault = true) →
      (forIn (m := Except String) l (accCtx, accPs) fun (m, sk, dom) (ctx, ps) => do
        let k ← x.toK ctx dom
        let pc ← x.cl.type ctx.length k
        let ps := ps.push { mode := m.input, cls := pc, skel := sk, noLeaf := x.noLeafType dom }
        let ctx := ⟨.fvar ctx.length k, pc⟩ :: ctx
        pure (ForInStep.yield (ctx, ps))) = .ok (outCtx, outPs) →
      ∀ p ∈ outPs.toList, p.mode = .many ∧ p.skel.isDefault = true := by
    intro l
    induction l with
    | nil =>
      intro accCtx accPs outCtx outPs _ hacc hf
      simp only [List.forIn_nil, Ex_pure, Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf; exact hacc
    | cons hd rest ih =>
      obtain ⟨m0, sk0, dom0⟩ := hd
      intro accCtx accPs outCtx outPs hl hacc hf
      rw [List.forIn_cons] at hf
      obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
      obtain ⟨k, _, hstep⟩ := Ex_bind_elim hstep
      obtain ⟨pc, _, hstep⟩ := Ex_bind_elim hstep
      simp only [Ex_pure, Except.ok.injEq] at hstep
      subst hstep; dsimp only at hf
      obtain ⟨hm0, hsk0⟩ := hl (m0, sk0, dom0) (List.mem_cons_self ..)
      have hmEq : m0 = {} := by simpa [AllMode.isDefault] using hm0
      apply ih _ _ outCtx outPs (fun tb htb => hl tb (List.mem_cons_of_mem _ htb)) _ hf
      intro p hp
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp0 | rfl
      · exact hacc p hp0
      · exact ⟨by simp [hmEq], hsk0⟩
  unfold openParams at h
  obtain ⟨res, hf, h⟩ := Ex_bind_elim h
  simp only [Ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hloop tele [] #[] res.1 res.2 hdef (by simp) hf

theorem readTele_body_props {β : Type} {x : RCx} {lam : Bool}
    {k : List TeleBinder → Ixon.Expr → RM β} {P : List TeleBinder → Ixon.Expr → β → Prop}
    (hbd : BlocksDefault x.rm) (hshDef : ∀ ent ∈ x.c.sharing.toList, ExprLetsDefault ent)
    (hk : ∀ bs bd cs cs' v,
      (∀ tb ∈ bs, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) →
      ExprLetsDefault bd →
      (∀ nd ∈ cs.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
      (k bs bd).run cs = .ok (v, cs') → P bs bd v) :
    ∀ {n : Nat} {acc : List TeleBinder} {e : Ixon.Expr} {cs cs' : Cursor} {v : β},
      (∀ tb ∈ acc, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) →
      ExprLetsDefault e →
      (∀ nd ∈ cs.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
      (readTele x lam k n acc e).run cs = .ok (v, cs') →
      ∃ bs bd, P bs bd v := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ h; simp [readTele, RM_run_throw] at h
  | succ n ih =>
    intro acc e cs cs' v hacc he hcs h
    unfold readTele at h
    obtain ⟨vv, cs0, hvl, h⟩ := RM_bind_elim h
    obtain ⟨hv, hcs0⟩ := RM_lift_elim hvl; subst cs0
    have hstop : (k acc.reverse e).run cs = .ok (v, cs') → ∃ bs bd, P bs bd v := fun hs =>
      ⟨acc.reverse, e, hk acc.reverse e cs cs' v
        (fun tb htb => hacc tb (List.mem_reverse.mp htb)) he hcs hs⟩
    cases vv with
    | all ty b =>
      cases lam with
      | true => simp only [↓reduceIte] at h; exact hstop h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hbDef : ExprLetsDefault b := by
          cases e <;> simp [view, Ex_pure] at hv
          obtain ⟨_, rfl⟩ := hv; exact he.2
        obtain ⟨m, cs1, hm, h⟩ := RM_bind_elim h
        obtain ⟨hmDef, hnd1⟩ := cursor_allDefault_nextBinder hcs hm
        have hcs1 : ∀ nd ∈ cs1.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
          rw [hnd1]; exact hcs
        obtain ⟨d, cs2, hd, h⟩ := RM_bind_elim h
        obtain ⟨hdDef, hnd2⟩ := readSkel_isDefault_of_blocksDefault hbd n ty hcs1 hd
        have hcs2 : ∀ nd ∈ cs2.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
          rw [hnd2]; exact hcs1
        exact ih (fun tb htb => by
          rcases List.mem_cons.mp htb with rfl | hrest
          · exact ⟨hmDef, hdDef⟩
          · exact hacc tb hrest) hbDef hcs2 h
    | lam ty b =>
      cases lam with
      | true =>
        simp only [↓reduceIte] at h
        have hbDef : ExprLetsDefault b := by
          cases e <;> simp [view, Ex_pure] at hv
          obtain ⟨_, rfl⟩ := hv; exact he.2
        obtain ⟨m, cs1, hm, h⟩ := RM_bind_elim h
        obtain ⟨hmDef, hnd1⟩ := cursor_allDefault_nextBinder hcs hm
        have hcs1 : ∀ nd ∈ cs1.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
          rw [hnd1]; exact hcs
        obtain ⟨d, cs2, hd, h⟩ := RM_bind_elim h
        obtain ⟨hdDef, hnd2⟩ := readSkel_isDefault_of_blocksDefault hbd n ty hcs1 hd
        have hcs2 : ∀ nd ∈ cs2.nodes.toList, ∀ m', nd = .binder m' → m'.isDefault = true := by
          rw [hnd2]; exact hcs1
        exact ih (fun tb htb => by
          rcases List.mem_cons.mp htb with rfl | hrest
          · exact ⟨hmDef, hdDef⟩
          · exact hacc tb hrest) hbDef hcs2 h
      | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact hstop h
    | share i =>
      cases hsh : x.c.sharing[i]? with
      | none => simp only [hsh] at h; exact hstop h
      | some ent =>
        simp only [hsh] at h
        cases hc : continuesTele x.c lam ent with
        | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact hstop h
        | true =>
          simp only [hc, ↓reduceIte] at h
          obtain ⟨key, cs₁, hinner, _⟩ := enterShare_ok h
          exact ih hacc (hshDef ent (array_mem_toList_of_getElem?' hsh)) (hbd.block? key) hinner
    | _ => exact hstop h

theorem readTele_struct_k {β : Type} {x : RCx} {lam : Bool}
    {k : List TeleBinder → Ixon.Expr → RM β} {P : β → Prop}
    (hk : ∀ bs bd cs cs' v, (k bs bd).run cs = .ok (v, cs') → P v) :
    ∀ {n : Nat} {acc : List TeleBinder} {e : Ixon.Expr} {cs cs' : Cursor} {v : β},
      (readTele x lam k n acc e).run cs = .ok (v, cs') → P v := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; simp [readTele, RM_run_throw] at h
  | succ n ih =>
    intro acc e cs cs' v h
    unfold readTele at h
    obtain ⟨vv, cs0, _, h⟩ := RM_bind_elim h
    cases vv with
    | all ty b =>
      cases lam with
      | true => simp only [↓reduceIte] at h; exact hk _ _ _ _ _ h
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨_, _, _, h⟩ := RM_bind_elim h
        obtain ⟨_, _, _, h⟩ := RM_bind_elim h
        exact ih h
    | lam ty b =>
      cases lam with
      | true =>
        simp only [↓reduceIte] at h
        obtain ⟨_, _, _, h⟩ := RM_bind_elim h
        obtain ⟨_, _, _, h⟩ := RM_bind_elim h
        exact ih h
      | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact hk _ _ _ _ _ h
    | share i =>
      cases hsh : x.c.sharing[i]? with
      | none => simp only [hsh] at h; exact hk _ _ _ _ _ h
      | some ent =>
        simp only [hsh] at h
        cases hc : continuesTele x.c lam ent with
        | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at h; exact hk _ _ _ _ _ h
        | true =>
          simp only [hc, ↓reduceIte] at h
          obtain ⟨_, _, hinner, _⟩ := enterShare_ok h
          exact ih hinner
    | _ => exact hk _ _ _ _ _ h

theorem readForalls_isDefault {x : RCx} {fuel : Nat} {ty : Ixon.Expr} {key : BlockKey}
    {alls : List TeleBinder} {cod : Ixon.Expr} {codSkel : Skel} {cs : Cursor}
    (hbd : BlocksDefault x.rm)
    (h : (inBlock x.rm key (readForalls x fuel ty (readSkel x fuel))).run {} = .ok ((alls, cod, codSkel), cs)) :
    (∀ tb ∈ alls, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) ∧ codSkel.isDefault = true := by
  obtain ⟨cs₁, hinner, _⟩ := inBlock_nodes_preserved h
  unfold readForalls at hinner
  have hall := readTele_isDefault_of_blocksDefault hbd (by simp) (hbd.block? key) hinner
  have hcod : codSkel.isDefault = true := by
    have haux : ∀ {n : Nat} {acc : List TeleBinder} {e : Ixon.Expr} {c0 c1 : Cursor}
        {ls : List TeleBinder} {bd : Ixon.Expr} {sk : Skel},
        (∀ nd ∈ c0.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
        (readTele x false (fun bs cd => do pure (bs, cd, ← readSkel x fuel cd)) n acc e).run c0 =
          .ok ((ls, bd, sk), c1) →
        sk.isDefault = true := by
      intro n
      induction n with
      | zero => intro _ _ _ _ _ _ _ _ hr; simp [readTele, RM_run_throw] at hr
      | succ n ihr =>
        intro acc e c0 c1 ls bd sk hc0 hr
        unfold readTele at hr
        obtain ⟨vv, c0', hvl, hr⟩ := RM_bind_elim hr
        obtain ⟨_, hc0Eq⟩ := RM_lift_elim hvl; subst c0'
        have hstop : ∀ {e0}, (do pure (acc.reverse, e0, ← readSkel x fuel e0)).run c0 = .ok ((ls, bd, sk), c1) →
            sk.isDefault = true := by
          intro e0 hs
          obtain ⟨sk0, c2, hsk, hs⟩ := RM_bind_elim hs
          simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hs
          obtain ⟨⟨_, _, rfl⟩, _⟩ := hs
          exact (readSkel_isDefault_of_blocksDefault hbd fuel e0 hc0 hsk).1
        cases vv with
        | all ty' b' =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hr
          obtain ⟨_, c2, hm, hr⟩ := RM_bind_elim hr
          have hnd2 := nextBinder_nodes hm
          have hc2 : ∀ nd ∈ c2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
            rw [hnd2]; exact hc0
          obtain ⟨_, c3, hsk, hr⟩ := RM_bind_elim hr
          have hnd3 := (readSkel_isDefault_of_blocksDefault hbd n ty' hc2 hsk).2
          have hc3 : ∀ nd ∈ c3.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
            rw [hnd3]; exact hc2
          exact ihr hc3 hr
        | lam _ _ => simp only [Bool.false_eq_true, ↓reduceIte] at hr; exact hstop hr
        | share i =>
          cases hsh : x.c.sharing[i]? with
          | none => simp only [hsh] at hr; exact hstop hr
          | some ent =>
            simp only [hsh] at hr
            cases hc : continuesTele x.c false ent with
            | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr; exact hstop hr
            | true =>
              simp only [hc, ↓reduceIte] at hr
              obtain ⟨key', _, hinner', _⟩ := enterShare_ok hr
              exact ihr (hbd.block? key') hinner'
        | _ => exact hstop hr
    exact haux (hbd.block? key) hinner
  exact ⟨hall, hcod⟩

theorem ifaceAt_isDefault {x : RCx} {ty : Ixon.Expr} {key : BlockKey}
    {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel}
    (hbd : BlocksDefault x.rm)
    (hi : ifaceAt x ty key = .ok (ps, res, rc, rs)) :
    (∀ p ∈ ps.toList, p.mode = .many ∧ p.skel.isDefault = true) ∧
    res = .shared ∧ rs.isDefault = true := by
  unfold ifaceAt at hi
  obtain ⟨⟨⟨ps1, res1, rc1, rs1⟩, cs1⟩, hri, hEq⟩ := Ex_map_elim hi
  simp only [Prod.mk.injEq] at hEq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
  obtain ⟨_, hinner, _⟩ := inBlock_nodes_preserved hri
  unfold readIface at hinner
  obtain ⟨⟨alls, cod, codSkel⟩, cs2, hrf, hinner⟩ := RM_bind_elim hinner
  obtain ⟨⟨ctx, ps'⟩, cs3, hopL, hinner⟩ := RM_bind_elim hinner
  have hop : openParams x alls = .ok (ctx, ps') := by
    cases h1 : openParams x alls with
    | error _ => simp [h1] at hopL
    | ok p => simp only [h1, RM_run_lift, Ex_map_ok, Except.ok.injEq, Prod.mk.injEq] at hopL; rw [← hopL.1]
  obtain ⟨_, cs4, _, hinner⟩ := RM_bind_elim hinner
  obtain ⟨kv, cs5, _, hinner⟩ := RM_bind_elim hinner
  obtain ⟨rc', cs6, _, hinner⟩ := RM_bind_elim hinner
  simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hinner
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, _⟩ := hinner
  have hall := readTele_isDefault_of_blocksDefault hbd (by simp) (hbd.block? key) hrf
  have hcod : codSkel.isDefault = true := by
    have hwrap : (inBlock x.rm key (readForalls x readFuel ty (readSkel x readFuel))).run {} =
        .ok ((alls, cod, codSkel), {}) ∨ codSkel.isDefault = true := by
      -- directly use `readForalls_isDefault` via the same inner run? Just use `haux`!
      right
      have haux : ∀ {n : Nat} {acc : List TeleBinder} {e : Ixon.Expr} {c0 c1 : Cursor}
          {ls : List TeleBinder} {bd : Ixon.Expr} {sk : Skel},
          (∀ nd ∈ c0.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
          (readTele x false (fun bs cd => do pure (bs, cd, ← readSkel x readFuel cd)) n acc e).run c0 =
            .ok ((ls, bd, sk), c1) →
          sk.isDefault = true := by
        intro n
        induction n with
        | zero => intro _ _ _ _ _ _ _ _ hr; simp [readTele, RM_run_throw] at hr
        | succ n ihr =>
          intro acc e c0 c1 ls bd sk hc0 hr
          unfold readTele at hr
          obtain ⟨vv, c0', hvl, hr⟩ := RM_bind_elim hr
          obtain ⟨_, hc0Eq⟩ := RM_lift_elim hvl; subst c0'
          have hstop : ∀ {e0}, (do pure (acc.reverse, e0, ← readSkel x readFuel e0)).run c0 = .ok ((ls, bd, sk), c1) →
              sk.isDefault = true := by
            intro e0 hs
            obtain ⟨sk0, c2, hsk, hs⟩ := RM_bind_elim hs
            simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hs
            obtain ⟨⟨_, _, rfl⟩, _⟩ := hs
            exact (readSkel_isDefault_of_blocksDefault hbd readFuel e0 hc0 hsk).1
          cases vv with
          | all ty' b' =>
            simp only [Bool.false_eq_true, ↓reduceIte] at hr
            obtain ⟨_, c2, hm, hr⟩ := RM_bind_elim hr
            have hc2 : ∀ nd ∈ c2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
              rw [nextBinder_nodes hm]; exact hc0
            obtain ⟨_, c3, hsk, hr⟩ := RM_bind_elim hr
            have hc3 : ∀ nd ∈ c3.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
              rw [(readSkel_isDefault_of_blocksDefault hbd n ty' hc2 hsk).2]; exact hc2
            exact ihr hc3 hr
          | lam _ _ => simp only [Bool.false_eq_true, ↓reduceIte] at hr; exact hstop hr
          | share i =>
            cases hsh : x.c.sharing[i]? with
            | none => simp only [hsh] at hr; exact hstop hr
            | some ent =>
              simp only [hsh] at hr
              cases hc : continuesTele x.c false ent with
              | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr; exact hstop hr
              | true =>
                simp only [hc, ↓reduceIte] at hr
                obtain ⟨key', _, hinner', _⟩ := enterShare_ok hr
                exact ihr (hbd.block? key') hinner'
          | _ => exact hstop hr
      exact haux (hbd.block? key) hrf
    rcases hwrap with h1 | h2
    · exact (readForalls_isDefault hbd h1).2
    · exact h2
  have hres : (Option.map (fun x => x.1.result) alls.getLast?).getD ResultMode.shared = .shared := by
    cases hgl : alls.getLast? with
    | none => rfl
    | some tb =>
      have hmem : tb ∈ alls := List.mem_of_getLast? hgl
      have hmEq : tb.1 = {} := by simpa [AllMode.isDefault] using (hall tb hmem).1
      simp [hmEq]
  exact ⟨openParams_isDefault hop hall, hres, hcod⟩

theorem fieldModesDefault_elim {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    {i ci f : Nat} {ind : Ixon.Inductive} {ctor : Ixon.Constructor}
    (hfm : fieldModesDefault c = true) (hinfo : c.info = .muts ms)
    (hmi : ms[i]? = some (.indc ind)) (hci : ind.ctors[ci]? = some ctor)
    (hf : f < ctor.fields.toNat) :
    fieldMode c i ci f = .inherited := by
  unfold fieldModesDefault at hfm
  rw [hinfo] at hfm
  have h1 := Array.all_eq_true.mp hfm
  have hiLt : i < ms.size := (Array.getElem?_eq_some_iff.mp hmi).1
  have hiZ : i < ms.zipIdx.size := by simp [hiLt]
  have h1i := h1 i hiZ
  have hzipI : ms.zipIdx[i] = (ms[i], i) := by simp
  rw [hzipI] at h1i
  have hmiEq : ms[i] = .indc ind := by
    have := Array.getElem?_eq_getElem hiLt
    rw [hmi] at this; exact (Option.some.inj this).symm
  rw [hmiEq] at h1i
  dsimp only at h1i
  have h2 := Array.all_eq_true.mp h1i
  have hciLt : ci < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hci).1
  have hciZ : ci < ind.ctors.zipIdx.size := by simp [hciLt]
  have h2c := h2 ci hciZ
  have hzipC : ind.ctors.zipIdx[ci] = (ind.ctors[ci], ci) := by simp
  rw [hzipC] at h2c
  have hciEq : ind.ctors[ci] = ctor := by
    have := Array.getElem?_eq_getElem hciLt
    rw [hci] at this; exact (Option.some.inj this).symm
  rw [hciEq] at h2c
  dsimp only at h2c
  have h3 := List.all_eq_true.mp h2c f (List.mem_range.mpr hf)
  exact beq_iff_eq.mp (by simpa [fieldMode, hinfo] using h3)

theorem readCtorFields_isDefault {x : RCx} {ms : Array Ixon.MutConst} {i ci : Nat}
    {indV : Ixon.Inductive} {ctor : Ixon.Constructor} {key : BlockKey} {fs : Array Field}
    (hbd : BlocksDefault x.rm) (hfm : fieldModesDefault x.c = true)
    (hinfo : x.c.info = .muts ms) (hmi : ms[i]? = some (.indc indV)) (hci : indV.ctors[ci]? = some ctor)
    (hrcf : readCtorFields x i ci indV.params.toNat ctor.fields.toNat ctor.typ key = .ok fs) :
    ∀ f ∈ fs.toList, f.mode = .many ∧ f.fmode = .inherited := by
  unfold readCtorFields at hrcf
  obtain ⟨⟨⟨alls, cod, codSkel⟩, cs⟩, hrf, hrcf⟩ := Ex_bind_elim hrcf
  dsimp only at hrcf
  split at hrcf
  · rename_i hlen
    have hlenEq : alls.length = indV.params.toNat + ctor.fields.toNat := beq_iff_eq.mp (by simpa using hlen)
    have hall := (readForalls_isDefault hbd hrf).1
    have hloop : ∀ (l : List ((AllMode × Skel × Ixon.Expr) × Nat))
        (accCtx : List Local) (accOut : Array Field) (outCtx : List Local) (outFs : Array Field),
        (∀ p ∈ l, p.1.1.isDefault = true ∧ p.2 < indV.params.toNat + ctor.fields.toNat) →
        (∀ f ∈ accOut.toList, f.mode = .many ∧ f.fmode = .inherited) →
        (forIn (m := Except String) l (accCtx, accOut) fun ((m, _, dom), idx) (ctx, out) => do
          let kv ← x.toK ctx dom
          let pc ← x.cl.type ctx.length kv
          let ctx := ⟨.fvar ctx.length kv, pc⟩ :: ctx
          unless m.result == .shared do throw "a constructor binder with a result mode"
          if idx < indV.params.toNat then
            unless m.input == .many do throw "a moded constructor parameter"
            pure (ForInStep.yield (ctx, out))
          else
            unless m.input == .many || m.input == .erased do
              throw "a constructor field binder with a mode other than erased"
            pure (ForInStep.yield (ctx, out.push { mode := m.input, fmode := fieldMode x.c i ci (idx - indV.params.toNat), cls := pc }))) =
          .ok (outCtx, outFs) →
        ∀ f ∈ outFs.toList, f.mode = .many ∧ f.fmode = .inherited := by
      intro l
      induction l with
      | nil =>
        intro _ accOut _ outFs _ hacc hf
        simp only [List.forIn_nil, Ex_pure, Except.ok.injEq, Prod.mk.injEq] at hf
        obtain ⟨_, rfl⟩ := hf; exact hacc
      | cons hd rest ih =>
        obtain ⟨⟨m0, sk0, dom0⟩, idx0⟩ := hd
        intro accCtx accOut outCtx outFs hl hacc hf
        rw [List.forIn_cons] at hf
        obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
        obtain ⟨kv, _, hstep⟩ := Ex_bind_elim hstep
        obtain ⟨pc, _, hstep⟩ := Ex_bind_elim hstep
        dsimp only at hstep
        obtain ⟨hm0, hidxLt⟩ := hl ((m0, sk0, dom0), idx0) (List.mem_cons_self ..)
        have hmEq : m0 = {} := by simpa [AllMode.isDefault] using hm0
        split at hstep
        · by_cases hlt : idx0 < indV.params.toNat
          · simp only [hlt, ↓reduceIte] at hstep
            split at hstep
            · simp only [Ex_pure, Except.ok.injEq] at hstep
              subst hstep; dsimp only at hf
              exact ih _ accOut outCtx outFs (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hacc hf
            · simp only [Ex_throw] at hstep; cases hstep
          · simp only [hlt, ↓reduceIte] at hstep
            split at hstep
            · simp only [Ex_pure, Except.ok.injEq] at hstep
              subst hstep; dsimp only at hf
              apply ih _ _ outCtx outFs (fun p hp => hl p (List.mem_cons_of_mem _ hp)) _ hf
              intro f hf'
              rw [Array.toList_push, List.mem_append, List.mem_singleton] at hf'
              rcases hf' with h0 | rfl
              · exact hacc f h0
              · exact ⟨by simp [hmEq], fieldModesDefault_elim hfm hinfo hmi hci (by omega)⟩
            · simp only [Ex_throw] at hstep; cases hstep
        · simp only [Ex_throw, Ex_bind_err] at hstep; cases hstep
    obtain ⟨res, hfl, hrcf⟩ := Ex_bind_elim hrcf
    simp only [Ex_pure, Except.ok.injEq] at hrcf
    subst hrcf
    apply hloop alls.zipIdx [] #[] res.1 res.2 _ (by simp) hfl
    intro p hp
    have hg := list_getElem?_of_mem_zipIdx hp
    have hlt : p.2 < alls.length := (List.getElem?_eq_some_iff.mp hg).1
    exact ⟨(hall p.1 (list_mem_of_mem_zipIdx' hp)).1, by omega⟩
  · simp [Ex_throw] at hrcf

theorem binderRoots_mem_defn {c : Ixon.Constant} {dd : Ixon.Definition} {i : Nat}
    (hsrc : c.info = .defn dd ∨ ∃ ms, c.info = .muts ms ∧ ms[i]? = some (.defn dd)) :
    dd.value ∈ (binderRoots c.info).toList := by
  rcases hsrc with h | ⟨ms, h, hmi⟩
  · simp [binderRoots, h]
  · unfold binderRoots
    rw [h]; dsimp only
    rw [← Array.foldl_toList]
    have hmem : Ixon.MutConst.defn dd ∈ ms.toList := array_mem_toList_of_getElem?' hmi
    have aux : ∀ (l : List Ixon.MutConst) (acc : Array Ixon.Expr),
        (dd.value ∈ acc.toList ∨ Ixon.MutConst.defn dd ∈ l) →
        dd.value ∈ (l.foldl (fun acc m => acc ++ match m with
          | .defn d => #[d.typ, d.value]
          | .indc i => #[i.typ] ++ i.ctors.map (·.typ)
          | .recr r => #[r.typ] ++ r.rules.map (·.rhs)) acc).toList := by
      intro l
      induction l with
      | nil =>
        intro acc hor
        rcases hor with h0 | h1
        · exact h0
        · cases h1
      | cons m rest ih =>
        intro acc hor
        simp only [List.foldl_cons]
        apply ih
        rcases hor with h0 | h1
        · left; rw [Array.toList_append, List.mem_append]; exact Or.inl h0
        · rcases List.mem_cons.mp h1 with rfl | hrest
          · left; rw [Array.toList_append, List.mem_append]; right; simp
          · exact Or.inr hrest
    exact aux ms.toList #[] (Or.inr hmem)

/-- Structural and default-interface properties of `readEquation` entries. -/
theorem readEquation_props {rd : Reading} {cl : Classifier} {x : RCx}
    {eqRef andRef : Option Ref} {targets : Array (Ref × RunDef)} :
    ∀ {n : Nat} {ctx : List Local} {e : Ixon.Expr} {cs cs' : Cursor} {entries : Array (Ref × RunDef)},
      (readEquation rd cl x eqRef andRef targets n ctx e).run cs = .ok (entries, cs') →
      ∀ p ∈ entries.toList,
        (∀ ps res rc rs rhs, p.2 = .body ps res rc rs rhs →
          LamsClosed rhs ∧ CaseFieldsDistinct rhs) ∧
        (∀ c, rd.s.store p.1.block = some c → recordDefault c = .ok true → DefaultIface p.2) := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ h; simp [readEquation, RM_run_throw] at h
  | succ n ih =>
    intro ctx e cs cs' entries h
    unfold readEquation at h
    obtain ⟨vv, cs0, _, h⟩ := RM_bind_elim h
    cases vv with
    | all ty b =>
      obtain ⟨_, _, _, h⟩ := RM_bind_elim h
      split at h
      · obtain ⟨_, _, _, h⟩ := RM_bind_elim h
        obtain ⟨_, _, _, h⟩ := RM_bind_elim h
        obtain ⟨_, _, _, h⟩ := RM_bind_elim h
        exact ih h
      · simp only [RM_run_bind, RM_run_throw] at h; cases h
    | share i =>
      cases hsh : x.c.sharing[i]? with
      | none => simp [hsh, RM_run_throw] at h
      | some ent =>
        simp only [hsh] at h
        obtain ⟨_, _, hinner, _⟩ := enterShare_ok h
        exact ih hinner
    | app fArg lastArg =>
      obtain ⟨ha, cs1, _, h⟩ := RM_bind_elim h
      by_cases hand : (ctx.isEmpty && (headRefOf rd.s x.owner x.c ha.1).isSome &&
          headRefOf rd.s x.owner x.c ha.1 == andRef && ha.2.size == 2) = true
      · simp only [hand, ↓reduceIte] at h
        have hleft : ∀ m fArg' cs0 cs1 a,
            (readAndLeft x (readEquation rd cl x eqRef andRef targets n []) m fArg').run cs0 = .ok (a, cs1) →
            ∀ p ∈ a.toList,
              (∀ ps res rc rs rhs, p.2 = .body ps res rc rs rhs →
                LamsClosed rhs ∧ CaseFieldsDistinct rhs) ∧
              (∀ c, rd.s.store p.1.block = some c → recordDefault c = .ok true → DefaultIface p.2) := by
          intro m
          induction m with
          | zero => intro _ _ _ _ hl; simp [readAndLeft, RM_run_throw] at hl
          | succ m ihm =>
            intro fArg' cs0 cs1 a hl
            unfold readAndLeft at hl
            obtain ⟨vf, _, _, hl⟩ := RM_bind_elim hl
            cases vf with
            | app _ a0 => exact ih hl
            | share i =>
              cases hsh : x.c.sharing[i]? with
              | none => simp [hsh, RM_run_throw] at hl
              | some ent =>
                simp only [hsh] at hl
                obtain ⟨_, cs2, hinner, _⟩ := enterShare_ok hl
                exact ihm ent _ cs2 a hinner
            | _ => simp [RM_run_throw] at hl
        obtain ⟨ea, cs2, hla, h⟩ := RM_bind_elim h
        obtain ⟨eb, cs3, hlb, h⟩ := RM_bind_elim h
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        intro p hp
        rw [Array.toList_append, List.mem_append] at hp
        rcases hp with hp1 | hp2
        · exact hleft n fArg cs1 cs2 ea hla p hp1
        · exact ih hlb p hp2
      · simp only [hand, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · obtain ⟨lha, _, _, h⟩ := RM_bind_elim h
          cases hlf : headRefOf rd.s x.owner x.c lha.1 with
          | none => simp [hlf, RM_run_throw] at h
          | some f =>
            simp only [hlf] at h
            split at h
            · obtain ⟨_, _, _, h⟩ := RM_bind_elim h
              obtain ⟨_, _, _, h⟩ := RM_bind_elim h
              obtain ⟨_, _, _, h⟩ := RM_bind_elim h
              obtain ⟨_, _, _, h⟩ := RM_bind_elim h
              obtain ⟨⟨rhs, _⟩, _, hrhs, h⟩ := RM_bind_elim h
              cases hdef : definitionAt? rd.s f with
              | none => simp [hdef, RM_run_throw] at h
              | some fcd =>
                simp only [hdef] at h
                split at h
                · obtain ⟨fx, _, hfxL, h⟩ := RM_bind_elim h
                  obtain ⟨hfx, _⟩ := RM_lift_elim hfxL
                  obtain ⟨⟨⟨alls, cod, codSkel⟩, csF⟩, _, hrfL, h⟩ := RM_bind_elim h
                  obtain ⟨hrf, _⟩ := RM_lift_elim hrfL
                  split at h
                  · obtain ⟨_, _, _, h⟩ := RM_bind_elim h
                    obtain ⟨_, _, _, h⟩ := RM_bind_elim h
                    simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, _⟩ := h
                    intro p hp
                    simp only [List.mem_singleton] at hp
                    subst hp
                    constructor
                    · intro _ _ _ _ _ hEq
                      injection hEq with _ _ _ _ hrhsEq; subst hrhsEq
                      exact readTerm_struct (fun _ _ hcs => caseShape_distinct hcs) hrhs
                    · intro c hst hdefC
                      obtain ⟨rm, hrm, hbd, _, _⟩ := recordDefault_ok_true hdefC
                      have hfxrm : fx.rm = rm := by
                        unfold Reading.rcx at hfx
                        simp only [hst, hrm, Ex_bind_ok, Ex_pure, Except.ok.injEq] at hfx
                        rw [← hfx]
                      have hbdFx : BlocksDefault fx.rm := hfxrm ▸ hbd
                      obtain ⟨hall, hcod⟩ := readForalls_isDefault hbdFx hrf
                      refine ⟨?_, ?_, ?_⟩
                      · intro param hpm
                        simp only [List.mem_map] at hpm
                        obtain ⟨⟨⟨m, sk, dom⟩, idx⟩, hmz, rfl⟩ := hpm
                        have hmemTake : (m, sk, dom) ∈ alls.take ctx.length := list_mem_of_mem_zipIdx' hmz
                        have hmemAll : (m, sk, dom) ∈ alls := List.mem_of_mem_take hmemTake
                        obtain ⟨hm, hsk⟩ := hall (m, sk, dom) hmemAll
                        have hmEq : m = {} := by simpa [AllMode.isDefault] using hm
                        exact ⟨by simp [hmEq], hsk⟩
                      · cases hgl : (alls.take ctx.length).getLast? with
                        | none => rfl
                        | some tb =>
                          have hmem : tb ∈ alls := List.mem_of_mem_take (List.mem_of_getLast? hgl)
                          have hmEq : tb.1 = {} := by simpa [AllMode.isDefault] using (hall tb hmem).1
                          simp [hmEq]
                      · apply arrowChain_isDefault _ codSkel _ hcod
                        intro q hq
                        rw [List.mem_map] at hq
                        obtain ⟨tb, htb, rfl⟩ := hq
                        exact hall tb (List.mem_of_mem_drop htb)
                  · simp only [RM_run_bind, RM_run_throw] at h; cases h
                · simp only [RM_run_bind, RM_run_throw] at h; cases h
            · simp only [RM_run_bind, RM_run_throw] at h; cases h
        · simp only [RM_run_bind, RM_run_throw] at h; cases h
    | _ => simp [RM_run_throw] at h

theorem runTable_props {rd : Reading} {cl : Classifier} {rt : Array (Ref × RunDef)}
    (hrt : rd.runTable cl = .ok rt) :
    ∀ p ∈ rt.toList,
      (∀ ps res rc rs rhs, p.2 = .body ps res rc rs rhs →
        LamsClosed rhs ∧ CaseFieldsDistinct rhs) ∧
      (∀ c, rd.s.store p.1.block = some c → recordDefault c = .ok true → DefaultIface p.2) := by
  unfold Reading.runTable at hrt
  by_cases hemp : rd.s.runTable.isEmpty = true
  · simp only [hemp, ↓reduceIte, Ex_pure, Except.ok.injEq] at hrt
    subst hrt; intro _ hp; simp at hp
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte] at hrt
    have hloop : ∀ (l : List Address) (acc out : Array (Ref × RunDef)),
        (∀ p ∈ acc.toList,
          (∀ ps res rc rs rhs, p.2 = .body ps res rc rs rhs →
            LamsClosed rhs ∧ CaseFieldsDistinct rhs) ∧
          (∀ c, rd.s.store p.1.block = some c → recordDefault c = .ok true → DefaultIface p.2)) →
        (forIn (m := Except String) l acc fun a entries => do
          let some r := Ix.Kernel.Reader.resolve rd.s.store a | throw "the run table does not resolve"
          let some (c, d) := definitionAt? rd.s r | throw "the run table is not a definition"
          unless d.kind == .thm do throw "the run table is not a theorem"
          let x ← rd.rcx cl r
          let base := match r with | .member _ i => rootBase c i | _ => 0
          let es ← ((inBlock x.rm (rootKey base)
            (readEquation rd cl x (roleRef? rd.s .eq) (roleRef? rd.s .and) (runTableTargets rd) readFuel [] d.typ)).run {}).map (·.1)
          pure (ForInStep.yield (entries ++ es))) = .ok out →
        ∀ p ∈ out.toList,
          (∀ ps res rc rs rhs, p.2 = .body ps res rc rs rhs →
            LamsClosed rhs ∧ CaseFieldsDistinct rhs) ∧
          (∀ c, rd.s.store p.1.block = some c → recordDefault c = .ok true → DefaultIface p.2) := by
      intro l
      induction l with
      | nil =>
        intro acc out hacc hf
        simp only [List.forIn_nil, Ex_pure, Except.ok.injEq] at hf
        subst hf; exact hacc
      | cons a rest ih =>
        intro acc out hacc hf
        rw [List.forIn_cons] at hf
        cases hres : Ix.Kernel.Reader.resolve rd.s.store a with
        | none => simp [hres, Ex_throw, Ex_bind_err] at hf
        | some r =>
          simp only [hres] at hf
          cases hdef : definitionAt? rd.s r with
          | none => simp [hdef, Ex_throw, Ex_bind_err] at hf
          | some cd =>
            simp only [hdef] at hf
            obtain ⟨stepV, hstep, hf⟩ := Ex_bind_elim hf
            split at hstep
            · obtain ⟨x, _, hstep⟩ := Ex_bind_elim hstep
              obtain ⟨es, hesMap, hstep⟩ := Ex_bind_elim hstep
              simp only [Ex_pure, Except.ok.injEq] at hstep
              subst hstep
              obtain ⟨pes, hes, rfl⟩ := Ex_map_elim hesMap
              obtain ⟨_, hinner, _⟩ := inBlock_nodes_preserved hes
              have hnew := readEquation_props hinner
              dsimp only at hf
              apply ih (acc ++ pes.1) out _ hf
              intro p hp
              rw [Array.toList_append, List.mem_append] at hp
              rcases hp with hp1 | hp2
              · exact hacc p hp1
              · exact hnew p hp2
            · simp only [Ex_throw] at hstep; cases hstep
    obtain ⟨entries, hfl, hrt⟩ := Ex_bind_elim hrt
    obtain ⟨_, _, hrt⟩ := Ex_bind_elim hrt
    simp only [Ex_pure, Except.ok.injEq] at hrt
    subst hrt
    exact hloop rd.s.runTable #[] entries (by simp) hfl

/-- Every `.body` produced by `readDef` (whether from `readBody` or `runTable`) has
`LamsClosed body ∧ CaseFieldsDistinct body`. -/
theorem readDef_body_struct {rd : Reading} {cl : Classifier} {rt : Array (Ref × RunDef)}
    {r : Ref} {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term}
    (hrt : rd.runTable cl = .ok rt)
    (hrd : rd.readDef cl rt true r = .ok (.body ps res rc rs body)) :
    LamsClosed body ∧ CaseFieldsDistinct body := by
  generalize hd0 : RunDef.body ps res rc rs body = d0 at hrd
  cases readDef_elim hrd with
  | runTable q hrf =>
    have hp := (runTable_props hrt q (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hrf))).1
    exact hp ps res rc rs body hd0.symm
  | prim _ _ _ _ _ _ _ => cases hd0
  | ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | caseDef _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | ind _ _ _ _ _ _ _ _ _ => cases hd0
  | extern _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | stuck _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | body x b i dd ps' res' rc' rs' t _ _ _ hbd =>
    injection hd0 with _ _ _ _ htEq; subst htEq
    unfold readBody at hbd
    obtain ⟨_, _, hbd⟩ := Ex_bind_elim hbd
    obtain ⟨⟨⟨lams, bd, ctx, params, bodyT, bodyC?⟩, cs2⟩, hrl, hbd⟩ := Ex_bind_elim hbd
    have hbodyTEq : bodyT = body := by
      obtain ⟨_, _, hbd⟩ := Ex_bind_elim hbd
      dsimp only at hbd
      split at hbd
      · obtain ⟨_, _, hbd⟩ := Ex_bind_elim hbd
        obtain ⟨_, _, hbd⟩ := Ex_bind_elim hbd
        obtain ⟨_, _, hbd⟩ := Ex_bind_elim hbd
        simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbd
        exact hbd.2.2.2.2
      · cases bodyC? with
        | some _ =>
          obtain ⟨_, _, hbd⟩ := Ex_bind_elim hbd
          simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbd
          exact hbd.2.2.2.2
        | none =>
          obtain ⟨_, _, hbd⟩ := Ex_bind_elim hbd
          simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbd
          exact hbd.2.2.2.2
    subst hbodyTEq
    obtain ⟨_, hinner, _⟩ := inBlock_nodes_preserved hrl
    unfold readLamNodes at hinner
    exact readTele_struct_k (P := fun res => LamsClosed res.2.2.2.2.1 ∧ CaseFieldsDistinct res.2.2.2.2.1)
      (fun bs bd cs cs' v hv => by
        obtain ⟨⟨ctx1, ps1, bt1, bc1⟩, cs1, h1, hv⟩ := RM_bind_elim hv
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, _⟩ := hv
        obtain ⟨⟨ctx2, ps2⟩, cs2, _, h1⟩ := RM_bind_elim h1
        simp only [↓reduceIte] at h1
        obtain ⟨⟨bt2, bc2⟩, cs3, hrtm, h1⟩ := RM_bind_elim h1
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨⟨_, _, rfl, _⟩, _⟩ := h1
        exact readTerm_struct (fun _ _ hcs => caseShape_distinct hcs) hrtm) hinner

/-- Any `RunDef` read from a record satisfying `recordDefault c = .ok true` has `DefaultIface d`
(even when bound by `runTable`, because `readEquation` takes the interface from `r`'s own record). -/
theorem readDef_defaultIface {rd : Reading} {cl : Classifier} {rt : Array (Ref × RunDef)}
    {r : Ref} {c : Ixon.Constant} {d : RunDef}
    (hrt : rd.runTable cl = .ok rt)
    (hst : rd.s.store r.block = some c) (hdef : recordDefault c = .ok true)
    (hrd : rd.readDef cl rt true r = .ok d) :
    DefaultIface d := by
  obtain ⟨rm, hrm, hbd, hfm, _⟩ := recordDefault_ok_true hdef
  have hrcxRm : ∀ x, rd.rcx cl r = .ok x → x.c = c ∧ BlocksDefault x.rm := by
    intro x hx
    have hxc := rcx_c_eq hx hst
    have hxrm : x.rm = rm := by
      unfold Reading.rcx at hx
      simp only [hst, hrm, Ex_bind_ok, Ex_pure, Except.ok.injEq] at hx
      rw [← hx]
    exact ⟨hxc, hxrm ▸ hbd⟩
  cases readDef_elim hrd with
  | prim _ _ _ _ _ _ _ => trivial
  | ind _ _ _ _ _ _ _ _ _ => trivial
  | caseDef _ _ _ _ _ _ _ _ _ _ _ => trivial
  | runTable q hrf =>
    have hqeq : q.1 = r := beq_iff_eq.mp (Array.find?_some (p := fun x : Ref × RunDef => x.1 == r) hrf)
    have hp := (runTable_props hrt q (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hrf))).2
    exact hp c (hqeq ▸ hst) hdef
  | ctor x b i ci ms indV ctor fs hr hx hinfo hmi hci hrcf =>
    subst hr
    obtain ⟨hxc, hbdX⟩ := hrcxRm x hx
    exact readCtorFields_isDefault hbdX (hxc ▸ hfm) hinfo hmi hci hrcf
  | extern x b i root ty ps res rc rs hr hx _ hext =>
    subst hr
    obtain ⟨_, hbdX⟩ := hrcxRm x hx
    obtain ⟨_, _, _, _, hEq, hi⟩ := externAt_ok hext
    injection hEq with h1 h2 _ h4
    subst h1; subst h2; subst h4
    exact ifaceAt_isDefault hbdX hi
  | stuck x b i root ty ps res rc rs hr hx _ hstk =>
    subst hr
    obtain ⟨_, hbdX⟩ := hrcxRm x hx
    obtain ⟨_, _, _, _, hEq, hi, _, _⟩ := stuckAt_ok hstk
    injection hEq with h1 h2 _ h4
    subst h1; subst h2; subst h4
    exact ifaceAt_isDefault hbdX hi
  | body x b i dd ps res rc rs t hr hx _ hbdRun =>
    subst hr
    obtain ⟨_, hbdX⟩ := hrcxRm x hx
    unfold readBody at hbdRun
    obtain ⟨⟨⟨alls, cod, codSkel⟩, cs1⟩, hrf, hbdRun⟩ := Ex_bind_elim hbdRun
    obtain ⟨⟨⟨lams, bd, ctx, params, bodyT, bodyC?⟩, cs2⟩, hrl, hbdRun⟩ := Ex_bind_elim hbdRun
    obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
    obtain ⟨hallsDef, hcodDef⟩ := readForalls_isDefault hbdX hrf
    obtain ⟨_, hrlIn, _⟩ := inBlock_nodes_preserved hrl
    unfold readLamNodes at hrlIn
    have hlamsDef := readTele_isDefault_of_blocksDefault hbdX (by simp) (hbdX.block? _) hrlIn
    have hopParams : ∀ p ∈ params.toList, p.mode = .many ∧ p.skel.isDefault = true := by
      have haux : ∀ {n : Nat} {acc : List TeleBinder} {e : Ixon.Expr} {c0 c1 : Cursor}
          {res0 : List TeleBinder × Ixon.Expr × List Local × Array Param × Term × Option Cls},
          (∀ tb ∈ acc, tb.1.isDefault = true ∧ tb.2.1.isDefault = true) →
          (∀ nd ∈ c0.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true) →
          (readTele x true (fun ls bd => do
            pure (ls, bd, ← (do
              let (ctx, params) ← openParams x ls
              let (bt, bc) ← readTerm x (caseShape rd.s rt 16) readFuel ctx bd
              pure (ctx, params, bt, some bc)))) n acc e).run c0 = .ok (res0, c1) →
          ∀ p ∈ res0.2.2.2.1.toList, p.mode = .many ∧ p.skel.isDefault = true := by
        intro n
        induction n with
        | zero => intro _ _ _ _ _ _ _ hr; simp [readTele, RM_run_throw] at hr
        | succ n ihr =>
          intro acc e c0 c1 res0 hacc hc0 hr
          unfold readTele at hr
          obtain ⟨vv, c0', hvl, hr⟩ := RM_bind_elim hr
          obtain ⟨_, hc0Eq⟩ := RM_lift_elim hvl; subst c0'
          have hstop : ∀ {e0}, (do
              pure (acc.reverse, e0, ← ((do
                let (ctx, params) ← openParams x acc.reverse
                let (bt, bc) ← readTerm x (caseShape rd.s rt 16) readFuel ctx e0
                pure (ctx, params, bt, some bc)) : RM _))).run c0 = .ok (res0, c1) →
              ∀ p ∈ res0.2.2.2.1.toList, p.mode = .many ∧ p.skel.isDefault = true := by
            intro e0 hs
            obtain ⟨⟨ctx0, ps0, bt0, bc0⟩, _, hinner', hs⟩ := RM_bind_elim hs
            simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, _⟩ := hs
            obtain ⟨⟨ctx1, ps1⟩, _, hopL, hinner'⟩ := RM_bind_elim hinner'
            have hop : openParams x acc.reverse = .ok (ctx1, ps1) := by
              cases h1 : openParams x acc.reverse with
              | error _ => simp [h1] at hopL
              | ok p => simp only [h1, RM_run_lift, Ex_map_ok, Except.ok.injEq, Prod.mk.injEq] at hopL; rw [← hopL.1]
            obtain ⟨⟨bt1, bc1⟩, _, _, hinner'⟩ := RM_bind_elim hinner'
            simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hinner'
            obtain ⟨⟨_, rfl, _, _⟩, _⟩ := hinner'
            exact openParams_isDefault hop (fun tb htb => hacc tb (List.mem_reverse.mp htb))
          cases vv with
          | all _ _ => simp only [↓reduceIte] at hr; exact hstop hr
          | lam ty' b' =>
            simp only [↓reduceIte] at hr
            obtain ⟨m0, c2, hm, hr⟩ := RM_bind_elim hr
            obtain ⟨hmDef, hnd2⟩ := cursor_allDefault_nextBinder hc0 hm
            have hc2 : ∀ nd ∈ c2.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
              rw [hnd2]; exact hc0
            obtain ⟨d0, c3, hd, hr⟩ := RM_bind_elim hr
            obtain ⟨hdDef, hnd3⟩ := readSkel_isDefault_of_blocksDefault hbdX n ty' hc2 hd
            have hc3 : ∀ nd ∈ c3.nodes.toList, ∀ m, nd = .binder m → m.isDefault = true := by
              rw [hnd3]; exact hc2
            exact ihr (fun tb htb => by
              rcases List.mem_cons.mp htb with rfl | hrest
              · exact ⟨hmDef, hdDef⟩
              · exact hacc tb hrest) hc3 hr
          | share j =>
            cases hsh : x.c.sharing[j]? with
            | none => simp only [hsh] at hr; exact hstop hr
            | some ent =>
              simp only [hsh] at hr
              cases hc : continuesTele x.c true ent with
              | false => simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr; exact hstop hr
              | true =>
                simp only [hc, ↓reduceIte] at hr
                obtain ⟨key', _, hinner', _⟩ := enterShare_ok hr
                exact ihr hacc (hbdX.block? key') hinner'
          | _ => exact hstop hr
      exact haux (acc := []) (by simp) (hbdX.block? _) (by simpa using hrlIn)
    have hresDef : (Option.map (fun x => x.1.result) lams.getLast?).getD ResultMode.shared = .shared := by
      cases hgl : lams.getLast? with
      | none => rfl
      | some tb =>
        have hmEq : tb.1 = {} := by simpa [AllMode.isDefault] using (hlamsDef tb (List.mem_of_getLast? hgl)).1
        simp [hmEq]
    dsimp only at hbdRun
    split at hbdRun
    · obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
      obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
      obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
      simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbdRun
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbdRun
      refine ⟨hopParams, hresDef, arrowChain_isDefault _ codSkel ?_ hcodDef⟩
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨tb, htb, rfl⟩ := hq
      exact hallsDef tb (List.mem_of_mem_drop htb)
    · cases bodyC? with
      | some _ =>
        obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
        simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbdRun
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbdRun
        exact ⟨hopParams, hresDef, rfl⟩
      | none =>
        obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
        simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbdRun
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hbdRun
        exact ⟨hopParams, hresDef, rfl⟩

/-- A `.body` read from a default-mode record not bound by `rt` satisfies both `DefaultIface`
and `TermModesDefault body`. -/
theorem readDef_body_modesDefault {rd : Reading} {cl : Classifier} {rt : Array (Ref × RunDef)}
    {r : Ref} {c : Ixon.Constant} {ps : Array Param} {res : ResultMode} {rc : Cls} {rs : Skel} {body : Term}
    (hrt : rd.runTable cl = .ok rt)
    (hrtNone : rt.find? (·.1 == r) = none)
    (hst : rd.s.store r.block = some c) (hdef : recordDefault c = .ok true)
    (hrd : rd.readDef cl rt true r = .ok (.body ps res rc rs body)) :
    DefaultIface (.body ps res rc rs body) ∧ TermModesDefault body := by
  refine ⟨readDef_defaultIface hrt hst hdef hrd, ?_⟩
  obtain ⟨rm, hrm, hbd, _, hlets⟩ := recordDefault_ok_true hdef
  generalize hd0 : RunDef.body ps res rc rs body = d0 at hrd
  cases readDef_elim hrd with
  | runTable q hrf => rw [hrtNone] at hrf; cases hrf
  | prim _ _ _ _ _ _ _ => cases hd0
  | ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | caseDef _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | ind _ _ _ _ _ _ _ _ _ => cases hd0
  | extern _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | stuck _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
  | body x b i dd ps' res' rc' rs' t hr hx hsrc hbdRun =>
    injection hd0 with _ _ _ _ htEq; subst htEq
    subst hr
    have hxc := rcx_c_eq hx hst
    have hxrm : x.rm = rm := by
      unfold Reading.rcx at hx
      simp only [hst, hrm, Ex_bind_ok, Ex_pure, Except.ok.injEq] at hx
      rw [← hx]
    have hbdX : BlocksDefault x.rm := hxrm ▸ hbd
    have hshDef : ∀ ent ∈ x.c.sharing.toList, ExprLetsDefault ent := by
      intro ent hent
      rw [hxc] at hent
      apply letsDefault_ok_true
      exact hlets ent (by rw [Array.toList_append, List.mem_append]; exact Or.inr hent)
    have hvalDef : ExprLetsDefault dd.value := by
      rw [hxc] at hsrc
      apply letsDefault_ok_true
      exact hlets dd.value (by
        rw [Array.toList_append, List.mem_append]
        exact Or.inl (binderRoots_mem_defn hsrc))
    unfold readBody at hbdRun
    obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
    obtain ⟨⟨⟨lams, bd, ctx, params, bodyT, bodyC?⟩, cs2⟩, hrl, hbdRun⟩ := Ex_bind_elim hbdRun
    have hbodyTEq : bodyT = body := by
      obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
      dsimp only at hbdRun
      split at hbdRun
      · obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
        obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
        obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
        simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbdRun
        exact hbdRun.2.2.2.2
      · cases bodyC? with
        | some _ =>
          obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
          simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbdRun
          exact hbdRun.2.2.2.2
        | none =>
          obtain ⟨_, _, hbdRun⟩ := Ex_bind_elim hbdRun
          simp only [Ex_pure, Except.ok.injEq, RunDef.body.injEq] at hbdRun
          exact hbdRun.2.2.2.2
    subst hbodyTEq
    obtain ⟨_, hrlIn, _⟩ := inBlock_nodes_preserved hrl
    unfold readLamNodes at hrlIn
    obtain ⟨_, _, hD⟩ := readTele_body_props (P := fun _ _ res => TermModesDefault res.2.2.2.2.1)
      hbdX hshDef
      (fun bs bd0 cs0 cs0' v _ hbdDef hcs0 hv => by
        obtain ⟨⟨ctx0, ps0, bt0, bc0⟩, cs1, h1, hv⟩ := RM_bind_elim hv
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, _⟩ := hv
        obtain ⟨⟨ctx1, ps1⟩, cs2, hopL, h1⟩ := RM_bind_elim h1
        obtain ⟨_, hcs2⟩ := RM_lift_elim hopL; subst cs2
        simp only [↓reduceIte] at h1
        obtain ⟨⟨bt1, bc1⟩, cs3, hrtm, h1⟩ := RM_bind_elim h1
        simp only [RM_run_pure, Except.ok.injEq, Prod.mk.injEq] at h1
        obtain ⟨⟨_, _, hbtEq, _⟩, _⟩ := h1
        subst hbtEq
        exact (readTerm_modesDefault hbdX hshDef hbdDef hcs0 hrtm).1)
      (by simp) hvalDef (hbdX.block? _) hrlIn
    exact hD

/-- Every constructor in `(P.ctorsOf ind).toList` lives in the same record block as `ind`. -/
theorem readProg_ind_ctor_block {s : Subject} {cl : Classifier} {P : Prog}
    (hp : readProg s cl = .ok P) {ind ctor : Ref} (hmem : ctor ∈ (P.ctorsOf ind).toList) :
    ctor.block = ind.block := by
  obtain ⟨_, rt, hrt, _, _, hfindElim, _, _, _⟩ := readProg_elim hp
  unfold Prog.ctorsOf at hmem
  cases hfind : P.find? ind with
  | none => simp [hfind] at hmem
  | some d =>
    rw [hfind] at hmem
    cases d with
    | ind cs =>
      obtain ⟨c, _, _, _, hrd⟩ := hfindElim ind (.ind cs) hfind
      generalize hd0 : RunDef.ind cs = d0 at hrd
      cases readDef_elim hrd with
      | runTable q hrf =>
        obtain ⟨_, _, _, _, _, hbd⟩ :=
          (runTable_mem_body hrt q (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hrf))).1
        rw [hbd] at hd0; cases hd0
      | prim _ _ _ _ _ _ _ => cases hd0
      | ctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | caseDef _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | extern _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | stuck _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | body _ _ _ _ _ _ _ _ _ _ _ _ _ => cases hd0
      | ind x b i ms indV hr _ _ _ =>
        injection hd0 with hcsEq; subst hcsEq
        subst hr
        simp only [Array.toList_map, List.mem_map] at hmem
        obtain ⟨j, _, rfl⟩ := hmem
        rfl
    | _ => simp at hmem

end IxCK.Resource.Proof
