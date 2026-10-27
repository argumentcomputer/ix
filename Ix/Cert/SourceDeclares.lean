import Ix.Cert.SourceTrace
import Ix.Cert.ReaderUnits
import IxC.Kernel.Verify.Frontend.Prepare

/-! # Quotient Source declares every stored constant's quotient key

When quotient Source's preparation succeeds (`Ix.LeanIngress.prepareSourceCollapsed`),
every name `n` that the closure stores a constant under is declared by some
declaration of the prepared stream, under its quotient key
(`Key.subst ρ (ingressKey n)`):

1. **Grouping covers every stored name** (`stored_grouped`): `groupsOf`'s last loop
   pushes a group of its own (`unplaced`) for every stored name no earlier group
   lists, compared by spelling.
2. **Every group converts** and is scheduled (`scheduleOf_complete`), and a group's
   conversion declares the ingress keys of the group's names (`convert_declares`,
   the converse of `ReaderUnits.convert_keys`); the hint override keeps them and the
   quotient renaming renames them (`convKeys_withHints`, `convKeys_quotient`).
3. **Lowering declares them** (`lower_declares`).
4. **The collapse drops no name** (`trace_declares`): a lowered group's names are
   owned after its collapse (`SourcePrelude.collapseRead_facts`), owners persist
   (`OwnerExt`), and an alias group's names are owned through the kept block it
   aliases (`BlockOwned`: every name of a kept block is owned). An owned name is a
   name of a kept declaration (`SourceReplay.trace_ownerExact`).
5. **Preparation keeps every kept declaration** (`Frontend.preparePrelude_perm`).

The result is `prepared_declares`, and its form at a compiled artifact
`preparedAt_declares`. -/

namespace Ix.Cert.SourceDeclares

open Ix.Kernel Ix.Kernel.Reader Ix.LeanIngress Ix.Cert.SourcePrelude Ix.Cert.SourceReplay
open Ix.CompileCert.Loop (except_bind_ok idBind idPure)

/-! ## Loops -/

/-- An `Id` loop each of whose steps keeps its state's elements, and holds one
`R`-related to the step's element, as long as the state holds `init`'s, holds one
for every element. -/
theorem forIn_id_cover {α G : Type} {R : α → G → Prop} (f : α → Array G → Id (ForInStep (Array G)))
    (init : Array G)
    (step : ∀ a acc, (∀ y ∈ init, y ∈ acc) →
      ∃ b, f a acc = .yield b ∧ (∀ y ∈ acc, y ∈ b) ∧ ∃ y ∈ b, R a y) :
    ∀ (l : List α) (acc : Array G), (∀ y ∈ init, y ∈ acc) →
      (∀ y ∈ acc, y ∈ Id.run (forIn l acc f)) ∧ ∀ a ∈ l, ∃ y ∈ Id.run (forIn l acc f), R a y
  | [], _, _ => ⟨fun _ h => h, fun _ h => nomatch h⟩
  | a :: l, acc, hacc => by
    obtain ⟨b, hb, keep, y, hy, hr⟩ := step a acc hacc
    have ih := forIn_id_cover f init step l b (fun z hz => keep z (hacc z hz))
    rw [List.forIn_cons, hb]
    refine ⟨fun z hz => ih.1 z (keep z hz), fun a' ha' => ?_⟩
    rcases List.mem_cons.mp ha' with rfl | ha'
    · exact ⟨y, ih.1 y hy, hr⟩
    · exact ih.2 a' ha'

/-- A name a set of spellings holds is one inserted into it. -/
theorem tableSet_contains {s : Ix.Set TableName} {a k : TableName} :
    (s.insert a).contains k = true ↔ a = k ∨ s.contains k = true := by
  rw [Std.HashSet.contains_insert, Bool.or_eq_true]
  exact or_congr_left ⟨fun h => Ix.Name.beqRaw_iff.mp h, fun h => Ix.Name.beqRaw_iff.mpr h⟩

/-- An `Id` loop each of whose steps adds names `names a` to a set of spellings
holds only names it was given or started with. -/
theorem forIn_id_claims {α : Type} (names : α → List TableName)
    (f : α → Ix.Set TableName → Id (ForInStep (Ix.Set TableName)))
    (step : ∀ a s, ∃ s', f a s = .yield s' ∧
      ∀ k, s'.contains k = true → k ∈ names a ∨ s.contains k = true) :
    ∀ (l : List α) (s : Ix.Set TableName) (k : TableName), (Id.run (forIn l s f)).contains k = true →
      (∃ a ∈ l, k ∈ names a) ∨ s.contains k = true
  | [], _, _, h => .inr h
  | a :: l, s, k, h => by
    obtain ⟨s', hs', back⟩ := step a s
    rw [List.forIn_cons, hs'] at h
    rcases forIn_id_claims names f step l s' k h with ⟨a', ha', hk⟩ | hk
    · exact .inl ⟨a', List.mem_cons_of_mem _ ha', hk⟩
    · rcases back k hk with hk | hk
      · exact .inl ⟨a, List.mem_cons_self, hk⟩
      · exact .inr hk

/-- `forIn_id_claims` over an array. -/
theorem forIn_id_claims_array {α : Type} (names : α → List TableName)
    (f : α → Ix.Set TableName → Id (ForInStep (Ix.Set TableName)))
    (step : ∀ a s, ∃ s', f a s = .yield s' ∧
      ∀ k, s'.contains k = true → k ∈ names a ∨ s.contains k = true)
    (xs : Array α) (s : Ix.Set TableName) (k : TableName) (h : (Id.run (forIn xs s f)).contains k = true) :
    (∃ a ∈ xs.toList, k ∈ names a) ∨ s.contains k = true := by
  rw [← Array.forIn_toList] at h
  exact forIn_id_claims names f step xs.toList s k h

/-- A fallible loop each of whose steps keeps `get`'s elements and holds one
`Q`-related to each item of the step's element holds one for every item. -/
theorem forIn_covers {α σ β γ : Type} (get : σ → Array β) (items : α → List γ) (Q : γ → β → Prop)
    (xs : Array α) (f : α → σ → ReadM (ForInStep σ))
    (step : ∀ x ∈ xs.toList, ∀ s r, f x s = .ok r →
      ∃ s', r = .yield s' ∧ (∀ e ∈ get s, e ∈ get s') ∧ ∀ y ∈ items x, ∃ e ∈ get s', Q y e)
    {s res : σ} (ran : forIn xs s f = .ok res) :
    (∀ e ∈ get s, e ∈ get res) ∧ ∀ x ∈ xs.toList, ∀ y ∈ items x, ∃ e ∈ get res, Q y e :=
  Ix.CompileCert.Loop.forIn_inv_array
    (fun pre t => (∀ e ∈ get s, e ∈ get t) ∧ ∀ x ∈ pre, ∀ y ∈ items x, ∃ e ∈ get t, Q y e) f xs
    (fun pre x post t r split hI hf => by
      have hx : x ∈ xs.toList := by rw [← split]; simp
      obtain ⟨s', rfl, keep, covers⟩ := step x hx t r hf
      refine ⟨s', rfl, fun e' he' => keep e' (hI.1 e' he'), fun x' hx' y hy => ?_⟩
      rcases List.mem_append.mp hx' with hx' | hx'
      · obtain ⟨e', he', hq'⟩ := hI.2 x' hx' y hy
        exact ⟨e', keep e' he', hq'⟩
      · rw [List.mem_singleton] at hx'
        subst hx'
        exact covers y hy)
    ⟨fun _ h => h, fun _ h _ _ => nomatch h⟩ ran

/-! ## 1. Grouping covers every stored name -/

theorem unplaced_names (n : Ix.Name) (ci : Ix.ConstantInfo) : (unplaced n ci).names = #[n] := by
  unfold unplaced
  split <;> rfl

/-- **Every name the environment stores a constant under is a name of one of its
groups**, spelled exactly. -/
theorem stored_grouped (env : Ix.Environment) (blocks : Ix.CondensedBlocks) {n : Ix.Name}
    {ci : Ix.ConstantInfo} (h : (n, ci) ∈ env.consts.toList) :
    ∃ g ∈ groupsOf env blocks, n ∈ g.names := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  refine (forIn_id_cover (R := fun (a : Ix.Name × Ix.ConstantInfo) (g : Group) => a.1 ∈ g.names)
    _ _ ?_ _ _ (fun _ h => h)).2 (n, ci) h
  intro a acc hacc
  split
  · rename_i hc
    refine ⟨_, rfl, fun _ h => h, ?_⟩
    have one : ∀ (x : Ix.Name) (t : Ix.Set TableName), ∃ t',
        ForInStep.yield (Std.HashSet.insert t x) = ForInStep.yield t' ∧
          ∀ k, t'.contains k = true → k ∈ [x] ∨ t.contains k = true := by
      intro x t
      refine ⟨_, rfl, fun k hk => ?_⟩
      rcases tableSet_contains.mp hk with rfl | hk
      · exact .inl List.mem_cons_self
      · exact .inr hk
    have step : ∀ (g : Group) (s : Ix.Set TableName), ∃ s',
        ForInStep.yield (forIn (m := Id) g.names s fun n t => ForInStep.yield (Std.HashSet.insert t n)) =
          ForInStep.yield s' ∧ ∀ k : TableName, s'.contains k = true → k ∈ g.names.toList ∨ s.contains k = true := by
      intro g s
      refine ⟨_, rfl, fun k hk => ?_⟩
      rcases forIn_id_claims_array (fun (x : Ix.Name) => [x]) _ one g.names s k hk with ⟨x, hx, hkx⟩ | hk
      · have hkx' := List.mem_singleton.mp hkx
        subst hkx'
        exact .inl hx
      · exact .inr hk
    rcases forIn_id_claims_array (fun (g : Group) => g.names.toList) _ step _ _ _ hc with ⟨g, hg, hk⟩ | hk
    · exact ⟨g, hacc g (Array.mem_toList_iff.mp hg), Array.mem_toList_iff.mp hk⟩
    · have e : Std.HashSet.contains (∅ : Ix.Set TableName) a.fst = false := Std.HashSet.contains_empty
      exact absurd (e.symm.trans hk) (by decide)
  · refine ⟨_, rfl, fun _ h => Array.mem_push_of_mem _ h, _, Array.mem_push_self, ?_⟩
    rw [unplaced_names]
    exact Array.mem_singleton.mpr rfl

/-! ## 2. A group's conversion declares its names -/

/-- The keys a converted group declares. -/
def convKeys : Converted → List (CName .source)
  | .inductive rb => BlockRead.names rb
  | .definitions ms => ms.toList.map (·.cv.name)
  | .axiom cv => [cv.name]
  | .quot _ cv => [cv.name]

/-- `defOrder`'s marks: `done` has one mark per member, every index pushed is a
member's and marked, and no index is pushed twice. -/
def Marked (n : Nat) (done : Array Bool) (out : Array Nat) : Prop :=
  done.size = n ∧ (∀ i ∈ out, i < n ∧ done[i]? = some true) ∧ out.toList.Nodup

/-- `defOrder`'s outer state: marked, and an early result holds every member once. -/
def OrderMarked (n : Nat) (u : Option (Option (Array Nat)) × Array Bool × Array Nat) : Prop :=
  Marked n u.2.1 u.2.2 ∧
    ∀ o, u.1 = some (some o) → o.size = n ∧ o.toList.Nodup ∧ ∀ i ∈ o, i < n

/-- An array of distinct members, as many as there are, holds every member. -/
theorem all_members {n : Nat} {o : Array Nat} (size : o.size = n) (nodup : o.toList.Nodup)
    (lt : ∀ i ∈ o, i < n) : ∀ j < n, j ∈ o := by
  intro j hj
  refine Classical.byContradiction fun hno => ?_
  have hnd : (j :: o.toList).Nodup :=
    List.nodup_cons.mpr ⟨fun h => hno (Array.mem_toList_iff.mp h), nodup⟩
  have hsub : (j :: o.toList) ⊆ List.range n := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_range.mpr hj
    · exact List.mem_range.mpr (lt x (Array.mem_toList_iff.mp hx))
  have := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_cons, Array.length_toList, List.length_range] at this
  omega

/-- **`defOrder` orders every member**: the order it returns holds every index
below the number of members. -/
theorem defOrder_complete {deps : Array (Std.HashSet Nat)} {out : Array Nat} (h : defOrder deps = some out) :
    ∀ j < deps.size, j ∈ out := by
  suffices good : out.size = deps.size ∧ out.toList.Nodup ∧ ∀ i ∈ out, i < deps.size from
    all_members good.1 good.2.1 good.2.2
  unfold defOrder at h
  revert h
  apply ReaderUnits.forIn_range_value_inv (OrderMarked deps.size)
    (fun v => v = some out → out.size = deps.size ∧ out.toList.Nodup ∧ ∀ i ∈ out, i < deps.size)
  · intro x _ t ht
    apply ReaderUnits.forIn_range_value_inv
      (fun (u : Array Bool × Array Nat × Bool) => Marked deps.size u.1 u.2.1)
      (fun v => OrderMarked deps.size (ForInStep.value v))
    · intro i hi u hu
      dsimp only
      split
      · rename_i hcond
        obtain ⟨hsize, hmarked, hnodup⟩ := hu
        have hlt : i < u.1.size := by rw [hsize]; exact hi
        have hfalse : u.1[i]! = false := by
          have := (Bool.and_eq_true _ _).mp hcond
          simpa using this.1
        have hnot : i ∉ u.2.1 := by
          intro hin
          have hm := (hmarked i hin).2
          rw [Array.getElem?_eq_getElem hlt] at hm
          rw [getElem!_pos u.1 i hlt] at hfalse
          rw [Option.some.inj hm] at hfalse
          cases hfalse
        show Marked deps.size (u.fst.set! i true) (u.snd.fst.push i)
        refine ⟨by simp [hsize], fun j hj => ?_, ?_⟩
        · rw [Array.set!_eq_setIfInBounds]
          rcases Array.mem_push.mp hj with hj | rfl
          · refine ⟨(hmarked j hj).1, ?_⟩
            by_cases hji : i = j
            · subst hji
              exact Array.getElem?_setIfInBounds_self_of_lt hlt
            · rw [Array.getElem?_setIfInBounds_ne hji]
              exact (hmarked j hj).2
          · exact ⟨hi, Array.getElem?_setIfInBounds_self_of_lt hlt⟩
        · rw [Array.toList_push]
          exact List.nodup_append.mpr ⟨hnodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
            fun a ha b hb hab => by
              rw [List.mem_singleton] at hb
              subst hb hab
              exact hnot (Array.mem_toList_iff.mp ha)⟩
      · exact hu
    · exact ht.1
    · intro u hu
      dsimp only
      split
      · rename_i hsz
        exact ⟨hu, fun o ho => by
          cases ho
          exact ⟨beq_iff_eq.mp hsz, hu.2.2, fun i hi => (hu.2.1 i hi).1⟩⟩
      · split
        · exact ⟨hu, fun o ho => by cases ho⟩
        · exact ⟨hu, fun o ho => by cases ho⟩
  · exact ⟨⟨by simp, fun i hi => by simp at hi, by simp⟩, fun o ho => by cases ho⟩
  · intro u hu
    dsimp only
    split
    · rename_i r hr
      intro hro
      cases hro
      exact hu.2 out hr
    · intro hro
      split at hro
      · rename_i hsz
        cases hro
        exact ⟨beq_iff_eq.mp hsz, hu.1.2.2, fun i hi => (hu.1.2.1 i hi).1⟩
      · cases hro

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ x ∈ l₁, ∃ y ∈ l₂, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons (b := b) h t, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, r⟩ := forall₂_mem_left t x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, r⟩

/-- **A converted definition group declares every member's ingress key** (the block
order `defOrder` returns holds every member, `defOrder_complete`). -/
theorem convertDefinitions_declares {members : Array Ix.ConstantInfo} {conv : Converted}
    (ran : convertDefinitions members = .ok conv) :
    ∃ ms : Array DefMember, conv = .definitions ms ∧
      ∀ ci ∈ members, ∃ m ∈ ms, m.cv.name = ingressKey ci.getCnst.name := by
  unfold convertDefinitions at ran
  obtain ⟨shapes, hshapes, ran⟩ := except_bind_ok.mp ran
  have shapesOf : ∀ ci ∈ members, ∃ x ∈ shapes, x.1 = ci := by
    intro ci hci
    obtain ⟨x, hx, hf⟩ := forall₂_mem_left (ReaderUnits.array_mapM_ok hshapes) ci
      (Array.mem_toList_iff.mpr hci)
    refine ⟨x, Array.mem_toList_iff.mp hx, ?_⟩
    split at hf
    · simp only [pure, Except.pure, Except.ok.injEq] at hf
      subst hf
      rfl
    · cases hf
  have zipped : ∀ x ∈ shapes, ∃ j, (x, j) ∈ shapes.zipIdx := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hx
    exact ⟨j, Array.mem_zipIdx_iff_getElem?.mpr (by simp [hj])⟩
  dsimp only at ran
  rcases ReaderUnits.ite_ok ran with ran | ran <;>
    try (split at ran; exact (ReaderUnits.fail_bind ran).elim)
  all_goals
    obtain ⟨ks, -, ran⟩ := except_bind_ok.mp ran
    rcases ReaderUnits.ite_ok ran with ran | ran
    · simp only [pure, Except.pure, Except.ok.injEq] at ran
      subst ran
      refine ⟨_, rfl, fun ci hci => ?_⟩
      obtain ⟨x, hx, rfl⟩ := shapesOf ci hci
      obtain ⟨j, hj⟩ := zipped x hx
      exact ⟨_, Array.mem_map_of_mem hj, rfl⟩
    · split at ran
      · rename_i order horder
        simp only [pure, Except.pure, Except.ok.injEq] at ran
        subst ran
        refine ⟨_, rfl, fun ci hci => ?_⟩
        obtain ⟨x, hx, rfl⟩ := shapesOf ci hci
        obtain ⟨j, hj⟩ := zipped x hx
        have hlt : j < shapes.size := (Array.getElem?_eq_some_iff.mp (Array.mem_zipIdx_iff_getElem?.mp hj)).1
        have member := defOrder_complete horder j (by simpa using hlt)
        refine ⟨_, Array.mem_map_of_mem member, ?_⟩
        rw [getElem!_pos _ j (by simpa using hlt)]
        simp only [Array.getElem_map, Array.getElem_zipIdx]
        rw [(Array.getElem?_eq_some_iff.mp (Array.mem_zipIdx_iff_getElem?.mp hj)).2]
      · cases ran

/-- **A converted inductive block declares every source constant's ingress key**:
each type's, constructor's and recursor's. -/
theorem convertInductive_declares {types : Array Ix.InductiveVal} {ctors : Array (Array Ix.ConstructorVal)}
    {recs : Array Ix.RecursorVal} {conv : Converted} (ran : convertInductive types ctors recs = .ok conv) :
    ∃ rb : BlockRead .source, conv = .inductive rb ∧
      (∀ v ∈ types, ∃ e ∈ rb.types, e.1.name = ingressKey v.cnst.name) ∧
      (∀ cs ∈ ctors, ∀ c ∈ cs, ∃ e ∈ rb.ctors, e.1.name = ingressKey c.cnst.name) ∧
      (∀ r ∈ recs, ∃ e ∈ rb.recs, e.1.name = ingressKey r.cnst.name) := by
  unfold convertInductive at ran
  split at ran
  · simp only at ran
    split at ran
    · cases ran
    · split at ran
      · obtain ⟨ks, -, rest⟩ := except_bind_ok.mp ran
        obtain ⟨s₁, typesLoop, rest⟩ := except_bind_ok.mp rest
        obtain ⟨s₂, ctorsLoop, rest⟩ := except_bind_ok.mp rest
        obtain ⟨s₃, recsLoop, rest⟩ := except_bind_ok.mp rest
        simp only [pure, Except.pure, Except.ok.injEq] at rest
        subst rest
        have tk := (forIn_covers (fun s => s.2) (fun v => [v])
          (fun (v : Ix.InductiveVal) (e : CVal .source × Nat × Nat) => e.1.name = ingressKey v.cnst.name) _ _
          (fun v _ s r hf => by
            simp only [pure, Except.pure, Except.ok.injEq] at hf
            subst hf
            refine ⟨_, rfl, fun e he => Array.mem_push_of_mem _ he, fun y hy => ?_⟩
            rw [List.mem_singleton] at hy
            subst hy
            exact ⟨_, Array.mem_push_self, rfl⟩) typesLoop).2
        have ck := (forIn_covers (fun s => s.2.1) (fun cs => cs.toList)
          (fun (c : Ix.ConstructorVal) (e : CVal .source × Nat × Nat) => e.1.name = ingressKey c.cnst.name) _ _
          (fun cs _ s r hf => by
            obtain ⟨s1, hs1, hf⟩ := except_bind_ok.mp hf
            simp only [pure, Except.pure, Except.ok.injEq] at hf
            subst hf
            have inner := forIn_covers (fun s => s.2.1) (fun c => [c])
              (fun (c : Ix.ConstructorVal) (e : CVal .source × Nat × Nat) => e.1.name = ingressKey c.cnst.name)
              _ _ (fun c _ t q hq => by
                split at hq
                · simp only [pure, Except.pure, Except.ok.injEq] at hq
                  subst hq
                  refine ⟨_, rfl, fun e he => Array.mem_push_of_mem _ he, fun y hy => ?_⟩
                  rw [List.mem_singleton] at hy
                  subst hy
                  exact ⟨_, Array.mem_push_self, rfl⟩
                · cases hq) hs1
            exact ⟨_, rfl, inner.1, fun c hc => inner.2 c hc c List.mem_cons_self⟩) ctorsLoop).2
        have rk := (forIn_covers (fun s => s.2) (fun r => [r])
          (fun (r : Ix.RecursorVal) (e : CVal .source × RecCounts × List (Ix.Kernel.RecRule .source)) =>
            e.1.name = ingressKey r.cnst.name) _ _
          (fun r _ s q hq => by
            obtain ⟨s1, -, hq⟩ := except_bind_ok.mp hq
            simp only [pure, Except.pure, Except.ok.injEq] at hq
            subst hq
            refine ⟨_, rfl, fun e he => Array.mem_push_of_mem _ he, fun y hy => ?_⟩
            rw [List.mem_singleton] at hy
            subst hy
            exact ⟨_, Array.mem_push_self, rfl⟩) recsLoop).2
        exact ⟨_, rfl, fun v hv => tk v (Array.mem_toList_iff.mpr hv) v List.mem_cons_self,
          fun cs hcs c hc => ck cs (Array.mem_toList_iff.mpr hcs) c (Array.mem_toList_iff.mpr hc),
          fun r hr => rk r (Array.mem_toList_iff.mpr hr) r List.mem_cons_self⟩
      · cases ran
  · cases ran

/-- **A group's conversion declares the ingress key of each of its names.** -/
theorem convert_declares {gr : Group} {c : Converted} (h : convert gr = .ok c) :
    ∀ n ∈ gr.names, ingressKey n ∈ convKeys c := by
  cases gr with
  | «inductive» types ctors recs =>
    obtain ⟨rb, rfl, tk, ck, rk⟩ := convertInductive_declares h
    intro n hn
    show ingressKey n ∈ rb.types.toList.map (·.1.name) ++ rb.ctors.toList.map (·.1.name) ++
      rb.recs.toList.map (·.1.name)
    rcases Array.mem_append.mp hn with hn | hn
    · rcases Array.mem_append.mp hn with hn | hn
      · obtain ⟨v, hv, rfl⟩ := Array.mem_map.mp hn
        obtain ⟨e, he, hname⟩ := tk v hv
        exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.mpr ⟨e, Array.mem_toList_iff.mpr he, hname⟩))
      · obtain ⟨cs, hcs, hn⟩ := Array.mem_flatMap.mp hn
        obtain ⟨c, hc, rfl⟩ := Array.mem_map.mp hn
        obtain ⟨e, he, hname⟩ := ck cs hcs c hc
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_map.mpr ⟨e, Array.mem_toList_iff.mpr he, hname⟩))
    · obtain ⟨r, hr, rfl⟩ := Array.mem_map.mp hn
      obtain ⟨e, he, hname⟩ := rk r hr
      exact List.mem_append_right _ (List.mem_map.mpr ⟨e, Array.mem_toList_iff.mpr he, hname⟩)
  | definitions members =>
    obtain ⟨ms, rfl, hk⟩ := convertDefinitions_declares h
    intro n hn
    obtain ⟨ci, hci, rfl⟩ := Array.mem_map.mp hn
    obtain ⟨m, hm, hname⟩ := hk ci hci
    exact List.mem_map.mpr ⟨m, Array.mem_toList_iff.mpr hm, hname⟩
  | «axiom» v =>
    unfold convert at h
    dsimp only at h
    rcases ReaderUnits.ite_ok h with h | h
    · exact (ReaderUnits.fail_bind h).elim
    · obtain ⟨ks, -, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro n hn
      have : n = v.cnst.name := by simpa [Group.names] using hn
      subst this
      exact List.mem_singleton.mpr rfl
  | quot v =>
    unfold convert at h
    obtain ⟨ks, -, h⟩ := except_bind_ok.mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro n hn
    have : n = v.cnst.name := by simpa [Group.names] using hn
    subst this
    exact List.mem_singleton.mpr rfl
  | invalid _ e => cases h

/-- The hint override keeps a converted group's keys. -/
theorem convKeys_withHints (hints : CName .source → Option ReducibilityHint) (c : Converted) :
    convKeys (c.withHints hints) = convKeys c := by
  cases c with
  | definitions ms =>
    simp only [Converted.withHints, convKeys, Array.toList_map, List.map_map]
    refine List.map_congr_left fun m _ => ?_
    simp only [Function.comp]
    split <;> rfl
  | _ => rfl

/-- `canonInfo` at a recursor keeps its name, whatever it returns. -/
theorem canonRec_name (c : CVal .source) (rc : RecCounts) (rules : List (Ix.Kernel.RecRule .source)) :
    (match canonInfo (.recInfo c 0 0 rules) with
      | .recInfo c' _ _ rules' => (c', rc, rules')
      | _ => (c, rc, rules)).1.name = c.name := by
  have hn := ReaderUnits.canonInfo_name (.recInfo c 0 0 rules)
  split
  · rename_i c' _ _ _ heq
    rw [heq] at hn
    exact hn
  · rfl

/-- **The quotient renaming renames a converted group's keys.** -/
theorem convKeys_quotient {ρ : FiberMap} {c : Converted} {k : CName .source} (hk : k ∈ convKeys c) :
    Key.subst ρ k ∈ convKeys (c.quotient ρ) := by
  cases c with
  | «inductive» rb =>
    change k ∈ BlockRead.names rb at hk
    show Key.subst ρ k ∈ BlockRead.names (BlockRead.canon (BlockRead.substKeys ρ rb))
    unfold BlockRead.names at hk ⊢
    rcases List.mem_append.mp hk with hk | hk
    · rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨⟨c, p, i⟩, he, rfl⟩ := List.mem_map.mp hk
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr
          ⟨_, Array.mem_toList_iff.mpr (Array.mem_map_of_mem (Array.mem_map_of_mem
            (Array.mem_toList_iff.mp he))), rfl⟩))
      · obtain ⟨⟨c, p, f⟩, he, rfl⟩ := List.mem_map.mp hk
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr
          ⟨_, Array.mem_toList_iff.mpr (Array.mem_map_of_mem (Array.mem_map_of_mem
            (Array.mem_toList_iff.mp he))), rfl⟩))
    · obtain ⟨⟨c, rc, rules⟩, he, rfl⟩ := List.mem_map.mp hk
      exact List.mem_append_right _ (List.mem_map.mpr
        ⟨_, Array.mem_toList_iff.mpr (Array.mem_map_of_mem (Array.mem_map_of_mem
          (Array.mem_toList_iff.mp he))), canonRec_name _ rc _⟩)
  | definitions ms =>
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hk
    exact List.mem_map.mpr ⟨_, Array.mem_toList_iff.mpr (Array.mem_map_of_mem (Array.mem_map_of_mem
      (Array.mem_toList_iff.mp hm))), rfl⟩
  | «axiom» cv =>
    rw [List.mem_singleton.mp hk]
    exact List.mem_singleton.mpr rfl
  | quot q cv =>
    rw [List.mem_singleton.mp hk]
    exact List.mem_singleton.mpr rfl

/-! ## 3. Lowering declares a converted group's keys -/

/-- **A converted group's lowering declares each of its keys.** -/
theorem lower_declares {st : State .source} {c : Converted} {r : Read .source} (h : lower st c = .ok r) :
    ∀ k ∈ convKeys c, ∃ d ∈ r.decls.toList, k ∈ d.names := by
  cases c with
  | «inductive» rb =>
    obtain ⟨gens, d, hd, -, hn⟩ := ReaderUnits.lowerInductive_decls h
    intro k hk
    refine ⟨d, by rw [hd]; exact List.mem_append_right _ List.mem_cons_self, ?_⟩
    rw [hn]
    exact hk
  | definitions ms =>
    unfold lower at h
    delta Ix.LeanIngress.lower.match_6 at h
    dsimp only at h
    split at h
    · rename_i hsz
      obtain ⟨l⟩ := ms
      obtain _ | ⟨m, _ | ⟨_, _⟩⟩ := l
      · cases hsz
      · simp only at h
        obtain ⟨⟨decl, rw⟩, hd, h⟩ := except_bind_ok.mp h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro k hk
        have hk' : k = m.cv.name := by simpa [convKeys] using hk
        subst hk'
        refine ⟨decl, by simp, ?_⟩
        rw [ReaderUnits.lowerDefinition_names hd]
        exact List.mem_singleton.mpr rfl
      · simp at hsz
    · obtain ⟨s, hs, h⟩ := except_bind_ok.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have covered := (forIn_covers (fun s => s.2.1) (fun m => [m])
        (fun (m : DefMember) (d : CDecl .source) => m.cv.name ∈ d.names) _ _
        (fun m _ s q hq => by
          obtain ⟨⟨decl, rw⟩, hd, hq⟩ := except_bind_ok.mp hq
          have hn := ReaderUnits.lowerDefinition_names hd
          dsimp only at hq
          split at hq <;> split at hq <;>
          · simp only [pure, Except.pure, Except.ok.injEq] at hq
            subst hq
            refine ⟨_, rfl, fun e he => Array.mem_push_of_mem _ he, fun y hy => ?_⟩
            rw [List.mem_singleton] at hy
            subst hy
            refine ⟨_, Array.mem_push_self, ?_⟩
            rw [hn]
            exact List.mem_singleton.mpr rfl) hs).2
      intro k hk
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hk
      obtain ⟨d, hd, hk⟩ := covered m hm m List.mem_cons_self
      exact ⟨d, Array.mem_toList_iff.mpr hd, hk⟩
  | «axiom» cv =>
    unfold lower at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro k hk
    exact ⟨_, List.mem_singleton.mpr rfl, hk⟩
  | quot kind cv =>
    unfold lower at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro k hk
    exact ⟨_, List.mem_singleton.mpr rfl, hk⟩

/-! ## 4. The collapse drops no name -/

/-- Every name of a kept block is owned. -/
abbrev BlockOwned (s : CollapseState) (kb : KeptBlocks) : Prop :=
  ∀ k : CName .source, (kb.blockOf[k]?).isSome = true → (s.owner[k]?).isSome = true

/-- A name a kept block's push records is one of its names or was recorded before. -/
theorem push_blockOf {kb : KeptBlocks} {rb : BlockRead .source} {k : CName .source}
    (h : ((kb.push rb).blockOf[k]?).isSome = true) :
    k ∈ BlockRead.names rb ∨ (kb.blockOf[k]?).isSome = true := by
  obtain ⟨blocks, blockOf⟩ := kb
  have fold : ∀ (l : List (CName .source)) (m : Std.HashMap (CName .source) Nat) (i : Nat),
      ((l.foldl (fun (m : Std.HashMap (CName .source) Nat) (n : CName .source) => m.insert n i) m)[k]?).isSome = true →
        k ∈ l ∨ (m[k]?).isSome = true := by
    intro l
    induction l with
    | nil => intro m i h; exact .inr h
    | cons n l ih =>
      intro m i h
      rw [List.foldl_cons] at h
      rcases ih _ i h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · rw [Std.HashMap.getElem?_insert] at h
        split at h
        · rename_i hnk
          exact .inl (by rw [← beq_iff_eq.mp hnk]; exact List.mem_cons_self)
        · exact .inr h
  exact fold _ _ _ h

/-- An inductive group that aliases kept block `i` has every name recorded at `i`. -/
theorem alias_names {kb : KeptBlocks} {s : CollapseState} {first : CName .source}
    {rb : BlockRead .source} {i : Nat} (h : kb.alias s first rb = .ok (some i)) :
    ∀ n ∈ BlockRead.names rb, kb.blockOf[n]? = some i := by
  unfold KeptBlocks.alias at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hall
        cases h
        intro n hn
        exact beq_iff_eq.mp (List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hall).1 n hn)
      · cases h
    · cases h

/-- An alias step is an inductive group that aliases a kept block. -/
theorem collapseGroup_alias_inv {st : State .source} {s s' : CollapseState} {kb kb' : KeptBlocks}
    {first : CName .source} {pos i : Nat} {c : Except ReadError Converted}
    (h : collapseGroup st s kb first pos c = .alias i s' kb') :
    ∃ rb, c = .ok (.inductive rb) ∧ kb.alias s first rb = .ok (some i) := by
  cases c with
  | error e => simp [collapseGroup] at h
  | ok c =>
    unfold collapseGroup at h
    dsimp only at h
    split at h
    · cases h
    · rename_i k hk
      cases h
      cases c with
      | «inductive» rb => exact ⟨rb, rfl, hk⟩
      | _ => cases hk
    · split at h
      · cases h
      · split at h <;> cases h

/-- A lowered step's kept blocks: a lowered inductive group's block is recorded. -/
theorem collapseGroup_lowered_kb {st : State .source} {s s' : CollapseState} {kb kb' : KeptBlocks}
    {first : CName .source} {pos : Nat} {c : Except ReadError Converted} {r : Read .source}
    {dropped : Array (CName .source)}
    (h : collapseGroup st s kb first pos c = .lowered s' kb' r dropped) :
    ∃ conv, c = .ok conv ∧ kb' = (match conv with | .inductive rb => kb.push rb | _ => kb) := by
  cases c with
  | error e => simp [collapseGroup] at h
  | ok c =>
    unfold collapseGroup at h
    dsimp only at h
    split at h
    · cases h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
          exact ⟨c, rfl, rfl⟩

/-- **Along quotient Source's lowering trace, every scheduled group converted and
its keys are owned**, and every name of a kept block is owned. -/
theorem trace_declares {g : Graph} {start st : State .source} {xs rs s kb}
    (h : Trace g start xs rs st s kb) :
    BlockOwned s kb ∧ ∀ x ∈ xs, ∃ conv, x.1.2 = .ok conv ∧
      ∀ k ∈ convKeys conv, (s.owner[k]?).isSome = true := by
  induction h with
  | nil => exact ⟨fun k hk => by simp at hk, fun x hx => nomatch hx⟩
  | @«alias» xs rs st s kb x i ht hcol ih =>
    obtain ⟨owned, covered⟩ := ih
    refine ⟨owned, fun y hy => ?_⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact covered y hy
    · rw [List.mem_singleton] at hy
      subst hy
      obtain ⟨rb, hc, ha⟩ := collapseGroup_alias_inv hcol
      refine ⟨.inductive rb, hc, fun k hk => owned k ?_⟩
      rw [alias_names ha k hk]
      rfl
  | @lowered xs rs st s kb x s' kb' conv raw r dropped ht hc hl hr hcol ih =>
    obtain ⟨owned, covered⟩ := ih
    obtain ⟨ext, all, -⟩ := collapseRead_facts hr
    have newKeys : ∀ k ∈ convKeys conv, (s'.owner[k]?).isSome = true := by
      intro k hk
      obtain ⟨d, hd, hkd⟩ := lower_declares hl k hk
      exact all d hd k hkd
    obtain ⟨conv', hc', hkb⟩ := collapseGroup_lowered_kb hcol
    rw [hc] at hc'
    cases hc'
    refine ⟨fun k hk => ?_, fun y hy => ?_⟩
    · subst hkb
      cases conv with
      | «inductive» rb =>
        rcases push_blockOf hk with hk | hk
        · exact newKeys k hk
        · exact ext.isSome (owned k hk)
      | definitions ms => exact ext.isSome (owned k hk)
      | «axiom» cv => exact ext.isSome (owned k hk)
      | quot q cv => exact ext.isSome (owned k hk)
    · rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨c, hcy, keys⟩ := covered y hy
        exact ⟨c, hcy, fun k hk => ext.isSome (keys k hk)⟩
      · rw [List.mem_singleton] at hy
        subst hy
        exact ⟨conv, hc, newKeys⟩

/-! ## 5. The prepared stream declares every stored name's quotient key -/

/-- **Quotient Source's prepared stream declares every name the environment stores
a constant under**, under its quotient key. -/
theorem prepared_declares {ρ : FiberMap} {hints : CName .source → Option ReducibilityHint}
    {pre : Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (Declaration .source)} (h : prepareSourceCollapsed ρ hints pre env blocks = .ok ds)
    {n : Ix.Name} {ci : Ix.ConstantInfo} (hn : (n, ci) ∈ env.consts.toList) :
    ∃ d ∈ ds.toList, Key.subst ρ (ingressKey n) ∈ d.names := by
  obtain ⟨fin, decls, hl, -, hds⟩ := prepareSourceCollapsed_keepsPrelude h
  obtain ⟨rs, s, kb, ht, hkept, -, -⟩ := lowerAllCollapsed_trace hl
  obtain ⟨gr, hgr, hname⟩ := stored_grouped env blocks hn
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hgr
  have hgroups : (graphCollapsed ρ hints env blocks).groups = groupsOf env blocks := by
    show (graph env blocks).groups = _
    exact ReaderUnits.graph_groups env blocks
  have hi' : i < (graphCollapsed ρ hints env blocks).groups.size := by rw [hgroups]; exact hi
  obtain ⟨c, hcmem⟩ := scheduleOf_complete _ hi'
  obtain ⟨j, hj, hjeq⟩ := Array.getElem_of_mem hcmem
  have hx : ((i, c), j) ∈ (scheduleOf (graphCollapsed ρ hints env blocks)).zipIdx.toList :=
    Array.mem_toList_iff.mpr (Array.mem_zipIdx_iff_getElem?.mpr (by simp [hj, hjeq]))
  obtain ⟨-, covered⟩ := trace_declares ht
  obtain ⟨conv, hconv, keys⟩ := covered _ hx
  have hcv := ReaderUnits.scheduleOf_ok (Array.mem_toList_iff.mpr hcmem) hconv
  obtain ⟨gr', c0, hgr', hc0, rfl⟩ := SourceTrace.graph_conversion hcv
  have same : gr' = (groupsOf env blocks)[i] := by
    rw [ReaderUnits.graph_groups] at hgr'
    rw [Array.getElem?_eq_getElem hi] at hgr'
    exact (Option.some.inj hgr').symm
  subst same
  have hk := convKeys_quotient (ρ := ρ)
    (by rw [convKeys_withHints hints]; exact convert_declares hc0 n hname)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (keys _ hk)
  obtain ⟨d, hd, hkd⟩ := (trace_ownerExact ht _ v).mp hv
  have hdecl : d ∈ decls.toList := by
    rw [← hkept]
    exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hd)
  obtain ⟨extra, -, perm⟩ := Frontend.preparePrelude_perm pre.ix decls
  refine ⟨d, ?_, hkd⟩
  rw [hds]
  exact perm.mem_iff.mpr (List.mem_append_left _ hdecl)

/-- Quotient Source's checked stream, over any bundle source and evidence, is its
collapse's stream. -/
theorem preparedAtUsing_collapsed {bundle : Except String Ix.RoleEvidence.Bundle}
    {ev : Ix.Kernel.Evidences .source} {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {hints : CName .source → Option ReducibilityHint} {pre : Prelude .source} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {ds : Array (Declaration .source)}
    (h : prepareSourceCollapsedAtUsing bundle ev ixe t hints pre env blocks = .ok ds) :
    prepareSourceCollapsed (fiberAliasAt ixe (roleAtMap t)) hints pre env blocks = .ok ds := by
  unfold prepareSourceCollapsedAtUsing at h
  split at h
  · cases h
  · rename_i ds' hds
    split at h
    · cases h
    · cases h
      exact hds

/-- Quotient Source's stream at a compiled artifact is its collapse's stream, checked. -/
theorem preparedAt_collapsed {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {hints : CName .source → Option ReducibilityHint} {pre : Prelude .source} {env : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {ds : Array (Declaration .source)}
    (h : prepareSourceCollapsedAt ixe t hints pre env blocks = .ok ds) :
    prepareSourceCollapsed (fiberAliasAt ixe (roleAtMap t)) hints pre env blocks = .ok ds :=
  preparedAtUsing_collapsed h

/-- **At a compiled artifact, quotient Source's prepared stream declares every name
the closure stores a constant under**, under its quotient key. -/
theorem preparedAt_declares {ixe : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {hints : CName .source → Option ReducibilityHint} {pre : Prelude .source} {sub : Ix.Environment}
    {blocks : Ix.CondensedBlocks} {ds : Array (Declaration .source)}
    (h : prepareSourceCollapsedAt ixe t hints pre sub blocks = .ok ds)
    {n : Ix.Name} {ci : Ix.ConstantInfo} (hn : (n, ci) ∈ sub.consts.toList) :
    ∃ d ∈ ds.toList, Key.subst (fiberAliasAt ixe (roleAtMap t)) (ingressKey n) ∈ d.names :=
  prepared_declares (preparedAt_collapsed h) hn

/-- info: 'Ix.Cert.SourceDeclares.preparedAt_declares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms preparedAt_declares

end Ix.Cert.SourceDeclares
