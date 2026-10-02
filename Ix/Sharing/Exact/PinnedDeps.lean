/-
  Nearest stored descendants without a hash set per term.

  `pinnedDeps` walks down from every stored term to its nearest stored
  descendants, keeping the visited terms in a fresh `Std.HashSet` per term.
  `pinnedDepsFast` makes the same walks (same stack, same order, same fuel)
  with the visited terms of the `k`-th walk marked `k + 1` in one stamp array
  shared by all walks, so a walk costs its own region only.
  `pinnedDeps_eq_fast : @pinnedDeps = @pinnedDepsFast` (`@[csimp]`) holds for
  every input: terms outside the DAG are never stored and have no children, so
  whether a walk remembers them changes neither its stack nor its output.
-/
module

public import Ix.Sharing.Exact.Uniform
import all Ix.Sharing.Exact.Uniform
import all Ix.Sharing.Exact.Dag
import Std.Data.HashSet.Lemmas

public section

namespace Ix.Sharing.Exact

/-- One walk of `pinnedDeps` (its inner loop), visited terms as a hash set. -/
def pinnedWalkSpec (dag : Dag) (isStored : Array Bool) :
    Nat → Std.HashSet Nat → Array Nat → Array Nat → Std.HashSet Nat × Array Nat × Array Nat
  | 0, seen, stack, out => (seen, stack, out)
  | fuel + 1, seen, stack, out =>
    (stack.back?).elim (seen, stack, out) fun u =>
      if seen.contains u then pinnedWalkSpec dag isStored fuel seen stack.pop out
      else if isStored[u]! then
        pinnedWalkSpec dag isStored fuel (seen.insert u) stack.pop (out.push u)
      else pinnedWalkSpec dag isStored fuel (seen.insert u) (stack.pop ++ (dag.node u).children) out

/-- One walk with the visited terms marked `mark` in `stamp`. -/
def pinnedWalk (dag : Dag) (isStored : Array Bool) (mark : Nat) :
    Nat → Array Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, stamp, out => (stamp, out)
  | fuel + 1, stack, stamp, out =>
    (stack.back?).elim (stamp, out) fun u =>
      if stamp[u]! == mark then pinnedWalk dag isStored mark fuel stack.pop stamp out
      else if isStored[u]! then
        pinnedWalk dag isStored mark fuel stack.pop (stamp.set! u mark) (out.push u)
      else pinnedWalk dag isStored mark fuel (stack.pop ++ (dag.node u).children)
        (stamp.set! u mark) out

/-- One term of `pinnedDepsFast`: walk from `t` with mark `k + 1`. -/
def pinnedDepsStep (dag : Dag) (isStored : Array Bool) (n : Nat)
    (acc : Std.HashMap Nat (Array Nat) × Array Nat × Nat) (t : Nat) :
    Std.HashMap Nat (Array Nat) × Array Nat × Nat :=
  match acc with
  | (deps, stamp, k) =>
    match pinnedWalk dag isStored (k + 1) (4 * n + 4) (dag.node t).children stamp #[] with
    | (stamp, out) => (deps.insert t out, stamp, k + 1)

/-- `pinnedDeps` with one stamp array for all walks. -/
def pinnedDepsFast (dag : Dag) (stored : Array Nat) : Std.HashMap Nat (Array Nat) :=
  let n := dag.size
  let isStored := stored.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  (stored.foldl (pinnedDepsStep dag isStored n) ({}, Array.replicate n 0, 0)).1

/-! ## The loop of the specification -/

/-- One step of the inner loop of `pinnedDeps`. -/
def pinnedStep (dag : Dag) (isStored : Array Bool) (seen : Std.HashSet Nat)
    (stack out : Array Nat) : Id (ForInStep (Std.HashSet Nat × Array Nat × Array Nat)) :=
  (stack.back?).elim (pure (.done (seen, stack, out))) fun u =>
    if seen.contains u then pure (.yield (seen, stack.pop, out))
    else if isStored[u]! then pure (.yield (seen.insert u, stack.pop, out.push u))
    else pure (.yield (seen.insert u, stack.pop ++ (dag.node u).children, out))

theorem forIn_pinnedStep (dag : Dag) (isStored : Array Bool)
    (f : Nat → Std.HashSet Nat × Array Nat × Array Nat →
      Id (ForInStep (Std.HashSet Nat × Array Nat × Array Nat)))
    (hf : ∀ x seen stack out, f x (seen, stack, out) = pinnedStep dag isStored seen stack out) :
    ∀ (fuel s : Nat) (seen : Std.HashSet Nat) (stack out : Array Nat),
      forIn (List.range' s fuel) (seen, stack, out) f =
        pinnedWalkSpec dag isStored fuel seen stack out := by
  intro fuel
  induction fuel with
  | zero => intro s seen stack out; rfl
  | succ fuel ih =>
    intro s seen stack out
    rw [List.range'_succ, List.forIn_cons, hf]
    unfold pinnedStep pinnedWalkSpec
    cases stack.back? with
    | none => rfl
    | some u =>
      simp only [Option.elim_some]
      by_cases hs : seen.contains u = true
      · simp only [hs, ite_true]
        exact ih _ _ _ _
      · simp only [hs, Bool.false_eq_true, ite_false]
        split
        · exact ih _ _ _ _
        · exact ih _ _ _ _

/-! ## The walks agree -/

/-- The visited set and the stamps agree on the DAG's terms. -/
def WalkRel (n mark : Nat) (seen : Std.HashSet Nat) (stamp : Array Nat) : Prop :=
  stamp.size = n ∧ ∀ u, u < n → (seen.contains u = true ↔ stamp[u]! = mark)

theorem pinnedWalk_eq (dag : Dag) (isStored : Array Bool) (hiS : isStored.size = dag.size)
    (mark : Nat) (hmark : 0 < mark) :
    ∀ (fuel : Nat) (seen : Std.HashSet Nat) (stack stamp out : Array Nat),
      WalkRel dag.size mark seen stamp →
      (pinnedWalkSpec dag isStored fuel seen stack out).2.2 =
          (pinnedWalk dag isStored mark fuel stack stamp out).2 ∧
        (pinnedWalk dag isStored mark fuel stack stamp out).1.size = dag.size ∧
        ∀ u, u < dag.size → (pinnedWalk dag isStored mark fuel stack stamp out).1[u]! = stamp[u]! ∨
          (pinnedWalk dag isStored mark fuel stack stamp out).1[u]! = mark := by
  intro fuel
  induction fuel with
  | zero => intro seen stack stamp out h; exact ⟨rfl, h.1, fun u _ => Or.inl rfl⟩
  | succ fuel ih =>
    intro seen stack stamp out h
    obtain ⟨hsz, hrel⟩ := h
    unfold pinnedWalkSpec pinnedWalk
    cases stack.back? with
    | none => exact ⟨rfl, hsz, fun u _ => Or.inl rfl⟩
    | some u =>
      simp only [Option.elim_some]
      by_cases hu : u < dag.size
      · -- a term of the DAG: the two visited sets agree on it
        by_cases hs : seen.contains u = true
        · have hm : (stamp[u]! == mark) = true := by simpa using (hrel u hu).mp hs
          simp only [hs, ite_true, hm]
          exact ih _ _ _ _ ⟨hsz, hrel⟩
        · have hm : (stamp[u]! == mark) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]
            exact fun h' => hs ((hrel u hu).mpr h')
          simp only [hs, Bool.false_eq_true, ite_false, hm]
          have hrel' : WalkRel dag.size mark (seen.insert u) (stamp.set! u mark) := by
            refine ⟨by simp [hsz], fun v hv => ?_⟩
            rw [Std.HashSet.contains_insert]
            by_cases hvu : v = u
            · subst hvu
              simp only [beq_self_eq_true, Bool.true_or, true_iff]
              simp only [Array.set!_eq_setIfInBounds, getElem!_def]
              rw [Array.getElem?_setIfInBounds]
              simp [hsz, hv]
            · have : (u == v) = false := by
                simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h' => hvu h'.symm
              rw [this, Bool.false_or, hrel v hv]
              simp only [Array.set!_eq_setIfInBounds, getElem!_def]
              rw [Array.getElem?_setIfInBounds]
              simp [Ne.symm hvu]
          have hkeep : ∀ (r : Array Nat × Array Nat), (r.1.size = dag.size ∧
              ∀ v, v < dag.size → r.1[v]! = (stamp.set! u mark)[v]! ∨ r.1[v]! = mark) →
              r.1.size = dag.size ∧ ∀ v, v < dag.size → r.1[v]! = stamp[v]! ∨ r.1[v]! = mark := by
            intro r ⟨h1, h2⟩
            refine ⟨h1, fun v hv => ?_⟩
            rcases h2 v hv with h3 | h3
            · rw [h3]
              by_cases hvu : v = u
              · subst hvu
                right
                simp only [Array.set!_eq_setIfInBounds, getElem!_def]
                rw [Array.getElem?_setIfInBounds]
                simp [hsz, hv]
              · left
                simp only [Array.set!_eq_setIfInBounds, getElem!_def]
                rw [Array.getElem?_setIfInBounds]
                simp [Ne.symm hvu]
            · exact Or.inr h3
          split
          · obtain ⟨e1, e2, e3⟩ := ih _ _ _ _ hrel'
            exact ⟨e1, hkeep _ ⟨e2, e3⟩⟩
          · obtain ⟨e1, e2, e3⟩ := ih _ _ _ _ hrel'
            exact ⟨e1, hkeep _ ⟨e2, e3⟩⟩
      · -- a term outside the DAG: not stored, no children, no stamp
        have hnode : (dag.node u).children = #[] := by
          unfold Dag.node
          rw [Array.getElem?_eq_none (by simp only [Dag.size] at hu; omega)]
          rfl
        have hst : isStored[u]! = false := by
          rw [getElem!_neg isStored u (by omega)]
          rfl
        have hstamp : stamp[u]! = 0 := by
          rw [getElem!_neg stamp u (by omega)]
          rfl
        have hm : (stamp[u]! == mark) = false := by
          rw [hstamp]; simp only [beq_eq_false_iff_ne, ne_eq]; omega
        have hset : stamp.set! u mark = stamp := by
          simp only [Array.set!_eq_setIfInBounds]
          exact Array.setIfInBounds_eq_of_size_le (by omega)
        simp only [hm, hst, Bool.false_eq_true, ite_false, hnode, Array.append_empty, hset]
        have hrel' : WalkRel dag.size mark (seen.insert u) stamp := by
          refine ⟨hsz, fun v hv => ?_⟩
          rw [Std.HashSet.contains_insert]
          have : (u == v) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; omega
          rw [this, Bool.false_or]
          exact hrel v hv
        by_cases hs : seen.contains u = true
        · simp only [hs, ite_true]
          exact ih _ _ _ _ ⟨hsz, hrel⟩
        · simp only [hs, Bool.false_eq_true, ite_false]
          exact ih _ _ _ _ hrel'

/-! ## All walks -/

/-- `pinnedDeps` with its inner loop body written as `pinnedStep`. -/
def pinnedDepsAlt (dag : Dag) (stored : Array Nat) : Std.HashMap Nat (Array Nat) := Id.run do
  let n := dag.size
  let isStored := stored.foldl (fun acc t => acc.set! t true) (Array.replicate n false)
  let mut deps : Std.HashMap Nat (Array Nat) := {}
  for t in stored do
    let r ← forIn [0:4 * n + 4] ((∅ : Std.HashSet Nat), (dag.node t).children, (#[] : Array Nat))
      fun _ s => pinnedStep dag isStored s.1 s.2.1 s.2.2
    deps := deps.insert t r.2.2
  return deps

theorem pinnedDeps_eq_alt (dag : Dag) (stored : Array Nat) :
    pinnedDeps dag stored = pinnedDepsAlt dag stored := by
  unfold pinnedDeps pinnedDepsAlt
  simp only [Id.run]
  congr 1
  congr 1
  funext t deps
  congr 1
  · congr 1
    funext x s
    obtain ⟨seen, stack, out⟩ := s
    unfold pinnedStep
    simp only
    cases stack.back? <;> rfl

theorem pinnedDepsAlt_eq_foldl (dag : Dag) (stored : Array Nat) :
    pinnedDepsAlt dag stored =
      stored.foldl (fun deps t => deps.insert t
        (pinnedWalkSpec dag (stored.foldl (fun acc t => acc.set! t true)
          (Array.replicate dag.size false)) (4 * dag.size + 4) ∅ (dag.node t).children #[]).2.2) {} := by
  unfold pinnedDepsAlt
  have key := forIn_pinnedStep dag (stored.foldl (fun acc t => acc.set! t true)
    (Array.replicate dag.size false))
    (fun _ s => pinnedStep dag (stored.foldl (fun acc t => acc.set! t true)
      (Array.replicate dag.size false)) s.1 s.2.1 s.2.2) (fun _ _ _ _ => rfl)
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', key]
  simp [Id.run]
  rfl

theorem pinnedDepsStep_eq (dag : Dag) (isStored : Array Bool) (n : Nat)
    (deps : Std.HashMap Nat (Array Nat)) (stamp : Array Nat) (k t : Nat) :
    pinnedDepsStep dag isStored n (deps, stamp, k) t =
      (deps.insert t (pinnedWalk dag isStored (k + 1) (4 * n + 4) (dag.node t).children stamp #[]).2,
       (pinnedWalk dag isStored (k + 1) (4 * n + 4) (dag.node t).children stamp #[]).1, k + 1) := by
  unfold pinnedDepsStep
  rfl

theorem pinnedDeps_foldl (dag : Dag) (isStored : Array Bool) (hiS : isStored.size = dag.size) :
    ∀ (l : List Nat) (deps : Std.HashMap Nat (Array Nat)) (stamp : Array Nat) (k : Nat),
      stamp.size = dag.size → (∀ u, u < dag.size → stamp[u]! ≤ k) →
      l.foldl (fun deps t => deps.insert t
          (pinnedWalkSpec dag isStored (4 * dag.size + 4) ∅ (dag.node t).children #[]).2.2) deps =
        (l.foldl (pinnedDepsStep dag isStored dag.size) (deps, stamp, k)).1 := by
  intro l
  induction l with
  | nil => intro deps stamp k _ _; rfl
  | cons t l ih =>
    intro deps stamp k hsz hle
    simp only [List.foldl_cons]
    rw [pinnedDepsStep_eq]
    obtain ⟨e1, e2, e3⟩ := pinnedWalk_eq dag isStored hiS (k + 1) (by omega) (4 * dag.size + 4)
      ∅ (dag.node t).children stamp #[]
      ⟨hsz, fun u hu => by
        simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_iff]
        have := hle u hu
        omega⟩
    rw [e1]
    apply ih _ _ _ e2
    intro u hu
    rcases e3 u hu with h | h
    · rw [h]; have := hle u hu; omega
    · rw [h]; exact Nat.le_refl _

theorem foldl_set_size (stored : List Nat) (A : Array Bool) :
    (stored.foldl (fun acc t => acc.set! t true) A).size = A.size := by
  induction stored generalizing A with
  | nil => rfl
  | cons t l ih => simp only [List.foldl_cons]; rw [ih]; simp

theorem pinnedDeps_eq_fast_apply (dag : Dag) (stored : Array Nat) :
    pinnedDeps dag stored = pinnedDepsFast dag stored := by
  rw [pinnedDeps_eq_alt, pinnedDepsAlt_eq_foldl]
  unfold pinnedDepsFast
  simp only
  have hiS : (stored.foldl (fun acc t => acc.set! t true) (Array.replicate dag.size false)).size =
      dag.size := by
    rw [← Array.foldl_toList, foldl_set_size]; simp
  generalize stored.foldl (fun acc t => acc.set! t true) (Array.replicate dag.size false) =
    isStored at hiS ⊢
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact pinnedDeps_foldl dag _ hiS stored.toList {} (Array.replicate dag.size 0) 0 (by simp)
    (fun u hu => by
    rw [getElem!_pos _ u (by simpa using hu)]; simp)

@[csimp] theorem pinnedDeps_eq_fast : @pinnedDeps = @pinnedDepsFast := by
  funext dag stored
  exact pinnedDeps_eq_fast_apply dag stored

end Ix.Sharing.Exact

end
