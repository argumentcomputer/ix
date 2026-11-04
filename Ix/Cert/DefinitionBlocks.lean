import Ix.Cert.ReaderUnits
import Ix.Cert.CtxAgree
import Ix.CompileCert.SourceConstructorPositions

/-! # Definition groups of several members

Quotient Source lowers a definition group of several members only in a dependency order of
its members (`Ix.Kernel.Reader.defOrder` over which members' converted terms mention which
members), as the reader reads a definition block. A group in which every member mentions
another member has no such order (`defOrder_none`), so quotient Source declines it
(`convertDefinitions_source`: a group it converts has a member whose converted type and
value mention no other member).

A definition block of a compiled closure is a component of the reference graph, and in a
component of several members every member references another one; so no closure quotient
Source accepts holds a definition block of several members, and the reader's streams never
read one. -/

namespace Ix.Cert.DefinitionBlocks

open Ix.Kernel Ix.Kernel.Reader
open Ix.LeanIngress (Numbering ingressKey ingressExpr)

/-! ## The dependency order -/

theorem inner_stuck (deps : Array (Std.HashSet Nat))
    (h : ∀ i < deps.size, ∃ j ∈ deps[i]!.toList, j ≠ i ∧ j < deps.size) :
    ∀ (l : List Nat), (∀ i ∈ l, i < deps.size) →
      (forIn (m := Id) l (Array.replicate deps.size false, (#[] : Array Nat), false)
        fun i (s : Array Bool × Array Nat × Bool) =>
          if (!s.1[i]! && deps[i]!.toList.all fun j => j == i || decide (j ≥ deps.size) || s.1[j]!) = true then
            pure (ForInStep.yield (s.1.set! i true, s.2.1.push i, true))
          else pure (ForInStep.yield (s.1, s.2.1, s.2.2))) =
        (Array.replicate deps.size false, #[], false)
  | [], _ => rfl
  | i :: l, hl => by
    rw [List.forIn_cons]
    have hi := hl i List.mem_cons_self
    obtain ⟨j, hj, hji, hjn⟩ := h i hi
    have hrep : (Array.replicate deps.size false)[j]! = false := by
      rw [getElem!_pos _ j (by simpa using hjn)]; simp
    have hall : (deps[i]!.toList.all fun j => j == i || decide (j ≥ deps.size) ||
        (Array.replicate deps.size false)[j]!) = false := by
      rw [Bool.eq_false_iff]
      intro hall
      have := List.all_eq_true.mp hall j hj
      simp only [hrep, Bool.or_false, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      omega
    simp only [hall, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact inner_stuck deps h l (fun i hi => hl i (List.mem_cons_of_mem _ hi))

/-- **No dependency order when every member depends on another one.** -/
theorem defOrder_none (deps : Array (Std.HashSet Nat)) (hn : 0 < deps.size)
    (h : ∀ i < deps.size, ∃ j ∈ deps[i]!.toList, j ≠ i ∧ j < deps.size) : defOrder deps = none := by
  unfold defOrder
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hsize : [:deps.size].size = deps.size := by simp [Std.Legacy.Range.size]
  rw [hsize]
  obtain ⟨k, hk⟩ : ∃ k, deps.size = k + 1 := ⟨deps.size - 1, by omega⟩
  have hl : ∀ i ∈ List.range' 0 deps.size, i < deps.size := by
    intro i hi; simp [List.mem_range'] at hi; omega
  have hrange : List.range' 0 deps.size = 0 :: List.range' 1 k := by rw [hk, List.range'_succ]
  rw [hrange] at hl ⊢
  rw [List.forIn_cons]
  dsimp only
  rw [inner_stuck deps h _ hl]
  simp only [hk]
  rfl

/-! ## Lists -/

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ k (h : k < l.length) (h' : k < l'.length),
      R l[k] l'[k]
  | _, _, .nil, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _, _, .cons hab rest, 0, _, _ => hab
  | _, _, .cons _ rest, k + 1, h, h' => forall₂_getElem rest k (by simpa using h) (by simpa using h')

theorem flatMap_pair_length {α β : Type} (f g : α → β) (l : List α) :
    (l.flatMap fun x => [f x, g x]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]; omega

theorem flatMap_pair_getElem? {α β : Type} (f g : α → β) :
    ∀ (l : List α) (i : Nat),
      (l.flatMap fun x => [f x, g x])[2 * i]? = l[i]?.map f ∧
        (l.flatMap fun x => [f x, g x])[2 * i + 1]? = l[i]?.map g
  | [], _ => ⟨rfl, rfl⟩
  | x :: l, 0 => ⟨rfl, rfl⟩
  | x :: l, i + 1 => by
    have := flatMap_pair_getElem? f g l i
    simp only [List.flatMap_cons, List.getElem?_cons_succ]
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by omega,
      List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
    simpa using this

/-- A member index enters the dependency set of the members it is found in. -/
theorem foldl_insert_mem {α : Type} (p : α → Bool) :
    ∀ (l : List (α × Nat)) (acc : Std.HashSet Nat) (x : α × Nat), x ∈ l → p x.1 = true →
      x.2 ∈ (l.foldl (fun acc y => if p y.1 = true then acc.insert y.2 else acc) acc)
  | [], _, _, h, _ => by cases h
  | y :: l, acc, x, h, hp => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · refine foldl_keep_mem p l _ x.2 ?_
      simp [hp]
    · exact foldl_insert_mem p l _ x h hp
where
  foldl_keep_mem (p : α → Bool) : ∀ (l : List (α × Nat)) (acc : Std.HashSet Nat) (j : Nat), j ∈ acc →
      j ∈ (l.foldl (fun acc y => if p y.1 = true then acc.insert y.2 else acc) acc)
    | [], _, _, h => h
    | y :: l, acc, j, h => by
      simp only [List.foldl_cons]
      apply foldl_keep_mem p l
      split
      · exact Std.HashSet.mem_insert.mpr (.inr h)
      · exact h

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {k : Nat} {a : α}, l[k]? = some a →
      ∃ b, l'[k]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons hab _, 0, _, h => by cases h; exact ⟨_, rfl, hab⟩
  | _, _, .cons _ rest, k + 1, _, h => forall₂_getElem? rest (by simpa using h)

theorem forall₂_length {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ rest => by simp [forall₂_length rest]

/-- The dependency sets of converted definition members, as `convertDefinitions` computes
them. -/
def depsOf (ms : Array Ix.LeanIngress.DefMember) : Array (Std.HashSet Nat) :=
  ms.map fun m => (ms.map (·.cv.name)).zipIdx.foldl (fun acc x =>
    if (Frontend.occursConstFast x.1 m.cv.type || Frontend.occursConstFast x.1 m.value) = true then
      acc.insert x.2 else acc) ∅

/-- **A dependency order of several converted members has a member that mentions no
other member.** -/
theorem defOrder_some_member (ms : Array Ix.LeanIngress.DefMember) {order : Array Nat}
    (h : defOrder (depsOf ms) = some order) (hsize : 2 ≤ ms.size) :
    ∃ i, ∃ _ : i < ms.size, ∀ j (hj : j < ms.size), j ≠ i →
      Frontend.occursConst ms[j].cv.name ms[i].cv.type = false ∧
        Frontend.occursConst ms[j].cv.name ms[i].value = false := by
  apply Classical.byContradiction
  intro hcon
  have hall : ∀ i < (depsOf ms).size, ∃ j ∈ (depsOf ms)[i]!.toList, j ≠ i ∧ j < (depsOf ms).size := by
    intro i hi
    simp only [depsOf, Array.size_map] at hi ⊢
    have hj : ∃ j, ∃ _ : j < ms.size, j ≠ i ∧
        (Frontend.occursConst ms[j].cv.name ms[i].cv.type = true ∨
          Frontend.occursConst ms[j].cv.name ms[i].value = true) := by
      apply Classical.byContradiction
      intro hno
      exact hcon ⟨i, hi, fun j hj hji => by
        refine ⟨?_, ?_⟩ <;> (rw [Bool.eq_false_iff]; intro ho; exact hno ⟨j, hj, hji, by simp [ho]⟩)⟩
    obtain ⟨j, hj, hji, ho⟩ := hj
    refine ⟨j, ?_, hji, hj⟩
    rw [Std.HashSet.mem_toList, getElem!_pos _ i (by simpa using hi), Array.getElem_map]
    rw [← Array.foldl_toList]
    refine foldl_insert_mem (fun n => Frontend.occursConstFast n ms[i].cv.type ||
      Frontend.occursConstFast n ms[i].value) _ ∅ (ms[j].cv.name, j) ?_ ?_
    · rw [Array.toList_zipIdx, List.mem_zipIdx_iff_getElem?]
      simp [hj]
    · simpa [CtxAgree.occursConstFast_eq] using ho
  rw [defOrder_none _ (by simp [depsOf]; omega) hall] at h
  cases h

/-! ## Quotient Source's definition groups -/

/-- **A definition group of several members that quotient Source converts has a member
whose converted type and value mention no other member.** -/
theorem convertDefinitions_source {members : Array Ix.ConstantInfo} {c : Ix.LeanIngress.Converted}
    (h : Ix.LeanIngress.convertDefinitions members = .ok c) (hsize : 2 ≤ members.size) :
    ∃ i, ∃ _ : i < members.size, ∃ (v : Ix.Expr) (σ τ : Numbering) (t' v' : CExpr .source),
      Ix.LeanIngress.definitionValue members[i] = some v ∧
      ingressExpr σ.pos members[i].getCnst.type = .ok t' ∧ ingressExpr τ.pos v = .ok v' ∧
      ∀ j (_ : j < members.size), j ≠ i →
        Frontend.occursConst (ingressKey members[j].getCnst.name) t' = false ∧
        Frontend.occursConst (ingressKey members[j].getCnst.name) v' = false := by
  unfold Ix.LeanIngress.convertDefinitions at h
  obtain ⟨shapes, hshapes, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
  have F := ReaderUnits.array_mapM_ok hshapes
  have hlen : shapes.size = members.size := by simpa using (forall₂_length F).symm
  have hshape : ∀ k (hk : k < members.size), ∃ s v, Ix.LeanIngress.definitionValue members[k] = some v ∧
      shapes.toList[k]? = some (members[k], s, v) := by
    intro k hk
    obtain ⟨y, hy, hf⟩ := forall₂_getElem? F (k := k) (a := members[k]) (by simp [hk])
    split at hf
    · rename_i s v hs hv
      simp only [pure, Except.pure, Except.ok.injEq] at hf
      exact ⟨s, v, hv, by rw [hy, hf]⟩
    · cases hf
  have hgt : shapes.size > 1 := by omega
  simp only [hgt, ↓reduceIte] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · obtain ⟨ks, hks, h⟩ := Ix.CompileCert.Loop.except_bind_ok.mp h
    have hms : ¬ (shapes.zipIdx.size ≤ 1) := by simp; omega
    simp only [Array.size_map, hms, ↓reduceIte] at h
    split at h
    · rename_i order hdef
      obtain ⟨i, hi, hfree⟩ := defOrder_some_member _ hdef (by simp; omega)
      simp only [Array.size_map, Array.size_zipIdx] at hi
      have hi' : i < members.size := by omega
      obtain ⟨s, v, hv, hsh⟩ := hshape i hi'
      have hitems := Ix.CompileCert.SourceConstructorPositions.exprsOf_spec hks
      have hlist : (Array.flatMap (fun x : Ix.ConstantInfo × (Ix.DefKind × Ix.DefinitionSafety ×
            ReducibilityHint) × Ix.Expr =>
          #[((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.1.getCnst.type),
            ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.2.2)]) shapes).toList =
          shapes.toList.flatMap fun x => [((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.1.getCnst.type),
            ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.2.2)] := by
        simp [Array.toList_flatMap]
      rw [hlist] at hitems
      obtain ⟨h0, h1⟩ := flatMap_pair_getElem? (fun x : Ix.ConstantInfo × (Ix.DefKind × Ix.DefinitionSafety ×
            ReducibilityHint) × Ix.Expr => ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.1.getCnst.type))
        (fun x => ((⟨x.1.getCnst.levelParams, false⟩ : Numbering), x.2.2)) shapes.toList i
      rw [hsh] at h0 h1
      obtain ⟨t', ht', ⟨σ, hσ⟩⟩ := forall₂_getElem? hitems h0
      obtain ⟨v', hv', ⟨τ, hτ⟩⟩ := forall₂_getElem? hitems h1
      refine ⟨i, hi', v, σ, τ, t', v', hv, hσ, hτ, fun j hj hji => ?_⟩
      have hj' : j < shapes.zipIdx.size := by simp; omega
      obtain ⟨e1, e2⟩ := hfree j (by simpa using hj') hji
      have hshj : shapes[j].1 = members[j] := by
        obtain ⟨s', v'', -, hsj⟩ := hshape j hj
        rw [List.getElem?_eq_getElem (by simpa [hlen] using hj)] at hsj
        simp only [Array.getElem_toList, Option.some.injEq] at hsj
        rw [hsj]
      have hk0 : ks[2 * i]! = t' := by
        rw [Array.getElem?_toList] at ht'
        simp [getElem!_def, ht']
      have hk1 : ks[2 * i + 1]! = v' := by
        rw [Array.getElem?_toList] at hv'
        simp [getElem!_def, hv']
      simp only [Array.getElem_map, Array.getElem_zipIdx, hshj, Nat.zero_add, hk0, hk1] at e1 e2
      exact ⟨e1, e2⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/--
info: 'Ix.Cert.DefinitionBlocks.convertDefinitions_source' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms convertDefinitions_source

end Ix.Cert.DefinitionBlocks
