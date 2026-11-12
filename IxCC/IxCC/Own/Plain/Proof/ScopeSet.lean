import IxCC.Own.Plain.Check
import IxCC.Own.Plain.ScopeSet

/-! # The scope check over sets equals the scope check over lists

`Own/Plain/ScopeSet.lean`'s set forms (`freshSet`, `scopeOkSet`, `scopeAltsSet`, `scopeOptSet`,
with `signatureArity` for a callee's arity) compute the list forms of `Own/Plain/Check.lean`
(`fresh`, `scopeOk`, `scopeAlts`, `scopeOpt`, with `signatures`) whenever the set and the list
have the same members. `programDomain` and `contractProgramDomain` run the set forms;
`programDomain_eq_list` and `contractProgramDomain_eq_list` restate each as its former definition
over the list forms, through which their `_function` lemmas (`Own/Plain/Proof/Admission.lean`)
conclude `fresh` and `scopeOk`. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open IxCC.Fir (Var JoinId FunId Arg Rhs)

/-- A lookup after `setF` (the insertion of `Src.NatMap`), proved without classical reasoning:
`Src.NatMap.get?_setF`'s proof uses `Classical.choice`, which `programDomain_function`'s exact
axiom set (`propext`, `Quot.sound`) does not admit. -/
theorem natMap_setF_get? {α : Type} : ∀ (fuel : Nat) (m : Src.NatMap α) (k : Nat) (v : Option α)
    (y : Nat), k < fuel → (Src.NatMap.setF fuel m k v).get? y = if y = k then v else m.get? y
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, m, k, v, y, h => by
    have node : ∀ (w : Option α) (z o : Src.NatMap α), (Src.NatMap.node w z o).get? y =
        if y = 0 then w else if y % 2 = 0 then z.get? (y / 2) else o.get? (y / 2) := by
      intro w z o
      simp only [Src.NatMap.get?, beq_iff_eq]
    have parts : ∃ w z o, Src.NatMap.parts m = (w, z, o) ∧ m.get? y =
        if y = 0 then w else if y % 2 = 0 then z.get? (y / 2) else o.get? (y / 2) := by
      cases m with
      | leaf =>
        refine ⟨none, .leaf, .leaf, rfl, ?_⟩
        simp only [Src.NatMap.get?]
        split <;> (try split) <;> rfl
      | node w z o => exact ⟨w, z, o, rfl, node w z o⟩
    obtain ⟨w, z, o, hp, hm⟩ := parts
    rw [hm]
    simp only [Src.NatMap.setF, hp, beq_iff_eq]
    by_cases hk : k = 0
    · subst hk
      by_cases hy : y = 0
      · subst hy
        simp only [↓reduceIte, Src.NatMap.get?, beq_iff_eq]
      · simp only [hy, ↓reduceIte, node]
    · by_cases he : k % 2 = 0
      · simp only [hk, he, ↓reduceIte, node]
        rw [natMap_setF_get? fuel z (k / 2) v (y / 2) (by omega)]
        by_cases hy : y = 0
        · subst hy
          simp only [Ne.symm hk, ↓reduceIte]
        · by_cases hye : y % 2 = 0
          · have hiff : (y / 2 = k / 2) ↔ (y = k) := ⟨fun _ => by omega, fun _ => by omega⟩
            simp only [hy, hye, ↓reduceIte, hiff]
          · have hyk : ¬ y = k := fun _ => by omega
            simp only [hy, hye, hyk, ↓reduceIte]
      · simp only [hk, he, ↓reduceIte, node]
        rw [natMap_setF_get? fuel o (k / 2) v (y / 2) (by omega)]
        by_cases hy : y = 0
        · subst hy
          simp only [Ne.symm hk, ↓reduceIte]
        · by_cases hye : y % 2 = 0
          · have hyk : ¬ y = k := fun _ => by omega
            simp only [hy, hye, hyk, ↓reduceIte]
          · have hiff : (y / 2 = k / 2) ↔ (y = k) := ⟨fun _ => by omega, fun _ => by omega⟩
            simp only [hy, hye, ↓reduceIte, hiff]

theorem natSet_contains_insert (s : Src.NatSet) (k x : Nat) :
    (s.insert k).contains x = (x == k || s.contains x) := by
  simp only [Src.NatSet.insert, Src.NatMap.insert, Src.NatMap.contains]
  rw [natMap_setF_get? (k + 1) s k (some ()) x (Nat.lt_succ_self k)]
  split
  · next h => simp only [show (x == k) = true from decide_eq_true h, Bool.true_or, Option.isSome_some]
  · next h => simp only [show (x == k) = false from beq_false_of_ne h, Bool.false_or]

theorem list_contains_append_single (live : List Var) (y x : Var) :
    (live ++ [y]).contains x = (x == y || live.contains x) := by
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, List.mem_append, List.mem_singleton, Bool.or_eq_true,
    beq_iff_eq]
  exact Or.comm

theorem contains_insert_append {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (y : Var) :
    ∀ x, (s.insert y).contains x = (live ++ [y]).contains x := by
  intro x
  rw [natSet_contains_insert, h x, list_contains_append_single]

theorem contains_insertVars {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (xs : List Var) :
    ∀ x, (insertVars s xs).contains x = (live ++ xs).contains x := by
  induction xs generalizing s live with
  | nil => simpa only [insertVars, List.append_nil] using h
  | cons y ys ih =>
    intro x
    have := ih (contains_insert_append h y) x
    rwa [List.append_assoc, List.singleton_append] at this

theorem argInSet_eq {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (a : Arg) :
    argInSet s a = argIn live a := by
  cases a with
  | var x => exact h x
  | lit _ => rfl
  | erased => rfl

theorem freshSet_eq {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (xs : List Var) :
    freshSet s xs = fresh live xs := by
  induction xs generalizing s live with
  | nil => rfl
  | cons x xs ih =>
    simp only [freshSet, fresh, h x, ih (contains_insert_append h x)]

theorem lookup_signatures_range' (P : Fir.Program) (f : Nat) : ∀ (m s : Nat),
    (((List.range' s m).filterMap fun g => (P.fun? g).map (g, ·)).map
        fun (p : Nat × Fir.Fun) => (p.1, p.2.arity)).lookup f =
      if s ≤ f ∧ f < s + m then (P.fun? f).map (·.arity) else none
  | 0, s => by
    simp only [List.range'_zero, List.filterMap_nil, List.map_nil, List.lookup_nil]
    split
    · next hc => exact absurd hc.2 (by have := hc.1; omega)
    · rfl
  | m + 1, s => by
    rw [List.range'_succ, List.filterMap_cons]
    have ih := lookup_signatures_range' P f m (s + 1)
    cases hs : P.fun? s with
    | none =>
      simp only [Option.map_none]
      rw [ih]
      by_cases hf : f = s
      · have h1 : ¬ (s + 1 ≤ f ∧ f < s + 1 + m) := fun ⟨_, _⟩ => by omega
        split
        · next hc => exact absurd hc h1
        · split
          · simp only [hf, hs, Option.map_none]
          · rfl
      · have : (s + 1 ≤ f ∧ f < s + 1 + m) ↔ (s ≤ f ∧ f < s + (m + 1)) :=
          ⟨fun ⟨_, _⟩ => ⟨by omega, by omega⟩, fun ⟨_, _⟩ => ⟨by omega, by omega⟩⟩
        simp only [this]
    | some fd =>
      simp only [Option.map_some, List.map_cons, List.lookup_cons]
      by_cases hf : f = s
      · simp only [show (f == s) = true from decide_eq_true hf]
        split
        · simp only [hf, hs, Option.map_some]
        · next hc => exact absurd ⟨by omega, by omega⟩ hc
      · simp only [show (f == s) = false from beq_false_of_ne hf]
        rw [ih]
        have : (s + 1 ≤ f ∧ f < s + 1 + m) ↔ (s ≤ f ∧ f < s + (m + 1)) :=
          ⟨fun ⟨_, _⟩ => ⟨by omega, by omega⟩, fun ⟨_, _⟩ => ⟨by omega, by omega⟩⟩
        simp only [this]

theorem signatureArity_eq (P : Fir.Program) (f : FunId) :
    signatureArity P f = (signatures P).lookup f := by
  have h := lookup_signatures_range' P f P.size 0
  rw [← List.range_eq_range'] at h
  simp only [Nat.zero_le, true_and, Nat.zero_add] at h
  unfold signatureArity
  exact h.symm

theorem rhsInSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (r : Rhs) :
    rhsInSet P s r = rhsIn (signatures P) live r := by
  have ha : argInSet s = argIn live := funext (argInSet_eq h)
  cases r with
  | arg a => exact argInSet_eq h a
  | ctor c args => simp only [rhsInSet, rhsIn, ha]
  | proj x c i => exact h x
  | prim p args => simp only [rhsInSet, rhsIn, ha]
  | call f args => simp only [rhsInSet, rhsIn, ha, signatureArity_eq]

mutual
theorem scopeOkSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (joins : JoinArities) :
    ∀ c : Fir.Code, scopeOkSet P s joins c = scopeOk (signatures P) live joins c
  | .bind x r k => by
    simp only [scopeOkSet, scopeOk, h x, rhsInSet_eq P h r,
      scopeOkSet_eq P (contains_insert_append h x) joins k]
  | .jp j ps rec body k => by
    simp only [scopeOkSet, scopeOk, freshSet_eq h ps,
      scopeOkSet_eq P (contains_insertVars h ps) (if rec then (j, ps.length) :: joins else joins) body,
      scopeOkSet_eq P h ((j, ps.length) :: joins) k]
  | .jmp j args => by
    simp only [scopeOkSet, scopeOk, funext (argInSet_eq h)]
  | .case x alts dflt => by
    simp only [scopeOkSet, scopeOk, h x, scopeAltsSet_eq P h joins alts,
      scopeOptSet_eq P h joins dflt]
  | .ret a => argInSet_eq h a
  | .tcall f args => by
    simp only [scopeOkSet, scopeOk, funext (argInSet_eq h), signatureArity_eq]
  | .trap => rfl

theorem scopeAltsSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (joins : JoinArities) :
    ∀ alts : List Fir.Alt, scopeAltsSet P s joins alts = scopeAlts (signatures P) live joins alts
  | [] => rfl
  | .mk _ body :: alts => by
    simp only [scopeAltsSet, scopeAlts, scopeOkSet_eq P h joins body,
      scopeAltsSet_eq P h joins alts]

theorem scopeOptSet_eq (P : Fir.Program) {s : Src.NatSet} {live : List Var}
    (h : ∀ x, s.contains x = live.contains x) (joins : JoinArities) :
    ∀ d : Option Fir.Code, scopeOptSet P s joins d = scopeOpt (signatures P) live joins d
  | none => rfl
  | some c => scopeOkSet_eq P h joins c
end

/-- **A function's scope check, set form = list form** (what `programDomain` and
`contractProgramDomain` run per numbered function: fresh parameters, then the body in their scope
with no join). -/
theorem functionScope_eq (P : Fir.Program) (ps : List Var) (body : Fir.Code) :
    (freshSet .leaf ps && scopeOkSet P (insertVars .leaf ps) [] body) =
      (fresh [] ps && scopeOk (signatures P) ps [] body) := by
  have h0 : ∀ x, (Src.NatMap.leaf : Src.NatSet).contains x = ([] : List Var).contains x :=
    fun _ => rfl
  rw [freshSet_eq h0, scopeOkSet_eq P (contains_insertVars h0 ps) [] body, List.nil_append]

/-- **`programDomain` is its former definition over lists** (`fresh` and `scopeOk` over
`signatures`). -/
theorem programDomain_eq_list (P : Fir.Program) :
    programDomain P = (List.range P.size).all fun f =>
      match P.fun? f with
      | none => false
      | some fd => funDomain fd && fresh [] (fd.params.map (·.1)) &&
          scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body := by
  unfold programDomain
  refine congrArg ((List.range P.size).all ·) (funext fun f => ?_)
  cases P.fun? f with
  | none => rfl
  | some fd =>
    dsimp only
    rw [Bool.and_assoc, Bool.and_assoc, functionScope_eq]

/-- **`contractProgramDomain` is its former definition over lists**. -/
theorem contractProgramDomain_eq_list (P : Fir.Program) :
    contractProgramDomain P = (List.range P.size).all fun f =>
      match P.fun? f with
      | none => false
      | some fd => contractFunDomain fd && fresh [] (fd.params.map (·.1)) &&
          scopeOk (signatures P) (fd.params.map (·.1)) [] fd.body := by
  unfold contractProgramDomain
  refine congrArg ((List.range P.size).all ·) (funext fun f => ?_)
  cases P.fun? f with
  | none => rfl
  | some fd =>
    dsimp only
    rw [Bool.and_assoc, Bool.and_assoc, functionScope_eq]

end IxCC.Own.Plain
