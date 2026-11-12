import IxCC.Own.Plain.Check
import IxCC.Own.Plain.ScopeSet
import IxCC.Src.Proof.NatMap

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

theorem natSet_contains_insert (s : Src.NatSet) (k x : Nat) :
    (s.insert k).contains x = (x == k || s.contains x) := by
  simp only [Src.NatSet.insert, Src.NatMap.contains, Src.NatMap.get?_insert]
  by_cases h : x = k
  · simp [h]
  · simp [h]

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

private theorem lookup_signatures_range' (P : Fir.Program) (f : FunId) : ∀ (m s : Nat),
    (((List.range' s m).filterMap fun g => (P.fun? g).map (g, ·)).map
        fun (p : FunId × Fir.Fun) => (p.1, p.2.arity)).lookup f =
      if s ≤ f ∧ f < s + m then (P.fun? f).map (·.arity) else none
  | 0, s => by
    simp only [List.range'_zero, List.filterMap_nil, List.map_nil, List.lookup_nil]
    split <;> first | rfl | omega
  | m + 1, s => by
    rw [List.range'_succ, List.filterMap_cons]
    have ih := lookup_signatures_range' P f m (s + 1)
    cases hs : P.fun? s with
    | none =>
      simp only [Option.map_none]
      rw [ih]
      by_cases hf : f = s
      · subst hf
        simp [hs]
      · have : (s + 1 ≤ f ∧ f < s + 1 + m) ↔ (s ≤ f ∧ f < s + (m + 1)) := by omega
        simp only [this]
    | some fd =>
      simp only [Option.map_some, List.map_cons, List.lookup_cons]
      by_cases hf : f = s
      · subst hf
        simp [hs]
      · have hb : (f == s) = false := by simpa using hf
        simp only [hb]
        rw [ih]
        have : (s + 1 ≤ f ∧ f < s + 1 + m) ↔ (s ≤ f ∧ f < s + (m + 1)) := by omega
        simp only [this]

theorem signatureArity_eq (P : Fir.Program) (f : FunId) :
    signatureArity P f = (signatures P).lookup f := by
  unfold signatureArity signatures Fir.Program.funList
  rw [List.range_eq_range', lookup_signatures_range']
  simp only [Nat.zero_le, true_and, Nat.zero_add]

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
