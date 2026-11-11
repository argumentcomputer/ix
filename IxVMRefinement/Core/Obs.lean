import Ix.IxVM.Refinement.Mirror
import Aiur.HeapMono

/-! # Observed derivations: inversion and the induction on size

The core of IxVM is proved
sound against the kernel's rules by **one induction on derivation size over all
functions at once**. A derivation is an observed one (`ObsFn`, with its call
list), because the collision escape of the statement is read off the calls; its
size is the length of the call list. A callee's call list is a strict infix of
its caller's (`ObsExpr.call` adds the callee's own entry), so the statement for
the callees "at smaller size" is the statement for every observed derivation
with fewer calls (`ObsFn.strong_induction`).

This module is generic (nothing about IxVM): the inversion lemmas for observed
expressions, one per node (the observed twins of `Mirror.lean`'s
`EvalExpr.*_inv`), the arm selection (`selectArm_mem`), and the induction
principle. -/

namespace Aiur.Generic.SourceSemantics

variable {F : Type} [Field F] [DecidableEq F] {world : World F} {types : Types}
  {locals : Environment F Nat} {before after : Heap F} {result : SourceValue F}
  {calls : List (Call F)}

/-! ## Inversion at the head of an observed expression -/

theorem ObsExpr.literal_inv {x : F}
    (h : ObsExpr world types locals (.literal x) before result after calls) :
    result = .field x ∧ after = before ∧ calls = [] := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem ObsExpr.var_inv {name : String}
    (h : ObsExpr world types locals (.var name) before result after calls) :
    locals.find? (·.1 == name) = some (name, result) ∧ after = before ∧ calls = [] := by
  cases h with | var lookup => exact ⟨lookup, rfl, rfl⟩

theorem ObsExpr.load_inv {e : Expr F}
    (h : ObsExpr world types locals (.load e) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      loadValue after input = .ok result := by
  cases h with | load pointer loaded => exact ⟨_, pointer, loaded⟩

theorem ObsExpr.store_inv {e : Expr F}
    (h : ObsExpr world types locals (.store e) before result after calls) :
    ∃ input middle, ObsExpr world types locals e before input middle calls ∧
      result = .ptr input.type middle.length ∧ after = middle ++ [input] := by
  cases h with | store value => exact ⟨_, _, value, rfl, rfl⟩

theorem ObsExpr.construct_inv {name : String} {args : Option (List Ty)} {ctor : String}
    {es : List (Expr F)}
    (h : ObsExpr world types locals (.construct name args ctor es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      result = .construct (instanceName types name args) ctor values := by
  cases h with | construct items => exact ⟨_, items, rfl⟩

theorem ObsExpr.tuple_inv {es : List (Expr F)}
    (h : ObsExpr world types locals (.tuple es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      result = .tuple values := by
  cases h with | tuple items => exact ⟨_, items, rfl⟩

theorem ObsExpr.letValue_inv {pat : Pattern F} {e rest : Expr F}
    (h : ObsExpr world types locals (.letValue pat e rest) before result after calls) :
    ∃ input middle bindings calls₁ calls₂,
      ObsExpr world types locals e before input middle calls₁ ∧
      world.matchPattern types middle pat input = .ok (some bindings) ∧
      ObsExpr world types (bindings ++ locals) rest middle result after calls₂ ∧
      calls = calls₁ ++ calls₂ := by
  cases h with
  | letValue value matched body => exact ⟨_, _, _, _, _, value, matched, body, rfl⟩

theorem ObsExpr.matchValue_inv {e : Expr F} {arms : List (Pattern F × Expr F)}
    (h : ObsExpr world types locals (.matchValue e arms) before result after calls) :
    ∃ input middle bindings body calls₁ calls₂,
      ObsExpr world types locals e before input middle calls₁ ∧
      selectArm world types middle input arms = .ok (some (bindings, body)) ∧
      ObsExpr world types (bindings ++ locals) body middle result after calls₂ ∧
      calls = calls₁ ++ calls₂ := by
  cases h with
  | matchValue value selected branch =>
    exact ⟨_, _, _, _, _, _, value, selected, branch, rfl⟩

theorem ObsExpr.binary_inv {op : BinOp} {lhs rhs : Expr F}
    (h : ObsExpr world types locals (.binary op lhs rhs) before result after calls) :
    ∃ x y middle calls₁ calls₂, ObsExpr world types locals lhs before x middle calls₁ ∧
      ObsExpr world types locals rhs middle y after calls₂ ∧ evalBinOp op x y = .ok result ∧
      calls = calls₁ ++ calls₂ := by
  cases h with
  | binary left right operation => exact ⟨_, _, _, _, _, left, right, operation, rfl⟩

theorem ObsExpr.builtin_inv {op : Builtin} {es : List (Expr F)}
    (h : ObsExpr world types locals (.builtin op es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      op.apply values = .ok result := by
  cases h with | builtin items applied => exact ⟨_, items, applied⟩

theorem ObsArgs.nil_inv {values : List (SourceValue F)}
    (h : ObsArgs world types locals [] before values after calls) :
    values = [] ∧ after = before ∧ calls = [] := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem ObsArgs.cons_inv {e : Expr F} {es : List (Expr F)} {values : List (SourceValue F)}
    (h : ObsArgs world types locals (e :: es) before values after calls) :
    ∃ v vs middle calls₁ calls₂, values = v :: vs ∧
      ObsExpr world types locals e before v middle calls₁ ∧
      ObsArgs world types locals es middle vs after calls₂ ∧ calls = calls₁ ++ calls₂ := by
  cases h with | cons head tail => exact ⟨_, _, _, _, _, rfl, head, tail, rfl⟩

theorem ObsExpr.global_literal_inv {name : String} {t : Ty} {x : F}
    (hc : world.constant name (t.subst types) = .ok (.literal x))
    (h : ObsExpr world types locals (.global name (some t)) before result after calls) :
    result = .field x ∧ after = before ∧ calls = [] := by
  cases h with
  | global lookup interpreted value =>
    rw [hc] at lookup
    cases lookup
    simp only [Consts.toExpr, pure, Except.pure, Except.ok.injEq] at interpreted
    subst interpreted
    exact value.literal_inv

theorem ObsExpr.array_inv {es : List (Expr F)}
    (h : ObsExpr world types locals (.array es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      result = .tuple values := by
  cases h with | array items => exact ⟨_, items, rfl⟩

theorem ObsExpr.repeat_inv {e : Expr F} {n : Nat}
    (h : ObsExpr world types locals (.repeat e n) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      result = .tuple (List.replicate n input) := by
  cases h with | «repeat» value => exact ⟨_, value, rfl⟩

theorem ObsExpr.index_inv {e : Expr F} {i : Nat}
    (h : ObsExpr world types locals (.index e i) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      projectValue input i = .ok result := by
  cases h with | index value projected => exact ⟨_, value, projected⟩

theorem ObsExpr.project_inv {e : Expr F} {i : Nat}
    (h : ObsExpr world types locals (.project e i) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      projectValue input i = .ok result := by
  cases h with | project value projected => exact ⟨_, value, projected⟩

theorem ObsExpr.slice_inv {e : Expr F} {a : Nat} {b : Option Nat}
    (h : ObsExpr world types locals (.slice e a b) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      sliceValue input a b = .ok result := by
  cases h with | slice value sliced => exact ⟨_, value, sliced⟩

theorem ObsExpr.member_inv {e : Expr F} {field : FieldRef}
    (h : ObsExpr world types locals (.member e field) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      memberValue types field input = .ok result := by
  cases h with | member value projected => exact ⟨_, value, projected⟩

theorem ObsExpr.neg_inv {e : Expr F}
    (h : ObsExpr world types locals (.neg e) before result after calls) :
    ∃ input, ObsExpr world types locals e before input after calls ∧
      evalNeg input = .ok result := by
  cases h with | neg value operation => exact ⟨_, value, operation⟩

theorem ObsExpr.constructAs_inv {ps : List String} {t : Ty} {ctor : String} {es : List (Expr F)}
    (h : ObsExpr world types locals (.constructAs ps t ctor es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      result = .construct (constructorName types t) ctor values := by
  cases h with | constructAs items => exact ⟨_, items, rfl⟩

theorem ObsExpr.update_inv {paths : List UpdatePath} {es : List (Expr F)}
    (h : ObsExpr world types locals (.update paths es) before result after calls) :
    ∃ values, ObsArgs world types locals es before values after calls ∧
      Update.value types paths values = .ok result := by
  cases h with | update items updated => exact ⟨_, items, updated⟩

theorem ObsExpr.hint_inv {t : Ty} {key : Expr F} {channel : String}
    (h : ObsExpr world types locals (.hint t key channel) before result after calls) :
    ∃ input value, ObsExpr world types locals key before input after calls ∧
      world.typed (t.subst types).toCore value = true ∧ result = value.toValue := by
  cases h with | hint key typed => exact ⟨_, _, key, typed, rfl⟩

omit [Field F] in
theorem Builtin.ascribe_inv {t : Ty} {v r : SourceValue F}
    (h : (Builtin.ascribe t).apply [v] = .ok r) : r = v := by
  have hv : (Builtin.ascribe t).apply [v] = .ok v := rfl
  rw [hv] at h
  cases h
  rfl

omit [Field F] in
theorem Builtin.debug_inv {m : String} {vs : List (SourceValue F)} {r : SourceValue F}
    (h : (Builtin.debug m).apply vs = .ok r) : r = .tuple [] := by
  have hv : (Builtin.debug m).apply vs = .ok (.tuple []) := rfl
  rw [hv] at h
  cases h
  rfl

omit [Field F] in
theorem Builtin.assertEq_inv {a : Assertion} {x y r : SourceValue F}
    (h : (Builtin.assertEq a).apply [x, y] = .ok r) : x = y ∧ r = .tuple [] := by
  have hv : (Builtin.assertEq a).apply [x, y] = evalAssertEq a x y := rfl
  rw [hv, evalAssertEq_ok] at h
  exact ⟨h.2.1, h.2.2⟩

/-- A named type's constructor name is its instance's name. -/
theorem constructorName_named (types : Types) (n : String) (args : List Ty) :
    constructorName types (.named n args) = instanceName types n (some args) := by
  unfold constructorName instanceName
  simp [Ty.subst, Ty.toCore]

/-! ## Arm selection and patterns, one step at a time

The generated path lemmas (`IxVMRefinement.Obs`) select arms in order
(`selectArm_cons_inv`: the arm's pattern matched, or it did not and a later
arm was selected) and invert a pattern node by node. -/

omit [Field F] in
theorem selectArm_cons_inv {p : Pattern F} {b : Expr F} {arms : List (Pattern F × Expr F)}
    {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat} {body : Expr F}
    (h : selectArm world types heap v ((p, b) :: arms) = .ok (some (bs, body))) :
    (world.matchPattern types heap p v = .ok (some bs) ∧ body = b) ∨
      (world.matchPattern types heap p v = .ok none ∧
        selectArm world types heap v arms = .ok (some (bs, body))) := by
  rw [selectArm] at h
  cases hm : world.matchPattern types heap p v with
  | error e => simp [hm, bind, Except.bind] at h
  | ok opt =>
    cases opt with
    | some bindings =>
      simp only [hm, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inl ⟨rfl, rfl⟩
    | none =>
      simp only [hm, bind, Except.bind] at h
      exact .inr ⟨rfl, h⟩

omit [Field F] in
theorem selectArm_nil_inv {v : SourceValue F} {heap : Heap F} {bs : Environment F Nat}
    {body : Expr F} (h : selectArm world types heap v [] = .ok (some (bs, body))) : False := by
  simp [SourceSemantics.selectArm] at h

omit [Field F] in
theorem matchPattern_bind_inv {n : String} {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (h : world.matchPattern types heap (.bind n) v = .ok (some bs)) :
    bs = [(n, v)] := by
  rw [matchPattern_bind] at h
  cases h
  rfl

omit [Field F] in
theorem matchPattern_wildcard_inv {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (h : world.matchPattern types heap .wildcard v = .ok (some bs)) :
    bs = [] := by
  rw [matchPattern_wildcard] at h
  cases h
  rfl

omit [Field F] in
theorem matchPattern_bind_none {n : String} {v : SourceValue F} {heap : Heap F}
    (h : world.matchPattern types heap (.bind n) v = .ok none) : False := by
  rw [matchPattern_bind] at h
  cases h

omit [Field F] in
theorem matchPattern_wildcard_none {v : SourceValue F} {heap : Heap F}
    (h : world.matchPattern types heap .wildcard v = .ok none) : False := by
  rw [matchPattern_wildcard] at h
  cases h

omit [Field F] in
theorem MatchesConst.some_inv {p : Pattern F} {u v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (hp : MatchesConst world types p u)
    (h : world.matchPattern types heap p v = .ok (some bs)) : v = u ∧ bs = [] := by
  rw [hp heap v] at h
  split at h
  · rename_i hv
    cases h
    exact ⟨hv, rfl⟩
  · cases h

omit [Field F] in
theorem MatchesConst.none_inv {p : Pattern F} {u v : SourceValue F} {heap : Heap F}
    (hp : MatchesConst world types p u) (h : world.matchPattern types heap p v = .ok none) :
    v ≠ u := by
  intro hv
  rw [hp heap v] at h
  split at h
  · cases h
  · rename_i hne
    exact hne hv

omit [Field F] in
theorem matchPattern_tuple_tuple_inv {ps : List (Pattern F)} {us : List (SourceValue F)}
    {heap : Heap F} {bs : Environment F Nat}
    (h : world.matchPattern types heap (.tuple ps) (.tuple us) = .ok (some bs)) :
    matchListWith (world.matchPattern types heap) ps us = .ok (some bs) := by
  rw [matchPattern_tuple] at h
  split at h
  · cases h
  · exact h

omit [Field F] in
theorem matchPattern_array_tuple_inv {ps : List (Pattern F)} {us : List (SourceValue F)}
    {heap : Heap F} {bs : Environment F Nat}
    (h : world.matchPattern types heap (.array ps) (.tuple us) = .ok (some bs)) :
    matchListWith (world.matchPattern types heap) ps us = .ok (some bs) := by
  rw [matchPattern_array] at h
  split at h
  · cases h
  · exact h

omit [Field F] in
/-- A flat array pattern that did not match: the value is no such tuple. -/
theorem matchPattern_array_none {ps : List (Pattern F)} {v : SourceValue F} {heap : Heap F}
    (hflat : IsFlatPatternList ps) (h : world.matchPattern types heap (.array ps) v = .ok none) :
    ∀ vs : List (SourceValue F), vs.length = ps.length → v ≠ .tuple vs := by
  intro vs hlen hv
  subst hv
  rw [matchPattern_array] at h
  simp only [hlen, bne_self_eq_false] at h
  obtain ⟨bs', hbs'⟩ := hflat.matchListWith (world := world) (types := types) hlen.symm heap
  rw [hbs'] at h
  cases h

omit [Field F] in
theorem matchPattern_load_inv {p : Pattern F} {v : SourceValue F} {heap : Heap F}
    {bs : Environment F Nat} (h : world.matchPattern types heap (.load p) v = .ok (some bs)) :
    ∃ u, loadValue heap v = .ok u ∧ world.matchPattern types heap p u = .ok (some bs) := by
  unfold World.matchPattern at h
  rw [matchPatternWith] at h
  cases hl : loadValue heap v with
  | error e => simp [hl, bind, Except.bind] at h
  | ok u =>
    simp only [hl, bind, Except.bind] at h
    exact ⟨u, rfl, h⟩

omit [Field F] in
/-- A flat constructor pattern that did not match: the value is no such constructor. -/
theorem matchPattern_construct_none {t : Ty} {c : String} {ps : List (Pattern F)}
    {v : SourceValue F} {heap : Heap F} (hflat : IsFlatPatternList ps)
    (h : world.matchPattern types heap (.construct t c ps) v = .ok none) :
    ∀ vs : List (SourceValue F), vs.length = ps.length →
      v ≠ .construct (constructorName types t) c vs := by
  intro vs hlen hv
  subst hv
  rw [matchPattern_construct] at h
  simp only [hlen, bne_self_eq_false, Bool.false_or] at h
  obtain ⟨bs', hbs'⟩ := hflat.matchListWith (world := world) (types := types) hlen.symm heap
  rw [hbs'] at h
  cases h

omit [Field F] in
/-- A flat tuple pattern that did not match: the value is no such tuple. -/
theorem matchPattern_tuple_none {ps : List (Pattern F)} {v : SourceValue F} {heap : Heap F}
    (hflat : IsFlatPatternList ps) (h : world.matchPattern types heap (.tuple ps) v = .ok none) :
    ∀ vs : List (SourceValue F), vs.length = ps.length → v ≠ .tuple vs := by
  intro vs hlen hv
  subst hv
  rw [matchPattern_tuple] at h
  simp only [hlen, bne_self_eq_false] at h
  obtain ⟨bs', hbs'⟩ := hflat.matchListWith (world := world) (types := types) hlen.symm heap
  rw [hbs'] at h
  cases h

omit [Field F] [DecidableEq F] in
theorem matchListWith_nil_inv {A : Type}
    {f : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {vs : List (SourceValue F)} {bs : Environment F Nat}
    (h : matchListWith f [] vs = .ok (some bs)) : vs = [] ∧ bs = [] := by
  cases vs with
  | nil =>
    have hv : matchListWith f [] ([] : List (SourceValue F)) = .ok (some []) := rfl
    rw [hv] at h
    cases h
    exact ⟨rfl, rfl⟩
  | cons v vs =>
    have hv : matchListWith f [] (v :: vs) = .ok none := rfl
    rw [hv] at h
    cases h

omit [Field F] [DecidableEq F] in
theorem matchListWith_cons_cons_inv {A : Type}
    {f : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {p : A} {ps : List A} {v : SourceValue F} {vs : List (SourceValue F)} {bs : Environment F Nat}
    (h : matchListWith f (p :: ps) (v :: vs) = .ok (some bs)) :
    ∃ b1 b2, f p v = .ok (some b1) ∧ matchListWith f ps vs = .ok (some b2) ∧
      bs = b1 ++ b2 := by
  rw [matchListWith] at h
  cases h1 : f p v with
  | error e => simp [h1, bind, Except.bind] at h
  | ok o =>
    cases o with
    | none => simp [h1, bind, Except.bind, pure, Except.pure] at h
    | some b1 =>
      cases h2 : matchListWith f ps vs with
      | error e => simp [h1, h2, bind, Except.bind] at h
      | ok o2 =>
        cases o2 with
        | none => simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
        | some b2 =>
          simp only [h1, h2, bind, Except.bind, pure, Except.pure] at h
          cases h
          exact ⟨b1, b2, rfl, rfl, rfl⟩

omit [Field F] [DecidableEq F] in
theorem matchListWith_cons_inv {A : Type}
    {f : A → SourceValue F → Except EvalError (Option (Environment F Nat))}
    {p : A} {ps : List A} {vs : List (SourceValue F)} {bs : Environment F Nat}
    (h : matchListWith f (p :: ps) vs = .ok (some bs)) :
    ∃ v vs' b1 b2, vs = v :: vs' ∧ f p v = .ok (some b1) ∧
      matchListWith f ps vs' = .ok (some b2) ∧ bs = b1 ++ b2 := by
  cases vs with
  | nil =>
    have hv : matchListWith f (p :: ps) ([] : List (SourceValue F)) = .ok none := rfl
    rw [hv] at h
    cases h
  | cons v vs =>
    obtain ⟨b1, b2, h1, h2, rfl⟩ := matchListWith_cons_cons_inv h
    exact ⟨v, vs, b1, b2, rfl, h1, h2, rfl⟩

/-! ## Arm selection -/

omit [Field F] in
/-- **The selected arm is an arm whose pattern matched**, with the bindings the
match produced. (Which matching arm is selected is not needed when every arm's
result is sound on its own.) -/
theorem selectArm_mem {arms : List (Pattern F × Expr F)} {input : SourceValue F}
    {heap : Heap F} {bindings : Environment F Nat} {body : Expr F}
    (selected : selectArm world types heap input arms = .ok (some (bindings, body))) :
    ∃ pat, (pat, body) ∈ arms ∧ world.matchPattern types heap pat input = .ok (some bindings) := by
  induction arms with
  | nil => simp [SourceSemantics.selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pat, expr⟩
      cases matched : world.matchPattern types heap pat input with
      | error e => simp [SourceSemantics.selectArm, matched, bind, Except.bind] at selected
      | ok bs => cases bs with
        | none =>
            obtain ⟨p, hp, hm⟩ := ih (by
              simpa [SourceSemantics.selectArm, matched, bind, Except.bind] using selected)
            exact ⟨p, by simp [hp], hm⟩
        | some bs =>
            have same : bs = bindings ∧ expr = body := by
              simpa [SourceSemantics.selectArm, matched, bind, Except.bind, pure, Except.pure]
                using selected
            obtain ⟨rfl, rfl⟩ := same
            exact ⟨pat, by simp, matched⟩

/-! ## The induction on size -/

/-- **Strong induction on the size of observed derivations**, the length of
their call lists, for every function at once: if every observed derivation
satisfies `P` whenever all observed derivations with strictly fewer calls do,
then every observed derivation satisfies `P`. -/
theorem ObsFn.strong_induction
    (P : String → List (SourceValue F) → Heap F → SourceValue F → Heap F → List (Call F) → Prop)
    (step : ∀ n args b v a cs, ObsFn world n args b v a cs →
      (∀ n' args' b' v' a' cs', cs'.length < cs.length → ObsFn world n' args' b' v' a' cs' →
        P n' args' b' v' a' cs') →
      P n args b v a cs) :
    ∀ n args b v a cs, ObsFn world n args b v a cs → P n args b v a cs := by
  have key : ∀ N n args b v a cs, cs.length ≤ N → ObsFn world n args b v a cs →
      P n args b v a cs := by
    intro N
    induction N with
    | zero =>
        intro n args b v a cs hle ev
        exact step _ _ _ _ _ _ ev (fun _ _ _ _ _ cs' hlt _ => absurd hlt (by omega))
    | succ N ih =>
        intro n args b v a cs hle ev
        exact step _ _ _ _ _ _ ev (fun n' args' b' v' a' cs' hlt ev' =>
          ih n' args' b' v' a' cs' (by omega) ev')
  exact fun n args b v a cs ev => key _ n args b v a cs (Nat.le_refl _) ev

/-! ## The heap only grows -/

theorem ObsExpr.heap_extends {expr : Expr F}
    (evaluated : ObsExpr world types locals expr before result after calls) :
    Heap.Extends before after := by
  induction evaluated using ObsExpr.rec
    (motive_2 := fun _ _ _ before _ after _ _ => Heap.Extends before after)
    (motive_3 := fun _ _ before _ after _ _ => Heap.Extends before after)
    (motive_4 := fun _ _ _ before _ _ after _ _ => Heap.Extends before after)
    (motive_5 := fun _ _ _ before _ _ after _ _ => Heap.Extends before after) with
  | literal | var | nil =>
      exact Heap.Extends.refl _
  | block _ ih
  | blockExit _ ih
  | global _ _ _ ih
  | tuple _ ih
  | array _ ih
  | «repeat» _ ih
  | index _ _ ih
  | slice _ _ ih
  | builtin _ _ ih
  | update _ _ ih
  | record _ ih
  | member _ _ ih
  | construct _ ih
  | constructAs _ ih
  | project _ _ ih
  | load _ _ ih
  | hint _ _ ih
  | neg _ _ ih
  | intro _ _ ih
  | returned _ _ ih
  | exit _ ih
  | exitPayload _ ih
  | fromBlock _ _ ih
  | fromGlobal _ _ _ ih
  | fromTuple _ ih
  | fromArray _ ih
  | fromRepeat _ ih
  | fromIndex _ ih
  | fromSlice _ ih
  | fromBuiltin _ ih
  | fromUpdate _ ih
  | fromRecord _ ih
  | fromMember _ ih
  | fromConstruct _ ih
  | fromConstructAs _ ih
  | fromProject _ ih
  | fromLetValue _ ih
  | fromStore _ ih
  | fromLoad _ ih
  | fromHint _ ih
  | fromNeg _ ih
  | binaryLeft _ ih
  | fromCall _ ih
  | fromMatchValue _ ih
  | head _ ih =>
      exact ih
  | letValue _ _ _ ih₁ ih₂
  | binary _ _ _ ih₁ ih₂
  | call _ _ ih₁ ih₂
  | matchValue _ _ _ ih₁ ih₂
  | cons _ _ ih₁ ih₂
  | letBody _ _ _ ih₁ ih₂
  | binaryRight _ _ ih₁ ih₂
  | matchBody _ _ _ ih₁ ih₂
  | tail _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂
  | store _ ih =>
      exact ih.trans (Heap.Extends.snoc _ _)

theorem ObsArgs.heap_extends {exprs : List (Expr F)} {values : List (SourceValue F)}
    (evaluated : ObsArgs world types locals exprs before values after calls) :
    Heap.Extends before after :=
  (ObsExpr.tuple evaluated).heap_extends

theorem ObsFn.heap_extends {name : String} {args : List (SourceValue F)}
    (evaluated : ObsFn world name args before result after calls) :
    Heap.Extends before after :=
  evaluated.erase.heap_extends

end Aiur.Generic.SourceSemantics
