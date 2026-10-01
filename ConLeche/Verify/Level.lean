module

public import ConLeche.Kernel.Level

public section

/-!
# Soundness of the level operations

Levels are given semantics by evaluation into `Nat` under an assignment of
the parameters (`Level.eval`).  The results proved here:

* `eval_simplify`: `simplify` preserves evaluation.
* `leqCore_sound`: `leqCore … = some true` implies `eval φ l ≤ eval φ r + diff`
  for every assignment `φ`.
* `isEquiv_sound`: `isEquiv l r = some true` implies `eval φ l = eval φ r`
  for every assignment `φ`.

Only the `true` direction is needed: a `false` verdict leads to rejection,
which needs no justification, and `none` is an internal error.
-/

namespace ConLeche.Level

/-- Evaluate a level under an assignment of its parameters. -/
@[expose] def eval (φ : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => eval φ l + 1
  | .max l r => Max.max (eval φ l) (eval φ r)
  | .imax l r => if eval φ r = 0 then 0 else Max.max (eval φ l) (eval φ r)
  | .param n => φ n

/-- The assignment corresponding to a parameter substitution. -/
@[expose] def substFn (φ : Name → Nat) : List Name → List Level → Name → Nat
  | k :: ks, v :: vs, n => if k = n then eval φ v else substFn φ ks vs n
  | _, _, n => φ n

theorem eval_subst_go (φ : Name → Nat) (ks : List Name) (vs : List Level) (n : Name) :
    eval φ (subst.go ks vs n) = substFn φ ks vs n := by
  fun_induction subst.go with grind [eval, substFn]

theorem eval_subst (φ : Name → Nat) (ks : List Name) (vs : List Level) (l : Level) :
    eval φ (subst ks vs l) = eval (substFn φ ks vs) l := by
  fun_induction subst with grind [eval, eval_subst_go]

theorem eval_combining (φ : Name → Nat) (l r : Level) :
    eval φ (combining l r) = Max.max (eval φ l) (eval φ r) := by
  fun_induction combining with grind [eval]

theorem eval_simplify (φ : Name → Nat) (l : Level) :
    eval φ (simplify l) = eval φ l := by
  fun_induction simplify with grind [eval, eval_combining]

/-- The semantic statement decided by `leqCore fuel l r diff = some true`. -/
def Sem (l r : Level) (diff : Int) : Prop :=
  ∀ φ : Name → Nat, (eval φ l : Int) ≤ eval φ r + diff

private theorem bind_and_some_true {x y : Option Bool}
    (h : (do if ← x then y else pure false : Option Bool) = some true) :
    x = some true ∧ y = some true := by
  cases x with
  | none => simp_all [Bind.bind, Option.bind]
  | some b => cases b <;> simp_all [Bind.bind, Option.bind, Pure.pure]

private theorem bind_or_some_true {x y : Option Bool}
    (h : (do if ← x then pure true else y : Option Bool) = some true) :
    x = some true ∨ y = some true := by
  cases x with
  | none => simp_all [Bind.bind, Option.bind]
  | some b => cases b <;> simp_all [Bind.bind, Option.bind, Pure.pure]

/-- Point update of an assignment. -/
private def upd (φ : Name → Nat) (p : Name) (v : Nat) : Name → Nat :=
  fun n => if p = n then v else φ n

private theorem eval_subst_single (φ : Name → Nat) (p : Name) (v : Level) (l : Level) :
    eval φ (subst [p] [v] l) = eval (upd φ p (eval φ v)) l := by
  rw [eval_subst]
  have h : substFn φ [p] [v] = upd φ p (eval φ v) := by
    funext n; simp [substFn, upd]
  rw [h]

/-- `byCases` is sound for an arbitrary split parameter. -/
theorem byCases_sound {fuel : Nat}
    (ih : ∀ l r diff, leqCore fuel l r diff = some true → Sem l r diff)
    {p : Name} {l r : Level} {diff : Int}
    (h : byCases fuel p l r diff = some true) : Sem l r diff := by
  unfold byCases at h
  obtain ⟨h0, hs⟩ := bind_and_some_true h
  have s0 := ih _ _ _ h0
  have ss := ih _ _ _ hs
  intro φ
  by_cases hp : φ p = 0
  · have := s0 (upd φ p 0)
    rw [eval_simplify, eval_simplify, eval_subst_single, eval_subst_single] at this
    have hupd : upd (upd φ p 0) p (eval (upd φ p 0) Level.zero) = φ := by
      funext n; simp only [upd, eval]; split <;> simp_all
    rw [hupd] at this
    exact this
  · obtain ⟨k, hk⟩ : ∃ k, φ p = k + 1 := ⟨φ p - 1, by omega⟩
    have := ss (upd φ p k)
    rw [eval_simplify, eval_simplify, eval_subst_single, eval_subst_single] at this
    have hupd : upd (upd φ p k) p (eval (upd φ p k) (Level.succ (Level.param p))) = φ := by
      funext n; simp only [upd, eval]; split <;> simp_all
    rw [hupd] at this
    exact this

private theorem eval_imax_imax (φ : Name → Nat) (a x y : Level) :
    eval φ (Level.imax a (.imax x y)) = eval φ (Level.max (.imax a y) (.imax x y)) := by
  simp only [eval]; grind

private theorem eval_imax_max (φ : Name → Nat) (a x y : Level) :
    eval φ (Level.imax a (.max x y)) = eval φ (Level.max (.imax a x) (.imax a y)) := by
  simp only [eval]; grind

/-- Soundness of `leqCore` (with `rest`, `imaxRules`, `byCases`):
a `some true` verdict means `l ≤ r + diff` under every assignment. -/
theorem leqCore_sound : ∀ {fuel : Nat} {l r : Level} {diff : Int},
    leqCore fuel l r diff = some true → Sem l r diff := by
  intro fuel
  induction fuel with
  | zero => intro l r diff h; simp [leqCore] at h
  | succ fuel ih =>
    have imaxRules_sound : ∀ {l r diff}, imaxRules fuel l r diff = some true → Sem l r diff := by
      intro l r diff h
      unfold imaxRules at h
      split at h
      · exact byCases_sound (fun _ _ _ => ih) h
      · exact byCases_sound (fun _ _ _ => ih) h
      · intro φ; have H := ih h φ; rw [eval_imax_imax]; exact H
      · intro φ; have H := ih h φ; rw [eval_simplify] at H; rw [eval_imax_max]; exact H
      · intro φ; have H := ih h φ; rw [eval_imax_imax]; exact H
      · intro φ; have H := ih h φ; rw [eval_simplify] at H; rw [eval_imax_max]; exact H
      · simp at h
    have rest_sound : ∀ {l r diff}, rest fuel l r diff = some true → Sem l r diff := by
      intro l r diff h
      unfold rest at h
      split at h
      · simp only [Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, hd⟩ := h
        intro φ; omega
      · simp at h
      · simp only [Option.some.injEq, decide_eq_true_eq] at h
        intro φ; simp only [eval]; omega
      · intro φ; have H := ih h φ; simp only [eval]; push_cast; omega
      · intro φ; have H := ih h φ; simp only [eval] at H ⊢; push_cast at H ⊢; omega
      · obtain ⟨h1, h2⟩ := bind_and_some_true h
        intro φ; have H1 := ih h1 φ; have H2 := ih h2 φ
        simp only [eval] at H1 H2 ⊢; omega
      · rcases bind_or_some_true h with h1 | h1 <;>
          { intro φ; have H := ih h1 φ; simp only [eval] at H ⊢; omega }
      · rcases bind_or_some_true h with h1 | h1 <;>
          { intro φ; have H := ih h1 φ; simp only [eval] at H ⊢; omega }
      · split at h
        · split at h
          · subst_eqs
            rename_i hcond
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨⟨rfl, rfl⟩, hd⟩ := hcond
            intro φ; omega
          · exact imaxRules_sound h
        · exact imaxRules_sound h
    intro l r diff h
    unfold leqCore at h
    split at h
    · next hc =>
      obtain ⟨rfl, hd⟩ := hc
      intro φ; simp only [eval]; omega
    · split at h
      · simp at h
      · exact rest_sound h

theorem leq_sound {l r : Level} (h : leq l r = some true) :
    ∀ φ, eval φ l ≤ eval φ r := by
  intro φ
  have := leqCore_sound (fuel := defaultFuel) (by simpa [leq] using h) φ
  rw [eval_simplify, eval_simplify] at this
  omega

/-- **Conformance, task #176 P2 (restrictions-are-findings).**  The
`l == r` disjunct `isEquiv` gained — official's
`is_equivalent(lhs, rhs) = lhs == rhs || normalize lhs == normalize rhs`
(`level.cpp:518`) — is *redundant*: `isEquiv` is equal to the
definition without it, because `l = r` implies
`simplify l = simplify r`, which already returned `some true`.  So the
alignment is verdict-neutral in **both** directions, not merely an
accept-superset. -/
theorem isEquiv_eq_withoutPtr (l r : Level) :
    isEquiv l r
      = (if simplify l = simplify r then pure true
         else do if ← leq l r then leq r l else pure false) := by
  rw [isEquiv]
  by_cases h : (l == r) = true
  · rw [if_pos h, if_pos (congrArg simplify (eq_of_beq h))]
  · rw [if_neg h]

/-- The disjunct, read off: syntactically equal levels are equivalent. -/
theorem isEquiv_of_beq {l r : Level} (h : (l == r) = true) :
    isEquiv l r = some true := by rw [isEquiv, if_pos h]; rfl

theorem isEquiv_sound' {l r : Level} (h : isEquiv l r = some true) :
    ∀ φ, eval φ l = eval φ r := by
  intro φ
  by_cases hss : simplify l = simplify r
  · have := congrArg (eval φ) hss
    rwa [eval_simplify, eval_simplify] at this
  · rw [isEquiv_eq_withoutPtr, if_neg hss] at h
    obtain ⟨h1, h2⟩ := bind_and_some_true h
    exact Nat.le_antisymm (leq_sound h1 φ) (leq_sound h2 φ)

/-- Pointwise evaluation equality of two level lists. -/
def EvalEqList (φ : Name → Nat) : List Level → List Level → Prop
  | [], [] => True
  | u :: us, v :: vs => eval φ u = eval φ v ∧ EvalEqList φ us vs
  | _, _ => False

/-- Pointwise soundness of level-list equivalence. -/
theorem isEquivList_sound : ∀ {us vs : List Level}, isEquivList us vs = some true →
    ∀ φ, EvalEqList φ us vs
  | [], [], _, φ => trivial
  | u :: us, v :: vs, h, φ => by
    obtain ⟨h1, h2⟩ := bind_and_some_true (by simpa [isEquivList] using h)
    exact ⟨isEquiv_sound' h1 φ, isEquivList_sound h2 φ⟩
  | [], _ :: _, h, φ => by simp [isEquivList] at h
  | _ :: _, [], h, φ => by simp [isEquivList] at h

theorem isEquivList_length : ∀ {us vs : List Level}, isEquivList us vs = some true →
    us.length = vs.length
  | [], [], _ => rfl
  | u :: us, v :: vs, h => by
    obtain ⟨-, h2⟩ := bind_and_some_true (by simpa [isEquivList] using h)
    simpa using isEquivList_length h2
  | [], _ :: _, h => by simp [isEquivList] at h
  | _ :: _, [], h => by simp [isEquivList] at h

/-- Pointwise-equivalent substitutions induce the same assignment. -/
theorem substFn_congr {φ : Name → Nat} : ∀ {ks : List Name} {us vs : List Level},
    EvalEqList φ us vs → substFn φ ks us = substFn φ ks vs := by
  intro ks
  induction ks with
  | nil => intro us vs _; funext n; cases us <;> cases vs <;> simp [substFn]
  | cons k ks ih =>
    intro us vs h
    cases us with
    | nil =>
      cases vs with
      | nil => rfl
      | cons v vs => exact absurd h (by simp [EvalEqList])
    | cons u us =>
      cases vs with
      | nil => exact absurd h (by simp [EvalEqList])
      | cons v vs =>
        obtain ⟨hu, hrest⟩ : eval φ u = eval φ v ∧ EvalEqList φ us vs := h
        funext n
        simp only [substFn]
        split
        · exact hu
        · exact congrFun (ih hrest) n

/-- Evaluation reads the assignment only at the level's parameters. -/
theorem eval_ext {ps : List Name} : ∀ {u : Level}, u.allParamsDefined ps = true →
    ∀ {φ₁ φ₂ : Name → Nat}, (∀ p ∈ ps, φ₁ p = φ₂ p) → eval φ₁ u = eval φ₂ u := by
  intro u
  induction u with
  | zero => intro _ _ _ _; rfl
  | succ v ih => intro h φ₁ φ₂ hφ; simp only [eval, ih h hφ]
  | max a b iha ihb =>
    intro h φ₁ φ₂ hφ
    simp only [allParamsDefined, Bool.and_eq_true] at h
    simp only [eval, iha h.1 hφ, ihb h.2 hφ]
  | imax a b iha ihb =>
    intro h φ₁ φ₂ hφ
    simp only [allParamsDefined, Bool.and_eq_true] at h
    simp only [eval, iha h.1 hφ, ihb h.2 hφ]
  | param n =>
    intro h φ₁ φ₂ hφ
    exact hφ n (by simpa [allParamsDefined] using h)

/-- Substituting pre-substituted levels agrees with composing assignments,
at the substituted parameters. -/
theorem substFn_map_subst {φ : Name → Nat} {ks : List Name} {vs : List Level} :
    ∀ {ks' : List Name} {ws : List Level} {p : Name},
      ws.length = ks'.length → p ∈ ks' →
      substFn φ ks' (ws.map (subst ks vs)) p = substFn (substFn φ ks vs) ks' ws p := by
  intro ks'
  induction ks' with
  | nil => intro ws p _ hp; simp at hp
  | cons k ks' ih =>
    intro ws p hal hp
    cases ws with
    | nil => simp at hal
    | cons w ws =>
      simp only [List.map, substFn]
      split
      · exact eval_subst φ ks vs w
      · next hne =>
        refine ih (by simpa using hal) ?_
        rcases List.mem_cons.mp hp with rfl | h
        · exact absurd rfl hne
        · exact h

/-- Substituting a parameter list for itself is the identity assignment. -/
theorem substFn_map_param {φ : Name → Nat} :
    ∀ {ks : List Name} {p : Name}, substFn φ ks (ks.map .param) p = φ p := by
  intro ks
  induction ks with
  | nil => intro p; rfl
  | cons k ks ih =>
    intro p
    simp only [List.map, substFn]
    split
    · next h => rw [← h]; rfl
    · exact ih

/-- `substFn` only reads the assignment through the substituted levels'
parameters (given membership and alignment). -/
theorem substFn_ext {φ₁ φ₂ : Name → Nat} {ps : List Name}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ {ks' : List Name} {ws : List Level},
      (∀ u ∈ ws, u.allParamsDefined ps = true) → ws.length = ks'.length →
      ∀ p ∈ ks', substFn φ₁ ks' ws p = substFn φ₂ ks' ws p := by
  intro ks'
  induction ks' with
  | nil => intro ws _ _ p hp; simp at hp
  | cons k ks' ih =>
    intro ws hws hal p hp
    cases ws with
    | nil => simp at hal
    | cons w ws =>
      simp only [substFn]
      split
      · exact eval_ext (hws w (by simp)) hφ
      · next hne =>
        refine ih (fun u hu => hws u (by simp [hu])) (by simpa using hal) p ?_
        rcases List.mem_cons.mp hp with rfl | h
        · exact absurd rfl hne
        · exact h

theorem isEquiv_sound {l r : Level} (h : isEquiv l r = some true) :
    ∀ φ, eval φ l = eval φ r :=
  isEquiv_sound' h


/-! ## Substitution under pointwise-equal evaluations

Relocated from `ConLeche/TTVerify/DefEqStep.lean` (task #148, T3): the
fact both lanes' same-head spine short-circuits need, and a statement
about levels alone. -/

/-- Level lists with pointwise equal evaluations are indistinguishable
to a substitution.  The checker compares levels with `Level.isEquiv`,
which is sound for `eval` and nothing stronger, so this is exactly the
form the spine short-circuit's soundness needs. -/
theorem substFn_of_evalEqList {φ : Name → Nat} :
    ∀ (ks : List Name) {us us' : List Level}, EvalEqList φ us us' →
      ∀ p, substFn φ ks us p = substFn φ ks us' p := by
  intro ks
  induction ks with
  | nil =>
    intro us us' h p
    cases us <;> cases us' <;> simp [substFn] <;> exact nomatch h
  | cons k ks ih =>
    intro us us' h p
    cases us with
    | nil => cases us' with
      | nil => rfl
      | cons _ _ => exact nomatch h
    | cons u uss => cases us' with
      | nil => exact nomatch h
      | cons u' uss' =>
        obtain ⟨h1, h2⟩ := h
        simp only [substFn]
        split
        · exact h1
        · exact ih h2 p

/-- A declaration read at its *own* level parameters is read at the
ambient assignment.  Every basis constant's type mentions its siblings
this way. -/
theorem substFn_param_self (φ : Name → Nat) :
    ∀ (ks : List Name), Level.substFn φ ks (ks.map Level.param) = φ := by
  intro ks
  induction ks with
  | nil => funext n; rfl
  | cons k ks ih =>
    funext n
    by_cases h : k = n
    · subst h; simp [Level.substFn, Level.eval]
    · simp only [List.map_cons, Level.substFn, if_neg h]
      exact congrFun ih n

end ConLeche.Level
