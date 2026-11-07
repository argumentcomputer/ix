import IxCC.Sem.TracedTransform

/-!
# A toy big-step language with IO

The IO toy checks the traced clause shapes of decision D-1 on a pipeline
like M2.1's (`IxCCTests.Sem.Toy`): the same first-order language of
one-argument functions with a depth clock, plus two event-producing
constructs, `out a e` (output the value of `a`, then evaluate `e`) and
`inp` (input a number). An abstract oracle answers an input from the events
performed so far; theorems quantify over it.

A computation `M α` reads the events performed before it and returns the
traced outcome of its own events: results sequence as `Result.bind` and
traces append (`M.bind`). The evaluator is written in bind form, clause for
clause as `Toy.Big.evalAt`, and its clock lemmas (`evalAt_agree`: clock
monotonicity, `evalAt_dom`: a program runs no further than another) have
the pure toy's per-construct proofs over the traced combinators
`MAgrees.bind` and `MDom.bind`, plus one case per new construct.
-/

namespace IxCCTests.Sem.Toy.IO

open IxCC.Sem

/-- The toy's events: an output, or an input with the oracle's answer. -/
inductive Ev where
  | out (n : Nat)
  | inp (n : Nat)
  deriving DecidableEq, Repr

/-- The toy's environment: the answer to an input, given the events so
far. -/
abbrev Oracle := List Ev → Nat

inductive Expr where
  | lit (n : Nat)
  | arg
  | add (a b : Expr)
  | sub (a b : Expr)
  /-- `ifz c t e`: `t` if `c` is zero, else `e`. -/
  | ifz (c t e : Expr)
  /-- Call function `f` on `a`; charges the clock. -/
  | call (f : Nat) (a : Expr)
  /-- Charge the clock, then evaluate `e`. -/
  | tick (e : Expr)
  /-- Output the value of `a`, then evaluate `e`. -/
  | out (a e : Expr)
  /-- Input a number from the environment. -/
  | inp
  deriving Repr, Inhabited

/-- `n` ticks around `e`. -/
def ticks : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => .tick (ticks n e)

/-- Function bodies; function 0 is `main`. -/
abbrev Prog := List Expr

/-- A computation: from the events performed so far, its outcome and the
events it performs. -/
abbrev M (α : Type) := List Ev → Traced Ev α

namespace M

variable {α β : Type}

def pure (v : α) : M α := fun _ => ⟨.ok v, []⟩

/-- An outcome with no event (`timeout` or `stuck`). -/
def halt (r : Result α) : M α := fun _ => ⟨r, []⟩

/-- Sequencing: results as `Result.bind`, traces appended; the continuation
sees the events so far. -/
def bind (m : M α) (f : α → M β) : M β := fun h =>
  match (m h).result with
  | .ok v => ⟨(f v (h ++ (m h).trace)).result, (m h).trace ++ (f v (h ++ (m h).trace)).trace⟩
  | .timeout => ⟨.timeout, (m h).trace⟩
  | .resource r => ⟨.resource r, (m h).trace⟩
  | .trap => ⟨.trap, (m h).trace⟩
  | .stuck => ⟨.stuck, (m h).trace⟩

/-- Perform an event. -/
def emit (e : Ev) : M Unit := fun _ => ⟨.ok (), [e]⟩

/-- Input: the oracle's answer from the events so far, performed as an
event. -/
def input (o : Oracle) : M Nat := fun h => ⟨.ok (o h), [.inp (o h)]⟩

theorem bind_ok {m : M α} {f : α → M β} {h : List Ev} {v : α} (hm : (m h).result = .ok v) :
    m.bind f h = ⟨(f v (h ++ (m h).trace)).result, (m h).trace ++ (f v (h ++ (m h).trace)).trace⟩ := by
  simp only [M.bind, hm]

/-- The trace of a sequence starts with the trace of its first part. -/
theorem prefix_bind (m : M α) (f : α → M β) (h : List Ev) : (m h).trace <+: (m.bind f h).trace := by
  unfold M.bind
  cases (m h).result <;> simp

/-- A sequence returns a value exactly when both parts do. -/
theorem bind_eq_ok {m : M α} {f : α → M β} {h : List Ev} {w : β} {tr : List Ev} :
    m.bind f h = ⟨.ok w, tr⟩ ↔
      ∃ v tr₁ tr₂, m h = ⟨.ok v, tr₁⟩ ∧ f v (h ++ tr₁) = ⟨.ok w, tr₂⟩ ∧ tr = tr₁ ++ tr₂ := by
  constructor
  · intro e
    cases hr : (m h).result with
    | ok v =>
      rw [bind_ok hr] at e
      injection e with e₁ e₂
      exact ⟨v, (m h).trace, _, Traced.ext hr rfl, Traced.ext e₁ rfl, e₂.symm⟩
    | _ => simp [M.bind, hr] at e
  · rintro ⟨v, tr₁, tr₂, hm, hf, rfl⟩
    rw [bind_ok (by rw [hm])]
    simp [hm, hf]

/-- A sequence that does not return a value stopped in its first part, with
that part's outcome and trace, or in its second part. -/
theorem bind_stop {m : M α} {f : α → M β} {h : List Ev}
    (hne : ∀ w, (m.bind f h).result ≠ .ok w) :
    ((∀ v, (m h).result ≠ .ok v) ∧ (m.bind f h).trace = (m h).trace ∧
        ((m.bind f h).result = .timeout ↔ (m h).result = .timeout)) ∨
      ∃ v, (m h).result = .ok v ∧ (∀ w, (f v (h ++ (m h).trace)).result ≠ .ok w) ∧
        m.bind f h = ⟨(f v (h ++ (m h).trace)).result, (m h).trace ++ (f v (h ++ (m h).trace)).trace⟩ := by
  cases hr : (m h).result with
  | ok v =>
    refine .inr ⟨v, rfl, fun w e => hne w ?_, bind_ok hr⟩
    rw [bind_ok hr]
    exact e
  | _ => exact .inl ⟨(fun _ e => nomatch e), by simp [M.bind, hr], by simp [M.bind, hr]⟩

end M

/-! ## Clock comparisons -/

/-- `t'` is `t` wherever `t` does not time out, and extends its trace:
`t'` runs at least as far as `t`. -/
def TAgrees {α : Type} (t' t : Traced Ev α) : Prop :=
  (t.result ≠ .timeout → t' = t) ∧ t.trace <+: t'.trace

/-- `t'` is `t`, or a timeout after a prefix of `t`'s trace: `t'` runs no
further than `t`. -/
def TDom {α : Type} (t' t : Traced Ev α) : Prop :=
  t' = t ∨ (t'.result = .timeout ∧ t'.trace <+: t.trace)

/-- `TAgrees` from every history. -/
def MAgrees {α : Type} (m' m : M α) : Prop := ∀ h, TAgrees (m' h) (m h)

/-- `TDom` from every history. -/
def MDom {α : Type} (m' m : M α) : Prop := ∀ h, TDom (m' h) (m h)

section

variable {α β : Type}

theorem TAgrees.trans {a b c : Traced Ev α} (h₁ : TAgrees a b) (h₂ : TAgrees b c) :
    TAgrees a c :=
  ⟨fun hc => by
    have e := h₂.1 hc
    rw [h₁.1 (by rw [e]; exact hc), e], h₂.2.trans h₁.2⟩

/-- Upward agreement at every pair of clocks is trace monotonicity. -/
theorem TAgrees.traceMono {c : Nat → Traced Ev α}
    (h : ∀ k k', k ≤ k' → TAgrees (c k') (c k)) : TraceMono c where
  final k k' hle hk := (h k k' hle).1 hk
  grows k k' hle := (h k k' hle).2

theorem TDom.trans {a b c : Traced Ev α} (h₁ : TDom a b) (h₂ : TDom b c) : TDom a c := by
  rcases h₁ with rfl | ⟨ha, hp⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨_, hp'⟩
    · exact .inr ⟨ha, hp⟩
    · exact .inr ⟨ha, hp.trans hp'⟩

/-- A run no further than a timeout is a timeout after a prefix of its
trace. -/
theorem TDom.timeout {t' t : Traced Ev α} (h : TDom t' t) (ht : t.result = .timeout) :
    t'.result = .timeout ∧ t'.trace <+: t.trace := by
  rcases h with rfl | h
  · exact ⟨ht, List.prefix_refl _⟩
  · exact h

/-- A later clock runs at least as far: a smaller one runs no further. -/
theorem TAgrees.dom {t' t : Traced Ev α} (h : TAgrees t' t) : TDom t t' := by
  by_cases ht : t.result = .timeout
  · exact .inr ⟨ht, h.2⟩
  · exact .inl (h.1 ht).symm

theorem MAgrees.refl (m : M α) : MAgrees m m := fun _ => ⟨fun _ => rfl, List.prefix_refl _⟩

theorem MAgrees.trans {a b c : M α} (h₁ : MAgrees a b) (h₂ : MAgrees b c) : MAgrees a c :=
  fun h => (h₁ h).trans (h₂ h)

theorem MDom.refl (m : M α) : MDom m m := fun _ => .inl rfl

theorem MDom.trans {a b c : M α} (h₁ : MDom a b) (h₂ : MDom b c) : MDom a c :=
  fun h => (h₁ h).trans (h₂ h)

/-- A timeout runs no further than anything. -/
theorem MDom.halt_timeout (m : M α) : MDom (M.halt .timeout) m :=
  fun _ => .inr ⟨rfl, List.nil_prefix⟩

theorem MAgrees.bind {m m' : M α} {f f' : α → M β} (hm : MAgrees m' m)
    (hf : ∀ v, MAgrees (f' v) (f v)) : MAgrees (m'.bind f') (m.bind f) := by
  intro h
  obtain ⟨hfin, hpre⟩ := hm h
  cases hr : (m h).result with
  | ok v =>
    have e : m' h = m h := hfin (by rw [hr]; exact nofun)
    have hr' : (m' h).result = .ok v := by rw [e, hr]
    obtain ⟨hfin', hpre'⟩ := hf v (h ++ (m h).trace)
    rw [M.bind_ok hr, M.bind_ok hr', e]
    refine ⟨fun hne => ?_, (List.prefix_append_right_inj _).2 hpre'⟩
    rw [hfin' hne]
  | timeout =>
    refine ⟨fun hne => by simp [M.bind, hr] at hne, ?_⟩
    have : (m.bind f h).trace = (m h).trace := by simp [M.bind, hr]
    rw [this]
    exact hpre.trans (M.prefix_bind _ _ _)
  | _ =>
    have e : m' h = m h := hfin (by rw [hr]; exact nofun)
    refine ⟨fun _ => ?_, ?_⟩ <;> simp [M.bind, e, hr]

theorem MDom.bind {m m' : M α} {f f' : α → M β} (hm : MDom m' m)
    (hf : ∀ v, MDom (f' v) (f v)) : MDom (m'.bind f') (m.bind f) := by
  intro h
  rcases hm h with e | ⟨ht, hp⟩
  · cases hr : (m h).result with
    | ok v =>
      have hr' : (m' h).result = .ok v := by rw [e, hr]
      rw [M.bind_ok hr, M.bind_ok hr', e]
      rcases hf v (h ++ (m h).trace) with e' | ⟨ht', hp'⟩
      · rw [e']
        exact .inl rfl
      · exact .inr ⟨ht', (List.prefix_append_right_inj _).2 hp'⟩
    | _ => exact .inl (by simp [M.bind, e, hr])
  · refine .inr ⟨by simp [M.bind, ht], ?_⟩
    have : (m'.bind f' h).trace = (m' h).trace := by simp [M.bind, ht]
    rw [this]
    exact hp.trans (M.prefix_bind _ _ _)

end

namespace Big

/-- A call at one clock level: the body at the level below, or `stuck` for
an unknown function. -/
def callAt (p : Prog) (below : Nat → Expr → M Nat) (f v : Nat) : M Nat :=
  match p[f]? with
  | some body => below v body
  | none => M.halt .stuck

/-- One clock level with argument `x` under oracle `o`. -/
def evalAt (o : Oracle) (p : Prog) (below : Nat → Expr → M Nat) (x : Nat) : Expr → M Nat
  | .lit n => M.pure n
  | .arg => M.pure x
  | .add a b =>
      (evalAt o p below x a).bind fun va => (evalAt o p below x b).bind fun vb => M.pure (va + vb)
  | .sub a b =>
      (evalAt o p below x a).bind fun va => (evalAt o p below x b).bind fun vb => M.pure (va - vb)
  | .ifz c t e =>
      (evalAt o p below x c).bind fun vc =>
        if vc = 0 then evalAt o p below x t else evalAt o p below x e
  | .call f a => (evalAt o p below x a).bind (callAt p below f)
  | .tick e => below x e
  | .out a e =>
      (evalAt o p below x a).bind fun v => (M.emit (.out v)).bind fun _ => evalAt o p below x e
  | .inp => M.input o

/-- Evaluation with depth clock `k` and argument `x` under oracle `o`. -/
def eval (o : Oracle) (p : Prog) : Nat → Nat → Expr → M Nat
  | 0 => evalAt o p fun _ _ => M.halt .timeout
  | k + 1 => evalAt o p (eval o p k)

/-- Run `main` on `x` under oracle `o` with clock `k`, from no events. -/
def run (p : Prog) (x : Nat) (o : Oracle) (k : Nat) : Traced Ev Nat :=
  match p[0]? with
  | some main => eval o p k x main []
  | none => ⟨.stuck, []⟩

/-- Two clock levels, possibly of two programs, agree where the first does
not time out if their calls and ticks do (the pure toy's
`Big.evalAt_agree`, plus `out` and `inp`). -/
theorem evalAt_agree {o : Oracle} {p p' : Prog} {below below' : Nat → Expr → M Nat} {x : Nat}
    (hcall : ∀ f v, MAgrees (callAt p' below' f v) (callAt p below f v))
    (htick : ∀ v e, MAgrees (below' v e) (below v e)) :
    ∀ e, MAgrees (evalAt o p' below' x e) (evalAt o p below x e)
  | .lit _ => MAgrees.refl _
  | .arg => MAgrees.refl _
  | .add a b => (evalAt_agree hcall htick a).bind fun _ =>
      (evalAt_agree hcall htick b).bind fun _ => MAgrees.refl _
  | .sub a b => (evalAt_agree hcall htick a).bind fun _ =>
      (evalAt_agree hcall htick b).bind fun _ => MAgrees.refl _
  | .ifz c t e => (evalAt_agree hcall htick c).bind fun vc => by
      by_cases h : vc = 0
      · simp only [h, ↓reduceIte]; exact evalAt_agree hcall htick t
      · simp only [h, ↓reduceIte]; exact evalAt_agree hcall htick e
  | .call f a => (evalAt_agree hcall htick a).bind fun v => hcall f v
  | .tick e => htick x e
  | .out a e => (evalAt_agree hcall htick a).bind fun _ =>
      (MAgrees.refl _).bind fun _ => evalAt_agree hcall htick e
  | .inp => MAgrees.refl _

/-- Two clock levels, possibly of two programs: the second runs no further
than the first if their calls and ticks do not. -/
theorem evalAt_dom {o : Oracle} {p p' : Prog} {below below' : Nat → Expr → M Nat} {x : Nat}
    (hcall : ∀ f v, MDom (callAt p' below' f v) (callAt p below f v))
    (htick : ∀ v e, MDom (below' v e) (below v e)) :
    ∀ e, MDom (evalAt o p' below' x e) (evalAt o p below x e)
  | .lit _ => MDom.refl _
  | .arg => MDom.refl _
  | .add a b => (evalAt_dom hcall htick a).bind fun _ =>
      (evalAt_dom hcall htick b).bind fun _ => MDom.refl _
  | .sub a b => (evalAt_dom hcall htick a).bind fun _ =>
      (evalAt_dom hcall htick b).bind fun _ => MDom.refl _
  | .ifz c t e => (evalAt_dom hcall htick c).bind fun vc => by
      by_cases h : vc = 0
      · simp only [h, ↓reduceIte]; exact evalAt_dom hcall htick t
      · simp only [h, ↓reduceIte]; exact evalAt_dom hcall htick e
  | .call f a => (evalAt_dom hcall htick a).bind fun v => hcall f v
  | .tick e => htick x e
  | .out a e => (evalAt_dom hcall htick a).bind fun _ =>
      (MDom.refl _).bind fun _ => evalAt_dom hcall htick e
  | .inp => MDom.refl _

theorem callAt_agree {p : Prog} {below below' : Nat → Expr → M Nat}
    (h : ∀ v e, MAgrees (below' v e) (below v e)) (f v : Nat) :
    MAgrees (callAt p below' f v) (callAt p below f v) := by
  unfold callAt
  split
  · exact h _ _
  · exact MAgrees.refl _

/-- Clock monotonicity: a larger clock agrees wherever a smaller one does
not time out, and extends its trace. -/
theorem eval_agree (o : Oracle) (p : Prog) :
    ∀ {k k' : Nat}, k ≤ k' → ∀ x e, MAgrees (eval o p k' x e) (eval o p k x e)
  | 0, 0, _, _, _ => MAgrees.refl _
  | 0, k' + 1, _, x, e => evalAt_agree
      (callAt_agree fun _ _ _ => ⟨fun h => absurd rfl h, List.nil_prefix⟩)
      (fun _ _ _ => ⟨fun h => absurd rfl h, List.nil_prefix⟩) e
  | k + 1, k' + 1, hle, x, e =>
      evalAt_agree (callAt_agree fun v e => eval_agree o p (by omega) v e)
        (fun v e => eval_agree o p (by omega) v e) e

theorem eval_mono (o : Oracle) (p : Prog) (x : Nat) (e : Expr) (h : List Ev) :
    TraceMono fun k => eval o p k x e h :=
  TAgrees.traceMono fun _ _ hle => eval_agree o p hle x e h

theorem run_mono (p : Prog) (x : Nat) (o : Oracle) : TraceMono (run p x o) := by
  unfold run
  split
  · exact eval_mono o p x _ []
  · exact TraceMono.const _

/-- A smaller clock runs no further. -/
theorem eval_dom_of_le (o : Oracle) (p : Prog) {k k' : Nat} (hle : k ≤ k') (x : Nat)
    (e : Expr) : MDom (eval o p k x e) (eval o p k' x e) :=
  fun h => (eval_agree o p hle x e h).dom

end Big

/-- The IO toy's source language: runs from `main` read an oracle and
perform `Ev`s. -/
instance : TLang Oracle Ev Nat Prog where
  Val := Nat
  run := Big.run
  mono := Big.run_mono
  obs v := some (.nat v)

end IxCCTests.Sem.Toy.IO
