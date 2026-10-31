module

public import IxC.Kernel.Verify.Rename.CoreDefs

@[expose] public section

/-!
# Success simulation of a renamed run

`SimE G m x x'`: every success of the original run `x` is a success of the
renamed run `x'` with the renamed result (`m`), and the result satisfies
`G` (is good). The renaming lemma is stated success-only (the owner's
decision of 2026-10-16), so nothing is said where `x` fails.

The combinators follow the shape of the checker's `do` blocks: `pure`,
`bind` (one bind peeled at a time), `throw` (an original failure promises
nothing), the conditionals. `CoreSim P f r r'` says the same of every entry
of two core records, one renamed: the hypothesis the knot's bodies are
walked under (`IxC/Kernel/Verify/Rename/Core*.lean`).
-/

set_option linter.unusedSimpArgs false

namespace Ix.Kernel

variable {md md' : Mode} {f : md.Id → md'.Id} {P : KeyScope md}

/-- **Success simulation**: every success of `x` satisfies `G` and is a
success of `x'`, renamed by `m`. -/
def SimE {ε ε' α α' : Type} (G : α → Prop) (m : α → α') (x : Except ε α) (x' : Except ε' α') :
    Prop :=
  ∀ a, x = .ok a → G a ∧ x' = .ok (m a)

namespace SimE

variable {ε ε' α α' β β' : Type} {G : α → Prop} {m : α → α'}

theorem pure' {a : α} {a' : α'} (hG : G a) (h : a' = m a) :
    SimE G m (pure a : Except ε α) (pure a' : Except ε' α') := by
  intro b hb
  cases hb
  exact ⟨hG, by rw [h]; rfl⟩

theorem ok' {a : α} {a' : α'} (hG : G a) (h : a' = m a) :
    SimE G m (.ok a : Except ε α) (.ok a' : Except ε' α') :=
  pure' hG h

theorem throw' {e : ε} {x' : Except ε' α'} : SimE G m (throw e : Except ε α) x' :=
  fun _ h => nomatch h

theorem error' {e : ε} {x' : Except ε' α'} : SimE G m (.error e : Except ε α) x' :=
  fun _ h => nomatch h

/-- A run that never succeeds simulates anything. -/
theorem of_fail {x : Except ε α} {x' : Except ε' α'} (h : ∀ a, x ≠ .ok a) : SimE G m x x' :=
  fun a ha => absurd ha (h a)

/-- A failure followed by anything. -/
theorem throw_bind {β : Type} {e : ε} {k : β → Except ε α} {x' : Except ε' α'} :
    SimE G m ((throw e : Except ε β) >>= k) x' :=
  fun _ h => nomatch h

/-- Peel one bind. -/
theorem bind {G₂ : β → Prop} {m₂ : β → β'} {x : Except ε α} {x' : Except ε' α'}
    {k : α → Except ε β} {k' : α' → Except ε' β'} (hx : SimE G m x x')
    (hk : ∀ a, G a → SimE G₂ m₂ (k a) (k' (m a))) : SimE G₂ m₂ (x >>= k) (x' >>= k') := by
  intro b hb
  cases hxa : x with
  | error e => rw [hxa] at hb; exact nomatch hb
  | ok a =>
    rw [hxa] at hb
    obtain ⟨hGa, hx'⟩ := hx a hxa
    rw [hx']
    exact hk a hGa b hb

/-- Conditionals whose conditions agree. -/
theorem ite {c c' : Prop} [Decidable c] [Decidable c'] {t e : Except ε α} {t' e' : Except ε' α'}
    (hc : c ↔ c') (ht : c → SimE G m t t') (he : ¬c → SimE G m e e') :
    SimE G m (if c then t else e) (if c' then t' else e') := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc.mp h)]; exact ht h
  · rw [if_neg h, if_neg (fun h' => h (hc.mpr h'))]; exact he h

/-- **A guard**: a condition the original passes the renamed run passes,
and the original's other branch fails. -/
theorem ite_guard {c c' : Prop} [Decidable c] [Decidable c'] {t e : Except ε α}
    {t' e' : Except ε' α'} (hc : c → c') (ht : c → SimE G m t t') (he : ∀ a, e ≠ .ok a) :
    SimE G m (if c then t else e) (if c' then t' else e') := by
  by_cases h : c
  · rw [if_pos h, if_pos (hc h)]; exact ht h
  · rw [if_neg h]; exact of_fail he

/-- Rewrite the renamed run. -/
theorem congr {x : Except ε α} {x'₁ x'₂ : Except ε' α'} (h : x'₁ = x'₂) (hs : SimE G m x x'₁) :
    SimE G m x x'₂ :=
  h ▸ hs

/-- Weaken the goodness. -/
theorem mono {G' : α → Prop} {x : Except ε α} {x' : Except ε' α'} (hG : ∀ a, G a → G' a)
    (hs : SimE G m x x') : SimE G' m x x' :=
  fun a h => let ⟨hg, h'⟩ := hs a h; ⟨hG a hg, h'⟩

/-- Equal runs simulate each other at the identity. -/
theorem refl {x : Except ε α} {x' : Except ε' α} (h : ∀ a, x = .ok a → x' = .ok a) :
    SimE (fun _ => True) id x x' :=
  fun a ha => ⟨trivial, h a ha⟩

/-- A simulation at the identity with a trivial goodness: equal successes. -/
theorem of_eq {x : Except ε α} (x' : Except ε' α) (h : ∀ a, x = .ok a → x' = .ok a) :
    SimE (fun _ => True) id x x' :=
  refl h

end SimE

/-- `liftFueled` at a key-free value is the same on both sides. -/
theorem SimE.liftFueled {α : Type} (what : String) (o : Option α) :
    SimE (fun _ => True) id (liftFueled what o : CheckM md α) (liftFueled what o : CheckM md' α) := by
  cases o with
  | none => exact SimE.throw'
  | some a => exact SimE.pure' trivial rfl

/-! ## The core records -/

/-- **Two core records, one the renaming of the other**, on good
arguments: every entry's success is the renamed entry's, with a good
result. -/
structure CoreSim (P : KeyScope md) (f : md.Id → md'.Id) (r : (CoreFns md) (CheckM md))
    (r' : (CoreFns md') (CheckM md')) : Prop where
  whnfCore : ∀ d (e : Expr md), e.Good P →
    SimE (Expr.Good P) (Expr.mapKeys f) (r.whnfCore d e) (r'.whnfCore d (e.mapKeys f))
  whnf : ∀ d (e : Expr md), e.Good P →
    SimE (Expr.Good P) (Expr.mapKeys f) (r.whnf d e) (r'.whnf d (e.mapKeys f))
  infer : ∀ d (e : Expr md), e.Good P →
    SimE (Expr.Good P) (Expr.mapKeys f) (r.infer d e) (r'.infer d (e.mapKeys f))
  defeq : ∀ d (a b : Expr md), a.Good P → b.Good P →
    SimE (fun _ => True) id (r.defeq d a b) (r'.defeq d (a.mapKeys f) (b.mapKeys f))
  annotate : ∀ d (e : Expr md), e.Good P →
    SimE (Expr.Good P) (Expr.mapKeys f) (r.annotate d e) (r'.annotate d (e.mapKeys f))
  inferIO : ∀ d (e : Expr md), e.Good P →
    SimE (Expr.Good P) (Expr.mapKeys f) (r.inferIO d e) (r'.inferIO d (e.mapKeys f))

/-- The io-grade views of related records are related. -/
theorem CoreSim.ioView {r : (CoreFns md) (CheckM md)} {r' : (CoreFns md') (CheckM md')}
    (h : CoreSim P f r r') : CoreSim P f r.ioView r'.ioView :=
  ⟨h.whnfCore, h.whnf, h.inferIO, h.defeq, h.annotate, h.inferIO⟩

/-- The exhausted knot level simulates anything: it only fails. -/
theorem CoreSim.zero (mode : CheckMode) (env : Env md) (env' : Env md') :
    CoreSim P f (coreKnot mode env id 0) (coreKnot mode env' id 0) :=
  ⟨fun _ _ _ => SimE.throw', fun _ _ _ => SimE.throw', fun _ _ _ => SimE.throw',
    fun _ _ _ _ _ => SimE.throw', fun _ _ _ => SimE.throw', fun _ _ _ => SimE.throw'⟩

end Ix.Kernel
