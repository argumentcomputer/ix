import Ix.Tc.Knot

/-!
# EStateM Hoare kernel for `TcM`

A6 of plans/tc-verify-roadmap.md, M1 core form. `TcM m = EStateM (TcError m)
(TcState m)` is **non-backtracking**: state written before a throw survives
`tryCatch` (cache inserts, consumed fuel — load-bearing Rust parity, see
Ix/Tc/Monad.lean's module doc). So unlike lean4lean's `M.WF` (StateT over
`Except`, where errors discard state and `throw := nofun`), the triple here
constrains **both outcomes**: an invariant `I` holds on the post-state of
success *and* error, `Q` on success, `E` on error (default trivial — most
proofs never mention it; nontrivial `E` only at catch-and-continue sites).

M1 scope: the invariant is a plain predicate over `TcState`. M3 upgrades
this to the ghost `VState` (venv + cache views) with a monotone extension
order; the combinator lemmas below carry over verbatim — only the state
type enriches.
-/

namespace Ix.Tc

variable {m : Mode}

open EStateM (Result)

/-- Hoare triple over `TcM`: from an `I`-state, `x` preserves `I` on both
    outcomes, with postcondition `Q` on success and `E` on error. -/
def TcM.WF (I : TcState m → Prop) (s : TcState m) (x : TcM m α)
    (Q : α → TcState m → Prop)
    (E : TcError m → TcState m → Prop := fun _ _ => True) : Prop :=
  I s →
    match x s with
    | .ok a s' => I s' ∧ Q a s'
    | .error e s' => I s' ∧ E e s'

namespace TcM.WF

theorem pure {I : TcState m → Prop} {Q : α → TcState m → Prop}
    {E : TcError m → TcState m → Prop} {a : α}
    (h : I s → Q a s) : TcM.WF I s (Pure.pure a) Q E :=
  fun hI => ⟨hI, h hI⟩

theorem throw {I : TcState m → Prop} {Q : α → TcState m → Prop}
    {E : TcError m → TcState m → Prop} {e : TcError m}
    (h : I s → E e s) : TcM.WF I s (throw e : TcM m α) Q E :=
  fun hI => ⟨hI, h hI⟩

/-- Weaken postconditions (and strengthen nothing): the workhorse. -/
theorem mono {I : TcState m → Prop} {Q Q' : α → TcState m → Prop}
    {E E' : TcError m → TcState m → Prop} {x : TcM m α}
    (hx : TcM.WF I s x Q E)
    (hq : ∀ a s', Q a s' → Q' a s')
    (he : ∀ e s', E e s' → E' e s') : TcM.WF I s x Q' E' := by
  intro hI
  have := hx hI
  match hxs : x s with
  | .ok a s' => rw [hxs] at this; exact ⟨this.1, hq _ _ this.2⟩
  | .error e s' => rw [hxs] at this; exact ⟨this.1, he _ _ this.2⟩

theorem bind {I : TcState m → Prop} {Q₁ : α → TcState m → Prop}
    {Q₂ : β → TcState m → Prop} {E : TcError m → TcState m → Prop}
    {x : TcM m α} {f : α → TcM m β}
    (hx : TcM.WF I s x Q₁ E)
    (hf : ∀ a s', Q₁ a s' → TcM.WF I s' (f a) Q₂ E) :
    TcM.WF I s (x >>= f) Q₂ E := by
  intro hI
  have hres := hx hI
  show (match (x >>= f) s with
    | .ok a s' => I s' ∧ Q₂ a s'
    | .error e s' => I s' ∧ E e s')
  show (match (EStateM.bind x f) s with
    | .ok a s' => I s' ∧ Q₂ a s'
    | .error e s' => I s' ∧ E e s')
  unfold EStateM.bind
  match hxs : x s with
  | .ok a s' =>
    rw [hxs] at hres
    exact hf a s' hres.2 hres.1
  | .error e s' =>
    rw [hxs] at hres
    exact hres

/-- The error clause feeds the handler's precondition — where
    error-carries-state pays off: the handler starts from the *post-throw*
    state, and `E` is what we know about it. -/
theorem tryCatch {I : TcState m → Prop} {Q : α → TcState m → Prop}
    {E₁ E₂ : TcError m → TcState m → Prop}
    {x : TcM m α} {h : TcError m → TcM m α}
    (hx : TcM.WF I s x Q E₁)
    (hh : ∀ e s', E₁ e s' → TcM.WF I s' (h e) Q E₂) :
    TcM.WF I s (tryCatch x h) Q E₂ := by
  intro hI
  have hres := hx hI
  show (match (EStateM.tryCatch x h : TcM m α) s with
    | .ok a s' => I s' ∧ Q a s'
    | .error e s' => I s' ∧ E₂ e s')
  unfold EStateM.tryCatch
  match hxs : x s with
  | .ok a s' =>
    rw [hxs] at hres
    exact hres
  | .error e s' =>
    rw [hxs] at hres
    exact hh e s' hres.2 hres.1

theorem get {I : TcState m → Prop} {Q : TcState m → TcState m → Prop}
    {E : TcError m → TcState m → Prop}
    (h : I s → Q s s) : TcM.WF I s (get : TcM m (TcState m)) Q E :=
  fun hI => ⟨hI, h hI⟩

theorem set {I : TcState m → Prop} {Q : PUnit → TcState m → Prop}
    {E : TcError m → TcState m → Prop} {s' : TcState m}
    (hI' : I s → I s') (h : I s → Q ⟨⟩ s') :
    TcM.WF I s (set s' : TcM m PUnit) Q E :=
  fun hI => ⟨hI' hI, h hI⟩

theorem modifyGet {I : TcState m → Prop} {Q : α → TcState m → Prop}
    {E : TcError m → TcState m → Prop} {f : TcState m → α × TcState m}
    (hI' : I s → I (f s).2) (h : I s → Q (f s).1 (f s).2) :
    TcM.WF I s (modifyGet f : TcM m α) Q E :=
  fun hI => ⟨hI' hI, h hI⟩

end TcM.WF

/-! ### Validation on real helpers -/

/-- `tick` preserves any fuel-agnostic invariant: consumes one `recFuel` on
    success (throwing `.maxRecFuel` *before* any write when exhausted — the
    state is untouched on the error path). -/
theorem TcM.tick.wf {I : TcState m → Prop}
    (hfuel : ∀ s : TcState m, I s → I { s with recFuel := s.recFuel - 1 }) :
    TcM.WF I s (TcM.tick (m := m))
      (fun _ s' => s'.recFuel = s.recFuel - 1)
      (fun e s' => e = .maxRecFuel ∧ s' = s) := by
  unfold TcM.tick
  refine TcM.WF.bind (Q₁ := fun a s' => a = s ∧ s' = s)
    (TcM.WF.get fun _ => ⟨rfl, rfl⟩) ?_
  rintro a s' ⟨rfl, rfl⟩
  split
  · exact TcM.WF.throw fun _ => ⟨rfl, rfl⟩
  · exact TcM.WF.set (fun hI => hfuel _ hI) (fun _ => rfl)

end Ix.Tc
