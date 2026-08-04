import Ix.Tc.Knot

/-!
# EStateM Hoare kernel for `TcM`

The verification's Hoare kernel, core form. `TcM m = EStateM (TcError m)
(TcState m)` is **non-backtracking**: state written before a throw survives
`tryCatch` (cache inserts, consumed fuel — load-bearing Rust parity, see
Ix/Tc/Monad.lean's module doc). So unlike lean4lean's `M.WF` (StateT over
`Except`, where errors discard state and `throw := nofun`), the triple here
constrains **both outcomes**: an invariant `I` holds on the post-state of
success *and* error, `Q` on success, `E` on error (default trivial — most
proofs never mention it; nontrivial `E` only at catch-and-continue sites).

Scope here: the invariant is a plain predicate over `TcState`.
Verify/State.lean instantiates it with a monotone `VerifyWorld` containing an
immutable catalog and a growing trusted semantic environment; the combinator
lemmas below carry over verbatim.
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

/-- Expose the invariant already carried by a successful `TcM.WF` result.
This is useful when the next verified action needs to construct semantic
provenance from the intermediate state rather than merely consume the stated
postcondition. -/
theorem withInv
    {I : TcState m → Prop} {s : TcState m}
    {x : TcM m alpha} {Q : alpha → TcState m → Prop}
    {E : TcError m → TcState m → Prop}
    (hx : TcM.WF I s x Q E) :
    TcM.WF I s x (fun result after => I after ∧ Q result after) E := by
  intro hI
  have hpost := hx hI
  cases hrun : x s with
  | ok result after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.1, hpost.2⟩
  | error err after =>
      rw [hrun] at hpost
      exact hpost

/-- Retain the concrete execution equation selected by either outcome of a
verified computation.  Semantic boundaries use this strengthening to ensure
that an external certificate is tied to the value production actually
computed, without granting that certificate any state authority. -/
theorem with_run_eq {I : TcState m → Prop} {s : TcState m} {x : TcM m α}
    {Q : α → TcState m → Prop}
    {E : TcError m → TcState m → Prop}
    (hx : TcM.WF I s x Q E) :
    TcM.WF I s x
      (fun value after => Q value after ∧ x s = .ok value after)
      (fun err after => E err after ∧ x s = .error err after) := by
  intro hI
  have hpost := hx hI
  cases hrun : x s with
  | ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩
  | error err after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩

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

/-- Exact non-backtracking equation for an `EStateM` finalizer.  The
finalizer always runs after the body; a finalizer error supersedes either
body outcome, while a successful finalizer retains the body's payload. -/
private theorem tryFinally_eq
    (x : TcM m α) (finalizer : TcM m β) (s : TcState m) :
    tryFinally x finalizer s =
      match x s with
      | .ok a after =>
          match finalizer after with
          | .ok _ final => .ok a final
          | .error err final => .error err final
      | .error err after =>
          match finalizer after with
          | .ok _ final => .error err final
          | .error cleanupErr final => .error cleanupErr final := by
  unfold tryFinally
  change EStateM.map (fun x : α × β => x.1)
    (tryFinally' x (fun _ => finalizer)) s = _
  unfold EStateM.map MonadFinally.tryFinally' EStateM.instMonadFinally
  cases hrun : x s <;>
    simp only [hrun] <;>
    cases hcleanup : finalizer _ <;>
    rfl

/-- A state-independent success fact survives an invariant-preserving
`finally` action.  Both body and finalizer errors retain the invariant; the
error payload remains intentionally unconstrained. -/
theorem tryFinally_const
    {I : TcState m → Prop} {s : TcState m}
    {x : TcM m α} {finalizer : TcM m β} {Q : α → Prop}
    (hx : TcM.WF I s x (fun a _ => Q a))
    (hfinalizer : ∀ s', TcM.WF I s' finalizer (fun _ _ => True)) :
    TcM.WF I s (tryFinally x finalizer) (fun a _ => Q a) := by
  intro hI
  have hbody := hx hI
  rw [tryFinally_eq]
  cases hrun : x s with
  | ok a after =>
      rw [hrun] at hbody
      simp only
      have hfinal := hfinalizer after hbody.1
      cases hcleanup : finalizer after with
      | ok _ final =>
          rw [hcleanup] at hfinal
          simp only
          exact ⟨hfinal.1, hbody.2⟩
      | error err final =>
          rw [hcleanup] at hfinal
          simp only
          exact ⟨hfinal.1, trivial⟩
  | error err after =>
      rw [hrun] at hbody
      simp only
      have hfinal := hfinalizer after hbody.1
      cases hcleanup : finalizer after with
      | ok _ final =>
          rw [hcleanup] at hfinal
          simp only
          exact ⟨hfinal.1, trivial⟩
      | error cleanupErr final =>
          rw [hcleanup] at hfinal
          simp only
          exact ⟨hfinal.1, trivial⟩

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
