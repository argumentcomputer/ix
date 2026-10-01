module

public section

/-!
# Peeling `Except` binds

The one generic lemma the checker's do-block inversions share.  It
lived in `ConLeche/Verify/ProjPinInv.lean` until that module — the
pinned pair entries' install-time invariant — was retired with the
`PSigma'` pin (task #175 W6, 2026-09-05); relocated verbatim.
-/

namespace ConLeche

/-- Peel one `Except` bind.  Peeling rather than inlining the whole
do-block is what keeps these inversions cheap: `simp only [bind,
Except.bind]` materialises the entire nested block and `split`'s
internal `simp` then exceeds its step budget on the larger checkers. -/
theorem exceptBind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-- An `Except` that returns nothing errors.  This is how the main
corollary's conclusion — the chain of the binary's three steps returns
an error — is reached from the absurdity of the environment it would
otherwise have accepted. -/
theorem Except.exists_error_of_not_ok {ε α : Type} {x : Except ε α} (h : ∀ a, x ≠ .ok a) :
    ∃ e, x = .error e := by
  cases x with
  | error e => exact ⟨e, rfl⟩
  | ok a => exact absurd rfl (h a)

end ConLeche
