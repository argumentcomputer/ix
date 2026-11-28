import IxCC.Lam.Erase
import IxCC.Lam.Proof.ModesOk

/-! # Erasure's output is `ModesOk`

A by-name binder's dispatch signature comes from how the δ body of a `lazy`
constant applies that parameter, which erasure does not constrain (a `lazy`
hint needs only a safe definition with enough leading λs), so erasure checks
its output with ANF's own checker (`erase-modes`). `erase_modesOk` states
the result both as the checker's verdict and as `ModesOkSpec`. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

/-- **Erasure's output is `ModesOk`.** -/
theorem erase_modesOk {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) : Lam.ModesOk L := by
  unfold erase at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  · split at h
    · cases h
    · next hm =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      show modesOk _ = true
      simpa using hm

/-- The same, as the proposition `ModesOkSpec`. -/
theorem erase_modesOkSpec {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) : ModesOkSpec L :=
  modesOk_sound (erase_modesOk h)

end IxCC.Lam.Erase.Proof
