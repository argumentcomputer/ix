import IxCC.Rt.Rc.Gen.Proof.ReleaseInvariant

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Own IxCC.Own.Rc
open IxCC.Rt.Proof

theorem valueWord_immediate_tag {addresses : AddressMap} {value : RVal} {word : Word}
    (hw : valueWord addresses value = some word) (hn : ∀ location, value ≠ .loc location) :
    word &&& 1 = 1 := by
  cases value with
  | loc location => exact False.elim (hn location rfl)
  | erased => simp [valueWord] at hw; subst word; decide
  | lit literal =>
    cases literal with
    | str text => simp [valueWord] at hw
    | nat n => exact (odd_word (natWord_toNat hw)).1
  | ctor0 ctor =>
    simp only [valueWord] at hw
    split at hw
    · rename_i hguard
      have htag : ctor.tag ≤ maxTag := by simpa using (Bool.and_eq_true_iff.mp hguard).2
      have he : ctor0Word ctor.tag = word := Option.some.inj hw
      rw [← he]
      apply (odd_word (ctor0Word_toNat ?_)).1
      unfold maxTag natLimit at *
      omega
    · cases hw

theorem ReleaseInvariant.consume_immediate
    {heap addresses mem external value frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external (some value) frames context base bump limit slots lists)
    (hn : ∀ location, value ≠ .loc location) :
    ReleaseInvariant cmax heap addresses mem external none frames context base bump limit slots lists := by
  refine {h with balance := ?_}
  intro location
  have hb := h.balance location
  simpa [refsIn, hn location] using hb

/-- The immediate branch of the real current-value dispatcher consumes one
logical pending token and changes no memory. Tag correctness is derived from
the encoded source value. -/
theorem ReleaseInvariant.immediate_step
    {heap addresses mem external value frames context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external (some value) frames context base bump limit slots lists)
    (hn : ∀ location, value ≠ .loc location) (word : Word)
    (hw : valueWord addresses value = some word)
    (env : Env) (h1 : env[1]? = some word) (h2 : env[2]? = some (cursorHead frames)) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 1 0) 0
      (releaseState mem context (env.insert 8 (cursorHead frames)) 6 0) ∧
    ReleaseInvariant cmax heap addresses mem external none frames context base bump limit slots lists := by
  have htag := valueWord_immediate_tag hw hn
  refine ⟨?_, h.consume_immediate hn⟩
  apply Sem.Star.free (s' := releaseState mem context (env.insert 8 (cursorHead frames)) 6 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, h1, h2, Cond.holds, htag]
  exact .refl _




end IxCC.Rt.Rc.Gen
