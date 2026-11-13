import IxCCGrounding.Syntax

/-!
# `Ok`'s closure, decided (`IxCCGrounding.Ok`)

`okClosedB` asks, for each constant of `Sl`, each of its run terms and each profile of its level
parameters at which the annotation does not classify it as irrelevant, that every constant at a
position SrcEval may evaluate be classified relevant at the instantiated profile. A concrete
instantiation `ls` of the right length is one of those profiles (`profileOf ls`), and Src's own
exactness lemmas (`PropWhen.holds_profile`, `PropWhen.inst_holds`) turn the profile answer into
the answer at `ls`. So the check gives `OkClosed` at every instantiation (`okClosed_of_check`).
-/

namespace IxCC.Grounding

open IxCC.Src (Term CId Program Levels)

/-- Every list of `n` Booleans is a profile `profiles n` enumerates. -/
theorem mem_profiles : ∀ (n : Nat) (prof : IxCC.Src.Profile), prof.length = n → prof ∈ profiles n
  | 0, prof, h => by rw [List.length_eq_zero_iff.mp h]; simp [profiles]
  | n + 1, prof, h => by
    have hne : prof ≠ [] := by intro h'; rw [h'] at h; simp at h
    have hsplit := List.dropLast_concat_getLast hne
    have hlen : prof.dropLast.length = n := by rw [List.length_dropLast, h]; rfl
    have ih := mem_profiles n prof.dropLast hlen
    simp only [profiles, List.mem_flatMap]
    refine ⟨prof.dropLast, ih, ?_⟩
    cases hb : prof.getLast hne with
    | true => rw [hb] at hsplit; simp [hsplit]
    | false => rw [hb] at hsplit; simp [hsplit]

/-- An argument is irrelevant at `ls` exactly when it is at `ls`'s profile. -/
theorem irrAt_profile (r : IxCC.Src.Rel) (ls : Levels) :
    r.irrAt ls = r.irrP (IxCC.Src.profileOf ls) :=
  IxCC.Src.PropWhen.holds_profile r.irrWhen ls

/-- The constants SrcEval may evaluate at `ls` are those at `ls`'s profile. -/
theorem evalConsts_profile (ls : Levels) :
    ∀ t : Term, evalConsts ls t = evalConstsP (IxCC.Src.profileOf ls) t
  | .var _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app f a _ r => by
    simp only [evalConsts, evalConstsP, irrAt_profile, evalConsts_profile ls f,
      evalConsts_profile ls a]
  | .lam _ _ body => by simp only [evalConsts, evalConstsP, evalConsts_profile ls body]
  | .pi .. => rfl
  | .letE _ r _ v b => by
    simp only [evalConsts, evalConstsP, irrAt_profile, evalConsts_profile ls v,
      evalConsts_profile ls b]
  | .proj _ _ e => by simp only [evalConsts, evalConstsP, evalConsts_profile ls e]
  | .natLit _ => rfl
  | .strLit _ => rfl

/-- **The closure check is sound.** -/
theorem okClosed_of_check {p : Program} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (h : okClosedB p ann Sl = true) : OkClosed p ann (· ∈ Sl) := by
  intro c ls hc hOk t ht d us hd
  obtain ⟨hlen, r, hr, hirr⟩ := hOk
  have hall := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h c hc) t ht)
    (IxCC.Src.profileOf ls) (mem_profiles _ _ (by rw [IxCC.Src.profileOf, List.length_map, hlen]))
  rw [hr] at hall
  rw [irrAt_profile] at hirr
  simp only [hirr, Bool.false_or] at hall
  rw [← evalConsts_profile] at hall
  have hd' := List.all_eq_true.mp hall (d, us) hd
  simp only [Bool.and_eq_true, beq_iff_eq] at hd'
  obtain ⟨hus, hd'⟩ := hd'
  cases hcd : constClass ann d with
  | none => rw [hcd] at hd'; exact absurd hd' (by simp)
  | some r' =>
    rw [hcd] at hd'
    refine ⟨by rw [List.length_map, hus], r', hcd, ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hd'
    simp only [IxCC.Src.Rel.irrAt]
    rw [← IxCC.Src.PropWhen.inst_holds, IxCC.Src.PropWhen.holds_profile]
    exact hd'

end IxCC.Grounding
