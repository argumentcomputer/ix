module

public import ConLeche.Model.IndRecs
import ConLeche.Semantics.ProjPhase
public section

/-!
# The projection phase's renaming and valuation invariant, P tier
(task #161, IND TIER part 10)

`ProjPhaseInvS`'s annotated half.  v1's phase invariant has three
conjuncts, each pairing a *lookup* (the model artifact is stored, with
matching level parameters) with a *valuation* identification; the
lookups are V-free and consumed from the v1 predicate directly, so the
P tier stores only the three `acval` equations — exactly the
`BlockInstalledTT` / `BlockAcvalInstalled` split the member phase
already uses.

`projFwd_renameOk` is then `projFwd_renameOkT`'s twin: its first two
clauses are *literally* v1's (`RenameOk` and `RenameOkT` share them),
and only the valuation clause is re-proved at the annotated valuation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps projFnName projModelName projFwd ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]

/-- **The projection phase's annotated valuation invariant**: the
parent type, the constructor and every installed projection function
carry their model artifact's *leaf*.  `ProjPhaseInvS`'s third
component, one currency over; the lookups stay in the v1 predicate. -/
@[expose] def ProjPhaseAcval (T ctorName : Name) (nF : Nat) (env' : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) : Prop :=
  ((env'.find? T).isSome = true →
    ∀ ψ : Name → Nat, acval T ψ = acval (T.str "_model") ψ) ∧
  ((env'.find? ctorName).isSome = true →
    ∀ ψ : Name → Nat,
      acval ctorName ψ = acval (ctorName.str "_model") ψ) ∧
  (∀ j, j < nF → (env'.find? (projFnName T j)).isSome = true →
    ∀ ψ : Name → Nat,
      acval (projFnName T j) ψ = acval (projModelName T j) ψ)

/-- The projection renaming, pruned to the stored names, is sound at
the reading.  Its first two clauses are v1's verbatim
(`projFwd_renameOkT`); only the valuation clause is new, and its three
cases *are* `ProjPhaseAcval`'s three conjuncts. -/
theorem projFwd_renameOk {T ctorName : Name} {nF : Nat} {env' : Env}
    {cval : TConstVal} {acval : Name → (Name → Nat) → AnnotTerm}
    (hinv : ProjPhaseInvS T ctorName nF env' cval)
    (hinvA : ProjPhaseAcval T ctorName nF env' acval) :
    RenameOk acval env' (fun n => if (env'.find? n).isSome = true then
      projFwd T ctorName nF n else n) := by
  refine ⟨(projFwd_renameOkT hinv).1,
    (projFwd_renameOkT hinv).2.1, ?_⟩
  intro n ψ
  dsimp only
  cases hf : env'.find? n with
  | none =>
    rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
      from fun hx => nomatch hx)]
  | some ci =>
    rw [if_pos (show (some ci : Option ConstantInfo).isSome = true
      from rfl)]
    unfold projFwd
    try dsimp only
    by_cases h1 : n = T
    · subst h1
      rw [if_pos rfl]
      exact (hinvA.1 (by rw [hf]; rfl) ψ).symm
    rw [if_neg h1]
    by_cases h2 : n = ctorName
    · subst h2
      rw [if_pos rfl]
      exact (hinvA.2.1 (by rw [hf]; rfl) ψ).symm
    rw [if_neg h2]
    cases hfind : (List.range nF).find?
      (fun j => n == projFnName T j) with
    | none => rfl
    | some j =>
      have hjlt : j < nF :=
        List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hn : n = projFnName T j := by
        have hprop := List.find?_some hfind
        exact eq_of_beq (by simpa using hprop)
      subst hn
      exact (hinvA.2.2 j hjlt (by rw [hf]; rfl) ψ).symm

/-- **The annotated phase invariant crosses a projection cons.**
`projPhaseInvS_cons`'s twin: the head's name is `projFnName T i`, which
is neither `T`, nor the constructor, nor any *other* field's slot, nor
any model artifact's name — so the three equations are either the
installed one (`acvalWith_self`) or carried unchanged. -/
theorem projPhaseAcval_cons {T ctorName : Name} {nF : Nat}
    {env' : Env} {acval : Name → (Name → Nat) → AnnotTerm}
    {c₀ : ConstantInfo} {i : Nat}
    (hname : c₀.name = projFnName T i)
    (hinvA : ProjPhaseAcval T ctorName nF env' acval)
    (hfresh : env'.find? (projFnName T i) = none)
    (hTf : (env'.find? T).isSome = true)
    (hCf : (env'.find? ctorName).isSome = true)
    (hilt : i < nF)
    (A : (Name → Nat) → AnnotTerm)
    (hself : ∀ ψ : Name → Nat, A ψ = acval (projModelName T i) ψ) :
    ProjPhaseAcval T ctorName nF ⟨c₀ :: env'.consts⟩
      (acvalWith acval c₀.name A) := by
  -- the head's name differs from every name the invariant reads
  have hneP : ∀ n : Name, (env'.find? n).isSome = true →
      n ≠ projFnName T i := by
    intro n hn hh
    rw [hh, hfresh] at hn
    exact nomatch hn
  have hmodelNeP : ∀ j : Nat, projModelName T j ≠ projFnName T i :=
    fun j hh => ConLeche.Name.num_ne_str _ _ _ _ hh.symm
  have hstrNeP : ∀ n : Name, n.str "_model" ≠ projFnName T i :=
    fun n hh => ConLeche.Name.num_ne_str _ _ _ _ hh.symm
  have hne : ∀ n : Name, n ≠ projFnName T i → n ≠ c₀.name :=
    fun n hn hh => hn (by rw [hh, hname])
  have hdown : ∀ n : Name, n ≠ projFnName T i →
      (Env.find? ⟨c₀ :: env'.consts⟩ n).isSome = true →
      (env'.find? n).isSome = true := by
    intro n hn hs
    rw [Env.find?_cons, if_neg (fun hh => hn (by rw [← hh, hname]))]
      at hs
    exact hs
  refine ⟨?_, ?_, ?_⟩
  · intro hT ψ
    rw [acvalWith_ne (hne T (hneP T hTf)),
      acvalWith_ne (hne _ (hstrNeP T))]
    exact hinvA.1 hTf ψ
  · intro hC ψ
    rw [acvalWith_ne (hne ctorName (hneP ctorName hCf)),
      acvalWith_ne (hne _ (hstrNeP ctorName))]
    exact hinvA.2.1 hCf ψ
  · intro j hj hP ψ
    by_cases hji : j = i
    · subst hji
      rw [← hname, acvalWith_self, acvalWith_ne (hne _ (hmodelNeP j))]
      exact hself ψ
    · have hjneP : projFnName T j ≠ projFnName T i := by
        intro hh
        have hh2 : ConLeche.Name.num (T.str "proj") j
          = ConLeche.Name.num (T.str "proj") i := hh
        injection hh2 with _hp hij
        exact hji hij
      rw [acvalWith_ne (hne _ hjneP),
        acvalWith_ne (hne _ (hmodelNeP j))]
      exact hinvA.2.2 j hj (hdown _ hjneP hP) ψ

end ConLeche.Model
