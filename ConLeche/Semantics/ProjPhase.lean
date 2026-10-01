module

public import ConLeche.Verify.Denote.Rename
import ConLeche.Kernel.Inductives.Modeled

@[expose] public section

/-!
# The projection phase's fold invariant (task #161, S1)

THE SEPARATION's shared base: `ProjPhaseInvS` and its renaming
soundness, lifted out of `SetR/Install/ProjInstallS.lean` (design
census §3.3, edge 10).  The invariant is a **valuation-equality
predicate** — it quantifies over a `TConstVal` and the environment's
stored constants, and names no `V`, no `interp` and no `EnvS`; its one
consequence here, `projFwd_renameOkT`, is the model-free `RenameOkT`
of `Verify/Denote/Rename.lean`.  The collapsed lane instantiates it at
`m.cval`, the graded lane (`Interp/ProjRenameP.lean`) at the
carrier's own valuation.

Statements verbatim from their old home; the namespace is unchanged.
-/

namespace ConLeche.Semantics
open ConLeche.Term ConLeche.Verify

/-- **The projection phase's fold invariant** ([set] transpose of
`ProjPhaseInv`): the parent type and the constructor still carry their
model values, and every installed projection function carries its
`_model.proj_j`'s.  These three conjuncts are `projFwd`'s three
cases. -/
def ProjPhaseInvS (T ctorName : Name) (nF : Nat) (env' : Env)
    (cval : TConstVal) : Prop :=
  (∀ ci, env'.find? T = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (T.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat, cval T ψ = cval (T.str "_model") ψ) ∧
  (∀ ci, env'.find? ctorName = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (ctorName.str "_model")
        = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        cval ctorName ψ = cval (ctorName.str "_model") ψ) ∧
  (∀ j, j < nF → ∀ ci, env'.find? (projFnName T j) = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (projModelName T j)
        = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ∀ ψ : Name → Nat,
        cval (projFnName T j) ψ = cval (projModelName T j) ψ)

/-- The projection renaming, pruned to the stored names, is sound at
the phase invariant.  Its three cases *are* the invariant's three
conjuncts. -/
theorem projFwd_renameOkT {T ctorName : Name} {nF : Nat} {env' : Env}
    {cval : TConstVal} (hinv : ProjPhaseInvS T ctorName nF env' cval) :
    RenameOkT cval env' (fun n => if (env'.find? n).isSome = true then
      projFwd T ctorName nF n else n) := by
  have hfound : ∀ n ci₂, env'.find? n = some ci₂ →
      (∃ ci', env'.find? (projFwd T ctorName nF n) = some ci' ∧
        ci'.toConstantVal.levelParams = ci₂.toConstantVal.levelParams) ∧
      (∀ ψ : Name → Nat,
        cval (projFwd T ctorName nF n) ψ = cval n ψ) := by
    intro n ci₂ hf₂
    unfold projFwd
    try dsimp only
    by_cases h1 : n = T
    · subst h1
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h1]
    by_cases h2 : n = ctorName
    · subst h2
      rw [if_pos rfl]
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ := hinv.2.1 ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
    rw [if_neg h2]
    cases hfind : (List.range nF).find?
      (fun j => n == projFnName T j) with
    | none => exact ⟨⟨ci₂, hf₂, rfl⟩, fun ψ => rfl⟩
    | some j =>
      have hjlt : j < nF :=
        List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hn : n = projFnName T j := by
        have hprop := List.find?_some hfind
        exact eq_of_beq (by simpa using hprop)
      subst hn
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hv₂⟩ :=
        hinv.2.2 j hjlt ci₂ hf₂
      exact ⟨⟨_, hfm₂, hlps₂⟩, fun ψ => (hv₂ ψ).symm⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n ci₂ hf₂
    dsimp only
    rw [if_pos (show (env'.find? n).isSome = true by rw [hf₂]; rfl)]
    exact (hfound n ci₂ hf₂).1
  · intro n hf₂
    dsimp only
    rw [if_neg (show ¬(env'.find? n).isSome = true by
      rw [hf₂]; exact fun hx => nomatch hx)]
    exact hf₂
  · intro n ψ
    dsimp only
    cases hf₂ : env'.find? n with
    | none =>
      rw [if_neg (show ¬(none : Option ConstantInfo).isSome = true
        from fun hx => nomatch hx)]
    | some ci₂ =>
      rw [if_pos (show (some ci₂ : Option ConstantInfo).isSome = true
        from rfl)]
      exact (hfound n ci₂ hf₂).2 ψ

end ConLeche.Semantics
