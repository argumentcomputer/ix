import IxCCGrounding.SelRetype
import IxCCGrounding.Laws

/-!
# The law recursors with parameters need (`IxCCCorrect.CanonLaw`)

W-c (F2 at a recursor with parameters, `List.rec`, `Option.rec`, …) needs, at the major premise,
that the constructor value's fields fit the constructor's type **at the recursor's parameter
sets**, which the value relation knows only at the constructor value's own parameter sets. The
grounding library already names the model property that closes the gap: `CtorCanon M`
(`IxCCGrounding/Laws.lean`, "constructor canonicity across parameters and levels, at families
that are not propositions"): a constructor image, built at any levels `ls'` and parameters `Ps'`,
that lies in the denotation of its inductive applied (at levels `ls`) to parameters denoting `Ps`,
**is** the image at `ls` and `Ps` of the same fields, and the fields fit the constructor's type
there.

`SameDenotation` quantifies over every model, so the hypothesis the W-c theorems take is that
**every** model of the environment satisfies it:

```lean
def ModelsCtorCanon.{w} (env : KEnv) : Prop :=
  ∀ (V : Type w) [SetTheory V] (M : Model V env), CtorCanon M
```

It is not provable from today's `Ix.Kernel.Model` laws (nothing there relates images at different
parameters), so it is a hypothesis, never an axiom. It becomes a theorem once the kernel adds the
law to `Model` and its main theorem shows the constructed model satisfies it
(`plans/GROUNDING.md`, section 14, for why it does). `ctorCanon_selRetype` moves it to the
retyped reading the root theorem works on, so the hypothesis is stated on the admitted
environment itself.
-/

set_option autoImplicit false

namespace IxCC.Correct

open Ix.Kernel
open IxCC.Grounding

universe w

/-- **Constructor canonicity in every model of `env`**, over every set theory at universe `w`: the
hypothesis W-c's theorems take (see the module note). -/
def ModelsCtorCanon.{u} (env : KEnv) : Prop :=
  ∀ (V : Type u) [Ix.Kernel.SetTheory V] (M : Model V env), CtorCanon M

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V]

/-- A constructor or an inductive of a retyping is the reading's (only definitions are retyped). -/
theorem selRetype1_eq_of_not_defn {env : KEnv} {ci ci' : ConstantInfo .anon}
    (h : SelRetype1 env ci ci') (hnd : ∀ cv v hint, ci' ≠ .defnInfo cv v hint) : ci' = ci := by
  rcases h with h | ⟨cv, v, hint, T', -, h2, -⟩
  · exact h
  · exact absurd h2 (hnd _ _ _)

/-- **Canonicity moves to the retyped reading**: a retyping keeps every constructor and inductive
and every denotation, so `CtorCanon` of a model of the reading is `CtorCanon` of the model of the
retyping with the same `cval`. -/
theorem ctorCanon_selRetype {env env' : KEnv} (h : SelRetype env env') {M : Model V env}
    {M' : Model V env'} (hc : M'.cval = M.cval) (hcc : CtorCanon M) : CtorCanon M' := by
  have hD := denotes_selRetype' (V := V) h M.cval
  have hF := fits_selRetype (V := V) h M.cval
  have hDL := denotesList_selRetype (V := V) h M.cval
  intro c cvC nP nF hfc D cvD caps s ls ls' φ ρ τ σ' dom R' Ps Ps' Fs K K' X hfD hs hl hl' hPl hPl'
    hFl hK hK' hfit hR' hdom hX hPs hmem
  rw [hc] at hK hK' hfit hX hPs ⊢
  rw [hD] at hK hK' hX
  rw [hF] at hfit ⊢
  rw [hDL] at hPs
  obtain ⟨ci, hci, h1⟩ := find?_back h hfc
  have e1 := selRetype1_eq_of_not_defn h1 (fun _ _ _ hh => by cases hh)
  subst e1
  obtain ⟨di, hdi, h2⟩ := find?_back h hfD
  have e2 := selRetype1_eq_of_not_defn h2 (fun _ _ _ hh => by cases hh)
  subst e2
  exact hcc c cvC nP nF hci D cvD caps s ls ls' φ ρ τ σ' dom R' Ps Ps' Fs K K' X hdi hs hl hl'
    hPl hPl' hFl hK hK' hfit hR' hdom hX hPs hmem

end Sem

end IxCC.Correct
