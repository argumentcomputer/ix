module

public import ConLeche.Model.AxiomBits
public import ConLeche.Verify.StdAxiomPin

public section

/-!
# The pinned axioms' `interp` memberships (task #161, ENDGAME C, task 1a)

`StdAxiomKey.lean`'s two forcing arguments, re-derived at the graded
currency.  The ENDGAME B seal wrote the route; this file executes it,
and one step of it needed content the seal did not predict.

## The unpredicted step, and the lemma that supplies it

The seal's route says: *instantiate `Iff.rec` at `ψ uN ≠ 0`, where
every bit is `1`, so the motive space is the graph regime and
`app_lamR_pos` computes*.  **The bits it names are the pin's, not the
stored constant's** — `matchesPin` compares through `erasePw`, so the
stored companions' binder data are exactly what the comparison
forgives, and `AxiomBitsP`'s bit lemmas are unavailable here: they read
`ConstantValR`'s recorded run, and the recorded run in scope belongs to
the *axiom being installed*, never to `Iff.rec`, which was stored many
declarations ago.

So the route as written does not close, and the missing step is not a
bit lemma (there is no run to read).  It is this:

> **`pi_sort_bit_ne_zero`** — a graded `∀`-node whose codomain is a
> *sort* and whose domain is *inhabited* has a nonzero bit.

`AnnotValid`'s `pi` third component is one-directional — `v = 0 → ∀ x
∈ A, B x ∈ˢ univZero` — which the ENDGAME A seal recorded as the reason
it cannot *pin* a bit.  It can still *refute* one: at a sort codomain
the consequent is `univ n ∈ˢ univZero`, and no universe is a truth
value (`univ_not_mem_univZero`, one line from `mem_univZero` +
`pt_not_mem_univZero`).  The domain's inhabitant is free at both
recursors — it is the very witness being eliminated.

That makes the memberships **bit-agnostic in the companions**: every
elimination of a stored family goes through `app_mem_piR` with its side
condition read off `type_wellDenotedV` (the seal's dissolved case-split,
confirmed), and the one place a *computation* is needed — the motive's
β — is licensed by `pi_sort_bit_ne_zero` rather than by a known bit.

## The second unpredicted step: the minor cannot be built positively

Removing the motive's bit is not enough.  v1's `iff_forces_eqS` builds
the recursor's minor premise *positively*: it applies the stored
`Iff.intro` to the arguments the recursor's own minor binder supplies.
Those two domains are binder data of **two different stored
constants** — `Iff.intro`'s implication binders and `Iff.rec`'s — and
`matchesPin` forgives both, so `piR e A (fun _ => B)` and
`piR d A (fun _ => B)` are not the same set unless `e` and `d` agree
in zero-ness, which nothing in the tree says.  A graph is not the
canonical proof; off a graph's domain the motive applies to `∅`; the
minor's fibre is then empty and the premise is *unsatisfiable*.  This
is not a gap in the proof, it is a gap in the invariant — the same
species as ENDGAME B's `rec_rules` wall.

It is routed around rather than closed, and the route is cheap:
`Classical.byContradiction` on `A = B` makes the minor's **binders**
vacuous.  The moment an implication and its converse are both in hand,
`eq_of_impls` gives `A = B` and contradicts the assumption — so the
minor is a `lamR`-tower over an unreachable body, and the stored
`Iff.intro` never appears in the argument at all.  Two consequences
worth recording:

* the level assignment stops being a choice.  The ENDGAME B seal
  requires `ψ uN ≠ 0` (all bits `1`) and pays a `univ_mono` residue for
  `eqv A B ∈ˢ univ (ψ uN)`.  Here the recursor is read at `ψ0 = fun _
  => 0`, `eqv_mem_univ` closes the fibre outright, and **`univ_mono` is
  not used**.  The graph regime comes from the sort codomain at *every*
  assignment;
* `Iff.intro`'s membership — v1's `iffIntroVal_app₄_memS` — has no
  P-tier counterpart and needs none.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The lever

Two lemmas.  The first is pure set theory and belongs to no tier; the
second is the graded model's reading of `AnnotValid`'s one-directional
`pi` obligation. -/

/-- **No universe is a truth value.**  `univZero`'s members are subsets
of `{pt}`, and `empty` is in every universe, so a universe inside
`univZero` would make `empty = pt` — and `empty` *is* a truth value,
while `pt` is not (`pt_not_mem_univZero`). -/
theorem univ_not_mem_univZero (n : Nat) : ¬ (univ n : V) ∈ˢ univZero := by
  intro h
  have hemp : (empty : V) ∈ˢ unitSet := mem_univZero.mp h _ (empty_mem_univ n)
  have he : (empty : V) = pt := mem_unitSet hemp
  refine ConLeche.Semantics.pt_not_mem_univZero (V := V) ?_
  rw [← he]
  exact univ_zero (V := V) ▸ empty_mem_univ 0

/-- **A graded `∀` over an inhabited domain, with a sort codomain, is
in the graph regime.**  The lever of this file (see the module
docstring): `AnnotValid`'s `pi` clause cannot *establish* a bit, but
at a sort codomain it *refutes* zero, and the refutation needs only an
inhabitant of the domain — which every elimination has in hand. -/
theorem pi_sort_bit_ne_zero {ρ : Nat → V} {u v n : Nat} {Aa : AnnotTerm}
    (hv : AnnotValid V ρ (.pi u v Aa (.sort n)))
    {x : V} (hx : x ∈ˢ interp V ρ Aa) : v ≠ 0 := by
  intro h0
  rw [AnnotValid_pi] at hv
  exact univ_not_mem_univZero (V := V) n (hv.2.2 h0 x hx)

/-- Elimination at a `pi` reading, with the side condition read off the
node's own validity — the ENDGAME B seal's dissolved case-split, as a
lemma.  **No knowledge of `v` is needed**: this is why the stored
companions' unpinned bits never have to be established. -/
theorem app_mem_pi_validV {ρ : Nat → V} {u v : Nat} {Aa Ba : AnnotTerm}
    {f a : V} (hf : f ∈ˢ interp V ρ (.pi u v Aa Ba))
    (ha : a ∈ˢ interp V ρ Aa)
    (hv : AnnotValid V ρ (.pi u v Aa Ba)) :
    SetTheory.app f a ∈ˢ interp V (cons a ρ) Ba := by
  rw [interp_pi] at hf
  rw [AnnotValid_pi] at hv
  exact app_mem_piR hf ha hv.2.2

/-! ## The stored `Iff` family's shapes

Every domain and body of the three pins is binder-free, so the double
erasure fixes the whole telescope and leaves exactly the binder names
and the binder metas free — the same mechanical inversion
`AxiomBitsP`'s `propext_shapeS` runs, at three longer shapes. -/

/-- The stored `Iff` former's shape. -/
theorem iff_shapeS {ty : Expr}
    (h : ty.erasePw
      = iffA.toConstantVal.type.erasePw) :
    ∃ m₁ m₂, ty = .forallE (.sort .zero)
      (.forallE (.sort .zero) (.sort .zero) m₂) m₁ := by
  simp only [iffA, ConstantInfo.toConstantVal, Expr.erasePw] at h
  obtain ⟨ty₁, b₁, m₁, rfl, hty₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS hty₁
  obtain ⟨ty₂, b₂, m₂, rfl, hty₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  obtain rfl := erasePwNames_sort_invS hty₂
  obtain rfl := erasePwNames_sort_invS hb₂
  exact ⟨m₁, m₂, rfl⟩

/-- The stored `Iff.intro`'s shape. -/
theorem iffIntro_shapeS {ty : Expr}
    (h : ty.erasePw
      = iffIntroA.toConstantVal.type.erasePw) :
    ∃ m₁ m₂ m₃ m₄ m₅ m₆,
      ty = .forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE (.forallE (.bvar 1) (.bvar 1) m₄)
            (.forallE (.forallE (.bvar 1) (.bvar 3) m₆)
              (.app (.app (.const iffName []) (.bvar 3)) (.bvar 2))
              m₅) m₃) m₂) m₁ := by
  simp only [iffIntroA, ConstantInfo.toConstantVal, Expr.erasePw] at h
  obtain ⟨t₁, b₁, m₁, rfl, ht₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS ht₁
  obtain ⟨t₂, b₂, m₂, rfl, ht₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  obtain rfl := erasePwNames_sort_invS ht₂
  obtain ⟨t₃, b₃, m₃, rfl, ht₃, hb₃⟩ := erasePwNames_forallE_invS hb₂
  obtain ⟨t₄, b₄, m₄, rfl, ht₄, hb₄⟩ := erasePwNames_forallE_invS ht₃
  obtain rfl := erasePwNames_bvar_invS ht₄
  obtain rfl := erasePwNames_bvar_invS hb₄
  obtain ⟨t₅, b₅, m₅, rfl, ht₅, hb₅⟩ := erasePwNames_forallE_invS hb₃
  obtain ⟨t₆, b₆, m₆, rfl, ht₆, hb₆⟩ := erasePwNames_forallE_invS ht₅
  obtain rfl := erasePwNames_bvar_invS ht₆
  obtain rfl := erasePwNames_bvar_invS hb₆
  obtain ⟨f, a, rfl, hf, ha⟩ := erasePwNames_app_invS hb₅
  obtain ⟨f', a', rfl, hf', ha'⟩ := erasePwNames_app_invS hf
  obtain rfl := erasePwNames_const_invS hf'
  obtain rfl := erasePwNames_bvar_invS ha'
  obtain rfl := erasePwNames_bvar_invS ha
  exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, rfl⟩

/-- The stored `Iff.rec`'s shape.  Five telescope binders and four
nested ones; the motive's codomain `Sort u` is what
`pi_sort_bit_ne_zero` later fires on. -/
theorem iffRec_shapeS {ty : Expr}
    (h : ty.erasePw
      = iffRecA.toConstantVal.type.erasePw) :
    ∃ m₁ m₂ m₃ m₄ m₅ mt mmp mr mmpr ma,
      ty = .forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.forallE
              (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
              (.sort (.param uN)) mt)
            (.forallE
              (.forallE (.forallE (.bvar 2) (.bvar 2) mr)
                (.forallE (.forallE (.bvar 2) (.bvar 4) ma)
                  (.app (.bvar 2)
                    (.app (.app (.app (.app (.const iffIntroName [])
                      (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0)))
                  mmpr) mmp)
              (.forallE
                (.app (.app (.const iffName []) (.bvar 3)) (.bvar 2))
                (.app (.bvar 2) (.bvar 0)) m₅) m₄) m₃) m₂) m₁ := by
  simp only [iffRecA, ConstantInfo.toConstantVal, Expr.erasePw] at h
  obtain ⟨t₁, b₁, m₁, rfl, ht₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS ht₁
  obtain ⟨t₂, b₂, m₂, rfl, ht₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  obtain rfl := erasePwNames_sort_invS ht₂
  obtain ⟨t₃, b₃, m₃, rfl, ht₃, hb₃⟩ := erasePwNames_forallE_invS hb₂
  -- the motive's type
  obtain ⟨tt, bt, mt, rfl, htt, hbt⟩ := erasePwNames_forallE_invS ht₃
  obtain ⟨f, a, rfl, hf, ha⟩ := erasePwNames_app_invS htt
  obtain ⟨f', a', rfl, hf', ha'⟩ := erasePwNames_app_invS hf
  obtain rfl := erasePwNames_const_invS hf'
  obtain rfl := erasePwNames_bvar_invS ha'
  obtain rfl := erasePwNames_bvar_invS ha
  obtain rfl := erasePwNames_sort_invS hbt
  -- the minor
  obtain ⟨t₄, b₄, m₄, rfl, ht₄, hb₄⟩ := erasePwNames_forallE_invS hb₃
  obtain ⟨t₅, b₅, m₅, rfl, ht₅, hb₅⟩ := erasePwNames_forallE_invS ht₄
  obtain ⟨tr, br, mr, rfl, htr, hbr⟩ := erasePwNames_forallE_invS ht₅
  obtain rfl := erasePwNames_bvar_invS htr
  obtain rfl := erasePwNames_bvar_invS hbr
  obtain ⟨ta, ba, ma, rfl, hta, hba⟩ := erasePwNames_forallE_invS hb₅
  obtain ⟨tt', bt', mt', rfl, htt', hbt'⟩ :=
    erasePwNames_forallE_invS hta
  obtain rfl := erasePwNames_bvar_invS htt'
  obtain rfl := erasePwNames_bvar_invS hbt'
  obtain ⟨g, c, rfl, hg, hc⟩ := erasePwNames_app_invS hba
  obtain rfl := erasePwNames_bvar_invS hg
  obtain ⟨g₁, c₁, rfl, hg₁, hc₁⟩ := erasePwNames_app_invS hc
  obtain ⟨g₂, c₂, rfl, hg₂, hc₂⟩ := erasePwNames_app_invS hg₁
  obtain ⟨g₃, c₃, rfl, hg₃, hc₃⟩ := erasePwNames_app_invS hg₂
  obtain ⟨g₄, c₄, rfl, hg₄, hc₄⟩ := erasePwNames_app_invS hg₃
  obtain rfl := erasePwNames_const_invS hg₄
  obtain rfl := erasePwNames_bvar_invS hc₄
  obtain rfl := erasePwNames_bvar_invS hc₃
  obtain rfl := erasePwNames_bvar_invS hc₂
  obtain rfl := erasePwNames_bvar_invS hc₁
  -- the major
  obtain ⟨tt'', bt'', mt'', rfl, htt'', hbt''⟩ :=
    erasePwNames_forallE_invS hb₄
  obtain ⟨p, q, rfl, hp, hq⟩ := erasePwNames_app_invS htt''
  obtain ⟨p', q', rfl, hp', hq'⟩ := erasePwNames_app_invS hp
  obtain rfl := erasePwNames_const_invS hp'
  obtain rfl := erasePwNames_bvar_invS hq'
  obtain rfl := erasePwNames_bvar_invS hq
  obtain ⟨r, s, rfl, hr, hs⟩ := erasePwNames_app_invS hbt''
  obtain rfl := erasePwNames_bvar_invS hr
  obtain rfl := erasePwNames_bvar_invS hs
  exact ⟨m₁, m₂, m₃, m₄, mt'', mt, m₅, mr, ma, mt', rfl⟩

/-! ## The stored `Iff` family's `interp` memberships

Each is `mem_type` at the stored constant, its reading computed off
the shape, and `app_mem_pi_validV` once per argument — the side
conditions read off `type_wellDenotedV`, never off a bit. -/

/-- The stored `Iff`, applied to two propositions, is a proposition. -/
theorem iffVal_app₂_memP (mp : EnvModelM V μ env)
    {cvI : ConstantVal} {caps : ConLeche.IndCaps}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (htyI : cvI.type.erasePw
      = iffA.toConstantVal.type.erasePw)
    (ψ : Name → Nat) (ρ : Nat → V) {A B : V}
    (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V)) :
    SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval iffName ψ)) A) B
      ∈ˢ (univ 0 : V) := by
  obtain ⟨m₁, m₂, hsh⟩ := iff_shapeS htyI
  have hden : denoteMeta mp.base2.acval env ψ 0
      (ConstantInfo.indInfo cvI caps).toConstantVal.type
      = some (.pi 0 (pwBit ψ m₁.pw) (.sort 0)
          (.pi 0 (pwBit ψ m₂.pw) (.sort 0) (.sort 0))) := by
    show denoteMeta mp.base2.acval env ψ 0 cvI.type = _
    rw [hsh]
    simp [denoteMeta_forallE, denoteMeta_sort, Expr.instantiate1, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfI) ψ _ hden ρ
  have hval := (mp.type_wellDenotedV _ (Env.find?_mem hfI) ψ _ hden ρ).2
  rw [Env.find?_name hfI] at hmem
  have h1 := app_mem_pi_validV hmem (by rw [interp_sort]; exact hA) hval
  rw [AnnotValid_pi] at hval
  have hval2 := hval.2.1 A (by rw [interp_sort]; exact hA)
  have h2 := app_mem_pi_validV h1 (by rw [interp_sort]; exact hB) hval2
  rw [interp_sort] at h2
  exact h2

/-- **Two mutually inverse implications identify their propositions.**
The regime bits play no part: `app_mem_piR`'s side condition at a
`Prop` codomain is `B ∈ˢ univZero`, which is the hypothesis itself. -/
theorem eq_of_impls {A B f g : V} (hA : A ∈ˢ (univ 0 : V))
    (hB : B ∈ˢ (univ 0 : V)) {d e : Nat}
    (hf : f ∈ˢ piR d A fun _ => B) (hg : g ∈ˢ piR e B fun _ => A) :
    A = B := by
  refine prop_ext hA hB (fun hptA => ?_) (fun hptB => ?_)
  · have h1 := app_mem_piR hf hptA
      (fun _ _ _ => univ_zero (V := V) ▸ hB)
    rwa [mem_univ_zero hB h1] at h1
  · have h1 := app_mem_piR hg hptB
      (fun _ _ _ => univ_zero (V := V) ▸ hA)
    rwa [mem_univ_zero hA h1] at h1

/-- **Interpreted `Iff` forces equality of truth values, at the graded
currency.**

Not a transcription of `iff_forces_eqS`, and the difference is the
finding this file records.  v1 builds the minor *positively*: it
applies the stored `Iff.intro` to the recursor's own minor arguments.
At `interp` that step does not exist — `Iff.intro`'s implication
binders and `Iff.rec`'s implication binders are binder data of **two
different stored constants**, agreeing only up to `erasePw`, so
`piR e A (fun _ => B)` and `piR d A (fun _ => B)` need not be the same
set, and a graph in one regime is not the canonical proof in the
other.  Nothing in the tree relates two stored constants' binder data.

The argument is restructured instead: `Classical.byContradiction` on
`A = B` makes the minor's *binders* vacuous — the moment both an
implication and its converse are in hand, `eq_of_impls` closes, so the
minor is `lamR`-of-`lamR` over an unreachable body and the stored
`Iff.intro` never appears at all.  The only computation needed is the
motive's β, licensed by `pi_sort_bit_ne_zero`.  The level assignment
is then free: this instantiates at `ψ0 uN = 0`, where `eqv A B ∈ˢ
univ 0` is `eqv_mem_univ` outright and the ENDGAME B seal's `univ_mono`
residue does not arise. -/
theorem iff_forces_eq (mp : EnvModelM V μ env)
    {cvI : ConstantVal} {caps : ConLeche.IndCaps} {cvIi cvIr : ConstantVal}
    {mI rP : Nat} {rules : List ConLeche.RecRule}
    (hfI : env.find? iffName = some (.indInfo cvI caps))
    (hlpI : cvI.levelParams = [])
    (hfIi : env.find? iffIntroName = some (.ctorInfo cvIi 2 2))
    (hlpIi : cvIi.levelParams = [])
    (hfIr : env.find? iffRecName = some (.recInfo cvIr mI rP rules))
    (htyIr : cvIr.type.erasePw
      = iffRecA.toConstantVal.type.erasePw)
    (ψ : Name → Nat) (ρ : Nat → V) {A B w : V}
    (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V))
    (hw : w ∈ˢ SetTheory.app (SetTheory.app
      (interp V ρ (mp.base2.acval iffName ψ)) A) B) :
    A = B := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨m₁, m₂, m₃, m₄, m₅, mt, mmp, mr, mmpr, ma, hsh⟩ :=
    iffRec_shapeS htyIr
  -- the parameterless family members do not read the assignment, so
  -- the recursor may be read at **any** level assignment
  have hIval : mp.base2.acval iffName (fun _ => 0)
      = mp.base2.acval iffName ψ :=
    mp.base2.acval_params _ _ hfI _ _ (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI
        from rfl, hlpI]
      intro p hp; cases hp)
  have hI : ∀ d, denoteMeta mp.base2.acval env (fun _ => 0) d
      (.const iffName []) = some (mp.base2.acval iffName (fun _ => 0)) :=
    fun d => denoteMeta_levelless_const hfI (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI
        from rfl, hlpI])
  have hIi : ∀ d, denoteMeta mp.base2.acval env (fun _ => 0) d
      (.const iffIntroName [])
        = some (mp.base2.acval iffIntroName (fun _ => 0)) :=
    fun d => denoteMeta_levelless_const hfIi (by
      rw [show (ConstantInfo.ctorInfo cvIi 2 2).toConstantVal = cvIi
        from rfl, hlpIi])
  -- the recursor's stored type, read at the zero assignment
  have hden : denoteMeta mp.base2.acval env (fun _ => 0) 0
      (ConstantInfo.recInfo cvIr mI rP rules).toConstantVal.type
      = some (.pi 0 (pwBit (fun _ => 0) m₁.pw) (.sort 0)
        (.pi 0 (pwBit (fun _ => 0) m₂.pw) (.sort 0)
          (.pi 0 (pwBit (fun _ => 0) m₃.pw)
            (.pi 0 (pwBit (fun _ => 0) mt.pw)
              (.app (.app (mp.base2.acval iffName (fun _ => 0))
                (.bvar 1)) (.bvar 0)) (.sort 0))
            (.pi 0 (pwBit (fun _ => 0) m₄.pw)
              (.pi 0 (pwBit (fun _ => 0) mmp.pw)
                (.pi 0 (pwBit (fun _ => 0) mr.pw) (.bvar 2) (.bvar 2))
                (.pi 0 (pwBit (fun _ => 0) mmpr.pw)
                  (.pi 0 (pwBit (fun _ => 0) ma.pw) (.bvar 2) (.bvar 4))
                  (.app (.bvar 2)
                    (.app (.app (.app (.app
                      (mp.base2.acval iffIntroName (fun _ => 0))
                      (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0)))))
              (.pi 0 (pwBit (fun _ => 0) m₅.pw)
                (.app (.app (mp.base2.acval iffName (fun _ => 0))
                  (.bvar 3)) (.bvar 2))
                (.app (.bvar 2) (.bvar 0))))))) := by
    show denoteMeta mp.base2.acval env (fun _ => 0) 0 cvIr.type = _
    rw [hsh]
    simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
      Expr.instantiate1, hI, hIi, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfIr) _ _ hden ρ
  have hval := (mp.type_wellDenotedV _ (Env.find?_mem hfIr) _ _ hden ρ).2
  rw [Env.find?_name hfIr] at hmem
  rw [hIval] at hmem hval
  -- the family leaf's interpretation does not read the environment
  have hIc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval iffName ψ)
        = interp V ρ (mp.base2.acval iffName ψ) :=
    fun ρ' => acval_interp_closedC mp.base2 _ ψ ρ' ρ
  -- ARG 1 and 2: the two propositions
  have hAd : A ∈ˢ interp V ρ (AnnotTerm.sort 0) := by
    rw [interp_sort]; exact hA
  have h1 := app_mem_pi_validV hmem hAd hval
  rw [AnnotValid_pi] at hval
  have hval1 := hval.2.1 A hAd
  have hBd : B ∈ˢ interp V (cons A ρ) (AnnotTerm.sort 0) := by
    rw [interp_sort]; exact hB
  have h2 := app_mem_pi_validV h1 hBd hval1
  rw [AnnotValid_pi] at hval1
  have hval2 := hval1.2.1 B hBd
  -- ARG 3: the constantly-`eqv A B` motive.  Its space is the graph
  -- regime by `pi_sort_bit_ne_zero`, with the major premise `w` as the
  -- domain's inhabitant — **no bit of the stored recursor is known**
  have hval2d := hval2
  rw [AnnotValid_pi] at hval2d
  have hwd : w ∈ˢ interp V (cons B (cons A ρ))
      (.app (.app (mp.base2.acval iffName ψ) (.bvar 1)) (.bvar 0)) := by
    simp only [interp_app, interp_bvar, cons_zero, cons_succ, hIc]
    exact hw
  have hc : pwBit (fun _ => 0) mt.pw ≠ 0 :=
    pi_sort_bit_ne_zero hval2d.1 hwd
  obtain ⟨M, hME⟩ : ∃ M : V, M = lamR (pwBit (fun _ => 0) mt.pw)
      (SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval iffName ψ)) A) B)
      (fun _ => eqv A B) := ⟨_, rfl⟩
  have hMd : M ∈ˢ interp V (cons B (cons A ρ))
      (.pi 0 (pwBit (fun _ => 0) mt.pw)
        (.app (.app (mp.base2.acval iffName ψ) (.bvar 1)) (.bvar 0))
        (.sort 0)) := by
    rw [hME, interp_pi]
    simp only [interp_app, interp_bvar, cons_zero, cons_succ,
      interp_sort, hIc]
    exact lamR_mem fun _ _ => eqv_mem_univ A B
  have h3 := app_mem_pi_validV h2 hMd hval2
  have hval3 := hval2d.2.1 M hMd
  -- ARG 4: the minor.  **Vacuous**: an implication and its converse in
  -- hand contradict `hne`, so the stored `Iff.intro` never appears
  have hval3d := hval3
  rw [AnnotValid_pi] at hval3d
  obtain ⟨Min, hMinE⟩ : ∃ Min : V, Min = lamR (pwBit (fun _ => 0) mmp.pw)
      (piR (pwBit (fun _ => 0) mr.pw) A fun _ => B)
      (fun _ => lamR (pwBit (fun _ => 0) mmpr.pw)
        (piR (pwBit (fun _ => 0) ma.pw) B fun _ => A) fun _ => pt) :=
    ⟨_, rfl⟩
  have hMind : Min ∈ˢ interp V (cons M (cons B (cons A ρ)))
      (.pi 0 (pwBit (fun _ => 0) mmp.pw)
        (.pi 0 (pwBit (fun _ => 0) mr.pw) (.bvar 2) (.bvar 2))
        (.pi 0 (pwBit (fun _ => 0) mmpr.pw)
          (.pi 0 (pwBit (fun _ => 0) ma.pw) (.bvar 2) (.bvar 4))
          (.app (.bvar 2)
            (.app (.app (.app (.app
              (mp.base2.acval iffIntroName (fun _ => 0))
              (.bvar 4)) (.bvar 3)) (.bvar 1)) (.bvar 0))))) := by
    rw [hMinE]
    simp only [interp_pi, interp_bvar, cons_zero, cons_succ]
    refine lamR_mem fun x hx => ?_
    exact lamR_mem fun y hy => absurd (eq_of_impls hA hB hx hy) hne
  have h4 := app_mem_pi_validV h3 hMind hval3
  have hval4 := hval3d.2.1 Min hMind
  -- ARG 5: the major, and the motive's β
  have hwd' : w ∈ˢ interp V (cons Min (cons M (cons B (cons A ρ))))
      (.app (.app (mp.base2.acval iffName ψ) (.bvar 3)) (.bvar 2)) := by
    simp only [interp_app, interp_bvar, cons_zero, cons_succ, hIc]
    exact hw
  have h5 := app_mem_pi_validV h4 hwd' hval4
  simp only [interp_app, interp_bvar, cons_zero, cons_succ] at h5
  rw [hME, app_lamR_pos hc hw] at h5
  exact hne (mem_eqv h5)

/-! ## `propext`'s membership

The leaf is the layer's own `propext` constant, whose `bval` is `pt`,
and `propext_bits` makes every binder of the stored type carry bit
`0` — so all three products are truth values and `pt_mem_piR_zero_of`
descends through them.  The innermost fibre is the `Eq`-spine, whose
value is `eq_law`'s (the field, at the pin's own level instantiation
`u ↦ 1`), and `iff_forces_eq` supplies the equation. -/

/-- **`propext` inhabits its stored type's reading.** -/
theorem propext_mem (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {cvA : ConstantVal} (hok : ConLeche.stdAxiomOk env cvA = true)
    (hn : cvA.name = propextName) {F d : Nat} {stype : Expr}
    (hrun : ConLeche.inferTypeCore μ env F d cvA.type = .ok stype)
    (ψ : Name → Nat) (ta : AnnotTerm)
    (hta : denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta)
    (ρ : Nat → V) :
    interp V ρ (.const .propext []) ∈ˢ interp V ρ ta := by
  obtain ⟨hEq, ⟨cvI, caps, hfI, hlpI, htyI⟩, ⟨cvIi, hfIi, hlpIi, htyIi⟩,
    ⟨cvIr, mI, rP, rules, hfIr, hlpIr, htyIr⟩, hApin⟩ :=
    iff_shapes hok hn
  have hApinT : cvA.type.erasePw
      = propextA.type.erasePw := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      beq_iff_eq] at hApin
    exact hApin.2
  obtain ⟨m₁, m₂, m₃, hsh⟩ := propext_shapeS hApinT
  rw [hsh] at hrun hta
  obtain ⟨hb₁, hb₂, hb₃⟩ := propext_bits hμ hEq hrun ψ
  -- the `Eq` former's one level parameter is pinned to `1`
  have heqψ : Level.substFn ψ eqA.toConstantVal.levelParams
      [Level.zero.succ] uN = 1 := rfl
  have hI : ∀ e, denoteMeta mp.base2.acval env ψ e (.const iffName [])
      = some (mp.base2.acval iffName ψ) :=
    fun e => denoteMeta_levelless_const hfI (by
      rw [show (ConstantInfo.indInfo cvI caps).toConstantVal = cvI
        from rfl, hlpI])
  have hQ : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const eqName [Level.zero.succ])
      = some (mp.base2.acval eqName (Level.substFn ψ
          eqA.toConstantVal.levelParams [Level.zero.succ])) :=
    fun e => denoteMeta_const hEq rfl
  -- the stored type's reading, at the bits the run fixes
  have hden : denoteMeta mp.base2.acval env ψ 0
      (.forallE (.sort .zero)
        (.forallE (.sort .zero)
          (.forallE
            (.app (.app (.const iffName []) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (.const eqName [.succ .zero])
                (.sort .zero)) (.bvar 2)) (.bvar 1)) m₃) m₂) m₁)
      = some (.pi 0 0 (.sort 0) (.pi 0 0 (.sort 0)
          (.pi 0 0
            (.app (.app (mp.base2.acval iffName ψ) (.bvar 1)) (.bvar 0))
            (.app (.app (.app (mp.base2.acval eqName
                (Level.substFn ψ eqA.toConstantVal.levelParams
                  [Level.zero.succ])) (.sort 0)) (.bvar 2))
              (.bvar 1))))) := by
    simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
      Expr.instantiate1, hI, hQ, Level.eval, hb₁, hb₂, hb₃]
  obtain rfl : ta = _ := Option.some.inj (hta.symm.trans hden)
  -- the leaves' interpretations do not read the environment
  have hIc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval iffName ψ)
        = interp V ρ (mp.base2.acval iffName ψ) :=
    fun ρ' => acval_interp_closedC mp.base2 _ ψ ρ' ρ
  -- three `Prop`-level products, all `pt`-inhabited
  show (pt : V) ∈ˢ _
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ, hIc]
  refine pt_mem_piR_zero_of fun A hA => ?_
  refine pt_mem_piR_zero_of fun B hB => ?_
  refine pt_mem_piR_zero_of fun w hw => ?_
  have hAB : A = B :=
    iff_forces_eq mp hfI hlpI hfIi hlpIi hfIr htyIr ψ
      (cons w (cons B (cons A ρ))) hA hB (by
        simp only [hIc]; exact hw)
  rw [(mp.eq_law hEq _).1 (cons w (cons B (cons A ρ)))
    (univ 0) A B (by rw [heqψ]; exact univ_mem_univ 0) hA hB]
  exact hAB ▸ pt_mem_eqv_self A

/-! ## The stored `Nonempty` family

`Classical.choice`'s companions.  The regime clash that forced
`propext`'s restructuring **does not arise here**: `Nonempty.rec`'s
minor binds a plain element of `α`, not a function, so there is no
second `piR` whose bit would have to agree with `Nonempty.intro`'s.
The one bit still out of reach — the motive space's — is again removed
by `pi_sort_bit_ne_zero`, this time at the codomain `Prop`, where the
refuted consequent is `univZero ∈ˢ univZero`. -/

/-- The stored `Nonempty` former's shape. -/
theorem nonempty_shapeS {ty : Expr}
    (h : ty.erasePw
      = nonemptyA.toConstantVal.type.erasePw) :
    ∃ m₁, ty = .forallE (.sort (.param uN)) (.sort .zero) m₁ := by
  simp only [nonemptyA, ConstantInfo.toConstantVal, Expr.erasePw] at h
  obtain ⟨t₁, b₁, m₁, rfl, ht₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS ht₁
  obtain rfl := erasePwNames_sort_invS hb₁
  exact ⟨m₁, rfl⟩

/-- The stored `Nonempty.intro`'s shape. -/
theorem nonemptyIntro_shapeS {ty : Expr}
    (h : ty.erasePw
      = nonemptyIntroA.toConstantVal.type.erasePw) :
    ∃ m₁ m₂, ty = .forallE (.sort (.param uN))
      (.forallE (.bvar 0)
        (.app (.const nonemptyName [.param uN]) (.bvar 1)) m₂) m₁ := by
  simp only [nonemptyIntroA, ConstantInfo.toConstantVal, Expr.erasePw] at h
  obtain ⟨t₁, b₁, m₁, rfl, ht₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS ht₁
  obtain ⟨t₂, b₂, m₂, rfl, ht₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  obtain rfl := erasePwNames_bvar_invS ht₂
  obtain ⟨f, a, rfl, hf, ha⟩ := erasePwNames_app_invS hb₂
  obtain rfl := erasePwNames_const_invS hf
  obtain rfl := erasePwNames_bvar_invS ha
  exact ⟨m₁, m₂, rfl⟩

/-- The stored `Nonempty.rec`'s shape. -/
theorem nonemptyRec_shapeS {ty : Expr}
    (h : ty.erasePw
      = nonemptyRecA.toConstantVal.type.erasePw) :
    ∃ m₁ m₂ m₃ m₄ mt mv,
      ty = .forallE (.sort (.param uN))
        (.forallE
          (.forallE
            (.app (.const nonemptyName [.param uN]) (.bvar 0))
            (.sort .zero) mt)
          (.forallE
            (.forallE (.bvar 1)
              (.app (.bvar 1)
                (.app (.app (.const nonemptyIntroName [.param uN])
                  (.bvar 2)) (.bvar 0))) mv)
            (.forallE
              (.app (.const nonemptyName [.param uN]) (.bvar 2))
              (.app (.bvar 2) (.bvar 0)) m₄) m₃) m₂) m₁ := by
  simp only [nonemptyRecA, ConstantInfo.toConstantVal, Expr.erasePw] at h
  obtain ⟨t₁, b₁, m₁, rfl, ht₁, hb₁⟩ := erasePwNames_forallE_invS h
  obtain rfl := erasePwNames_sort_invS ht₁
  obtain ⟨t₂, b₂, m₂, rfl, ht₂, hb₂⟩ := erasePwNames_forallE_invS hb₁
  -- the motive's type
  obtain ⟨tt, bt, mt, rfl, htt, hbt⟩ := erasePwNames_forallE_invS ht₂
  obtain ⟨f, a, rfl, hf, ha⟩ := erasePwNames_app_invS htt
  obtain rfl := erasePwNames_const_invS hf
  obtain rfl := erasePwNames_bvar_invS ha
  obtain rfl := erasePwNames_sort_invS hbt
  -- the minor
  obtain ⟨t₃, b₃, m₃, rfl, ht₃, hb₃⟩ := erasePwNames_forallE_invS hb₂
  obtain ⟨tv, bv, mv, rfl, htv, hbv⟩ := erasePwNames_forallE_invS ht₃
  obtain rfl := erasePwNames_bvar_invS htv
  obtain ⟨g, c, rfl, hg, hc⟩ := erasePwNames_app_invS hbv
  obtain rfl := erasePwNames_bvar_invS hg
  obtain ⟨g₁, c₁, rfl, hg₁, hc₁⟩ := erasePwNames_app_invS hc
  obtain ⟨g₂, c₂, rfl, hg₂, hc₂⟩ := erasePwNames_app_invS hg₁
  obtain rfl := erasePwNames_const_invS hg₂
  obtain rfl := erasePwNames_bvar_invS hc₂
  obtain rfl := erasePwNames_bvar_invS hc₁
  -- the major
  obtain ⟨tm, bm, m₄, rfl, htm, hbm⟩ := erasePwNames_forallE_invS hb₃
  obtain ⟨p, q, rfl, hp, hq⟩ := erasePwNames_app_invS htm
  obtain rfl := erasePwNames_const_invS hp
  obtain rfl := erasePwNames_bvar_invS hq
  obtain ⟨r, s, rfl, hr, hs⟩ := erasePwNames_app_invS hbm
  obtain rfl := erasePwNames_bvar_invS hr
  obtain rfl := erasePwNames_bvar_invS hs
  exact ⟨m₁, m₂, m₃, m₄, mt, mv, rfl⟩

/-- A member of the `Nonempty` family, referenced at its own level
parameter, reads to its leaf at the plain assignment. -/
theorem denoteMeta_selfParam_constS {acval : Name → (Name → Nat) → AnnotTerm}
    {ψ : Name → Nat} {d : Nat} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlp : ci.toConstantVal.levelParams = [uN]) :
    denoteMeta acval env ψ d (.const n [.param uN]) = some (acval n ψ) := by
  have h : denoteMeta acval env ψ d (.const n [.param uN])
      = some (acval n (Level.substFn ψ
          ci.toConstantVal.levelParams [Level.param uN])) :=
    denoteMeta_const hf (by rw [hlp]; rfl)
  rwa [hlp, show Level.substFn ψ [uN] [Level.param uN] = ψ from
    funext fun _ => Level.substFn_map_param] at h

/-- The interpreted `Nonempty A` is a truth value. -/
theorem nonemptyVal_app_mem (mp : EnvModelM V μ env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (htyN : cvN.type.erasePw
      = nonemptyA.toConstantVal.type.erasePw)
    (ψ : Name → Nat) (ρ : Nat → V) {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A
      ∈ˢ (univ 0 : V) := by
  obtain ⟨m₁, hsh⟩ := nonempty_shapeS htyN
  have hden : denoteMeta mp.base2.acval env ψ 0
      (ConstantInfo.indInfo cvN capsN).toConstantVal.type
      = some (.pi 0 (pwBit ψ m₁.pw) (.sort (ψ uN)) (.sort 0)) := by
    show denoteMeta mp.base2.acval env ψ 0 cvN.type = _
    rw [hsh]
    simp [denoteMeta_forallE, denoteMeta_sort, Expr.instantiate1, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfN) ψ _ hden ρ
  have hval := (mp.type_wellDenotedV _ (Env.find?_mem hfN) ψ _ hden ρ).2
  rw [Env.find?_name hfN] at hmem
  have h1 := app_mem_pi_validV hmem (by rw [interp_sort]; exact hA) hval
  rwa [interp_sort] at h1

/-- The interpreted `Nonempty.intro A a` inhabits `Nonempty A`. -/
theorem nonemptyIntroVal_app₂_memP (mp : EnvModelM V μ env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps} {cvNi : ConstantVal}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (htyNi : cvNi.type.erasePw
      = nonemptyIntroA.toConstantVal.type.erasePw)
    (ψ : Name → Nat) (ρ : Nat → V) {A a : V} (hA : A ∈ˢ univ (ψ uN))
    (ha : a ∈ˢ A) :
    SetTheory.app (SetTheory.app
        (interp V ρ (mp.base2.acval nonemptyIntroName ψ)) A) a
      ∈ˢ SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A := by
  obtain ⟨m₁, m₂, hsh⟩ := nonemptyIntro_shapeS htyNi
  have hN : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const nonemptyName [.param uN])
      = some (mp.base2.acval nonemptyName ψ) :=
    fun e => denoteMeta_selfParam_constS hfN (by
      show cvN.levelParams = [uN]; rw [hlpN]; rfl)
  have hden : denoteMeta mp.base2.acval env ψ 0
      (ConstantInfo.ctorInfo cvNi 1 1).toConstantVal.type
      = some (.pi 0 (pwBit ψ m₁.pw) (.sort (ψ uN))
          (.pi 0 (pwBit ψ m₂.pw) (.bvar 0)
            (.app (mp.base2.acval nonemptyName ψ) (.bvar 1)))) := by
    show denoteMeta mp.base2.acval env ψ 0 cvNi.type = _
    rw [hsh]
    simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
      Expr.instantiate1, hN, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfNi) ψ _ hden ρ
  have hval := (mp.type_wellDenotedV _ (Env.find?_mem hfNi) ψ _ hden ρ).2
  rw [Env.find?_name hfNi] at hmem
  have hNc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval nonemptyName ψ)
        = interp V ρ (mp.base2.acval nonemptyName ψ) :=
    fun ρ' => acval_interp_closedC mp.base2 _ ψ ρ' ρ
  have hAd : A ∈ˢ interp V ρ (AnnotTerm.sort (ψ uN)) := by
    rw [interp_sort]; exact hA
  have h1 := app_mem_pi_validV hmem hAd hval
  have hvald := hval
  rw [AnnotValid_pi] at hvald
  have hval1 := hvald.2.1 A hAd
  have had : a ∈ˢ interp V (cons A ρ) (AnnotTerm.bvar 0) := ha
  have h2 := app_mem_pi_validV h1 had hval1
  simpa only [interp_app, interp_bvar, cons_zero, cons_succ, hNc]
    using h2

/-- **A witness of the interpreted `Nonempty A` forces `A`
inhabited.**  The constantly-`∅` motive, as in v1 — and here the minor
really *is* vacuous by the ambient contradiction hypothesis rather than
by restructuring, because `Nonempty.rec`'s minor binds a plain element
of `α`.  The motive space's regime is `pi_sort_bit_ne_zero`'s, at the
codomain `Prop`. -/
theorem nonemptyVal_forces (mp : EnvModelM V μ env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps}
    {cvNi cvNr : ConstantVal} {mI rP : Nat}
    {rulesN : List ConLeche.RecRule}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams
      = nonemptyIntroA.toConstantVal.levelParams)
    (hfNr : env.find? nonemptyRecName
      = some (.recInfo cvNr mI rP rulesN))
    (htyNr : cvNr.type.erasePw
      = nonemptyRecA.toConstantVal.type.erasePw)
    (ψ : Name → Nat) (ρ : Nat → V) {A h : V} (hA : A ∈ˢ univ (ψ uN))
    (hh : h ∈ˢ SetTheory.app
      (interp V ρ (mp.base2.acval nonemptyName ψ)) A) :
    ∃ x, x ∈ˢ A := by
  refine Classical.byContradiction fun hno => ?_
  obtain ⟨m₁, m₂, m₃, m₄, mt, mv, hsh⟩ :=
    nonemptyRec_shapeS htyNr
  have hN : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const nonemptyName [.param uN])
      = some (mp.base2.acval nonemptyName ψ) :=
    fun e => denoteMeta_selfParam_constS hfN (by
      show cvN.levelParams = [uN]; rw [hlpN]; rfl)
  have hNi : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const nonemptyIntroName [.param uN])
      = some (mp.base2.acval nonemptyIntroName ψ) :=
    fun e => denoteMeta_selfParam_constS hfNi (by
      show cvNi.levelParams = [uN]; rw [hlpNi]; rfl)
  have hden : denoteMeta mp.base2.acval env ψ 0
      (ConstantInfo.recInfo cvNr mI rP rulesN).toConstantVal.type
      = some (.pi 0 (pwBit ψ m₁.pw) (.sort (ψ uN))
        (.pi 0 (pwBit ψ m₂.pw)
          (.pi 0 (pwBit ψ mt.pw)
            (.app (mp.base2.acval nonemptyName ψ) (.bvar 0)) (.sort 0))
          (.pi 0 (pwBit ψ m₃.pw)
            (.pi 0 (pwBit ψ mv.pw) (.bvar 1)
              (.app (.bvar 1)
                (.app (.app (mp.base2.acval nonemptyIntroName ψ)
                  (.bvar 2)) (.bvar 0))))
            (.pi 0 (pwBit ψ m₄.pw)
              (.app (mp.base2.acval nonemptyName ψ) (.bvar 2))
              (.app (.bvar 2) (.bvar 0)))))) := by
    show denoteMeta mp.base2.acval env ψ 0 cvNr.type = _
    rw [hsh]
    simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
      Expr.instantiate1, hN, hNi, Level.eval]
  have hmem := mp.mem_type _ (Env.find?_mem hfNr) ψ _ hden ρ
  have hval := (mp.type_wellDenotedV _ (Env.find?_mem hfNr) ψ _ hden ρ).2
  rw [Env.find?_name hfNr] at hmem
  have hNc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval nonemptyName ψ)
        = interp V ρ (mp.base2.acval nonemptyName ψ) :=
    fun ρ' => acval_interp_closedC mp.base2 _ ψ ρ' ρ
  -- ARG 1: the type
  have hAd : A ∈ˢ interp V ρ (AnnotTerm.sort (ψ uN)) := by
    rw [interp_sort]; exact hA
  have h1 := app_mem_pi_validV hmem hAd hval
  have hvald := hval
  rw [AnnotValid_pi] at hvald
  have hval1 := hvald.2.1 A hAd
  -- ARG 2: the constantly-`∅` motive
  have hval1d := hval1
  rw [AnnotValid_pi] at hval1d
  have hhd : h ∈ˢ interp V (cons A ρ)
      (.app (mp.base2.acval nonemptyName ψ) (.bvar 0)) := by
    simp only [interp_app, interp_bvar, cons_zero, hNc]; exact hh
  have hdt : pwBit ψ mt.pw ≠ 0 := pi_sort_bit_ne_zero hval1d.1 hhd
  obtain ⟨M, hME⟩ : ∃ M : V, M = lamR (pwBit ψ mt.pw)
      (SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A)
      (fun _ => (empty : V)) := ⟨_, rfl⟩
  have hMd : M ∈ˢ interp V (cons A ρ)
      (.pi 0 (pwBit ψ mt.pw)
        (.app (mp.base2.acval nonemptyName ψ) (.bvar 0)) (.sort 0)) := by
    rw [hME, interp_pi]
    simp only [interp_app, interp_bvar, cons_zero, interp_sort, hNc]
    exact lamR_mem fun _ _ => empty_mem_univ 0
  have h2 := app_mem_pi_validV h1 hMd hval1
  have hval2 := hval1d.2.1 M hMd
  -- ARG 3: the minor, vacuous over an empty `A`
  have hval2d := hval2
  rw [AnnotValid_pi] at hval2d
  obtain ⟨Min, hMinE⟩ : ∃ Min : V,
      Min = lamR (pwBit ψ mv.pw) A (fun _ => (empty : V)) := ⟨_, rfl⟩
  have hMind : Min ∈ˢ interp V (cons M (cons A ρ))
      (.pi 0 (pwBit ψ mv.pw) (.bvar 1)
        (.app (.bvar 1)
          (.app (.app (mp.base2.acval nonemptyIntroName ψ)
            (.bvar 2)) (.bvar 0)))) := by
    rw [hMinE]
    simp only [interp_pi, interp_bvar, cons_zero, cons_succ]
    exact lamR_mem fun v hv => absurd ⟨v, hv⟩ hno
  have h3 := app_mem_pi_validV h2 hMind hval2
  have hval3 := hval2d.2.1 Min hMind
  -- ARG 4: the major, and the motive's β
  have hhd' : h ∈ˢ interp V (cons Min (cons M (cons A ρ)))
      (.app (mp.base2.acval nonemptyName ψ) (.bvar 2)) := by
    simp only [interp_app, interp_bvar, cons_zero, cons_succ, hNc]
    exact hh
  have h4 := app_mem_pi_validV h3 hhd' hval3
  simp only [interp_app, interp_bvar, cons_zero, cons_succ] at h4
  rw [hME, app_lamR_pos hdt hh] at h4
  exact not_mem_empty _ h4

/-- **The two domains agree.**  The layer's `¬¬A` and the checker's
stored `Nonempty A` are propositions with the same inhabitation, hence
the same set. -/
theorem dneg_eq_nonempty (mp : EnvModelM V μ env)
    {cvN : ConstantVal} {capsN : ConLeche.IndCaps}
    {cvNi cvNr : ConstantVal} {mI rP : Nat}
    {rulesN : List ConLeche.RecRule}
    (hfN : env.find? nonemptyName = some (.indInfo cvN capsN))
    (hlpN : cvN.levelParams = nonemptyA.toConstantVal.levelParams)
    (htyN : cvN.type.erasePw
      = nonemptyA.toConstantVal.type.erasePw)
    (hfNi : env.find? nonemptyIntroName = some (.ctorInfo cvNi 1 1))
    (hlpNi : cvNi.levelParams
      = nonemptyIntroA.toConstantVal.levelParams)
    (htyNi : cvNi.type.erasePw
      = nonemptyIntroA.toConstantVal.type.erasePw)
    (hfNr : env.find? nonemptyRecName
      = some (.recInfo cvNr mI rP rulesN))
    (htyNr : cvNr.type.erasePw
      = nonemptyRecA.toConstantVal.type.erasePw)
    (ψ : Name → Nat) (ρ : Nat → V) {A : V} (hA : A ∈ˢ univ (ψ uN)) :
    dnegSpace V A
      = SetTheory.app (interp V ρ (mp.base2.acval nonemptyName ψ)) A := by
  have hNE := nonemptyVal_app_mem mp hfN htyN ψ ρ hA
  have hdn : dnegSpace V A ∈ˢ (univ 0 : V) := by
    rw [univ_zero, dnegSpace]; exact piR_zero_mem_univZero
  refine prop_ext hdn hNE (fun hpt => ?_) (fun hpt => ?_)
  · obtain ⟨x, hx⟩ := exists_mem_of_dneg V hpt
    have hi := nonemptyIntroVal_app₂_memP mp hfN hlpN hfNi htyNi ψ ρ hA hx
    rwa [mem_univ_zero hNE hi] at hi
  · obtain ⟨x, hx⟩ := nonemptyVal_forces mp hfN hlpN hfNi hlpNi hfNr
      htyNr ψ ρ hA hpt
    rw [dnegSpace]
    exact pt_mem_piR_zero fun g hg =>
      absurd (app_mem_piR hg hx (fun _ _ _ =>
        univ_zero (V := V) ▸ empty_mem_univ 0)) (not_mem_empty _)

/-- **`Classical.choice` inhabits its stored type's reading.**  The
leaf is the layer's own `choice` constant, and `choice_bits` makes
both binders of the stored type carry the pin's own datum — so the
witness's two `lamR`s and the reading's two `piR`s agree on zero-ness
and `lamR_mem_zero_agree` crosses each.  `dneg_eq_nonempty` identifies
the witness's double-negation domain with the checker's stored
`Nonempty`. -/
theorem choice_mem (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {cvA : ConstantVal} (hok : ConLeche.stdAxiomOk env cvA = true)
    (hn : cvA.name = choiceName) {F d : Nat} {stype : Expr}
    (hrun : ConLeche.inferTypeCore μ env F d cvA.type = .ok stype)
    (ψ : Name → Nat) (ta : AnnotTerm)
    (hta : denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta)
    (ρ : Nat → V) :
    interp V ρ (.const .choice [ψ uN]) ∈ˢ interp V ρ ta := by
  obtain ⟨⟨cvN, capsN, hfN, hlpN, htyN⟩, ⟨cvNi, hfNi, hlpNi, htyNi⟩,
    ⟨cvNr, mI, rP, rulesN, hfNr, hlpNr, htyNr⟩, hApin⟩ :=
    nonempty_shapes hok hn
  have hApinT : cvA.type.erasePw
      = choiceA.type.erasePw := by
    simp only [ConstantVal.matchesPin, Bool.and_eq_true,
      beq_iff_eq] at hApin
    exact hApin.2
  obtain ⟨m₁, m₂, hsh⟩ := choice_shapeS hApinT
  rw [hsh] at hrun hta
  obtain ⟨hb₁, hb₂⟩ := choice_bits hμ hrun ψ
  have hN : ∀ e, denoteMeta mp.base2.acval env ψ e
      (.const nonemptyName [.param uN])
      = some (mp.base2.acval nonemptyName ψ) :=
    fun e => denoteMeta_selfParam_constS hfN (by
      show cvN.levelParams = [uN]; rw [hlpN]; rfl)
  have hden : denoteMeta mp.base2.acval env ψ 0
      (.forallE (.sort (.param uN))
        (.forallE
          (.app (.const nonemptyName [.param uN]) (.bvar 0))
          (.bvar 1) m₂) m₁)
      = some (.pi 0 (pwBit ψ m₁.pw) (.sort (ψ uN))
          (.pi 0 (pwBit ψ m₂.pw)
            (.app (mp.base2.acval nonemptyName ψ) (.bvar 0))
            (.bvar 1))) := by
    simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_app, denoteMeta_fvar,
      Expr.instantiate1, hN, Level.eval]
  obtain rfl : ta = _ := Option.some.inj (hta.symm.trans hden)
  have hNc : ∀ ρ' : Nat → V,
      interp V ρ' (mp.base2.acval nonemptyName ψ)
        = interp V ρ (mp.base2.acval nonemptyName ψ) :=
    fun ρ' => acval_interp_closedC mp.base2 _ ψ ρ' ρ
  show choiceV V (ψ uN) ∈ˢ _
  simp only [interp_pi, interp_sort, interp_app, interp_bvar,
    cons_zero, cons_succ, hNc]
  rw [choiceV]
  refine lamR_mem_zero_agree hb₁.symm fun A hA => ?_
  rw [dneg_eq_nonempty mp hfN hlpN htyN hfNi hlpNi htyNi hfNr htyNr
    ψ ρ hA]
  refine lamR_mem_zero_agree hb₂.symm fun hx hhx => ?_
  obtain ⟨x, hxA⟩ := nonemptyVal_forces mp hfN hlpN hfNi hlpNi hfNr
    htyNr ψ ρ hA hhx
  exact schoice_mem hxA
