module

public import ConLeche.Model.BasisCons
public import ConLeche.Semantics.EqTower

public section

/-!
# The annotated hand-built basis towers, `Eq` family (task #161, ENDGAME E)

The ENDGAME D seal's §4 named the basis tier's one wall: `pinnedStructT`
has no entry for `Eq`, `Eq.refl`, `Eq.rec` or `PSigma'.rec`, and `BConst`
has no such constructors, so `acval_basis_pinned` — which unlocks the
other five blocks' leaves — is *empty* on `eqK`.  v1 builds those leaves
by hand (`Install/BasisS.lean`'s `eqValT`/`eqReflValT`/`eqRecValT`) and
derives `EqLawV` from the tower; the P tier needs the **annotated**
towers, whose binder numerals `interp` dispatches on.

## The bits are NOT chosen — `mem_type` pins every one of them

The DESIGN entry "the chosen bits of the hand-built basis towers"
licensed a *choice* here (graph-regime bits, model-side data, no
establishment doctrine touched) and fenced it as the campaign's only
such site.  **The license is not exercised, because there is nothing
left to choose.**  Every one of these towers is stored at a constant
whose type is *also* stored, and `EnvModelM.mem_type` demands

> `interp ρ (acval n ψ) ∈ˢ interp ρ (the type's reading)`

whose right-hand side is a `piR` tower whose numerals are the pinned
declaration's own `pw` data (`pwBit ψ`).  `lamR`/`piR` disagree
irreconcilably across the regime split — `bit_forced_pos` and
`bit_forced_zero` below — so the tower's λ bit at every binder is
*forced* to agree in zero-ness with the corresponding `pi` bit of the
pinned type.  Concretely:

| tower | pinned `pw` | forced bits |
|---|---|---|
| `eqValAV` | `.never` ×3 | all **nonzero** (the ratified choice, arrived at by force) |
| `eqReflValAV` | `.ifAllZero []` ×2 | all **zero** |
| `eqRecValAV` | `.ifAllZero [u_1]` ×6 | zero **iff `ψ u_1 = 0`** |

So the design entry's counterfactual (iii) is right about `Eq` and
inverted at `Eq.refl`: there bit `0` is not the collapse, it is the only
legal value, and a nonzero bit is what would break the law.  Nothing is
free; the doctrine "bits are never taken from a metatheorem" holds here
in its strongest form — the bits come from the *pin*, exactly as at the
sixteen `pinnedStructT` blocks, only through `mem_type` rather than
through `pinnedStructT`.

The scope fence in the DESIGN entry therefore stands unused, and should
be recorded as such rather than deleted: a future hand-built value at a
constant whose type is *not* stored would still have a genuine choice.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm eqValT eqReflValT eqRecValT)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The forcing lemmas

Two lines each, and together they are the whole reason this file has no
freedom.  A λ-tower's numeral and its type's numeral must agree in
zero-ness, because the two regimes' inhabitants are disjoint: above
zero a `lamR` is a graph and a `piR` is a set of graphs; at zero a
`lamR` is `pt` and a `piR` is a truth value, whose only member is
`pt`. -/

/-- **A graph-regime abstraction never inhabits a squash-regime
product.**  So a tower whose stored type's binder carries bit `0` may
not carry a nonzero bit. -/
theorem bit_forced_pos {v : Nat} {A : V} {F B : V → V} (hv : v ≠ 0)
    (h : lamR v A F ∈ˢ piR 0 A B) : False :=
  lamR_ne_pt hv (eq_pt_of_mem_piR_zero h)

/-- **A squash-regime abstraction inhabits a graph-regime product only
if the product is degenerate.**  The complement of `bit_forced_pos`:
`pt` is not a graph, so at a nonempty domain with inhabited fibres the
membership fails.  (Stated as the contrapositive the towers use: from
the membership and a domain witness, the product's fibre at that
witness is a truth value.) -/
theorem bit_forced_zero {v : Nat} {A a : V} {F B : V → V} (hv : v ≠ 0)
    (h : lamR 0 A F ∈ˢ piR v A B) (ha : a ∈ˢ A) :
    (pt : V) ∈ˢ B a := by
  rw [lamR_zero] at h
  exact app_pt (V := V) a ▸ app_mem_piR_pos hv h ha

/-! ## `Eq` — all three bits nonzero, forced

The pinned `Eq` carries `pw = .never` at all three binders, and it is
right to: the codomain of the innermost binder is `Prop`, and `Prop`
*as a type* lives in `Sort 1`.  The `v'`-for-a-`Sort` trap
(`Interp/BasisType.lean`'s docstring) is exactly what makes the `Eq`
former a graph and not a proof point. -/

/-- `Eq`'s annotated valuation: v1's `eqValT` with all three binders in
the graph regime (forced — see the module docstring). -/
@[expose] def eqValAV (ψ : Name → Nat) : AnnotTerm :=
  .lam 1 (.sort (ψ uN)) (.lam 1 (.bvar 0) (.lam 1 (.bvar 1)
    (.eqE (.bvar 1) (.bvar 0))))

/-- `Eq.refl`'s annotated valuation: `.prf` under two **squash-regime**
binders (forced: the pinned `pw` is `.ifAllZero []` at both, because
`Eq α a a` is a proposition). -/
@[expose] def eqReflValAV (ψ : Name → Nat) : AnnotTerm :=
  .lam 0 (.sort (ψ uN)) (.lam 0 (.bvar 0) .prf)

/-- `Eq.rec`'s annotated valuation: the minor premise, returned, under
six binders whose bit is the motive level's own zero test — the pinned
`pw` is `.ifAllZero [u_1]` at every one of them. -/
@[expose] def eqRecValAV (ψ : Name → Nat) : AnnotTerm :=
  let m : Nat := pwBit ψ (.ifAllZero [u1N])
  .lam m (.sort (ψ uN))
    (.lam m (.bvar 0)
      (.lam m (.pi 0 1 (.bvar 1)
          (.pi 0 (ψ u1N + 1)
            (AnnotTerm.mkAppN (eqValAV ψ) [.bvar 2, .bvar 1, .bvar 0])
            (.sort (ψ u1N))))
        (.lam m (.app (.app (.bvar 0) (.bvar 1))
            (AnnotTerm.mkAppN (eqReflValAV ψ) [.bvar 2, .bvar 1]))
          (.lam m (.bvar 3)
            (.lam m (AnnotTerm.mkAppN (eqValAV ψ) [.bvar 4, .bvar 3, .bvar 0])
              (.bvar 2))))))

/-! ### Erasure: the towers project onto v1's -/

@[simp] theorem eqValAV_erase (ψ : Name → Nat) :
    (eqValAV ψ).erase = eqValT ψ := rfl

@[simp] theorem eqReflValAV_erase (ψ : Name → Nat) :
    (eqReflValAV ψ).erase = eqReflValT ψ := rfl

@[simp] theorem eqRecValAV_erase (ψ : Name → Nat) :
    (eqRecValAV ψ).erase = eqRecValT ψ := rfl

/-! ### The towers read the assignment only at their own level names -/

theorem eqValAV_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqValAV ψ₁ = eqValAV ψ₂ := by rw [eqValAV, eqValAV, h]

theorem eqReflValAV_congr {ψ₁ ψ₂ : Name → Nat} (h : ψ₁ uN = ψ₂ uN) :
    eqReflValAV ψ₁ = eqReflValAV ψ₂ := by rw [eqReflValAV, eqReflValAV, h]

/-! ## `Eq`'s tower, interpreted -/

/-- **`Eq`'s tower, interpreted**: a three-deep graph-regime `lamR` over
the truth-set former. -/
theorem eqValAV_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValAV ψ)
      = lamR 1 (univ (ψ uN))
        (fun a => lamR 1 a (fun x => lamR 1 a (fun y => eqv x y))) := by
  simp [eqValAV, cons]

/-- **The full spine's value** — `EqLaw`'s first conjunct at the tower:
three `app_lamR_pos`, one per binder, each on its domain. -/
theorem eqValAV_app₃ (ψ : Name → Nat) (ρ : Nat → V) (A a b : V)
    (hA : A ∈ˢ (univ (ψ uN) : V)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) :
    SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρ (eqValAV ψ)) A) a) b = eqv a b := by
  rw [eqValAV_interp, app_lamR_pos Nat.one_ne_zero hA,
    app_lamR_pos Nat.one_ne_zero ha, app_lamR_pos Nat.one_ne_zero hb]

/-- The tower inhabits the `Eq` former's product tower, at the pinned
type's own numerals (all nonzero). -/
theorem eqValAV_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqValAV ψ) ∈ˢ piR 1 (univ (ψ uN) : V)
      (fun a => piR 1 a (fun _ => piR 1 a (fun _ => univZero))) := by
  rw [eqValAV_interp]
  exact lamR_mem (fun _a _ => lamR_mem (fun _x _ =>
    lamR_mem (fun _y _ => eqv_mem_univZero _ _)))

/-- The tower is graded (`WellDenoted`), at every environment. -/
theorem eqValAV_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (eqValAV ψ) := by
  refine ⟨trivial, fun A _ => ⟨trivial, fun a _ => ⟨trivial,
    fun b _ => ⟨trivial, trivial⟩, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨fun _ => univZero, fun _ _ => eqv_mem_univZero _ _,
      fun h => nomatch h⟩
  · exact ⟨fun _ => piR 1 A (fun _ => univZero),
      fun _ _ => lamR_mem fun _ _ => eqv_mem_univZero _ _,
      fun h => nomatch h⟩
  · exact ⟨fun x => piR 1 x (fun _ => piR 1 x (fun _ => univZero)),
      fun _ _ => lamR_mem fun _ _ =>
        lamR_mem fun _ _ => eqv_mem_univZero _ _,
      fun h => nomatch h⟩

/-- The tower is bit-valid (`AnnotValid`) — the `lam` clause is
bit-free, so this is pure structure. -/
theorem eqValAV_validV (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotValid V ρ (eqValAV ψ) := by
  refine ⟨trivial, fun A _ => ⟨trivial, fun a _ => ⟨trivial,
    fun b _ => ⟨trivial, trivial⟩⟩⟩⟩

/-- The P currency, packaged. -/
theorem eqValAV_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (eqValAV ψ) :=
  ⟨eqValAV_wellDenoted ψ ρ, eqValAV_validV ψ ρ⟩

/-! ## `Eq.refl`'s tower, interpreted — the squash regime, forced -/

/-- **`Eq.refl`'s tower, interpreted**: `pt`, because its outer binder's
codomain `(a : α) → Eq α a a` is a proposition. -/
theorem eqReflValAV_interp (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValAV ψ) = (pt : V) := by
  simp [eqReflValAV, lamR_zero]

/-- The tower inhabits `Eq.refl`'s product tower at the pinned type's
numerals (both zero) — `pt_mem_piR_zero_of` twice, bottoming at
`pt_mem_eqv_self`. -/
theorem eqReflValAV_mem (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (eqReflValAV ψ) ∈ˢ piR 0 (univ (ψ uN) : V)
      (fun a => piR 0 a (fun x => eqv x x)) := by
  rw [eqReflValAV_interp]
  exact pt_mem_piR_zero_of fun _A _ =>
    pt_mem_piR_zero_of fun x _ => pt_mem_eqv_self x

theorem eqReflValAV_wellDenoted (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenoted V ρ (eqReflValAV ψ) := by
  refine ⟨trivial, fun A _ => ⟨trivial, fun _a _ => trivial, ?_⟩, ?_⟩
  · exact ⟨fun x => eqv x x, fun x _ => pt_mem_eqv_self x,
      fun _ x _ => eqv_mem_univZero x x⟩
  · exact ⟨fun x => piR 0 x (fun y => eqv y y),
      fun _ _ => pt_mem_piR_zero_of fun y _ => pt_mem_eqv_self y,
      fun _ _ _ => piR_zero_mem_univZero⟩

theorem eqReflValAV_validV (ψ : Name → Nat) (ρ : Nat → V) :
    AnnotValid V ρ (eqReflValAV ψ) :=
  ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

theorem eqReflValAV_wellDenotedV (ψ : Name → Nat) (ρ : Nat → V) :
    WellDenotedV V ρ (eqReflValAV ψ) :=
  ⟨eqReflValAV_wellDenoted ψ ρ, eqReflValAV_validV ψ ρ⟩

/-! ## `EqLaw`, discharged from the tower

The field the ENDGAME D seal named as `eqK`'s whole content, and the
reason `eqLaw_cons_fresh` is structurally unavailable at this block
(its side condition is `eqName ≠ c₀.name` and the cons *is* `Eq`).
Both conjuncts come off `eqValAV` directly:

* the **value** clause is `eqValAV_app₃` — three `app_lamR_pos`, one
  per binder, each on its own domain.  v1 needs two `app_lamC`s and
  states the law at the two-fold application because its η/unit
  consumers want the rigidity clause; the P consumers read the
  three-fold form, so all three fire here;
* the **grading** clause — which v1 has no analogue of — is the
  `WellDenoted` `.app` chain over `eqValAV_mem`, whose three `v = 0`
  fibre obligations are all vacuous (the bits are nonzero), plus
  `eqv_mem_univZero` for the propositionhood half. -/

/-- **The `Eq` spine over the tower is graded, and is a proposition.**
`EqLaw`'s second conjunct, factored out: the `Eq.refl` and `Eq.rec`
type readings both mention the spine directly, not through the
field. -/
theorem eqValAV_app₃_okP (ψ : Name → Nat) (ρ : Nat → V)
    {Aa la ra : AnnotTerm} (hAa : WellDenotedV V ρ Aa) (hla : WellDenotedV V ρ la)
    (hra : WellDenotedV V ρ ra)
    (hA : interp V ρ Aa ∈ˢ (univ (ψ uN) : V))
    (ha : interp V ρ la ∈ˢ interp V ρ Aa)
    (hb : interp V ρ ra ∈ˢ interp V ρ Aa) :
    WellDenotedV V ρ (.app (.app (.app (eqValAV ψ) Aa) la) ra) ∧
      interp V ρ (.app (.app (.app (eqValAV ψ) Aa) la) ra)
        ∈ˢ (univZero : V) := by
  have hmem := eqValAV_mem (V := V) ψ ρ
  have h1 : SetTheory.app (interp V ρ (eqValAV ψ)) (interp V ρ Aa)
      ∈ˢ piR 1 (interp V ρ Aa)
        (fun _ => piR 1 (interp V ρ Aa) (fun _ => univZero)) :=
    app_mem_piR_pos Nat.one_ne_zero hmem hA
  have h2 : SetTheory.app (SetTheory.app (interp V ρ (eqValAV ψ))
        (interp V ρ Aa)) (interp V ρ la)
      ∈ˢ piR 1 (interp V ρ Aa) (fun _ => univZero) :=
    app_mem_piR_pos Nat.one_ne_zero h1 ha
  refine ⟨⟨⟨⟨⟨eqValAV_wellDenoted ψ ρ, hAa.1, 1, _, _, hmem, hA,
      fun h => nomatch h⟩, hla.1, 1, _, _, h1, ha,
      fun h => nomatch h⟩, hra.1, 1, _, _, h2, hb,
      fun h => nomatch h⟩,
    ⟨⟨eqValAV_validV ψ ρ, hAa.2⟩, hla.2⟩, hra.2⟩, ?_⟩
  rw [interp_app, interp_app, interp_app,
    eqValAV_app₃ ψ ρ _ _ _ hA ha hb]
  exact eqv_mem_univZero _ _

/-- **`EqLaw` from the tower.**  Any environment carrier whose `Eq`
leaf is the annotated tower satisfies the field. -/
theorem eqLaw_of_tower {env : ConLeche.Env} (m : EnvModel V env)
    (hleaf : ∀ ψ : Name → Nat, m.acval eqName ψ = eqValAV ψ) :
    EqLaw m := by
  intro _hf ψ
  refine ⟨fun ρ A a b hA ha hb => ?_, fun ρ Aa la ra hAa hla hra
    hA ha hb => ?_⟩
  · rw [hleaf]; exact eqValAV_app₃ ψ ρ A a b hA ha hb
  · rw [hleaf]
    exact eqValAV_app₃_okP ψ ρ hAa hla hra hA ha hb

end ConLeche.Model
